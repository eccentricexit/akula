use crate::{
    commitment::generic::*,
    consensus::ValidationError,
    kv::{mdbx::*, tables},
    models::*,
    stagedsync::{
        stage::{ExecOutput, Stage, StageError, StageInput, UnwindInput, UnwindOutput},
        stages::*,
    },
    StageId,
};
use anyhow::format_err;
use async_trait::async_trait;
use std::collections::{HashMap, HashSet};
use tracing::*;

const COMMITMENT_CHUNK: usize = 90_000;

#[derive(Debug)]
pub enum Change {
    Account(Address),
    Storage(Address, H256),
}

pub fn increment_commitment<'db, 'tx, E>(
    tx: &'tx MdbxTransaction<'db, RW, E>,
    from: Option<BlockNumber>,
) -> anyhow::Result<H256>
where
    'db: 'tx,
    E: EnvironmentKind,
{
    let mut updates = HashMap::<Address, HashSet<H256>>::new();

    if let Some(from) = from {
        for change in tx.cursor(tables::AccountChangeSet)?.walk(Some(from + 1)) {
            updates.entry(change?.1.address).or_default();
        }

        for change in tx.cursor(tables::StorageChangeSet)?.walk(Some(from + 1)) {
            let change = change?;
            updates
                .entry(change.0.address)
                .or_default()
                .insert(change.1.location);
        }
    } else {
        for e in tx.cursor(tables::Account)?.walk(None) {
            updates.entry(e?.0).or_default();
        }

        for e in tx.cursor(tables::Storage)?.walk(None) {
            let (address, (location, _)) = e?;
            updates.entry(address).or_default().insert(location);
        }
    }

    fn compute_storage_root<'db: 'tx, 'tx, E>(
        tx: &'tx MdbxTransaction<'db, RW, E>,
        address: Address,
        locations: impl IntoIterator<Item = H256>,
    ) -> anyhow::Result<H256>
    where
        E: EnvironmentKind,
    {
        struct TxStateForStorage<'tx, 'db, K, E>
        where
            K: TransactionKind,
            E: EnvironmentKind,
            'db: 'tx,
        {
            tx: &'tx MdbxTransaction<'db, K, E>,
            address: Address,
        }

        impl<'tx, 'db, K, E> crate::commitment::generic::State<H256, U256>
            for TxStateForStorage<'tx, 'db, K, E>
        where
            K: TransactionKind,
            E: EnvironmentKind,
            'db: 'tx,
        {
            fn get_branch(&mut self, prefix: &[u8]) -> anyhow::Result<Option<BranchData<H256>>> {
                self.tx.get(
                    tables::StorageCommitment,
                    tables::StorageCommitmentKey {
                        address: self.address,
                        prefix: prefix.to_vec(),
                    },
                )
            }
            fn get_payload(&mut self, location: &H256) -> anyhow::Result<Option<U256>> {
                Ok(self
                    .tx
                    .cursor(tables::Storage)?
                    .seek_both_range(self.address, *location)?
                    .filter(|&(l, _)| l == *location)
                    .map(|(_, v)| v))
            }
        }

        let mut tx_state = TxStateForStorage { tx, address };

        let (storage_root, branch_updates) =
            HexPatriciaHashed::new(&mut tx_state).process_updates(locations)?;
        for (branch_key, branch_update) in branch_updates {
            tx.set(
                tables::StorageCommitment,
                tables::StorageCommitmentKey {
                    address,
                    prefix: branch_key,
                },
                branch_update,
            )?;
        }

        Ok(storage_root)
    }

    let mut storage_roots = HashMap::new();
    for (address, locations) in updates {
        let entry = storage_roots.entry(address).or_insert(EMPTY_ROOT);
        if tx.get(tables::Account, address)?.is_some() {
            *entry = compute_storage_root(tx, address, locations)?;
        } else {
            let mut cur = tx.cursor(tables::StorageCommitment)?;
            while let Some((k, _)) = cur.seek(address)? {
                if k.address == address {
                    cur.delete_current()?;
                } else {
                    break;
                }
            }
        }
    }

    struct TxStateWithStorageRoots<'tx, 'db, E>
    where
        E: EnvironmentKind,
        'db: 'tx,
    {
        tx: &'tx MdbxTransaction<'db, RW, E>,
        storage_roots: HashMap<Address, H256>,
    }

    impl<'tx, 'db, E> crate::commitment::generic::State<Address, RlpAccount>
        for TxStateWithStorageRoots<'tx, 'db, E>
    where
        E: EnvironmentKind,
        'db: 'tx,
    {
        fn get_branch(&mut self, prefix: &[u8]) -> anyhow::Result<Option<BranchData<Address>>> {
            self.tx.get(tables::AccountCommitment, prefix.to_vec())
        }
        fn get_payload(&mut self, address: &Address) -> anyhow::Result<Option<RlpAccount>> {
            let rlp_acc = if let Some(acc) = self.tx.get(tables::Account, *address)? {
                let storage_root = if let Some(v) = self.storage_roots.get(address).copied() {
                    v
                } else {
                    compute_storage_root(self.tx, *address, [])?
                };

                Some(acc.to_rlp(storage_root))
            } else {
                None
            };
            trace!("Loaded account {:?}: {:?}", address, rlp_acc);

            Ok(rlp_acc)
        }
    }

    let addresses = storage_roots.keys().copied().collect::<Vec<_>>();

    let mut tx_state = TxStateWithStorageRoots { tx, storage_roots };

    let (state_root, branch_updates) =
        HexPatriciaHashed::new(&mut tx_state).process_updates(addresses)?;

    for (branch_key, branch_update) in branch_updates {
        tx.set(tables::AccountCommitment, branch_key, branch_update)?;
    }

    Ok(state_root)
}

#[derive(Debug)]
pub struct Commitment;

#[async_trait]
impl<'db, E> Stage<'db, E> for Commitment
where
    E: EnvironmentKind,
{
    fn id(&self) -> StageId {
        COMMITMENT
    }

    async fn execute<'tx>(
        &mut self,
        tx: &'tx mut MdbxTransaction<'db, RW, E>,
        input: StageInput,
    ) -> Result<ExecOutput, StageError>
    where
        'db: 'tx,
    {
        let genesis = BlockNumber(0);
        let max_block = input
            .previous_stage
            .map(|tuple| tuple.1)
            .ok_or_else(|| format_err!("Cannot be first stage"))?;
        let from = input.stage_progress.unwrap_or(genesis);

        let state_root = increment_commitment(tx, Some(from))?;

        let expected_root = crate::accessors::chain::header::read_canonical(tx, max_block)?
            .ok_or_else(|| format_err!("Block #{} not found", max_block))?
            .state_root;
        if expected_root != state_root {
            return Err(StageError::Validation {
                block: max_block,
                error: ValidationError::WrongStateRoot {
                    expected: expected_root,
                    got: state_root,
                },
            });
        }
        info!("State root OK: {:?}", state_root);

        Ok(ExecOutput::Progress {
            stage_progress: max_block,
            done: true,
            reached_tip: true,
        })
    }

    async fn unwind<'tx>(
        &mut self,
        tx: &'tx mut MdbxTransaction<'db, RW, E>,
        input: UnwindInput,
    ) -> anyhow::Result<UnwindOutput>
    where
        'db: 'tx,
    {
        let _ = tx;
        let _ = input;
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        crypto::{keccak256, trie_root},
        h256_to_u256,
        kv::{
            new_mem_database,
            tables::{AccountChange, StorageChange, StorageChangeKey},
        },
        u256_to_h256, zeroless_view,
    };
    use bytes::BytesMut;
    use fastrlp::Encodable;
    use proptest::prelude::*;
    use std::collections::BTreeMap;

    // strategies
    fn addresses() -> impl Strategy<Value = Address> {
        any::<[u8; 20]>().prop_map(Address::from)
    }

    fn h256s() -> impl Strategy<Value = H256> {
        any::<[u8; 32]>().prop_map(H256::from)
    }

    fn u256s() -> impl Strategy<Value = U256> {
        any::<[u8; 32]>().prop_map(|v| h256_to_u256(H256::from(v)))
    }

    fn nonzero_u256s() -> impl Strategy<Value = U256> {
        u256s().prop_filter("value must not be zero", |&x| x != 0)
    }

    prop_compose! {
        fn accounts()(
            nonce in any::<u64>(),
            balance in u256s(),
            code_hash in h256s(),
        ) -> Account {
            Account { nonce, balance, code_hash }
        }
    }

    type Storage = BTreeMap<H256, U256>;

    fn account_storages() -> impl Strategy<Value = Storage> {
        prop::collection::btree_map(h256s(), nonzero_u256s(), 0..20)
    }

    prop_compose! {
        fn accounts_with_storage()(
            account in accounts(),
            storage in account_storages(),
        ) -> (Account, Storage) {
            (account, storage)
        }
    }

    type ChangingAccount = BTreeMap<u32, Option<(Account, Storage)>>;

    #[derive(Debug)]
    struct ChangingAccountsFixture {
        accounts: BTreeMap<Address, ChangingAccount>,
        before_increment: u32,
        after_increment: u32,
    }

    fn changing_accounts(max_height: u32) -> impl Strategy<Value = ChangingAccount> {
        prop::collection::btree_map(
            0..max_height,
            prop::option::of(accounts_with_storage()),
            1..3,
        )
        .prop_filter("does not contain changes", |x| {
            for v in x.values() {
                if v.is_some() {
                    return true;
                }
            }
            false
        })
    }

    prop_compose! {
        fn test_datas()(
            after_increment in 2u32..,
        )(
            before_increment in 0..after_increment - 2,
            after_increment in Just(after_increment),
            accounts in prop::collection::btree_map(
                addresses(),
                changing_accounts(after_increment - 1),
                0..100
            ),
        ) -> ChangingAccountsFixture {
            ChangingAccountsFixture {
                accounts,
                before_increment,
                after_increment,
            }
        }
    }

    // helper functions
    fn expected_storage_root(storage: &Storage) -> H256 {
        if storage.is_empty() {
            EMPTY_ROOT
        } else {
            trie_root(storage.iter().map(|(k, v)| {
                let mut b = BytesMut::new();
                Encodable::encode(&zeroless_view(&u256_to_h256(*v)), &mut b);
                (keccak256(k.to_fixed_bytes()), b)
            }))
        }
    }

    fn expected_state_root(accounts_with_storage: &BTreeMap<Address, (Account, Storage)>) -> H256 {
        trie_root(
            accounts_with_storage
                .iter()
                .map(|(&address, (account, storage))| {
                    let account_rlp = account.to_rlp(expected_storage_root(storage));
                    (keccak256(address), fastrlp::encode_fixed_size(&account_rlp))
                }),
        )
    }

    fn accounts_at_height(
        changing_accounts: &ChangingAccountsFixture,
        height: u32,
    ) -> BTreeMap<Address, (Account, Storage)> {
        let mut result = BTreeMap::new();
        for (address, state) in &changing_accounts.accounts {
            if let Some(account_with_storage) = changing_account_at_height(state, height) {
                result.insert(*address, account_with_storage.clone());
            }
        }
        result
    }

    fn populate_state<'db, 'tx, E>(
        tx: &'tx MdbxTransaction<'db, RW, E>,
        accounts_with_storage: BTreeMap<Address, (Account, Storage)>,
    ) -> anyhow::Result<()>
    where
        E: EnvironmentKind,
        'db: 'tx,
    {
        tx.clear_table(tables::Account)?;
        tx.clear_table(tables::Storage)?;

        let mut account_cursor = tx.cursor(tables::Account)?;
        let mut storage_cursor = tx.cursor(tables::Storage)?;

        for (address, (account, storage)) in accounts_with_storage {
            account_cursor.upsert(address, account)?;
            for (location, value) in storage {
                storage_cursor.upsert(address, (location, value))?
            }
        }

        Ok(())
    }

    fn populate_change_sets<'db, 'tx, E>(
        tx: &'tx MdbxTransaction<'db, RW, E>,
        changing_accounts: &BTreeMap<Address, ChangingAccount>,
    ) -> anyhow::Result<()>
    where
        E: EnvironmentKind,
        'db: 'tx,
    {
        tx.clear_table(tables::AccountChangeSet)?;
        tx.clear_table(tables::StorageChangeSet)?;

        let mut account_cursor = tx.cursor(tables::AccountChangeSet)?;
        let mut storage_cursor = tx.cursor(tables::StorageChangeSet)?;

        for (address, states) in changing_accounts {
            let mut previous: Option<&(Account, Storage)> = None;
            for (height, current) in states {
                let block_number = BlockNumber(*height as u64);
                if current.as_ref() != previous {
                    let previous_account = previous.as_ref().map(|(a, _)| *a);
                    let current_account = current.as_ref().map(|(a, _)| *a);
                    if current_account != previous_account {
                        account_cursor.upsert(
                            block_number,
                            AccountChange {
                                address: *address,
                                account: previous_account,
                            },
                        )?;
                    }
                    let empty_storage = Storage::new();
                    let previous_storage =
                        previous.as_ref().map(|(_, s)| s).unwrap_or(&empty_storage);
                    let current_storage =
                        current.as_ref().map(|(_, s)| s).unwrap_or(&empty_storage);
                    for (location, value) in previous_storage {
                        if current_storage.get(location).unwrap_or(&U256::ZERO) != value {
                            storage_cursor.upsert(
                                StorageChangeKey {
                                    block_number,
                                    address: *address,
                                },
                                StorageChange {
                                    location: *location,
                                    value: *value,
                                },
                            )?;
                        }
                    }
                    for location in current_storage.keys() {
                        if !previous_storage.contains_key(location) {
                            storage_cursor.upsert(
                                StorageChangeKey {
                                    block_number,
                                    address: *address,
                                },
                                StorageChange {
                                    location: *location,
                                    value: U256::ZERO,
                                },
                            )?;
                        }
                    }
                }
                previous = current.as_ref();
            }
        }

        Ok(())
    }

    fn changing_account_at_height(
        account: &ChangingAccount,
        height: u32,
    ) -> Option<&(Account, Storage)> {
        for (changed_at, state) in account.iter().rev() {
            if changed_at <= &height {
                return state.as_ref();
            }
        }
        None
    }

    // test
    fn do_trie_root_matches(test_data: ChangingAccountsFixture) {
        let db = new_mem_database().unwrap();

        let tx = db.begin_mutable().unwrap();
        let state_before_increment = accounts_at_height(&test_data, test_data.before_increment);
        let expected = expected_state_root(&state_before_increment);
        populate_state(&tx, state_before_increment).unwrap();
        tx.commit().unwrap();

        let tx = db.begin_mutable().unwrap();
        let root = increment_commitment(&tx, None).unwrap();
        tx.commit().unwrap();

        assert_eq!(root, expected);

        let tx = db.begin_mutable().unwrap();
        let state_after_increment = accounts_at_height(&test_data, test_data.after_increment);
        let expected = expected_state_root(&state_after_increment);
        populate_state(&tx, state_after_increment).unwrap();
        populate_change_sets(&tx, &test_data.accounts).unwrap();
        tx.commit().unwrap();

        let tx = db.begin_mutable().unwrap();
        let root = increment_commitment(&tx, Some(BlockNumber(test_data.before_increment as u64)))
            .unwrap();

        assert_eq!(root, expected);
    }

    proptest! {
        #[test]
        fn trie_root_matches(test_data in test_datas()) {
            do_trie_root_matches(test_data);
        }
    }
}
