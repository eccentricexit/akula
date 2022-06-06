use crate::{
    commitment::generic::*,
    consensus::ValidationError,
    kv::{
        mdbx::*,
        tables::{self, StorageChangeKey},
        traits::ttw,
    },
    models::*,
    stagedsync::{
        stage::{ExecOutput, Stage, StageError, StageInput, UnwindInput, UnwindOutput},
        stages::*,
    },
    StageId,
};
use anyhow::format_err;
use async_trait::async_trait;
use std::{
    cmp,
    collections::{HashMap, HashSet},
};
use tracing::*;

const COMMITMENT_CHUNK: usize = 90_000;

#[derive(Debug)]
pub enum Change {
    Account(Address),
    Storage(Address, H256),
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
        let past_progress = input.stage_progress.unwrap_or(genesis);

        if max_block > past_progress {
            let mut updates = HashMap::<Address, HashSet<H256>>::new();
            for change in tx
                .cursor(tables::AccountChangeSet)?
                .walk(Some(past_progress + 1))
                .take_while(ttw(|(block_number, _)| *block_number <= max_block))
            {
                updates.entry(change?.1.address).or_default();
            }

            for change in tx
                .cursor(tables::StorageChangeSet)?
                .walk(Some(past_progress + 1))
                .take_while(ttw(|(StorageChangeKey { block_number, .. }, _)| {
                    *block_number <= max_block
                }))
            {
                let change = change?;
                updates
                    .entry(change.0.address)
                    .or_default()
                    .insert(change.1.location);
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
                    fn get_branch(
                        &mut self,
                        prefix: &[u8],
                    ) -> anyhow::Result<Option<BranchData<H256>>> {
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
                fn get_branch(
                    &mut self,
                    prefix: &[u8],
                ) -> anyhow::Result<Option<BranchData<Address>>> {
                    self.tx.get(tables::AccountCommitment, prefix.to_vec())
                }
                fn get_payload(&mut self, address: &Address) -> anyhow::Result<Option<RlpAccount>> {
                    let rlp_acc = if let Some(acc) = self.tx.get(tables::Account, *address)? {
                        let storage_root = if let Some(v) = self.storage_roots.get(address).copied()
                        {
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

            let header_state_root = crate::accessors::chain::header::read_canonical(tx, max_block)?
                .unwrap()
                .state_root;
            if header_state_root != state_root {
                return Err(StageError::Validation {
                    block: max_block,
                    error: ValidationError::WrongStateRoot {
                        expected: header_state_root,
                        got: state_root,
                    },
                });
            }
            info!("Block #{} state root OK: {:?}", max_block, state_root);
        }

        Ok(ExecOutput::Progress {
            stage_progress: cmp::max(max_block, past_progress),
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
