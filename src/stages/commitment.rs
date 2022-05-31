use crate::{
    commitment::{BranchData, HexPatriciaHashed, ProcessUpdateArg},
    consensus::ValidationError,
    kv::{
        mdbx::*,
        tables::{self, AccountChange, StorageChange, StorageChangeKey},
        traits::{ttw, TryGenIter},
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
use itertools::Itertools;
use std::{
    cmp::{self, Ordering},
    collections::HashMap,
};
use tracing::*;

pub enum Change {
    Account(Address),
    Storage(Address, H256),
}

pub fn gather_changes<'db, 'tx, K, E>(
    txn: &'tx MdbxTransaction<'db, K, E>,
    from: BlockNumber,
) -> impl Iterator<Item = anyhow::Result<(BlockNumber, Change)>> + 'tx
where
    'db: 'tx,
    K: TransactionKind,
    E: EnvironmentKind,
{
    TryGenIter::from(move || {
        let mut account_changes = txn.cursor(tables::AccountChangeSet)?;
        let mut storage_changes = txn.cursor(tables::StorageChangeSet)?;

        let mut account_data = account_changes.seek(from)?;
        let mut storage_data = storage_changes.seek(from)?;

        loop {
            let account_pos = account_data
                .as_ref()
                .map(|(block_number, change)| (*block_number, change.address))
                .unwrap_or((BlockNumber(u64::MAX), Address::from([0xff_u8; 20])));
            let storage_pos = storage_data
                .as_ref()
                .map(|(k, _)| (k.block_number, k.address))
                .unwrap_or((BlockNumber(u64::MAX), Address::from([0xff_u8; 20])));

            if account_pos.0 == BlockNumber(u64::MAX)
                && storage_pos.0 == BlockNumber(u64::MAX)
                && account_pos.1 == Address::from([0xff_u8; 20])
                && storage_pos.1 == Address::from([0xff_u8; 20])
            {
                break;
            }

            let advance_account = match account_pos.0.cmp(&storage_pos.0) {
                Ordering::Less => true,
                Ordering::Equal => match account_pos.1.cmp(&storage_pos.1) {
                    Ordering::Less => true,
                    Ordering::Equal => true,
                    Ordering::Greater => false,
                },
                Ordering::Greater => false,
            };

            if advance_account {
                let (block_number, AccountChange { address, .. }) = account_data.unwrap();
                yield (block_number, Change::Account(address));

                account_data = account_changes.next()?;
            } else {
                let (
                    StorageChangeKey {
                        block_number,
                        address,
                    },
                    StorageChange { location, .. },
                ) = storage_data.unwrap();
                yield (block_number, Change::Storage(address, location));

                storage_data = storage_changes.next()?;
            }
        }

        Ok(())
    })
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
            let change_iter = gather_changes(tx, past_progress + 1)
                .take_while(ttw(|(block_number, _)| *block_number <= max_block))
                .chunks(90_000);

            let mut state_root =
                crate::accessors::chain::header::read_canonical(tx, past_progress)?
                    .unwrap()
                    .state_root;
            for chunk in &change_iter {
                let mut updates = HashMap::<Address, ProcessUpdateArg>::new();
                for change in chunk {
                    match change?.1 {
                        Change::Account(address) => {
                            updates.entry(address).or_default().account_changed = true;
                        }
                        Change::Storage(address, location) => {
                            updates
                                .entry(address)
                                .or_default()
                                .changed_storage
                                .insert(location);
                        }
                    }
                }

                struct TxState<'tx, 'db, K, E>
                where
                    K: TransactionKind,
                    E: EnvironmentKind,
                    'db: 'tx,
                {
                    tx: &'tx MdbxTransaction<'db, K, E>,
                }

                impl<'tx, 'db, K, E> crate::commitment::State for TxState<'tx, 'db, K, E>
                where
                    K: TransactionKind,
                    E: EnvironmentKind,
                    'db: 'tx,
                {
                    fn get_branch(&mut self, prefix: &[u8]) -> anyhow::Result<Option<BranchData>> {
                        self.tx.get(tables::CommitmentBranch, prefix.to_vec())
                    }
                    fn get_account(&mut self, address: Address) -> anyhow::Result<Option<Account>> {
                        self.tx.get(tables::Account, address)
                    }
                    fn get_storage(
                        &mut self,
                        address: Address,
                        location: H256,
                    ) -> anyhow::Result<Option<U256>> {
                        Ok(self
                            .tx
                            .cursor(tables::Storage)?
                            .seek_both_range(address, location)?
                            .filter(|&(l, _)| l == location)
                            .map(|(_, v)| v))
                    }
                }

                let mut tx_state = TxState { tx };

                let branch_updates;
                (state_root, branch_updates) =
                    HexPatriciaHashed::new(&mut tx_state).process_updates(updates)?;
                for (branch_key, branch_update) in branch_updates {
                    tx.set(tables::CommitmentBranch, branch_key, branch_update)?;
                }
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
        todo!()
    }
}
