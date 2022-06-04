#![allow(unreachable_code, unused, unused_must_use)]

use super::{node::Node, types::GetPooledTransactions};
use crate::{
    kv::{tables, MdbxWithDirHandle},
    models::{BlockHeader, MessageWithSignature, H160, H256, H512},
    p2p::types::{Message, PeerFilter},
};
use dashmap::{mapref::one::Ref, DashMap, DashSet};
use derive_more::{Deref, DerefMut};
use ethereum_interfaces::sentry as grpc_sentry;
use ethnum::U256;
use futures::stream::FuturesUnordered;
use hashbrown::HashSet;
use itertools::Itertools;
use mdbx::{EnvironmentKind, WriteMap};
use parking_lot::Mutex;
use rand::Rng;
use std::{
    collections::BinaryHeap,
    sync::{atomic::AtomicU64, Arc},
    time::Duration,
};
use task_group::TaskGroup;
use tokio::sync::{mpsc, Mutex as AsyncMutex};
use tokio_stream::StreamExt;
use tracing::*;

#[derive(Debug, Clone, PartialEq, Eq, Deref, DerefMut)]
pub struct Transaction {
    #[deref]
    #[deref_mut]
    _message: MessageWithSignature,
    hash: H256,
    sender: H160,
}

impl TryFrom<MessageWithSignature> for Transaction {
    type Error = anyhow::Error;

    fn try_from(msg: MessageWithSignature) -> Result<Self, Self::Error> {
        let hash = msg.hash();
        let sender = msg.recover_sender()?;
        Ok(Self {
            _message: msg,
            hash,
            sender,
        })
    }
}

pub type Nonce = u64;
type PeerId = H512;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QueuedTransaction {
    sender: H160,
    hash: H256,
    nonce: Nonce,
    gas: U256,
}

impl<'a> From<&'a Transaction> for QueuedTransaction {
    fn from(msg: &'a Transaction) -> Self {
        Self {
            sender: msg.sender,
            hash: msg.hash,
            nonce: msg.nonce(),
            gas: msg.max_priority_fee_per_gas(),
        }
    }
}

impl Ord for QueuedTransaction {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.nonce == other.nonce {
            self.gas.cmp(&other.gas).reverse()
        } else {
            self.nonce.cmp(&other.nonce)
        }
    }
}

impl PartialOrd for QueuedTransaction {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

pub struct SubPool {
    local: DashMap<H256, Transaction>,
    remote: DashMap<H256, Transaction>,
}

impl SubPool {
    pub fn new() -> Self {
        Self {
            local: Default::default(),
            remote: Default::default(),
        }
    }

    pub fn insert(&self, tx: Transaction, local: bool) {
        if local {
            self.local.insert(tx.hash, tx);
        } else {
            self.remote.insert(tx.hash, tx);
        }
    }

    pub fn remove(&self, hash: &H256) -> Option<(H256, Transaction)> {
        if let Some((hash, tx)) = self.local.remove(hash) {
            Some((hash, tx))
        } else {
            self.remote.remove(hash)
        }
    }

    pub fn get(&self, hash: &H256) -> Option<Transaction> {
        self.local
            .get(hash)
            .or_else(|| self.remote.get(hash))
            .map(|ref_multi| ref_multi.clone())
    }
}

pub struct Queues {
    base_fee: BinaryHeap<QueuedTransaction>,
    processable: BinaryHeap<QueuedTransaction>,
}

pub struct TransactionPool {
    node: Arc<Node>,

    pending_base_fee: AtomicU64,
    db: Arc<MdbxWithDirHandle<WriteMap>>,

    queues: Mutex<Queues>,

    all: SubPool,

    unprocessed_queue: Mutex<Vec<Transaction>>,
    unprocessed_hashes: DashSet<H256>,

    nonces: DashMap<H160, Nonce>,
}

impl TransactionPool {
    pub fn new(node: Arc<Node>) -> Self {
        todo!()
    }
}

impl TransactionPool {
    const TICK: Duration = Duration::from_millis(100);

    pub async fn run(self: Arc<Self>) {
        let tasks = TaskGroup::new();

        let mut chain_event_sub = self.node.chain_event.subscribe();

        tasks.spawn({
            let handler = self.clone();
            let mut ticker = tokio::time::interval(Self::TICK);

            async move {
                loop {
                    tokio::select! {
                        at = ticker.tick() => {
                            debug!("Ticked at={:?}, processing unprocessed transactions...", at);

                            // let mut queues = handler.queues.lock();
                            let pending_base_fee: U256 = handler.pending_base_fee.load(std::sync::atomic::Ordering::Relaxed).into();

                            let mut processable = BinaryHeap::new();
                            let mut unprocessable = BinaryHeap::new();

                            for msg in std::mem::take(&mut *handler.unprocessed_queue.lock()) {
                                handler.unprocessed_hashes.remove(&msg.hash);

                                let queued = QueuedTransaction::from(&msg);
                                handler.all.insert(msg, false);

                                if queued.gas > pending_base_fee {
                                    // TODO: check nonces.
                                    processable.push(queued);
                                } else {
                                    unprocessable.push(queued);
                                }
                            }

                            {
                                let mut queues = handler.queues.lock();
                                queues.base_fee.append(&mut unprocessable);
                                queues.processable.append(&mut processable);
                            }
                        }
                        Some(event) = chain_event_sub.recv() => {
                            // TODO: rebuild txpool.
                        }
                    }
                }

                Ok::<_, anyhow::Error>(())
            }
        });
        tasks.spawn({
            let handler = self.clone();

            async move {
                let mut stream = handler
                    .node
                    .stream_by_predicate([
                        grpc_sentry::MessageId::PooledTransactions66 as i32,
                        grpc_sentry::MessageId::Transactions66 as i32,
                    ])
                    .await;

                while let Some(message) = stream.next().await {
                    match message.msg {
                        Message::Transactions(transactions) => {
                            let mut transactions = transactions
                                .0
                                .into_iter()
                                .filter_map(|msg| {
                                    let msg: Transaction = msg.try_into().ok()?;
                                    if !handler.unprocessed_hashes.contains(&msg.hash) {
                                        Some(msg)
                                    } else {
                                        None
                                    }
                                })
                                .collect::<Vec<_>>();
                            handler.unprocessed_queue.lock().append(&mut transactions);
                        }
                        Message::PooledTransactions(pooled) => {
                            let mut transactions = pooled
                                .transactions
                                .into_iter()
                                .filter_map(|msg| {
                                    let msg: Transaction = msg.try_into().ok()?;
                                    if !handler.unprocessed_hashes.contains(&msg.hash) {
                                        Some(msg)
                                    } else {
                                        None
                                    }
                                })
                                .collect::<Vec<_>>();
                            handler.unprocessed_queue.lock().append(&mut transactions);
                        }
                        _ => continue,
                    }
                }
            }
        });
    }
}
