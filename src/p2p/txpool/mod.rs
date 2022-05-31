#![allow(unreachable_code)]
use super::{node::Node, types::GetPooledTransactions};
use crate::{
    models::{MessageWithSignature, H160, H256, H512},
    p2p::types::{Message, PeerFilter},
};
use dashmap::{DashMap, DashSet};
use ethereum_interfaces::sentry as grpc_sentry;
use futures::stream::FuturesUnordered;
use hashbrown::HashSet;
use rand::Rng;
use std::{sync::Arc, time::Duration};
use task_group::TaskGroup;
use tokio_stream::StreamExt;
use tracing::*;

pub type Sender = H160;
pub type Nonce = u64;

type PeerId = H512;

#[derive(Debug, Clone, PartialEq, Eq)]
struct QueuedTransaction {
    sender: Sender,
    hash: H256,
    gas: u64,
}

impl Ord for QueuedTransaction {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.gas.cmp(&other.gas).reverse()
    }
}

impl PartialOrd for QueuedTransaction {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

pub struct TransactionPool {
    node: Arc<Node>,
    known: DashSet<H256>,
    transactions: DashMap<H256, MessageWithSignature>,
}

impl TransactionPool {
    pub fn new(node: Arc<Node>) -> Self {
        Self {
            node,
            known: DashSet::new(),
            transactions: DashMap::new(),
        }
    }
}

impl TransactionPool {
    async fn handle_peer_request(
        self: Arc<Self>,
        params: GetPooledTransactions,
        peer_id: H512,
    ) -> anyhow::Result<()> {
        let transactions = params
            .hashes
            .into_iter()
            .filter_map(|hash| {
                self.transactions
                    .get(&hash)
                    .map(|entry_ref| entry_ref.value().clone())
            })
            .collect::<Vec<_>>();
        self.node
            .send_pooled_transactions(params.request_id, transactions, PeerFilter::PeerId(peer_id))
            .await?;

        Ok(())
    }

    async fn make_batch_request(self: Arc<Self>) {
        let known_copy = self
            .known
            .iter()
            .map(|entry_ref| *entry_ref.key())
            .collect::<Vec<_>>();
        let batches: Vec<Vec<H256>> = known_copy.chunks(4).map(ToOwned::to_owned).collect();

        let sqrt_peers = self.node.sqrt_peers().await;

        let _ = batches
            .into_iter()
            .map(|batch| {
                tokio::spawn({
                    let handler = self.clone();
                    let request_id = rand::thread_rng().gen::<u64>();
                    async move {
                        handler
                            .node
                            .get_pooled_transactions(
                                request_id,
                                &batch,
                                PeerFilter::Random(sqrt_peers as u64),
                            )
                            .await?;
                        Ok::<(), anyhow::Error>(())
                    }
                })
            })
            .collect::<FuturesUnordered<_>>()
            .map(|_| ())
            .collect::<()>()
            .await;
    }

    pub async fn run(self: Arc<Self>) {
        let tasks = TaskGroup::new();

        tasks.spawn({
            let handler = self.clone();

            const PREDICATE: [i32; 1] = [grpc_sentry::MessageId::GetPooledTransactions66 as i32];

            async move {
                let mut stream = handler.node.stream_by_predicate(PREDICATE).await;

                while let Some(msg) = stream.next().await {
                    let peer_id = msg.peer_id;

                    if let Message::GetPooledTransactions(inner) = msg.msg {
                        tokio::spawn({
                            let handler = handler.clone();
                            async move {
                                handler.handle_peer_request(inner, peer_id).await?;
                                Ok::<_, anyhow::Error>(())
                            }
                        });
                    }
                }

                Ok::<_, anyhow::Error>(())
            }
        });

        tasks.spawn({
            let handler = self.clone();

            const PREDICATE: [i32; 1] =
                [grpc_sentry::MessageId::NewPooledTransactionHashes66 as i32];

            async move {
                let mut stream = handler.node.stream_by_predicate(PREDICATE).await;

                while let Some(msg) = stream.next().await {
                    if let Message::NewPooledTransactionHashes(hashes) = msg.msg {
                        let set = hashes.0.into_iter().collect::<HashSet<_>>();

                        for hash in set {
                            if !(handler.known.contains(&hash)
                                || handler.transactions.contains_key(&hash))
                            {
                                handler.known.insert(hash);
                            }
                        }
                    }
                }
            }
        });

        tasks.spawn({
            let handler = self.clone();

            const PREDICATE: [i32; 1] = [grpc_sentry::MessageId::PooledTransactions66 as i32];

            async move {
                let mut stream = handler.node.stream_by_predicate(PREDICATE).await;

                while let Some(msg) = stream.next().await {
                    if let Message::PooledTransactions(pooled) = msg.msg {
                        let set = pooled.transactions.into_iter().collect::<HashSet<_>>();

                        for msg in set {
                            let hash = msg.hash();

                            if !handler.transactions.contains_key(&hash) {
                                handler.known.remove(&hash);
                                handler.transactions.insert(hash, msg);
                            }
                        }
                    }
                }
            }
        });

        tasks.spawn({
            let handler = self.clone();

            const PREDICATE: [i32; 1] = [grpc_sentry::MessageId::Transactions66 as i32];

            async move {
                let mut stream = handler.node.stream_by_predicate(PREDICATE).await;

                while let Some(msg) = stream.next().await {
                    if let Message::Transactions(msgs) = msg.msg {
                        let msgs = msgs.0.into_iter().collect::<HashSet<_>>();

                        for msg in msgs {
                            let hash = msg.hash();

                            if !handler.transactions.contains_key(&hash) {
                                handler.known.remove(&hash);
                                //let _ = tx.send(msg.clone()).await;
                                handler.transactions.insert(hash, msg);
                            }
                        }
                    }
                }
            }
        });

        tasks.spawn({
            let handler = self.clone();

            async move {
                loop {
                    handler.clone().make_batch_request().await;

                    tokio::time::sleep(Duration::from_secs(10)).await;
                }

                Ok::<_, anyhow::Error>(())
            }
        });

        loop {
            info!(
                "known={} transactions={}",
                self.known.len(),
                self.transactions.len()
            );

            tokio::time::sleep(Duration::from_secs(10)).await;
        }
    }
}
