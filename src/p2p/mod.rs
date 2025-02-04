pub mod node;
pub mod types;

pub mod collections {
    use crate::models::{BlockHeader, BlockNumber, H256};
    use ethnum::U256;
    use hashbrown::HashSet;
    use hashlink::LruCache;
    use std::borrow::Borrow;

    #[derive(Debug, PartialEq, Eq, Clone, Default, Hash)]
    pub struct Link {
        height: BlockNumber,
        hash: H256,
        parent_hash: H256,
    }

    type Depth = usize;
    type Ancestor = H256;

    #[derive(Debug)]
    pub struct Graph {
        head: Link,
        chains: LruCache<H256, (U256, Depth, Ancestor)>,
        reorged: bool,

        skip_list: LruCache<H256, HashSet<H256>>,
        raw: LruCache<H256, BlockHeader>,
        q: LruCache<H256, ()>,
    }

    impl Default for Graph {
        fn default() -> Self {
            Self::new()
        }
    }

    impl Graph {
        const CHAINS_CAP: usize = 1 << 8;
        const CACHE_CAP: usize = 3 << 16;

        pub fn new() -> Self {
            Self {
                head: Default::default(),
                chains: LruCache::new(Self::CHAINS_CAP),
                reorged: Default::default(),
                skip_list: LruCache::new(Self::CACHE_CAP),
                raw: LruCache::new(Self::CACHE_CAP),
                q: LruCache::new(Self::CACHE_CAP),
            }
        }

        #[inline]
        pub fn contains<K>(&mut self, key: K) -> bool
        where
            K: Borrow<H256>,
        {
            self.raw.contains_key(key.borrow())
        }

        #[inline]
        pub fn clear(&mut self) {
            self.raw.clear();
            self.skip_list.clear();
            self.chains.clear();
            self.q.clear();
        }

        #[inline]
        pub fn len(&self) -> usize {
            self.raw.len()
        }

        #[inline]
        pub fn is_empty(&self) -> bool {
            self.raw.is_empty()
        }

        #[inline]
        pub fn insert_with_hash(&mut self, hash: H256, header: BlockHeader) {
            if self.q.contains_key(&hash) {
                return;
            }

            self.skip_list
                .entry(header.parent_hash)
                .or_insert(HashSet::new())
                .insert(hash);
            self.raw.insert(hash, header);
            self.q.insert(hash, ());
        }

        #[inline]
        pub fn insert(&mut self, header: BlockHeader) {
            let hash = header.hash();
            self.insert_with_hash(hash, header);
        }

        pub fn dfs(&mut self) -> Option<H256> {
            let mut roots = HashSet::new();

            for (hash, _) in self.q.iter() {
                if !self.skip_list.contains_key(hash) && self.raw.contains_key(hash) {
                    roots.insert(*hash);
                }
            }
            if roots.is_empty() {
                return None;
            }

            for root in roots {
                let mut current = root;
                let mut td = U256::ZERO;
                let mut depth = 0;

                while let Some(header) = self.raw.get(&current) {
                    if self.chains.contains_key(&current) {
                        break;
                    }
                    td += header.difficulty;
                    current = header.parent_hash;
                    depth += 1;
                }
                self.chains.insert(root, (td, depth, current));
            }

            if let Some((head_hash, (_, _, ancestor_hash))) =
                self.chains.iter().max_by_key(|(_, (td, _, _))| *td)
            {
                self.reorged = self.head.hash != *ancestor_hash;

                let header = self.raw.get(head_hash).unwrap();

                self.head = Link {
                    height: header.number,
                    hash: *head_hash,
                    parent_hash: header.parent_hash,
                };
                Some(*head_hash)
            } else {
                None
            }
        }

        pub fn backtrack(&mut self, tail: &H256) -> Vec<(H256, BlockHeader)> {
            let cap = self
                .chains
                .remove(tail)
                .map(|(_, depth, _)| depth)
                .expect("Tail is not in the graph");
            let mut headers = Vec::with_capacity(cap);

            let mut current = *tail;
            while let Some(header) = self.raw.remove(&current) {
                self.skip_list.remove(&current);

                let parent_hash = header.parent_hash;
                headers.push((current, header));
                current = parent_hash;
            }
            headers.reverse();
            headers
        }
    }

    impl Extend<BlockHeader> for Graph {
        fn extend<T>(&mut self, iter: T)
        where
            T: IntoIterator<Item = BlockHeader>,
        {
            for header in iter {
                self.insert(header);
            }
        }
    }

    impl Extend<(H256, BlockHeader)> for Graph {
        fn extend<T>(&mut self, iter: T)
        where
            T: IntoIterator<Item = (H256, BlockHeader)>,
        {
            for (hash, header) in iter {
                self.insert_with_hash(hash, header);
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_max_td() {
            let mut graph = Graph::new();
            let mut parent_hash = H256::default();

            // We're starting from the forked chain.
            for number in (0..10u64).map(BlockNumber) {
                let header = BlockHeader {
                    parent_hash,
                    number,
                    difficulty: U256::from(10u64),
                    ..Default::default()
                };
                parent_hash = header.hash();
                graph.insert(header);
            }
            assert_eq!(graph.dfs().unwrap(), parent_hash);
            assert!(!graph.reorged);
            for number in (10..20u64).map(BlockNumber) {
                let header = BlockHeader {
                    parent_hash,
                    number,
                    difficulty: U256::from(10u64),
                    ..Default::default()
                };
                parent_hash = header.hash();
                graph.insert(header);
            }
            assert_eq!(graph.dfs().unwrap(), parent_hash);
            assert!(!graph.reorged);

            // Insert chain with higher difficulty.
            let mut canonical_parent_hash = H256::default();
            for number in (0..10u64).map(BlockNumber) {
                let header = BlockHeader {
                    parent_hash: canonical_parent_hash,
                    number,
                    difficulty: U256::from(1000 * 10u64),
                    ..Default::default()
                };
                canonical_parent_hash = header.hash();
                graph.insert(header);
            }

            // Insert more blocks from the forked chain.
            for number in (30..40u64).map(BlockNumber) {
                let header = BlockHeader {
                    parent_hash,
                    number,
                    difficulty: U256::from(10u64),
                    ..Default::default()
                };
                parent_hash = header.hash();
                graph.insert(header);
            }
            assert_eq!(graph.dfs().unwrap(), canonical_parent_hash);
            assert!(graph.reorged);

            let mut hash = H256::default();
            for number in (0..10).map(BlockNumber) {
                let header = BlockHeader {
                    parent_hash: hash,
                    number,
                    difficulty: U256::from(10000000000 * 10u64),
                    ..Default::default()
                };
                hash = header.hash();
                graph.insert(header);
            }
            assert_eq!(graph.dfs().unwrap(), hash);
            assert!(graph.reorged);
        }
    }
}
