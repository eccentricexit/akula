use super::{rlputil::*, *};
use crate::{crypto::keccak256, models::*, prefix_length, u256_to_h256, zeroless_view};
use anyhow::{bail, ensure, format_err, Context};
use arrayref::array_ref;
use arrayvec::ArrayVec;
use bytes::{BufMut, BytesMut};
use sha3::{Digest, Keccak256};
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::{Debug, Display},
};
use tracing::*;

fn uvarint(buf: &[u8]) -> Option<(u64, usize)> {
    let mut x = 0;
    let mut s = 0;
    for (i, b) in buf.iter().copied().enumerate() {
        if i == 10 {
            return None;
        }
        if b < 0x80 {
            if i == 9 && b > 1 {
                return None;
            }
            return Some(((x | b << s).into(), i + 1));
        }
        x |= (b & 0x7f) << s as u64;
        s += 7;
    }
    Some((0, 0))
}

fn encode_uvarint(out: &mut Vec<u8>, mut x: u64) {
    while x >= 0x80 {
        out.push(x as u8 | 0x80);
        x >>= 7;
    }
    out.push(x as u8);
}

fn encode_slice(out: &mut Vec<u8>, s: &[u8]) {
    encode_uvarint(out, s.len() as u64);
    out.extend_from_slice(s);
}

pub type AccountCellPayload = RlpAccount;
pub type StorageCellPayload = U256;

#[derive(Clone, Debug)]
pub struct Cell<K, V>
where
    K: AsRef<[u8]>,
{
    hash: Option<H256>,
    down_hashed_key: ArrayVec<u8, 64>,
    extension: ArrayVec<u8, 64>,
    payload: Option<(K, V)>,
}

impl<K, V> Default for Cell<K, V>
where
    K: AsRef<[u8]>,
{
    fn default() -> Self {
        Self {
            hash: Default::default(),
            down_hashed_key: Default::default(),
            extension: Default::default(),
            payload: Default::default(),
        }
    }
}

impl<K, V> Cell<K, V>
where
    K: AsRef<[u8]>,
{
    const fn compute_hash_len(&self) -> usize {
        KECCAK_LENGTH + 1
    }

    fn fill_from_upper_cell(&mut self, up_cell: Cell<K, V>, depth_increment: usize) {
        self.down_hashed_key.clear();
        if up_cell.down_hashed_key.len() > depth_increment {
            self.down_hashed_key
                .try_extend_from_slice(&up_cell.down_hashed_key[depth_increment..])
                .unwrap();
        }
        self.extension.clear();
        if up_cell.extension.len() > depth_increment {
            self.extension
                .try_extend_from_slice(&up_cell.extension[depth_increment..])
                .unwrap();
        }
        self.payload = up_cell.payload;

        self.hash = up_cell.hash;
    }

    fn fill_from_lower_cell(&mut self, low_cell: Cell<K, V>, pre_extension: &[u8], nibble: usize) {
        self.payload = low_cell.payload;

        self.hash = low_cell.hash;
        if self.hash.is_some() {
            if self.payload.is_none() {
                // Extension is related to branch node, we prepend it by preExtension | nibble
                self.extension.clear();
                self.extension.try_extend_from_slice(pre_extension).unwrap();
                self.extension.push(nibble as u8);
                self.extension
                    .try_extend_from_slice(&low_cell.extension)
                    .unwrap();
            } else {
                // Extension is related to a storage branch node, so we copy it upwards as is
                self.extension = low_cell.extension;
            }
        }
    }

    fn derive_hashed_keys(&mut self, depth: usize) -> anyhow::Result<()> {
        let mut extra_len = 0_usize;
        if self.payload.is_some() {
            extra_len = 64_usize
                .checked_sub(depth)
                .ok_or_else(|| format_err!("plain_key present at depth > 64"))?;
        }

        if extra_len > 0 {
            let orig = self.down_hashed_key.clone();
            while self.down_hashed_key.remaining_capacity() > 0 {
                self.down_hashed_key.push(0);
            }
            if !self.down_hashed_key.is_empty() {
                let dst = &mut self.down_hashed_key[extra_len..];
                let len = std::cmp::min(dst.len(), orig.len());
                dst[..len].copy_from_slice(&orig[..len]);
            }
            self.down_hashed_key.truncate(orig.len() + extra_len);
            if let Some((plain_key, _)) = &self.payload {
                let k = hash_key(plain_key.as_ref(), depth);
                self.down_hashed_key[..k.len()].copy_from_slice(&k[..]);
            }
        }

        Ok(())
    }
}

#[derive(Clone, Default, PartialEq)]
pub struct StoredCell<K> {
    pub field_bits: PartFlags,
    pub extension: Option<ArrayVec<u8, 64>>,
    pub plain_key: Option<K>,
    pub hash: Option<H256>,
}

impl<K> Debug for StoredCell<K>
where
    K: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CellPayload")
            .field("field_bits", &self.field_bits)
            .field("extension", &self.extension.as_ref().map(hex::encode))
            .field("plain_key", &self.plain_key)
            .field("hash", &self.hash)
            .finish()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct BranchData<K> {
    pub touch_map: BranchBitmap,
    pub after_map: BranchBitmap,
    pub payload: Vec<StoredCell<K>>,
}

impl<K> Default for BranchData<K> {
    fn default() -> Self {
        Self {
            touch_map: Default::default(),
            after_map: Default::default(),
            payload: Default::default(),
        }
    }
}

impl<K> BranchData<K> {
    // pub fn encode(&self) -> Vec<u8> {
    //     let mut out = Vec::with_capacity(2 + 2);

    //     out.extend_from_slice(&self.touch_map.0.to_be_bytes());
    //     out.extend_from_slice(&self.after_map.0.to_be_bytes());

    //     for payload in &self.payload {
    //         out.push(payload.field_bits);
    //         if let Some(extension) = &payload.extension {
    //             encode_slice(&mut out, &extension[..]);
    //         }
    //         if let Some(apk) = &payload.apk {
    //             encode_slice(&mut out, &apk[..]);
    //         }
    //         if let Some((addr, location)) = &payload.spk {
    //             let mut spk = [0; H160::len_bytes() + H256::len_bytes()];
    //             spk[..H160::len_bytes()].copy_from_slice(&addr.0);
    //             spk[H160::len_bytes()..].copy_from_slice(&location.0);
    //             encode_slice(&mut out, &spk[..]);
    //         }
    //         if let Some(h) = &payload.h {
    //             encode_slice(&mut out, &h[..]);
    //         }
    //     }

    //     out
    // }

    // pub fn decode(buf: &[u8], mut pos: usize) -> anyhow::Result<(Self, usize)> {
    //     fn extract_length(data: &[u8], mut pos: usize) -> anyhow::Result<(usize, usize)> {
    //         let (l, n) =
    //             uvarint(&data[pos..]).ok_or_else(|| format_err!("value overflow for len"))?;
    //         if n == 0 {
    //             bail!("buffer too small for len");
    //         }

    //         pos += n;

    //         let l = l as usize;

    //         if data.len() < pos + l {
    //             bail!("buffer too small for value");
    //         }

    //         Ok((pos, l))
    //     }

    //     ensure!(buf.len() >= pos + 4);
    //     let touch_map = BranchBitmap(u16::from_be_bytes(*array_ref!(buf, pos, 2)));
    //     pos += 2;

    //     let after_map = BranchBitmap(u16::from_be_bytes(*array_ref!(buf, pos, 2)));
    //     pos += 2;

    //     let mut payload = vec![];
    //     while buf.len() != pos {
    //         let field_bits = buf[pos];
    //         pos += 1;

    //         let mut extension = None;
    //         if field_bits & HASHEDKEY_PART != 0 {
    //             let l;
    //             (pos, l) = extract_length(buf, pos)?;

    //             if l > 0 {
    //                 let mut v = ArrayVec::new();
    //                 v.try_extend_from_slice(&buf[pos..pos + l])?;
    //                 extension = Some(v);
    //                 pos += l;
    //             }
    //         }

    //         let mut apk = None;
    //         if field_bits & ACCOUNT_PLAIN_PART != 0 {
    //             let l;
    //             (pos, l) = extract_length(buf, pos)?;

    //             if l > 0 {
    //                 ensure!(l == ADDRESS_LENGTH);
    //                 apk = Some(Address::from_slice(&buf[pos..pos + l]));
    //                 pos += l;
    //             }
    //         }

    //         let mut spk = None;
    //         if field_bits & STORAGE_PLAIN_PART != 0 {
    //             let l;
    //             (pos, l) = extract_length(buf, pos)?;

    //             if l > 0 {
    //                 ensure!(l == ADDRESS_LENGTH + KECCAK_LENGTH);
    //                 spk = Some((
    //                     Address::from_slice(&buf[pos..pos + ADDRESS_LENGTH]),
    //                     H256::from_slice(
    //                         &buf[pos + ADDRESS_LENGTH..pos + ADDRESS_LENGTH + KECCAK_LENGTH],
    //                     ),
    //                 ));
    //                 pos += l;
    //             }
    //         }

    //         let mut h = None;
    //         if field_bits & HASH_PART != 0 {
    //             let l;
    //             (pos, l) = extract_length(buf, pos)?;

    //             if l > 0 {
    //                 ensure!(l == KECCAK_LENGTH);
    //                 h = Some(H256::from_slice(&buf[pos..pos + KECCAK_LENGTH]));
    //                 pos += l;
    //             }
    //         }

    //         payload.push(CellPayload {
    //             field_bits,
    //             extension,
    //             apk,
    //             spk,
    //             h,
    //         });
    //     }

    //     Ok((
    //         Self {
    //             touch_map,
    //             after_map,
    //             payload,
    //         },
    //         pos,
    //     ))
    // }
}

pub trait State<K, V> {
    fn get_branch(&mut self, prefix: &[u8]) -> anyhow::Result<Option<BranchData<K>>>;
    fn get_payload(&mut self, key: &K) -> anyhow::Result<Option<V>>;
}

#[derive(Debug)]
struct CellRow<K, V>
where
    K: AsRef<[u8]>,
{
    /// Cells in this row
    cells: [Cell<K, V>; 16],
    /// Depth of cells in this row
    depth: usize,
    /// Whether there was a branch node in the database loaded in unfold
    branch_before: bool,
    /// Bitmap of cells that were either present before modification, or modified or deleted
    touch_map: BranchBitmap,
    /// Bitmap of cells that were present after modification
    after_map: BranchBitmap,
}

impl<K, V> Default for CellRow<K, V>
where
    K: AsRef<[u8]>,
{
    fn default() -> Self {
        Self {
            cells: Default::default(),
            depth: Default::default(),
            branch_before: Default::default(),
            touch_map: Default::default(),
            after_map: Default::default(),
        }
    }
}

#[derive(Debug)]
struct CellGrid<K, V>
where
    K: AsRef<[u8]>,
{
    /// Root cell of the tree
    root: Cell<K, V>,
    /// Rows of the grid correspond to the level of depth in the patricia tree
    /// Columns of the grid correspond to pointers to the nodes further from the root
    /// First 64 rows of this grid are for account trie, and next 64 rows are for storage trie
    rows: ArrayVec<CellRow<K, V>, 64>,
}

impl<K: AsRef<[u8]>, V> Default for CellGrid<K, V> {
    fn default() -> Self {
        Self {
            root: Default::default(),
            rows: Default::default(),
        }
    }
}

impl<K, V> CellGrid<K, V>
where
    K: AsRef<[u8]>,
{
    fn delete_row(&mut self, row: usize) {
        self.rows.truncate(row);
    }
    fn cell(&self, cell_position: Option<CellPosition>) -> &Cell<K, V> {
        if let Some(cell_position) = cell_position {
            &self.rows[cell_position.row as usize].cells[cell_position.col as usize]
        } else {
            &self.root
        }
    }

    fn cell_mut(&mut self, cell_position: Option<CellPosition>) -> &mut Cell<K, V> {
        if let Some(cell_position) = cell_position {
            &mut self.rows[cell_position.row as usize].cells[cell_position.col as usize]
        } else {
            &mut self.root
        }
    }
}

fn hash_key(plain_key: &[u8], hashed_key_offset: usize) -> ArrayVec<u8, 64> {
    let hash_buf = keccak256(plain_key).0;
    let mut hash_buf = &hash_buf[hashed_key_offset / 2..];
    let mut dest = ArrayVec::new();
    if hashed_key_offset % 2 == 1 {
        dest.push(hash_buf[0] & 0xf);
        hash_buf = &hash_buf[1..];
    }
    for c in hash_buf {
        dest.push((c >> 4) & 0xf);
        dest.push(c & 0xf);
    }

    dest
}

/// HexPatriciaHashed implements commitment based on patricia merkle tree with radix 16,
/// with keys pre-hashed by keccak256
#[derive(Debug)]
pub struct HexPatriciaHashed<'state, K, V, S>
where
    S: State<K, V>,
    K: AsRef<[u8]>,
{
    state: &'state mut S,

    grid: CellGrid<K, V>,
    /// Length of the key that reflects current positioning of the grid. It may be larger than number of active rows,
    /// if a account leaf cell represents multiple nibbles in the key
    /// For each row indicates which column is currently selected
    current_key: ArrayVec<u8, 128>,
    root_checked: bool, // Set to false if it is not known whether the root is empty, set to true if it is checked
    root_touched: bool,
    root_present: bool,
}

impl<'state, K, V, S> HexPatriciaHashed<'state, K, V, S>
where
    K: AsRef<[u8]> + Clone + Debug,
    V: fastrlp::Encodable + Clone + Debug,
    S: State<K, V>,
{
    pub fn new(state: &'state mut S) -> Self {
        Self {
            state,

            grid: Default::default(),
            current_key: Default::default(),
            root_checked: Default::default(),
            root_touched: Default::default(),
            root_present: Default::default(),
        }
    }

    pub fn process_updates(
        mut self,
        updates: impl IntoIterator<Item = K>,
    ) -> anyhow::Result<(H256, HashMap<Vec<u8>, BranchData<K>>)> {
        let mut branch_node_updates = HashMap::new();

        let mut changed_keys = BTreeMap::new();

        for plain_key in updates {
            let hashed_key = hash_key(&plain_key.as_ref(), 0);

            let mut v = ArrayVec::new();
            v.try_extend_from_slice(&hashed_key[..]).unwrap();
            changed_keys.insert(v, plain_key);
        }

        for (hashed_key, plain_key) in changed_keys {
            trace!(
                "plain_key={:?} hashed_key={:?}, current_key={:?}",
                hex::encode(plain_key.as_ref()),
                hex::encode(&hashed_key),
                hex::encode(&self.current_key),
            );

            // Keep folding until the current_key is the prefix of the key we modify
            while self.need_folding(&hashed_key[..]) {
                if let (Some(branch_node_update), update_key) = self.fold() {
                    branch_node_updates.insert(update_key, branch_node_update);
                }
            }

            // Now unfold until we step on an empty cell
            loop {
                let unfolding = self.need_unfolding(&hashed_key[..]);
                if unfolding == 0 {
                    break;
                }

                self.unfold(&hashed_key[..], unfolding)?;
            }

            // Update the cell
            if let Some(payload) = self.state.get_payload(&plain_key)? {
                self.update_cell(plain_key, hashed_key, payload);
            } else {
                self.delete_cell(hashed_key);
            }
        }

        // Folding everything up to the root
        while !self.grid.rows.is_empty() {
            if let (Some(branch_data), update_key) = self.fold() {
                branch_node_updates.insert(update_key, branch_data);
            }
        }

        Ok((
            H256::from_slice(&self.compute_cell_hash(None, 0)[1..]),
            branch_node_updates,
        ))
    }

    #[instrument(skip(self))]
    fn compute_cell_hash(&mut self, pos: Option<CellPosition>, depth: usize) -> ArrayVec<u8, 33> {
        let cell = self.grid.cell_mut(pos);
        if let Some((plain_key, value)) = cell.payload {
            cell.down_hashed_key.clear();
            cell.down_hashed_key
                .try_extend_from_slice(&*hash_key(plain_key.as_ref(), depth))
                .unwrap();
            cell.down_hashed_key.push(16); // Add terminator

            let mut value_rlp = BytesMut::new();
            value.encode(&mut value_rlp);
            trace!(
                "accountLeafHashWithKey for [{}]=>[{}]",
                hex::encode(&cell.down_hashed_key[..65 - depth]),
                hex::encode(&value_rlp)
            );
            return leaf_hash_with_key(
                &cell.down_hashed_key[..65 - depth],
                RlpEncodableBytes(&value_rlp),
            );
        }

        let mut buf = ArrayVec::new();
        buf.push(0x80 + 32);
        if !cell.extension.is_empty() {
            // Extension
            let cell_hash = cell.hash.expect("extension without hash");
            trace!(
                "extension hash for [{}]=>[{:?}]",
                hex::encode(&cell.extension),
                cell_hash
            );
            buf.try_extend_from_slice(&extension_hash(&cell.extension, cell_hash).0)
                .unwrap();
        } else if let Some(cell_hash) = cell.hash {
            buf.try_extend_from_slice(&cell_hash[..]).unwrap();
        } else {
            buf.try_extend_from_slice(&EMPTY_HASH[..]).unwrap();
        }

        trace!("computed cell hash {}", hex::encode(&buf));

        buf
    }

    #[instrument(skip_all, fields(root_checked = self.root_checked))]
    fn need_unfolding(&self, hashed_key: &[u8]) -> usize {
        let cell: &Cell<K, V>;
        let mut depth = 0_usize;
        if let Some((idx, row)) = self.grid.rows.iter().enumerate().rev().next() {
            let col = hashed_key[self.current_key.len()] as usize;
            cell = &row.cells[col];
            depth = row.depth;
            trace!(
                "cell ({}, {:x}), currentKey=[{}], depth={}, cell.h=[{:?}]",
                idx,
                col,
                hex::encode(&self.current_key[..]),
                depth,
                cell.hash
            );
        } else {
            trace!("root");
            cell = &self.grid.root;
            if cell.down_hashed_key.is_empty() && cell.hash.is_none() && !self.root_checked {
                // Need to attempt to unfold the root
                return 1;
            }
        }
        if hashed_key.len() <= depth {
            return 0;
        }
        if cell.down_hashed_key.is_empty() {
            if cell.hash.is_none() {
                // cell is empty, no need to unfold further
                return 0;
            } else {
                // unfold branch node
                return 1;
            }
        }
        let cpl = prefix_length(
            &hashed_key[depth..],
            &cell.down_hashed_key[..cell.down_hashed_key.len() - 1],
        );
        trace!(
            "cpl={}, cell.downHashedKey=[{}], depth={}, hashedKey[depth..]=[{}]",
            cpl,
            hex::encode(&cell.down_hashed_key[..]),
            depth,
            hex::encode(&hashed_key[depth..]),
        );
        let mut unfolding = cpl + 1;
        if depth < 64 && depth + unfolding > 64 {
            // This is to make sure that unfolding always breaks at the level where storage subtrees start
            unfolding = 64 - depth;
            trace!("adjusted unfolding={}", unfolding);
        }

        unfolding
    }

    #[instrument(skip(self))]
    fn unfold_branch_node(
        &mut self,
        row: usize,
        deleted: bool,
        depth: usize,
    ) -> anyhow::Result<()> {
        let branch_data = self
            .state
            .get_branch(&hex_to_compact(&self.current_key[..]))?;

        if !self.root_checked && self.current_key.is_empty() && branch_data.is_none() {
            // Special case - empty or deleted root
            self.root_checked = true;
            return Ok(());
        }

        let cell_row = &mut self.grid.rows[row];
        let branch_data =
            branch_data.ok_or_else(|| format_err!("branch data unexpectedly absent"))?;
        cell_row.branch_before = true;
        let bitmap = branch_data.touch_map;
        if deleted {
            // All cells come as deleted (touched but not present after)
            cell_row.after_map = Default::default();
            cell_row.touch_map = bitmap;
        } else {
            cell_row.after_map = bitmap;
            cell_row.touch_map = Default::default();
        }
        if bitmap.parts() != branch_data.payload.len() {
            bail!(
                "len mismatch {} != {}",
                bitmap.parts(),
                branch_data.payload.len()
            );
        }

        for (nibble, cell_payload) in bitmap.iter().zip(branch_data.payload.into_iter()) {
            let cell = &mut self.grid.rows[row].cells[nibble as usize];
            cell.down_hashed_key.clear();
            cell.extension.clear();
            if let Some(extension) = cell_payload.extension {
                cell.down_hashed_key
                    .try_extend_from_slice(&extension[..])
                    .unwrap();
                cell.extension = extension;
            }

            cell.payload = None;
            if let Some(plain_key) = cell_payload.plain_key {
                let value = self
                    .state
                    .get_payload(&plain_key)?
                    .ok_or_else(|| format_err!("should not be empty"))?;

                cell.payload = Some((plain_key, value));
            }

            cell.hash = cell_payload.hash;
            trace!(
                "cell ({}, {:x}) depth={}, hash=[{:?}], payload=[{:?}], ex=[{}]",
                row,
                nibble,
                depth,
                cell.hash,
                cell.payload,
                hex::encode(&cell.extension)
            );
            cell.derive_hashed_keys(depth)?;
        }

        Ok(())
    }

    #[instrument(skip(self, hashed_key), fields(hashed_key = &*hex::encode(hashed_key), active_rows=self.grid.rows.len()))]
    fn unfold(&mut self, hashed_key: &[u8], unfolding: usize) -> anyhow::Result<()> {
        let touched;
        let present;
        let mut up_depth = 0;
        let depth;
        let up_cell;
        if self.grid.rows.is_empty() {
            let root = self.grid.root;
            if self.root_checked && root.hash.is_none() && root.down_hashed_key.is_empty() {
                // No unfolding for empty root
                return Ok(());
            }
            up_cell = root.clone();
            touched = self.root_touched;
            present = self.root_present;
            trace!("root, touched={}, present={}", touched, present);
        } else {
            let (row_idx, row) = self.grid.rows.iter().enumerate().rev().next().unwrap();
            up_depth = row.depth;
            let col = hashed_key[up_depth - 1];
            up_cell = row.cells[col as usize].clone();
            touched = row.touch_map.has(col);
            present = row.after_map.has(col);
            trace!(
                "upCell ({}, {:x}), touched {}, present {}",
                row_idx,
                col,
                touched,
                present
            );
            self.current_key.push(col);
        };
        self.grid.rows.pop();
        self.grid.rows.push(CellRow::default());
        let (row_idx, row) = self.grid.rows.iter_mut().enumerate().rev().next().unwrap();
        if up_cell.down_hashed_key.is_empty() {
            depth = up_depth + 1;
            self.unfold_branch_node(row_idx, touched && !present, depth)?;
        } else if up_cell.down_hashed_key.len() >= unfolding {
            depth = up_depth + unfolding;
            let nibble = up_cell.down_hashed_key[unfolding - 1];
            if touched {
                row.touch_map = BranchBitmap::from_nibble(nibble);
            }
            if present {
                row.after_map = BranchBitmap::from_nibble(nibble);
            }
            let cell = &mut row.cells[nibble as usize];
            cell.fill_from_upper_cell(up_cell.clone(), unfolding);
            trace!("cell ({}, {:x}) depth={}", row_idx, nibble, depth);
            if unfolding > 1 {
                self.current_key
                    .try_extend_from_slice(&up_cell.down_hashed_key[..unfolding - 1])
                    .unwrap();
            }
        } else {
            // upCell.downHashedLen < unfolding
            depth = up_depth + up_cell.down_hashed_key.len();
            let nibble = *up_cell.down_hashed_key.last().unwrap();
            if touched {
                row.touch_map = BranchBitmap::from_nibble(nibble);
            }
            if present {
                row.after_map = BranchBitmap::from_nibble(nibble);
            }
            let cell = &mut row.cells[nibble as usize];
            cell.fill_from_upper_cell(up_cell.clone(), up_cell.down_hashed_key.len());
            trace!("cell ({}, {:x}) depth={}", row_idx, nibble, depth);
            if up_cell.down_hashed_key.len() > 1 {
                self.current_key
                    .try_extend_from_slice(
                        &up_cell.down_hashed_key[..up_cell.down_hashed_key.len() - 1],
                    )
                    .unwrap();
            }
        }
        row.depth = depth;

        Ok(())
    }

    fn need_folding(&self, hashed_key: &[u8]) -> bool {
        !hashed_key[..].starts_with(&self.current_key[..])
    }

    #[instrument(skip(self), fields(active_rows=self.grid.rows.len(), current_key=&*hex::encode(&self.current_key), touch_map=&*self.touch_map[self.active_rows - 1].to_string(), after_map=&*self.after_map[self.active_rows - 1].to_string()))]
    pub(crate) fn fold(&mut self) -> (Option<BranchData<K>>, Vec<u8>) {
        assert_ne!(self.grid.rows.len(), 0, "cannot fold - no active rows");
        // Move information to the row above
        let row = self.grid.rows.len() - 1;
        let mut col = 0;
        let mut up_depth = 0;
        let up_cell = if row == 0 {
            trace!("upcell is root");

            None
        } else {
            up_depth = self.grid.rows[row - 1].depth;
            col = self.current_key[up_depth - 1];

            trace!("upcell is ({} x {}), upDepth={}", row - 1, col, up_depth);

            Some(CellPosition {
                row: row - 1,
                col: col as usize,
            })
        };
        let depth = self.grid.rows[row].depth;
        let mut branch_data = None;

        let update_key = hex_to_compact(&self.current_key);
        trace!(
            "touch_map[{}]={}, after_map[{}]={}",
            row,
            self.grid.rows[row].touch_map,
            row,
            self.grid.rows[row].after_map,
        );

        let parts_count = self.grid.rows[row].after_map.parts();
        match parts_count {
            0 => {
                // Everything deleted
                if self.grid.rows[row].touch_map.parts() > 0 {
                    if row == 0 {
                        // Root is deleted because the tree is empty
                        self.root_touched = true;
                        self.root_present = false;
                    } else if up_depth == 64 {
                        // Special case - all storage items of an account have been deleted, but it does not automatically delete the account, just makes it empty storage
                        // Therefore we are not propagating deletion upwards, but turn it into a modification
                        self.touch_map[row - 1].add_nibble(col);
                    } else {
                        // Deletion is propagated upwards
                        self.touch_map[row - 1].add_nibble(col);
                        self.after_map[row - 1].remove_nibble(col);
                    }
                }
                let up_cell = self.grid.cell_mut(up_cell);
                up_cell.h = None;
                up_cell.apk = None;
                up_cell.spk = None;
                up_cell.extension.clear();
                up_cell.down_hashed_key.clear();
                if self.branch_before[row] {
                    let branch_data = branch_data.get_or_insert_with(BranchData::default);
                    branch_data.touch_map = self.touch_map[row];
                    branch_data.after_map.clear();
                }
                self.active_rows -= 1;
                if up_depth > 0 {
                    self.current_key.truncate(up_depth - 1);
                } else {
                    self.current_key.clear();
                }
            }
            1 => {
                // Leaf or extension node
                if self.touch_map[row].parts() != 0 {
                    // any modifications
                    if row == 0 {
                        self.root_touched = true;
                    } else {
                        // Modification is propagated upwards
                        self.touch_map[row - 1].add_nibble(col);
                    }
                }
                let nibble = self.after_map[row].0.trailing_zeros().try_into().unwrap();
                let low_cell = self
                    .grid
                    .grid_cell(CellPosition { row, col: nibble })
                    .clone();
                let up_cell = self.grid.cell_mut(up_cell);
                up_cell.extension.clear();
                up_cell.fill_from_lower_cell(low_cell, &self.current_key[up_depth..], nibble);

                // Delete if it existed
                if self.grid.rows[row].branch_before {
                    let branch_data = branch_data.get_or_insert_with(BranchData::default);
                    branch_data.touch_map = self.grid.rows[row].touch_map;
                    branch_data.after_map.clear();
                }
                self.grid.rows.pop();

                self.current_key.truncate(up_depth.saturating_sub(1));
            }
            _ => {
                // Branch node
                if self.touch_map[row].parts() != 0 {
                    // any modifications
                    if row == 0 {
                        self.root_touched = true
                    } else {
                        // Modification is propagated upwards
                        self.touch_map[row - 1].add_nibble(col);
                    }
                }
                let mut changed_and_present =
                    BranchBitmap(self.touch_map[row].0 & self.after_map[row].0);
                if !self.branch_before[row] {
                    // There was no branch node before, so we need to touch even the singular child that existed
                    self.touch_map[row].0 |= self.after_map[row].0;
                    changed_and_present.0 |= self.after_map[row].0;
                }
                // Calculate total length of all hashes
                let mut total_branch_len = 17 - parts_count as usize; // for every empty cell, one byte

                for nibble in self.grid.rows[row].after_map.iter() {
                    total_branch_len += self
                        .grid
                        .cell_mut(Some(CellPosition {
                            row,
                            col: nibble as usize,
                        }))
                        .compute_hash_len();
                }

                let mut b = BranchData {
                    touch_map: self.grid.rows[row].touch_map,
                    after_map: self.grid.rows[row].after_map,

                    ..Default::default()
                };

                let mut hasher = Keccak256::new();
                hasher.update(&rlputil::generate_struct_len(total_branch_len));

                let mut last_nibble = 0;

                for nibble in self.grid.rows[row].after_map.iter() {
                    for i in last_nibble..nibble {
                        hasher.update(&[0x80]);
                        trace!("{:x}: empty({},{:x})", i, row, i);
                    }
                    last_nibble = nibble + 1;
                    let cell_pos = CellPosition {
                        row,
                        col: nibble as usize,
                    };
                    {
                        let cell_hash = self.compute_cell_hash(Some(cell_pos), depth);
                        hasher.update(cell_hash);
                    }

                    if changed_and_present.has(nibble) {
                        let mut field_bits = 0_u8;

                        let cell = self.grid.cell_mut(Some(cell_pos));
                        if !cell.extension.is_empty() {
                            field_bits |= HASHEDKEY_PART;
                        }
                        if cell.payload.is_some() {
                            field_bits |= PLAINKEY_PART;
                        }
                        if cell.hash.is_some() {
                            field_bits |= HASH_PART;
                        }

                        b.payload.push(StoredCell {
                            field_bits,
                            extension: if !cell.extension.is_empty() {
                                Some(cell.extension.clone())
                            } else {
                                None
                            },
                            plain_key: cell.payload.as_ref().map(|(k, _)| k.clone()),
                            hash: cell.hash,
                        });
                    }
                }

                branch_data = Some(b);

                {
                    let mut i = last_nibble;
                    while i < 17 {
                        hasher.update(&[0x80]);
                        trace!("{:x}: empty({},{:x})", i, row, i);

                        i += 1;
                    }
                }

                let up_cell = self.grid.cell_mut(up_cell);
                up_cell.extension.truncate(depth - up_depth - 1);
                if !up_cell.extension.is_empty() {
                    up_cell.extension.clear();
                    up_cell
                        .extension
                        .try_extend_from_slice(&self.current_key[up_depth..])
                        .unwrap();
                }
                if depth < 64 {
                    up_cell.apk = None;
                }
                up_cell.spk = None;

                {
                    let h = H256::from_slice(&hasher.finalize()[..]);
                    trace!("}} [{:?}]", h);
                    up_cell.hash = Some(h);
                }

                self.active_rows -= 1;

                self.current_key.truncate(up_depth.saturating_sub(1));
            }
        }
        if let Some(branch_data) = branch_data.as_mut() {
            trace!(
                "update key: {}, branch_data: [{:?}]",
                hex::encode(compact_to_hex(&update_key)),
                branch_data
            );
        }
        (branch_data, update_key)
    }

    #[instrument(skip(self))]
    fn delete_cell(&mut self, hashed_key: ArrayVec<u8, 64>) {
        trace!("called");
        if let Some((row, cell_row)) = self.grid.rows.iter_mut().enumerate().rev().next() {
            if cell_row.depth < hashed_key[..].len() {
                trace!(
                    "Skipping spurious delete depth={}, hashed_key_len={}",
                    cell_row.depth,
                    hashed_key[..].len()
                );
                return;
            }
            let col = hashed_key[self.current_key.len()];
            cell_row.cells[col as usize] = None;
            if cell_row.after_map.has(col) {
                // Prevent "spurious deletions", i.e. deletion of absent items
                cell_row.touch_map.add_nibble(col);
                cell_row.after_map.remove_nibble(col);
                trace!("Setting ({}, {:x})", row, col);
            } else {
                trace!("Ignoring ({}, {:x})", row, col);
            }
        } else {
            self.grid.root = None;
            self.root_touched = true;
            self.root_present = false;
        }
    }

    #[instrument(skip(self, hashed_key), fields(hashed_key = &*hex::encode(&hashed_key)))]
    fn update_cell(&mut self, plain_key: K, hashed_key: ArrayVec<u8, 64>, payload: V) {
        trace!("called");
        let row = self.grid.rows.len().checked_sub(1).unwrap();
        let col = hashed_key[self.current_key.len()];
        let cell_row = &self.grid.rows[row];
        let cell = cell_row.cells[col as usize].as_mut().unwrap();
        cell_row.touch_map.add_nibble(col);
        cell_row.after_map.add_nibble(col);
        trace!(
            "Setting ({}, {:x}), touch_map[{}]={}, depth={}",
            row,
            col,
            row,
            cell_row.touch_map,
            cell_row.depth
        );
        if cell.down_hashed_key.is_empty() {
            cell.down_hashed_key
                .try_extend_from_slice(&hashed_key[cell_row.depth..])
                .unwrap();
            trace!(
                "set down_hashed_key=[{}]",
                hex::encode(&cell.down_hashed_key[..])
            );
        } else {
            trace!(
                "left down_hashed_key=[{}]",
                hex::encode(&cell.down_hashed_key[..])
            );
        }

        cell.plain_key = Some(plain_key);
        cell.payload = payload;
    }
}

type PartFlags = u8;

const HASHEDKEY_PART: PartFlags = 1;
const PLAINKEY_PART: PartFlags = 2;
const HASH_PART: PartFlags = 8;

fn make_compact_zero_byte(key: &[u8]) -> (u8, usize, usize) {
    let mut compact_zero_byte = 0_u8;
    let mut key_pos = 0_usize;
    let mut key_len = key.len();
    if has_term(key) {
        key_len -= 1;
        compact_zero_byte = 0x20;
    }
    let first_nibble = key.first().copied().unwrap_or(0);
    if key_len & 1 == 1 {
        compact_zero_byte |= 0x10 | first_nibble; // Odd: (1<<4) + first nibble
        key_pos += 1
    }

    (compact_zero_byte, key_pos, key_len)
}

fn has_term(s: &[u8]) -> bool {
    s.last().map(|&v| v == 16).unwrap_or(false)
}

/// Combines two `BranchData`, number 2 coming after (and potentially shadowing) number 1
fn merge_hex_branches<K>(old: BranchData<K>, new: BranchData<K>) -> anyhow::Result<BranchData<K>> {
    let mut merged = BranchData::default();

    let old_bitmap = old.touch_map.0 & old.after_map.0;
    let new_bitmap = new.touch_map.0 & new.after_map.0;

    merged.touch_map = BranchBitmap(old.touch_map.0 | new.touch_map.0);
    merged.after_map = new.after_map;

    {
        let mut bitset = old_bitmap | new_bitmap;
        let mut old_payload_iter = old.payload.into_iter();
        let mut new_payload_iter = new.payload.into_iter();
        while bitset != 0 {
            let bit = bitset & 0_u16.overflowing_sub(bitset).0;
            if new_bitmap & bit != 0 {
                // Add fields from new BranchData
                merged
                    .payload
                    .push(new_payload_iter.next().context("no payload2")?);
            }
            if old_bitmap & bit != 0 {
                // Add fields from old BranchData
                if (new.touch_map.0 & bit == 0) && (new.after_map.0 & bit != 0) {
                    merged
                        .payload
                        .push(old_payload_iter.next().context("no payload1")?);
                }
            }
            bitset ^= bit;
        }
    }

    Ok(merged)
}

#[instrument(skip(key), fields(key=&*hex::encode(key)))]
fn hex_to_compact(key: &[u8]) -> Vec<u8> {
    let (zero_byte, key_pos, key_len) = make_compact_zero_byte(key);
    let buf_len = key_len / 2 + 1; // always > 0
    let mut buf = vec![0; buf_len];
    buf[0] = zero_byte;

    let key = &key[key_pos..];
    let mut key_len = key.len();
    if has_term(key) {
        key_len -= 1;
    }

    let mut key_index = 0;
    let mut buf_index = 1;
    while key_index < key_len {
        if key_index == key_len - 1 {
            buf[buf_index] &= 0x0f
        } else {
            buf[buf_index] = key[key_index + 1]
        }
        buf[buf_index] |= key[key_index] << 4;

        key_index += 2;
        buf_index += 1;
    }

    buf
}

fn leaf_hash_with_key(key: &[u8], val: impl RlpSerializable) -> ArrayVec<u8, 33> {
    // Write key
    let (compact_len, (compact0, ni)) = if has_term(key) {
        (
            (key.len() - 1) / 2 + 1,
            if key.len() & 1 == 0 {
                (
                    48 + key[0], // Odd (1<<4) + first nibble
                    1,
                )
            } else {
                (32, 0)
            },
        )
    } else {
        (
            key.len() / 2 + 1,
            if key.len() & 1 == 1 {
                (
                    16 + key[0], // Odd (1<<4) + first nibble
                    1,
                )
            } else {
                (0, 0)
            },
        )
    };
    // Compute the total length of binary representation
    let (kp, kl) = if compact_len > 1 {
        (Some(0x80 + compact_len as u8), compact_len)
    } else {
        (None, 1)
    };
    complete_leaf_hash(kp, kl, compact_len, key, compact0, ni, val)
}

fn extension_hash(key: &[u8], hash: H256) -> H256 {
    // Compute the total length of binary representation
    // Write key
    let (compact_len, (compact0, mut ni)) = if has_term(key) {
        (
            (key.len() - 1) / 2 + 1,
            if key.len() & 1 == 0 {
                (
                    0x30 + key[0], // Odd: (3<<4) + first nibble
                    1,
                )
            } else {
                (0x20, 0)
            },
        )
    } else {
        (
            key.len() / 2 + 1,
            if key.len() & 1 == 1 {
                (
                    0x10 + key[0], // Odd: (1<<4) + first nibble
                    1,
                )
            } else {
                (0, 0)
            },
        )
    };
    let (kp, kl) = if compact_len > 1 {
        (Some(0x80 + compact_len as u8), compact_len)
    } else {
        (None, 1)
    };
    let total_len = if kp.is_some() { 1 } else { 0 } + kl + 33;

    let mut hasher = Keccak256::new();
    hasher.update(&generate_struct_len(total_len));
    if let Some(kp) = kp {
        hasher.update(&[kp]);
    }
    hasher.update(&[compact0]);
    if compact_len > 1 {
        for _ in 1..compact_len {
            hasher.update(&[key[ni] * 16 + key[ni + 1]]);
            ni += 2
        }
    }
    hasher.update(&[0x80 + KECCAK_LENGTH as u8]);
    hasher.update(&hash[..]);
    // Replace previous hash with the new one
    H256::from_slice(&hasher.finalize())
}

fn complete_leaf_hash(
    kp: Option<u8>,
    kl: usize,
    compact_len: usize,
    key: &[u8],
    compact0: u8,
    mut ni: usize,
    val: impl rlputil::RlpSerializable,
) -> ArrayVec<u8, 33> {
    let total_len = if kp.is_some() { 1 } else { 0 } + kl + val.double_rlp_len();
    let len_prefix = generate_struct_len(total_len);

    let mut buf = ArrayVec::new();

    let mut hasher = Keccak256::new();
    hasher.update(&len_prefix);
    if let Some(kp) = kp {
        hasher.update(&[kp]);
    }
    hasher.update(&[compact0]);
    for _ in 1..compact_len {
        hasher.update(&[key[ni] * 16 + key[ni + 1]]);
        ni += 2;
    }
    val.to_double_rlp(&mut hasher);
    buf.push(0x80 + KECCAK_LENGTH as u8);
    buf.try_extend_from_slice(&hasher.finalize()[..]).unwrap();

    buf
}
