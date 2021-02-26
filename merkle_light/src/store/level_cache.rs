use std::fmt;
use std::fs::{remove_file, File, OpenOptions};
use std::io::{copy, Read, Seek, SeekFrom};
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

use anyhow::{Context, Result};
use memmap::MmapOptions;
use positioned_io::{ReadAt, WriteAt};
use rayon::iter::*;
use rayon::prelude::*;
use typenum::marker_traits::Unsigned;

use crate::hash::Algorithm;
use crate::merkle::{
    get_merkle_tree_cache_size, get_merkle_tree_leafs, get_merkle_tree_len, log2_pow2, next_pow2,
    Element,
};
use crate::store::{ExternalReader, Store, StoreConfig, BUILD_CHUNK_NODES};

use qiniu::service::storage::download::{qiniu_is_enable, reader_from_env};

use log::{trace, debug, warn};

use std::collections::HashMap;

use tempfile::tempfile;

// use backtrace::Backtrace;

struct MixFile {
    file: Option<File>,
    path: Option<String>,
    length: Option<u64>,
    last_bytes: Option<Vec<u8>>,
}

impl MixFile {
    fn native_exists(path: &PathBuf) -> bool {
        Path::new(&path).exists()
    }

    fn qiniu_open(path: &str, len: usize) -> std::io::Result<MixFile> {
        let r = reader_from_env(path).unwrap().read_last_bytes(len)?;
        trace!("read qiniu open {} {}", path, len);
        trace!("qiniu data {} {}", &r.1[0], &r.1[len - 1]);
        return Ok(MixFile {
            file: None,
            path: Some(path.to_string()),
            length: Some(r.0),
            last_bytes: Some(r.1),
        });
    }

    fn open<P: AsRef<Path>>(path: P) -> std::io::Result<MixFile> {
        let f = File::open(path)?;
        return Ok(MixFile {
            length: Some(f.metadata().unwrap().len()),
            file: Some(f),
            path: None,
            last_bytes: None,
        });
    }

    fn open_with_create<P: AsRef<Path>>(path: P) -> std::io::Result<MixFile> {
        let f = OpenOptions::new()
            .write(true)
            .read(true)
            .create_new(true)
            .open(path)?;
        Ok(MixFile {
            file: Some(f),
            path: None,
            length: None,
            last_bytes: None,
        })
    }

    fn open_with_write<P: AsRef<Path>>(path: P) -> std::io::Result<MixFile> {
        let f = OpenOptions::new().read(true).write(true).open(path)?;
        Ok(MixFile {
            file: Some(f),
            path: None,
            length: None,
            last_bytes: None,
        })
    }

    fn open_temp() -> std::io::Result<MixFile> {
        Ok(MixFile {
            file: Some(tempfile()?),
            path: None,
            last_bytes: None,
            length: None,
        })
    }

    fn len(&self) -> usize {
        if self.length.is_some() {
            return self.length.unwrap() as usize;
        }
        if self.file.is_some() {
            return self.file.as_ref().unwrap().metadata().unwrap().len() as usize;
        }
        warn!("call file len fall");
        return 0;
    }

    fn read_exact_at(&self, pos: u64, buf: &mut [u8]) -> std::io::Result<()> {
        if self.file.is_some() {
            return self.file.as_ref().unwrap().read_exact_at(pos, buf);
        }

        trace!(
            "read path {:?} at {} size {} f len {:?} {} ",
            self.path,
            pos,
            buf.len(),
            self.length,
            self.last_bytes.is_some()
        );

        if self.length.is_some() && self.last_bytes.is_some() {
            let l = self.length.unwrap() as i64;
            let data = self.last_bytes.as_ref().unwrap();
            let start = pos as i64 - (l - data.len() as i64);
            let end = start as usize + buf.len();
            trace!("start is {} end {}", start, end);
            trace!("data size {} {}", buf.len(), data.len());
            if start >= 0 {
                buf.copy_from_slice(&data[(start as usize)..end]);
                return Ok(());
            }
        }
        let e2 = std::io::Error::new(std::io::ErrorKind::NotFound, "mixfile has no file");
        return Err(e2);
    }

    fn set_len(&self, size: u64) -> std::io::Result<()> {
        if self.file.is_some() {
            return self.file.as_ref().unwrap().set_len(size);
        }
        return Ok(());
    }

    fn seek(&mut self, pos: SeekFrom) -> std::io::Result<u64> {
        self.file.as_ref().unwrap().seek(pos)
    }

    fn sync_all(&self) -> std::io::Result<()> {
        self.file.as_ref().unwrap().sync_all()
    }

    fn write_all_at(&mut self, pos: u64, buf: &[u8]) -> std::io::Result<()> {
        self.file.as_mut().unwrap().write_all_at(pos, buf)
    }
}

impl std::io::Write for MixFile {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.file.as_ref().unwrap().write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        std::io::Write::flush(&mut self.file.as_ref().unwrap())
    }
}

/// The LevelCacheStore is used to reduce the on-disk footprint even
/// further to the minimum at the cost of build time performance.
/// Each LevelCacheStore is created with a StoreConfig object which
/// contains the number of binary tree levels above the base that are
/// 'cached'.  This implementation has hard requirements about the on
/// disk file size based on that number of levels, so on-disk files
/// are tied, structurally to the configuration they were built with
/// and can only be accessed with the same number of levels.
pub struct LevelCacheStore<E: Element, R: Read + Send + Sync> {
    len: usize,
    elem_len: usize,
    file: MixFile, // last tree file

    // The number of base layer data items.
    data_width: usize,

    // The byte index of where the cached data begins.
    cache_index_start: usize,

    // This flag is useful only immediate after instantiation, which
    // is false if the store was newly initialized and true if the
    // store was loaded from already existing on-disk data.
    loaded_from_disk: bool,

    // We cache the on-disk file size to avoid accessing disk
    // unnecessarily.
    store_size: usize,

    // If provided, the store will use this method to access base
    // layer data.
    reader: Option<ExternalReader<R>>, // remote storage

    _e: PhantomData<E>,
}

impl<E: Element, R: Read + Send + Sync> fmt::Debug for LevelCacheStore<E, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LevelCacheStore")
            .field("len", &self.len)
            .field("elem_len", &self.len)
            .field("data_width", &self.data_width)
            .field("loaded_from_disk", &self.loaded_from_disk)
            .field("cache_index_start", &self.cache_index_start)
            .field("store_size", &self.store_size)
            .finish()
    }
}

impl<E: Element, R: Read + Send + Sync> LevelCacheStore<E, R> {
    /// Used for opening v2 compacted DiskStores.
    pub fn new_from_disk_with_reader(
        store_range: usize,
        branches: usize,
        config: &StoreConfig,
        reader: ExternalReader<R>,
    ) -> Result<Self> {
        let data_path = StoreConfig::data_path(&config.path, &config.id);

        let file = MixFile::open(data_path)?;
        let store_size = file.len();
        debug!(
            "new_from_disk_with_reader > {} {} {}",
            store_range,
            store_size,
            E::byte_len()
        );
        // The LevelCacheStore base data layer must already be a
        // massaged next pow2 (guaranteed if created with
        // DiskStore::compact, which is the only supported method at
        // the moment).
        let size = get_merkle_tree_leafs(store_range, branches)?;
        ensure!(
            size == next_pow2(size),
            "Inconsistent merkle tree row_count detected"
        );

        // Values below in bytes.
        // Convert store_range from an element count to bytes.
        let store_range = store_range * E::byte_len();

        // LevelCacheStore on disk file is only the cached data, so
        // the file size dictates the cache_size.  Calculate cache
        // start and the updated size with repect to the file size.
        let cache_size =
            get_merkle_tree_cache_size(size, branches, config.rows_to_discard)? * E::byte_len();
        let cache_index_start = store_range - cache_size;

        // Sanity checks that the StoreConfig rows_to_discard matches this
        // particular on-disk file.  Since an external reader *is*
        // set, we check to make sure that the data on disk is *only*
        // the cached element data.
        ensure!(
            store_size == cache_size,
            "Inconsistent store size detected with external reader ({} != {})",
            store_size,
            cache_size,
        );

        Ok(LevelCacheStore {
            len: store_range / E::byte_len(),
            elem_len: E::byte_len(),
            file,
            data_width: size,
            cache_index_start,
            store_size,
            loaded_from_disk: false,
            reader: Some(reader),
            _e: Default::default(),
        })
    }

    pub fn set_external_reader(&mut self, reader: ExternalReader<R>) -> Result<()> {
        self.reader = Some(reader);

        Ok(())
    }
}

impl<E: Element, R: Read + Send + Sync> Store<E> for LevelCacheStore<E, R> {
    fn new_with_config_v2(
        size: usize,
        branches: usize,
        config: StoreConfig,
        post: bool,
    ) -> Result<Self> {
        let data_path = StoreConfig::data_path(&config.path, &config.id);

        // If the specified file exists, load it from disk.  This is
        // the only supported usage of this call for this type of
        // Store.
        if MixFile::native_exists(&data_path) {
            return Self::new_from_disk(size, branches, &config);
        }

        if qiniu_is_enable() && post {
            return Self::new_from_disk_v2(size, branches, &config, post);
        }

        // Otherwise, create the file and allow it to be the on-disk store.
        let file = MixFile::open_with_create(data_path)?;

        let store_size = E::byte_len() * size;
        let leafs = get_merkle_tree_leafs(size, branches)?;

        ensure!(
            leafs == next_pow2(leafs),
            "Inconsistent merkle tree row_count detected"
        );

        // Calculate cache start and the updated size with repect to
        // the data size.
        let cache_size =
            get_merkle_tree_cache_size(leafs, branches, config.rows_to_discard)? * E::byte_len();
        let cache_index_start = store_size - cache_size;

        file.set_len(store_size as u64)?;
        Ok(LevelCacheStore {
            len: 0,
            elem_len: E::byte_len(),
            file,
            data_width: leafs,
            cache_index_start,
            store_size,
            loaded_from_disk: false,
            reader: None,
            _e: Default::default(),
        })
    }

    fn new_with_config(size: usize, branches: usize, config: StoreConfig) -> Result<Self> {
        Self::new_with_config_v2(size, branches, config, false)
    }

    fn new(size: usize) -> Result<Self> {
        let store_size = E::byte_len() * size;
        let file = MixFile::open_temp()?;
        file.set_len(store_size as u64)?;
        Ok(LevelCacheStore {
            len: 0,
            elem_len: E::byte_len(),
            file,
            data_width: size,
            cache_index_start: 0,
            store_size,
            loaded_from_disk: false,
            reader: None,
            _e: Default::default(),
        })
    }

    fn new_from_slice_with_config(
        size: usize,
        branches: usize,
        data: &[u8],
        config: StoreConfig,
    ) -> Result<Self> {
        ensure!(
            data.len() % E::byte_len() == 0,
            "data size must be a multiple of {}",
            E::byte_len()
        );

        let mut store = Self::new_with_config(size, branches, config)?;

        // If the store was loaded from disk (based on the config
        // information, avoid re-populating the store at this point
        // since it can be assumed by the config that the data is
        // already correct).
        if !store.loaded_from_disk {
            store.store_copy_from_slice(0, data)?;
            store.len = data.len() / store.elem_len;
        }

        Ok(store)
    }

    fn new_from_slice(size: usize, data: &[u8]) -> Result<Self> {
        ensure!(
            data.len() % E::byte_len() == 0,
            "data size must be a multiple of {}",
            E::byte_len()
        );

        let mut store = Self::new(size)?;
        store.store_copy_from_slice(0, data)?;
        store.len = data.len() / store.elem_len;

        Ok(store)
    }

    // Used for opening v1 compacted DiskStores.
    fn new_from_disk(store_range: usize, branches: usize, config: &StoreConfig) -> Result<Self> {
        return Self::new_from_disk_v2(store_range, branches, config, false);
    }
    fn new_from_disk_v2(
        store_range: usize,
        branches: usize,
        config: &StoreConfig,
        post: bool,
    ) -> Result<Self> {
        let data_path = StoreConfig::data_path(&config.path, &config.id);
        let file = if post && qiniu_is_enable() {
            MixFile::qiniu_open(data_path.to_str().unwrap(), E::byte_len())?
        } else {
            MixFile::open(data_path)?
        };

        let store_size = file.len();

        // The LevelCacheStore base data layer must already be a
        // massaged next pow2 (guaranteed if created with
        // DiskStore::compact, which is the only supported method at
        // the moment).
        let size = get_merkle_tree_leafs(store_range, branches)?;
        ensure!(
            size == next_pow2(size),
            "Inconsistent merkle tree row_count detected"
        );

        // Values below in bytes.
        // Convert store_range from an element count to bytes.
        let store_range = store_range * E::byte_len();

        // Calculate cache start and the updated size with repect to
        // the data size.
        let cache_size =
            get_merkle_tree_cache_size(size, branches, config.rows_to_discard)? * E::byte_len();
        let cache_index_start = store_range - cache_size;

        // For a true v1 compatible store, this check should remain,
        // but since the store structure is identical otherwise this
        // method can be re-used to open v2 stores, so long as an
        // external_reader is set afterward.

        // Sanity checks that the StoreConfig rows_to_discard matches this
        // particular on-disk file.
        /*
        ensure!(
            store_size == size * E::byte_len() + cache_size,
            "Inconsistent store size detected"
        );
         */

        Ok(LevelCacheStore {
            len: store_range / E::byte_len(),
            elem_len: E::byte_len(),
            file,
            data_width: size,
            cache_index_start,
            loaded_from_disk: true,
            store_size,
            reader: None,
            _e: Default::default(),
        })
    }

    fn write_at(&mut self, el: E, index: usize) -> Result<()> {
        self.store_copy_from_slice(index * self.elem_len, el.as_ref())?;
        self.len = std::cmp::max(self.len, index + 1);

        Ok(())
    }

    fn copy_from_slice(&mut self, buf: &[u8], start: usize) -> Result<()> {
        ensure!(
            buf.len() % self.elem_len == 0,
            "buf size must be a multiple of {}",
            self.elem_len
        );
        self.store_copy_from_slice(start * self.elem_len, buf)?;
        self.len = std::cmp::max(self.len, start + buf.len() / self.elem_len);
        Ok(())
    }

    fn read_at_v2_range(
        &self,
        index: usize,
        pos: &mut (u64, u64),
        lstree: &mut HashMap<String, Vec<(u64, u64)>>,
    ) -> Result<()> {
        let start = index * self.elem_len;
        let end = start + self.elem_len;

        let len = self.len * self.elem_len;
        ensure!(start < len, "start out of range {} >= {}", start, len);
        ensure!(end <= len, "end out of range {} > {}", end, len);
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        self.store_read_range_v2_range(start, end, pos, lstree)
    }

    fn get_path_v2(&self) -> Option<String> {
        if self.reader.is_some() {
            return Some(self.reader.as_ref().unwrap().path.to_string());
        }
        return None;
    }

    fn read_at_v2(
        &self,
        index: usize,
        buf: &[u8],
        pos: &Vec<(u64, u64)>,
        lstree: &HashMap<&String, (Vec<u8>, Vec<(u64, u64)>, Option<std::io::Error>)>,
    ) -> Result<E> {
        let start = index * self.elem_len;
        let end = start + self.elem_len;

        let len = self.len * self.elem_len;
        ensure!(start < len, "start out of range {} >= {}", start, len);
        ensure!(end <= len, "end out of range {} > {}", end, len);
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        Ok(E::from_slice(
            &self.store_read_range_v2(start, end, buf, pos, lstree)?,
        ))
    }

    fn read_at(&self, index: usize) -> Result<E> {
        let start = index * self.elem_len;
        let end = start + self.elem_len;

        let len = self.len * self.elem_len;
        ensure!(start < len, "start out of range {} >= {}", start, len);
        ensure!(end <= len, "end out of range {} > {}", end, len);
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        Ok(E::from_slice(&self.store_read_range(start, end)?))
    }

    fn read_into(&self, index: usize, buf: &mut [u8]) -> Result<()> {
        let start = index * self.elem_len;
        let end = start + self.elem_len;

        let len = self.len * self.elem_len;
        ensure!(start < len, "start out of range {} >= {}", start, len);
        ensure!(end <= len, "end out of range {} > {}", end, len);
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        self.store_read_into(start, end, buf)
    }

    fn read_range_into(&self, start: usize, end: usize, buf: &mut [u8]) -> Result<()> {
        let start = start * self.elem_len;
        let end = end * self.elem_len;

        let len = self.len * self.elem_len;
        ensure!(start < len, "start out of range {} >= {}", start, len);
        ensure!(end <= len, "end out of range {} > {}", end, len);
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        self.store_read_into(start, end, buf)
    }

    fn read_range_into_v2(
        &self,
        start: usize,
        end: usize,
        buf: &mut [u8],
        data: &[u8],
        pos: &Vec<(u64, u64)>,
        lstree: &HashMap<&String, (Vec<u8>, Vec<(u64, u64)>, Option<std::io::Error>)>,
    ) -> Result<()> {
        let start = start * self.elem_len;
        let end = end * self.elem_len;

        let len = self.len * self.elem_len;
        ensure!(start < len, "start out of range {} >= {}", start, len);
        ensure!(end <= len, "end out of range {} > {}", end, len);
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        self.store_read_into_v2(start, end, buf, data, pos, lstree)
    }

    fn read_range_into_v2_range(
        &self,
        start: usize,
        end: usize,
        pos: &mut (u64, u64),
        lstree: &mut HashMap<String, Vec<(u64, u64)>>,
    ) -> Result<()> {
        let start = start * self.elem_len;
        let end = end * self.elem_len;

        let len = self.len * self.elem_len;
        ensure!(start < len, "start out of range {} >= {}", start, len);
        ensure!(end <= len, "end out of range {} > {}", end, len);
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        self.store_read_into_v2_range(start, end, pos, lstree)
    }

    fn read_range(&self, r: ops::Range<usize>) -> Result<Vec<E>> {
        let start = r.start * self.elem_len;
        let end = r.end * self.elem_len;

        let len = self.len * self.elem_len;
        ensure!(start < len, "start out of range {} >= {}", start, len);
        ensure!(end <= len, "end out of range {} > {}", end, len);
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        Ok(self
            .store_read_range(start, end)?
            .chunks(self.elem_len)
            .map(E::from_slice)
            .collect())
    }

    fn len(&self) -> usize {
        debug!("level cache len {}", self.len);
        self.len
    }

    fn loaded_from_disk(&self) -> bool {
        self.loaded_from_disk
    }

    fn compact(
        &mut self,
        _branches: usize,
        _config: StoreConfig,
        _store_version: u32,
    ) -> Result<bool> {
        bail!("Cannot compact this type of Store");
    }

    fn delete(config: StoreConfig) -> Result<()> {
        let path = StoreConfig::data_path(&config.path, &config.id);
        remove_file(&path).with_context(|| format!("Failed to delete {:?}", &path))
    }

    fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn push(&mut self, el: E) -> Result<()> {
        let len = self.len;
        ensure!(
            (len + 1) * self.elem_len <= self.store_size(),
            "not enough space, len: {}, E size {}, store len {}",
            len,
            self.elem_len,
            self.store_size()
        );

        self.write_at(el, len)
    }

    fn sync(&self) -> Result<()> {
        self.file.sync_all().context("failed to sync file")
    }

    #[allow(unsafe_code)]
    fn process_layer<A: Algorithm<E>, U: Unsigned>(
        &mut self,
        width: usize,
        level: usize,
        read_start: usize,
        write_start: usize,
    ) -> Result<()> {
        // Safety: this operation is safe because it's a limited
        // writable region on the backing store managed by this type.
        let mut mmap = unsafe {
            let mut mmap_options = MmapOptions::new();
            mmap_options
                .offset((write_start * E::byte_len()) as u64)
                .len(width * E::byte_len())
                .map_mut(&self.file.file.as_mut().unwrap())
        }?;

        let data_lock = Arc::new(RwLock::new(self));
        let branches = U::to_usize();
        let shift = log2_pow2(branches);
        let write_chunk_width = (BUILD_CHUNK_NODES >> shift) * E::byte_len();

        ensure!(BUILD_CHUNK_NODES % branches == 0, "Invalid chunk size");
        Vec::from_iter((read_start..read_start + width).step_by(BUILD_CHUNK_NODES))
            .into_par_iter()
            .zip(mmap.par_chunks_mut(write_chunk_width))
            .try_for_each(|(chunk_index, write_mmap)| -> Result<()> {
                let chunk_size = std::cmp::min(BUILD_CHUNK_NODES, read_start + width - chunk_index);

                let chunk_nodes = {
                    // Read everything taking the lock once.
                    data_lock
                        .read()
                        .unwrap()
                        .read_range_internal(chunk_index..chunk_index + chunk_size)?
                };

                let nodes_size = (chunk_nodes.len() / branches) * E::byte_len();
                let hashed_nodes_as_bytes = chunk_nodes.chunks(branches).fold(
                    Vec::with_capacity(nodes_size),
                    |mut acc, nodes| {
                        let h = A::default().multi_node(&nodes, level);
                        acc.extend_from_slice(h.as_ref());
                        acc
                    },
                );

                // Check that we correctly pre-allocated the space.
                let hashed_nodes_as_bytes_len = hashed_nodes_as_bytes.len();
                ensure!(
                    hashed_nodes_as_bytes.len() == chunk_size / branches * E::byte_len(),
                    "Invalid hashed node length"
                );

                write_mmap[0..hashed_nodes_as_bytes_len].copy_from_slice(&hashed_nodes_as_bytes);

                Ok(())
            })
    }

    // LevelCacheStore specific merkle-tree build.
    fn build<A: Algorithm<E>, U: Unsigned>(
        &mut self,
        leafs: usize,
        row_count: usize,
        config: Option<StoreConfig>,
    ) -> Result<E> {
        let branches = U::to_usize();
        ensure!(
            next_pow2(branches) == branches,
            "branches MUST be a power of 2"
        );
        ensure!(Store::len(self) == leafs, "Inconsistent data");
        ensure!(leafs % 2 == 0, "Leafs must be a power of two");
        ensure!(
            config.is_some(),
            "LevelCacheStore build requires a valid config"
        );

        // Process one `level` at a time of `width` nodes. Each level has half the nodes
        // as the previous one; the first level, completely stored in `data`, has `leafs`
        // nodes. We guarantee an even number of nodes per `level`, duplicating the last
        // node if necessary.
        let mut level: usize = 0;
        let mut width = leafs;
        let mut level_node_index = 0;

        let config = config.unwrap();
        let shift = log2_pow2(branches);

        // Both in terms of elements, not bytes.
        let cache_size = get_merkle_tree_cache_size(leafs, branches, config.rows_to_discard)?;
        let cache_index_start = (get_merkle_tree_len(leafs, branches)?) - cache_size;

        while width > 1 {
            // Start reading at the beginning of the current level, and writing the next
            // level immediate after.  `level_node_index` keeps track of the current read
            // starts, and width is updated accordingly at each level so that we know where
            // to start writing.
            let (read_start, write_start) = if level == 0 {
                // Note that we previously asserted that data.len() == leafs.
                (0, Store::len(self))
            } else if level_node_index < cache_index_start {
                (0, width)
            } else {
                (
                    level_node_index - cache_index_start,
                    (level_node_index + width) - cache_index_start,
                )
            };

            self.process_layer::<A, U>(width, level, read_start, write_start)?;

            if level_node_index < cache_index_start {
                self.front_truncate(&config, width)?;
            }

            level_node_index += width;
            level += 1;
            width >>= shift; // width /= branches;

            // When the layer is complete, update the store length
            // since we know the backing file was updated outside of
            // the store interface.
            self.set_len(level_node_index);
        }

        // Account for the root element.
        self.set_len(Store::len(self) + 1);
        // Ensure every element is accounted for.
        ensure!(
            Store::len(self) == get_merkle_tree_len(leafs, branches)?,
            "Invalid merkle tree length"
        );

        ensure!(row_count == level + 1, "Invalid tree row_count");
        // The root isn't part of the previous loop so `row_count` is
        // missing one level.

        // Return the root.  Note that the offset is adjusted because
        // we've just built a store that says that it has the full
        // length of elements, when in fact only the cached portion is
        // on disk.
        self.read_at_internal(self.len() - cache_index_start - 1)
    }
}

fn replica_range(start: usize, offset: usize, read_len: usize, pos: &mut (u64, u64)) -> Result<()> {
    let st_r = start + offset;
    pos.0 = st_r as u64;
    pos.1 = read_len as u64;
    return Ok(());
}

fn last_tree_range(adjusted_start: usize, read_len: usize,
                   s: &Option<String>, lstree: &mut HashMap<String, Vec<(u64, u64)>>) -> Result<()> {
    if s.is_none() {
        return Ok(());
    }
    let s1 = s.as_ref().unwrap();
    let last_ranges = lstree
        .entry(s1.to_string())
        .or_insert(Vec::with_capacity(10));
    last_ranges.push((adjusted_start as u64, read_len as u64));
    debug!(
        "last_tree_range {} {}",
        adjusted_start, read_len
    );
    return Ok(());
}

fn last_tree_copy(adjusted_start: usize, read_len: usize, buf: &mut [u8],
                  s: &Option<String>, lstree: &HashMap<&String, (Vec<u8>, Vec<(u64, u64)>, Option<std::io::Error>)>) -> Result<()> {
    let s1 = s.as_ref().unwrap();
    let t = lstree.get(s1);
    if t.is_none() {
        warn!("last tree not found {}", s1);
        let e2 = std::io::Error::new(std::io::ErrorKind::Interrupted, "no last tree file");
        return Err(e2.into());
    }

    debug!("last_tree_copy {}, {}", adjusted_start, read_len);
    let temp = t.unwrap();
    let pos = &temp.1;
    let data = &temp.0;
    let err = &temp.2;
    if err.is_some() {
        let ex = err.as_ref().unwrap();
        let e2 = std::io::Error::new(std::io::ErrorKind::Interrupted, ex.to_string());
        return Err(e2.into());
    }
    let r = copy_data(adjusted_start, read_len, buf, data, pos);
    if !r {
        warn!("last_tree_copy found no data {} {} {}", s1, adjusted_start, read_len);
        let e2 = std::io::Error::new(std::io::ErrorKind::Interrupted, "last_tree_copy found no data");
        return Err(e2.into());
    }
    return Ok(());
}

fn copy_data(start: usize, read_len: usize, buf: &mut [u8], data: &[u8], pos: &Vec<(u64, u64)>) -> bool {
    for (i, j) in pos {
        if (*i >> 24) as usize == start && (*i & 0xFFFFFF) as usize == read_len {
            debug!(
                "copy_data i-off is {} i-len is {}, j {}",
                *i >> 24,
                *i & 0xFFFFFF,
                j
            );
            let a = *j as usize;
            let b = *j as usize + read_len;
            buf.copy_from_slice(&data[a..b]);
            debug!(
                "copy_data data {} {} {} {}",
                buf[0],
                buf[1],
                buf[read_len - 1],
                buf[read_len - 2]
            );
            return true;
        }
    }
    return false;
}

impl<E: Element, R: Read + Send + Sync> LevelCacheStore<E, R> {
    pub fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    // Remove 'len' elements from the front of the file.
    pub fn front_truncate(&mut self, config: &StoreConfig, len: usize) -> Result<()> {
        let store_size = self.file.len();
        let len = (len * E::byte_len()) as u64;

        ensure!(store_size as u64 >= len, "Invalid truncation length");

        // Seek the reader past the length we want removed.
        let mut reader = OpenOptions::new()
            .read(true)
            .open(StoreConfig::data_path(&config.path, &config.id))?;
        reader.seek(SeekFrom::Start(len))?;

        // Make sure the store file is opened for read/write.
        self.file = MixFile::open_with_write(StoreConfig::data_path(&config.path, &config.id))?;

        // Seek the writer.
        self.file.seek(SeekFrom::Start(0))?;

        let written = copy(&mut reader, &mut self.file)?;
        ensure!(
            written == store_size as u64 - len,
            "Failed to copy all data"
        );

        self.file.set_len(written)?;
        Ok(())
    }

    pub fn store_size(&self) -> usize {
        self.store_size
    }

    // 'store_range' must be the total number of elements in the store (e.g. tree.len()).
    pub fn is_consistent_v1(
        store_range: usize,
        branches: usize,
        config: &StoreConfig,
    ) -> Result<bool> {
        let data_path = StoreConfig::data_path(&config.path, &config.id);

        let file = File::open(data_path)?;
        let metadata = file.metadata()?;
        let store_size = metadata.len() as usize;

        // The LevelCacheStore base data layer must already be a
        // massaged next pow2 (guaranteed if created with
        // DiskStore::compact, which is the only supported method at
        // the moment).
        let size = get_merkle_tree_leafs(store_range, branches)?;
        ensure!(
            size == next_pow2(size),
            "Inconsistent merkle tree row_count detected"
        );

        // Calculate cache start and the updated size with repect to
        // the data size.
        let cache_size =
            get_merkle_tree_cache_size(size, branches, config.rows_to_discard)? * E::byte_len();

        // Sanity checks that the StoreConfig rows_to_discard matches this
        // particular on-disk file.
        Ok(store_size == size * E::byte_len() + cache_size)
    }

    // Note that v2 is now the default compaction mode, so this isn't a versioned call.
    // 'store_range' must be the total number of elements in the store (e.g. tree.len()).
    pub fn is_consistent(
        store_range: usize,
        branches: usize,
        config: &StoreConfig,
    ) -> Result<bool> {
        let data_path = StoreConfig::data_path(&config.path, &config.id);

        let file = File::open(data_path)?;
        let metadata = file.metadata()?;
        let store_size = metadata.len() as usize;

        // The LevelCacheStore base data layer must already be a
        // massaged next pow2 (guaranteed if created with
        // DiskStore::compact, which is the only supported method at
        // the moment).
        let size = get_merkle_tree_leafs(store_range, branches)?;
        ensure!(
            size == next_pow2(size),
            "Inconsistent merkle tree row_count detected"
        );

        // LevelCacheStore on disk file is only the cached data, so
        // the file size dictates the cache_size.  Calculate cache
        // start and the updated size with repect to the file size.
        let cache_size =
            get_merkle_tree_cache_size(size, branches, config.rows_to_discard)? * E::byte_len();

        // Sanity checks that the StoreConfig rows_to_discard matches this
        // particular on-disk file.  Since an external reader *is*
        // set, we check to make sure that the data on disk is *only*
        // the cached element data.
        Ok(store_size == cache_size)
    }

    pub fn store_read_range_v2_range(
        &self,
        start: usize,
        end: usize,
        pos: &mut (u64, u64),
        lstree: &mut HashMap<String, Vec<(u64, u64)>>,
    ) -> Result<()> {
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );
        let read_len = end - start;
        let s = &self.file.path;
        let mut adjusted_start = start;

        debug!("store_read_range_v2_range {} {}", start, end);

        // If an external reader was specified for the base layer, use it.
        if start < self.data_width * self.elem_len && self.reader.is_some() {
            return replica_range(start, self.reader.as_ref().unwrap().offset, read_len, pos);
        }

        // Adjust read index if in the cached ranged to be shifted
        // over since the data stored is compacted.
        if start >= self.cache_index_start {
            let v1 = self.reader.is_none();
            adjusted_start = if v1 {
                start - self.cache_index_start + (self.data_width * self.elem_len)
            } else {
                start - self.cache_index_start
            };
        }
        last_tree_range(adjusted_start, read_len, s, lstree)
    }

    pub fn store_read_range_v2(
        &self,
        start: usize,
        end: usize,
        buf: &[u8],
        pos: &Vec<(u64, u64)>,
        lstree: &HashMap<&String, (Vec<u8>, Vec<(u64, u64)>, Option<std::io::Error>)>,
    ) -> Result<Vec<u8>> {
        let read_len = end - start;
        let mut read_data = vec![0; read_len];
        let mut adjusted_start = start;
        let s = &self.file.path;
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        // If an external reader was specified for the base layer, use it.
        if start < self.data_width * self.elem_len && self.reader.is_some() {
            if pos.len() > 0 {
                let offset = self.reader.as_ref().unwrap().offset;
                let st_r = start + offset;
                debug!(
                    "store_read_range_v2 {}, {}, {}, {}",
                    offset,
                    st_r,
                    read_len,
                    pos.len()
                );
                let r = copy_data(st_r, read_len, &mut *read_data, buf, pos);
                if !r {
                    warn!("store_read_range_v2 found no data {:?} {} {}", self.get_path_v2(), st_r, read_len);
                    let e2 = std::io::Error::new(std::io::ErrorKind::NotFound, "store_read_range_v2 no data");
                    return Err(e2.into());
                }
                return Ok(read_data);
            } else {
                self.reader
                    .as_ref()
                    .unwrap()
                    .read(start, end, &mut read_data)
                    .with_context(|| {
                        format!(
                            "failed to read {} bytes from file at offset {}",
                            end - start,
                            start
                        )
                    })?;
                return Ok(read_data);
            }
        }

        // Adjust read index if in the cached ranged to be shifted
        // over since the data stored is compacted.
        if start >= self.cache_index_start {
            let v1 = self.reader.is_none();
            adjusted_start = if v1 {
                start - self.cache_index_start + (self.data_width * self.elem_len)
            } else {
                start - self.cache_index_start
            };
        }

        if s.is_some() {
            let rx = last_tree_copy(adjusted_start, read_len, &mut read_data, s, lstree);
            if rx.is_ok() {
                return Ok(read_data);
            } else {
                return Err(rx.err().unwrap());
            }

        } else {
            self.file
                .read_exact_at(adjusted_start as u64, &mut read_data)
                .with_context(|| {
                    format!(
                        "failed to read {} bytes from file at offset {}",
                        read_len, start
                    )
                })?;
            Ok(read_data)
        }
    }

    pub fn store_read_range(&self, start: usize, end: usize) -> Result<Vec<u8>> {
        let read_len = end - start;
        let mut read_data = vec![0; read_len];
        let mut adjusted_start = start;

        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        // If an external reader was specified for the base layer, use it.
        if start < self.data_width * self.elem_len && self.reader.is_some() {
            self.reader
                .as_ref()
                .unwrap()
                .read(start, end, &mut read_data)
                .with_context(|| {
                    format!(
                        "failed to read {} bytes from file at offset {}",
                        end - start,
                        start
                    )
                })?;

            return Ok(read_data);
        }

        // Adjust read index if in the cached ranged to be shifted
        // over since the data stored is compacted.
        if start >= self.cache_index_start {
            let v1 = self.reader.is_none();
            adjusted_start = if v1 {
                start - self.cache_index_start + (self.data_width * self.elem_len)
            } else {
                start - self.cache_index_start
            };
        }

        self.file
            .read_exact_at(adjusted_start as u64, &mut read_data)
            .with_context(|| {
                format!(
                    "failed to read {} bytes from file at offset {}",
                    read_len, start
                )
            })?;

        Ok(read_data)
    }

    // This read is for internal use only during the 'build' process.
    fn store_read_range_internal(&self, start: usize, end: usize) -> Result<Vec<u8>> {
        let read_len = end - start;
        let mut read_data = vec![0; read_len];

        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        self.file
            .read_exact_at(start as u64, &mut read_data)
            .with_context(|| {
                format!(
                    "failed to read {} bytes from file at offset {}",
                    read_len, start
                )
            })?;

        Ok(read_data)
    }

    fn read_range_internal(&self, r: ops::Range<usize>) -> Result<Vec<E>> {
        let start = r.start * self.elem_len;
        let end = r.end * self.elem_len;

        let len = self.len * self.elem_len;
        ensure!(start < len, "start out of range {} >= {}", start, len);
        ensure!(end <= len, "end out of range {} > {}", end, len);
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        Ok(self
            .store_read_range_internal(start, end)?
            .chunks(self.elem_len)
            .map(E::from_slice)
            .collect())
    }

    fn read_at_internal(&self, index: usize) -> Result<E> {
        let start = index * self.elem_len;
        let end = start + self.elem_len;

        let len = self.len * self.elem_len;
        ensure!(start < len, "start out of range {} >= {}", start, len);
        ensure!(end <= len, "end out of range {} > {}", end, len);
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "out of bounds"
        );

        Ok(E::from_slice(&self.store_read_range_internal(start, end)?))
    }

    pub fn store_read_into_v2(
        &self,
        start: usize,
        end: usize,
        buf: &mut [u8],
        data: &[u8],
        pos: &Vec<(u64, u64)>,
        lstree: &HashMap<&String, (Vec<u8>, Vec<(u64, u64)>, Option<std::io::Error>)>,
    ) -> Result<()> {
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "Invalid read start"
        );
        let s = &self.file.path;
        let read_len = end - start;
        // If an external reader was specified for the base layer, use it.
        if start < self.data_width * self.elem_len && self.reader.is_some() {
            if pos.len() > 0 {
                let offset = self.reader.as_ref().unwrap().offset;
                let st_r = start + offset;

                debug!(
                    "store_read_into_v2 {}, {}, {}, {}",
                    offset,
                    st_r,
                    read_len,
                    pos.len()
                );
                let r = copy_data(st_r, read_len, buf, data, pos);
                if !r {
                    warn!("store_read_into_v2 not found data {:?} {} {}", self.get_path_v2(), start, read_len);
                    let e2 = std::io::Error::new(std::io::ErrorKind::NotFound, "store_read_into_v2 no data");
                    return Err(e2.into());
                }
                return Ok(());
            } else {
                self.reader
                    .as_ref()
                    .unwrap()
                    .read(start, end, buf)
                    .with_context(|| {
                        format!(
                            "failed to read {} bytes from file at offset {}",
                            end - start,
                            start
                        )
                    })?;
            }
        } else {
            // Adjust read index if in the cached ranged to be shifted
            // over since the data stored is compacted.
            let adjusted_start = if start >= self.cache_index_start {
                if self.reader.is_none() {
                    // if v1
                    start - self.cache_index_start + (self.data_width * self.elem_len)
                } else {
                    start - self.cache_index_start
                }
            } else {
                start
            };

            if s.is_some() {
                return last_tree_copy(adjusted_start, read_len, buf, s, lstree);
            }
            self.file
                .read_exact_at(adjusted_start as u64, buf)
                .with_context(|| {
                    format!(
                        "failed to read {} bytes from file at offset {}",
                        end - start,
                        start
                    )
                })?;
        }

        Ok(())
    }

    pub fn store_read_into_v2_range(
        &self,
        start: usize,
        end: usize,
        pos: &mut (u64, u64),
        lstree: &mut HashMap<String, Vec<(u64, u64)>>,
    ) -> Result<()> {
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "Invalid read start"
        );
        let s = &self.file.path;
        let read_len = end - start;
        debug!("store_read_into_v2_range {} {}", start, end);
        // If an external reader was specified for the base layer, use it.
        if start < self.data_width * self.elem_len && self.reader.is_some() {
            return replica_range(start, self.reader.as_ref().unwrap().offset, read_len, pos);
        }
        // Adjust read index if in the cached ranged to be shifted
        // over since the data stored is compacted.
        let adjusted_start = if start >= self.cache_index_start {
            if self.reader.is_none() {
                // if v1
                start - self.cache_index_start + (self.data_width * self.elem_len)
            } else {
                start - self.cache_index_start
            }
        } else {
            start
        };
        last_tree_range(adjusted_start, read_len, s, lstree)
    }

    pub fn store_read_into(&self, start: usize, end: usize, buf: &mut [u8]) -> Result<()> {
        ensure!(
            start <= self.data_width * self.elem_len || start >= self.cache_index_start,
            "Invalid read start"
        );

        // If an external reader was specified for the base layer, use it.
        if start < self.data_width * self.elem_len && self.reader.is_some() {
            self.reader
                .as_ref()
                .unwrap()
                .read(start, end, buf)
                .with_context(|| {
                    format!(
                        "failed to read {} bytes from file at offset {}",
                        end - start,
                        start
                    )
                })?;
        } else {
            // Adjust read index if in the cached ranged to be shifted
            // over since the data stored is compacted.
            let adjusted_start = if start >= self.cache_index_start {
                if self.reader.is_none() {
                    // if v1
                    start - self.cache_index_start + (self.data_width * self.elem_len)
                } else {
                    start - self.cache_index_start
                }
            } else {
                start
            };

            self.file
                .read_exact_at(adjusted_start as u64, buf)
                .with_context(|| {
                    format!(
                        "failed to read {} bytes from file at offset {}",
                        end - start,
                        start
                    )
                })?;
        }

        Ok(())
    }

    pub fn store_copy_from_slice(&mut self, start: usize, slice: &[u8]) -> Result<()> {
        ensure!(
            start + slice.len() <= self.store_size,
            "Requested slice too large (max: {})",
            self.store_size
        );
        self.file.write_all_at(start as u64, slice)?;

        Ok(())
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use std::{boxed::Box, error::Error, result::Result};
//     use std::env;
//
//
//     #[test]
//     fn test_last_read(){
//         env::set_var("QINIU", "/Users/long/projects/filecoin/goupload/sim.toml");
//         let p = "/Users/long/projects/filecoin/lotus/stdir/bench890193298/cache/s-t01000-1/sc-02-data-tree-r-last.dat";
//         let f = MixFile::qiniu_open(p, 64).unwrap();
//         let mut bytes = vec![0; 64];
//
//         let ret = f.read_exact_at(f.len() as u64 -64, &mut bytes);
//         assert!(ret.is_ok())
//     }
// }
