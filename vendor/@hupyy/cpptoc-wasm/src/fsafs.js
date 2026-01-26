/**
 * FSAFS - File System Access API Backend for Emscripten
 *
 * Bridges browser FileSystemHandle API to Emscripten's synchronous FS layer.
 * Requires Asyncify-compiled WASM.
 */

// Early validation - log immediately when this file loads
console.log('[FSAFS] File loaded at:', new Date().toISOString());
console.log('[FSAFS] typeof Asyncify:', typeof Asyncify);
console.log('[FSAFS] typeof FS:', typeof FS);
console.log('[FSAFS] typeof Module:', typeof Module);

// Check if running in browser
if (typeof window !== 'undefined') {
  console.log('[FSAFS] Running in browser context');
  console.log('[FSAFS] window.Asyncify:', typeof window.Asyncify);

  // Log Module exports when available
  if (typeof Module !== 'undefined') {
    console.log('[FSAFS] Module object available');
    console.log('[FSAFS] Module.Asyncify:', typeof Module.Asyncify);
    console.log('[FSAFS] Module.FS:', typeof Module.FS);
  } else {
    console.warn('[FSAFS] Module not yet available - will be available after WASM loads');
  }
}

const FSAFS = {
  //==========================================================================
  // MOUNT OPERATION
  //==========================================================================

  mount(mount) {
    console.log('[FSAFS mount] ========================================');
    console.log('[FSAFS mount] Starting mount operation');
    console.log('[FSAFS mount] Mountpoint:', mount.mountpoint);
    console.log('[FSAFS mount] Handle provided:', !!mount.opts?.handle);
    console.log('[FSAFS mount] Handle kind:', mount.opts?.handle?.kind);

    // mount.opts should contain { handle: FileSystemDirectoryHandle }
    if (!mount.opts || !mount.opts.handle) {
      console.error('[FSAFS mount] ERROR: No handle provided');
      throw new Error('FSAFS requires mount opts with handle property');
    }

    console.log('[FSAFS mount] Creating root node...');
    // Create root node with directory mode
    const root = FS.createNode(null, '/', 16384 | 511, 0);
    console.log('[FSAFS mount] Root node created:', root.id);

    // Critical: Set the operations on the node
    console.log('[FSAFS mount] Attaching node_ops and stream_ops...');
    root.node_ops = FSAFS.node_ops;
    root.stream_ops = FSAFS.stream_ops;

    // Attach the FileSystemDirectoryHandle
    console.log('[FSAFS mount] Attaching FileSystemDirectoryHandle...');
    root.handle = mount.opts.handle;
    root.mount = mount;

    console.log('[FSAFS mount] Mount complete!');
    console.log('[FSAFS mount] - Root ID:', root.id);
    console.log('[FSAFS mount] - Has handle:', !!root.handle);
    console.log('[FSAFS mount] - Has node_ops:', !!root.node_ops);
    console.log('[FSAFS mount] - Has stream_ops:', !!root.stream_ops);
    console.log('[FSAFS mount] ========================================');

    return root;
  },

  //==========================================================================
  // HELPER FUNCTIONS
  //==========================================================================

  getModeForHandle(handle, isDir) {
    // Mode bits: directory (16384) or file (32768), plus permissions (511 = 0777)
    const typeBits = isDir ? 16384 : 32768;
    const permBits = 511; // rwxrwxrwx
    return typeBits | permBits;
  },

  // Wrapper for async operations - converts Promise to synchronous call via Asyncify
  syncify(asyncFn) {
    const callStack = new Error().stack;
    console.log('[FSAFS syncify] ========================================');
    console.log('[FSAFS syncify] Called from:', callStack.split('\n')[2]);
    console.log('[FSAFS syncify] typeof Asyncify:', typeof Asyncify);
    console.log('[FSAFS syncify] typeof window.Asyncify:', typeof window?.Asyncify);
    console.log('[FSAFS syncify] typeof Module.Asyncify:', typeof Module?.Asyncify);

    // Try multiple sources for Asyncify
    const AsyncifyRef = Asyncify || window?.Asyncify || Module?.Asyncify;

    if (typeof AsyncifyRef === 'undefined') {
      console.error('[FSAFS syncify] CRITICAL: Asyncify not found!');
      console.error('[FSAFS syncify] Available globals:', Object.keys(window).filter(k => k.includes('sync')));
      console.error('[FSAFS syncify] Module keys:', Module ? Object.keys(Module).filter(k => k.includes('sync')) : 'Module undefined');
      throw new Error('FSAFS requires Asyncify. Compiled with -s ASYNCIFY=1. Check EXPORTED_RUNTIME_METHODS includes Asyncify');
    }

    console.log('[FSAFS syncify] Asyncify found, calling handleSleep...');
    console.log('[FSAFS syncify]   AsyncifyRef.currData:', AsyncifyRef.currData);
    console.log('[FSAFS syncify]   AsyncifyRef.asyncPromiseHandlers:', AsyncifyRef.asyncPromiseHandlers);

    let asyncError = null;
    let result;

    try {
      result = AsyncifyRef.handleSleep(wakeUp => {
        console.log('[FSAFS syncify]   Inside handleSleep callback, executing async function...');
        asyncFn()
          .then(asyncResult => {
            console.log('[FSAFS syncify]   Async operation succeeded, result:', asyncResult);
            console.log('[FSAFS syncify]   Calling wakeUp with result...');
            wakeUp(asyncResult);
            console.log('[FSAFS syncify]   wakeUp completed');
          })
          .catch(err => {
            console.error('[FSAFS syncify]   Async operation failed:', err);
            console.error('[FSAFS syncify]   Error stack:', err.stack);
            asyncError = err;
            console.log('[FSAFS syncify]   Calling wakeUp with null...');
            wakeUp(null);
            console.log('[FSAFS syncify]   wakeUp completed (error case)');
          });
      });
      console.log('[FSAFS syncify] handleSleep returned:', result);
    } catch (e) {
      console.error('[FSAFS syncify] EXCEPTION in handleSleep:', e);
      console.error('[FSAFS syncify] Exception name:', e.name);
      console.error('[FSAFS syncify] Exception message:', e.message);
      console.error('[FSAFS syncify] Exception stack:', e.stack);
      throw e;
    }

    // If there was an async error, throw it now (after Asyncify completes)
    if (asyncError) {
      console.error('[FSAFS syncify] Throwing async error that occurred during operation');
      throw asyncError;
    }

    console.log('[FSAFS syncify] Returning result:', result);
    console.log('[FSAFS syncify] ========================================');
    return result;
  },

  // Convert FileSystemHandle errors to POSIX errno
  handleError(err, operation) {
    console.error(`FSAFS ${operation} error:`, err.name, err.message);

    // Use numeric errno codes directly (POSIX standard values)
    if (err.name === 'NotFoundError') {
      throw new FS.ErrnoError(44); // ENOENT
    } else if (err.name === 'TypeMismatchError') {
      throw new FS.ErrnoError(31); // EISDIR
    } else if (err.name === 'NotAllowedError') {
      throw new FS.ErrnoError(2); // EACCES
    } else if (err.name === 'InvalidModificationError') {
      throw new FS.ErrnoError(55); // ENOTEMPTY
    } else if (err.name === 'NoModificationAllowedError') {
      throw new FS.ErrnoError(30); // EROFS
    } else {
      throw new FS.ErrnoError(29); // EIO
    }
  },

  //==========================================================================
  // NODE OPERATIONS
  //==========================================================================

  node_ops: {
    //------------------------------------------------------------------------
    // getattr - Get file/directory attributes (stat)
    //------------------------------------------------------------------------
    getattr(node) {
      // Verify node has handle
      if (!node.handle) {
        console.error('FSAFS getattr: node has no handle');
        throw new FS.ErrnoError(63); // ENOSR - No STREAM resources
      }

      let size = 0;
      let mtime = Date.now();
      let isDir = node.handle.kind === 'directory';

      if (!isDir) {
        // For files, we need to get the actual size
        const fileData = FSAFS.syncify(async () => {
          try {
            const file = await node.handle.getFile();
            return { size: file.size, mtime: file.lastModified };
          } catch (e) {
            console.error('FSAFS getattr: failed to get file data', e);
            return { size: 0, mtime: Date.now() };
          }
        });

        if (fileData) {
          size = fileData.size;
          mtime = fileData.mtime;
        }
      }

      return {
        dev: 1,
        ino: node.id,
        mode: FSAFS.getModeForHandle(node.handle, isDir),
        nlink: 1,
        uid: 0,
        gid: 0,
        rdev: 0,
        size: size,
        atime: new Date(mtime),
        mtime: new Date(mtime),
        ctime: new Date(mtime),
        blksize: 4096,
        blocks: Math.ceil(size / 512)
      };
    },

    //------------------------------------------------------------------------
    // lookup - Find child node by name
    //------------------------------------------------------------------------
    lookup(parent, name) {
      console.log(`[FSAFS lookup] parent=${parent.id}, name="${name}"`);
      console.log(`[FSAFS lookup] parent.handle:`, parent.handle);
      console.log(`[FSAFS lookup] parent.handle.kind:`, parent.handle?.kind);

      const result = FSAFS.syncify(async () => {
        console.log(`[FSAFS lookup async] Looking for "${name}" in parent handle`);

        // Try as file first, then directory
        try {
          const fileHandle = await parent.handle.getFileHandle(name);
          return { handle: fileHandle, isDir: false };
        } catch (e) {
          if (e.name === 'TypeMismatchError' || e.name === 'NotFoundError') {
            try {
              const dirHandle = await parent.handle.getDirectoryHandle(name);
              return { handle: dirHandle, isDir: true };
            } catch (e2) {
              return null;
            }
          }
          return null;
        }
      });

      if (!result) {
        throw new FS.ErrnoError(44);
      }

      const childNode = FS.createNode(parent, name, FSAFS.getModeForHandle(result.handle, result.isDir), 0);
      childNode.handle = result.handle;
      childNode.mount = parent.mount;
      return childNode;
    },

    //------------------------------------------------------------------------
    // readdir - List directory contents
    //------------------------------------------------------------------------
    readdir(node) {
      if (node.handle.kind !== 'directory') {
        throw new FS.ErrnoError(54);
      }

      const entries = FSAFS.syncify(async () => {
        const names = [];
        try {
          for await (const name of node.handle.keys()) {
            names.push(name);
          }
        } catch (e) {
          console.error('readdir error:', e);
        }
        return names;
      });

      return ['.', '..'].concat(entries || []);
    },

    //------------------------------------------------------------------------
    // mknod - Create file
    //------------------------------------------------------------------------
    mknod(parent, name, mode, dev) {
      const isDir = (mode & 61440) === 16384;  // S_IFDIR

      const handle = FSAFS.syncify(async () => {
        try {
          if (isDir) {
            return await parent.handle.getDirectoryHandle(name, { create: true });
          } else {
            return await parent.handle.getFileHandle(name, { create: true });
          }
        } catch (e) {
          FSAFS.handleError(e, 'mknod');
        }
      });

      if (!handle) {
        throw new FS.ErrnoError(29);
      }

      const node = FS.createNode(parent, name, mode, dev);
      node.handle = handle;
      node.mount = parent.mount;
      return node;
    },

    //------------------------------------------------------------------------
    // mkdir - Create directory
    //------------------------------------------------------------------------
    mkdir(parent, name, mode) {
      return FSAFS.node_ops.mknod(parent, name, mode | 16384, 0);
    },

    //------------------------------------------------------------------------
    // rmdir - Remove directory
    //------------------------------------------------------------------------
    rmdir(parent, name) {
      FSAFS.syncify(async () => {
        try {
          await parent.handle.removeEntry(name);
        } catch (e) {
          FSAFS.handleError(e, 'rmdir');
        }
      });
    },

    //------------------------------------------------------------------------
    // unlink - Remove file
    //------------------------------------------------------------------------
    unlink(parent, name) {
      FSAFS.syncify(async () => {
        try {
          await parent.handle.removeEntry(name);
        } catch (e) {
          FSAFS.handleError(e, 'unlink');
        }
      });
    },

    //------------------------------------------------------------------------
    // rename - Move/rename file or directory
    //------------------------------------------------------------------------
    rename(oldNode, newDir, newName) {
      // File System Access API doesn't have native rename
      // Must copy + delete for cross-directory moves
      // For same-directory rename, still no native support

      FSAFS.syncify(async () => {
        try {
          if (oldNode.handle.kind === 'file') {
            // Read old file
            const file = await oldNode.handle.getFile();
            const contents = await file.arrayBuffer();

            // Create new file
            const newHandle = await newDir.handle.getFileHandle(newName, { create: true });
            const writable = await newHandle.createWritable();
            await writable.write(contents);
            await writable.close();

            // Delete old file
            const oldParent = oldNode.parent;
            await oldParent.handle.removeEntry(oldNode.name);

            // Update node
            oldNode.handle = newHandle;
          } else {
            // Directory rename is more complex - would need recursive copy
            throw new Error('Directory rename not implemented');
          }
        } catch (e) {
          FSAFS.handleError(e, 'rename');
        }
      });
    },

    //------------------------------------------------------------------------
    // setattr - Set file attributes (chmod, truncate, etc.)
    //------------------------------------------------------------------------
    setattr(node, attr) {
      // Handle truncation
      if (attr.size !== undefined && node.handle.kind === 'file') {
        FSAFS.syncify(async () => {
          try {
            const writable = await node.handle.createWritable({ keepExistingData: true });
            await writable.truncate(attr.size);
            await writable.close();
          } catch (e) {
            FSAFS.handleError(e, 'setattr/truncate');
          }
        });
      }
      // Other attributes (mode, times) are not supported by File System Access API
    }
  },

  //==========================================================================
  // STREAM OPERATIONS (for open files)
  //==========================================================================

  stream_ops: {
    //------------------------------------------------------------------------
    // open - Open file stream
    //------------------------------------------------------------------------
    open(stream) {
      // Initialize stream state
      stream.fsafsState = {
        // Cache file content for reading (optional optimization)
        cachedFile: null,
        cachedArrayBuffer: null,
        // Track if we have pending writes
        dirty: false
      };
    },

    //------------------------------------------------------------------------
    // close - Close file stream
    //------------------------------------------------------------------------
    close(stream) {
      // Clean up cached state
      stream.fsafsState = null;
    },

    //------------------------------------------------------------------------
    // read - Read bytes from file
    //------------------------------------------------------------------------
    read(stream, buffer, offset, length, position) {
      const node = stream.node;

      if (node.handle.kind !== 'file') {
        throw new FS.ErrnoError(31);
      }

      const bytesRead = FSAFS.syncify(async () => {
        try {
          const file = await node.handle.getFile();

          // Don't read past end of file
          const actualLength = Math.min(length, file.size - position);
          if (actualLength <= 0) {
            return 0;
          }

          const slice = file.slice(position, position + actualLength);
          const arrayBuffer = await slice.arrayBuffer();
          const uint8Array = new Uint8Array(arrayBuffer);

          // Copy to output buffer
          buffer.set(uint8Array, offset);
          return uint8Array.length;
        } catch (e) {
          FSAFS.handleError(e, 'read');
        }
      });

      return bytesRead || 0;
    },

    //------------------------------------------------------------------------
    // write - Write bytes to file
    //------------------------------------------------------------------------
    write(stream, buffer, offset, length, position) {
      const node = stream.node;

      if (node.handle.kind !== 'file') {
        throw new FS.ErrnoError(31);
      }

      const bytesWritten = FSAFS.syncify(async () => {
        try {
          // Get current file content if writing in middle
          const file = await node.handle.getFile();
          let existingData = new Uint8Array(0);

          if (position > 0 || position + length < file.size) {
            existingData = new Uint8Array(await file.arrayBuffer());
          }

          // Create new content array
          const newSize = Math.max(existingData.length, position + length);
          const newData = new Uint8Array(newSize);

          // Copy existing data
          if (existingData.length > 0) {
            newData.set(existingData);
          }

          // Write new data at position
          const dataToWrite = buffer.subarray(offset, offset + length);
          newData.set(dataToWrite, position);

          // Write to file
          const writable = await node.handle.createWritable();
          await writable.write(newData);
          await writable.close();

          return length;
        } catch (e) {
          FSAFS.handleError(e, 'write');
        }
      });

      return bytesWritten || 0;
    },

    //------------------------------------------------------------------------
    // llseek - Seek to position
    //------------------------------------------------------------------------
    llseek(stream, offset, whence) {
      let position = offset;

      if (whence === 1) { // SEEK_CUR
        position += stream.position;
      } else if (whence === 2) { // SEEK_END
        const attr = FSAFS.node_ops.getattr(stream.node);
        position += attr.size;
      }

      if (position < 0) {
        throw new FS.ErrnoError(28);
      }

      return position;
    },

    //------------------------------------------------------------------------
    // allocate - Preallocate space (optional)
    //------------------------------------------------------------------------
    allocate(stream, offset, length) {
      // File System Access API doesn't support preallocation
      // This is a no-op
    },

    //------------------------------------------------------------------------
    // mmap - Memory map file (not supported)
    //------------------------------------------------------------------------
    mmap(stream, length, position, prot, flags) {
      throw new FS.ErrnoError(43);
    },

    //------------------------------------------------------------------------
    // msync - Sync memory map (not supported)
    //------------------------------------------------------------------------
    msync(stream, buffer, offset, length, mmapFlags) {
      throw new FS.ErrnoError(43);
    }
  }
};

// Export for use in module
if (typeof module !== 'undefined') {
  module.exports = FSAFS;
}
