/**
 * Core IDBFS operations for browser-based transpilation
 *
 * Pure functions for working with Emscripten's IDBFS (IndexedDB Filesystem)
 * to enable ZIP file extraction, WASM transpilation, and output packaging.
 *
 * Following SOLID principles:
 * - Single Responsibility: Each function has one clear purpose
 * - Open/Closed: Functions are composable and extensible
 * - Dependency Inversion: Functions accept interfaces, not concrete types
 *
 * @module idbfs
 */

import JSZip from 'jszip';
import type {
  WASMModule,
  ExtractedFile,
  ExtractionProgressCallback,
  TranspilerOptions,
  isFSError,
} from './idbfs-types';

/**
 * IDBFS mount point in the virtual filesystem
 */
export const IDBFS_MOUNT_POINT = '/project';

/**
 * Default output directory for transpiled files
 */
export const OUTPUT_DIR = '/project/output';

/**
 * Mount IDBFS at the designated mount point
 *
 * Creates the mount point directory and mounts IDBFS, which provides
 * persistent storage backed by IndexedDB.
 *
 * @param module - WASM module with initialized filesystem
 * @throws Error if IDBFS is not available or mount fails
 */
export async function mountIDBFS(module: WASMModule): Promise<void> {
  // Check if FS.filesystems exists and has IDBFS
  // Note: Emscripten with -lidbfs.js should provide this, but the structure might vary
  if (!module.FS || !module.FS.filesystems) {
    throw new Error('Filesystem API not available in WASM module (FS.filesystems is undefined). Ensure WASM was built with FORCE_FILESYSTEM=1');
  }

  if (!module.FS.filesystems.IDBFS) {
    throw new Error('IDBFS filesystem not available in WASM module. Ensure WASM was built with -lidbfs.js');
  }

  try {
    // Create mount point if it doesn't exist
    const pathInfo = module.FS.analyzePath(IDBFS_MOUNT_POINT);
    if (!pathInfo.exists) {
      module.FS.mkdir(IDBFS_MOUNT_POINT);
    }

    // Mount IDBFS
    module.FS.mount(module.FS.filesystems.IDBFS, {}, IDBFS_MOUNT_POINT);

    // Load existing data from IndexedDB (if any)
    await syncIDBFS(module, true);
  } catch (error) {
    throw new Error(`Failed to mount IDBFS: ${error instanceof Error ? error.message : String(error)}`);
  }
}

/**
 * Unmount IDBFS and clean up
 *
 * @param module - WASM module with mounted IDBFS
 */
export function unmountIDBFS(module: WASMModule): void {
  try {
    const pathInfo = module.FS.analyzePath(IDBFS_MOUNT_POINT);
    if (pathInfo.exists) {
      module.FS.unmount(IDBFS_MOUNT_POINT);
    }
  } catch (error) {
    console.warn('Failed to unmount IDBFS:', error);
  }
}

/**
 * Synchronize IDBFS with IndexedDB
 *
 * @param module - WASM module with mounted IDBFS
 * @param populate - true to load from IndexedDB, false to save to IndexedDB
 * @returns Promise that resolves when sync is complete
 */
export async function syncIDBFS(module: WASMModule, populate: boolean): Promise<void> {
  return new Promise((resolve, reject) => {
    module.FS.syncfs(populate, (err) => {
      if (err) {
        reject(new Error(`IDBFS sync failed: ${err.message}`));
      } else {
        resolve();
      }
    });
  });
}

/**
 * Create directory recursively (like mkdir -p)
 *
 * Creates all parent directories as needed. Does not throw error
 * if directory already exists.
 *
 * @param path - Directory path to create
 * @param fs - Emscripten filesystem interface
 */
export function createDirectoryRecursive(path: string, fs: WASMModule['FS']): void {
  const parts = path.split('/').filter(p => p);
  let current = '';

  for (const part of parts) {
    current += '/' + part;
    try {
      fs.mkdir(current);
    } catch (error: unknown) {
      // Ignore EEXIST error (directory already exists)
      if (error instanceof Error && 'code' in error && error.code !== 'EEXIST') {
        throw error;
      }
    }
  }
}

/**
 * Extract ZIP file contents to IDBFS
 *
 * Extracts all files from a ZIP archive into the IDBFS virtual filesystem,
 * creating directory structures as needed.
 *
 * @param zipFile - ZIP file to extract
 * @param module - WASM module with mounted IDBFS
 * @param progressCallback - Optional callback for progress updates
 * @returns Array of extracted file paths (relative to mount point)
 * @throws Error if ZIP is invalid or extraction fails
 */
export async function extractZipToIDBFS(
  zipFile: File,
  module: WASMModule,
  progressCallback?: ExtractionProgressCallback
): Promise<string[]> {
  try {
    // Load and parse ZIP file
    const zip = await JSZip.loadAsync(zipFile);

    // Collect all file entries (skip directories)
    const fileEntries: Array<{ path: string; entry: JSZip.JSZipObject }> = [];
    zip.forEach((relativePath, zipEntry) => {
      if (!zipEntry.dir) {
        fileEntries.push({ path: relativePath, entry: zipEntry });
      }
    });

    if (fileEntries.length === 0) {
      throw new Error('ZIP file contains no files');
    }

    // Extract files in parallel
    const extractedFiles: ExtractedFile[] = await Promise.all(
      fileEntries.map(async ({ path, entry }) => {
        const content = await entry.async('uint8array');
        return {
          path,
          content,
          size: content.length,
        };
      })
    );

    // Write files to IDBFS
    const extractedPaths: string[] = [];
    for (let i = 0; i < extractedFiles.length; i++) {
      const { path, content } = extractedFiles[i];
      const fullPath = `${IDBFS_MOUNT_POINT}/${path}`;

      // Create parent directories
      const dir = fullPath.substring(0, fullPath.lastIndexOf('/'));
      if (dir && dir !== IDBFS_MOUNT_POINT) {
        createDirectoryRecursive(dir, module.FS);
      }

      // Write file
      module.FS.writeFile(fullPath, content);
      extractedPaths.push(path);

      // Report progress
      if (progressCallback) {
        progressCallback(i + 1, extractedFiles.length, path);
      }
    }

    // Persist to IndexedDB
    await syncIDBFS(module, false);

    return extractedPaths;
  } catch (error) {
    if (error instanceof Error) {
      throw new Error(`Failed to extract ZIP: ${error.message}`);
    }
    throw new Error('Failed to extract ZIP: Unknown error');
  }
}

/**
 * Build command-line arguments from transpiler options
 *
 * Converts high-level transpiler options into command-line arguments
 * for the WASM transpiler.
 *
 * @param options - Transpiler options
 * @param sourceDir - Source directory (default: /project/src)
 * @param outputDir - Output directory (default: /project/output)
 * @returns Array of command-line arguments
 */
export function buildTranspilerArgs(
  options: TranspilerOptions,
  sourceDir: string = `${IDBFS_MOUNT_POINT}/src`,
  outputDir: string = OUTPUT_DIR
): string[] {
  const args: string[] = [
    `--source-dir=${sourceDir}`,
    `--output-dir=${outputDir}`,
  ];

  // ACSL options
  if (options.generateACSL) {
    args.push('--generate-acsl');
    if (options.acslLevel) {
      args.push(`--acsl-level=${options.acslLevel}`);
    }
  }

  // Pragma once
  if (options.usePragmaOnce) {
    args.push('--use-pragma-once');
  }

  // Exceptions and RTTI
  if (options.enableExceptions === false) {
    args.push('--enable-exceptions=off');
  }

  if (options.enableRTTI === false) {
    args.push('--enable-rtti=off');
  }

  // Compiler flags separator
  args.push('--');

  // Target architecture (required for Clang)
  args.push('-target', 'x86_64-unknown-linux-gnu');

  // Include directories
  if (options.includeDirs) {
    options.includeDirs.forEach(dir => {
      args.push(`-I${dir}`);
    });
  } else {
    // Default include directory
    args.push(`-I${IDBFS_MOUNT_POINT}/include`);
  }

  // C++ standard
  const cppStd = options.cppStandard || 'c++17';
  args.push(`-std=${cppStd}`);

  // Additional flags
  if (options.additionalFlags) {
    args.push(...options.additionalFlags);
  }

  return args;
}

/**
 * List all files in output directory
 *
 * Recursively lists all files in the output directory,
 * excluding directories.
 *
 * @param module - WASM module with filesystem
 * @param outputDir - Output directory path (default: /project/output)
 * @returns Array of file paths (absolute paths)
 */
export function listOutputFiles(
  module: WASMModule,
  outputDir: string = OUTPUT_DIR
): string[] {
  const files: string[] = [];

  try {
    const pathInfo = module.FS.analyzePath(outputDir);
    if (!pathInfo.exists) {
      return files;
    }

    const entries = module.FS.readdir(outputDir);

    for (const entry of entries) {
      // Skip . and ..
      if (entry === '.' || entry === '..') {
        continue;
      }

      const fullPath = `${outputDir}/${entry}`;
      const stat = module.FS.stat(fullPath);

      if (stat.isFile()) {
        files.push(fullPath);
      } else if (stat.isDirectory()) {
        // Recursively list subdirectories
        files.push(...listOutputFiles(module, fullPath));
      }
    }
  } catch (error) {
    console.error('Error listing output files:', error);
  }

  return files;
}

/**
 * Create ZIP archive from output files
 *
 * Packages all transpiled output files into a downloadable ZIP archive.
 *
 * @param files - Array of file paths (absolute) to include in ZIP
 * @param module - WASM module with filesystem
 * @param baseDir - Base directory to strip from paths (default: /project/output)
 * @returns ZIP file as Blob
 */
export async function createOutputZip(
  files: string[],
  module: WASMModule,
  baseDir: string = OUTPUT_DIR
): Promise<Blob> {
  const zip = new JSZip();

  for (const filePath of files) {
    try {
      // Read file content
      const content = module.FS.readFile(filePath);

      // Calculate relative path
      const relativePath = filePath.startsWith(baseDir + '/')
        ? filePath.substring(baseDir.length + 1)
        : filePath.substring(filePath.lastIndexOf('/') + 1);

      // Add to ZIP
      zip.file(relativePath, content);
    } catch (error) {
      console.error(`Failed to add file to ZIP: ${filePath}`, error);
    }
  }

  // Generate ZIP blob
  return await zip.generateAsync({ type: 'blob' });
}

/**
 * Auto-detect source directory in extracted ZIP
 *
 * Attempts to find the main source directory by looking for common patterns:
 * - /project/src
 * - /project/source
 * - First directory containing .cpp files
 *
 * @param module - WASM module with filesystem
 * @returns Detected source directory path or default
 */
export function detectSourceDirectory(module: WASMModule): string {
  const candidates = [
    `${IDBFS_MOUNT_POINT}/src`,
    `${IDBFS_MOUNT_POINT}/source`,
    `${IDBFS_MOUNT_POINT}/Source`,
  ];

  // Check common directories first
  for (const candidate of candidates) {
    const pathInfo = module.FS.analyzePath(candidate);
    if (pathInfo.exists) {
      return candidate;
    }
  }

  // Search for first directory with C++ files
  try {
    const entries = module.FS.readdir(IDBFS_MOUNT_POINT);
    for (const entry of entries) {
      if (entry === '.' || entry === '..') {
        continue;
      }

      const fullPath = `${IDBFS_MOUNT_POINT}/${entry}`;
      const stat = module.FS.stat(fullPath);

      if (stat.isDirectory()) {
        const subEntries = module.FS.readdir(fullPath);
        const hasCppFiles = subEntries.some(f =>
          f.match(/\.(cpp|cxx|cc)$/i)
        );
        if (hasCppFiles) {
          return fullPath;
        }
      }
    }
  } catch (error) {
    console.warn('Error detecting source directory:', error);
  }

  // Default to /project/src
  return `${IDBFS_MOUNT_POINT}/src`;
}

/**
 * Clear IDBFS contents
 *
 * Removes all files and directories from the IDBFS mount point
 * and syncs to IndexedDB.
 *
 * @param module - WASM module with mounted IDBFS
 */
export async function clearIDBFS(module: WASMModule): Promise<void> {
  try {
    const entries = module.FS.readdir(IDBFS_MOUNT_POINT);

    for (const entry of entries) {
      if (entry === '.' || entry === '..') {
        continue;
      }

      const fullPath = `${IDBFS_MOUNT_POINT}/${entry}`;
      const stat = module.FS.stat(fullPath);

      if (stat.isFile()) {
        module.FS.unlink(fullPath);
      } else if (stat.isDirectory()) {
        // Recursively remove directory
        removeDirectoryRecursive(fullPath, module.FS);
      }
    }

    // Persist changes to IndexedDB
    await syncIDBFS(module, false);
  } catch (error) {
    console.error('Error clearing IDBFS:', error);
    throw new Error(`Failed to clear IDBFS: ${error instanceof Error ? error.message : String(error)}`);
  }
}

/**
 * Remove directory and all its contents recursively
 *
 * @param path - Directory path to remove
 * @param fs - Emscripten filesystem interface
 */
function removeDirectoryRecursive(path: string, fs: WASMModule['FS']): void {
  const entries = fs.readdir(path);

  for (const entry of entries) {
    if (entry === '.' || entry === '..') {
      continue;
    }

    const fullPath = `${path}/${entry}`;
    const stat = fs.stat(fullPath);

    if (stat.isFile()) {
      fs.unlink(fullPath);
    } else if (stat.isDirectory()) {
      removeDirectoryRecursive(fullPath, fs);
    }
  }

  fs.rmdir(path);
}

/**
 * Validate ZIP file structure
 *
 * Checks if ZIP contains expected C++ source files and structure.
 *
 * @param zipFile - ZIP file to validate
 * @returns Validation result with success flag and message
 */
export async function validateZipStructure(
  zipFile: File
): Promise<{ success: boolean; message: string; cppFileCount: number }> {
  try {
    const zip = await JSZip.loadAsync(zipFile);

    let cppFileCount = 0;
    let hasHeaders = false;

    zip.forEach((relativePath, zipEntry) => {
      if (zipEntry.dir) {
        return;
      }

      const fileName = relativePath.toLowerCase();
      if (fileName.match(/\.(cpp|cxx|cc)$/)) {
        cppFileCount++;
      } else if (fileName.match(/\.(h|hpp|hxx)$/)) {
        hasHeaders = true;
      }
    });

    if (cppFileCount === 0) {
      return {
        success: false,
        message: 'ZIP file contains no C++ source files (.cpp, .cxx, .cc)',
        cppFileCount: 0,
      };
    }

    return {
      success: true,
      message: `Found ${cppFileCount} C++ source file${cppFileCount > 1 ? 's' : ''}${hasHeaders ? ' and header files' : ''}`,
      cppFileCount,
    };
  } catch (error) {
    return {
      success: false,
      message: `Invalid ZIP file: ${error instanceof Error ? error.message : 'Unknown error'}`,
      cppFileCount: 0,
    };
  }
}
