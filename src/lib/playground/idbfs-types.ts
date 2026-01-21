/**
 * TypeScript type definitions for Emscripten WASM Module with IDBFS support
 *
 * These types define the interface for interacting with the WASM transpiler module
 * and its filesystem operations, specifically IDBFS (IndexedDB Filesystem).
 *
 * Following SOLID principles:
 * - Interface Segregation: Separate interfaces for different concerns
 * - Dependency Inversion: Code depends on these interfaces, not concrete WASM implementation
 */

/**
 * Emscripten File System error codes
 */
export interface FSError extends Error {
  code: string;
  errno: number;
}

/**
 * File system node statistics
 */
export interface FSStats {
  dev: number;
  ino: number;
  mode: number;
  nlink: number;
  uid: number;
  gid: number;
  rdev: number;
  size: number;
  atime: Date;
  mtime: Date;
  ctime: Date;
  blksize: number;
  blocks: number;
  isFile(): boolean;
  isDirectory(): boolean;
}

/**
 * Emscripten File System interface
 *
 * Provides low-level filesystem operations similar to POSIX
 */
export interface EmscriptenFS {
  /**
   * Create a directory
   * @param path - Directory path
   * @throws FSError with code 'EEXIST' if directory already exists
   */
  mkdir(path: string): void;

  /**
   * Remove a directory (must be empty)
   * @param path - Directory path
   */
  rmdir(path: string): void;

  /**
   * Read directory contents
   * @param path - Directory path
   * @returns Array of filenames (includes '.' and '..')
   */
  readdir(path: string): string[];

  /**
   * Write file with binary data
   * @param path - File path
   * @param data - File content as Uint8Array or string
   * @param opts - Write options
   */
  writeFile(path: string, data: Uint8Array | string, opts?: { encoding?: string }): void;

  /**
   * Read file as binary data
   * @param path - File path
   * @param opts - Read options
   * @returns File content as Uint8Array or string
   */
  readFile(path: string, opts?: { encoding?: string }): Uint8Array | string;

  /**
   * Get file/directory statistics
   * @param path - File or directory path
   * @returns File system statistics
   */
  stat(path: string): FSStats;

  /**
   * Check if path exists
   * @param path - File or directory path
   * @returns true if path exists
   */
  analyzePath(path: string): { exists: boolean; isRoot: boolean };

  /**
   * Mount a filesystem
   * @param type - Filesystem type (e.g., IDBFS)
   * @param opts - Mount options
   * @param mountpoint - Mount path
   */
  mount(type: FileSystemType, opts: Record<string, unknown>, mountpoint: string): void;

  /**
   * Unmount a filesystem
   * @param mountpoint - Mount path
   */
  unmount(mountpoint: string): void;

  /**
   * Synchronize IDBFS with IndexedDB
   * @param populate - true to load from IndexedDB, false to save to IndexedDB
   * @param callback - Completion callback with optional error
   */
  syncfs(populate: boolean, callback: (err: Error | null) => void): void;

  /**
   * Unlink (delete) a file
   * @param path - File path
   */
  unlink(path: string): void;

  /**
   * Available filesystem types
   */
  filesystems: {
    IDBFS: FileSystemType;
    MEMFS: FileSystemType;
    NODEFS: FileSystemType;
    WORKERFS: FileSystemType;
  };
}

/**
 * Filesystem type constructor
 */
export interface FileSystemType {
  new (): unknown;
}

/**
 * Console log entry with severity level
 */
export interface ConsoleLogEntry {
  timestamp: Date;
  level: 'info' | 'success' | 'error' | 'warn';
  message: string;
}

/**
 * Emscripten Module configuration and interface
 *
 * This is the main WASM module interface returned by the loader function
 */
export interface WASMModule {
  /**
   * File system interface
   */
  FS: EmscriptenFS;

  /**
   * Call main function with command-line arguments
   * @param args - Array of string arguments
   * @returns Exit code (0 for success, non-zero for error)
   * @throws ExitStatus exception with exit code
   */
  callMain(args: string[]): number;

  /**
   * Standard output handler
   * @param text - Output text
   */
  print?: (text: string) => void;

  /**
   * Standard error handler
   * @param text - Error text
   */
  printErr?: (text: string) => void;

  /**
   * Called when runtime is initialized and ready
   */
  onRuntimeInitialized?: () => void;

  /**
   * Whether to run main() automatically on load
   */
  noInitialRun?: boolean;

  /**
   * Pre-run functions to execute before main
   */
  preRun?: Array<() => void>;

  /**
   * Post-run functions to execute after main
   */
  postRun?: Array<() => void>;
}

/**
 * Configuration options for initializing the WASM module
 */
export interface WASMModuleConfig {
  /**
   * Whether to run main() automatically (should be false for transpiler)
   */
  noInitialRun?: boolean;

  /**
   * Standard output handler
   */
  print?: (text: string) => void;

  /**
   * Standard error handler
   */
  printErr?: (text: string) => void;

  /**
   * Callback when runtime is ready
   */
  onRuntimeInitialized?: () => void;
}

/**
 * WASM module factory function type
 *
 * This is the default export from cpptoc.js
 */
export type WASMModuleFactory = (config?: WASMModuleConfig) => Promise<WASMModule>;

/**
 * ACSL (ANSI/ISO C Specification Language) configuration
 *
 * Controls which ACSL features are generated in the transpiled code.
 * Each feature can be toggled independently.
 */
export interface ACSLConfig {
  /**
   * Generate statement-level ACSL annotations
   * Includes loop invariants, assertions, and statement contracts
   */
  statements?: boolean;

  /**
   * Generate type invariant annotations
   * Adds invariants for struct/class types
   */
  typeInvariants?: boolean;

  /**
   * Generate axiomatic definitions
   * Creates axiomatic blocks for mathematical properties
   */
  axiomatics?: boolean;

  /**
   * Generate ghost code for verification
   * Adds ghost variables and ghost code blocks
   */
  ghostCode?: boolean;

  /**
   * Generate behavior specifications
   * Adds named behavior contracts to functions
   */
  behaviors?: boolean;

  /**
   * Generate memory predicates
   * Includes allocable, freeable, block_length predicates
   */
  memoryPredicates?: boolean;
}

/**
 * Transpiler options for IDBFS-based transpilation
 */
export interface TranspilerOptions {
  /**
   * ACSL configuration
   * When any feature is enabled, ACSL generation is automatically enabled
   */
  acsl?: ACSLConfig;

  /**
   * ACSL annotation level (requires at least one ACSL feature enabled)
   * - Basic: Function contracts only (requires, ensures, assigns)
   * - Full: Function contracts + loop invariants + class invariants
   */
  acslLevel?: 'Basic' | 'Full';

  /**
   * ACSL output mode (requires at least one ACSL feature enabled)
   * - Inline: Annotations inline in generated C code
   * - Separate: Annotations in separate .acsl files
   */
  acslOutputMode?: 'Inline' | 'Separate';

  /**
   * @deprecated Use acsl config object instead
   * Kept for backwards compatibility
   */
  generateACSL?: boolean;

  /**
   * Use #pragma once instead of include guards
   */
  usePragmaOnce?: boolean;

  /**
   * Enable C++ exceptions
   */
  enableExceptions?: boolean;

  /**
   * Enable C++ RTTI (Run-Time Type Information)
   */
  enableRTTI?: boolean;

  /**
   * C++ standard version
   */
  cppStandard?: 'c++11' | 'c++14' | 'c++17' | 'c++20';

  /**
   * Additional include directories
   */
  includeDirs?: string[];

  /**
   * Additional compiler flags
   */
  additionalFlags?: string[];
}

/**
 * File entry extracted from ZIP
 */
export interface ExtractedFile {
  /**
   * Relative path within the ZIP
   */
  path: string;

  /**
   * File content as binary data
   */
  content: Uint8Array;

  /**
   * File size in bytes
   */
  size: number;
}

/**
 * Progress callback for ZIP extraction
 */
export type ExtractionProgressCallback = (current: number, total: number, fileName: string) => void;

/**
 * Transpilation status
 */
export type TranspilationStatus = 'idle' | 'mounting' | 'extracting' | 'transpiling' | 'packaging' | 'complete' | 'error';

/**
 * Transpilation state for React component
 */
export interface TranspilationState {
  status: TranspilationStatus;
  message: string;
  progress: number; // 0-100
  logs: ConsoleLogEntry[];
  exitCode: number | null;
  outputFiles: string[];
}

/**
 * ZIP upload mode state
 */
export interface ZipUploadState {
  /**
   * Selected ZIP file
   */
  file: File | null;

  /**
   * Whether ZIP has been extracted to IDBFS
   */
  isExtracted: boolean;

  /**
   * List of extracted files
   */
  extractedFiles: string[];

  /**
   * Transpiler options
   */
  options: TranspilerOptions;

  /**
   * Transpilation state
   */
  transpilation: TranspilationState;
}

/**
 * Exit status exception thrown by Module.callMain
 */
export interface ExitStatus extends Error {
  name: 'ExitStatus';
  status: number;
}

/**
 * Type guard for FSError
 */
export function isFSError(error: unknown): error is FSError {
  return (
    error instanceof Error &&
    'code' in error &&
    'errno' in error
  );
}

/**
 * Type guard for ExitStatus
 */
export function isExitStatus(error: unknown): error is ExitStatus {
  return (
    error instanceof Error &&
    error.name === 'ExitStatus' &&
    'status' in error
  );
}
