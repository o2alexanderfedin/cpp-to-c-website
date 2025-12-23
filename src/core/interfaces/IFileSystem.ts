/**
 * IFileSystem - File System Abstraction Interface
 *
 * Provides abstraction for file system operations to enable testing
 * and support multiple backends (File System Access API, mock filesystem, etc.)
 *
 * Following SOLID principles:
 * - Interface Segregation: Minimal, focused interface
 * - Dependency Inversion: High-level code depends on this abstraction
 */

/**
 * File information returned by traverseDirectory
 */
export interface FileInfo {
  /**
   * Full path to the file
   */
  path: string;

  /**
   * File system handle for the file (for File System Access API)
   */
  handle: FileSystemFileHandle;

  /**
   * File name without path
   */
  name: string;

  /**
   * Whether this is a directory
   */
  isDirectory: boolean;
}

/**
 * File system abstraction for reading, writing, and traversing files
 */
export interface IFileSystem {
  /**
   * Read content of a file
   * @param path - File path (absolute or relative)
   * @returns File content as string
   * @throws Error if file does not exist
   */
  readFile(path: string): Promise<string>;

  /**
   * Write content to a file
   * @param path - File path (absolute or relative)
   * @param content - Content to write
   * @throws Error if write fails
   */
  writeFile(path: string, content: string): Promise<void>;

  /**
   * Read directory contents (non-recursive)
   * @param path - Directory path
   * @returns Array of file/directory names in the directory
   */
  readDir(path: string): Promise<string[]>;

  /**
   * Check if file or directory exists
   * @param path - File or directory path
   * @returns true if exists, false otherwise
   */
  exists(path: string): Promise<boolean>;

  /**
   * Recursively traverse directory and return all files
   * @param dirHandle - Directory handle from File System Access API
   * @returns Array of FileInfo objects for all files in directory tree
   */
  traverseDirectory(dirHandle: FileSystemDirectoryHandle): Promise<FileInfo[]>;
}
