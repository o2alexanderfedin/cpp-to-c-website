/**
 * FileSystemAccessAdapter - File System Access API Implementation
 *
 * Implements IFileSystem interface using the browser's File System Access API.
 * Provides read/write access to local filesystem with permission management.
 *
 * Following SOLID principles:
 * - Single Responsibility: Only handles File System Access API interactions
 * - Liskov Substitution: Can replace any IFileSystem implementation
 * - Dependency Inversion: Implements IFileSystem abstraction
 *
 * Browser Support:
 * - Chrome 105+, Edge 105+, Opera 91+ (full support)
 * - Firefox, Safari: Not supported (requires fallback mechanisms)
 *
 * Security:
 * - Requires HTTPS (secure context)
 * - User-initiated file picker (no programmatic access)
 * - Permissions cleared when tabs close
 *
 * @see https://developer.mozilla.org/en-US/docs/Web/API/File_System_Access_API
 */

/// <reference path="../types/file-system-access-api.d.ts" />

import type { IFileSystem, FileInfo } from '../core/interfaces/IFileSystem';

/**
 * Adapter for File System Access API
 *
 * Implementation notes:
 * - This adapter uses internal Maps to store file/directory handles for testing
 * - In production, handles would be obtained via showDirectoryPicker(), showOpenFilePicker()
 * - Permissions are checked before each read/write operation
 * - Paths are normalized to ensure consistent behavior
 *
 * Future enhancements:
 * - Add browser-fs-access library for progressive enhancement
 * - Support drag-and-drop via DataTransferItem.getAsFileSystemHandle()
 * - Add IndexedDB integration for recent projects
 * - Implement recursive directory traversal
 */
export class FileSystemAccessAdapter implements IFileSystem {
  private readonly fileHandles: Map<string, FileSystemFileHandle> = new Map();
  private readonly directoryHandles: Map<string, FileSystemDirectoryHandle> = new Map();

  /**
   * Normalize path to consistent format
   * - Ensure leading slash
   * - Remove trailing slash
   * - Collapse multiple slashes
   */
  private normalizePath(path: string): string {
    // Ensure leading slash
    let normalized = path.startsWith('/') ? path : `/${path}`;

    // Remove trailing slash (except root)
    if (normalized.length > 1 && normalized.endsWith('/')) {
      normalized = normalized.slice(0, -1);
    }

    // Collapse multiple slashes
    normalized = normalized.replace(/\/+/g, '/');

    return normalized;
  }

  /**
   * Check and request permission for file/directory handle
   *
   * Implements the standard File System Access API permission flow:
   * 1. Query current permission status
   * 2. If not granted, request permission from user
   * 3. Throw error if permission denied
   *
   * @param handle - File or directory handle
   * @param mode - Permission mode ('read' or 'readwrite')
   * @param path - Path for error messages
   * @throws Error if permission is denied
   */
  private async checkPermission(
    handle: FileSystemHandle,
    mode: FileSystemPermissionMode,
    path: string
  ): Promise<void> {
    const options: FileSystemHandlePermissionDescriptor = { mode };

    // Check current permission status
    const permission = await handle.queryPermission(options);

    if (permission === 'granted') {
      return;
    }

    // Request permission if not already granted
    const requestedPermission = await handle.requestPermission(options);

    if (requestedPermission !== 'granted') {
      throw new Error(`Permission denied: ${path}`);
    }
  }

  /**
   * Read content of a file
   */
  async readFile(path: string): Promise<string> {
    const normalizedPath = this.normalizePath(path);
    const handle = this.fileHandles.get(normalizedPath);

    if (!handle) {
      throw new Error(`File not found: ${normalizedPath}`);
    }

    // Check read permission
    await this.checkPermission(handle, 'read', normalizedPath);

    // Get file and read content
    const file = await handle.getFile();
    return await file.text();
  }

  /**
   * Write content to a file
   */
  async writeFile(path: string, content: string): Promise<void> {
    const normalizedPath = this.normalizePath(path);
    const handle = this.fileHandles.get(normalizedPath);

    if (!handle) {
      throw new Error(`File not found: ${normalizedPath}`);
    }

    // Check write permission
    await this.checkPermission(handle, 'readwrite', normalizedPath);

    // Create writable stream and write content
    const writable = await handle.createWritable();

    try {
      await writable.write(content);
    } finally {
      // Always close the writable stream
      await writable.close();
    }
  }

  /**
   * Read directory contents (non-recursive)
   */
  async readDir(path: string): Promise<string[]> {
    const normalizedPath = this.normalizePath(path);
    const handle = this.directoryHandles.get(normalizedPath);

    if (!handle) {
      throw new Error(`Directory not found: ${normalizedPath}`);
    }

    const entries: string[] = [];

    // Iterate over directory entries
    for await (const entry of handle.values()) {
      entries.push(entry.name);
    }

    return entries;
  }

  /**
   * Check if file or directory exists
   */
  async exists(path: string): Promise<boolean> {
    const normalizedPath = this.normalizePath(path);

    return (
      this.fileHandles.has(normalizedPath) ||
      this.directoryHandles.has(normalizedPath)
    );
  }

  /**
   * Recursively traverse directory and return all files
   * @param dirHandle - Directory handle from File System Access API
   * @returns Array of FileInfo objects for all files in directory tree
   */
  async traverseDirectory(dirHandle: FileSystemDirectoryHandle): Promise<FileInfo[]> {
    const files: FileInfo[] = [];
    await this.traverseDirectoryRecursive(dirHandle, '', files, dirHandle.name);
    return files;
  }

  /**
   * Helper method to recursively traverse directories
   * @private
   */
  private async traverseDirectoryRecursive(
    dirHandle: FileSystemDirectoryHandle,
    currentPath: string,
    files: FileInfo[],
    rootName?: string
  ): Promise<void> {
    // Use rootName for the base path (only set on first call)
    const baseName = rootName || dirHandle.name;

    // Iterate over all entries in the directory
    for await (const entry of dirHandle.values()) {
      const entryPath = currentPath ? `${currentPath}/${entry.name}` : entry.name;

      if (entry.kind === 'file') {
        // Add file to results
        files.push({
          path: `/${baseName}/${entryPath}`,
          handle: entry as FileSystemFileHandle,
          name: entry.name,
          isDirectory: false,
        });
      } else if (entry.kind === 'directory') {
        // Recursively traverse subdirectory
        await this.traverseDirectoryRecursive(
          entry as FileSystemDirectoryHandle,
          entryPath,
          files,
          baseName
        );
      }
    }
  }

  /**
   * Test helper: Set file handle for testing
   * In production, this would be obtained via showOpenFilePicker() or showDirectoryPicker()
   */
  setFileHandle(path: string, handle: FileSystemFileHandle): void {
    const normalizedPath = this.normalizePath(path);
    this.fileHandles.set(normalizedPath, handle);
  }

  /**
   * Test helper: Set directory handle for testing
   * In production, this would be obtained via showDirectoryPicker()
   */
  setDirectoryHandle(path: string, handle: FileSystemDirectoryHandle): void {
    const normalizedPath = this.normalizePath(path);
    this.directoryHandles.set(normalizedPath, handle);
  }

  /**
   * Get file handle for testing
   */
  getFileHandle(path: string): FileSystemFileHandle | undefined {
    const normalizedPath = this.normalizePath(path);
    return this.fileHandles.get(normalizedPath);
  }

  /**
   * Get directory handle for testing
   */
  getDirectoryHandle(path: string): FileSystemDirectoryHandle | undefined {
    const normalizedPath = this.normalizePath(path);
    return this.directoryHandles.get(normalizedPath);
  }

  /**
   * Clear all handles (for testing)
   */
  clear(): void {
    this.fileHandles.clear();
    this.directoryHandles.clear();
  }
}
