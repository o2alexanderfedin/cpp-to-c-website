/**
 * MockFileSystem - In-Memory File System Implementation
 *
 * Test implementation of IFileSystem using in-memory Map for storage.
 * Used for unit testing without touching real file system.
 *
 * Following SOLID principles:
 * - Single Responsibility: Only manages in-memory file storage
 * - Liskov Substitution: Can replace any IFileSystem implementation
 */

import type { IFileSystem, FileInfo } from '../core/interfaces/IFileSystem';

/**
 * In-memory file system implementation for testing
 */
export class MockFileSystem implements IFileSystem {
  private files = new Map<string, string>();
  private directories = new Set<string>();
  private shouldFailReadPredicate?: (path: string) => boolean;
  private shouldFailWritePredicate?: (path: string) => boolean;

  /**
   * Read file content from in-memory storage
   */
  async readFile(path: string): Promise<string> {
    const normalizedPath = this.normalizePath(path);

    // Check if should fail
    if (this.shouldFailReadPredicate && this.shouldFailReadPredicate(normalizedPath)) {
      throw new Error(`Failed to read file: ${path}`);
    }

    if (!this.files.has(normalizedPath)) {
      throw new Error(`File not found: ${path}`);
    }

    return this.files.get(normalizedPath)!;
  }

  /**
   * Write file content to in-memory storage
   */
  async writeFile(path: string, content: string): Promise<void> {
    const normalizedPath = this.normalizePath(path);

    // Check if should fail
    if (this.shouldFailWritePredicate && this.shouldFailWritePredicate(normalizedPath)) {
      throw new Error(`Failed to write file: ${path}`);
    }

    // Auto-create parent directories
    const parentDir = this.getParentDir(normalizedPath);
    if (parentDir && !this.directories.has(parentDir)) {
      this.addDirectory(parentDir);
    }

    this.files.set(normalizedPath, content);
  }

  /**
   * Read directory contents (non-recursive)
   * Returns only direct children of the directory (files and subdirectories)
   */
  async readDir(path: string): Promise<string[]> {
    const normalizedPath = this.normalizePath(path);
    const dirPrefix = normalizedPath.endsWith('/') ? normalizedPath : `${normalizedPath}/`;

    const children = new Set<string>();

    // Find all direct file children
    for (const filePath of this.files.keys()) {
      if (filePath.startsWith(dirPrefix)) {
        // Get the relative path from the directory
        const relativePath = filePath.substring(dirPrefix.length);

        // Only include direct children (no nested paths)
        if (!relativePath.includes('/')) {
          children.add(relativePath);
        } else {
          // Add the first directory component
          const firstDir = relativePath.split('/')[0];
          children.add(firstDir);
        }
      }
    }

    // Also check registered directories
    for (const dirPath of this.directories) {
      if (dirPath.startsWith(dirPrefix) && dirPath !== normalizedPath) {
        const relativePath = dirPath.substring(dirPrefix.length);
        if (!relativePath.includes('/')) {
          children.add(relativePath);
        } else {
          const firstDir = relativePath.split('/')[0];
          children.add(firstDir);
        }
      }
    }

    return Array.from(children);
  }

  /**
   * Check if file exists in storage
   */
  async exists(path: string): Promise<boolean> {
    const normalizedPath = this.normalizePath(path);
    return this.files.has(normalizedPath);
  }

  /**
   * Recursively traverse directory and return all files
   * @param dirHandle - Directory handle (in mock, we use the name property to find files)
   * @returns Array of FileInfo objects for all files in directory tree
   */
  async traverseDirectory(dirHandle: FileSystemDirectoryHandle): Promise<FileInfo[]> {
    const dirName = dirHandle.name;
    const dirPath = this.normalizePath(`/${dirName}`);
    const files: FileInfo[] = [];

    // Find all files that start with this directory path
    for (const [filePath, _content] of this.files.entries()) {
      if (filePath.startsWith(dirPath + '/') || filePath === dirPath) {
        // Create a mock file handle
        const fileName = filePath.split('/').pop() || '';
        const mockHandle = {
          kind: 'file',
          name: fileName,
          getFile: async () => ({
            name: fileName,
            text: async () => this.files.get(filePath) || '',
          }),
        } as FileSystemFileHandle;

        files.push({
          path: filePath,
          handle: mockHandle,
          name: fileName,
          isDirectory: false,
        });
      }
    }

    return files;
  }

  /**
   * Test helper: Add file to storage (synchronous)
   */
  addFile(path: string, content: string): void {
    const normalizedPath = this.normalizePath(path);

    // Auto-create parent directories
    const parentDir = this.getParentDir(normalizedPath);
    if (parentDir && !this.directories.has(parentDir)) {
      this.addDirectory(parentDir);
    }

    this.files.set(normalizedPath, content);
  }

  /**
   * Test helper: Add directory to storage (synchronous)
   */
  addDirectory(path: string): void {
    const normalizedPath = this.normalizePath(path);
    this.directories.add(normalizedPath);

    // Also add all parent directories
    const parts = normalizedPath.split('/').filter(Boolean);
    for (let i = 1; i < parts.length; i++) {
      const parentPath = '/' + parts.slice(0, i).join('/');
      this.directories.add(parentPath);
    }
  }

  /**
   * Test helper: Clear all files
   */
  clear(): void {
    this.files.clear();
    this.directories.clear();
  }

  /**
   * Test helper: Get all file paths
   */
  getAllPaths(): string[] {
    return Array.from(this.files.keys());
  }

  /**
   * Test helper: Set files that should fail on read
   */
  setShouldFailRead(predicate: (path: string) => boolean): void {
    this.shouldFailReadPredicate = predicate;
  }

  /**
   * Test helper: Set files that should fail on write
   */
  setShouldFailWrite(predicate: (path: string) => boolean): void {
    this.shouldFailWritePredicate = predicate;
  }

  /**
   * Get parent directory path
   * @private
   */
  private getParentDir(path: string): string | null {
    const parts = path.split('/').filter(Boolean);
    if (parts.length <= 1) {
      return null;
    }
    return '/' + parts.slice(0, -1).join('/');
  }

  /**
   * Normalize path to ensure consistent handling
   * - Ensures leading slash
   * - Removes trailing slash (except for root)
   * - Handles both absolute and relative paths
   */
  private normalizePath(path: string): string {
    if (!path) {
      return '/';
    }

    // Add leading slash if missing
    let normalized = path.startsWith('/') ? path : `/${path}`;

    // Remove trailing slash (except for root)
    if (normalized.length > 1 && normalized.endsWith('/')) {
      normalized = normalized.slice(0, -1);
    }

    return normalized;
  }
}
