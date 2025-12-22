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

import type { IFileSystem } from '../core/interfaces/IFileSystem';

/**
 * In-memory file system implementation for testing
 */
export class MockFileSystem implements IFileSystem {
  private files = new Map<string, string>();

  /**
   * Read file content from in-memory storage
   */
  async readFile(path: string): Promise<string> {
    const normalizedPath = this.normalizePath(path);

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
    this.files.set(normalizedPath, content);
  }

  /**
   * Read directory contents (non-recursive)
   * Returns only direct children of the directory
   */
  async readDir(path: string): Promise<string[]> {
    const normalizedPath = this.normalizePath(path);
    const dirPrefix = normalizedPath.endsWith('/') ? normalizedPath : `${normalizedPath}/`;

    const files: string[] = [];

    for (const filePath of this.files.keys()) {
      if (filePath.startsWith(dirPrefix)) {
        // Get the relative path from the directory
        const relativePath = filePath.substring(dirPrefix.length);

        // Only include direct children (no nested paths)
        if (!relativePath.includes('/')) {
          files.push(relativePath);
        }
      }
    }

    return files;
  }

  /**
   * Check if file exists in storage
   */
  async exists(path: string): Promise<boolean> {
    const normalizedPath = this.normalizePath(path);
    return this.files.has(normalizedPath);
  }

  /**
   * Test helper: Add file to storage (synchronous)
   */
  addFile(path: string, content: string): void {
    const normalizedPath = this.normalizePath(path);
    this.files.set(normalizedPath, content);
  }

  /**
   * Test helper: Clear all files
   */
  clear(): void {
    this.files.clear();
  }

  /**
   * Test helper: Get all file paths
   */
  getAllPaths(): string[] {
    return Array.from(this.files.keys());
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
