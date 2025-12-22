/**
 * MockFileSystem Implementation Tests
 * Tests for the mock file system adapter beyond interface contracts
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { MockFileSystem } from './MockFileSystem';

describe('MockFileSystem', () => {
  let fs: MockFileSystem;

  beforeEach(() => {
    fs = new MockFileSystem();
  });

  describe('test helpers', () => {
    it('should add file synchronously via addFile', () => {
      fs.addFile('/test.txt', 'content');

      const paths = fs.getAllPaths();
      expect(paths).toContain('/test.txt');
    });

    it('should clear all files', async () => {
      await fs.writeFile('/file1.txt', 'content1');
      await fs.writeFile('/file2.txt', 'content2');

      fs.clear();

      const paths = fs.getAllPaths();
      expect(paths).toHaveLength(0);
    });

    it('should get all file paths', async () => {
      await fs.writeFile('/dir/file1.txt', 'content1');
      await fs.writeFile('/dir/file2.txt', 'content2');

      const paths = fs.getAllPaths();

      expect(paths).toContain('/dir/file1.txt');
      expect(paths).toContain('/dir/file2.txt');
      expect(paths).toHaveLength(2);
    });
  });

  describe('path normalization', () => {
    it('should normalize paths with leading slash', async () => {
      await fs.writeFile('file.txt', 'content');
      const content = await fs.readFile('/file.txt');

      expect(content).toBe('content');
    });

    it('should normalize paths without leading slash', async () => {
      await fs.writeFile('/file.txt', 'content');
      const content = await fs.readFile('file.txt');

      expect(content).toBe('content');
    });

    it('should handle nested paths correctly', async () => {
      await fs.writeFile('/dir/subdir/file.txt', 'content');

      const content = await fs.readFile('/dir/subdir/file.txt');
      expect(content).toBe('content');

      const exists = await fs.exists('/dir/subdir/file.txt');
      expect(exists).toBe(true);
    });
  });

  describe('directory operations', () => {
    it('should list only direct children of directory', async () => {
      await fs.writeFile('/dir/file1.txt', 'content1');
      await fs.writeFile('/dir/file2.txt', 'content2');
      await fs.writeFile('/dir/subdir/nested.txt', 'nested');

      const files = await fs.readDir('/dir');

      expect(files).toContain('file1.txt');
      expect(files).toContain('file2.txt');
      expect(files).not.toContain('nested.txt');
      expect(files).not.toContain('subdir/nested.txt');
    });

    it('should handle directory path with trailing slash', async () => {
      await fs.writeFile('/dir/file.txt', 'content');

      const files = await fs.readDir('/dir/');
      expect(files).toContain('file.txt');
    });

    it('should return empty array for non-existent directory', async () => {
      const files = await fs.readDir('/nonexistent');
      expect(files).toEqual([]);
    });

    it('should handle root directory', async () => {
      await fs.writeFile('/file1.txt', 'content1');
      await fs.writeFile('/file2.txt', 'content2');
      await fs.writeFile('/dir/file3.txt', 'content3');

      const files = await fs.readDir('/');

      expect(files).toContain('file1.txt');
      expect(files).toContain('file2.txt');
      expect(files).not.toContain('file3.txt');
    });
  });

  describe('error handling', () => {
    it('should throw descriptive error for missing file', async () => {
      await expect(fs.readFile('/missing.txt')).rejects.toThrow('File not found: /missing.txt');
    });

    it('should throw error for missing nested file', async () => {
      await expect(fs.readFile('/dir/subdir/missing.txt')).rejects.toThrow('File not found: /dir/subdir/missing.txt');
    });
  });

  describe('overwriting files', () => {
    it('should overwrite existing file content', async () => {
      await fs.writeFile('/file.txt', 'original');
      await fs.writeFile('/file.txt', 'updated');

      const content = await fs.readFile('/file.txt');
      expect(content).toBe('updated');
    });

    it('should maintain separate file contents', async () => {
      await fs.writeFile('/file1.txt', 'content1');
      await fs.writeFile('/file2.txt', 'content2');

      const content1 = await fs.readFile('/file1.txt');
      const content2 = await fs.readFile('/file2.txt');

      expect(content1).toBe('content1');
      expect(content2).toBe('content2');
    });
  });
});
