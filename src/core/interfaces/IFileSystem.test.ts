/**
 * IFileSystem Interface Contract Tests
 * TDD Phase: RED - Write failing tests first
 */

import { describe, it, expect, beforeEach } from 'vitest';
import type { IFileSystem } from './IFileSystem';
import { MockFileSystem } from '../../adapters/MockFileSystem';

describe('IFileSystem', () => {
  describe('contract', () => {
    let fs: IFileSystem;

    beforeEach(() => {
      fs = new MockFileSystem();
    });

    it('should have readFile method', () => {
      expect(typeof fs.readFile).toBe('function');
    });

    it('should have writeFile method', () => {
      expect(typeof fs.writeFile).toBe('function');
    });

    it('should have readDir method', () => {
      expect(typeof fs.readDir).toBe('function');
    });

    it('should have exists method', () => {
      expect(typeof fs.exists).toBe('function');
    });
  });

  describe('behavior', () => {
    let fs: IFileSystem;

    beforeEach(() => {
      fs = new MockFileSystem();
    });

    it('should read file content that was written', async () => {
      await fs.writeFile('/test.txt', 'hello world');
      const content = await fs.readFile('/test.txt');
      expect(content).toBe('hello world');
    });

    it('should throw error when reading non-existent file', async () => {
      await expect(fs.readFile('/missing.txt')).rejects.toThrow('File not found');
    });

    it('should list directory contents', async () => {
      await fs.writeFile('/dir/file1.txt', 'content1');
      await fs.writeFile('/dir/file2.txt', 'content2');

      const files = await fs.readDir('/dir');

      expect(files).toContain('file1.txt');
      expect(files).toContain('file2.txt');
      expect(files).toHaveLength(2);
    });

    it('should return empty array for empty directory', async () => {
      const files = await fs.readDir('/empty');
      expect(files).toEqual([]);
    });

    it('should check file existence - file exists', async () => {
      await fs.writeFile('/exists.txt', 'content');
      const exists = await fs.exists('/exists.txt');
      expect(exists).toBe(true);
    });

    it('should check file existence - file does not exist', async () => {
      const exists = await fs.exists('/missing.txt');
      expect(exists).toBe(false);
    });

    it('should not list files from parent directories', async () => {
      await fs.writeFile('/dir/file.txt', 'content');
      await fs.writeFile('/dir/subdir/nested.txt', 'nested');

      const files = await fs.readDir('/dir');

      expect(files).toContain('file.txt');
      expect(files).not.toContain('nested.txt');
    });

    it('should handle paths with or without leading slash consistently', async () => {
      await fs.writeFile('/file.txt', 'content1');
      await fs.writeFile('file2.txt', 'content2');

      const content1 = await fs.readFile('/file.txt');
      const content2 = await fs.readFile('file2.txt');

      expect(content1).toBe('content1');
      expect(content2).toBe('content2');
    });
  });
});
