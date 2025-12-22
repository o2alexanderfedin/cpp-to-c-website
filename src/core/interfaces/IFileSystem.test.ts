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

  describe('traverseDirectory', () => {
    let fs: MockFileSystem;

    beforeEach(() => {
      fs = new MockFileSystem();
    });

    it('should have traverseDirectory method', () => {
      expect(typeof fs.traverseDirectory).toBe('function');
    });

    it('should return flat list of files from directory', async () => {
      // Setup: Create a mock directory handle
      const mockDirHandle = {
        name: 'test-dir',
        kind: 'directory',
      } as FileSystemDirectoryHandle;

      // Add files to mock filesystem
      fs.addFile('/test-dir/file1.cpp', 'content1');
      fs.addFile('/test-dir/file2.h', 'content2');

      const files = await fs.traverseDirectory(mockDirHandle);

      expect(files).toHaveLength(2);
      expect(files[0]).toHaveProperty('path');
      expect(files[0]).toHaveProperty('handle');
      expect(files.map(f => f.path)).toContain('/test-dir/file1.cpp');
      expect(files.map(f => f.path)).toContain('/test-dir/file2.h');
    });

    it('should traverse nested directories recursively', async () => {
      const mockDirHandle = {
        name: 'project',
        kind: 'directory',
      } as FileSystemDirectoryHandle;

      // Setup nested structure
      fs.addFile('/project/main.cpp', 'main');
      fs.addFile('/project/src/utils.cpp', 'utils');
      fs.addFile('/project/src/lib/helper.h', 'helper');
      fs.addFile('/project/include/config.h', 'config');

      const files = await fs.traverseDirectory(mockDirHandle);

      expect(files).toHaveLength(4);
      expect(files.map(f => f.path)).toContain('/project/main.cpp');
      expect(files.map(f => f.path)).toContain('/project/src/utils.cpp');
      expect(files.map(f => f.path)).toContain('/project/src/lib/helper.h');
      expect(files.map(f => f.path)).toContain('/project/include/config.h');
    });

    it('should return empty array for empty directory', async () => {
      const mockDirHandle = {
        name: 'empty-dir',
        kind: 'directory',
      } as FileSystemDirectoryHandle;

      fs.addDirectory('/empty-dir');

      const files = await fs.traverseDirectory(mockDirHandle);

      expect(files).toEqual([]);
    });

    it('should filter only .cpp and .h files when used with filter', async () => {
      const mockDirHandle = {
        name: 'mixed',
        kind: 'directory',
      } as FileSystemDirectoryHandle;

      fs.addFile('/mixed/code.cpp', 'cpp');
      fs.addFile('/mixed/header.h', 'h');
      fs.addFile('/mixed/readme.txt', 'text');
      fs.addFile('/mixed/data.json', 'json');

      const files = await fs.traverseDirectory(mockDirHandle);
      const cppFiles = files.filter(f =>
        f.path.endsWith('.cpp') ||
        f.path.endsWith('.h') ||
        f.path.endsWith('.hpp') ||
        f.path.endsWith('.cc') ||
        f.path.endsWith('.cxx') ||
        f.path.endsWith('.hxx')
      );

      expect(cppFiles).toHaveLength(2);
      expect(cppFiles.map(f => f.path)).toContain('/mixed/code.cpp');
      expect(cppFiles.map(f => f.path)).toContain('/mixed/header.h');
    });

    it('should handle deeply nested directory structures', async () => {
      const mockDirHandle = {
        name: 'deep',
        kind: 'directory',
      } as FileSystemDirectoryHandle;

      fs.addFile('/deep/a/b/c/d/e/file.cpp', 'deep');

      const files = await fs.traverseDirectory(mockDirHandle);

      expect(files).toHaveLength(1);
      expect(files[0].path).toBe('/deep/a/b/c/d/e/file.cpp');
    });
  });
});
