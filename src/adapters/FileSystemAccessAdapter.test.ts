/**
 * FileSystemAccessAdapter Tests
 *
 * Following TDD cycle:
 * 1. RED: Write failing tests first
 * 2. GREEN: Implement minimum code to pass
 * 3. REFACTOR: Improve while keeping tests green
 *
 * Tests use mocked File System Access API objects
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { FileSystemAccessAdapter } from './FileSystemAccessAdapter';
import type { IFileSystem } from '../core/interfaces/IFileSystem';

describe('FileSystemAccessAdapter', () => {
  describe('IFileSystem contract compliance', () => {
    let adapter: IFileSystem;

    beforeEach(() => {
      adapter = new FileSystemAccessAdapter();
    });

    it('should implement IFileSystem interface', () => {
      expect(adapter).toBeDefined();
      expect(typeof adapter.readFile).toBe('function');
      expect(typeof adapter.writeFile).toBe('function');
      expect(typeof adapter.readDir).toBe('function');
      expect(typeof adapter.exists).toBe('function');
    });
  });

  describe('File reading', () => {
    let adapter: FileSystemAccessAdapter;
    let mockFileHandle: FileSystemFileHandle;
    let mockFile: File;

    beforeEach(() => {
      adapter = new FileSystemAccessAdapter();

      // Mock File object
      mockFile = new File(['test content'], 'test.txt', { type: 'text/plain' });

      // Mock FileSystemFileHandle
      mockFileHandle = {
        kind: 'file',
        name: 'test.txt',
        getFile: vi.fn().mockResolvedValue(mockFile),
        createWritable: vi.fn(),
        queryPermission: vi.fn().mockResolvedValue('granted'),
        requestPermission: vi.fn().mockResolvedValue('granted'),
        isSameEntry: vi.fn(),
      } as unknown as FileSystemFileHandle;
    });

    it('should read file content via File System Access API', async () => {
      adapter.setFileHandle('/test.txt', mockFileHandle);

      const content = await adapter.readFile('/test.txt');

      expect(content).toBe('test content');
      expect(mockFileHandle.getFile).toHaveBeenCalled();
    });

    it('should throw error if file handle not found', async () => {
      await expect(adapter.readFile('/missing.txt')).rejects.toThrow('File not found: /missing.txt');
    });

    it('should throw error if file read fails', async () => {
      mockFileHandle.getFile = vi.fn().mockRejectedValue(new Error('Read failed'));
      adapter.setFileHandle('/test.txt', mockFileHandle);

      await expect(adapter.readFile('/test.txt')).rejects.toThrow('Read failed');
    });

    it('should handle large files', async () => {
      const largeContent = 'x'.repeat(10000);
      mockFile = new File([largeContent], 'large.txt');
      mockFileHandle.getFile = vi.fn().mockResolvedValue(mockFile);
      adapter.setFileHandle('/large.txt', mockFileHandle);

      const content = await adapter.readFile('/large.txt');

      expect(content).toBe(largeContent);
      expect(content.length).toBe(10000);
    });
  });

  describe('File writing', () => {
    let adapter: FileSystemAccessAdapter;
    let mockFileHandle: FileSystemFileHandle;
    let mockWritable: FileSystemWritableFileStream;

    beforeEach(() => {
      adapter = new FileSystemAccessAdapter();

      // Mock FileSystemWritableFileStream
      mockWritable = {
        write: vi.fn().mockResolvedValue(undefined),
        close: vi.fn().mockResolvedValue(undefined),
        seek: vi.fn(),
        truncate: vi.fn(),
        abort: vi.fn(),
        getWriter: vi.fn(),
        locked: false,
      } as unknown as FileSystemWritableFileStream;

      // Mock FileSystemFileHandle
      mockFileHandle = {
        kind: 'file',
        name: 'test.txt',
        getFile: vi.fn(),
        createWritable: vi.fn().mockResolvedValue(mockWritable),
        queryPermission: vi.fn().mockResolvedValue('granted'),
        requestPermission: vi.fn().mockResolvedValue('granted'),
        isSameEntry: vi.fn(),
      } as unknown as FileSystemFileHandle;
    });

    it('should write file content via File System Access API', async () => {
      adapter.setFileHandle('/test.txt', mockFileHandle);

      await adapter.writeFile('/test.txt', 'new content');

      expect(mockFileHandle.createWritable).toHaveBeenCalled();
      expect(mockWritable.write).toHaveBeenCalledWith('new content');
      expect(mockWritable.close).toHaveBeenCalled();
    });

    it('should throw error if file handle not found for writing', async () => {
      await expect(adapter.writeFile('/missing.txt', 'content')).rejects.toThrow('File not found: /missing.txt');
    });

    it('should throw error if write fails', async () => {
      mockWritable.write = vi.fn().mockRejectedValue(new Error('Write failed'));
      adapter.setFileHandle('/test.txt', mockFileHandle);

      await expect(adapter.writeFile('/test.txt', 'content')).rejects.toThrow('Write failed');
    });

    it('should close writable stream even if write fails', async () => {
      mockWritable.write = vi.fn().mockRejectedValue(new Error('Write failed'));
      adapter.setFileHandle('/test.txt', mockFileHandle);

      await expect(adapter.writeFile('/test.txt', 'content')).rejects.toThrow('Write failed');
      expect(mockWritable.close).toHaveBeenCalled();
    });

    it('should handle empty content', async () => {
      adapter.setFileHandle('/empty.txt', mockFileHandle);

      await adapter.writeFile('/empty.txt', '');

      expect(mockWritable.write).toHaveBeenCalledWith('');
      expect(mockWritable.close).toHaveBeenCalled();
    });
  });

  describe('Directory reading', () => {
    let adapter: FileSystemAccessAdapter;
    let mockDirHandle: FileSystemDirectoryHandle;
    let mockFileHandle1: FileSystemFileHandle;
    let mockFileHandle2: FileSystemFileHandle;
    let mockSubDirHandle: FileSystemDirectoryHandle;

    beforeEach(() => {
      adapter = new FileSystemAccessAdapter();

      // Mock FileSystemFileHandles
      mockFileHandle1 = {
        kind: 'file',
        name: 'file1.txt',
      } as FileSystemFileHandle;

      mockFileHandle2 = {
        kind: 'file',
        name: 'file2.txt',
      } as FileSystemFileHandle;

      mockSubDirHandle = {
        kind: 'directory',
        name: 'subdir',
      } as FileSystemDirectoryHandle;

      // Mock DirectoryHandle with async iterator
      const entries: [string, FileSystemHandle][] = [
        ['file1.txt', mockFileHandle1],
        ['file2.txt', mockFileHandle2],
        ['subdir', mockSubDirHandle],
      ];

      mockDirHandle = {
        kind: 'directory',
        name: 'testdir',
        values: vi.fn().mockReturnValue({
          [Symbol.asyncIterator]: async function* () {
            for (const [, handle] of entries) {
              yield handle;
            }
          },
        }),
        entries: vi.fn(),
        keys: vi.fn(),
        getFileHandle: vi.fn(),
        getDirectoryHandle: vi.fn(),
        removeEntry: vi.fn(),
        resolve: vi.fn(),
        queryPermission: vi.fn().mockResolvedValue('granted'),
        requestPermission: vi.fn().mockResolvedValue('granted'),
        isSameEntry: vi.fn(),
      } as unknown as FileSystemDirectoryHandle;
    });

    it('should read directory contents', async () => {
      adapter.setDirectoryHandle('/testdir', mockDirHandle);

      const contents = await adapter.readDir('/testdir');

      expect(contents).toEqual(['file1.txt', 'file2.txt', 'subdir']);
      expect(mockDirHandle.values).toHaveBeenCalled();
    });

    it('should return empty array for empty directory', async () => {
      const emptyDirHandle = {
        kind: 'directory',
        name: 'emptydir',
        values: vi.fn().mockReturnValue({
          [Symbol.asyncIterator]: async function* () {
            // No entries
          },
        }),
      } as unknown as FileSystemDirectoryHandle;

      adapter.setDirectoryHandle('/emptydir', emptyDirHandle);

      const contents = await adapter.readDir('/emptydir');

      expect(contents).toEqual([]);
    });

    it('should throw error if directory handle not found', async () => {
      await expect(adapter.readDir('/missing')).rejects.toThrow('Directory not found: /missing');
    });

    it('should include subdirectories in results', async () => {
      adapter.setDirectoryHandle('/testdir', mockDirHandle);

      const contents = await adapter.readDir('/testdir');

      expect(contents).toContain('subdir');
    });
  });

  describe('File existence checking', () => {
    let adapter: FileSystemAccessAdapter;
    let mockFileHandle: FileSystemFileHandle;

    beforeEach(() => {
      adapter = new FileSystemAccessAdapter();

      mockFileHandle = {
        kind: 'file',
        name: 'exists.txt',
      } as FileSystemFileHandle;
    });

    it('should return true if file handle exists', async () => {
      adapter.setFileHandle('/exists.txt', mockFileHandle);

      const exists = await adapter.exists('/exists.txt');

      expect(exists).toBe(true);
    });

    it('should return false if file handle does not exist', async () => {
      const exists = await adapter.exists('/missing.txt');

      expect(exists).toBe(false);
    });

    it('should return true if directory handle exists', async () => {
      const mockDirHandle = {
        kind: 'directory',
        name: 'testdir',
      } as FileSystemDirectoryHandle;

      adapter.setDirectoryHandle('/testdir', mockDirHandle);

      const exists = await adapter.exists('/testdir');

      expect(exists).toBe(true);
    });
  });

  describe('Permission handling', () => {
    let adapter: FileSystemAccessAdapter;
    let mockFileHandle: FileSystemFileHandle;

    beforeEach(() => {
      adapter = new FileSystemAccessAdapter();

      mockFileHandle = {
        kind: 'file',
        name: 'test.txt',
        getFile: vi.fn().mockResolvedValue(new File(['content'], 'test.txt')),
        createWritable: vi.fn(),
        queryPermission: vi.fn(),
        requestPermission: vi.fn(),
        isSameEntry: vi.fn(),
      } as unknown as FileSystemFileHandle;
    });

    it('should request read permission if not granted', async () => {
      mockFileHandle.queryPermission = vi.fn().mockResolvedValue('prompt');
      mockFileHandle.requestPermission = vi.fn().mockResolvedValue('granted');
      adapter.setFileHandle('/test.txt', mockFileHandle);

      await adapter.readFile('/test.txt');

      expect(mockFileHandle.queryPermission).toHaveBeenCalledWith({ mode: 'read' });
      expect(mockFileHandle.requestPermission).toHaveBeenCalledWith({ mode: 'read' });
    });

    it('should throw error if read permission denied', async () => {
      mockFileHandle.queryPermission = vi.fn().mockResolvedValue('denied');
      mockFileHandle.requestPermission = vi.fn().mockResolvedValue('denied');
      adapter.setFileHandle('/test.txt', mockFileHandle);

      await expect(adapter.readFile('/test.txt')).rejects.toThrow('Permission denied: /test.txt');
    });

    it('should request write permission for writeFile', async () => {
      const mockWritable = {
        write: vi.fn().mockResolvedValue(undefined),
        close: vi.fn().mockResolvedValue(undefined),
      } as unknown as FileSystemWritableFileStream;

      mockFileHandle.queryPermission = vi.fn().mockResolvedValue('prompt');
      mockFileHandle.requestPermission = vi.fn().mockResolvedValue('granted');
      mockFileHandle.createWritable = vi.fn().mockResolvedValue(mockWritable);
      adapter.setFileHandle('/test.txt', mockFileHandle);

      await adapter.writeFile('/test.txt', 'content');

      expect(mockFileHandle.queryPermission).toHaveBeenCalledWith({ mode: 'readwrite' });
      expect(mockFileHandle.requestPermission).toHaveBeenCalledWith({ mode: 'readwrite' });
    });

    it('should throw error if write permission denied', async () => {
      mockFileHandle.queryPermission = vi.fn().mockResolvedValue('denied');
      mockFileHandle.requestPermission = vi.fn().mockResolvedValue('denied');
      adapter.setFileHandle('/test.txt', mockFileHandle);

      await expect(adapter.writeFile('/test.txt', 'content')).rejects.toThrow('Permission denied: /test.txt');
    });
  });

  describe('Path normalization', () => {
    let adapter: FileSystemAccessAdapter;
    let mockFileHandle: FileSystemFileHandle;

    beforeEach(() => {
      adapter = new FileSystemAccessAdapter();

      mockFileHandle = {
        kind: 'file',
        name: 'test.txt',
        getFile: vi.fn().mockResolvedValue(new File(['content'], 'test.txt')),
      } as unknown as FileSystemFileHandle;
    });

    it('should normalize paths with multiple slashes', async () => {
      adapter.setFileHandle('/test.txt', mockFileHandle);

      const exists = await adapter.exists('//test.txt');

      expect(exists).toBe(true);
    });

    it('should normalize paths without leading slash', async () => {
      adapter.setFileHandle('/test.txt', mockFileHandle);

      const exists = await adapter.exists('test.txt');

      expect(exists).toBe(true);
    });

    it('should normalize paths with trailing slash', async () => {
      const mockDirHandle = {
        kind: 'directory',
        name: 'testdir',
      } as FileSystemDirectoryHandle;

      adapter.setDirectoryHandle('/testdir', mockDirHandle);

      const exists = await adapter.exists('/testdir/');

      expect(exists).toBe(true);
    });
  });

  describe('Error handling', () => {
    let adapter: FileSystemAccessAdapter;

    beforeEach(() => {
      adapter = new FileSystemAccessAdapter();
    });

    it('should provide descriptive error messages', async () => {
      await expect(adapter.readFile('/missing.txt')).rejects.toThrow('File not found: /missing.txt');
      await expect(adapter.writeFile('/missing.txt', 'content')).rejects.toThrow('File not found: /missing.txt');
      await expect(adapter.readDir('/missing')).rejects.toThrow('Directory not found: /missing');
    });

    it('should propagate File System Access API errors', async () => {
      const mockFileHandle = {
        kind: 'file',
        name: 'test.txt',
        getFile: vi.fn().mockRejectedValue(new DOMException('NotAllowedError', 'NotAllowedError')),
        queryPermission: vi.fn().mockResolvedValue('granted'),
        requestPermission: vi.fn().mockResolvedValue('granted'),
      } as unknown as FileSystemFileHandle;

      adapter.setFileHandle('/test.txt', mockFileHandle);

      await expect(adapter.readFile('/test.txt')).rejects.toThrow('NotAllowedError');
    });
  });

  describe('Edge cases', () => {
    let adapter: FileSystemAccessAdapter;

    beforeEach(() => {
      adapter = new FileSystemAccessAdapter();
    });

    it('should handle special characters in filenames', async () => {
      const mockFileHandle = {
        kind: 'file',
        name: 'test-file_v2.0.txt',
        getFile: vi.fn().mockResolvedValue(new File(['content'], 'test-file_v2.0.txt')),
      } as unknown as FileSystemFileHandle;

      adapter.setFileHandle('/test-file_v2.0.txt', mockFileHandle);

      const exists = await adapter.exists('/test-file_v2.0.txt');

      expect(exists).toBe(true);
    });

    it('should handle Unicode filenames', async () => {
      const mockFileHandle = {
        kind: 'file',
        name: 'файл.txt',
        getFile: vi.fn().mockResolvedValue(new File(['content'], 'файл.txt')),
      } as unknown as FileSystemFileHandle;

      adapter.setFileHandle('/файл.txt', mockFileHandle);

      const exists = await adapter.exists('/файл.txt');

      expect(exists).toBe(true);
    });

    it('should handle very long paths', async () => {
      const longPath = '/' + 'a'.repeat(255);
      const mockFileHandle = {
        kind: 'file',
        name: 'a'.repeat(255),
        getFile: vi.fn().mockResolvedValue(new File(['content'], 'file.txt')),
      } as unknown as FileSystemFileHandle;

      adapter.setFileHandle(longPath, mockFileHandle);

      const exists = await adapter.exists(longPath);

      expect(exists).toBe(true);
    });
  });

  describe('Test helper methods', () => {
    let adapter: FileSystemAccessAdapter;

    beforeEach(() => {
      adapter = new FileSystemAccessAdapter();
    });

    it('should get file handle', () => {
      const mockFileHandle = {
        kind: 'file',
        name: 'test.txt',
      } as FileSystemFileHandle;

      adapter.setFileHandle('/test.txt', mockFileHandle);

      const retrieved = adapter.getFileHandle('/test.txt');

      expect(retrieved).toBe(mockFileHandle);
    });

    it('should return undefined for non-existent file handle', () => {
      const retrieved = adapter.getFileHandle('/missing.txt');

      expect(retrieved).toBeUndefined();
    });

    it('should get directory handle', () => {
      const mockDirHandle = {
        kind: 'directory',
        name: 'testdir',
      } as FileSystemDirectoryHandle;

      adapter.setDirectoryHandle('/testdir', mockDirHandle);

      const retrieved = adapter.getDirectoryHandle('/testdir');

      expect(retrieved).toBe(mockDirHandle);
    });

    it('should return undefined for non-existent directory handle', () => {
      const retrieved = adapter.getDirectoryHandle('/missing');

      expect(retrieved).toBeUndefined();
    });

    it('should clear all handles', async () => {
      const mockFileHandle = {
        kind: 'file',
        name: 'test.txt',
      } as FileSystemFileHandle;

      const mockDirHandle = {
        kind: 'directory',
        name: 'testdir',
      } as FileSystemDirectoryHandle;

      adapter.setFileHandle('/test.txt', mockFileHandle);
      adapter.setDirectoryHandle('/testdir', mockDirHandle);

      expect(await adapter.exists('/test.txt')).toBe(true);
      expect(await adapter.exists('/testdir')).toBe(true);

      adapter.clear();

      expect(await adapter.exists('/test.txt')).toBe(false);
      expect(await adapter.exists('/testdir')).toBe(false);
    });
  });
});
