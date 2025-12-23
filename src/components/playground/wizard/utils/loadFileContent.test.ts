import { describe, it, expect, vi } from 'vitest';
import { loadFileContent, findFileByPath } from './loadFileContent';
import type { FileInfo } from '../types';

describe('loadFileContent', () => {
  it('loads file content from handle', async () => {
    const mockHandle = {
      name: 'test.cpp',
      getFile: vi.fn().mockResolvedValue({
        text: vi.fn().mockResolvedValue('file content'),
      }),
    } as unknown as FileSystemFileHandle;

    const content = await loadFileContent(mockHandle);
    expect(content).toBe('file content');
  });

  it('throws error when file read fails', async () => {
    const mockHandle = {
      name: 'test.cpp',
      getFile: vi.fn().mockRejectedValue(new Error('Read failed')),
    } as unknown as FileSystemFileHandle;

    await expect(loadFileContent(mockHandle)).rejects.toThrow('Failed to read file');
  });
});

describe('findFileByPath', () => {
  const mockFiles: FileInfo[] = [
    { path: 'src/main.cpp', name: 'main.cpp', handle: {} as any, size: 100 },
    { path: 'src/helper.cpp', name: 'helper.cpp', handle: {} as any, size: 200 },
  ];

  it('finds file by path', () => {
    const file = findFileByPath(mockFiles, 'src/main.cpp');
    expect(file).toBeDefined();
    expect(file?.name).toBe('main.cpp');
  });

  it('returns undefined for non-existent path', () => {
    const file = findFileByPath(mockFiles, 'missing.cpp');
    expect(file).toBeUndefined();
  });
});
