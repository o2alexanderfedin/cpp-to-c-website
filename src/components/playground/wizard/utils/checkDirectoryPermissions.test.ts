import { describe, it, expect, vi } from 'vitest';
import { checkDirectoryPermissions, requestWritePermission } from './checkDirectoryPermissions';

describe('checkDirectoryPermissions', () => {
  it('returns permission status for directory', async () => {
    const mockDirHandle = {
      queryPermission: vi.fn()
        .mockResolvedValueOnce('granted') // read
        .mockResolvedValueOnce('granted') // write
    } as any;

    const result = await checkDirectoryPermissions(mockDirHandle);

    expect(result).toEqual({ read: true, write: true });
    expect(mockDirHandle.queryPermission).toHaveBeenCalledTimes(2);
    expect(mockDirHandle.queryPermission).toHaveBeenNthCalledWith(1, { mode: 'read' });
    expect(mockDirHandle.queryPermission).toHaveBeenNthCalledWith(2, { mode: 'readwrite' });
  });

  it('handles permission denied', async () => {
    const mockDirHandle = {
      queryPermission: vi.fn()
        .mockResolvedValueOnce('granted') // read
        .mockResolvedValueOnce('denied') // write
    } as any;

    const result = await checkDirectoryPermissions(mockDirHandle);

    expect(result).toEqual({ read: true, write: false });
  });

  it('handles prompt state', async () => {
    const mockDirHandle = {
      queryPermission: vi.fn()
        .mockResolvedValueOnce('granted') // read
        .mockResolvedValueOnce('prompt') // write
    } as any;

    const result = await checkDirectoryPermissions(mockDirHandle);

    expect(result).toEqual({ read: true, write: false });
  });

  it('handles errors gracefully', async () => {
    const mockDirHandle = {
      queryPermission: vi.fn().mockRejectedValue(new Error('Permission error'))
    } as any;

    const result = await checkDirectoryPermissions(mockDirHandle);

    expect(result).toEqual({ read: false, write: false });
  });

  it('handles both permissions denied', async () => {
    const mockDirHandle = {
      queryPermission: vi.fn()
        .mockResolvedValueOnce('denied') // read
        .mockResolvedValueOnce('denied') // write
    } as any;

    const result = await checkDirectoryPermissions(mockDirHandle);

    expect(result).toEqual({ read: false, write: false });
  });
});

describe('requestWritePermission', () => {
  it('requests and returns permission status', async () => {
    const mockDirHandle = {
      requestPermission: vi.fn().mockResolvedValue('granted')
    } as any;

    const result = await requestWritePermission(mockDirHandle);

    expect(result).toBe(true);
    expect(mockDirHandle.requestPermission).toHaveBeenCalledWith({ mode: 'readwrite' });
  });

  it('returns false when permission denied', async () => {
    const mockDirHandle = {
      requestPermission: vi.fn().mockResolvedValue('denied')
    } as any;

    const result = await requestWritePermission(mockDirHandle);

    expect(result).toBe(false);
  });

  it('returns false when permission prompt', async () => {
    const mockDirHandle = {
      requestPermission: vi.fn().mockResolvedValue('prompt')
    } as any;

    const result = await requestWritePermission(mockDirHandle);

    expect(result).toBe(false);
  });

  it('handles errors gracefully', async () => {
    const mockDirHandle = {
      requestPermission: vi.fn().mockRejectedValue(new Error('Request error'))
    } as any;

    const result = await requestWritePermission(mockDirHandle);

    expect(result).toBe(false);
  });
});
