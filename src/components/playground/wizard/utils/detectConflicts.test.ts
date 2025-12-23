import { describe, it, expect } from 'vitest';
import { convertToTargetFileName, detectConflicts, getConflictingFiles } from './detectConflicts';
import type { FileInfo } from '../types';

describe('convertToTargetFileName', () => {
  it('converts .cpp to .c', () => {
    expect(convertToTargetFileName('main.cpp')).toBe('main.c');
  });

  it('converts .cc to .c', () => {
    expect(convertToTargetFileName('helper.cc')).toBe('helper.c');
  });

  it('converts .cxx to .c', () => {
    expect(convertToTargetFileName('engine.cxx')).toBe('engine.c');
  });

  it('converts .C to .c', () => {
    expect(convertToTargetFileName('legacy.C')).toBe('legacy.c');
  });

  it('converts .hpp to .h', () => {
    expect(convertToTargetFileName('common.hpp')).toBe('common.h');
  });

  it('converts .hxx to .h', () => {
    expect(convertToTargetFileName('utils.hxx')).toBe('utils.h');
  });

  it('keeps .h as .h', () => {
    expect(convertToTargetFileName('utils.h')).toBe('utils.h');
  });

  it('keeps .c as .c', () => {
    expect(convertToTargetFileName('legacy.c')).toBe('legacy.c');
  });

  it('handles files with multiple dots', () => {
    expect(convertToTargetFileName('my.module.cpp')).toBe('my.module.c');
    expect(convertToTargetFileName('my.module.hpp')).toBe('my.module.h');
  });
});

describe('detectConflicts', () => {
  it('detects existing files in target directory', async () => {
    const mockFiles: FileInfo[] = [
      { path: 'main.cpp', name: 'main.cpp', handle: {} as any, size: 100 },
      { path: 'helper.cpp', name: 'helper.cpp', handle: {} as any, size: 200 }
    ];

    const mockTargetDir = {
      values: async function* () {
        yield { kind: 'file', name: 'main.c' };
        yield { kind: 'file', name: 'other.txt' };
      }
    } as any;

    const result = await detectConflicts(mockFiles, mockTargetDir);

    expect(result.totalFiles).toBe(2);
    expect(result.conflictCount).toBe(1);
    expect(result.conflicts).toHaveLength(2);
    expect(result.conflicts[0].exists).toBe(true); // main.c exists
    expect(result.conflicts[0].targetFileName).toBe('main.c');
    expect(result.conflicts[1].exists).toBe(false); // helper.c doesn't exist
    expect(result.conflicts[1].targetFileName).toBe('helper.c');
  });

  it('returns no conflicts for empty target directory', async () => {
    const mockFiles: FileInfo[] = [
      { path: 'main.cpp', name: 'main.cpp', handle: {} as any, size: 100 }
    ];

    const mockTargetDir = {
      values: async function* () {
        // Empty directory
      }
    } as any;

    const result = await detectConflicts(mockFiles, mockTargetDir);

    expect(result.conflictCount).toBe(0);
    expect(result.totalFiles).toBe(1);
    expect(result.conflicts[0].exists).toBe(false);
  });

  it('detects all conflicts when all files exist', async () => {
    const mockFiles: FileInfo[] = [
      { path: 'a.cpp', name: 'a.cpp', handle: {} as any, size: 100 },
      { path: 'b.cpp', name: 'b.cpp', handle: {} as any, size: 200 },
      { path: 'c.cpp', name: 'c.cpp', handle: {} as any, size: 300 }
    ];

    const mockTargetDir = {
      values: async function* () {
        yield { kind: 'file', name: 'a.c' };
        yield { kind: 'file', name: 'b.c' };
        yield { kind: 'file', name: 'c.c' };
      }
    } as any;

    const result = await detectConflicts(mockFiles, mockTargetDir);

    expect(result.conflictCount).toBe(3);
    expect(result.totalFiles).toBe(3);
    expect(result.conflicts.every(c => c.exists)).toBe(true);
  });

  it('ignores directories in target', async () => {
    const mockFiles: FileInfo[] = [
      { path: 'main.cpp', name: 'main.cpp', handle: {} as any, size: 100 }
    ];

    const mockTargetDir = {
      values: async function* () {
        yield { kind: 'directory', name: 'subdir' };
        yield { kind: 'file', name: 'other.txt' };
      }
    } as any;

    const result = await detectConflicts(mockFiles, mockTargetDir);

    expect(result.conflictCount).toBe(0);
  });

  it('throws error if directory read fails', async () => {
    const mockFiles: FileInfo[] = [
      { path: 'main.cpp', name: 'main.cpp', handle: {} as any, size: 100 }
    ];

    const mockTargetDir = {
      values: async function* () {
        throw new Error('Permission denied');
      }
    } as any;

    await expect(detectConflicts(mockFiles, mockTargetDir)).rejects.toThrow(
      'Failed to read target directory contents'
    );
  });

  it('handles header files correctly', async () => {
    const mockFiles: FileInfo[] = [
      { path: 'common.hpp', name: 'common.hpp', handle: {} as any, size: 100 },
      { path: 'utils.h', name: 'utils.h', handle: {} as any, size: 200 }
    ];

    const mockTargetDir = {
      values: async function* () {
        yield { kind: 'file', name: 'common.h' };
      }
    } as any;

    const result = await detectConflicts(mockFiles, mockTargetDir);

    expect(result.totalFiles).toBe(2);
    expect(result.conflictCount).toBe(1);
    expect(result.conflicts[0].targetFileName).toBe('common.h');
    expect(result.conflicts[0].exists).toBe(true);
    expect(result.conflicts[1].targetFileName).toBe('utils.h');
    expect(result.conflicts[1].exists).toBe(false);
  });
});

describe('getConflictingFiles', () => {
  it('filters to only conflicting files', () => {
    const result = {
      conflicts: [
        { sourcePath: 'a.cpp', targetFileName: 'a.c', exists: true },
        { sourcePath: 'b.cpp', targetFileName: 'b.c', exists: false },
        { sourcePath: 'c.cpp', targetFileName: 'c.c', exists: true }
      ],
      totalFiles: 3,
      conflictCount: 2
    };

    const conflicting = getConflictingFiles(result);

    expect(conflicting).toHaveLength(2);
    expect(conflicting[0].sourcePath).toBe('a.cpp');
    expect(conflicting[1].sourcePath).toBe('c.cpp');
  });

  it('returns empty array when no conflicts', () => {
    const result = {
      conflicts: [
        { sourcePath: 'a.cpp', targetFileName: 'a.c', exists: false },
        { sourcePath: 'b.cpp', targetFileName: 'b.c', exists: false }
      ],
      totalFiles: 2,
      conflictCount: 0
    };

    const conflicting = getConflictingFiles(result);

    expect(conflicting).toHaveLength(0);
  });

  it('returns all when all are conflicts', () => {
    const result = {
      conflicts: [
        { sourcePath: 'a.cpp', targetFileName: 'a.c', exists: true },
        { sourcePath: 'b.cpp', targetFileName: 'b.c', exists: true }
      ],
      totalFiles: 2,
      conflictCount: 2
    };

    const conflicting = getConflictingFiles(result);

    expect(conflicting).toHaveLength(2);
  });
});
