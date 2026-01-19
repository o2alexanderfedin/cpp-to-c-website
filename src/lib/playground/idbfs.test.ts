/**
 * Unit tests for IDBFS operations
 *
 * Tests pure functions for ZIP extraction, directory creation,
 * argument building, and output packaging.
 *
 * Following TDD principles:
 * - Each test is isolated and focused
 * - Uses mocks for WASM module to avoid dependencies
 * - Tests both success and error cases
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { WASMModule, TranspilerOptions } from './idbfs-types';
import {
  createDirectoryRecursive,
  buildTranspilerArgs,
  listOutputFiles,
  detectSourceDirectory,
  validateZipStructure,
  IDBFS_MOUNT_POINT,
  OUTPUT_DIR,
} from './idbfs';

/**
 * Create mock WASM module
 */
function createMockModule(): WASMModule {
  const fileSystem = new Map<string, { isDir: boolean; content?: Uint8Array }>();

  const module: WASMModule = {
    FS: {
      mkdir: vi.fn((path: string) => {
        if (fileSystem.has(path)) {
          const error = new Error('File exists') as any;
          error.code = 'EEXIST';
          throw error;
        }
        fileSystem.set(path, { isDir: true });
      }),
      rmdir: vi.fn((path: string) => {
        fileSystem.delete(path);
      }),
      readdir: vi.fn((path: string): string[] => {
        const entries = ['.', '..'];
        for (const [key] of fileSystem) {
          if (key.startsWith(path + '/')) {
            const rest = key.substring(path.length + 1);
            const firstSlash = rest.indexOf('/');
            const name = firstSlash === -1 ? rest : rest.substring(0, firstSlash);
            if (!entries.includes(name)) {
              entries.push(name);
            }
          }
        }
        return entries;
      }),
      writeFile: vi.fn((path: string, data: Uint8Array | string) => {
        const content = typeof data === 'string' ? new TextEncoder().encode(data) : data;
        fileSystem.set(path, { isDir: false, content });
      }),
      readFile: vi.fn((path: string): Uint8Array | string => {
        const entry = fileSystem.get(path);
        if (!entry || entry.isDir) {
          throw new Error('Not a file');
        }
        return entry.content || new Uint8Array();
      }),
      stat: vi.fn((path: string) => {
        const entry = fileSystem.get(path);
        if (!entry) {
          throw new Error('No such file or directory');
        }
        return {
          dev: 0,
          ino: 0,
          mode: 0,
          nlink: 0,
          uid: 0,
          gid: 0,
          rdev: 0,
          size: entry.content?.length || 0,
          atime: new Date(),
          mtime: new Date(),
          ctime: new Date(),
          blksize: 0,
          blocks: 0,
          isFile: () => !entry.isDir,
          isDirectory: () => entry.isDir,
        };
      }),
      analyzePath: vi.fn((path: string) => ({
        exists: fileSystem.has(path),
        isRoot: path === '/',
      })),
      mount: vi.fn(),
      unmount: vi.fn(),
      syncfs: vi.fn((_populate: boolean, callback: (err: Error | null) => void) => {
        callback(null);
      }),
      unlink: vi.fn((path: string) => {
        fileSystem.delete(path);
      }),
      filesystems: {
        IDBFS: function() {} as any,
        MEMFS: function() {} as any,
        NODEFS: function() {} as any,
        WORKERFS: function() {} as any,
      },
    },
    callMain: vi.fn(() => 0),
  };

  return module;
}

describe('createDirectoryRecursive', () => {
  it('should create single directory', () => {
    const module = createMockModule();
    createDirectoryRecursive('/test', module.FS);

    expect(module.FS.mkdir).toHaveBeenCalledWith('/test');
  });

  it('should create nested directories', () => {
    const module = createMockModule();
    createDirectoryRecursive('/test/nested/deep', module.FS);

    expect(module.FS.mkdir).toHaveBeenCalledWith('/test');
    expect(module.FS.mkdir).toHaveBeenCalledWith('/test/nested');
    expect(module.FS.mkdir).toHaveBeenCalledWith('/test/nested/deep');
  });

  it('should not fail if directory already exists', () => {
    const module = createMockModule();

    // Create directory first
    createDirectoryRecursive('/test', module.FS);

    // Should not throw when creating again
    expect(() => createDirectoryRecursive('/test', module.FS)).not.toThrow();
  });
});

describe('buildTranspilerArgs', () => {
  it('should build basic arguments with defaults', () => {
    const options: TranspilerOptions = {};
    const args = buildTranspilerArgs(options);

    expect(args).toContain('--source-dir=/project/src');
    expect(args).toContain('--output-dir=/project/output');
    expect(args).toContain('--');
    expect(args).toContain('-target');
    expect(args).toContain('x86_64-unknown-linux-gnu');
    expect(args).toContain('-std=c++17');
    expect(args).toContain('-I/project/include');
  });

  it('should include ACSL flags when enabled', () => {
    const options: TranspilerOptions = {
      generateACSL: true,
      acslLevel: 'full',
    };
    const args = buildTranspilerArgs(options);

    expect(args).toContain('--generate-acsl');
    expect(args).toContain('--acsl-level=full');
  });

  it('should include pragma once flag when enabled', () => {
    const options: TranspilerOptions = {
      usePragmaOnce: true,
    };
    const args = buildTranspilerArgs(options);

    expect(args).toContain('--use-pragma-once');
  });

  it('should disable exceptions when explicitly set to false', () => {
    const options: TranspilerOptions = {
      enableExceptions: false,
    };
    const args = buildTranspilerArgs(options);

    expect(args).toContain('--enable-exceptions=off');
  });

  it('should disable RTTI when explicitly set to false', () => {
    const options: TranspilerOptions = {
      enableRTTI: false,
    };
    const args = buildTranspilerArgs(options);

    expect(args).toContain('--enable-rtti=off');
  });

  it('should use specified C++ standard', () => {
    const standards: Array<TranspilerOptions['cppStandard']> = ['c++11', 'c++14', 'c++17', 'c++20'];

    standards.forEach(std => {
      const options: TranspilerOptions = { cppStandard: std };
      const args = buildTranspilerArgs(options);
      expect(args).toContain(`-std=${std}`);
    });
  });

  it('should include custom include directories', () => {
    const options: TranspilerOptions = {
      includeDirs: ['/custom/include', '/another/path'],
    };
    const args = buildTranspilerArgs(options);

    expect(args).toContain('-I/custom/include');
    expect(args).toContain('-I/another/path');
  });

  it('should include additional compiler flags', () => {
    const options: TranspilerOptions = {
      additionalFlags: ['-Wall', '-Wextra', '-O2'],
    };
    const args = buildTranspilerArgs(options);

    expect(args).toContain('-Wall');
    expect(args).toContain('-Wextra');
    expect(args).toContain('-O2');
  });
});

describe('listOutputFiles', () => {
  it('should return empty array when output directory does not exist', () => {
    const module = createMockModule();
    const files = listOutputFiles(module, OUTPUT_DIR);

    expect(files).toEqual([]);
  });

  it('should list files in output directory', () => {
    const module = createMockModule();

    // Create output directory and files
    module.FS.mkdir(OUTPUT_DIR);
    module.FS.writeFile(`${OUTPUT_DIR}/file1.c`, 'content1');
    module.FS.writeFile(`${OUTPUT_DIR}/file2.h`, 'content2');

    const files = listOutputFiles(module, OUTPUT_DIR);

    expect(files).toContain(`${OUTPUT_DIR}/file1.c`);
    expect(files).toContain(`${OUTPUT_DIR}/file2.h`);
    expect(files).not.toContain(`${OUTPUT_DIR}/.`);
    expect(files).not.toContain(`${OUTPUT_DIR}/..`);
  });

  it('should recursively list files in subdirectories', () => {
    const module = createMockModule();

    // Create output directory with subdirectories
    module.FS.mkdir(OUTPUT_DIR);
    module.FS.mkdir(`${OUTPUT_DIR}/subdir`);
    module.FS.writeFile(`${OUTPUT_DIR}/file1.c`, 'content1');
    module.FS.writeFile(`${OUTPUT_DIR}/subdir/file2.c`, 'content2');

    const files = listOutputFiles(module, OUTPUT_DIR);

    expect(files).toContain(`${OUTPUT_DIR}/file1.c`);
    expect(files).toContain(`${OUTPUT_DIR}/subdir/file2.c`);
  });
});

describe('detectSourceDirectory', () => {
  it('should detect /project/src if it exists', () => {
    const module = createMockModule();
    module.FS.mkdir(IDBFS_MOUNT_POINT);
    module.FS.mkdir(`${IDBFS_MOUNT_POINT}/src`);

    const sourceDir = detectSourceDirectory(module);

    expect(sourceDir).toBe(`${IDBFS_MOUNT_POINT}/src`);
  });

  it('should detect /project/source if /src does not exist', () => {
    const module = createMockModule();
    module.FS.mkdir(IDBFS_MOUNT_POINT);
    module.FS.mkdir(`${IDBFS_MOUNT_POINT}/source`);

    const sourceDir = detectSourceDirectory(module);

    expect(sourceDir).toBe(`${IDBFS_MOUNT_POINT}/source`);
  });

  it('should find directory with cpp files', () => {
    const module = createMockModule();
    module.FS.mkdir(IDBFS_MOUNT_POINT);
    module.FS.mkdir(`${IDBFS_MOUNT_POINT}/code`);
    module.FS.writeFile(`${IDBFS_MOUNT_POINT}/code/main.cpp`, 'content');

    const sourceDir = detectSourceDirectory(module);

    expect(sourceDir).toBe(`${IDBFS_MOUNT_POINT}/code`);
  });

  it('should default to /project/src if nothing found', () => {
    const module = createMockModule();
    module.FS.mkdir(IDBFS_MOUNT_POINT);

    const sourceDir = detectSourceDirectory(module);

    expect(sourceDir).toBe(`${IDBFS_MOUNT_POINT}/src`);
  });
});

describe('validateZipStructure', () => {
  it('should accept ZIP with C++ source files', async () => {
    const files = {
      'src/main.cpp': 'int main() { return 0; }',
      'include/utils.h': '#pragma once',
    };

    // Create mock ZIP file
    const JSZipMock = (await import('jszip')).default;
    const zip = new JSZipMock();
    for (const [path, content] of Object.entries(files)) {
      zip.file(path, content);
    }
    const blob = await zip.generateAsync({ type: 'blob' });
    const file = new File([blob], 'test.zip', { type: 'application/zip' });

    const result = await validateZipStructure(file);

    expect(result.success).toBe(true);
    expect(result.cppFileCount).toBe(1);
    expect(result.message).toContain('1 C++ source file');
    expect(result.message).toContain('header files');
  });

  it('should reject ZIP with no C++ files', async () => {
    const JSZipMock = (await import('jszip')).default;
    const zip = new JSZipMock();
    zip.file('readme.txt', 'This is a readme');
    const blob = await zip.generateAsync({ type: 'blob' });
    const file = new File([blob], 'test.zip', { type: 'application/zip' });

    const result = await validateZipStructure(file);

    expect(result.success).toBe(false);
    expect(result.cppFileCount).toBe(0);
    expect(result.message).toContain('no C++ source files');
  });

  it('should handle invalid ZIP files', async () => {
    const invalidZip = new File(['invalid content'], 'test.zip', { type: 'application/zip' });

    const result = await validateZipStructure(invalidZip);

    expect(result.success).toBe(false);
    expect(result.message).toContain('Invalid ZIP');
  });

  it('should count multiple C++ files correctly', async () => {
    const JSZipMock = (await import('jszip')).default;
    const zip = new JSZipMock();
    zip.file('main.cpp', 'int main() {}');
    zip.file('utils.cxx', 'void utils() {}');
    zip.file('helper.cc', 'void helper() {}');
    const blob = await zip.generateAsync({ type: 'blob' });
    const file = new File([blob], 'test.zip', { type: 'application/zip' });

    const result = await validateZipStructure(file);

    expect(result.success).toBe(true);
    expect(result.cppFileCount).toBe(3);
    expect(result.message).toContain('3 C++ source files');
  });
});
