import { describe, it, expect, beforeEach } from 'vitest';
import { TranspileService } from './TranspileService';
import { MockFileSystem } from '../../adapters/MockFileSystem';
import { MockTranspiler } from '../../adapters/MockTranspiler';
import { MockProgressReporter } from '../../adapters/MockProgressReporter';
import type { IFileSystem } from '../../core/interfaces/IFileSystem';
import type { ITranspiler } from '../../core/interfaces/ITranspiler';
import type { IProgressReporter } from '../../core/interfaces/IProgressReporter';

/**
 * TranspileService Test Suite
 *
 * Tests the core transpilation orchestration service following TDD principles
 */
describe('TranspileService', () => {
  let service: TranspileService;
  let mockFs: MockFileSystem;
  let mockTranspiler: MockTranspiler;
  let mockProgress: MockProgressReporter;

  beforeEach(() => {
    mockFs = new MockFileSystem();
    mockTranspiler = new MockTranspiler();
    mockProgress = new MockProgressReporter();
    service = new TranspileService(mockFs, mockTranspiler, mockProgress);
  });

  describe('constructor', () => {
    it('should accept dependencies via constructor injection', () => {
      expect(service).toBeDefined();
      expect(service).toBeInstanceOf(TranspileService);
    });

    it('should work with different implementations of interfaces', () => {
      const customFs: IFileSystem = mockFs;
      const customTranspiler: ITranspiler = mockTranspiler;
      const customProgress: IProgressReporter = mockProgress;

      const customService = new TranspileService(customFs, customTranspiler, customProgress);
      expect(customService).toBeDefined();
    });
  });

  describe('transpileProject', () => {
    it('should transpile a single C++ file', async () => {
      // Arrange
      mockFs.addFile('/source/main.cpp', 'int main() { return 0; }');
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.success).toBe(true);
      expect(result.filesProcessed).toBe(1);
      expect(result.errors).toHaveLength(0);
      expect(await mockFs.exists('/target/main.c')).toBe(true);
    });

    it('should transpile multiple C++ files', async () => {
      // Arrange
      mockFs.addFile('/source/main.cpp', 'int main() {}');
      mockFs.addFile('/source/utils.cpp', 'void util() {}');
      mockFs.addFile('/source/helper.cpp', 'int helper() { return 42; }');
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.success).toBe(true);
      expect(result.filesProcessed).toBe(3);
      expect(await mockFs.exists('/target/main.c')).toBe(true);
      expect(await mockFs.exists('/target/utils.c')).toBe(true);
      expect(await mockFs.exists('/target/helper.c')).toBe(true);
    });

    it('should preserve directory structure', async () => {
      // Arrange
      mockFs.addFile('/source/main.cpp', 'int main() {}');
      mockFs.addFile('/source/lib/utils.cpp', 'void util() {}');
      mockFs.addFile('/source/lib/core/helper.cpp', 'int helper() {}');
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.success).toBe(true);
      expect(await mockFs.exists('/target/main.c')).toBe(true);
      expect(await mockFs.exists('/target/lib/utils.c')).toBe(true);
      expect(await mockFs.exists('/target/lib/core/helper.c')).toBe(true);
    });

    it('should only transpile C++ files (filter by extension)', async () => {
      // Arrange
      mockFs.addFile('/source/main.cpp', 'int main() {}');
      mockFs.addFile('/source/utils.cc', 'void util() {}');
      mockFs.addFile('/source/helper.cxx', 'int helper() {}');
      mockFs.addFile('/source/header.h', 'void func();');
      mockFs.addFile('/source/header.hpp', 'class Foo {};');
      mockFs.addFile('/source/readme.txt', 'README');
      mockFs.addFile('/source/config.json', '{}');
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.success).toBe(true);
      expect(result.filesProcessed).toBe(5); // .cpp, .cc, .cxx, .h, .hpp
      expect(await mockFs.exists('/target/main.c')).toBe(true);
      expect(await mockFs.exists('/target/utils.c')).toBe(true);
      expect(await mockFs.exists('/target/helper.c')).toBe(true);
      expect(await mockFs.exists('/target/header.h')).toBe(true);
      expect(await mockFs.exists('/target/header.hpp')).toBe(true);
      expect(await mockFs.exists('/target/readme.txt')).toBe(false);
      expect(await mockFs.exists('/target/config.json')).toBe(false);
    });

    it('should handle empty directory', async () => {
      // Arrange
      mockFs.addDirectory('/source');
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.success).toBe(true);
      expect(result.filesProcessed).toBe(0);
      expect(result.errors).toHaveLength(0);
    });

    it('should report progress during transpilation', async () => {
      // Arrange
      mockFs.addFile('/source/file1.cpp', 'int a;');
      mockFs.addFile('/source/file2.cpp', 'int b;');
      mockFs.addFile('/source/file3.cpp', 'int c;');
      mockFs.addDirectory('/target');

      // Act
      await service.transpileProject('/source', '/target');

      // Assert
      expect(mockProgress.startCalled).toBe(true);
      expect(mockProgress.startTotal).toBe(3);
      expect(mockProgress.updateCallCount).toBeGreaterThanOrEqual(3);
      expect(mockProgress.completeCalled).toBe(true);
    });

    it('should continue processing on individual file error', async () => {
      // Arrange
      mockFs.addFile('/source/good1.cpp', 'int main() {}');
      mockFs.addFile('/source/bad.cpp', 'invalid C++ syntax {{{');
      mockFs.addFile('/source/good2.cpp', 'void func() {}');
      mockFs.addDirectory('/target');

      // Configure transpiler to fail on bad.cpp
      mockTranspiler.setShouldFail((path) => path.includes('bad.cpp'));

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.success).toBe(true); // Overall success despite one error
      expect(result.filesProcessed).toBe(3); // All 3 files attempted
      expect(result.errors).toHaveLength(1);
      expect(result.errors[0]).toContain('bad.cpp');
      expect(await mockFs.exists('/target/good1.c')).toBe(true);
      expect(await mockFs.exists('/target/good2.c')).toBe(true);
      expect(await mockFs.exists('/target/bad.c')).toBe(false); // Failed file not written
    });

    it('should collect multiple errors', async () => {
      // Arrange
      mockFs.addFile('/source/bad1.cpp', 'syntax error 1');
      mockFs.addFile('/source/bad2.cpp', 'syntax error 2');
      mockFs.addFile('/source/good.cpp', 'int main() {}');
      mockFs.addDirectory('/target');

      // Configure transpiler to fail on bad files
      mockTranspiler.setShouldFail((path) => path.includes('bad'));

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.errors).toHaveLength(2);
      expect(result.errors.some(e => e.includes('bad1.cpp'))).toBe(true);
      expect(result.errors.some(e => e.includes('bad2.cpp'))).toBe(true);
    });

    it('should update progress after each file', async () => {
      // Arrange
      mockFs.addFile('/source/file1.cpp', 'int a;');
      mockFs.addFile('/source/file2.cpp', 'int b;');
      mockFs.addFile('/source/file3.cpp', 'int c;');
      mockFs.addDirectory('/target');

      // Act
      await service.transpileProject('/source', '/target');

      // Assert
      const updates = mockProgress.updates;
      expect(updates.length).toBeGreaterThanOrEqual(3);
      expect(updates[0].current).toBe(1);
      expect(updates[0].total).toBe(3);
      expect(updates[1].current).toBe(2);
      expect(updates[2].current).toBe(3);
    });

    it('should report file-level progress messages', async () => {
      // Arrange
      mockFs.addFile('/source/main.cpp', 'int main() {}');
      mockFs.addDirectory('/target');

      // Act
      await service.transpileProject('/source', '/target');

      // Assert
      const updates = mockProgress.updates;
      expect(updates.some(u => u.message?.includes('main.cpp'))).toBe(true);
    });
  });

  describe('cancellation support', () => {
    it('should support cancellation via AbortSignal', async () => {
      // Arrange
      mockFs.addFile('/source/file1.cpp', 'int a;');
      mockFs.addFile('/source/file2.cpp', 'int b;');
      mockFs.addFile('/source/file3.cpp', 'int c;');
      mockFs.addDirectory('/target');

      const controller = new AbortController();

      // Cancel after first file
      mockTranspiler.onTranspile = () => {
        controller.abort();
      };

      // Act & Assert
      await expect(
        service.transpileProject('/source', '/target', { signal: controller.signal })
      ).rejects.toThrow('Operation cancelled');
    });

    it('should clean up resources on cancellation', async () => {
      // Arrange
      mockFs.addFile('/source/file1.cpp', 'int a;');
      mockFs.addFile('/source/file2.cpp', 'int b;');
      mockFs.addDirectory('/target');

      const controller = new AbortController();
      mockTranspiler.onTranspile = () => controller.abort();

      // Act
      try {
        await service.transpileProject('/source', '/target', { signal: controller.signal });
      } catch (error) {
        // Expected cancellation error
      }

      // Assert - progress reporter should receive error notification
      expect(mockProgress.errorCalled).toBe(true);
    });
  });

  describe('parallel processing', () => {
    it('should process files in parallel', async () => {
      // Arrange
      mockFs.addFile('/source/file1.cpp', 'int a;');
      mockFs.addFile('/source/file2.cpp', 'int b;');
      mockFs.addFile('/source/file3.cpp', 'int c;');
      mockFs.addFile('/source/file4.cpp', 'int d;');
      mockFs.addDirectory('/target');

      const startTimes: number[] = [];
      const endTimes: number[] = [];

      mockTranspiler.onTranspile = async () => {
        startTimes.push(Date.now());
        await new Promise(resolve => setTimeout(resolve, 10));
        endTimes.push(Date.now());
      };

      // Act
      const start = Date.now();
      await service.transpileProject('/source', '/target', { concurrency: 2 });
      const duration = Date.now() - start;

      // Assert - parallel processing should be faster than sequential
      // With concurrency=2 and 4 files of 10ms each, should take ~20ms not 40ms
      expect(duration).toBeLessThan(35); // Allow some overhead
      expect(startTimes.length).toBe(4);
    });

    it('should respect concurrency limit', async () => {
      // Arrange
      mockFs.addFile('/source/file1.cpp', 'int a;');
      mockFs.addFile('/source/file2.cpp', 'int b;');
      mockFs.addFile('/source/file3.cpp', 'int c;');
      mockFs.addFile('/source/file4.cpp', 'int d;');
      mockFs.addDirectory('/target');

      let concurrentCount = 0;
      let maxConcurrent = 0;

      mockTranspiler.onTranspile = async () => {
        concurrentCount++;
        maxConcurrent = Math.max(maxConcurrent, concurrentCount);
        await new Promise(resolve => setTimeout(resolve, 10));
        concurrentCount--;
      };

      // Act
      await service.transpileProject('/source', '/target', { concurrency: 2 });

      // Assert
      expect(maxConcurrent).toBeLessThanOrEqual(2);
    });

    it('should default to reasonable concurrency', async () => {
      // Arrange
      mockFs.addFile('/source/file1.cpp', 'int a;');
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert - should work without explicit concurrency setting
      expect(result.success).toBe(true);
    });
  });

  describe('error handling', () => {
    it('should handle file system read errors', async () => {
      // Arrange
      mockFs.addFile('/source/file.cpp', 'int a;');
      mockFs.addDirectory('/target');
      mockFs.setShouldFailRead((path) => path.includes('file.cpp'));

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.errors).toHaveLength(1);
      expect(result.errors[0]).toContain('file.cpp');
    });

    it('should handle file system write errors', async () => {
      // Arrange
      mockFs.addFile('/source/file.cpp', 'int a;');
      mockFs.addDirectory('/target');
      mockFs.setShouldFailWrite((path) => path.includes('file.c'));

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.errors).toHaveLength(1);
      expect(result.errors[0]).toContain('file.c');
    });

    it('should handle transpilation errors', async () => {
      // Arrange
      mockFs.addFile('/source/file.cpp', 'invalid syntax');
      mockFs.addDirectory('/target');
      mockTranspiler.setShouldFail(() => true);

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.errors).toHaveLength(1);
    });

    it('should provide detailed error messages', async () => {
      // Arrange
      mockFs.addFile('/source/file.cpp', 'int a;');
      mockFs.addDirectory('/target');
      mockTranspiler.setShouldFail(() => true);
      mockTranspiler.setErrorMessage('Parse error at line 1: unexpected token');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.errors[0]).toContain('file.cpp');
      expect(result.errors[0]).toContain('Parse error at line 1');
    });
  });

  describe('edge cases', () => {
    it('should handle files with same name in different directories', async () => {
      // Arrange
      mockFs.addFile('/source/dir1/main.cpp', 'int a;');
      mockFs.addFile('/source/dir2/main.cpp', 'int b;');
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.success).toBe(true);
      expect(await mockFs.exists('/target/dir1/main.c')).toBe(true);
      expect(await mockFs.exists('/target/dir2/main.c')).toBe(true);

      const content1 = await mockFs.readFile('/target/dir1/main.c');
      const content2 = await mockFs.readFile('/target/dir2/main.c');
      expect(content1).not.toBe(content2); // Different transpiled content
    });

    it('should handle deeply nested directory structures', async () => {
      // Arrange
      mockFs.addFile('/source/a/b/c/d/e/file.cpp', 'int x;');
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.success).toBe(true);
      expect(await mockFs.exists('/target/a/b/c/d/e/file.c')).toBe(true);
    });

    it('should handle special characters in filenames', async () => {
      // Arrange
      mockFs.addFile('/source/file-with-dashes.cpp', 'int a;');
      mockFs.addFile('/source/file_with_underscores.cpp', 'int b;');
      mockFs.addFile('/source/file.with.dots.cpp', 'int c;');
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.success).toBe(true);
      expect(result.filesProcessed).toBe(3);
    });

    it('should handle very large number of files', async () => {
      // Arrange
      for (let i = 0; i < 100; i++) {
        mockFs.addFile(`/source/file${i}.cpp`, `int x${i};`);
      }
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target', { concurrency: 10 });

      // Assert
      expect(result.success).toBe(true);
      expect(result.filesProcessed).toBe(100);
      expect(result.errors).toHaveLength(0);
    });
  });

  describe('statistics and reporting', () => {
    it('should report total files processed', async () => {
      // Arrange
      mockFs.addFile('/source/file1.cpp', 'int a;');
      mockFs.addFile('/source/file2.cpp', 'int b;');
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.filesProcessed).toBe(2);
    });

    it('should report success count', async () => {
      // Arrange
      mockFs.addFile('/source/good1.cpp', 'int a;');
      mockFs.addFile('/source/good2.cpp', 'int b;');
      mockFs.addFile('/source/bad.cpp', 'syntax error');
      mockFs.addDirectory('/target');
      mockTranspiler.setShouldFail((path) => path.includes('bad'));

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.successCount).toBe(2);
      expect(result.errorCount).toBe(1);
    });

    it('should report elapsed time', async () => {
      // Arrange
      mockFs.addFile('/source/file.cpp', 'int a;');
      mockFs.addDirectory('/target');

      // Act
      const result = await service.transpileProject('/source', '/target');

      // Assert
      expect(result.elapsedMs).toBeGreaterThan(0);
      expect(typeof result.elapsedMs).toBe('number');
    });
  });
});
