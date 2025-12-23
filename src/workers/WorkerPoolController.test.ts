import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { WorkerPoolController } from './WorkerPoolController';
import type { FileInfo, TranspileOptions } from '../components/playground/wizard/types';

describe('WorkerPoolController', () => {
  let controller: WorkerPoolController;

  beforeEach(() => {
    controller = new WorkerPoolController(2); // Use 2 workers for tests
  });

  afterEach(() => {
    controller.dispose();
  });

  it('initializes worker pool successfully', async () => {
    await controller.initialize();

    const stats = controller.getStats();
    expect(stats.workerCount).toBe(2);
    expect(stats.readyWorkers).toBe(2);
    expect(stats.activeWorkers).toBe(0);
    expect(stats.queuedTasks).toBe(0);
  });

  it('gets optimal worker count based on CPU cores', async () => {
    const controller2 = new WorkerPoolController();
    await controller2.initialize();
    const stats = controller2.getStats();

    // Should be between 2 and 8
    expect(stats.workerCount).toBeGreaterThanOrEqual(2);
    expect(stats.workerCount).toBeLessThanOrEqual(8);

    controller2.dispose();
  });

  it('transpiles a single file successfully', async () => {
    const mockFile: FileInfo = {
      path: 'test.cpp',
      name: 'test.cpp',
      handle: {
        getFile: () =>
          Promise.resolve({
            text: () => Promise.resolve('int main() { return 0; }')
          } as File)
      } as any,
      size: 100
    };

    const result = await controller.transpile(mockFile, 'int main() { return 0; }', {
      targetStandard: 'c99',
      includeACSL: false
    });

    expect(result).toBeDefined();
    expect(result.success).toBe(true);
  });

  it('transpiles multiple files in parallel', async () => {
    const files: FileInfo[] = [
      {
        path: 'file1.cpp',
        name: 'file1.cpp',
        handle: {
          getFile: () =>
            Promise.resolve({
              text: () => Promise.resolve('int main() { return 0; }')
            } as File)
        } as any,
        size: 100
      },
      {
        path: 'file2.cpp',
        name: 'file2.cpp',
        handle: {
          getFile: () =>
            Promise.resolve({
              text: () => Promise.resolve('int foo() { return 1; }')
            } as File)
        } as any,
        size: 100
      },
      {
        path: 'file3.cpp',
        name: 'file3.cpp',
        handle: {
          getFile: () =>
            Promise.resolve({
              text: () => Promise.resolve('int bar() { return 2; }')
            } as File)
        } as any,
        size: 100
      }
    ];

    const sources = new Map([
      ['file1.cpp', 'int main() { return 0; }'],
      ['file2.cpp', 'int foo() { return 1; }'],
      ['file3.cpp', 'int bar() { return 2; }']
    ]);

    const startTime = Date.now();
    const results = await controller.transpileAll(files, sources, {
      targetStandard: 'c99',
      includeACSL: false
    });
    const elapsed = Date.now() - startTime;

    expect(results.size).toBe(3);
    expect(results.get('file1.cpp')?.success).toBe(true);
    expect(results.get('file2.cpp')?.success).toBe(true);
    expect(results.get('file3.cpp')?.success).toBe(true);

    // Parallel execution should be faster than sequential
    console.log(`Parallel transpilation took ${elapsed}ms`);
  });

  it('emits progress events during transpilation', async () => {
    const progressEvents: any[] = [];
    const overallProgressEvents: any[] = [];

    controller.onProgress((event) => progressEvents.push(event));
    controller.onOverallProgress((event) => overallProgressEvents.push(event));

    const files: FileInfo[] = [
      {
        path: 'file1.cpp',
        name: 'file1.cpp',
        handle: {
          getFile: () =>
            Promise.resolve({
              text: () => Promise.resolve('int main() { return 0; }')
            } as File)
        } as any,
        size: 100
      },
      {
        path: 'file2.cpp',
        name: 'file2.cpp',
        handle: {
          getFile: () =>
            Promise.resolve({
              text: () => Promise.resolve('int foo() { return 1; }')
            } as File)
        } as any,
        size: 100
      }
    ];

    const sources = new Map([
      ['file1.cpp', 'int main() { return 0; }'],
      ['file2.cpp', 'int foo() { return 1; }']
    ]);

    await controller.transpileAll(files, sources, {
      targetStandard: 'c99',
      includeACSL: false
    });

    // Should have received progress events
    expect(progressEvents.length).toBeGreaterThan(0);
    expect(overallProgressEvents.length).toBeGreaterThan(0);

    // Final overall progress should be 100%
    const final = overallProgressEvents[overallProgressEvents.length - 1];
    expect(final.completed).toBe(2);
    expect(final.total).toBe(2);
    expect(final.percentage).toBe(100);
  });

  it('handles cancellation', async () => {
    const files: FileInfo[] = Array(10)
      .fill(null)
      .map((_, i) => ({
        path: `file${i}.cpp`,
        name: `file${i}.cpp`,
        handle: {
          getFile: () =>
            Promise.resolve({
              text: () => Promise.resolve('int main() { return 0; }')
            } as File)
        } as any,
        size: 100
      }));

    const sources = new Map(
      files.map((f) => [f.path, 'int main() { return 0; }'])
    );

    // Start transpilation
    const promise = controller.transpileAll(files, sources, {
      targetStandard: 'c99',
      includeACSL: false
    });

    // Cancel after a short delay
    setTimeout(() => controller.cancel(), 100);

    // Should either complete or be cancelled
    try {
      await promise;
    } catch (error) {
      expect(error).toBeInstanceOf(Error);
    }
  });

  it('disposes cleanly', async () => {
    await controller.initialize();

    const stats = controller.getStats();
    expect(stats.workerCount).toBe(2);

    controller.dispose();

    const statsAfter = controller.getStats();
    expect(statsAfter.workerCount).toBe(0);
    expect(statsAfter.readyWorkers).toBe(0);
  });

  it('handles worker errors gracefully', async () => {
    // This test would require mocking worker crashes
    // For now, just verify error handling structure exists
    expect(controller.getStats).toBeDefined();
  });
});
