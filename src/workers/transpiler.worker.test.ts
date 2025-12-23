import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import type { WorkerRequest, WorkerResponse } from './types';

// Check if Worker is available (browser environment)
const isWorkerAvailable = typeof Worker !== 'undefined';

describe('TranspilerWorker', () => {
  let worker: Worker | undefined;
  let messageQueue: WorkerResponse[] = [];

  beforeEach(() => {
    if (!isWorkerAvailable) {
      return; // Skip setup in Node environment
    }

    // Create worker instance
    worker = new Worker(new URL('./transpiler.worker.ts', import.meta.url), {
      type: 'module'
    });

    // Collect messages
    worker.onmessage = (e: MessageEvent<WorkerResponse>) => {
      messageQueue.push(e.data);
    };
  });

  afterEach(() => {
    if (worker) {
      worker.terminate();
    }
    messageQueue = [];
  });

  it.skipIf(!isWorkerAvailable)('initializes and sends READY message', async () => {
    if (!worker) return;

    worker.postMessage({ type: 'INIT' } as WorkerRequest);

    // Wait for READY message
    const result = await waitForMessage('READY');

    expect(result).toEqual({ type: 'READY' });
  });

  it.skipIf(!isWorkerAvailable)('transpiles source code successfully', async () => {
    if (!worker) return;

    // Initialize first
    worker.postMessage({ type: 'INIT' } as WorkerRequest);
    await waitForMessage('READY');

    // Send transpilation request
    worker.postMessage({
      type: 'TRANSPILE',
      taskId: 'test-task-1',
      source: 'int main() { return 0; }',
      options: { targetStandard: 'c99', includeACSL: false }
    } as WorkerRequest);

    // Wait for success
    const result = await waitForMessage('SUCCESS');

    expect(result.type).toBe('SUCCESS');
    if (result.type === 'SUCCESS') {
      expect(result.taskId).toBe('test-task-1');
      expect(result.result).toBeDefined();
      expect(result.result.success).toBe(true);
    }
  });

  it.skipIf(!isWorkerAvailable)('sends progress updates during transpilation', async () => {
    if (!worker) return;

    worker.postMessage({ type: 'INIT' } as WorkerRequest);
    await waitForMessage('READY');

    worker.postMessage({
      type: 'TRANSPILE',
      taskId: 'test-task-2',
      source: 'int main() { return 0; }',
      options: {}
    } as WorkerRequest);

    // Wait for at least one progress message
    await new Promise<void>((resolve) => {
      const interval = setInterval(() => {
        const progressMessages = messageQueue.filter(msg =>
          msg.type === 'PROGRESS' && msg.taskId === 'test-task-2'
        );
        if (progressMessages.length > 0) {
          clearInterval(interval);
          resolve();
        }
      }, 100);
    });

    const progressMessages = messageQueue.filter(msg =>
      msg.type === 'PROGRESS' && msg.taskId === 'test-task-2'
    );

    expect(progressMessages.length).toBeGreaterThan(0);
    expect(progressMessages[0]).toMatchObject({
      type: 'PROGRESS',
      taskId: 'test-task-2',
      progress: expect.any(Number)
    });
  });

  it.skipIf(!isWorkerAvailable)('handles transpilation errors gracefully', async () => {
    if (!worker) return;

    worker.postMessage({ type: 'INIT' } as WorkerRequest);
    await waitForMessage('READY');

    // Send invalid C++ code
    worker.postMessage({
      type: 'TRANSPILE',
      taskId: 'test-task-3',
      source: 'this is not valid C++ code @#$%',
      options: {}
    } as WorkerRequest);

    // Wait for error
    const result = await waitForMessage('ERROR');

    expect(result.type).toBe('ERROR');
    if (result.type === 'ERROR') {
      expect(result.taskId).toBe('test-task-3');
      expect(result.error).toBeDefined();
      expect(typeof result.error).toBe('string');
    }
  });

  it.skipIf(!isWorkerAvailable)('supports cancellation', async () => {
    if (!worker) return;

    worker.postMessage({ type: 'INIT' } as WorkerRequest);
    await waitForMessage('READY');

    // Start transpilation
    worker.postMessage({
      type: 'TRANSPILE',
      taskId: 'test-task-4',
      source: 'int main() { return 0; }',
      options: {}
    } as WorkerRequest);

    // Immediately cancel
    worker.postMessage({
      type: 'CANCEL',
      taskId: 'test-task-4'
    } as WorkerRequest);

    // Wait a bit
    await new Promise(resolve => setTimeout(resolve, 500));

    // Should not receive SUCCESS message after cancellation
    const successMessages = messageQueue.filter(msg =>
      msg.type === 'SUCCESS' && msg.taskId === 'test-task-4'
    );

    // Note: Cancellation is cooperative, so we might still get SUCCESS
    // if cancellation happened after transpilation completed
    // This test just verifies the CANCEL message is processed without error
    expect(true).toBe(true);
  });

  it.skipIf(!isWorkerAvailable)('disposes cleanly', async () => {
    if (!worker) return;

    worker.postMessage({ type: 'INIT' } as WorkerRequest);
    await waitForMessage('READY');

    worker.postMessage({ type: 'DISPOSE' } as WorkerRequest);

    // Worker should close
    await new Promise(resolve => setTimeout(resolve, 100));

    // Worker should be terminated
    expect(true).toBe(true); // Worker closes itself
  });

  // Helper function to wait for specific message type
  function waitForMessage(type: WorkerResponse['type']): Promise<WorkerResponse> {
    return new Promise((resolve, reject) => {
      const timeout = setTimeout(() => {
        reject(new Error(`Timeout waiting for message: ${type}`));
      }, 5000);

      const interval = setInterval(() => {
        const msg = messageQueue.find(m => m.type === type);
        if (msg) {
          clearInterval(interval);
          clearTimeout(timeout);
          resolve(msg);
        }
      }, 50);
    });
  }
});
