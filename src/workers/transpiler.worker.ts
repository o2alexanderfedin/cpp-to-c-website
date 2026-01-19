/// <reference lib="webworker" />

import { WasmTranspilerAdapter } from '../adapters/WasmTranspilerAdapter';
import type { WorkerRequest, WorkerResponse, WorkerState } from './types';

/**
 * Transpiler Web Worker
 * Runs WASM transpilation off the main thread
 *
 * Architecture:
 * - Dedicated worker (own WASM instance)
 * - Message-based communication
 * - Cooperative cancellation
 * - Progress reporting
 */

// Worker state
const state: WorkerState = {
  initialized: false,
  currentTaskId: null,
  canceled: false
};

let adapter: WasmTranspilerAdapter | null = null;

/**
 * Send message to main thread
 */
function postResponse(response: WorkerResponse): void {
  self.postMessage(response);
}

/**
 * Initialize WASM adapter
 */
async function initialize(): Promise<void> {
  if (state.initialized) {
    return; // Already initialized
  }

  try {
    adapter = new WasmTranspilerAdapter();

    // Pre-initialize WASM module by running a minimal transpilation
    // This loads the WASM binary and initializes the module
    await adapter.transpile('', {});

    state.initialized = true;
    postResponse({ type: 'READY' });
  } catch (error) {
    postResponse({
      type: 'ERROR',
      taskId: 'init',
      error: error instanceof Error ? error.message : String(error),
      stack: error instanceof Error ? error.stack : undefined
    });
  }
}

/**
 * Transpile source code
 */
async function transpile(
  taskId: string,
  source: string,
  options?: any
): Promise<void> {
  if (!adapter) {
    throw new Error('Worker not initialized');
  }

  state.currentTaskId = taskId;
  state.canceled = false;

  try {
    // Start progress reporting
    const progressInterval = setInterval(() => {
      if (!state.canceled && state.currentTaskId === taskId) {
        postResponse({
          type: 'PROGRESS',
          taskId,
          progress: 50, // Indeterminate for now (WASM is synchronous)
          stage: 'transpiling'
        });
      }
    }, 200); // 5 updates per second

    try {
      // Perform transpilation
      // Note: This is synchronous in C++, cannot be interrupted mid-execution
      const result = await adapter.transpile(source, options || {});

      // Clear progress interval
      clearInterval(progressInterval);

      // Check if canceled after completion
      if (state.canceled) {
        return; // Don't send result if canceled
      }

      // Check if transpilation failed
      if (!result.success) {
        // Send error response
        postResponse({
          type: 'ERROR',
          taskId,
          error: result.error || 'Transpilation failed',
          stack: undefined
        });
        return;
      }

      // Send success response
      postResponse({
        type: 'SUCCESS',
        taskId,
        result
      });
    } finally {
      clearInterval(progressInterval);
      state.currentTaskId = null;
    }
  } catch (error) {
    postResponse({
      type: 'ERROR',
      taskId,
      error: error instanceof Error ? error.message : String(error),
      stack: error instanceof Error ? error.stack : undefined
    });
  }
}

/**
 * Cancel current task
 */
function cancel(taskId: string): void {
  if (state.currentTaskId === taskId) {
    state.canceled = true;
  }
}

/**
 * Dispose worker resources
 */
function dispose(): void {
  adapter?.dispose?.(); // Call dispose if it exists
  adapter = null;
  state.initialized = false;
  state.currentTaskId = null;
  state.canceled = false;
  self.close();
}

/**
 * Message handler
 */
self.onmessage = async (e: MessageEvent<WorkerRequest>) => {
  const msg = e.data;

  try {
    switch (msg.type) {
      case 'INIT':
        await initialize();
        break;

      case 'TRANSPILE':
        await transpile(msg.taskId, msg.source, msg.options);
        break;

      case 'CANCEL':
        cancel(msg.taskId);
        break;

      case 'DISPOSE':
        dispose();
        break;

      default:
        // TypeScript exhaustiveness check
        const _exhaustive: never = msg;
        throw new Error(`Unknown message type: ${JSON.stringify(_exhaustive)}`);
    }
  } catch (error) {
    postResponse({
      type: 'ERROR',
      taskId: msg.type === 'TRANSPILE' ? msg.taskId : 'unknown',
      error: error instanceof Error ? error.message : String(error),
      stack: error instanceof Error ? error.stack : undefined
    });
  }
};

/**
 * Global error handler
 */
self.onerror = (event) => {
  postResponse({
    type: 'ERROR',
    taskId: state.currentTaskId || 'unknown',
    error: event.message || 'Unknown worker error',
    stack: event.error?.stack
  });
};

/**
 * Unhandled rejection handler
 */
self.onunhandledrejection = (event) => {
  postResponse({
    type: 'ERROR',
    taskId: state.currentTaskId || 'unknown',
    error: event.reason instanceof Error ? event.reason.message : String(event.reason),
    stack: event.reason instanceof Error ? event.reason.stack : undefined
  });
};
