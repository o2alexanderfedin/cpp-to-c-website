import '@testing-library/jest-dom';
import { vi } from 'vitest';

// Mock Worker for tests
class MockWorker {
  onmessage: ((e: MessageEvent) => void) | null = null;
  onerror: ((e: ErrorEvent) => void) | null = null;
  private messageHandlers: Set<(e: MessageEvent) => void> = new Set();

  constructor(public url: string | URL, public options?: WorkerOptions) {
    // Don't auto-send READY - wait for INIT
  }

  postMessage(message: any): void {
    // Use setTimeout to simulate async behavior but keep it very fast
    setTimeout(() => {
      if (message.type === 'INIT') {
        this.simulateMessage({ type: 'READY' });
      } else if (message.type === 'TRANSPILE') {
        // Simulate successful transpilation
        this.simulateMessage({
          type: 'PROGRESS',
          taskId: message.taskId,
          progress: 50,
          stage: 'transpiling'
        });

        setTimeout(() => {
          this.simulateMessage({
            type: 'SUCCESS',
            taskId: message.taskId,
            result: {
              success: true,
              cCode: '/* Transpiled C code */',
              sourcePath: 'test.cpp'
            }
          });
        }, 10);
      } else if (message.type === 'CANCEL') {
        // Cancellation doesn't send a response
      } else if (message.type === 'DISPOSE') {
        // Disposal doesn't send a response
      }
    }, 5);
  }

  addEventListener(event: string, handler: (e: MessageEvent) => void): void {
    if (event === 'message') {
      this.messageHandlers.add(handler);
    } else if (event === 'error') {
      this.onerror = handler as any;
    }
  }

  removeEventListener(event: string, handler: (e: MessageEvent) => void): void {
    if (event === 'message') {
      this.messageHandlers.delete(handler);
    } else if (event === 'error' && this.onerror === handler) {
      this.onerror = null;
    }
  }

  terminate(): void {
    // No-op for mock
  }

  private simulateMessage(data: any): void {
    const event = new MessageEvent('message', { data });

    // Call all registered handlers
    this.messageHandlers.forEach(handler => handler(event));

    // Also call onmessage if set
    if (this.onmessage) {
      this.onmessage(event);
    }
  }
}

// Make Worker available globally
(globalThis as any).Worker = MockWorker;
