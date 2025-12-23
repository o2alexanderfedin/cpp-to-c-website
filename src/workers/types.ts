/**
 * Worker message protocol types
 * Following discriminated union pattern for type safety
 */

import type { TranspileOptions, TranspileResult } from '../core/interfaces/types';

/**
 * Messages sent from main thread to worker
 */
export type WorkerRequest =
  | { type: 'INIT' }
  | { type: 'TRANSPILE'; taskId: string; source: string; options?: TranspileOptions }
  | { type: 'CANCEL'; taskId: string }
  | { type: 'DISPOSE' };

/**
 * Messages sent from worker to main thread
 */
export type WorkerResponse =
  | { type: 'READY' }
  | { type: 'PROGRESS'; taskId: string; progress: number; stage?: string }
  | { type: 'SUCCESS'; taskId: string; result: TranspileResult }
  | { type: 'ERROR'; taskId: string; error: string; stack?: string };

/**
 * Worker state
 */
export interface WorkerState {
  initialized: boolean;
  currentTaskId: string | null;
  canceled: boolean;
}

// Re-export core types for convenience
export type { TranspileOptions, TranspileResult } from '../core/interfaces/types';
