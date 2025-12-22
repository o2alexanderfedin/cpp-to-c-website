/**
 * IProgressReporter - Progress Reporting Abstraction Interface
 *
 * Provides abstraction for progress reporting to enable testing
 * and support multiple UI implementations (console, web UI, etc.)
 *
 * Following SOLID principles:
 * - Interface Segregation: Focused on progress reporting only
 * - Dependency Inversion: Services depend on this abstraction
 */

import type { ProgressState } from './types';

/**
 * Progress reporting abstraction
 */
export interface IProgressReporter {
  /**
   * Start progress tracking
   *
   * @param total - Total number of items to process
   */
  start(total: number): void;

  /**
   * Update progress
   *
   * @param current - Current number of items processed
   * @param message - Optional progress message
   */
  update(current: number, message?: string): void;

  /**
   * Mark progress as complete
   */
  complete(): void;

  /**
   * Report an error
   *
   * @param message - Error message
   */
  error(message: string): void;

  /**
   * Get current progress state
   *
   * @returns Current progress state
   */
  getState(): ProgressState;
}
