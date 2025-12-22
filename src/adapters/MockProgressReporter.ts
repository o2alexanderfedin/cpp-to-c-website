/**
 * MockProgressReporter - Mock Progress Reporter
 *
 * Test implementation of IProgressReporter that tracks progress in memory.
 * Used for unit testing without requiring UI updates.
 *
 * Following SOLID principles:
 * - Single Responsibility: Only tracks progress state
 * - Liskov Substitution: Can replace any IProgressReporter implementation
 */

import type { IProgressReporter } from '../core/interfaces/IProgressReporter';
import type { ProgressState } from '../core/interfaces/types';

/**
 * Mock progress reporter for testing
 */
export class MockProgressReporter implements IProgressReporter {
  private state: ProgressState = {
    total: 0,
    current: 0,
    percentage: 0,
  };

  /**
   * Start progress tracking
   */
  start(total: number): void {
    this.state = {
      total,
      current: 0,
      percentage: 0,
      message: undefined,
    };
  }

  /**
   * Update progress
   */
  update(current: number, message?: string): void {
    this.state.current = current;
    this.state.message = message;
    this.state.percentage = this.calculatePercentage(current, this.state.total);
  }

  /**
   * Mark progress as complete
   */
  complete(): void {
    this.state.current = this.state.total;
    this.state.percentage = 100;
    this.state.message = undefined;
  }

  /**
   * Report an error
   */
  error(message: string): void {
    this.state.message = message;
  }

  /**
   * Get current progress state
   */
  getState(): ProgressState {
    return { ...this.state };
  }

  /**
   * Calculate percentage complete
   * @private
   */
  private calculatePercentage(current: number, total: number): number {
    if (total === 0) {
      return 0;
    }

    const percentage = (current / total) * 100;

    // Clamp to 0-100 range
    return Math.min(100, Math.max(0, Math.round(percentage)));
  }

  /**
   * Test helper: Reset state
   */
  reset(): void {
    this.state = {
      total: 0,
      current: 0,
      percentage: 0,
    };
  }

  /**
   * Test helper: Get history of all updates (for advanced testing)
   */
  private history: Array<{
    action: 'start' | 'update' | 'complete' | 'error';
    timestamp: number;
    data?: unknown;
  }> = [];

  /**
   * Enable history tracking for testing
   */
  enableHistory(): void {
    this.history = [];
  }

  /**
   * Get update history
   */
  getHistory(): typeof this.history {
    return [...this.history];
  }

  /**
   * Record history entry
   * @private
   */
  private recordHistory(
    action: 'start' | 'update' | 'complete' | 'error',
    data?: unknown
  ): void {
    if (this.history) {
      this.history.push({
        action,
        timestamp: Date.now(),
        data,
      });
    }
  }
}
