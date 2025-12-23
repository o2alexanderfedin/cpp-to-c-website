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

  // Test tracking properties
  public startCalled = false;
  public startTotal = 0;
  public updateCallCount = 0;
  public updates: Array<{ current: number; total: number; message?: string }> = [];
  public completeCalled = false;
  public errorCalled = false;
  public lastErrorMessage?: string;

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
    this.startCalled = true;
    this.startTotal = total;
  }

  /**
   * Update progress
   */
  update(current: number, message?: string): void {
    this.state.current = current;
    this.state.message = message;
    this.state.percentage = this.calculatePercentage(current, this.state.total);
    this.updateCallCount++;
    this.updates.push({ current, total: this.state.total, message });
  }

  /**
   * Mark progress as complete
   */
  complete(): void {
    this.state.current = this.state.total;
    this.state.percentage = 100;
    this.state.message = undefined;
    this.completeCalled = true;
  }

  /**
   * Report an error
   */
  error(message: string): void {
    this.state.message = message;
    this.errorCalled = true;
    this.lastErrorMessage = message;
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
    this.startCalled = false;
    this.startTotal = 0;
    this.updateCallCount = 0;
    this.updates = [];
    this.completeCalled = false;
    this.errorCalled = false;
    this.lastErrorMessage = undefined;
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
