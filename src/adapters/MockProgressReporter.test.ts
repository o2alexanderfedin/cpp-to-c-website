/**
 * MockProgressReporter Implementation Tests
 * Tests for the mock progress reporter beyond interface contracts
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { MockProgressReporter } from './MockProgressReporter';

describe('MockProgressReporter', () => {
  let reporter: MockProgressReporter;

  beforeEach(() => {
    reporter = new MockProgressReporter();
  });

  describe('state management', () => {
    it('should initialize with zero state', () => {
      const state = reporter.getState();

      expect(state.total).toBe(0);
      expect(state.current).toBe(0);
      expect(state.percentage).toBe(0);
      expect(state.message).toBeUndefined();
    });

    it('should return immutable state copy', () => {
      reporter.start(100);

      const state1 = reporter.getState();
      const state2 = reporter.getState();

      expect(state1).not.toBe(state2); // Different objects
      expect(state1).toEqual(state2); // Same values
    });

    it('should not allow external state modification', () => {
      reporter.start(100);

      const state = reporter.getState();
      state.current = 999; // Try to modify

      const actualState = reporter.getState();
      expect(actualState.current).toBe(0); // Should still be 0
    });
  });

  describe('percentage calculation', () => {
    it('should calculate 0% at start', () => {
      reporter.start(100);

      const state = reporter.getState();
      expect(state.percentage).toBe(0);
    });

    it('should calculate 50% at midpoint', () => {
      reporter.start(100);
      reporter.update(50);

      const state = reporter.getState();
      expect(state.percentage).toBe(50);
    });

    it('should calculate 100% at completion', () => {
      reporter.start(100);
      reporter.complete();

      const state = reporter.getState();
      expect(state.percentage).toBe(100);
    });

    it('should round percentage to nearest integer', () => {
      reporter.start(3);
      reporter.update(1);

      const state = reporter.getState();
      expect(state.percentage).toBe(33); // 33.33... rounded to 33
    });

    it('should handle fractional percentages', () => {
      reporter.start(7);
      reporter.update(3);

      const state = reporter.getState();
      expect(state.percentage).toBe(43); // 42.857... rounded to 43
    });

    it('should clamp percentage below 0', () => {
      reporter.start(100);
      reporter.update(-10);

      const state = reporter.getState();
      expect(state.percentage).toBe(0);
    });

    it('should clamp percentage above 100', () => {
      reporter.start(100);
      reporter.update(150);

      const state = reporter.getState();
      expect(state.percentage).toBe(100);
    });
  });

  describe('message handling', () => {
    it('should store update message', () => {
      reporter.start(100);
      reporter.update(50, 'Halfway there!');

      const state = reporter.getState();
      expect(state.message).toBe('Halfway there!');
    });

    it('should clear message on complete', () => {
      reporter.start(100);
      reporter.update(50, 'Processing...');
      reporter.complete();

      const state = reporter.getState();
      expect(state.message).toBeUndefined();
    });

    it('should update message on error', () => {
      reporter.start(100);
      reporter.update(50, 'Processing...');
      reporter.error('Something went wrong');

      const state = reporter.getState();
      expect(state.message).toBe('Something went wrong');
    });

    it('should allow message to be omitted', () => {
      reporter.start(100);
      reporter.update(50);

      const state = reporter.getState();
      expect(state.message).toBeUndefined();
    });
  });

  describe('lifecycle', () => {
    it('should reset on new start', () => {
      reporter.start(100);
      reporter.update(50, 'First run');

      reporter.start(200);

      const state = reporter.getState();
      expect(state.total).toBe(200);
      expect(state.current).toBe(0);
      expect(state.percentage).toBe(0);
      expect(state.message).toBeUndefined();
    });

    it('should handle multiple complete calls', () => {
      reporter.start(100);
      reporter.update(50);
      reporter.complete();
      reporter.complete();

      const state = reporter.getState();
      expect(state.percentage).toBe(100);
      expect(state.current).toBe(100);
    });

    it('should handle updates after complete', () => {
      reporter.start(100);
      reporter.complete();
      reporter.update(50, 'After complete');

      const state = reporter.getState();
      expect(state.current).toBe(50);
      expect(state.message).toBe('After complete');
    });
  });

  describe('edge cases', () => {
    it('should handle total of 0', () => {
      reporter.start(0);

      const state = reporter.getState();
      expect(state.total).toBe(0);
      expect(state.percentage).toBe(0);
    });

    it('should handle total of 1', () => {
      reporter.start(1);
      reporter.update(1);

      const state = reporter.getState();
      expect(state.percentage).toBe(100);
    });

    it('should handle large totals', () => {
      reporter.start(1000000);
      reporter.update(500000);

      const state = reporter.getState();
      expect(state.percentage).toBe(50);
    });

    it('should handle rapid updates', () => {
      reporter.start(100);

      for (let i = 0; i <= 100; i++) {
        reporter.update(i);
      }

      const state = reporter.getState();
      expect(state.current).toBe(100);
      expect(state.percentage).toBe(100);
    });
  });

  describe('test helpers', () => {
    it('should reset state', () => {
      reporter.start(100);
      reporter.update(50, 'In progress');

      reporter.reset();

      const state = reporter.getState();
      expect(state.total).toBe(0);
      expect(state.current).toBe(0);
      expect(state.percentage).toBe(0);
      expect(state.message).toBeUndefined();
    });

    it('should enable history tracking', () => {
      reporter.enableHistory();

      expect(reporter.getHistory()).toEqual([]);
    });

    it('should return immutable history copy', () => {
      reporter.enableHistory();

      const history1 = reporter.getHistory();
      const history2 = reporter.getHistory();

      expect(history1).not.toBe(history2);
      expect(history1).toEqual(history2);
    });
  });

  describe('practical scenarios', () => {
    it('should track file processing progress', () => {
      const totalFiles = 10;
      reporter.start(totalFiles);

      for (let i = 1; i <= totalFiles; i++) {
        reporter.update(i, `Processing file ${i}/${totalFiles}`);
        const state = reporter.getState();
        expect(state.current).toBe(i);
        expect(state.percentage).toBe((i / totalFiles) * 100);
      }

      reporter.complete();
      const finalState = reporter.getState();
      expect(finalState.percentage).toBe(100);
    });

    it('should handle partial completion with error', () => {
      reporter.start(100);
      reporter.update(50, 'Processing...');
      reporter.error('Failed at 50%');

      const state = reporter.getState();
      expect(state.current).toBe(50);
      expect(state.percentage).toBe(50);
      expect(state.message).toBe('Failed at 50%');
    });
  });
});
