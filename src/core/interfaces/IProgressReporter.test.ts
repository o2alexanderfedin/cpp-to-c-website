/**
 * IProgressReporter Interface Contract Tests
 * TDD Phase: RED - Write failing tests first
 */

import { describe, it, expect, beforeEach } from 'vitest';
import type { IProgressReporter } from './IProgressReporter';
import { MockProgressReporter } from '../../adapters/MockProgressReporter';

describe('IProgressReporter', () => {
  describe('contract', () => {
    let reporter: IProgressReporter;

    beforeEach(() => {
      reporter = new MockProgressReporter();
    });

    it('should have start method', () => {
      expect(typeof reporter.start).toBe('function');
    });

    it('should have update method', () => {
      expect(typeof reporter.update).toBe('function');
    });

    it('should have complete method', () => {
      expect(typeof reporter.complete).toBe('function');
    });

    it('should have error method', () => {
      expect(typeof reporter.error).toBe('function');
    });

    it('should have getState method', () => {
      expect(typeof reporter.getState).toBe('function');
    });
  });

  describe('behavior', () => {
    let reporter: IProgressReporter;

    beforeEach(() => {
      reporter = new MockProgressReporter();
    });

    it('should start progress tracking', () => {
      reporter.start(100);

      const state = reporter.getState();
      expect(state.total).toBe(100);
      expect(state.current).toBe(0);
      expect(state.percentage).toBe(0);
    });

    it('should update progress', () => {
      reporter.start(100);
      reporter.update(50);

      const state = reporter.getState();
      expect(state.current).toBe(50);
      expect(state.percentage).toBe(50);
    });

    it('should update progress with message', () => {
      reporter.start(100);
      reporter.update(25, 'Processing file 25/100');

      const state = reporter.getState();
      expect(state.current).toBe(25);
      expect(state.message).toBe('Processing file 25/100');
    });

    it('should complete progress', () => {
      reporter.start(100);
      reporter.update(50);
      reporter.complete();

      const state = reporter.getState();
      expect(state.current).toBe(state.total);
      expect(state.percentage).toBe(100);
    });

    it('should report error', () => {
      reporter.start(100);
      reporter.update(50);
      reporter.error('An error occurred');

      const state = reporter.getState();
      expect(state.message).toBe('An error occurred');
    });

    it('should calculate percentage correctly', () => {
      reporter.start(200);
      reporter.update(50);

      const state = reporter.getState();
      expect(state.percentage).toBe(25);
    });

    it('should handle zero total', () => {
      reporter.start(0);

      const state = reporter.getState();
      expect(state.total).toBe(0);
      expect(state.percentage).toBe(0);
    });

    it('should clamp percentage to 100', () => {
      reporter.start(100);
      reporter.update(150); // More than total

      const state = reporter.getState();
      expect(state.percentage).toBeLessThanOrEqual(100);
    });

    it('should track multiple updates', () => {
      reporter.start(100);

      reporter.update(25, 'Step 1');
      let state = reporter.getState();
      expect(state.current).toBe(25);

      reporter.update(50, 'Step 2');
      state = reporter.getState();
      expect(state.current).toBe(50);

      reporter.update(75, 'Step 3');
      state = reporter.getState();
      expect(state.current).toBe(75);
    });

    it('should reset on new start', () => {
      reporter.start(100);
      reporter.update(50);
      reporter.start(200);

      const state = reporter.getState();
      expect(state.total).toBe(200);
      expect(state.current).toBe(0);
      expect(state.percentage).toBe(0);
    });
  });
});
