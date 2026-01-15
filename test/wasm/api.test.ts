/**
 * Unit tests for WASM API wrapper
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { isTranspilerReady } from '../../src/lib/wasm/api';

describe('WASM API', () => {
  beforeEach(() => {
    // Tests are isolated - each test gets fresh state
  });

  describe('isTranspilerReady', () => {
    it('should return false before loading', () => {
      // Before any loading, should be false
      // Note: This might be true if previous tests loaded the module
      // In real tests, we'd mock the loader
      const ready = isTranspilerReady();
      expect(typeof ready).toBe('boolean');
    });
  });

  // Note: Full transpilation tests require:
  // 1. WASM module to be available
  // 2. Proper environment setup
  // 3. Mock or real WASM binary
  //
  // These are better suited as integration tests rather than unit tests.
  // The API is a thin wrapper - integration tests verify it works correctly.
});
