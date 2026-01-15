/**
 * Unit tests for WASM loader
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { wasmLoader } from '../../src/lib/wasm/loader';

describe('WasmLoader', () => {
  beforeEach(() => {
    // Reset loader before each test
    wasmLoader.reset();
  });

  it('should start in idle state', () => {
    const state = wasmLoader.getState();
    expect(state.status).toBe('idle');
  });

  it('should notify listeners when state changes', async () => {
    const listener = vi.fn();
    const unsubscribe = wasmLoader.subscribe(listener);

    // Listener should be called immediately with current state
    expect(listener).toHaveBeenCalledTimes(1);
    expect(listener).toHaveBeenCalledWith({ status: 'idle' });

    unsubscribe();
  });

  it('should support multiple listeners', () => {
    const listener1 = vi.fn();
    const listener2 = vi.fn();

    wasmLoader.subscribe(listener1);
    wasmLoader.subscribe(listener2);

    // Both should be called immediately
    expect(listener1).toHaveBeenCalledTimes(1);
    expect(listener2).toHaveBeenCalledTimes(1);
  });

  it('should unsubscribe listeners', () => {
    const listener = vi.fn();
    const unsubscribe = wasmLoader.subscribe(listener);

    // Clear call count
    listener.mockClear();

    // Unsubscribe
    unsubscribe();

    // Reset state (triggers notification)
    wasmLoader.reset();

    // Listener should not be called after unsubscribe
    expect(listener).not.toHaveBeenCalled();
  });

  it('should reset to idle state', () => {
    wasmLoader.reset();
    const state = wasmLoader.getState();
    expect(state.status).toBe('idle');
  });

  // Note: Actual loading tests require mocking the dynamic import
  // which is complex with Vitest. These would be integration tests.
});
