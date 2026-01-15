/**
 * React Hooks for WASM Module
 *
 * Provides React hooks for loading and using the WASM transpiler module.
 *
 * Following SOLID principles:
 * - Single Responsibility: React integration only
 * - Open/Closed: Can add more hooks without modifying existing ones
 * - Interface Segregation: Each hook has a specific purpose
 */

import { useState, useEffect, useCallback } from 'react';
import type { WASMModule, TranspilerInstance } from '@hupyy/cpptoc-wasm';
import { wasmLoader, type LoaderState } from './loader';

/**
 * Hook result for WASM module loading
 */
export interface UseWasmModuleResult {
  /** Current loading state */
  state: LoaderState;
  /** WASM module (null if not loaded) */
  module: WASMModule | null;
  /** Loading flag */
  isLoading: boolean;
  /** Ready flag */
  isReady: boolean;
  /** Error (null if no error) */
  error: Error | null;
  /** Manually trigger load */
  load: () => Promise<WASMModule>;
  /** Reset loader (for retry) */
  reset: () => void;
}

/**
 * Hook for loading WASM module with state tracking
 *
 * Usage:
 * ```tsx
 * function MyComponent() {
 *   const { isLoading, isReady, error, module } = useWasmModule();
 *
 *   if (isLoading) return <div>Loading transpiler...</div>;
 *   if (error) return <div>Error: {error.message}</div>;
 *   if (!isReady) return null;
 *
 *   // Use module...
 * }
 * ```
 *
 * @param autoLoad - Automatically start loading on mount (default: true)
 */
export function useWasmModule(autoLoad = true): UseWasmModuleResult {
  const [state, setState] = useState<LoaderState>(wasmLoader.getState());

  useEffect(() => {
    // Subscribe to loader state changes
    const unsubscribe = wasmLoader.subscribe(setState);
    return unsubscribe;
  }, []);

  useEffect(() => {
    // Auto-load on mount if requested
    if (autoLoad && state.status === 'idle') {
      wasmLoader.load().catch(err => {
        console.error('Auto-load failed:', err);
      });
    }
  }, [autoLoad, state.status]);

  const load = useCallback(async () => {
    return await wasmLoader.load();
  }, []);

  const reset = useCallback(() => {
    wasmLoader.reset();
  }, []);

  return {
    state,
    module: state.status === 'ready' ? state.module : null,
    isLoading: state.status === 'loading',
    isReady: state.status === 'ready',
    error: state.status === 'error' ? state.error : null,
    load,
    reset
  };
}

/**
 * Hook result for transpiler instance
 */
export interface UseTranspilerResult {
  /** Transpiler instance (null if not ready) */
  instance: TranspilerInstance | null;
  /** Loading flag */
  isLoading: boolean;
  /** Ready flag */
  isReady: boolean;
  /** Error (null if no error) */
  error: Error | null;
  /** Manually trigger load */
  load: () => Promise<void>;
}

/**
 * Hook for creating and managing a transpiler instance
 *
 * Automatically creates/destroys instance based on module availability.
 *
 * Usage:
 * ```tsx
 * function TranspilerComponent() {
 *   const { instance, isReady, error } = useTranspiler();
 *
 *   if (!isReady) return <div>Loading...</div>;
 *
 *   const handleTranspile = () => {
 *     const result = instance!.transpile(code, options);
 *     // Use result...
 *   };
 * }
 * ```
 */
export function useTranspiler(): UseTranspilerResult {
  const { module, isLoading, isReady, error, load: loadModule } = useWasmModule();
  const [instance, setInstance] = useState<TranspilerInstance | null>(null);

  useEffect(() => {
    // Create instance when module is ready
    if (module && !instance) {
      try {
        const newInstance = new module.Transpiler();
        setInstance(newInstance);
        console.log('✅ Transpiler instance created');
      } catch (err) {
        console.error('❌ Failed to create transpiler instance:', err);
      }
    }

    // Cleanup instance when module is unloaded or component unmounts
    return () => {
      if (instance) {
        instance.delete();
        setInstance(null);
        console.log('🧹 Transpiler instance destroyed');
      }
    };
  }, [module]); // Only depend on module, not instance (to avoid recreation loop)

  const load = useCallback(async () => {
    await loadModule();
  }, [loadModule]);

  return {
    instance,
    isLoading,
    isReady: isReady && instance !== null,
    error,
    load
  };
}

/**
 * Loading state component helper type
 */
export interface WasmLoadingStateProps {
  loading?: React.ReactNode;
  error?: (error: Error) => React.ReactNode;
  children: (module: WASMModule) => React.ReactNode;
}

/**
 * Hook for rendering based on WASM loading state
 *
 * Usage:
 * ```tsx
 * function MyComponent() {
 *   const renderState = useWasmLoadingState();
 *
 *   return renderState({
 *     loading: <div>Loading...</div>,
 *     error: (err) => <div>Error: {err.message}</div>,
 *     children: (module) => <TranspilerUI module={module} />
 *   });
 * }
 * ```
 */
export function useWasmLoadingState() {
  const { state, module } = useWasmModule();

  return useCallback((props: WasmLoadingStateProps): React.ReactNode => {
    if (state.status === 'loading') {
      return props.loading || <div>Loading WASM module...</div>;
    }

    if (state.status === 'error') {
      const errorRender = props.error || ((err: Error) => <div>Error: {err.message}</div>);
      return errorRender(state.error);
    }

    if (state.status === 'ready' && module) {
      return props.children(module);
    }

    return null;
  }, [state, module]);
}
