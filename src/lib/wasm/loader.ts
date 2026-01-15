/**
 * WASM Loader - Singleton loader for @hupyy/cpptoc-wasm module
 *
 * Provides centralized WASM module loading with:
 * - Lazy loading (load on first use)
 * - Singleton pattern (one instance across app)
 * - Loading state management
 * - Error handling and retry support
 *
 * Following SOLID principles:
 * - Single Responsibility: WASM module loading only
 * - Open/Closed: Can extend with caching strategies
 * - Dependency Inversion: Depends on WASM module interface
 */

import type {
  WASMModule,
  CreateCppToCModule,
  CreateModuleOptions
} from '@hupyy/cpptoc-wasm';

/**
 * WASM loader state
 */
export type LoaderState =
  | { status: 'idle' }
  | { status: 'loading' }
  | { status: 'ready'; module: WASMModule }
  | { status: 'error'; error: Error };

/**
 * Loader event listener
 */
export type LoaderListener = (state: LoaderState) => void;

/**
 * WASM Loader singleton
 */
class WasmLoader {
  private state: LoaderState = { status: 'idle' };
  private listeners = new Set<LoaderListener>();
  private loadPromise: Promise<WASMModule> | null = null;

  /**
   * Get current state
   */
  getState(): LoaderState {
    return this.state;
  }

  /**
   * Subscribe to state changes
   */
  subscribe(listener: LoaderListener): () => void {
    this.listeners.add(listener);
    // Immediately call with current state
    listener(this.state);

    // Return unsubscribe function
    return () => {
      this.listeners.delete(listener);
    };
  }

  /**
   * Notify all listeners of state change
   */
  private notify(): void {
    this.listeners.forEach(listener => listener(this.state));
  }

  /**
   * Load WASM module
   *
   * Returns cached module if already loaded.
   * Returns in-progress promise if already loading.
   */
  async load(): Promise<WASMModule> {
    // Already loaded
    if (this.state.status === 'ready') {
      return this.state.module;
    }

    // Already loading
    if (this.loadPromise) {
      return this.loadPromise;
    }

    // Start loading
    this.state = { status: 'loading' };
    this.notify();

    this.loadPromise = (async () => {
      try {
        console.log('🔄 Loading @hupyy/cpptoc-wasm module...');

        // Dynamically import WASM module factory
        // The package exports the full build by default
        const wasmModule = await import('@hupyy/cpptoc-wasm');
        const createModule = (wasmModule as any).default as CreateCppToCModule;

        // Create WASM module with Emscripten options
        const options: CreateModuleOptions = {
          // Locate WASM file (bundler handles this automatically in most cases)
          locateFile: (path: string, prefix: string) => {
            console.log(`📦 Locating WASM file: ${path} (prefix: ${prefix})`);
            // Return default path (Vite/bundler will resolve)
            return prefix + path;
          },
          // Called when WASM runtime is ready
          onRuntimeInitialized: () => {
            console.log('🚀 WASM runtime initialized');
          }
        };

        const module = await createModule(options);

        // Create a test instance to verify the module works
        const testInstance = new module.Transpiler();
        const version = testInstance.getVersion();
        testInstance.delete();

        console.log(`✅ @hupyy/cpptoc-wasm module loaded successfully`);
        console.log(`📦 Transpiler version: ${version}`);

        // Update state
        this.state = { status: 'ready', module };
        this.notify();

        return module;
      } catch (error) {
        console.error('❌ Failed to load @hupyy/cpptoc-wasm module:', error);

        const err = error instanceof Error ? error : new Error(String(error));

        // Update state
        this.state = { status: 'error', error: err };
        this.notify();

        // Clear load promise to allow retry
        this.loadPromise = null;

        throw err;
      }
    })();

    return this.loadPromise;
  }

  /**
   * Reset loader state (for testing or retry)
   */
  reset(): void {
    this.state = { status: 'idle' };
    this.loadPromise = null;
    this.notify();
  }
}

/**
 * Singleton instance
 */
export const wasmLoader = new WasmLoader();

/**
 * Convenience function to load WASM module
 */
export const loadWasmModule = () => wasmLoader.load();

/**
 * Convenience function to get current state
 */
export const getLoaderState = () => wasmLoader.getState();
