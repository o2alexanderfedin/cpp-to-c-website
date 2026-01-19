/**
 * React hook for WASM transpiler with IDBFS support
 *
 * Manages WASM module lifecycle, IDBFS mounting, transpilation execution,
 * and output packaging for browser-based C++ to C transpilation.
 *
 * Following React best practices:
 * - Uses hooks for state management and side effects
 * - Properly cleans up resources on unmount
 * - Provides stable API through useCallback
 *
 * @module useWASMTranspiler
 */

import { useState, useEffect, useCallback, useRef } from 'react';
import type {
  WASMModule,
  WASMModuleFactory,
  TranspilerOptions,
  ConsoleLogEntry,
  TranspilationStatus,
} from './idbfs-types';
import { isExitStatus } from './idbfs-types';
import {
  mountIDBFS,
  unmountIDBFS,
  extractZipToIDBFS,
  buildTranspilerArgs,
  listOutputFiles,
  createOutputZip,
  detectSourceDirectory,
  clearIDBFS,
  OUTPUT_DIR,
} from './idbfs';

/**
 * Hook state interface
 */
export interface UseWASMTranspilerState {
  /**
   * WASM module instance (null until loaded)
   */
  module: WASMModule | null;

  /**
   * Loading state
   */
  isLoading: boolean;

  /**
   * Whether IDBFS is mounted
   */
  isMounted: boolean;

  /**
   * Error message (null if no error)
   */
  error: string | null;

  /**
   * Current transpilation status
   */
  status: TranspilationStatus;

  /**
   * Console log entries
   */
  logs: ConsoleLogEntry[];

  /**
   * Transpilation exit code (null if not run yet)
   */
  exitCode: number | null;

  /**
   * List of generated output file paths
   */
  outputFiles: string[];
}

/**
 * Hook return type
 */
export interface UseWASMTranspilerReturn extends UseWASMTranspilerState {
  /**
   * Extract ZIP file to IDBFS
   */
  extractZip: (file: File) => Promise<string[]>;

  /**
   * Run transpilation with given options
   */
  transpile: (options: TranspilerOptions) => Promise<number>;

  /**
   * Download output files as ZIP
   */
  downloadOutput: (fileName: string) => Promise<void>;

  /**
   * Clear console logs
   */
  clearLogs: () => void;

  /**
   * Clear IDBFS and reset state
   */
  reset: () => Promise<void>;

  /**
   * Add custom log entry
   */
  addLog: (message: string, level?: ConsoleLogEntry['level']) => void;
}

/**
 * Hook for WASM transpiler with IDBFS support
 *
 * Automatically loads WASM module and mounts IDBFS on component mount.
 * Cleans up resources on component unmount.
 *
 * @returns Transpiler state and operations
 *
 * @example
 * ```tsx
 * function PlaygroundComponent() {
 *   const {
 *     isLoading,
 *     isMounted,
 *     extractZip,
 *     transpile,
 *     downloadOutput,
 *     logs
 *   } = useWASMTranspiler();
 *
 *   if (isLoading) return <div>Loading WASM...</div>;
 *   if (!isMounted) return <div>Mounting filesystem...</div>;
 *
 *   return (
 *     <div>
 *       <input type="file" onChange={e => extractZip(e.target.files[0])} />
 *       <button onClick={() => transpile({ cppStandard: 'c++17' })}>
 *         Transpile
 *       </button>
 *       <Console logs={logs} />
 *     </div>
 *   );
 * }
 * ```
 */
export function useWASMTranspiler(): UseWASMTranspilerReturn {
  const [state, setState] = useState<UseWASMTranspilerState>({
    module: null,
    isLoading: true,
    isMounted: false,
    error: null,
    status: 'idle',
    logs: [],
    exitCode: null,
    outputFiles: [],
  });

  // Use ref to track if component is mounted (for cleanup)
  const isMountedRef = useRef(true);

  // Stable log function using useCallback
  const addLog = useCallback((message: string, level: ConsoleLogEntry['level'] = 'info') => {
    const entry: ConsoleLogEntry = {
      timestamp: new Date(),
      level,
      message,
    };

    setState(prev => ({
      ...prev,
      logs: [...prev.logs, entry],
    }));
  }, []);

  // Load WASM module and mount IDBFS
  useEffect(() => {
    let moduleInstance: WASMModule | null = null;

    async function initializeWASM() {
      try {
        addLog('Loading WASM transpiler module...', 'info');

        // Dynamic import of WASM module factory
        // The WASM module is a file:../ dependency pointing to ../wasm/glue
        // Import the full cpptoc.js which exports the factory function
        const wasmModulePath = '../../../wasm/glue/dist/full/cpptoc.js';
        const createCppToC = (await import(/* @vite-ignore */ wasmModulePath)).default as WASMModuleFactory;

        // Create module with console handlers
        moduleInstance = await createCppToC({
          noInitialRun: true,
          print: (text: string) => addLog(text, 'success'),
          printErr: (text: string) => addLog(text, 'error'),
          onRuntimeInitialized: function() {
            addLog('WASM runtime initialized', 'success');
          },
        });

        if (!isMountedRef.current) {
          return; // Component unmounted during load
        }

        if (!moduleInstance) {
          throw new Error('Failed to create WASM module instance');
        }

        addLog('WASM module loaded successfully', 'success');
        addLog(`IDBFS available: ${typeof moduleInstance.FS.filesystems.IDBFS !== 'undefined'}`, 'info');

        // Mount IDBFS
        setState(prev => ({ ...prev, status: 'mounting' }));
        addLog('Mounting IDBFS...', 'info');
        await mountIDBFS(moduleInstance);

        if (!isMountedRef.current) {
          return; // Component unmounted during mount
        }

        addLog('IDBFS mounted successfully', 'success');

        setState(prev => ({
          ...prev,
          module: moduleInstance,
          isLoading: false,
          isMounted: true,
          status: 'idle',
        }));
      } catch (error) {
        const errorMessage = error instanceof Error ? error.message : String(error);
        addLog(`Failed to initialize: ${errorMessage}`, 'error');

        if (isMountedRef.current) {
          setState(prev => ({
            ...prev,
            isLoading: false,
            error: errorMessage,
            status: 'error',
          }));
        }
      }
    }

    initializeWASM();

    // Cleanup on unmount
    return () => {
      isMountedRef.current = false;
      if (moduleInstance) {
        try {
          unmountIDBFS(moduleInstance);
        } catch (error) {
          console.warn('Error unmounting IDBFS:', error);
        }
      }
    };
  }, []); // Empty deps - run once on mount

  /**
   * Extract ZIP file to IDBFS
   */
  const extractZip = useCallback(async (file: File): Promise<string[]> => {
    if (!state.module) {
      throw new Error('WASM module not loaded');
    }

    if (!state.isMounted) {
      throw new Error('IDBFS not mounted');
    }

    try {
      setState(prev => ({ ...prev, status: 'extracting' }));
      addLog(`Extracting ${file.name} (${(file.size / 1024).toFixed(2)} KB)...`, 'info');

      const extractedFiles = await extractZipToIDBFS(
        file,
        state.module,
        (current, total, fileName) => {
          if (current % 10 === 0 || current === total) {
            addLog(`Extracted ${current}/${total} files...`, 'info');
          }
        }
      );

      addLog(`Successfully extracted ${extractedFiles.length} files`, 'success');
      setState(prev => ({ ...prev, status: 'idle' }));

      return extractedFiles;
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);
      addLog(`Extraction failed: ${errorMessage}`, 'error');
      setState(prev => ({ ...prev, status: 'error', error: errorMessage }));
      throw error;
    }
  }, [state.module, state.isMounted, addLog]);

  /**
   * Run transpilation
   */
  const transpile = useCallback(async (options: TranspilerOptions): Promise<number> => {
    if (!state.module) {
      throw new Error('WASM module not loaded');
    }

    if (!state.isMounted) {
      throw new Error('IDBFS not mounted');
    }

    try {
      setState(prev => ({ ...prev, status: 'transpiling', exitCode: null, outputFiles: [] }));
      addLog('Starting transpilation...', 'info');

      // Detect source directory
      const sourceDir = detectSourceDirectory(state.module);
      addLog(`Source directory: ${sourceDir}`, 'info');

      // Create output directory
      try {
        state.module.FS.mkdir(OUTPUT_DIR);
      } catch (error: unknown) {
        // Ignore if already exists
        if (error instanceof Error && 'code' in error && error.code !== 'EEXIST') {
          throw error;
        }
      }

      // Build arguments
      const args = buildTranspilerArgs(options, sourceDir, OUTPUT_DIR);
      addLog(`Command: cpptoc ${args.join(' ')}`, 'info');

      // Run transpiler
      let exitCode: number;
      try {
        exitCode = state.module.callMain(args);
      } catch (error: unknown) {
        if (isExitStatus(error)) {
          exitCode = error.status;
        } else {
          throw error;
        }
      }

      addLog(`Transpilation completed with exit code: ${exitCode}`, exitCode === 0 ? 'success' : 'error');

      // List output files
      const outputFiles = listOutputFiles(state.module, OUTPUT_DIR);
      if (outputFiles.length > 0) {
        addLog(`Generated ${outputFiles.length} output files:`, 'success');
        outputFiles.forEach(f => {
          const fileName = f.substring(f.lastIndexOf('/') + 1);
          addLog(`  - ${fileName}`, 'info');
        });
      }

      setState(prev => ({
        ...prev,
        status: exitCode === 0 ? 'complete' : 'error',
        exitCode,
        outputFiles,
      }));

      return exitCode;
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);
      addLog(`Transpilation error: ${errorMessage}`, 'error');
      setState(prev => ({ ...prev, status: 'error', error: errorMessage, exitCode: -1 }));
      throw error;
    }
  }, [state.module, state.isMounted, addLog]);

  /**
   * Download output files as ZIP
   */
  const downloadOutput = useCallback(async (fileName: string): Promise<void> => {
    if (!state.module) {
      throw new Error('WASM module not loaded');
    }

    if (state.outputFiles.length === 0) {
      throw new Error('No output files to download');
    }

    try {
      setState(prev => ({ ...prev, status: 'packaging' }));
      addLog('Creating output ZIP...', 'info');

      const blob = await createOutputZip(state.outputFiles, state.module, OUTPUT_DIR);

      // Trigger download
      const url = URL.createObjectURL(blob);
      const a = document.createElement('a');
      a.href = url;
      a.download = fileName;
      a.click();
      URL.revokeObjectURL(url);

      addLog('Download started', 'success');
      setState(prev => ({ ...prev, status: 'complete' }));
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);
      addLog(`Download failed: ${errorMessage}`, 'error');
      setState(prev => ({ ...prev, status: 'error', error: errorMessage }));
      throw error;
    }
  }, [state.module, state.outputFiles, addLog]);

  /**
   * Clear console logs
   */
  const clearLogs = useCallback(() => {
    setState(prev => ({ ...prev, logs: [] }));
  }, []);

  /**
   * Reset state and clear IDBFS
   */
  const reset = useCallback(async (): Promise<void> => {
    if (!state.module) {
      return;
    }

    try {
      addLog('Clearing IDBFS...', 'info');
      await clearIDBFS(state.module);
      addLog('IDBFS cleared', 'success');

      setState(prev => ({
        ...prev,
        status: 'idle',
        exitCode: null,
        outputFiles: [],
        error: null,
      }));
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);
      addLog(`Failed to clear IDBFS: ${errorMessage}`, 'error');
      throw error;
    }
  }, [state.module, addLog]);

  return {
    ...state,
    extractZip,
    transpile,
    downloadOutput,
    clearLogs,
    reset,
    addLog,
  };
}
