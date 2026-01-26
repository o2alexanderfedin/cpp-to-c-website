/**
 * React hook for WASM transpiler with CLI mode
 *
 * Manages WASM module lifecycle, ZIP extraction, and transpilation execution
 * using the transpiler's CLI interface via Module.callMain().
 *
 * @module useWASMTranspiler
 */

import { useState, useEffect, useCallback, useRef } from 'react';
import {
  transpileFromZip,
  type WASMModule,
  type WASMModuleFactory,
  type TranspileResult,
  type TranspileOptions,
} from './wasmTranspiler';

export type TranspilationStatus =
  | 'idle'
  | 'loading'
  | 'ready'
  | 'mounting'
  | 'extracting'
  | 'writing'
  | 'transpiling'
  | 'success'
  | 'error';

export interface ConsoleLogEntry {
  message: string;
  type: 'info' | 'error' | 'success';
  timestamp: Date;
}

export interface UseWASMTranspilerState {
  /** WASM module instance (null until loaded) */
  module: WASMModule | null;

  /** Loading state */
  isLoading: boolean;

  /** Error message (null if no error) */
  error: string | null;

  /** Current transpilation status */
  status: TranspilationStatus;

  /** Console log entries */
  logs: ConsoleLogEntry[];

  /** Last transpilation result */
  result: TranspileResult | null;
}

export interface UseWASMTranspilerReturn extends UseWASMTranspilerState {
  /** Transpile from ZIP file */
  transpileZip: (file: File, options?: TranspileOptions) => Promise<TranspileResult>;

  /** Clear console logs */
  clearLogs: () => void;

  /** Download result as ZIP file */
  downloadResult: (result: TranspileResult, baseName: string) => Promise<void>;
}

/**
 * Hook for managing WASM transpiler
 */
export function useWASMTranspiler(): UseWASMTranspilerReturn {
  const [state, setState] = useState<UseWASMTranspilerState>({
    module: null,
    isLoading: true,
    error: null,
    status: 'loading',
    logs: [],
    result: null,
  });

  const moduleRef = useRef<WASMModule | null>(null);

  // Add log entry
  const addLog = useCallback((message: string, type: ConsoleLogEntry['type']) => {
    setState(prev => ({
      ...prev,
      logs: [...prev.logs, { message, type, timestamp: new Date() }],
    }));
  }, []);

  // Initialize WASM module
  useEffect(() => {
    let cancelled = false;

    async function initializeWASM() {
      try {
        setState(prev => ({ ...prev, status: 'loading' }));
        addLog('Loading WASM transpiler module...', 'info');

        // Load WASM from npm package (configured in website/package.json as @hupyy/cpptoc-wasm)
        // The package is linked to ../wasm/glue which contains the built WASM module
        // In dev: Uses the linked package from wasm/glue/dist
        // In production: Will be bundled or loaded from public/wasm
        const { default: createCppToC } = await import('@hupyy/cpptoc-wasm');

        // CRITICAL: The module instance with FS is 'this' in onRuntimeInitialized, NOT the return value
        // Declare variable first to avoid temporal dead zone
        let moduleInstance: WASMModule | null = null;

        const promiseResult = await createCppToC({
          noInitialRun: true,
          print: (text: string) => addLog(text, 'success'),
          printErr: (text: string) => addLog(text, 'error'),
          locateFile: (path: string) => {
            // WASM files are in /wasm/ directory (base path is handled by Astro)
            if (path.endsWith('.wasm')) {
              return `/cpp-to-c-website/wasm/${path}`;
            }
            return path;
          },
          onRuntimeInitialized: function() {
            // 'this' is the REAL module instance with FS - capture it
            moduleInstance = this as unknown as WASMModule;
            addLog('WASM runtime initialized', 'success');
            addLog('FS available: ' + (typeof this.FS !== 'undefined'), 'info');
            addLog('IDBFS available: ' + (typeof this.FS?.filesystems?.IDBFS !== 'undefined'), 'info');
          },
        });

        // Poll until moduleInstance is set and has FS
        const maxWaitMs = 10000;
        const pollIntervalMs = 50;
        let waited = 0;

        while ((!moduleInstance || !moduleInstance.FS || typeof moduleInstance.FS.mkdir !== 'function') && waited < maxWaitMs) {
          await new Promise(resolve => setTimeout(resolve, pollIntervalMs));
          waited += pollIntervalMs;
        }

        if (!moduleInstance || !moduleInstance.FS || typeof moduleInstance.FS.mkdir !== 'function') {
          throw new Error(`WASM FS not available after ${waited}ms`);
        }

        addLog('WASM module ready with FS', 'success');

        if (cancelled) return;

        moduleRef.current = moduleInstance;
        setState(prev => ({
          ...prev,
          module: moduleInstance,
          isLoading: false,
          status: 'ready',
        }));

        addLog('WASM module loaded successfully', 'success');

      } catch (error) {
        if (cancelled) return;

        const errorMessage = error instanceof Error ? error.message : String(error);
        setState(prev => ({
          ...prev,
          isLoading: false,
          status: 'error',
          error: `Failed to Load WASM Module: ${errorMessage}`,
        }));
        addLog(`Failed to load WASM: ${errorMessage}`, 'error');
      }
    }

    initializeWASM();

    return () => {
      cancelled = true;
    };
  }, [addLog]);

  // Transpile from ZIP file
  const transpileZip = useCallback(async (
    file: File,
    options: TranspileOptions = {}
  ): Promise<TranspileResult> => {
    if (!moduleRef.current) {
      throw new Error('WASM module not loaded');
    }

    try {
      setState(prev => ({ ...prev, status: 'extracting', error: null }));
      addLog(`Extracting ZIP: ${file.name}`, 'info');

      const result = await transpileFromZip(moduleRef.current, file, (stage, progress) => {
        if (stage === 'extracting') {
          setState(prev => ({ ...prev, status: 'extracting' }));
          addLog(`Extracting files... ${Math.round(progress)}%`, 'info');
        } else if (stage === 'mounting') {
          setState(prev => ({ ...prev, status: 'mounting' }));
          addLog('Mounting IDBFS filesystem...', 'info');
        } else if (stage === 'writing') {
          setState(prev => ({ ...prev, status: 'writing' }));
          addLog('Writing files to virtual filesystem...', 'info');
        } else if (stage === 'transpiling') {
          setState(prev => ({ ...prev, status: 'transpiling' }));
          addLog('Transpiling...', 'info');
        } else if (stage === 'complete') {
          addLog('Processing complete', 'info');
        }
      }, options);

      if (result.success) {
        setState(prev => ({ ...prev, status: 'success', result }));
        addLog('Transpilation completed successfully', 'success');
        addLog(`Generated ${result.c.length} bytes of C code`, 'info');
        addLog(`Generated ${result.h.length} bytes of header code`, 'info');
        if (result.acsl) {
          addLog(`Generated ${result.acsl.length} bytes of ACSL code`, 'info');
        }
      } else {
        setState(prev => ({ ...prev, status: 'error', result }));
        addLog('Transpilation failed', 'error');
        addLog(`Exit code: ${result.exitCode}`, 'error');
        result.diagnostics.forEach(diag => {
          addLog(`${diag.severity}: ${diag.message} (line ${diag.line})`, 'error');
        });
      }

      return result;

    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);
      setState(prev => ({ ...prev, status: 'error', error: errorMessage }));
      addLog(`Transpilation error: ${errorMessage}`, 'error');
      throw error;
    }
  }, [addLog]);

  // Clear logs
  const clearLogs = useCallback(() => {
    setState(prev => ({ ...prev, logs: [] }));
  }, []);

  // Download result as ZIP file
  const downloadResult = useCallback(async (result: TranspileResult, baseName: string) => {
    try {
      // Dynamically import JSZip
      const JSZip = (await import('jszip')).default;
      const zip = new JSZip();

      // Add files to ZIP
      if (result.c) {
        zip.file(`${baseName}.c`, result.c);
      }
      if (result.h) {
        zip.file(`${baseName}.h`, result.h);
      }
      if (result.acsl) {
        zip.file(`${baseName}.acsl`, result.acsl);
      }

      // Generate ZIP file
      const zipBlob = await zip.generateAsync({ type: 'blob' });

      // Download ZIP
      const zipUrl = URL.createObjectURL(zipBlob);
      const zipLink = document.createElement('a');
      zipLink.href = zipUrl;
      zipLink.download = `${baseName}-transpiled.zip`;
      zipLink.click();
      URL.revokeObjectURL(zipUrl);

      addLog(`Downloaded transpilation results as ZIP`, 'success');
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);
      addLog(`Failed to create ZIP: ${errorMessage}`, 'error');
      throw error;
    }
  }, [addLog]);

  return {
    ...state,
    transpileZip,
    clearLogs,
    downloadResult,
  };
}
