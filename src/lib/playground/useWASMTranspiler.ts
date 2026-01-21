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

  /** Download result as files */
  downloadResult: (result: TranspileResult, baseName: string) => void;
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

        // Use root cpptoc.js which has IDBFS support, not full/cpptoc.js
        const wasmModulePath = '../../../wasm/glue/dist/cpptoc.js';
        const createCppToC = (await import(/* @vite-ignore */ wasmModulePath)).default as WASMModuleFactory;

        const moduleInstance = await createCppToC({
          noInitialRun: true,
          print: (text: string) => addLog(text, 'success'),
          printErr: (text: string) => addLog(text, 'error'),
          onRuntimeInitialized: function() {
            addLog('WASM runtime initialized', 'success');
            addLog('IDBFS available: ' + (typeof this.FS?.filesystems?.IDBFS !== 'undefined'), 'info');
          },
        });

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

  // Download result as files
  const downloadResult = useCallback((result: TranspileResult, baseName: string) => {
    // Download C file
    if (result.c) {
      const cBlob = new Blob([result.c], { type: 'text/plain' });
      const cUrl = URL.createObjectURL(cBlob);
      const cLink = document.createElement('a');
      cLink.href = cUrl;
      cLink.download = `${baseName}.c`;
      cLink.click();
      URL.revokeObjectURL(cUrl);
    }

    // Download H file
    if (result.h) {
      const hBlob = new Blob([result.h], { type: 'text/plain' });
      const hUrl = URL.createObjectURL(hBlob);
      const hLink = document.createElement('a');
      hLink.href = hUrl;
      hLink.download = `${baseName}.h`;
      hLink.click();
      URL.revokeObjectURL(hUrl);
    }

    // Download ACSL file if present
    if (result.acsl) {
      const acslBlob = new Blob([result.acsl], { type: 'text/plain' });
      const acslUrl = URL.createObjectURL(acslBlob);
      const acslLink = document.createElement('a');
      acslLink.href = acslUrl;
      acslLink.download = `${baseName}.acsl`;
      acslLink.click();
      URL.revokeObjectURL(acslUrl);
    }

    addLog(`Downloaded transpilation results`, 'success');
  }, [addLog]);

  return {
    ...state,
    transpileZip,
    clearLogs,
    downloadResult,
  };
}
