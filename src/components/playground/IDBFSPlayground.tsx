/**
 * IDBFS Playground Component
 *
 * Complete browser-based transpilation workflow using IDBFS (IndexedDB Filesystem).
 * Integrates ZIP upload, transpiler options, execution, and output download.
 *
 * This component provides an alternative to the File System Access API-based
 * wizard for browsers that don't support it (Tier 2/3) or as a simpler
 * ZIP-based workflow (Tier 1).
 *
 * Workflow:
 * 1. Upload ZIP containing C++ project
 * 2. Configure transpiler options
 * 3. Run transpilation in WASM
 * 4. Download transpiled C code as ZIP
 *
 * @module IDBFSPlayground
 */

import React, { useState, useCallback } from 'react';
import { ZipUpload } from './ZipUpload';
import { TranspilerOptionsComponent } from './TranspilerOptions';
import { ConsoleOutput } from './ConsoleOutput';
import { useWASMTranspiler } from '../../lib/playground/useWASMTranspiler';
import type { TranspileResult } from '../../lib/playground/wasmTranspiler';

/**
 * IDBFS Playground Component
 */
export const IDBFSPlayground: React.FC = () => {
  const {
    isLoading,
    error: wasmError,
    status,
    logs,
    result,
    transpileZip,
    clearLogs,
    downloadResult,
  } = useWASMTranspiler();

  const [selectedFile, setSelectedFile] = useState<File | null>(null);
  const [transpileResult, setTranspileResult] = useState<TranspileResult | null>(null);

  /**
   * Handle ZIP file selection and transpilation
   */
  const handleFileSelected = useCallback(async (file: File) => {
    setSelectedFile(file);
    setTranspileResult(null);

    try {
      const result = await transpileZip(file);
      setTranspileResult(result);
    } catch (error) {
      console.error('Transpilation failed:', error);
    }
  }, [transpileZip]);

  /**
   * Handle download
   */
  const handleDownload = useCallback(() => {
    if (!transpileResult || !transpileResult.success) {
      return;
    }

    const baseName = selectedFile?.name.replace('.zip', '') || 'output';
    downloadResult(transpileResult, baseName);
  }, [transpileResult, selectedFile, downloadResult]);

  /**
   * Handle reset
   */
  const handleReset = useCallback(() => {
    setSelectedFile(null);
    setTranspileResult(null);
    clearLogs();
  }, [clearLogs]);

  const canDownload = transpileResult?.success === true;
  const isTranspiling = status === 'transpiling' || status === 'extracting';
  const isReady = status === 'ready';

  // Loading state
  if (isLoading) {
    return (
      <div className="idbfs-playground loading-state">
        <div className="loading-spinner" />
        <p>Loading WASM transpiler module...</p>
        <style>{styles}</style>
      </div>
    );
  }

  // Error state
  if (wasmError) {
    return (
      <div className="idbfs-playground error-state">
        <h2>Failed to Load WASM Module</h2>
        <p className="error-message">{wasmError}</p>
        <p className="error-help">
          Please refresh the page to try again. If the problem persists,
          your browser may not support WebAssembly or IndexedDB.
        </p>
        <style>{styles}</style>
      </div>
    );
  }

  return (
    <div className="idbfs-playground">
      <div className="playground-header">
        <h1>C++ to C Transpiler - ZIP Upload Mode</h1>
        <p className="playground-subtitle">
          Upload a ZIP file with your C++ project and transpile it entirely in the browser!
        </p>
      </div>

      {/* Section 1: Upload */}
      <section className="playground-section">
        <h2 className="section-title">1. Upload and Transpile C++ Project</h2>
        <ZipUpload
          onFileSelected={handleFileSelected}
          disabled={isLoading || isTranspiling}
          selectedFile={selectedFile}
        />
        {transpileResult && transpileResult.success && (
          <div className="success-badge" role="status">
            ✓ Transpilation completed successfully
          </div>
        )}
        {transpileResult && !transpileResult.success && (
          <div className="error-badge" role="status">
            ✗ Transpilation failed - check console for details
          </div>
        )}
      </section>

      {/* Section 2: Actions */}
      <section className="playground-section">
        <h2 className="section-title">2. Download Results</h2>
        <div className="action-buttons">
          <button
            onClick={handleDownload}
            disabled={!canDownload}
            className="btn btn-success"
            aria-label="Download transpiled output"
          >
            Download Output
          </button>

          <button
            onClick={handleReset}
            disabled={isTranspiling}
            className="btn btn-secondary"
            aria-label="Reset and clear all data"
          >
            Reset
          </button>

          <div className="status-indicator">
            <span className="status-label">Status:</span>
            <span className={`status-badge status-${status}`}>
              {status.charAt(0).toUpperCase() + status.slice(1)}
            </span>
          </div>
        </div>

        {transpileResult && (
          <div className={`exit-code ${transpileResult.success ? 'success' : 'error'}`} role="status">
            Result: {transpileResult.success ? 'Success' : 'Failed'}
            {transpileResult.diagnostics.length > 0 && ` (${transpileResult.diagnostics.length} diagnostic${transpileResult.diagnostics.length > 1 ? 's' : ''})`}
          </div>
        )}
      </section>

      {/* Section 4: Console Output */}
      <section className="playground-section">
        <h2 className="section-title">4. Console Output</h2>
        <ConsoleOutput
          logs={logs}
          onClear={clearLogs}
          maxHeight="500px"
        />
      </section>

      <style>{styles}</style>
    </div>
  );
};

const styles = `
  .idbfs-playground {
    max-width: 1200px;
    margin: 0 auto;
    padding: 2rem;
  }

  .loading-state,
  .error-state {
    text-align: center;
    padding: 4rem 2rem;
  }

  .loading-spinner {
    width: 50px;
    height: 50px;
    border: 5px solid #e0e0e0;
    border-top-color: #667eea;
    border-radius: 50%;
    animation: spin 1s linear infinite;
    margin: 0 auto 1rem;
  }

  @keyframes spin {
    to { transform: rotate(360deg); }
  }

  .error-state h2 {
    color: #dc2626;
    margin-bottom: 1rem;
  }

  .error-message {
    color: #991b1b;
    background: #fee;
    border: 1px solid #fcc;
    padding: 1rem;
    border-radius: 6px;
    margin-bottom: 1rem;
  }

  .error-help {
    color: #6b7280;
    font-size: 0.9rem;
  }

  .playground-header {
    text-align: center;
    margin-bottom: 3rem;
    padding-bottom: 2rem;
    border-bottom: 2px solid #e5e7eb;
  }

  .playground-header h1 {
    margin: 0 0 0.5rem 0;
    font-size: 2rem;
    color: #1f2937;
    background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
    -webkit-background-clip: text;
    -webkit-text-fill-color: transparent;
    background-clip: text;
  }

  .playground-subtitle {
    color: #6b7280;
    font-size: 1.1rem;
  }

  .playground-section {
    margin-bottom: 2.5rem;
    background: white;
    border: 1px solid #e5e7eb;
    border-radius: 8px;
    padding: 2rem;
  }

  .section-title {
    margin: 0 0 1.5rem 0;
    font-size: 1.5rem;
    color: #667eea;
    font-weight: 600;
  }

  .success-badge {
    margin-top: 1rem;
    padding: 0.75rem 1rem;
    background: #d1fae5;
    border: 1px solid #6ee7b7;
    border-radius: 6px;
    color: #065f46;
    font-weight: 500;
  }

  .action-buttons {
    display: flex;
    flex-wrap: wrap;
    gap: 1rem;
    align-items: center;
  }

  .btn {
    padding: 0.75rem 1.5rem;
    border: none;
    border-radius: 6px;
    font-size: 1rem;
    font-weight: 600;
    cursor: pointer;
    transition: all 0.3s ease;
  }

  .btn:disabled {
    opacity: 0.5;
    cursor: not-allowed;
  }

  .btn-primary {
    background: #667eea;
    color: white;
  }

  .btn-primary:hover:not(:disabled) {
    background: #5568d3;
    transform: translateY(-2px);
    box-shadow: 0 4px 12px rgba(102, 126, 234, 0.4);
  }

  .btn-success {
    background: #48bb78;
    color: white;
  }

  .btn-success:hover:not(:disabled) {
    background: #38a169;
    transform: translateY(-2px);
    box-shadow: 0 4px 12px rgba(72, 187, 120, 0.4);
  }

  .btn-secondary {
    background: #718096;
    color: white;
  }

  .btn-secondary:hover:not(:disabled) {
    background: #4a5568;
  }

  .btn:focus-visible {
    outline: 3px solid rgba(102, 126, 234, 0.5);
    outline-offset: 2px;
  }

  .status-indicator {
    display: flex;
    align-items: center;
    gap: 0.5rem;
    padding: 0.5rem 1rem;
    background: #f9fafb;
    border: 1px solid #e5e7eb;
    border-radius: 6px;
  }

  .status-label {
    font-weight: 600;
    color: #6b7280;
  }

  .status-badge {
    padding: 0.25rem 0.75rem;
    border-radius: 4px;
    font-size: 0.875rem;
    font-weight: 600;
  }

  .status-idle {
    background: #e5e7eb;
    color: #6b7280;
  }

  .status-mounting,
  .status-extracting,
  .status-writing,
  .status-transpiling {
    background: #fef3c7;
    color: #92400e;
  }

  .status-success {
    background: #d1fae5;
    color: #065f46;
  }

  .status-error {
    background: #fee2e2;
    color: #991b1b;
  }

  .exit-code {
    margin-top: 1rem;
    padding: 0.75rem 1rem;
    border-radius: 6px;
    font-weight: 600;
  }

  .exit-code.success {
    background: #d1fae5;
    border: 1px solid #6ee7b7;
    color: #065f46;
  }

  .exit-code.error {
    background: #fee2e2;
    border: 1px solid #fca5a5;
    color: #991b1b;
  }

  @media (max-width: 768px) {
    .idbfs-playground {
      padding: 1rem;
    }

    .playground-header h1 {
      font-size: 1.5rem;
    }

    .playground-subtitle {
      font-size: 1rem;
    }

    .playground-section {
      padding: 1.5rem;
    }

    .section-title {
      font-size: 1.25rem;
    }

    .action-buttons {
      flex-direction: column;
      align-items: stretch;
    }

    .btn {
      width: 100%;
    }

    .status-indicator {
      width: 100%;
      justify-content: space-between;
    }
  }
`;
