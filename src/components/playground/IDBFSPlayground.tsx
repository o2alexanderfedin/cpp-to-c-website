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
  const handleDownload = useCallback(async () => {
    if (!transpileResult || !transpileResult.success) {
      return;
    }

    const baseName = selectedFile?.name.replace('.zip', '') || 'output';
    await downloadResult(transpileResult, baseName);
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
        <h1>🔄 C++ to C Transpiler - ZIP Upload Mode</h1>
        <p className="playground-subtitle">
          Upload a ZIP file with your C++ project and transpile it entirely in the browser!
        </p>
      </div>

      {/* Section 1: Upload */}
      <section className="playground-section">
        <h2 className="section-title">📦 Upload C++ Project</h2>
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
        <h2 className="section-title">▶️ Actions</h2>
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
        <h2 className="section-title">📊 Console Output</h2>
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
  * { box-sizing: border-box; margin: 0; padding: 0; }

  body {
    font-family: 'Segoe UI', system-ui, sans-serif;
  }

  .idbfs-playground {
    background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
    min-height: 100vh;
    padding: 20px;
  }

  .idbfs-playground > * {
    max-width: 1200px;
    margin: 0 auto;
    background: white;
    border-radius: 12px;
    box-shadow: 0 20px 60px rgba(0,0,0,0.3);
    overflow: hidden;
  }

  .loading-state,
  .error-state {
    text-align: center;
    padding: 4rem 2rem;
    background: white;
    border-radius: 12px;
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
    background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
    color: white;
    padding: 30px;
    text-align: center;
  }

  .playground-header h1 {
    font-size: 32px;
    margin-bottom: 10px;
  }

  .playground-subtitle {
    opacity: 0.9;
    font-size: 16px;
  }

  .playground-section {
    padding: 30px;
    border-bottom: 1px solid #e0e0e0;
  }

  .playground-section:last-child {
    border-bottom: none;
  }

  .section-title {
    color: #667eea;
    margin-bottom: 20px;
    font-size: 20px;
  }

  .success-badge,
  .error-badge {
    margin-top: 1rem;
    padding: 0.75rem 1rem;
    border-radius: 6px;
    font-weight: 500;
  }

  .success-badge {
    background: #d1fae5;
    border: 1px solid #6ee7b7;
    color: #065f46;
  }

  .error-badge {
    background: #fee2e2;
    border: 1px solid #fca5a5;
    color: #991b1b;
  }

  .action-buttons {
    display: flex;
    flex-wrap: wrap;
    gap: 1rem;
    align-items: center;
  }

  .btn {
    padding: 12px 24px;
    border: none;
    border-radius: 6px;
    font-size: 15px;
    font-weight: 600;
    cursor: pointer;
    transition: all 0.3s;
    margin-right: 10px;
    margin-bottom: 10px;
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
  }

  .btn-success {
    background: #48bb78;
    color: white;
  }

  .btn-success:hover:not(:disabled) {
    background: #38a169;
  }

  .btn-secondary {
    background: #718096;
    color: white;
  }

  .btn:focus-visible {
    outline: 3px solid rgba(102, 126, 234, 0.5);
    outline-offset: 2px;
  }

  .status-indicator {
    display: inline-flex;
    align-items: center;
    gap: 0.5rem;
  }

  .status-label {
    font-weight: 600;
    color: #6b7280;
  }

  .status-badge {
    display: inline-block;
    padding: 6px 12px;
    border-radius: 4px;
    font-size: 14px;
    font-weight: 600;
    margin-left: 10px;
  }

  .status-idle {
    background: #e5e7eb;
    color: #6b7280;
  }

  .status-loading {
    background: #ffd93d;
    color: #000;
  }

  .status-ready {
    background: #51cf66;
    color: white;
  }

  .status-mounting,
  .status-extracting,
  .status-writing,
  .status-transpiling {
    background: #ffd93d;
    color: #000;
  }

  .status-success {
    background: #51cf66;
    color: white;
  }

  .status-error {
    background: #ff6b6b;
    color: white;
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
      font-size: 24px;
    }

    .playground-subtitle {
      font-size: 14px;
    }

    .playground-section {
      padding: 20px;
    }

    .section-title {
      font-size: 18px;
    }

    .action-buttons {
      flex-direction: column;
      align-items: stretch;
    }

    .btn {
      width: 100%;
      margin-right: 0;
    }

    .status-indicator {
      width: 100%;
      justify-content: space-between;
    }
  }
`;
