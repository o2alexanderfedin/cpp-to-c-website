import React, { useState, useCallback, useEffect } from 'react';
import { WizardStepper } from './WizardStepper';
import { FileTreeView, FileStatus } from './FileTreeView';
import { useTranspilation } from './hooks/useTranspilation';
import type { WizardState, TranspileResult } from './types';

interface Step3Props {
  state: WizardState;
  onStartTranspilation: () => void;
  onPauseTranspilation: () => void;
  onCancelTranspilation: () => void;
  onFileCompleted: (filePath: string, result: TranspileResult) => void;
}

export const Step3Transpilation: React.FC<Step3Props> = ({
  state,
  onStartTranspilation,
  onPauseTranspilation,
  onCancelTranspilation,
  onFileCompleted
}) => {
  const [currentFile, setCurrentFile] = useState<string | null>(null);
  const [fileStatuses, setFileStatuses] = useState<Map<string, FileStatus>>(new Map());
  const [fileErrors, setFileErrors] = useState<Map<string, string>>(new Map());
  const [showErrorDetails, setShowErrorDetails] = useState(false);
  const [progress, setProgress] = useState({ current: 0, total: 0, percentage: 0 });
  const [metrics, setMetrics] = useState({
    elapsedMs: 0,
    filesPerSecond: 0,
    estimatedRemainingMs: 0
  });
  const [isPaused, setIsPaused] = useState(false);
  const [hasStarted, setHasStarted] = useState(false);
  const [isComplete, setIsComplete] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [executionMode, setExecutionMode] = useState<'parallel' | 'sequential' | null>(null);

  // Initialize all files as pending
  useEffect(() => {
    const initialStatuses = new Map<string, FileStatus>();
    state.sourceFiles.forEach(file => {
      initialStatuses.set(file.path, FileStatus.PENDING);
    });
    setFileStatuses(initialStatuses);
  }, [state.sourceFiles]);

  // Transpilation hook with callbacks
  const transpilation = useTranspilation({
    onFileStarted: (filePath) => {
      setCurrentFile(filePath);
      setFileStatuses(prev => {
        const updated = new Map(prev);
        updated.set(filePath, FileStatus.IN_PROGRESS);
        return updated;
      });
    },
    onFileCompleted: (filePath, result) => {
      setFileStatuses(prev => {
        const updated = new Map(prev);
        updated.set(filePath, result.success ? FileStatus.SUCCESS : FileStatus.ERROR);
        return updated;
      });
      // Save result to wizard state for Step 4
      onFileCompleted(filePath, result);
    },
    onFileError: (filePath, errorMsg) => {
      setFileStatuses(prev => {
        const updated = new Map(prev);
        updated.set(filePath, FileStatus.ERROR);
        return updated;
      });
      setFileErrors(prev => {
        const updated = new Map(prev);
        updated.set(filePath, errorMsg);
        return updated;
      });
      console.error(`Error transpiling ${filePath}:`, errorMsg);
    },
    onProgress: (current, total, percentage) => {
      setProgress({ current, total, percentage });
    },
    onMetrics: (elapsedMs, filesPerSecond, estimatedRemainingMs) => {
      setMetrics({ elapsedMs, filesPerSecond, estimatedRemainingMs });
    },
    onCompleted: () => {
      setIsComplete(true);
      setCurrentFile(null);
    },
    onCancelled: () => {
      onCancelTranspilation();
      setCurrentFile(null);
    },
    onError: (errorMsg) => {
      setError(errorMsg);
    }
  });

  // Auto-start transpilation when entering this step
  useEffect(() => {
    if (!hasStarted && state.sourceFiles.length > 0 && state.targetDir) {
      setHasStarted(true);
      onStartTranspilation();

      // Start transpilation
      transpilation.start(
        state.sourceFiles,
        state.targetDir,
        state.targetOptions
      );

      // Detect execution mode after a brief delay
      setTimeout(() => {
        const mode = transpilation.getExecutionMode();
        if (mode) {
          setExecutionMode(mode);
        }
      }, 100);
    }
  }, [hasStarted, state, onStartTranspilation, transpilation]);

  const handlePause = useCallback(() => {
    transpilation.pause();
    setIsPaused(true);
    onPauseTranspilation();
  }, [transpilation, onPauseTranspilation]);

  const handleResume = useCallback(() => {
    transpilation.resume();
    setIsPaused(false);
  }, [transpilation]);

  const handleCancel = useCallback(() => {
    transpilation.cancel();
  }, [transpilation]);

  // Keyboard shortcuts
  useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      // Space = pause/resume
      if (event.code === 'Space' && !isComplete) {
        event.preventDefault();
        if (isPaused) {
          handleResume();
        } else {
          handlePause();
        }
      }

      // Escape = cancel
      if (event.code === 'Escape' && !isComplete) {
        event.preventDefault();
        if (window.confirm('Are you sure you want to cancel transpilation?')) {
          handleCancel();
        }
      }
    };

    window.addEventListener('keydown', handleKeyDown);

    return () => {
      window.removeEventListener('keydown', handleKeyDown);
    };
  }, [isPaused, isComplete, handlePause, handleResume, handleCancel]);

  // Format time in MM:SS
  const formatTime = (ms: number): string => {
    const seconds = Math.floor(ms / 1000);
    const minutes = Math.floor(seconds / 60);
    const remainingSeconds = seconds % 60;
    return `${minutes}:${remainingSeconds.toString().padStart(2, '0')}`;
  };

  // Count files by status
  const successCount = Array.from(fileStatuses.values()).filter(s => s === FileStatus.SUCCESS).length;
  const errorCount = Array.from(fileStatuses.values()).filter(s => s === FileStatus.ERROR).length;
  const completedCount = successCount + errorCount; // Total completed (success + error)

  return (
    <>
      <WizardStepper />
      <div className="wizard-step-content">
        <h2>Step 3: Transpilation</h2>
        <p className="step-description">
          Transpiling your C++ files to C...
        </p>

        <div className="transpilation-layout">
          {/* Left: Progress and Controls */}
          <div className="progress-section">
            {/* Execution Mode Indicator */}
            {executionMode && (
              <div className="execution-mode-indicator">
                {executionMode === 'parallel' ? (
                  <span className="parallel-mode">
                    ⚡ Parallel Mode ({navigator.hardwareConcurrency - 1} workers)
                  </span>
                ) : (
                  <span className="sequential-mode">
                    ⏱️ Sequential Mode
                  </span>
                )}
              </div>
            )}

            {/* Progress Bar */}
            <div className="progress-container">
              <div className={`progress-bar ${isPaused ? 'paused' : ''}`}>
                <div
                  className="progress-fill"
                  style={{ width: `${state.sourceFiles.length > 0 ? (completedCount / state.sourceFiles.length) * 100 : 0}%` }}
                />
                {isPaused && (
                  <div className="pause-indicator">
                    <span className="pause-icon">⏸</span>
                    <span className="pause-text">Paused</span>
                  </div>
                )}
              </div>
              <div className="progress-text">
                {completedCount} of {state.sourceFiles.length} files ({state.sourceFiles.length > 0 ? Math.round((completedCount / state.sourceFiles.length) * 100) : 0}%)
              </div>
            </div>

            {/* Current File */}
            {currentFile && (
              <div className="current-file">
                <strong>Processing:</strong> <code>{currentFile}</code>
              </div>
            )}

            {/* Status Summary */}
            <div className="status-summary">
              <div className="status-item success">
                <span className="status-icon">✓</span>
                <span className="status-count">{successCount} successful</span>
              </div>
              {errorCount > 0 && (
                <div className="status-item error">
                  <span className="status-icon">✗</span>
                  <span className="status-count">{errorCount} errors</span>
                </div>
              )}
            </div>

            {/* Error Details (Collapsible) */}
            {errorCount > 0 && (
              <div className="error-details-section">
                <button
                  className="error-details-toggle"
                  onClick={() => setShowErrorDetails(!showErrorDetails)}
                  aria-expanded={showErrorDetails}
                  aria-controls="error-details-list"
                >
                  {showErrorDetails ? '▼' : '▶'} {errorCount === 1 ? 'Show Error Detail' : `Show ${errorCount} Error Details`}
                </button>

                {showErrorDetails && (
                  <div className="error-details-list" id="error-details-list">
                    {Array.from(fileErrors.entries()).map(([filePath, errorMsg]) => (
                      <div key={filePath} className="error-detail-item">
                        <div className="error-file-path">
                          <span className="error-icon">✗</span>
                          <code>{filePath}</code>
                        </div>
                        <div className="error-message-text">{errorMsg}</div>
                      </div>
                    ))}
                  </div>
                )}
              </div>
            )}

            {/* Metrics */}
            <div className="metrics">
              <div className="metric">
                <span className="metric-label">Elapsed Time:</span>
                <span className="metric-value">{formatTime(metrics.elapsedMs)}</span>
              </div>
              <div className="metric">
                <span className="metric-label">Speed:</span>
                <span className="metric-value">
                  {metrics.filesPerSecond.toFixed(1)} files/sec
                </span>
              </div>
              <div className="metric">
                <span className="metric-label">Estimated Remaining:</span>
                <span className="metric-value">
                  {formatTime(metrics.estimatedRemainingMs)}
                </span>
              </div>
            </div>

            {/* Control Buttons */}
            {!isComplete && (
              <div className="transpilation-controls" role="group" aria-label="Transpilation controls">
                {!isPaused ? (
                  <button
                    className="control-button pause"
                    onClick={handlePause}
                    aria-label="Pause transpilation"
                    aria-pressed={isPaused}
                  >
                    <span className="button-icon">⏸</span>
                    <span>Pause</span>
                  </button>
                ) : (
                  <button
                    className="control-button resume"
                    onClick={handleResume}
                    aria-label="Resume transpilation"
                    aria-pressed={!isPaused}
                  >
                    <span className="button-icon">▶</span>
                    <span>Resume</span>
                  </button>
                )}
                <button
                  className="control-button cancel"
                  onClick={handleCancel}
                  aria-label="Cancel transpilation"
                >
                  <span className="button-icon">✖</span>
                  <span>Cancel</span>
                </button>
              </div>
            )}

            {/* Keyboard Hints */}
            {!isComplete && (
              <div className="keyboard-hints">
                <span className="hint">
                  <kbd>Space</kbd> {isPaused ? 'Resume' : 'Pause'}
                </span>
                <span className="hint">
                  <kbd>Esc</kbd> Cancel
                </span>
              </div>
            )}

            {/* Completion Message */}
            {isComplete && (
              <div className="completion-message">
                ✓ Transpilation complete! {successCount} files processed successfully
                {errorCount > 0 && `, ${errorCount} errors.`}
              </div>
            )}

            {/* Error Display */}
            {error && (
              <div className="error-message">
                Error: {error}
              </div>
            )}
          </div>

          {/* Right: File Tree with Live Status */}
          <div className="tree-section">
            <h3>File Status</h3>
            <FileTreeView
              files={state.sourceFiles}
              selectedFile={currentFile ?? undefined}
              fileStatuses={fileStatuses}
              height={500}
              autoScroll={true}
            />
          </div>
        </div>
      </div>

      <style>{`
        .wizard-step-content {
          background-color: #fff;
          border: 1px solid #ddd;
          border-radius: 8px;
          padding: 2rem;
          min-height: 400px;
        }

        .wizard-step-content h2 {
          margin: 0 0 0.5rem 0;
          font-size: 1.75rem;
          color: #333;
        }

        .step-description {
          margin: 0 0 1.5rem 0;
          color: #666;
        }

        .transpilation-layout {
          display: grid;
          grid-template-columns: 1fr 1fr;
          gap: 2rem;
        }

        @media (max-width: 768px) {
          .transpilation-layout {
            grid-template-columns: 1fr;
          }
        }

        .progress-section {
          display: flex;
          flex-direction: column;
          gap: 1.5rem;
        }

        .tree-section h3 {
          margin: 0 0 1rem 0;
          font-size: 1.25rem;
          color: #333;
        }

        .execution-mode-indicator {
          display: inline-flex;
          align-items: center;
          gap: 0.5rem;
          padding: 0.5rem 1rem;
          border-radius: 6px;
          font-size: 0.875rem;
          font-weight: 500;
          margin-bottom: 1rem;
        }

        .parallel-mode {
          color: #2ecc71;
          background-color: rgba(46, 204, 113, 0.1);
          border: 1px solid rgba(46, 204, 113, 0.3);
          padding: 0.375rem 0.75rem;
          border-radius: 4px;
          display: inline-flex;
          align-items: center;
          gap: 0.25rem;
        }

        .sequential-mode {
          color: #95a5a6;
          background-color: rgba(149, 165, 166, 0.1);
          border: 1px solid rgba(149, 165, 166, 0.3);
          padding: 0.375rem 0.75rem;
          border-radius: 4px;
          display: inline-flex;
          align-items: center;
          gap: 0.25rem;
        }

        .progress-container {
          /* Existing progress bar styles */
        }

        .progress-bar {
          width: 100%;
          height: 32px;
          background-color: #f0f0f0;
          border-radius: 4px;
          overflow: hidden;
          border: 1px solid #ddd;
          position: relative;
          transition: all 0.3s ease;
        }

        .progress-bar.paused {
          border-color: #ffc107;
          box-shadow: 0 0 0 2px rgba(255, 193, 7, 0.2);
        }

        .progress-fill {
          height: 100%;
          background: linear-gradient(90deg, #4A90E2 0%, #357abd 100%);
          transition: width 0.3s ease;
          position: relative;
          overflow: hidden;
        }

        /* Animated shimmer effect */
        .progress-fill::before {
          content: '';
          position: absolute;
          top: 0;
          left: -100%;
          width: 100%;
          height: 100%;
          background: linear-gradient(
            90deg,
            transparent,
            rgba(255, 255, 255, 0.3),
            transparent
          );
          animation: shimmer 2s infinite;
        }

        @keyframes shimmer {
          0% {
            left: -100%;
          }
          100% {
            left: 100%;
          }
        }

        .progress-bar.paused .progress-fill {
          background: linear-gradient(90deg, #ffc107 0%, #e0a800 100%);
        }

        .progress-bar.paused .progress-fill::before {
          animation: none;
        }

        .pause-indicator {
          position: absolute;
          top: 50%;
          left: 50%;
          transform: translate(-50%, -50%);
          display: flex;
          align-items: center;
          gap: 0.5rem;
          color: #333;
          font-weight: 600;
          z-index: 10;
        }

        .pause-icon {
          font-size: 1.25rem;
        }

        .pause-text {
          font-size: 0.875rem;
        }

        .progress-text {
          margin-top: 0.5rem;
          text-align: center;
          font-size: 0.875rem;
          color: #666;
        }

        .current-file {
          padding: 0.75rem;
          background-color: #e7f3ff;
          border: 1px solid #b3d9ff;
          border-radius: 4px;
        }

        .current-file code {
          font-family: 'Courier New', monospace;
          font-size: 0.9rem;
          margin-left: 0.5rem;
        }

        .status-summary {
          display: flex;
          gap: 1rem;
        }

        .status-item {
          display: flex;
          align-items: center;
          gap: 0.5rem;
          padding: 0.5rem 0.75rem;
          border-radius: 4px;
        }

        .status-item.success {
          background-color: #d4edda;
          color: #155724;
        }

        .status-item.error {
          background-color: #f8d7da;
          color: #721c24;
        }

        .status-icon {
          font-size: 1.25rem;
          font-weight: bold;
        }

        .status-count {
          font-size: 0.875rem;
          font-weight: 500;
        }

        .metrics {
          display: grid;
          grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
          gap: 1rem;
        }

        .metric {
          padding: 0.75rem;
          background-color: #f9f9f9;
          border: 1px solid #ddd;
          border-radius: 4px;
          display: flex;
          flex-direction: column;
          gap: 0.25rem;
        }

        .metric-label {
          font-size: 0.75rem;
          color: #666;
          text-transform: uppercase;
          letter-spacing: 0.5px;
        }

        .metric-value {
          font-size: 1.25rem;
          font-weight: 600;
          color: #333;
        }

        .transpilation-controls {
          display: flex;
          gap: 0.75rem;
        }

        .control-button {
          padding: 0.5rem 1.5rem;
          border: none;
          border-radius: 4px;
          cursor: pointer;
          font-size: 0.875rem;
          font-weight: 500;
          transition: all 0.15s;
          display: flex;
          align-items: center;
          gap: 0.5rem;
        }

        .button-icon {
          font-size: 1rem;
        }

        .control-button:focus-visible {
          outline: 2px solid #4A90E2;
          outline-offset: 2px;
        }

        .control-button:active {
          transform: scale(0.98);
        }

        .control-button.pause {
          background-color: #ffc107;
          color: #333;
        }

        .control-button.pause:hover {
          background-color: #e0a800;
        }

        .control-button.resume {
          background-color: #28a745;
          color: white;
        }

        .control-button.resume:hover {
          background-color: #218838;
        }

        .control-button.cancel {
          background-color: #dc3545;
          color: white;
        }

        .control-button.cancel:hover {
          background-color: #c82333;
        }

        .keyboard-hints {
          display: flex;
          gap: 1rem;
          padding: 0.75rem;
          background-color: #f9f9f9;
          border: 1px solid #ddd;
          border-radius: 4px;
          font-size: 0.75rem;
          color: #666;
        }

        .hint {
          display: flex;
          align-items: center;
          gap: 0.25rem;
        }

        kbd {
          padding: 0.125rem 0.375rem;
          background-color: #fff;
          border: 1px solid #ccc;
          border-radius: 3px;
          font-family: 'Courier New', monospace;
          font-size: 0.75rem;
          box-shadow: 0 1px 0 rgba(0, 0, 0, 0.2);
        }

        .completion-message {
          padding: 1rem;
          background-color: #d4edda;
          color: #155724;
          border: 1px solid #c3e6cb;
          border-radius: 4px;
          font-weight: 500;
        }

        .error-message {
          padding: 1rem;
          background-color: #f8d7da;
          color: #721c24;
          border: 1px solid #f5c6cb;
          border-radius: 4px;
        }

        .error-details-section {
          border: 1px solid #f5c6cb;
          border-radius: 4px;
          background-color: #fff;
          overflow: hidden;
        }

        .error-details-toggle {
          width: 100%;
          padding: 0.75rem 1rem;
          background-color: #f8d7da;
          color: #721c24;
          border: none;
          text-align: left;
          cursor: pointer;
          font-size: 0.875rem;
          font-weight: 500;
          display: flex;
          align-items: center;
          gap: 0.5rem;
          transition: background-color 0.15s;
        }

        .error-details-toggle:hover {
          background-color: #f5c6cb;
        }

        .error-details-toggle:focus-visible {
          outline: 2px solid #721c24;
          outline-offset: -2px;
        }

        .error-details-list {
          max-height: 300px;
          overflow-y: auto;
          border-top: 1px solid #f5c6cb;
        }

        .error-detail-item {
          padding: 0.75rem 1rem;
          border-bottom: 1px solid #f5c6cb;
        }

        .error-detail-item:last-child {
          border-bottom: none;
        }

        .error-file-path {
          display: flex;
          align-items: center;
          gap: 0.5rem;
          margin-bottom: 0.5rem;
          font-weight: 500;
        }

        .error-file-path .error-icon {
          color: #dc3545;
          font-size: 1rem;
        }

        .error-file-path code {
          color: #333;
          background-color: #f5f5f5;
          padding: 0.125rem 0.375rem;
          border-radius: 3px;
          font-size: 0.875rem;
        }

        .error-message-text {
          color: #721c24;
          font-size: 0.875rem;
          margin-left: 1.5rem;
          line-height: 1.5;
          white-space: pre-wrap;
          word-break: break-word;
        }
      `}</style>
    </>
  );
};
