import React from 'react';
import type { TranspileResult } from './types';

export interface ErrorSummaryProps {
  transpilationResults: Map<string, TranspileResult>;
  onFileSelect: (filePath: string) => void;
}

export const ErrorSummary: React.FC<ErrorSummaryProps> = ({
  transpilationResults,
  onFileSelect,
}) => {
  // Get all failed transpilations
  const errors = React.useMemo(() => {
    const errorList: Array<{ path: string; result: TranspileResult }> = [];
    for (const [path, result] of transpilationResults.entries()) {
      if (!result.success) {
        errorList.push({ path, result });
      }
    }
    return errorList;
  }, [transpilationResults]);

  // No errors - show success message
  if (errors.length === 0) {
    return null; // Don't show component if no errors
  }

  return (
    <div className="error-summary">
      <div className="error-header">
        <span className="error-icon">⚠️</span>
        <h3>Transpilation Errors ({errors.length})</h3>
      </div>

      <div className="error-list">
        {errors.map(({ path, result }) => (
          <div key={path} className="error-item">
            <button
              className="error-file-link"
              onClick={() => onFileSelect(path)}
            >
              {path}
            </button>
            <div className="error-message">
              {result.error || 'Unknown error'}
            </div>
            {result.diagnostics && result.diagnostics.length > 0 && (
              <details className="error-diagnostics">
                <summary>View diagnostics ({result.diagnostics.length})</summary>
                <ul>
                  {result.diagnostics.map((diag, i) => (
                    <li key={i}>{diag}</li>
                  ))}
                </ul>
              </details>
            )}
          </div>
        ))}
      </div>

      <style>{`
        .error-summary {
          padding: 1.5rem;
          background-color: #fff3e0;
          border: 1px solid #ffb74d;
          border-radius: 8px;
        }

        .error-header {
          display: flex;
          align-items: center;
          gap: 0.5rem;
          margin-bottom: 1rem;
        }

        .error-icon {
          font-size: 1.5rem;
        }

        .error-header h3 {
          margin: 0;
          font-size: 1rem;
          font-weight: 600;
          color: #e65100;
        }

        .error-list {
          display: flex;
          flex-direction: column;
          gap: 1rem;
        }

        .error-item {
          padding: 1rem;
          background-color: #fff;
          border: 1px solid #ffcc80;
          border-radius: 4px;
        }

        .error-file-link {
          display: block;
          margin-bottom: 0.5rem;
          padding: 0;
          background: none;
          border: none;
          color: #1976d2;
          font-family: 'Consolas', 'Monaco', monospace;
          font-size: 0.9rem;
          font-weight: 600;
          cursor: pointer;
          text-align: left;
        }

        .error-file-link:hover {
          text-decoration: underline;
        }

        .error-message {
          color: #d32f2f;
          font-size: 0.9rem;
          margin-bottom: 0.5rem;
          font-family: 'Consolas', 'Monaco', monospace;
        }

        .error-diagnostics {
          margin-top: 0.5rem;
        }

        .error-diagnostics summary {
          cursor: pointer;
          font-size: 0.85rem;
          color: #666;
        }

        .error-diagnostics summary:hover {
          color: #333;
        }

        .error-diagnostics ul {
          margin: 0.5rem 0 0 0;
          padding-left: 1.5rem;
        }

        .error-diagnostics li {
          font-size: 0.85rem;
          color: #666;
          margin: 0.25rem 0;
          font-family: 'Consolas', 'Monaco', monospace;
        }
      `}</style>
    </div>
  );
};
