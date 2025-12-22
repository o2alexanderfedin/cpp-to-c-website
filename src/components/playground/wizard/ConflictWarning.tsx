import React, { useState } from 'react';
import type { FileConflict } from './utils/detectConflicts';

export interface ConflictWarningProps {
  conflicts: FileConflict[];
  totalFiles: number;
  onProceed: () => void;
  onCancel: () => void;
}

export const ConflictWarning: React.FC<ConflictWarningProps> = ({
  conflicts,
  totalFiles,
  onProceed,
  onCancel
}) => {
  const [showDetails, setShowDetails] = useState(false);
  const conflictingFiles = conflicts.filter(c => c.exists);
  const conflictCount = conflictingFiles.length;

  if (conflictCount === 0) {
    return (
      <div className="conflict-warning success">
        <div className="warning-icon">✓</div>
        <div className="warning-content">
          <strong>No conflicts detected</strong>
          <p>All {totalFiles} files will be created as new files.</p>
        </div>

        <style>{`
          .conflict-warning.success {
            display: flex;
            gap: 1rem;
            padding: 1rem;
            background-color: #d4edda;
            border: 1px solid #c3e6cb;
            border-radius: 4px;
            margin: 1rem 0;
          }

          .conflict-warning.success .warning-icon {
            font-size: 1.5rem;
            color: #155724;
          }

          .conflict-warning.success .warning-content {
            flex: 1;
          }

          .conflict-warning.success strong {
            display: block;
            color: #155724;
            margin-bottom: 0.25rem;
          }

          .conflict-warning.success p {
            margin: 0;
            color: #155724;
            font-size: 0.875rem;
          }
        `}</style>
      </div>
    );
  }

  return (
    <div className="conflict-warning danger">
      <div className="warning-icon">⚠️</div>
      <div className="warning-content">
        <strong>File Conflicts Detected</strong>
        <p>
          {conflictCount} of {totalFiles} files already exist in the target directory and will be overwritten.
        </p>

        {/* Show/Hide Details Toggle */}
        <button
          className="toggle-details"
          onClick={() => setShowDetails(!showDetails)}
        >
          {showDetails ? 'Hide' : 'Show'} conflicting files
        </button>

        {/* Conflict List */}
        {showDetails && (
          <div className="conflict-list">
            <ul>
              {conflictingFiles.map((conflict, idx) => (
                <li key={idx}>
                  <code>{conflict.targetFileName}</code>
                  <span className="source-path">← {conflict.sourcePath}</span>
                </li>
              ))}
            </ul>
          </div>
        )}

        {/* Action Buttons */}
        <div className="conflict-actions">
          <button className="proceed-button" onClick={onProceed}>
            Proceed Anyway (Overwrite Files)
          </button>
          <button className="cancel-button" onClick={onCancel}>
            Choose Different Directory
          </button>
        </div>
      </div>

      <style>{`
        .conflict-warning.danger {
          display: flex;
          gap: 1rem;
          padding: 1rem;
          background-color: #fff3cd;
          border: 1px solid #ffeaa7;
          border-radius: 4px;
          margin: 1rem 0;
        }

        .conflict-warning.danger .warning-icon {
          font-size: 1.5rem;
          color: #856404;
          flex-shrink: 0;
        }

        .conflict-warning.danger .warning-content {
          flex: 1;
        }

        .conflict-warning.danger strong {
          display: block;
          color: #856404;
          margin-bottom: 0.25rem;
          font-size: 1rem;
        }

        .conflict-warning.danger p {
          margin: 0 0 0.75rem 0;
          color: #856404;
          font-size: 0.875rem;
        }

        .toggle-details {
          padding: 0.25rem 0.75rem;
          background: transparent;
          color: #856404;
          border: 1px solid #856404;
          border-radius: 3px;
          cursor: pointer;
          font-size: 0.875rem;
          transition: all 0.15s;
        }

        .toggle-details:hover {
          background-color: #856404;
          color: white;
        }

        .conflict-list {
          margin-top: 1rem;
          padding: 0.75rem;
          background-color: white;
          border: 1px solid #ddd;
          border-radius: 4px;
          max-height: 200px;
          overflow-y: auto;
        }

        .conflict-list ul {
          margin: 0;
          padding: 0;
          list-style: none;
        }

        .conflict-list li {
          padding: 0.5rem;
          border-bottom: 1px solid #f0f0f0;
          display: flex;
          align-items: center;
          gap: 0.5rem;
        }

        .conflict-list li:last-child {
          border-bottom: none;
        }

        .conflict-list code {
          font-family: 'Courier New', monospace;
          font-size: 0.875rem;
          padding: 0.125rem 0.375rem;
          background-color: #f5f5f5;
          border-radius: 3px;
          font-weight: 600;
        }

        .source-path {
          font-size: 0.75rem;
          color: #666;
        }

        .conflict-actions {
          margin-top: 1rem;
          display: flex;
          gap: 0.75rem;
          flex-wrap: wrap;
        }

        .proceed-button {
          padding: 0.5rem 1rem;
          background-color: #dc3545;
          color: white;
          border: none;
          border-radius: 4px;
          cursor: pointer;
          font-size: 0.875rem;
          font-weight: 500;
          transition: background-color 0.15s;
        }

        .proceed-button:hover {
          background-color: #c82333;
        }

        .cancel-button {
          padding: 0.5rem 1rem;
          background-color: #6c757d;
          color: white;
          border: none;
          border-radius: 4px;
          cursor: pointer;
          font-size: 0.875rem;
          font-weight: 500;
          transition: background-color 0.15s;
        }

        .cancel-button:hover {
          background-color: #5a6268;
        }
      `}</style>
    </div>
  );
};
