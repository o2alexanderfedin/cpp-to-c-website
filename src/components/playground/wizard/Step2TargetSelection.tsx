import React, { useState, useEffect, useCallback } from 'react';
import { WizardStepper } from './WizardStepper';
import { PermissionIndicator } from './PermissionIndicator';
import { ConflictWarning } from './ConflictWarning';
import type { WizardState, TranspileOptions } from './types';
import {
  checkDirectoryPermissions,
  requestWritePermission,
  type PermissionStatus
} from './utils/checkDirectoryPermissions';
import {
  detectConflicts,
  type ConflictDetectionResult
} from './utils/detectConflicts';

interface Step2Props {
  state: WizardState;
  onTargetDirSelected: (dir: FileSystemDirectoryHandle) => void;
  onOptionsChanged: (options: TranspileOptions) => void;
}

export const Step2TargetSelection: React.FC<Step2Props> = ({
  state,
  onTargetDirSelected,
  onOptionsChanged
}) => {
  const [permissions, setPermissions] = useState<PermissionStatus>({
    read: false,
    write: false
  });
  const [isSelecting, setIsSelecting] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [conflictResult, setConflictResult] = useState<ConflictDetectionResult | null>(null);
  const [isScanning, setIsScanning] = useState(false);
  const [userAcknowledgedConflicts, setUserAcknowledgedConflicts] = useState(false);

  // Check permissions when target directory changes
  useEffect(() => {
    if (state.targetDir) {
      checkDirectoryPermissions(state.targetDir).then(setPermissions);
    }
  }, [state.targetDir]);

  // Detect conflicts when target directory or source files change
  useEffect(() => {
    async function scanForConflicts() {
      if (!state.targetDir || state.sourceFiles.length === 0) {
        setConflictResult(null);
        return;
      }

      setIsScanning(true);
      setError(null);
      setUserAcknowledgedConflicts(false);

      try {
        const result = await detectConflicts(state.sourceFiles, state.targetDir);
        setConflictResult(result);
      } catch (err) {
        setError(err instanceof Error ? err.message : 'Failed to scan target directory');
        setConflictResult(null);
      } finally {
        setIsScanning(false);
      }
    }

    scanForConflicts();
  }, [state.targetDir, state.sourceFiles]);

  const handleSelectDirectory = useCallback(async () => {
    setIsSelecting(true);
    setError(null);
    setUserAcknowledgedConflicts(false);

    try {
      // Check if File System Access API is supported
      if (!('showDirectoryPicker' in window)) {
        setError('Your browser does not support directory selection. Please use Chrome 105+ or Edge 105+.');
        return;
      }

      // Show directory picker
      const dirHandle = await window.showDirectoryPicker({
        mode: 'readwrite'
      });

      // Verify permissions
      const perms = await checkDirectoryPermissions(dirHandle);

      if (!perms.write) {
        // Try to request write permission
        const granted = await requestWritePermission(dirHandle);
        if (!granted) {
          setError('Write permission denied. Please select a directory where you have write access.');
          return;
        }
      }

      // Set target directory in wizard state
      onTargetDirSelected(dirHandle);

    } catch (err) {
      if (err instanceof Error) {
        // User cancelled or error occurred
        if (err.name !== 'AbortError') {
          setError(`Failed to select directory: ${err.message}`);
        }
      }
    } finally {
      setIsSelecting(false);
    }
  }, [onTargetDirSelected]);

  const handleRequestPermission = useCallback(async () => {
    if (!state.targetDir) return;

    const granted = await requestWritePermission(state.targetDir);
    if (granted) {
      const perms = await checkDirectoryPermissions(state.targetDir);
      setPermissions(perms);
    } else {
      setError('Write permission denied. Please select a different directory.');
    }
  }, [state.targetDir]);

  const handleOptionsChange = useCallback((field: keyof TranspileOptions, value: any) => {
    onOptionsChanged({
      ...state.targetOptions,
      [field]: value
    });
  }, [state.targetOptions, onOptionsChanged]);

  const handleConflictAcknowledgment = useCallback((acknowledged: boolean) => {
    setUserAcknowledgedConflicts(acknowledged);
  }, []);

  // Determine if user can proceed to next step
  const canProceed = state.targetDir !== null &&
    permissions.write &&
    (!conflictResult || conflictResult.conflictCount === 0 || userAcknowledgedConflicts);

  return (
    <>
      <WizardStepper />
      <div className="wizard-step-content">
        <h2>Step 2: Select Target Directory</h2>
        <p className="step-description">
          Choose where transpiled C files will be saved.
        </p>

        {/* Directory Selection */}
        <div className="directory-selection">
          <button
            className="select-directory-button"
            onClick={handleSelectDirectory}
            disabled={isSelecting}
          >
            {isSelecting ? 'Selecting...' : state.targetDir ? 'Change Target Directory' : 'Select Target Directory'}
          </button>

          {state.targetDir && (
            <div className="selected-directory">
              <strong>Selected Directory:</strong>
              <code>{state.targetDir.name}</code>
            </div>
          )}
        </div>

        {/* Permission Status */}
        {state.targetDir && (
          <PermissionIndicator
            hasRead={permissions.read}
            hasWrite={permissions.write}
            onRequestPermission={handleRequestPermission}
          />
        )}

        {/* Conflict Detection */}
        {isScanning && (
          <div className="scanning-message">
            Scanning target directory for conflicts...
          </div>
        )}

        {conflictResult && !isScanning && (
          <ConflictWarning
            conflicts={conflictResult.conflicts}
            totalFiles={conflictResult.totalFiles}
            acknowledged={userAcknowledgedConflicts}
            onAcknowledgeChange={handleConflictAcknowledgment}
          />
        )}

        {/* Error Display */}
        {error && (
          <div className="error-message">
            {error}
          </div>
        )}

        {/* Transpilation Options */}
        <div className="transpile-options">
          <h3>Transpilation Options</h3>

          <label className="option-label">
            <span>Target C Standard:</span>
            <select
              value={state.targetOptions.targetStandard}
              onChange={(e) => handleOptionsChange('targetStandard', e.target.value)}
            >
              <option value="c99">C99</option>
              <option value="c11">C11</option>
            </select>
          </label>

          <label className="option-checkbox">
            <input
              type="checkbox"
              checked={state.targetOptions.includeACSL}
              onChange={(e) => handleOptionsChange('includeACSL', e.target.checked)}
            />
            <span>Include ACSL annotations</span>
          </label>
        </div>

        {/* Navigation Hint */}
        {!canProceed && state.targetDir && (
          <div className="navigation-hint">
            {conflictResult && conflictResult.conflictCount > 0 && !userAcknowledgedConflicts && (
              <p>⚠️ Please acknowledge the file conflicts to proceed.</p>
            )}
            {!permissions.write && (
              <p>⚠️ Write permission required to proceed.</p>
            )}
          </div>
        )}
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

        .directory-selection {
          margin-bottom: 1.5rem;
        }

        .select-directory-button {
          padding: 0.75rem 1.5rem;
          background-color: #4A90E2;
          color: white;
          border: none;
          border-radius: 4px;
          cursor: pointer;
          font-size: 1rem;
          font-weight: 500;
          transition: background-color 0.15s;
        }

        .select-directory-button:hover:not(:disabled) {
          background-color: #357abd;
        }

        .select-directory-button:disabled {
          background-color: #ccc;
          cursor: not-allowed;
        }

        .selected-directory {
          margin-top: 1rem;
          padding: 0.75rem;
          background-color: #f5f5f5;
          border-radius: 4px;
          border: 1px solid #ddd;
        }

        .selected-directory code {
          display: inline-block;
          margin-left: 0.5rem;
          padding: 0.25rem 0.5rem;
          background-color: #fff;
          border: 1px solid #ddd;
          border-radius: 3px;
          font-family: 'Courier New', monospace;
          font-size: 0.9rem;
        }

        .error-message {
          margin: 1rem 0;
          padding: 0.75rem;
          background-color: #f8d7da;
          color: #721c24;
          border: 1px solid #f5c6cb;
          border-radius: 4px;
          font-size: 0.875rem;
        }

        .transpile-options {
          margin-top: 2rem;
          padding-top: 1.5rem;
          border-top: 1px solid #ddd;
        }

        .transpile-options h3 {
          margin: 0 0 1rem 0;
          font-size: 1.25rem;
          color: #333;
        }

        .option-label {
          display: flex;
          flex-direction: column;
          gap: 0.5rem;
          margin-bottom: 1rem;
        }

        .option-label span {
          font-weight: 500;
          color: #333;
        }

        .option-label select {
          padding: 0.5rem;
          border: 1px solid #ddd;
          border-radius: 4px;
          font-size: 1rem;
          max-width: 200px;
        }

        .option-checkbox {
          display: flex;
          align-items: center;
          gap: 0.5rem;
          cursor: pointer;
        }

        .option-checkbox input {
          width: 1.25rem;
          height: 1.25rem;
          cursor: pointer;
        }

        .scanning-message {
          padding: 1rem;
          background-color: #e7f3ff;
          border: 1px solid #b3d9ff;
          border-radius: 4px;
          margin: 1rem 0;
          color: #004085;
          font-size: 0.875rem;
        }

        .navigation-hint {
          margin-top: 1.5rem;
          padding: 0.75rem;
          background-color: #fff3cd;
          border: 1px solid #ffeaa7;
          border-radius: 4px;
        }

        .navigation-hint p {
          margin: 0;
          color: #856404;
          font-size: 0.875rem;
        }
      `}</style>
    </>
  );
};
