import React, { useState, useCallback } from 'react';
import { WizardStepper } from './WizardStepper';
import { DirectorySelector } from '../DirectorySelector';
import { FileTreeView } from './FileTreeView';
import { FileStatistics } from './FileStatistics';
import { discoverCppFiles } from './utils/fileDiscovery';
import type { WizardState, FileInfo } from './types';

interface Step1Props {
  state: WizardState;
  onSourceDirSelected: (dir: FileSystemDirectoryHandle, files: FileInfo[]) => void;
}

export const Step1SourceSelection: React.FC<Step1Props> = ({ state, onSourceDirSelected }) => {
  const [isDiscovering, setIsDiscovering] = useState(false);
  const [selectedPath, setSelectedPath] = useState<string>('');
  const [error, setError] = useState<string>('');

  /**
   * Handle directory selection
   */
  const handleDirectorySelected = useCallback(async (dirHandle: FileSystemDirectoryHandle) => {
    setIsDiscovering(true);
    setError('');

    try {
      // Discover C++ files recursively
      const files = await discoverCppFiles(dirHandle);

      if (files.length === 0) {
        setError('No C++ files found in the selected directory. Please select a directory containing C++ source files (.cpp, .cc, .cxx, .h, .hpp, .hxx).');
        setIsDiscovering(false);
        return;
      }

      // Update wizard state
      onSourceDirSelected(dirHandle, files);
      setSelectedPath(dirHandle.name);
      setError('');
    } catch (err: any) {
      setError(`Error discovering files: ${err.message}`);
      console.error('File discovery error:', err);
    } finally {
      setIsDiscovering(false);
    }
  }, [onSourceDirSelected]);

  const hasSourceFiles = state.sourceFiles.length > 0;

  return (
    <>
      <WizardStepper />
      <div className="wizard-step-content">
        <h2>Step 1: Select Source Directory</h2>
        <p className="step-description">
          Select a directory containing your C++ source code. We'll automatically discover all C++ files (.cpp, .cc, .cxx, .h, .hpp, .hxx) for transpilation.
        </p>

        {/* Directory Selector */}
        <DirectorySelector
          onDirectorySelected={handleDirectorySelected}
          selectedPath={selectedPath}
        />

        {/* Loading State */}
        {isDiscovering && (
          <div className="discovering-state" role="status" aria-live="polite">
            <div className="spinner"></div>
            <p>Discovering C++ files...</p>
          </div>
        )}

        {/* Error State */}
        {error && (
          <div className="error-message" role="alert" aria-live="assertive">
            {error}
          </div>
        )}

        {/* File Statistics */}
        {hasSourceFiles && !isDiscovering && (
          <div className="file-info-section">
            <h3>Discovered Files</h3>
            <FileStatistics files={state.sourceFiles} />
          </div>
        )}

        {/* File Tree View */}
        {hasSourceFiles && !isDiscovering && (
          <div className="file-tree-section">
            <h3>File Tree</h3>
            <FileTreeView files={state.sourceFiles} />
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
          margin: 0 0 2rem 0;
          color: #666;
          font-size: 1rem;
          line-height: 1.5;
        }

        .discovering-state {
          display: flex;
          align-items: center;
          gap: 1rem;
          padding: 1.5rem;
          background-color: #f0f8ff;
          border: 1px solid #b3d9ff;
          border-radius: 6px;
          margin-top: 1rem;
        }

        .spinner {
          width: 24px;
          height: 24px;
          border: 3px solid #e0e0e0;
          border-top-color: #4A90E2;
          border-radius: 50%;
          animation: spin 0.8s linear infinite;
        }

        @keyframes spin {
          to { transform: rotate(360deg); }
        }

        .error-message {
          padding: 1rem;
          background-color: #fee;
          border: 1px solid #fcc;
          border-radius: 6px;
          color: #c00;
          margin-top: 1rem;
        }

        .file-info-section,
        .file-tree-section {
          margin-top: 2rem;
        }

        .file-info-section h3,
        .file-tree-section h3 {
          margin: 0 0 1rem 0;
          font-size: 1.25rem;
          color: #333;
          font-weight: 600;
        }

        .file-tree-section {
          margin-bottom: 2rem;
        }

        @media (max-width: 768px) {
          .wizard-step-content {
            padding: 1rem;
          }
        }
      `}</style>
    </>
  );
};
