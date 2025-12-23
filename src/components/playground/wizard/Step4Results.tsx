import React from 'react';
import { WizardStepper } from './WizardStepper';
import { FileTreeView } from './FileTreeView';
import { DualPaneViewer } from './DualPaneViewer';
import { DownloadOptions } from './DownloadOptions';
import { ErrorSummary } from './ErrorSummary';
import type { WizardState, FileInfo } from './types';
import { loadFileContent, findFileByPath } from './utils/loadFileContent';

interface Step4Props {
  state: WizardState;
  onFileSelected: (filePath: string) => void;
  onDownload: () => void;
}

export const Step4Results: React.FC<Step4Props> = ({
  state,
  onFileSelected,
  onDownload
}) => {
  // Local state for loaded file contents
  const [sourceContent, setSourceContent] = React.useState<string>('');
  const [transpileContent, setTranspileContent] = React.useState<string>('');
  const [isLoading, setIsLoading] = React.useState<boolean>(false);
  const [loadError, setLoadError] = React.useState<string | null>(null);

  // Get list of files that were transpiled (from state.sourceFiles)
  const transpiledFiles = React.useMemo(() => {
    return state.sourceFiles.filter(file =>
      state.transpilationResults.has(file.path)
    );
  }, [state.sourceFiles, state.transpilationResults]);

  // Calculate statistics
  const stats = React.useMemo(() => {
    const total = state.transpilationResults.size;
    const successful = Array.from(state.transpilationResults.values())
      .filter(r => r.success).length;
    const failed = total - successful;

    return { total, successful, failed };
  }, [state.transpilationResults]);

  // Load file contents when selectedPreviewFile changes
  React.useEffect(() => {
    const loadFile = async () => {
      if (!state.selectedPreviewFile) {
        setSourceContent('');
        setTranspileContent('');
        return;
      }

      setIsLoading(true);
      setLoadError(null);

      try {
        // Find source file
        const sourceFile = findFileByPath(state.sourceFiles, state.selectedPreviewFile);
        if (!sourceFile) {
          throw new Error('Source file not found');
        }

        // Load source content
        const source = await loadFileContent(sourceFile.handle);
        setSourceContent(source);

        // Get transpilation result
        const result = state.transpilationResults.get(state.selectedPreviewFile);
        if (result?.success && result.cCode) {
          setTranspileContent(result.cCode);
        } else if (result?.error) {
          setTranspileContent(`// Transpilation failed:\n// ${result.error}`);
        } else {
          setTranspileContent('// No transpiled output available');
        }
      } catch (error) {
        console.error('Error loading file:', error);
        setLoadError(error instanceof Error ? error.message : 'Unknown error');
        setSourceContent('');
        setTranspileContent('');
      } finally {
        setIsLoading(false);
      }
    };

    loadFile();
  }, [state.selectedPreviewFile, state.sourceFiles, state.transpilationResults]);

  // Handle file selection from tree
  const handleFileSelect = React.useCallback((file: FileInfo) => {
    onFileSelected(file.path);
  }, [onFileSelected]);

  // Handle file selection from error summary
  const handleErrorFileSelect = React.useCallback((filePath: string) => {
    onFileSelected(filePath);
  }, [onFileSelected]);

  // Calculate elapsed time
  const elapsedTime = React.useMemo(() => {
    if (!state.transpileStartTime) return undefined;
    return Date.now() - state.transpileStartTime;
  }, [state.transpileStartTime]);

  // Empty state: no transpilation results
  if (state.transpilationResults.size === 0) {
    return (
      <>
        <WizardStepper />
        <div className="wizard-step-content">
          <div className="empty-state">
            <h2>No Results Yet</h2>
            <p>Complete transpilation in Step 3 to view results here.</p>
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

          .empty-state {
            text-align: center;
            padding: 4rem 2rem;
            color: #666;
          }

          .empty-state h2 {
            margin: 0 0 1rem 0;
            color: #999;
          }
        `}</style>
      </>
    );
  }

  return (
    <>
      <WizardStepper />
      <div className="wizard-step-content">
        <div className="results-header">
          <h2>Step 4: Results</h2>

          {/* Statistics */}
          <div className="results-stats">
            <div className="stat">
              <span className="stat-label">Total:</span>
              <span className="stat-value">{stats.total}</span>
            </div>
            <div className="stat stat-success">
              <span className="stat-label">Success:</span>
              <span className="stat-value">{stats.successful}</span>
            </div>
            {stats.failed > 0 && (
              <div className="stat stat-error">
                <span className="stat-label">Failed:</span>
                <span className="stat-value">{stats.failed}</span>
              </div>
            )}
          </div>
        </div>

        {/* Main content: Tree + Viewer */}
        <div className="results-content">
          {/* Left: File tree */}
          <div className="results-tree">
            <h3>Transpiled Files</h3>
            <FileTreeView
              files={transpiledFiles}
              selectedFile={state.selectedPreviewFile || undefined}
              onFileSelect={handleFileSelect}
              height={500}
            />
          </div>

          {/* Right: Dual-pane viewer */}
          <div className="results-viewer">
            {loadError ? (
              <div className="load-error">
                <h3>Error Loading File</h3>
                <p>{loadError}</p>
              </div>
            ) : isLoading ? (
              <div className="loading-state">
                <p>Loading file contents...</p>
              </div>
            ) : (
              <DualPaneViewer
                sourceContent={sourceContent}
                sourceFilename={state.selectedPreviewFile || undefined}
                transpileContent={transpileContent}
                transpileFilename={
                  state.selectedPreviewFile
                    ? state.selectedPreviewFile.replace(/\.(cpp|cc|cxx)$/i, '.c')
                    : undefined
                }
              />
            )}
          </div>
        </div>

        {/* Download and Error sections */}
        <div className="results-footer">
          {/* Error summary (only if errors exist) */}
          <ErrorSummary
            transpilationResults={state.transpilationResults}
            onFileSelect={handleErrorFileSelect}
          />

          {/* Download options */}
          <DownloadOptions
            transpilationResults={state.transpilationResults}
            selectedFile={state.selectedPreviewFile}
            selectedFileContent={transpileContent}
            elapsedTime={elapsedTime}
            targetDirSelected={state.targetDir !== null}
          />
        </div>
      </div>

      <style>{`
        .wizard-step-content {
          background-color: #fff;
          border: 1px solid #ddd;
          border-radius: 8px;
          padding: 2rem;
          min-height: 600px;
        }

        .results-header {
          margin-bottom: 1.5rem;
        }

        .results-header h2 {
          margin: 0 0 1rem 0;
          font-size: 1.75rem;
          color: #333;
        }

        .results-stats {
          display: flex;
          gap: 1.5rem;
        }

        .stat {
          display: flex;
          align-items: center;
          gap: 0.5rem;
          padding: 0.5rem 1rem;
          background-color: #f5f5f5;
          border-radius: 4px;
        }

        .stat-label {
          font-size: 0.9rem;
          color: #666;
        }

        .stat-value {
          font-size: 1.25rem;
          font-weight: 600;
          color: #333;
        }

        .stat-success .stat-value {
          color: #4caf50;
        }

        .stat-error .stat-value {
          color: #f44336;
        }

        .results-content {
          display: grid;
          grid-template-columns: 300px 1fr;
          gap: 1.5rem;
          height: 500px;
        }

        .results-tree {
          display: flex;
          flex-direction: column;
        }

        .results-tree h3 {
          margin: 0 0 0.75rem 0;
          font-size: 1rem;
          color: #666;
        }

        .results-viewer {
          display: flex;
          flex-direction: column;
        }

        .load-error,
        .loading-state {
          display: flex;
          flex-direction: column;
          align-items: center;
          justify-content: center;
          height: 100%;
          background-color: #fafafa;
          border: 1px solid #ddd;
          border-radius: 8px;
          padding: 2rem;
        }

        .load-error {
          color: #f44336;
        }

        .load-error h3 {
          margin: 0 0 0.5rem 0;
        }

        .loading-state {
          color: #666;
          font-style: italic;
        }

        .results-footer {
          margin-top: 2rem;
          display: flex;
          flex-direction: column;
          gap: 1.5rem;
        }

        @media (max-width: 768px) {
          .results-content {
            grid-template-columns: 1fr;
            grid-template-rows: 250px 1fr;
            height: auto;
          }
        }
      `}</style>
    </>
  );
};
