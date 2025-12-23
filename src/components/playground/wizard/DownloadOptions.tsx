import React from 'react';
import type { TranspileResult } from './types';
import {
  downloadFile,
  createZipArchive,
  downloadZip,
  calculateTotalBytes,
  formatBytes,
} from './utils/downloadHelpers';

export interface DownloadOptionsProps {
  transpilationResults: Map<string, TranspileResult>;
  selectedFile?: string | null;
  selectedFileContent?: string;
  selectedHeaderContent?: string;
  elapsedTime?: number; // In milliseconds
  targetDirSelected?: boolean; // Whether files were written to target dir
}

export const DownloadOptions: React.FC<DownloadOptionsProps> = ({
  transpilationResults,
  selectedFile,
  selectedFileContent,
  selectedHeaderContent,
  elapsedTime,
  targetDirSelected = false,
}) => {
  const [isCreatingZip, setIsCreatingZip] = React.useState(false);

  // Calculate metrics
  const metrics = React.useMemo(() => {
    const totalFiles = transpilationResults.size;
    const successfulFiles = Array.from(transpilationResults.values())
      .filter(r => r.success).length;
    const totalBytes = calculateTotalBytes(transpilationResults);
    const timeSeconds = elapsedTime ? (elapsedTime / 1000).toFixed(1) : null;

    return {
      totalFiles,
      successfulFiles,
      totalBytes,
      totalBytesFormatted: formatBytes(totalBytes),
      timeSeconds,
    };
  }, [transpilationResults, elapsedTime]);

  // Download current .c file
  const handleDownloadFile = React.useCallback(() => {
    if (!selectedFile || !selectedFileContent) return;

    const filename = selectedFile
      .replace(/\.(cpp|cc|cxx)$/i, '.c')
      .replace(/\.(hpp|hxx)$/i, '.h');
    downloadFile(filename, selectedFileContent);
  }, [selectedFile, selectedFileContent]);

  // Download current .h file
  const handleDownloadHeader = React.useCallback(() => {
    if (!selectedFile || !selectedHeaderContent) return;

    const filename = selectedFile
      .replace(/\.(cpp|cc|cxx)$/i, '.h')
      .replace(/\.(hpp|hxx)$/i, '.h');
    downloadFile(filename, selectedHeaderContent);
  }, [selectedFile, selectedHeaderContent]);

  // Download all as ZIP
  const handleDownloadZip = React.useCallback(async () => {
    setIsCreatingZip(true);
    try {
      const zipBlob = await createZipArchive(transpilationResults);
      downloadZip(zipBlob, 'transpiled-files.zip');
    } catch (error) {
      console.error('Failed to create ZIP:', error);
      alert('Failed to create ZIP archive. Please try again.');
    } finally {
      setIsCreatingZip(false);
    }
  }, [transpilationResults]);

  return (
    <div className="download-options">
      {/* Metrics section */}
      <div className="metrics-section">
        <h3>Transpilation Summary</h3>
        <div className="metrics-grid">
          <div className="metric">
            <span className="metric-value">{metrics.successfulFiles}</span>
            <span className="metric-label">
              File{metrics.successfulFiles !== 1 ? 's' : ''} Transpiled
            </span>
          </div>
          <div className="metric">
            <span className="metric-value">{metrics.totalBytesFormatted}</span>
            <span className="metric-label">Total Output</span>
          </div>
          {metrics.timeSeconds && (
            <div className="metric">
              <span className="metric-value">{metrics.timeSeconds}s</span>
              <span className="metric-label">Time Elapsed</span>
            </div>
          )}
        </div>
      </div>

      {/* Download buttons */}
      <div className="download-section">
        <h3>Download Options</h3>

        {targetDirSelected && (
          <div className="info-message">
            Files have been written to your target directory
          </div>
        )}

        <div className="download-buttons">
          <button
            className="download-btn download-btn-primary"
            onClick={handleDownloadZip}
            disabled={isCreatingZip || metrics.successfulFiles === 0}
          >
            {isCreatingZip ? 'Creating ZIP...' : 'Download All as ZIP'}
          </button>

          {selectedFile && selectedHeaderContent && (
            <button
              className="download-btn download-btn-secondary"
              onClick={handleDownloadHeader}
              disabled={!selectedHeaderContent}
            >
              Download Header (.h)
            </button>
          )}

          {selectedFile && (
            <button
              className="download-btn download-btn-secondary"
              onClick={handleDownloadFile}
              disabled={!selectedFileContent}
            >
              Download Implementation (.c)
            </button>
          )}
        </div>
      </div>

      <style>{`
        .download-options {
          display: flex;
          flex-direction: column;
          gap: 1.5rem;
          padding: 1.5rem;
          background-color: #f9f9f9;
          border: 1px solid #e0e0e0;
          border-radius: 8px;
        }

        .metrics-section h3,
        .download-section h3 {
          margin: 0 0 1rem 0;
          font-size: 1rem;
          font-weight: 600;
          color: #333;
        }

        .metrics-grid {
          display: grid;
          grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
          gap: 1rem;
        }

        .metric {
          display: flex;
          flex-direction: column;
          padding: 1rem;
          background-color: #fff;
          border: 1px solid #e0e0e0;
          border-radius: 4px;
          text-align: center;
        }

        .metric-value {
          font-size: 1.75rem;
          font-weight: 700;
          color: #4A90E2;
          margin-bottom: 0.25rem;
        }

        .metric-label {
          font-size: 0.85rem;
          color: #666;
        }

        .info-message {
          padding: 0.75rem 1rem;
          background-color: #e8f5e9;
          color: #2e7d32;
          border-radius: 4px;
          font-size: 0.9rem;
          margin-bottom: 1rem;
        }

        .download-buttons {
          display: flex;
          gap: 0.75rem;
          flex-wrap: wrap;
        }

        .download-btn {
          padding: 0.75rem 1.5rem;
          border: none;
          border-radius: 4px;
          font-size: 0.95rem;
          font-weight: 600;
          cursor: pointer;
          transition: all 0.2s;
        }

        .download-btn:disabled {
          opacity: 0.5;
          cursor: not-allowed;
        }

        .download-btn-primary {
          background-color: #4A90E2;
          color: #fff;
        }

        .download-btn-primary:hover:not(:disabled) {
          background-color: #357ABD;
        }

        .download-btn-secondary {
          background-color: #fff;
          color: #4A90E2;
          border: 2px solid #4A90E2;
        }

        .download-btn-secondary:hover:not(:disabled) {
          background-color: #f0f7ff;
        }
      `}</style>
    </div>
  );
};
