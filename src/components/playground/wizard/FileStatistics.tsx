import React from 'react';
import type { FileInfo } from './types';
import { calculateTotalSize, formatFileSize } from './utils/fileDiscovery';

interface FileStatisticsProps {
  files: FileInfo[];
}

/**
 * Display file count and size statistics
 */
export const FileStatistics: React.FC<FileStatisticsProps> = ({ files }) => {
  const fileCount = files.length;
  const totalSize = calculateTotalSize(files);
  const formattedSize = formatFileSize(totalSize);

  // Count source vs header files
  const sourceFiles = files.filter(f =>
    f.name.endsWith('.cpp') || f.name.endsWith('.cc') || f.name.endsWith('.cxx')
  ).length;
  const headerFiles = fileCount - sourceFiles;

  return (
    <div className="file-statistics">
      <div className="stat-item">
        <span className="stat-label">Total Files:</span>
        <span className="stat-value">{fileCount}</span>
      </div>

      <div className="stat-item">
        <span className="stat-label">Source Files:</span>
        <span className="stat-value">{sourceFiles}</span>
      </div>

      <div className="stat-item">
        <span className="stat-label">Header Files:</span>
        <span className="stat-value">{headerFiles}</span>
      </div>

      <div className="stat-item">
        <span className="stat-label">Total Size:</span>
        <span className="stat-value">{formattedSize}</span>
      </div>

      <style>{`
        .file-statistics {
          display: flex;
          gap: 1.5rem;
          padding: 1rem;
          background-color: #f5f5f5;
          border-radius: 6px;
          flex-wrap: wrap;
        }

        .stat-item {
          display: flex;
          flex-direction: column;
          gap: 0.25rem;
        }

        .stat-label {
          font-size: 0.875rem;
          color: #666;
          font-weight: 500;
        }

        .stat-value {
          font-size: 1.25rem;
          color: #333;
          font-weight: 600;
        }

        @media (max-width: 768px) {
          .file-statistics {
            flex-direction: column;
            gap: 0.75rem;
          }

          .stat-item {
            flex-direction: row;
            justify-content: space-between;
          }
        }
      `}</style>
    </div>
  );
};
