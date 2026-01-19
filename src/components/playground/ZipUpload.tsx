/**
 * ZIP Upload Component
 *
 * Provides drag-and-drop and file picker interface for uploading ZIP files
 * containing C++ projects. Validates file type and structure before extraction.
 *
 * Features:
 * - Drag-and-drop zone with visual feedback
 * - File picker fallback
 * - Size and type validation
 * - Accessibility (keyboard navigation, screen reader support)
 *
 * @module ZipUpload
 */

import React, { useCallback, useState, useRef } from 'react';
import { validateZipStructure } from '../../lib/playground/idbfs';

export interface ZipUploadProps {
  /**
   * Callback when valid ZIP file is selected
   */
  onFileSelected: (file: File) => void;

  /**
   * Whether upload is disabled (e.g., during extraction)
   */
  disabled?: boolean;

  /**
   * Maximum file size in MB (default: 50)
   */
  maxSizeMB?: number;

  /**
   * Currently selected file (for display)
   */
  selectedFile?: File | null;
}

/**
 * ZIP Upload Component
 */
export const ZipUpload: React.FC<ZipUploadProps> = ({
  onFileSelected,
  disabled = false,
  maxSizeMB = 50,
  selectedFile = null,
}) => {
  const [isDragging, setIsDragging] = useState(false);
  const [error, setError] = useState<string>('');
  const [isValidating, setIsValidating] = useState(false);
  const fileInputRef = useRef<HTMLInputElement>(null);

  const maxSizeBytes = maxSizeMB * 1024 * 1024;

  /**
   * Validate and process selected file
   */
  const processFile = useCallback(async (file: File) => {
    setError('');
    setIsValidating(true);

    try {
      // Check file extension
      if (!file.name.endsWith('.zip')) {
        setError('Please select a .zip file');
        setIsValidating(false);
        return;
      }

      // Check file size
      if (file.size > maxSizeBytes) {
        setError(`File size exceeds ${maxSizeMB}MB limit`);
        setIsValidating(false);
        return;
      }

      // Validate ZIP structure
      const validation = await validateZipStructure(file);
      if (!validation.success) {
        setError(validation.message);
        setIsValidating(false);
        return;
      }

      // File is valid
      onFileSelected(file);
      setError('');
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Failed to process file');
    } finally {
      setIsValidating(false);
    }
  }, [maxSizeBytes, maxSizeMB, onFileSelected]);

  /**
   * Handle file input change
   */
  const handleFileInputChange = useCallback((event: React.ChangeEvent<HTMLInputElement>) => {
    const file = event.target.files?.[0];
    if (file) {
      processFile(file);
    }
  }, [processFile]);

  /**
   * Handle drag over
   */
  const handleDragOver = useCallback((event: React.DragEvent) => {
    event.preventDefault();
    event.stopPropagation();
    if (!disabled) {
      setIsDragging(true);
    }
  }, [disabled]);

  /**
   * Handle drag leave
   */
  const handleDragLeave = useCallback((event: React.DragEvent) => {
    event.preventDefault();
    event.stopPropagation();
    setIsDragging(false);
  }, []);

  /**
   * Handle drop
   */
  const handleDrop = useCallback((event: React.DragEvent) => {
    event.preventDefault();
    event.stopPropagation();
    setIsDragging(false);

    if (disabled) {
      return;
    }

    const file = event.dataTransfer.files[0];
    if (file) {
      processFile(file);
    }
  }, [disabled, processFile]);

  /**
   * Handle click on upload zone
   */
  const handleZoneClick = useCallback(() => {
    if (!disabled && fileInputRef.current) {
      fileInputRef.current.click();
    }
  }, [disabled]);

  /**
   * Handle keyboard activation
   */
  const handleKeyDown = useCallback((event: React.KeyboardEvent) => {
    if (event.key === 'Enter' || event.key === ' ') {
      event.preventDefault();
      handleZoneClick();
    }
  }, [handleZoneClick]);

  const zoneClassName = `upload-zone ${isDragging ? 'drag-over' : ''} ${disabled ? 'disabled' : ''}`;

  return (
    <div className="zip-upload-container">
      <div
        className={zoneClassName}
        onDragOver={handleDragOver}
        onDragLeave={handleDragLeave}
        onDrop={handleDrop}
        onClick={handleZoneClick}
        onKeyDown={handleKeyDown}
        role="button"
        tabIndex={disabled ? -1 : 0}
        aria-label="Upload ZIP file with drag and drop or click to browse"
        aria-disabled={disabled}
      >
        <div className="upload-icon" aria-hidden="true">
          📁
        </div>
        <div className="upload-text">
          <p className="upload-title">
            <strong>Drop a ZIP file here or click to browse</strong>
          </p>
          <p className="upload-subtitle">
            Supported: .zip files containing C++ source code (.cpp, .cxx, .cc)
          </p>
          <p className="upload-hint">
            Expected structure: src/*.cpp, include/*.h (or similar)
          </p>
          <p className="upload-limit">
            Maximum file size: {maxSizeMB}MB
          </p>
        </div>
      </div>

      <input
        ref={fileInputRef}
        type="file"
        accept=".zip"
        onChange={handleFileInputChange}
        disabled={disabled}
        aria-label="Select ZIP file"
        style={{ display: 'none' }}
      />

      {isValidating && (
        <div className="validating-state" role="status" aria-live="polite">
          <div className="spinner" />
          <span>Validating ZIP file...</span>
        </div>
      )}

      {error && (
        <div className="error-message" role="alert" aria-live="assertive">
          {error}
        </div>
      )}

      {selectedFile && !error && !isValidating && (
        <div className="file-info" role="status" aria-live="polite">
          <div className="file-info-row">
            <strong>Selected:</strong> {selectedFile.name}
          </div>
          <div className="file-info-row">
            <strong>Size:</strong> {(selectedFile.size / 1024).toFixed(2)} KB
          </div>
        </div>
      )}

      <style>{`
        .zip-upload-container {
          margin: 1.5rem 0;
        }

        .upload-zone {
          border: 3px dashed #cbd5e0;
          border-radius: 8px;
          padding: 3rem 2rem;
          text-align: center;
          cursor: pointer;
          transition: all 0.3s ease;
          background: #f7fafc;
          outline: none;
        }

        .upload-zone:hover:not(.disabled) {
          border-color: #667eea;
          background: #edf2f7;
        }

        .upload-zone:focus-visible {
          border-color: #667eea;
          box-shadow: 0 0 0 3px rgba(102, 126, 234, 0.3);
        }

        .upload-zone.drag-over {
          border-color: #667eea;
          background: #e6f2ff;
        }

        .upload-zone.disabled {
          opacity: 0.5;
          cursor: not-allowed;
          background: #e2e8f0;
        }

        .upload-icon {
          font-size: 4rem;
          margin-bottom: 1rem;
        }

        .upload-text {
          color: #4a5568;
        }

        .upload-title {
          font-size: 1.125rem;
          margin-bottom: 0.5rem;
        }

        .upload-subtitle {
          font-size: 0.875rem;
          color: #718096;
          margin-bottom: 0.25rem;
        }

        .upload-hint {
          font-size: 0.875rem;
          color: #718096;
          margin-bottom: 0.5rem;
        }

        .upload-limit {
          font-size: 0.8rem;
          color: #a0aec0;
        }

        .validating-state {
          display: flex;
          align-items: center;
          gap: 0.75rem;
          padding: 1rem;
          background-color: #f0f8ff;
          border: 1px solid #b3d9ff;
          border-radius: 6px;
          margin-top: 1rem;
        }

        .spinner {
          width: 20px;
          height: 20px;
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
          font-size: 0.9rem;
        }

        .file-info {
          padding: 1rem;
          background-color: #f0f9ff;
          border: 1px solid #bae6fd;
          border-radius: 6px;
          margin-top: 1rem;
        }

        .file-info-row {
          margin-bottom: 0.5rem;
          font-size: 0.9rem;
          color: #0c4a6e;
        }

        .file-info-row:last-child {
          margin-bottom: 0;
        }

        @media (max-width: 768px) {
          .upload-zone {
            padding: 2rem 1rem;
          }

          .upload-icon {
            font-size: 3rem;
          }

          .upload-title {
            font-size: 1rem;
          }
        }
      `}</style>
    </div>
  );
};
