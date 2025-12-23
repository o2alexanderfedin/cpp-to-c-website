import React, { useState } from 'react';

export interface DirectorySelectorProps {
    onDirectorySelected: (handle: FileSystemDirectoryHandle) => void;
    selectedPath?: string;
    onValidate?: (handle: FileSystemDirectoryHandle) => Promise<boolean>;
}

export const DirectorySelector: React.FC<DirectorySelectorProps> = ({
    onDirectorySelected,
    selectedPath,
    onValidate,
}) => {
    const [error, setError] = useState<string>('');
    const [isDragActive, setIsDragActive] = useState(false);

    const handleButtonClick = async () => {
        setError('');

        try {
            // Check if File System Access API is available
            if (!('showDirectoryPicker' in window)) {
                setError('File System Access API is not supported in this browser');
                return;
            }

            const handle = await (window as any).showDirectoryPicker();

            if (!handle) {
                return;
            }

            // Validate if custom validation provided
            if (onValidate) {
                const isValid = await onValidate(handle);
                if (!isValid) {
                    setError('Directory validation failed');
                    return;
                }
            }

            onDirectorySelected(handle);
        } catch (err: any) {
            // User cancelled - don't show error
            if (err.name === 'AbortError') {
                return;
            }

            setError(`Error selecting directory: ${err.message}`);
        }
    };

    const handleDragOver = (e: React.DragEvent) => {
        e.preventDefault();
        e.stopPropagation();
        setIsDragActive(true);
    };

    const handleDragLeave = (e: React.DragEvent) => {
        e.preventDefault();
        e.stopPropagation();
        setIsDragActive(false);
    };

    const handleDrop = async (e: React.DragEvent) => {
        e.preventDefault();
        e.stopPropagation();
        setIsDragActive(false);
        setError('');

        try {
            const items = Array.from(e.dataTransfer.items);

            if (items.length === 0) {
                return;
            }

            const item = items[0];

            if (item.kind !== 'file') {
                setError('Invalid item type');
                return;
            }

            // Get file system handle
            if (typeof (item as any).getAsFileSystemHandle !== 'function') {
                setError('Drag and drop of directories is not supported in this browser');
                return;
            }

            const handle = await (item as any).getAsFileSystemHandle();

            if (!handle) {
                return;
            }

            // Check if it's a directory
            if (handle.kind !== 'directory') {
                setError('Selected item must be a directory');
                return;
            }

            // Validate if custom validation provided
            if (onValidate) {
                const isValid = await onValidate(handle);
                if (!isValid) {
                    setError('Directory validation failed');
                    return;
                }
            }

            onDirectorySelected(handle);
        } catch (err: any) {
            setError(`Error processing dropped item: ${err.message}`);
        }
    };

    return (
        <div className="directory-selector">
            <button
                onClick={handleButtonClick}
                aria-label="Select directory"
                className="select-button"
            >
                Select Directory
            </button>

            <div
                data-testid="drop-zone"
                onDragOver={handleDragOver}
                onDragLeave={handleDragLeave}
                onDrop={handleDrop}
                className={`drop-zone ${isDragActive ? 'drag-active' : ''}`}
                aria-label="Drag and drop directory here"
            >
                <p>Or drag and drop a directory here</p>
            </div>

            {selectedPath && (
                <div data-testid="selected-path" className="selected-path">
                    <strong>Selected:</strong> {selectedPath}
                </div>
            )}

            {error && (
                <div role="alert" aria-live="polite" className="error-message">
                    {error}
                </div>
            )}

            <style>{`
                .directory-selector {
                    display: flex;
                    flex-direction: column;
                    gap: 1rem;
                    padding: 1rem;
                }

                .select-button {
                    padding: 0.75rem 1.5rem;
                    font-size: 1rem;
                    background-color: #4A90E2;
                    color: white;
                    border: none;
                    border-radius: 4px;
                    cursor: pointer;
                    transition: background-color 0.2s;
                }

                .select-button:hover {
                    background-color: #357ABD;
                }

                .select-button:focus {
                    outline: 2px solid #4A90E2;
                    outline-offset: 2px;
                }

                .drop-zone {
                    border: 2px dashed #ccc;
                    border-radius: 4px;
                    padding: 2rem;
                    text-align: center;
                    transition: border-color 0.2s, background-color 0.2s;
                }

                .drop-zone.drag-active {
                    border-color: #4A90E2;
                    background-color: #f0f8ff;
                }

                .selected-path {
                    padding: 0.5rem;
                    background-color: #e8f4f8;
                    border-radius: 4px;
                }

                .error-message {
                    padding: 0.75rem;
                    background-color: #fee;
                    border: 1px solid #fcc;
                    border-radius: 4px;
                    color: #c00;
                }
            `}</style>
        </div>
    );
};
