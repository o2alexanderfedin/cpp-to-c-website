import React, { useState } from 'react';
import type { TranspileError } from '../../features/transpile/types';

export interface ErrorDisplayProps {
    errors: TranspileError[];
    onCopy?: (text: string) => void;
    showSearch?: boolean;
}

export const ErrorDisplay: React.FC<ErrorDisplayProps> = ({
    errors,
    onCopy,
    showSearch = false,
}) => {
    const [expandedIndices, setExpandedIndices] = useState<Set<number>>(new Set());
    const [searchTerm, setSearchTerm] = useState('');
    const [copied, setCopied] = useState(false);

    const toggleExpand = (index: number) => {
        const newExpanded = new Set(expandedIndices);
        if (newExpanded.has(index)) {
            newExpanded.delete(index);
        } else {
            newExpanded.add(index);
        }
        setExpandedIndices(newExpanded);
    };

    const handleCopy = () => {
        if (!onCopy) return;

        const formattedErrors = errors
            .map(error => {
                let location = error.filePath || 'Unknown file';
                if (error.line !== undefined) {
                    location += `:${error.line}`;
                    if (error.column !== undefined) {
                        location += `:${error.column}`;
                    }
                }
                return `${location}\n  ${error.message}`;
            })
            .join('\n\n');

        onCopy(formattedErrors);
        setCopied(true);
        setTimeout(() => setCopied(false), 2000);
    };

    const filteredErrors = showSearch
        ? errors.filter(
              error =>
                  error.filePath.toLowerCase().includes(searchTerm.toLowerCase()) ||
                  error.message.toLowerCase().includes(searchTerm.toLowerCase())
          )
        : errors;

    const errorCount = errors.length;
    const filteredCount = filteredErrors.length;
    const hasErrors = errorCount > 0;

    return (
        <div
            data-testid="error-display"
            className={`error-display ${hasErrors ? 'has-errors' : 'no-errors'}`}
            role="region"
            aria-label="Error list"
        >
            <div className="error-header">
                <h3 className="error-title">
                    <span aria-live="polite">
                        {hasErrors
                            ? `${errorCount} error${errorCount === 1 ? '' : 's'}`
                            : 'No errors'}
                    </span>
                </h3>

                {onCopy && hasErrors && (
                    <button
                        onClick={handleCopy}
                        aria-label="Copy errors to clipboard"
                        className="copy-button"
                    >
                        {copied ? 'Copied!' : 'Copy to Clipboard'}
                    </button>
                )}
            </div>

            {showSearch && hasErrors && (
                <div className="search-container">
                    <input
                        type="text"
                        value={searchTerm}
                        onChange={e => setSearchTerm(e.target.value)}
                        placeholder="Search errors..."
                        aria-label="Search errors"
                        className="search-input"
                    />
                    {searchTerm && (
                        <span className="search-results">
                            Showing {filteredCount} of {errorCount} errors
                        </span>
                    )}
                </div>
            )}

            {!hasErrors ? (
                <div className="no-errors-message">
                    <p>No errors detected</p>
                </div>
            ) : (
                <ul className="error-list">
                    {filteredErrors.map((error, index) => {
                        const isExpanded = expandedIndices.has(index);
                        const hasLocation = error.line !== undefined;
                        const filePath = error.filePath || 'Unknown file';

                        return (
                            <li key={index} className={`error-item ${hasLocation ? 'has-location' : ''}`}>
                                <button
                                    onClick={() => toggleExpand(index)}
                                    aria-expanded={isExpanded}
                                    aria-label={`Error in ${filePath}`}
                                    className="error-item-button"
                                    tabIndex={0}
                                >
                                    <div className="error-header-row">
                                        <span
                                            data-testid="expand-indicator"
                                            className="expand-indicator"
                                        >
                                            {isExpanded ? '▼' : '▶'}
                                        </span>
                                        <span className="error-file-path">{filePath}</span>
                                        {error.line !== undefined && (
                                            <span className="error-location">
                                                Line {error.line}
                                                {error.column !== undefined && `, Column ${error.column}`}
                                            </span>
                                        )}
                                    </div>
                                </button>

                                <div className={`error-details ${isExpanded ? '' : 'collapsed'}`}>
                                    <p className="error-message">{error.message}</p>
                                </div>
                            </li>
                        );
                    })}
                </ul>
            )}

            <style>{`
                .error-display {
                    display: flex;
                    flex-direction: column;
                    gap: 1rem;
                    padding: 1rem;
                    border: 1px solid #ddd;
                    border-radius: 4px;
                    background-color: #fff;
                }

                .error-display.has-errors {
                    border-color: #d32f2f;
                }

                .error-header {
                    display: flex;
                    justify-content: space-between;
                    align-items: center;
                }

                .error-title {
                    margin: 0;
                    font-size: 1.25rem;
                    color: #d32f2f;
                }

                .error-display.no-errors .error-title {
                    color: #4caf50;
                }

                .copy-button {
                    padding: 0.5rem 1rem;
                    font-size: 0.875rem;
                    background-color: #fff;
                    color: #4A90E2;
                    border: 1px solid #4A90E2;
                    border-radius: 4px;
                    cursor: pointer;
                    transition: all 0.2s;
                }

                .copy-button:hover {
                    background-color: #4A90E2;
                    color: #fff;
                }

                .copy-button:focus {
                    outline: 2px solid #4A90E2;
                    outline-offset: 2px;
                }

                .search-container {
                    display: flex;
                    flex-direction: column;
                    gap: 0.5rem;
                }

                .search-input {
                    padding: 0.5rem;
                    border: 1px solid #ddd;
                    border-radius: 4px;
                    font-size: 0.875rem;
                }

                .search-input:focus {
                    outline: 2px solid #4A90E2;
                    outline-offset: 0;
                }

                .search-results {
                    font-size: 0.75rem;
                    color: #666;
                }

                .no-errors-message {
                    padding: 2rem;
                    text-align: center;
                    color: #4caf50;
                }

                .error-list {
                    list-style: none;
                    padding: 0;
                    margin: 0;
                    display: flex;
                    flex-direction: column;
                    gap: 0.5rem;
                }

                .error-item {
                    border: 1px solid #ffcdd2;
                    border-radius: 4px;
                    background-color: #fff;
                }

                .error-item.has-location {
                    border-left: 4px solid #d32f2f;
                }

                .error-item-button {
                    width: 100%;
                    padding: 0.75rem;
                    background: none;
                    border: none;
                    cursor: pointer;
                    text-align: left;
                    transition: background-color 0.2s;
                }

                .error-item-button:hover {
                    background-color: #ffebee;
                }

                .error-item-button:focus {
                    outline: 2px solid #d32f2f;
                    outline-offset: -2px;
                }

                .error-header-row {
                    display: flex;
                    gap: 0.5rem;
                    align-items: center;
                }

                .expand-indicator {
                    flex-shrink: 0;
                    color: #666;
                    font-size: 0.75rem;
                }

                .error-file-path {
                    font-weight: 500;
                    color: #333;
                    flex: 1;
                }

                .error-location {
                    font-size: 0.875rem;
                    color: #666;
                    white-space: nowrap;
                }

                .error-details {
                    padding: 0 0.75rem 0.75rem 2rem;
                    transition: max-height 0.3s ease;
                }

                .error-details.collapsed {
                    display: none;
                }

                .error-message {
                    margin: 0;
                    font-size: 0.875rem;
                    color: #d32f2f;
                    line-height: 1.5;
                    word-break: break-word;
                }
            `}</style>
        </div>
    );
};
