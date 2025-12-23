import React from 'react';

export interface ProgressIndicatorProps {
    current: number;
    total: number;
    currentFile?: string;
    onCancel?: () => void;
    isCancelling?: boolean;
    statusMessage?: string;
}

export const ProgressIndicator: React.FC<ProgressIndicatorProps> = ({
    current,
    total,
    currentFile,
    onCancel,
    isCancelling = false,
    statusMessage,
}) => {
    // Calculate percentage, handling edge cases
    const normalizedCurrent = Math.max(0, Math.min(current, total));
    const percentage = total > 0 ? Math.round((normalizedCurrent / total) * 100) : 0;

    // Determine visual state
    const isComplete = current >= total && total > 0;
    const className = `progress-indicator ${isComplete ? 'complete' : 'in-progress'} ${isCancelling ? 'cancelling' : ''}`;

    return (
        <div data-testid="progress-indicator" className={className}>
            <div className="progress-header">
                <div className="progress-info">
                    <span className="percentage">{percentage}%</span>
                    <span className="count">
                        {normalizedCurrent} / {total} files
                    </span>
                </div>

                {onCancel && (
                    <button
                        onClick={onCancel}
                        disabled={isCancelling}
                        aria-label="Cancel operation"
                        className="cancel-button"
                    >
                        {isCancelling ? 'Cancelling...' : 'Cancel'}
                    </button>
                )}
            </div>

            <div
                role="progressbar"
                aria-valuenow={normalizedCurrent}
                aria-valuemin={0}
                aria-valuemax={total}
                aria-label={`Progress: ${percentage}% complete, ${normalizedCurrent} of ${total} files processed`}
                className="progress-bar"
            >
                <div
                    data-testid="progress-bar-fill"
                    className="progress-bar-fill"
                    style={{ width: `${percentage}%` }}
                />
            </div>

            {currentFile && (
                <div data-testid="current-file" className="current-file">
                    Processing: {currentFile}
                </div>
            )}

            {statusMessage && (
                <div data-testid="status-message" className="status-message">
                    {statusMessage}
                </div>
            )}

            <style>{`
                .progress-indicator {
                    display: flex;
                    flex-direction: column;
                    gap: 0.75rem;
                    padding: 1rem;
                    border: 1px solid #ddd;
                    border-radius: 4px;
                    background-color: #fff;
                }

                .progress-indicator.complete {
                    border-color: #4caf50;
                }

                .progress-indicator.cancelling {
                    border-color: #ff9800;
                }

                .progress-header {
                    display: flex;
                    justify-content: space-between;
                    align-items: center;
                }

                .progress-info {
                    display: flex;
                    gap: 1rem;
                    align-items: baseline;
                }

                .percentage {
                    font-size: 1.5rem;
                    font-weight: bold;
                    color: #4A90E2;
                }

                .count {
                    font-size: 0.875rem;
                    color: #666;
                }

                .cancel-button {
                    padding: 0.5rem 1rem;
                    font-size: 0.875rem;
                    background-color: #fff;
                    color: #d32f2f;
                    border: 1px solid #d32f2f;
                    border-radius: 4px;
                    cursor: pointer;
                    transition: all 0.2s;
                }

                .cancel-button:hover:not(:disabled) {
                    background-color: #d32f2f;
                    color: #fff;
                }

                .cancel-button:disabled {
                    opacity: 0.5;
                    cursor: not-allowed;
                }

                .cancel-button:focus {
                    outline: 2px solid #d32f2f;
                    outline-offset: 2px;
                }

                .progress-bar {
                    width: 100%;
                    height: 24px;
                    background-color: #e0e0e0;
                    border-radius: 12px;
                    overflow: hidden;
                }

                .progress-bar-fill {
                    height: 100%;
                    background: linear-gradient(90deg, #4A90E2 0%, #357ABD 100%);
                    transition: width 0.3s ease;
                }

                .progress-indicator.complete .progress-bar-fill {
                    background: linear-gradient(90deg, #4caf50 0%, #45a049 100%);
                }

                .progress-indicator.cancelling .progress-bar-fill {
                    background: linear-gradient(90deg, #ff9800 0%, #f57c00 100%);
                }

                .current-file {
                    font-size: 0.875rem;
                    color: #666;
                    font-style: italic;
                    white-space: nowrap;
                    overflow: hidden;
                    text-overflow: ellipsis;
                }

                .status-message {
                    font-size: 0.875rem;
                    color: #666;
                }
            `}</style>
        </div>
    );
};
