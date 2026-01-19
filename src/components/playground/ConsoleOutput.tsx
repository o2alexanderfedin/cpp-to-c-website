/**
 * Console Output Component
 *
 * Displays real-time console logs from the WASM transpiler with
 * color-coded severity levels and auto-scrolling.
 *
 * Features:
 * - Color-coded log levels (info, success, error, warn)
 * - Auto-scroll to bottom on new entries
 * - Timestamp display
 * - Clear functionality
 * - Accessibility (screen reader announcements)
 *
 * @module ConsoleOutput
 */

import React, { useEffect, useRef } from 'react';
import type { ConsoleLogEntry } from '../../lib/playground/idbfs-types';

export interface ConsoleOutputProps {
  /**
   * Array of log entries to display
   */
  logs: ConsoleLogEntry[];

  /**
   * Maximum height of console (default: 500px)
   */
  maxHeight?: string;

  /**
   * Callback for clear button
   */
  onClear?: () => void;

  /**
   * Show timestamps (default: true)
   */
  showTimestamps?: boolean;
}

/**
 * Console Output Component
 */
export const ConsoleOutput: React.FC<ConsoleOutputProps> = ({
  logs,
  maxHeight = '500px',
  onClear,
  showTimestamps = true,
}) => {
  const consoleRef = useRef<HTMLDivElement>(null);
  const shouldAutoScroll = useRef(true);

  /**
   * Auto-scroll to bottom when new logs arrive
   */
  useEffect(() => {
    if (consoleRef.current && shouldAutoScroll.current) {
      consoleRef.current.scrollTop = consoleRef.current.scrollHeight;
    }
  }, [logs]);

  /**
   * Track if user has scrolled away from bottom
   */
  const handleScroll = () => {
    if (consoleRef.current) {
      const { scrollTop, scrollHeight, clientHeight } = consoleRef.current;
      const isAtBottom = scrollHeight - scrollTop - clientHeight < 10;
      shouldAutoScroll.current = isAtBottom;
    }
  };

  /**
   * Format timestamp
   */
  const formatTimestamp = (date: Date): string => {
    return date.toLocaleTimeString('en-US', {
      hour12: false,
      hour: '2-digit',
      minute: '2-digit',
      second: '2-digit',
    });
  };

  /**
   * Get CSS class for log level
   */
  const getLogClass = (level: ConsoleLogEntry['level']): string => {
    return `log-entry log-${level}`;
  };

  /**
   * Get icon for log level
   */
  const getLogIcon = (level: ConsoleLogEntry['level']): string => {
    switch (level) {
      case 'success': return '✓';
      case 'error': return '✗';
      case 'warn': return '⚠';
      case 'info': return 'ℹ';
    }
  };

  return (
    <div className="console-output-container">
      <div className="console-header">
        <h3 className="console-title">Console Output</h3>
        {onClear && (
          <button
            onClick={onClear}
            className="clear-button"
            aria-label="Clear console"
            type="button"
          >
            Clear
          </button>
        )}
      </div>

      <div
        ref={consoleRef}
        className="console-content"
        style={{ maxHeight }}
        onScroll={handleScroll}
        role="log"
        aria-live="polite"
        aria-atomic="false"
        aria-label="Transpiler console output"
      >
        {logs.length === 0 ? (
          <div className="console-empty">
            <p>Console is empty. Upload a ZIP file and run transpilation to see output.</p>
          </div>
        ) : (
          logs.map((entry, index) => (
            <div
              key={index}
              className={getLogClass(entry.level)}
              role="status"
            >
              <span className="log-icon" aria-hidden="true">
                {getLogIcon(entry.level)}
              </span>
              {showTimestamps && (
                <span className="log-timestamp">
                  [{formatTimestamp(entry.timestamp)}]
                </span>
              )}
              <span className="log-message">{entry.message}</span>
            </div>
          ))
        )}
      </div>

      <style>{`
        .console-output-container {
          margin: 1.5rem 0;
          border: 1px solid #e5e7eb;
          border-radius: 8px;
          overflow: hidden;
          background: white;
        }

        .console-header {
          display: flex;
          justify-content: space-between;
          align-items: center;
          padding: 1rem 1.25rem;
          background: linear-gradient(135deg, #1e293b 0%, #334155 100%);
          border-bottom: 1px solid #e5e7eb;
        }

        .console-title {
          margin: 0;
          font-size: 1rem;
          font-weight: 600;
          color: white;
        }

        .clear-button {
          padding: 0.5rem 1rem;
          background: #475569;
          color: white;
          border: none;
          border-radius: 4px;
          font-size: 0.875rem;
          font-weight: 500;
          cursor: pointer;
          transition: background-color 0.2s ease;
        }

        .clear-button:hover {
          background: #64748b;
        }

        .clear-button:focus {
          outline: none;
          box-shadow: 0 0 0 3px rgba(100, 116, 139, 0.4);
        }

        .console-content {
          background: #1a1a1a;
          color: #00ff00;
          padding: 1.25rem;
          font-family: 'Courier New', 'Consolas', monospace;
          font-size: 0.875rem;
          line-height: 1.6;
          overflow-y: auto;
          white-space: pre-wrap;
          word-wrap: break-word;
        }

        .console-content::-webkit-scrollbar {
          width: 10px;
        }

        .console-content::-webkit-scrollbar-track {
          background: #2d2d2d;
        }

        .console-content::-webkit-scrollbar-thumb {
          background: #555;
          border-radius: 5px;
        }

        .console-content::-webkit-scrollbar-thumb:hover {
          background: #777;
        }

        .console-empty {
          color: #888;
          font-style: italic;
          text-align: center;
          padding: 2rem;
        }

        .log-entry {
          display: flex;
          align-items: flex-start;
          gap: 0.5rem;
          margin-bottom: 0.25rem;
          padding: 0.25rem 0;
        }

        .log-icon {
          flex-shrink: 0;
          font-weight: bold;
        }

        .log-timestamp {
          flex-shrink: 0;
          opacity: 0.7;
          font-size: 0.8rem;
        }

        .log-message {
          flex: 1;
          word-break: break-word;
        }

        .log-info {
          color: #74c0fc;
        }

        .log-success {
          color: #51cf66;
        }

        .log-error {
          color: #ff6b6b;
        }

        .log-warn {
          color: #ffd93d;
        }

        .log-info .log-icon {
          color: #74c0fc;
        }

        .log-success .log-icon {
          color: #51cf66;
        }

        .log-error .log-icon {
          color: #ff6b6b;
        }

        .log-warn .log-icon {
          color: #ffd93d;
        }

        @media (max-width: 768px) {
          .console-header {
            padding: 0.75rem 1rem;
          }

          .console-title {
            font-size: 0.9rem;
          }

          .clear-button {
            padding: 0.375rem 0.75rem;
            font-size: 0.8rem;
          }

          .console-content {
            padding: 1rem;
            font-size: 0.8rem;
          }

          .log-timestamp {
            font-size: 0.75rem;
          }
        }
      `}</style>
    </div>
  );
};
