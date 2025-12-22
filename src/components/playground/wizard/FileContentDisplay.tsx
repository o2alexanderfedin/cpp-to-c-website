import React from 'react';
import { SyntaxHighlighter } from './SyntaxHighlighter';

/**
 * FileContentDisplay - Displays file content with line numbers and optional syntax highlighting
 *
 * @example Basic usage
 * ```tsx
 * <FileContentDisplay
 *   content={sourceCode}
 *   filename="main.cpp"
 *   language="cpp"
 * />
 * ```
 */

export interface FileContentDisplayProps {
  content: string;
  filename?: string;
  language?: 'cpp' | 'c';
  lineNumbers?: boolean;
  emptyMessage?: string;
  enableSyntaxHighlighting?: boolean; // NEW: toggle syntax highlighting
}

export const FileContentDisplay: React.FC<FileContentDisplayProps> = ({
  content,
  filename,
  language = 'cpp',
  lineNumbers = true,
  emptyMessage = 'No file selected',
  enableSyntaxHighlighting = true, // NEW: enabled by default
}) => {
  // Split content into lines for plain text rendering
  const lines = React.useMemo(() => content.split('\n'), [content]);

  // Empty state
  if (!content || content.trim() === '') {
    return (
      <div className="file-content-empty">
        <p>{emptyMessage}</p>

        <style>{`
          .file-content-empty {
            display: flex;
            align-items: center;
            justify-content: center;
            height: 100%;
            color: #999;
            font-size: 0.95rem;
            font-style: italic;
          }
        `}</style>
      </div>
    );
  }

  return (
    <div className="file-content-display">
      {/* Header with filename */}
      {filename && (
        <div className="file-content-header">
          <span className="file-content-filename">{filename}</span>
          <span className="file-content-language">{language.toUpperCase()}</span>
        </div>
      )}

      {/* Content area - NEW: use SyntaxHighlighter if enabled */}
      <div className="file-content-wrapper">
        {enableSyntaxHighlighting ? (
          <SyntaxHighlighter
            code={content}
            language={language}
            lineNumbers={lineNumbers}
          />
        ) : (
          // Fallback: plain text rendering (old implementation)
          <pre className="file-content-code">
            {lineNumbers && (
              <div className="line-numbers">
                {lines.map((_, index) => (
                  <div key={index} className="line-number">
                    {index + 1}
                  </div>
                ))}
              </div>
            )}
            <div className="code-lines">
              <code>{content}</code>
            </div>
          </pre>
        )}
      </div>

      <style>{`
        .file-content-display {
          display: flex;
          flex-direction: column;
          height: 100%;
          background-color: #fafafa;
          border-radius: 4px;
          overflow: hidden;
        }

        .file-content-header {
          display: flex;
          justify-content: space-between;
          align-items: center;
          padding: 0.75rem 1rem;
          background-color: #f5f5f5;
          border-bottom: 1px solid #e0e0e0;
        }

        .file-content-filename {
          font-size: 0.9rem;
          font-weight: 600;
          color: #333;
        }

        .file-content-language {
          font-size: 0.75rem;
          font-weight: 600;
          color: #666;
          background-color: #e0e0e0;
          padding: 0.25rem 0.5rem;
          border-radius: 3px;
        }

        .file-content-wrapper {
          flex: 1;
          overflow: auto;
          background-color: #fff;
        }

        .file-content-code {
          display: flex;
          margin: 0;
          padding: 0;
          font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
          font-size: 0.9rem;
          line-height: 1.6;
          min-height: 100%;
        }

        .line-numbers {
          display: flex;
          flex-direction: column;
          background-color: #f5f5f5;
          color: #999;
          padding: 1rem 0.75rem;
          text-align: right;
          user-select: none;
          border-right: 1px solid #e0e0e0;
          min-width: 3rem;
        }

        .line-number {
          height: 1.6em;
        }

        .code-lines {
          flex: 1;
          padding: 1rem;
          overflow-x: auto;
        }

        .code-lines code {
          display: block;
          white-space: pre;
          font-family: inherit;
          font-size: inherit;
          line-height: inherit;
        }
      `}</style>
    </div>
  );
};
