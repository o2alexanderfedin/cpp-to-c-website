import React from 'react';
import { Highlight, themes } from 'prism-react-renderer';

/**
 * SyntaxHighlighter - Async syntax highlighting for C++ and C code
 *
 * Uses prism-react-renderer for lightweight, fast syntax highlighting.
 * Automatically defers rendering for large files (>1000 lines) to prevent UI blocking.
 *
 * @example
 * ```tsx
 * <SyntaxHighlighter
 *   code={sourceCode}
 *   language="cpp"
 *   lineNumbers={true}
 * />
 * ```
 *
 * @example Highlight specific lines
 * ```tsx
 * <SyntaxHighlighter
 *   code={code}
 *   language="c"
 *   highlightLines={[5, 10, 15]}
 * />
 * ```
 */
export interface SyntaxHighlighterProps {
  code: string;
  language: 'cpp' | 'c';
  lineNumbers?: boolean;
  showLineNumbers?: boolean; // Alias for lineNumbers
  highlightLines?: number[]; // Optional: highlight specific lines
}

export const SyntaxHighlighter: React.FC<SyntaxHighlighterProps> = ({
  code,
  language,
  lineNumbers,
  showLineNumbers,
  highlightLines = [],
}) => {
  // Default to true only if both are undefined
  const displayLineNumbers = lineNumbers !== undefined
    ? lineNumbers
    : showLineNumbers !== undefined
    ? showLineNumbers
    : true;

  // Use async rendering for large files (>1000 lines)
  const [isReady, setIsReady] = React.useState(code.split('\n').length < 1000);

  React.useEffect(() => {
    if (!isReady) {
      // Defer rendering to next frame to prevent blocking
      const timer = setTimeout(() => setIsReady(true), 0);
      return () => clearTimeout(timer);
    }
  }, [isReady, code]);

  // Loading state for large files
  if (!isReady) {
    return (
      <div className="syntax-loading">
        <p>Preparing syntax highlighting...</p>
        <style>{`
          .syntax-loading {
            padding: 2rem;
            text-align: center;
            color: #666;
            font-style: italic;
          }
        `}</style>
      </div>
    );
  }

  return (
    <Highlight
      theme={themes.github} // Clean light theme
      code={code}
      language={language}
    >
      {({ className, tokens, getLineProps, getTokenProps }) => (
        <div className="syntax-highlighter">
          <pre className={className}>
            {displayLineNumbers && (
              <div className="syntax-line-numbers">
                {tokens.map((line, i) => (
                  <div
                    key={i}
                    className={`syntax-line-number ${
                      highlightLines.includes(i + 1) ? 'highlighted' : ''
                    }`}
                  >
                    {i + 1}
                  </div>
                ))}
              </div>
            )}
            <div className="syntax-code-lines">
              {tokens.map((line, i) => (
                <div
                  key={i}
                  {...getLineProps({ line })}
                  className={`syntax-code-line ${
                    highlightLines.includes(i + 1) ? 'highlighted' : ''
                  }`}
                >
                  {line.map((token, key) => (
                    <span key={key} {...getTokenProps({ token })} />
                  ))}
                </div>
              ))}
            </div>
          </pre>

          <style>{`
            .syntax-highlighter {
              height: 100%;
              overflow: auto;
            }

            .syntax-highlighter pre {
              display: flex;
              margin: 0;
              padding: 0;
              font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
              font-size: 0.9rem;
              line-height: 1.6;
              min-height: 100%;
              overflow: visible;
              background-color: #f6f8fa;
              color: #24292f;
            }

            .syntax-line-numbers {
              display: flex;
              flex-direction: column;
              background-color: #f6f8fa;
              color: #57606a;
              padding: 1rem 0.75rem;
              text-align: right;
              user-select: none;
              border-right: 1px solid #d0d7de;
              min-width: 3rem;
            }

            .syntax-line-number {
              height: 1.6em;
            }

            .syntax-line-number.highlighted {
              background-color: #fff8c5;
              color: #24292f;
              font-weight: 600;
            }

            .syntax-code-lines {
              flex: 1;
              padding: 1rem;
            }

            .syntax-code-line {
              height: 1.6em;
            }

            .syntax-code-line.highlighted {
              background-color: #fff8c5;
              display: block;
              margin-left: -1rem;
              margin-right: -1rem;
              padding-left: 1rem;
              padding-right: 1rem;
            }
          `}</style>
        </div>
      )}
    </Highlight>
  );
};
