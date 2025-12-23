import React, { useState, useEffect } from 'react';
import { FileContentDisplay } from './FileContentDisplay';

/**
 * TabbedCodeViewer - Tab-based interface for switching between source and transpiled code
 *
 * @example
 * ```tsx
 * <TabbedCodeViewer
 *   sourceContent={cppCode}
 *   sourceFilename="example.cpp"
 *   transpileContent={cCode}
 *   transpileFilename="example.c"
 *   headerContent={hCode}
 *   headerFilename="example.h"
 *   defaultTab="cpp"
 * />
 * ```
 */

export interface TabbedCodeViewerProps {
  sourceContent: string;
  sourceFilename?: string;
  transpileContent: string;
  transpileFilename?: string;
  headerContent?: string;
  headerFilename?: string;
  defaultTab?: 'cpp' | 'h' | 'c';
}

export const TabbedCodeViewer: React.FC<TabbedCodeViewerProps> = ({
  sourceContent,
  sourceFilename,
  transpileContent,
  transpileFilename,
  headerContent,
  headerFilename,
  defaultTab = 'cpp',
}) => {
  const [activeTab, setActiveTab] = useState<'cpp' | 'h' | 'c'>(defaultTab);

  // Keyboard shortcuts: Alt+1 for C++, Alt+2 for Header, Alt+3 for C
  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      if (e.altKey && e.key === '1') {
        e.preventDefault();
        setActiveTab('cpp');
      } else if (e.altKey && e.key === '2' && headerContent) {
        e.preventDefault();
        setActiveTab('h');
      } else if (e.altKey && e.key === '3') {
        e.preventDefault();
        setActiveTab('c');
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [headerContent]);

  return (
    <div className="tabbed-code-viewer">
      {/* Tab Bar */}
      <div className="tab-bar">
        <button
          className={`tab ${activeTab === 'cpp' ? 'active' : ''}`}
          onClick={() => setActiveTab('cpp')}
          title="C++ Source (Alt+1)"
        >
          C++ Source
        </button>
        {headerContent && (
          <button
            className={`tab ${activeTab === 'h' ? 'active' : ''}`}
            onClick={() => setActiveTab('h')}
            title="Header File (.h) (Alt+2)"
          >
            Header (.h)
          </button>
        )}
        <button
          className={`tab ${activeTab === 'c' ? 'active' : ''}`}
          onClick={() => setActiveTab('c')}
          title={`C Implementation (Alt+${headerContent ? '3' : '2'})`}
        >
          Implementation (.c)
        </button>
      </div>

      {/* Content Pane */}
      <div className="tab-content">
        {activeTab === 'cpp' ? (
          <FileContentDisplay
            content={sourceContent}
            filename={sourceFilename}
            language="cpp"
            emptyMessage="No source file selected"
          />
        ) : activeTab === 'h' ? (
          <FileContentDisplay
            content={headerContent || ''}
            filename={headerFilename}
            language="c"
            emptyMessage="No header file generated"
          />
        ) : (
          <FileContentDisplay
            content={transpileContent}
            filename={transpileFilename}
            language="c"
            emptyMessage="No transpiled output"
          />
        )}
      </div>

      <style>{`
        .tabbed-code-viewer {
          height: 100%;
          width: 100%;
          display: flex;
          flex-direction: column;
          background-color: #fff;
          border: 1px solid #ddd;
          border-radius: 8px;
          overflow: hidden;
        }

        .tab-bar {
          display: flex;
          border-bottom: 2px solid #e0e0e0;
          background-color: #f5f5f5;
        }

        .tab {
          flex: 0 0 auto;
          padding: 0.75rem 1.5rem;
          background: none;
          border: none;
          border-bottom: 3px solid transparent;
          font-size: 0.95rem;
          font-weight: 500;
          color: #666;
          cursor: pointer;
          transition: all 0.2s;
          position: relative;
        }

        .tab:hover {
          background-color: #ebebeb;
          color: #333;
        }

        .tab.active {
          color: #4A90E2;
          border-bottom-color: #4A90E2;
          background-color: #fff;
        }

        .tab:focus {
          outline: 2px solid #4A90E2;
          outline-offset: -2px;
        }

        .tab-content {
          flex: 1;
          overflow: auto;
          padding: 0.5rem;
        }
      `}</style>
    </div>
  );
};
