import React from 'react';
import { Panel, Group, Separator } from 'react-resizable-panels';
import { FileContentDisplay } from './FileContentDisplay';

/**
 * DualPaneViewer - Side-by-side comparison of source and transpiled code
 *
 * @example
 * ```tsx
 * <DualPaneViewer
 *   sourceContent={cppCode}
 *   sourceFilename="example.cpp"
 *   transpileContent={cCode}
 *   transpileFilename="example.c"
 *   defaultLayout={[50, 50]}
 * />
 * ```
 */

export interface DualPaneViewerProps {
  sourceContent: string;
  sourceFilename?: string;
  transpileContent: string;
  transpileFilename?: string;
  defaultLayout?: number[]; // [leftPercent, rightPercent]
}

export const DualPaneViewer: React.FC<DualPaneViewerProps> = ({
  sourceContent,
  sourceFilename,
  transpileContent,
  transpileFilename,
  defaultLayout = [50, 50],
}) => {
  return (
    <div className="dual-pane-viewer">
      <Group orientation="horizontal">
        {/* Left pane: Source C++ */}
        <Panel defaultSize={defaultLayout[0]} minSize={20}>
          <div className="pane-container">
            <FileContentDisplay
              content={sourceContent}
              filename={sourceFilename}
              language="cpp"
              emptyMessage="No source file selected"
            />
          </div>
        </Panel>

        {/* Resize handle */}
        <Separator className="resize-handle">
          <div className="resize-handle-line" />
        </Separator>

        {/* Right pane: Transpiled C */}
        <Panel defaultSize={defaultLayout[1]} minSize={20}>
          <div className="pane-container">
            <FileContentDisplay
              content={transpileContent}
              filename={transpileFilename}
              language="c"
              emptyMessage="No transpiled output"
            />
          </div>
        </Panel>
      </Group>

      <style>{`
        .dual-pane-viewer {
          height: 100%;
          width: 100%;
          background-color: #fff;
          border: 1px solid #ddd;
          border-radius: 8px;
          overflow: hidden;
        }

        .pane-container {
          height: 100%;
          padding: 0.5rem;
        }

        .resize-handle {
          position: relative;
          display: flex;
          align-items: center;
          justify-content: center;
          background-color: #f0f0f0;
          cursor: col-resize;
          transition: background-color 0.2s;
          width: 8px;
        }

        .resize-handle:hover {
          background-color: #4A90E2;
        }

        .resize-handle:active {
          background-color: #1976d2;
        }

        .resize-handle-line {
          width: 2px;
          height: 100%;
          background-color: #ddd;
          pointer-events: none;
        }

        .resize-handle:hover .resize-handle-line {
          background-color: #fff;
        }
      `}</style>
    </div>
  );
};
