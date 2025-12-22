import React from 'react';
import { WizardStepper } from './WizardStepper';
import { FileTreeView } from './FileTreeView';
import type { WizardState, FileInfo } from './types';

interface Step1Props {
  state: WizardState;
  onSourceDirSelected: (dir: FileSystemDirectoryHandle, files: FileInfo[]) => void;
}

// Mock data for testing FileTreeView
const mockFiles: FileInfo[] = [
  { path: 'main.cpp', name: 'main.cpp', handle: {} as any, size: 1024 },
  { path: 'src/core/engine.cpp', name: 'engine.cpp', handle: {} as any, size: 2048 },
  { path: 'src/core/renderer.cpp', name: 'renderer.cpp', handle: {} as any, size: 3072 },
  { path: 'src/utils/math.h', name: 'math.h', handle: {} as any, size: 512 },
  { path: 'src/utils/string.cpp', name: 'string.cpp', handle: {} as any, size: 768 },
  { path: 'tests/test_main.cpp', name: 'test_main.cpp', handle: {} as any, size: 1536 },
  { path: 'tests/core/test_engine.cpp', name: 'test_engine.cpp', handle: {} as any, size: 2560 },
  { path: 'include/common.h', name: 'common.h', handle: {} as any, size: 256 },
];

export const Step1SourceSelection: React.FC<Step1Props> = ({ state, onSourceDirSelected }) => {
  return (
    <>
      <WizardStepper />
      <div className="wizard-step-content">
        <h2>Step 1: Select Source Directory</h2>
        <p>Preview of FileTreeView component with mock data:</p>

        <FileTreeView files={mockFiles} height={400} />

        <p style={{ marginTop: '1rem', fontSize: '0.9rem', color: '#666' }}>
          <strong>Note:</strong> This is a preview of the FileTreeView component with mock data.
          Full directory selection functionality will be integrated in Phase 2, Plan 02-03.
        </p>
      </div>

      <style>{`
        .wizard-step-content {
          background-color: #fff;
          border: 1px solid #ddd;
          border-radius: 8px;
          padding: 2rem;
          min-height: 400px;
        }

        .wizard-step-content h2 {
          margin: 0 0 1rem 0;
          font-size: 1.75rem;
          color: #333;
        }
      `}</style>
    </>
  );
};
