import React from 'react';
import { WizardStepper } from './WizardStepper';
import type { WizardState, FileInfo } from './types';

interface Step1Props {
  state: WizardState;
  onSourceDirSelected: (dir: FileSystemDirectoryHandle, files: FileInfo[]) => void;
}

export const Step1SourceSelection: React.FC<Step1Props> = ({ state, onSourceDirSelected }) => {
  return (
    <>
      <WizardStepper />
      <div className="wizard-step-content">
        <h2>Step 1: Select Source Directory</h2>
        <p>Select your C++ source directory (functionality coming in Phase 2)</p>
        {/* DirectorySelector will be integrated in Phase 2 */}
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
