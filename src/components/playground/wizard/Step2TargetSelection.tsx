import React from 'react';
import { WizardStepper } from './WizardStepper';
import type { WizardState, TranspileOptions } from './types';

interface Step2Props {
  state: WizardState;
  onTargetDirSelected: (dir: FileSystemDirectoryHandle) => void;
  onOptionsChanged: (options: TranspileOptions) => void;
}

export const Step2TargetSelection: React.FC<Step2Props> = ({
  state,
  onTargetDirSelected,
  onOptionsChanged
}) => {
  return (
    <>
      <WizardStepper />
      <div className="wizard-step-content">
        <h2>Step 2: Select Target Directory</h2>
        <p>Configure transpilation options (functionality coming in Phase 3)</p>
      </div>

      <style>{`
        .wizard-step-content {
          background-color: #fff;
          border: 1px solid #ddd;
          border-radius: 8px;
          padding: 2rem;
          min-height: 400px;
        }
      `}</style>
    </>
  );
};
