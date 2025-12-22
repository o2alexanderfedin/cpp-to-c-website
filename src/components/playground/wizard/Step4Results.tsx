import React from 'react';
import { WizardStepper } from './WizardStepper';
import type { WizardState } from './types';

interface Step4Props {
  state: WizardState;
  onFileSelected: (filePath: string) => void;
  onDownload: () => void;
}

export const Step4Results: React.FC<Step4Props> = ({
  state,
  onFileSelected,
  onDownload
}) => {
  return (
    <>
      <WizardStepper />
      <div className="wizard-step-content">
        <h2>Step 4: Results</h2>
        <p>View and download results (functionality coming in Phase 4)</p>
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
