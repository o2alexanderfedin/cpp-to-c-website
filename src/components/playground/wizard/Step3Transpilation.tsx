import React from 'react';
import { WizardStepper } from './WizardStepper';
import type { WizardState } from './types';

interface Step3Props {
  state: WizardState;
  onStartTranspilation: () => void;
  onPauseTranspilation: () => void;
  onCancelTranspilation: () => void;
}

export const Step3Transpilation: React.FC<Step3Props> = ({
  state,
  onStartTranspilation,
  onPauseTranspilation,
  onCancelTranspilation
}) => {
  return (
    <>
      <WizardStepper />
      <div className="wizard-step-content">
        <h2>Step 3: Transpilation</h2>
        <p>Transpile with real-time progress (functionality coming in Phase 3)</p>
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
