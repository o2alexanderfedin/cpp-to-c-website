import React from 'react';
import { Wizard } from 'react-use-wizard';
import { useWizardState } from './useWizardState';
import { Step1SourceSelection } from './Step1SourceSelection';
import { Step2TargetSelection } from './Step2TargetSelection';
import { Step3Transpilation } from './Step3Transpilation';
import { Step4Results } from './Step4Results';

export const PlaygroundWizard: React.FC = () => {
  const { state, handlers, validation } = useWizardState();

  return (
    <div className="playground-wizard">
      <Wizard>
        <Step1SourceSelection
          state={state}
          onSourceDirSelected={handlers.setSourceDir}
        />
        <Step2TargetSelection
          state={state}
          onTargetDirSelected={handlers.setTargetDir}
          onOptionsChanged={handlers.setTargetOptions}
        />
        <Step3Transpilation
          state={state}
          onStartTranspilation={handlers.startTranspilation}
          onPauseTranspilation={handlers.stopTranspilation}
          onCancelTranspilation={handlers.stopTranspilation}
        />
        <Step4Results
          state={state}
          onFileSelected={handlers.setSelectedPreviewFile}
          onDownload={() => {/* TODO: Implement in Phase 4 */}}
        />
      </Wizard>

      <style>{`
        .playground-wizard {
          max-width: 1200px;
          margin: 0 auto;
          padding: 2rem;
        }

        @media (max-width: 768px) {
          .playground-wizard {
            padding: 1rem;
          }
        }
      `}</style>
    </div>
  );
};
