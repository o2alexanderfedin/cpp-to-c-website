import React from 'react';
import { Wizard } from 'react-use-wizard';
import { WizardStepper } from './WizardStepper';

// Step components
const Step1: React.FC = () => (
    <>
        <WizardStepper />
        <div className="wizard-step-content">
            <div className="step-placeholder">
                <h2>Step 1: Source Selection</h2>
                <p>Select your C++ source directory (placeholder)</p>
            </div>
        </div>
    </>
);

const Step2: React.FC = () => (
    <>
        <WizardStepper />
        <div className="wizard-step-content">
            <div className="step-placeholder">
                <h2>Step 2: Target Selection</h2>
                <p>Configure transpilation target (placeholder)</p>
            </div>
        </div>
    </>
);

const Step3: React.FC = () => (
    <>
        <WizardStepper />
        <div className="wizard-step-content">
            <div className="step-placeholder">
                <h2>Step 3: Transpilation</h2>
                <p>Transpile your code (placeholder)</p>
            </div>
        </div>
    </>
);

const Step4: React.FC = () => (
    <>
        <WizardStepper />
        <div className="wizard-step-content">
            <div className="step-placeholder">
                <h2>Step 4: Results</h2>
                <p>View transpilation results (placeholder)</p>
            </div>
        </div>
    </>
);

export const PlaygroundWizard: React.FC = () => {
    return (
        <div className="playground-wizard">
            <Wizard>
                <Step1 />
                <Step2 />
                <Step3 />
                <Step4 />
            </Wizard>

            <style>{`
                .playground-wizard {
                    max-width: 1200px;
                    margin: 0 auto;
                    padding: 2rem;
                }

                .wizard-step-content {
                    background-color: #fff;
                    border: 1px solid #ddd;
                    border-radius: 8px;
                    padding: 2rem;
                    min-height: 400px;
                }

                .step-placeholder {
                    text-align: center;
                    padding: 3rem 1rem;
                }

                .step-placeholder h2 {
                    margin: 0 0 1rem 0;
                    font-size: 1.75rem;
                    color: #333;
                }

                .step-placeholder p {
                    margin: 0;
                    color: #666;
                    font-size: 1.125rem;
                }

                @media (max-width: 768px) {
                    .playground-wizard {
                        padding: 1rem;
                    }

                    .wizard-step-content {
                        padding: 1rem;
                        min-height: 300px;
                    }

                    .step-placeholder {
                        padding: 2rem 1rem;
                    }

                    .step-placeholder h2 {
                        font-size: 1.5rem;
                    }

                    .step-placeholder p {
                        font-size: 1rem;
                    }
                }
            `}</style>
        </div>
    );
};
