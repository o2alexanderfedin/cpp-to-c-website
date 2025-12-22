import React from 'react';
import { useWizard } from 'react-use-wizard';

export interface WizardStepperProps {
    // No props needed - gets state from useWizard context
}

const STEPS = [
    { number: 1, label: 'Source' },
    { number: 2, label: 'Target' },
    { number: 3, label: 'Transpile' },
    { number: 4, label: 'Results' },
];

export const WizardStepper: React.FC<WizardStepperProps> = () => {
    const { activeStep, stepCount, previousStep, nextStep, isFirstStep, isLastStep } = useWizard();

    return (
        <div className="wizard-stepper">
            <div className="stepper-steps">
                {STEPS.map((step, index) => {
                    const isActive = index === activeStep;
                    const isCompleted = index < activeStep;
                    const stepClass = isActive ? 'active' : isCompleted ? 'completed' : 'inactive';

                    return (
                        <React.Fragment key={step.number}>
                            <div className={`step ${stepClass}`}>
                                <div className="step-circle">
                                    {isCompleted ? (
                                        <span className="checkmark">✓</span>
                                    ) : (
                                        <span className="step-number">{step.number}</span>
                                    )}
                                </div>
                                <div className="step-label">{step.label}</div>
                            </div>
                            {index < STEPS.length - 1 && (
                                <div className={`step-connector ${isCompleted ? 'completed' : ''}`} />
                            )}
                        </React.Fragment>
                    );
                })}
            </div>

            <div className="stepper-controls">
                <button
                    onClick={previousStep}
                    disabled={isFirstStep}
                    className="btn-back"
                    aria-label="Go to previous step"
                >
                    Back
                </button>
                <button
                    onClick={nextStep}
                    disabled={isLastStep}
                    className="btn-next"
                    aria-label="Go to next step"
                >
                    Next
                </button>
            </div>

            <style>{`
                .wizard-stepper {
                    padding: 2rem;
                    background-color: #fff;
                    border: 1px solid #ddd;
                    border-radius: 8px;
                    margin-bottom: 2rem;
                }

                .stepper-steps {
                    display: flex;
                    align-items: center;
                    justify-content: center;
                    margin-bottom: 2rem;
                    gap: 0;
                }

                .step {
                    display: flex;
                    flex-direction: column;
                    align-items: center;
                    position: relative;
                }

                .step-circle {
                    width: 48px;
                    height: 48px;
                    border-radius: 50%;
                    display: flex;
                    align-items: center;
                    justify-content: center;
                    font-weight: 600;
                    font-size: 1.125rem;
                    transition: all 0.3s ease;
                    border: 2px solid;
                }

                .step.inactive .step-circle {
                    background-color: #f5f5f5;
                    border-color: #ccc;
                    color: #999;
                }

                .step.active .step-circle {
                    background-color: #2196f3;
                    border-color: #2196f3;
                    color: white;
                }

                .step.completed .step-circle {
                    background-color: #4caf50;
                    border-color: #4caf50;
                    color: white;
                }

                .checkmark {
                    font-size: 1.5rem;
                    line-height: 1;
                }

                .step-number {
                    line-height: 1;
                }

                .step-label {
                    margin-top: 0.5rem;
                    font-size: 0.875rem;
                    font-weight: 500;
                    text-align: center;
                    min-width: 80px;
                }

                .step.inactive .step-label {
                    color: #999;
                }

                .step.active .step-label {
                    color: #2196f3;
                }

                .step.completed .step-label {
                    color: #4caf50;
                }

                .step-connector {
                    flex: 1;
                    height: 2px;
                    background-color: #ccc;
                    min-width: 40px;
                    margin: 0 8px;
                    margin-bottom: 28px;
                    transition: background-color 0.3s ease;
                }

                .step-connector.completed {
                    background-color: #4caf50;
                }

                .stepper-controls {
                    display: flex;
                    gap: 1rem;
                    justify-content: center;
                }

                .stepper-controls button {
                    padding: 0.75rem 2rem;
                    font-size: 1rem;
                    font-weight: 500;
                    border: none;
                    border-radius: 4px;
                    cursor: pointer;
                    transition: all 0.2s;
                    min-width: 120px;
                }

                .btn-back {
                    background-color: #f5f5f5;
                    color: #333;
                    border: 1px solid #ddd;
                }

                .btn-back:hover:not(:disabled) {
                    background-color: #e0e0e0;
                }

                .btn-next {
                    background-color: #2196f3;
                    color: white;
                }

                .btn-next:hover:not(:disabled) {
                    background-color: #1976d2;
                }

                .stepper-controls button:disabled {
                    opacity: 0.5;
                    cursor: not-allowed;
                }

                .stepper-controls button:focus {
                    outline: 2px solid #2196f3;
                    outline-offset: 2px;
                }

                @media (max-width: 640px) {
                    .wizard-stepper {
                        padding: 1rem;
                    }

                    .stepper-steps {
                        flex-direction: column;
                        gap: 1rem;
                    }

                    .step-connector {
                        display: none;
                    }

                    .step {
                        flex-direction: row;
                        gap: 1rem;
                        width: 100%;
                    }

                    .step-label {
                        margin-top: 0;
                        text-align: left;
                    }

                    .stepper-controls {
                        flex-direction: column;
                    }

                    .stepper-controls button {
                        width: 100%;
                    }
                }
            `}</style>
        </div>
    );
};
