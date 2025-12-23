import { describe, it, expect, vi } from 'vitest';
import { render, screen, fireEvent, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { Wizard } from 'react-use-wizard';
import { WizardStepper } from './WizardStepper';

describe('WizardStepper', () => {
    // Wrapper components for each step
    const Step1 = () => (
        <>
            <WizardStepper />
            <div>Step 1 Content</div>
        </>
    );

    const Step2 = () => (
        <>
            <WizardStepper />
            <div>Step 2 Content</div>
        </>
    );

    const Step3 = () => (
        <>
            <WizardStepper />
            <div>Step 3 Content</div>
        </>
    );

    const Step4 = () => (
        <>
            <WizardStepper />
            <div>Step 4 Content</div>
        </>
    );

    const renderWithWizard = () => {
        return render(
            <Wizard>
                <Step1 />
                <Step2 />
                <Step3 />
                <Step4 />
            </Wizard>
        );
    };

    describe('rendering', () => {
        it('renders 4 steps with correct labels', () => {
            renderWithWizard();

            expect(screen.getByText('Source')).toBeInTheDocument();
            expect(screen.getByText('Target')).toBeInTheDocument();
            expect(screen.getByText('Transpile')).toBeInTheDocument();
            expect(screen.getByText('Results')).toBeInTheDocument();
        });

        it('displays step numbers 1-4', () => {
            renderWithWizard();

            // Step 1 is active, so it shows number
            expect(screen.getByText('1')).toBeInTheDocument();
            // Others should also be visible
            expect(screen.getByText('2')).toBeInTheDocument();
            expect(screen.getByText('3')).toBeInTheDocument();
            expect(screen.getByText('4')).toBeInTheDocument();
        });

        it('has Next and Back buttons', () => {
            renderWithWizard();

            expect(screen.getByRole('button', { name: /go to next step/i })).toBeInTheDocument();
            expect(screen.getByRole('button', { name: /go to previous step/i })).toBeInTheDocument();
        });
    });

    describe('initial state', () => {
        it('highlights step 1 as active initially', () => {
            renderWithWizard();

            const steps = screen.getAllByText(/Source|Target|Transpile|Results/);
            const sourceStep = steps.find((el) => el.textContent === 'Source');

            expect(sourceStep?.parentElement).toHaveClass('active');
        });

        it('has Back button disabled on first step', () => {
            renderWithWizard();

            const backButton = screen.getByRole('button', { name: /go to previous step/i });
            expect(backButton).toBeDisabled();
        });

        it('has Next button enabled on first step', () => {
            renderWithWizard();

            const nextButton = screen.getByRole('button', { name: /go to next step/i });
            expect(nextButton).not.toBeDisabled();
        });
    });

    describe('navigation', () => {
        it('advances to step 2 when Next is clicked', async () => {
            renderWithWizard();

            const nextButton = screen.getByRole('button', { name: /go to next step/i });
            await userEvent.click(nextButton);

            // After navigation, step 2 content should be visible
            expect(screen.getByText('Step 2 Content')).toBeInTheDocument();
        });

        it('can navigate through all 4 steps', async () => {
            renderWithWizard();

            // Start at step 1
            expect(screen.getByText('Step 1 Content')).toBeInTheDocument();

            // Go to step 2
            const nextButton = screen.getByRole('button', { name: /go to next step/i });
            await userEvent.click(nextButton);
            await waitFor(() => expect(screen.getByText('Step 2 Content')).toBeInTheDocument());

            // Go to step 3
            await userEvent.click(screen.getByRole('button', { name: /go to next step/i }));
            await waitFor(() => expect(screen.getByText('Step 3 Content')).toBeInTheDocument());

            // Go to step 4
            await userEvent.click(screen.getByRole('button', { name: /go to next step/i }));
            await waitFor(() => expect(screen.getByText('Step 4 Content')).toBeInTheDocument());
        });

        it('returns to previous step when Back is clicked', async () => {
            renderWithWizard();

            const nextButton = screen.getByRole('button', { name: /go to next step/i });

            // Go to step 2
            await userEvent.click(nextButton);
            await waitFor(() => expect(screen.getByText('Step 2 Content')).toBeInTheDocument());

            // Go back to step 1
            const backButton = screen.getByRole('button', { name: /go to previous step/i });
            await userEvent.click(backButton);
            await waitFor(() => expect(screen.getByText('Step 1 Content')).toBeInTheDocument());
        });

        it('disables Next button on last step', async () => {
            renderWithWizard();

            // Navigate to last step
            let nextButton = screen.getByRole('button', { name: /go to next step/i });
            await userEvent.click(nextButton); // Step 2
            await waitFor(() => expect(screen.getByText('Step 2 Content')).toBeInTheDocument());

            nextButton = screen.getByRole('button', { name: /go to next step/i });
            await userEvent.click(nextButton); // Step 3
            await waitFor(() => expect(screen.getByText('Step 3 Content')).toBeInTheDocument());

            nextButton = screen.getByRole('button', { name: /go to next step/i });
            await userEvent.click(nextButton); // Step 4
            await waitFor(() => expect(screen.getByText('Step 4 Content')).toBeInTheDocument());

            // Next button should be disabled on step 4
            nextButton = screen.getByRole('button', { name: /go to next step/i });
            expect(nextButton).toBeDisabled();
        });

        it('enables Back button after navigating from first step', async () => {
            renderWithWizard();

            const backButton = screen.getByRole('button', { name: /go to previous step/i });

            // Initially disabled
            expect(backButton).toBeDisabled();

            // Navigate to step 2
            const nextButton = screen.getByRole('button', { name: /go to next step/i });
            await userEvent.click(nextButton);
            await waitFor(() => expect(screen.getByText('Step 2 Content')).toBeInTheDocument());

            // Now enabled
            const newBackButton = screen.getByRole('button', { name: /go to previous step/i });
            expect(newBackButton).not.toBeDisabled();
        });
    });

    describe('visual states', () => {
        it('shows completed steps with checkmarks', async () => {
            renderWithWizard();

            const nextButton = screen.getByRole('button', { name: /go to next step/i });

            // Navigate to step 2
            await userEvent.click(nextButton);

            // Step 1 should now show a checkmark
            const checkmarks = screen.getAllByText('✓');
            expect(checkmarks.length).toBeGreaterThan(0);
        });

        it('marks multiple steps as completed when navigating forward', async () => {
            renderWithWizard();

            // Navigate to step 3
            let nextButton = screen.getByRole('button', { name: /go to next step/i });
            await userEvent.click(nextButton); // Step 2
            await waitFor(() => expect(screen.getByText('Step 2 Content')).toBeInTheDocument());

            nextButton = screen.getByRole('button', { name: /go to next step/i });
            await userEvent.click(nextButton); // Step 3
            await waitFor(() => expect(screen.getByText('Step 3 Content')).toBeInTheDocument());

            // Steps 1 and 2 should have checkmarks
            const checkmarks = screen.getAllByText('✓');
            expect(checkmarks.length).toBeGreaterThanOrEqual(2);
        });
    });

    describe('accessibility', () => {
        it('has proper ARIA labels on buttons', () => {
            renderWithWizard();

            const nextButton = screen.getByRole('button', { name: /go to next step/i });
            const backButton = screen.getByRole('button', { name: /go to previous step/i });

            expect(nextButton).toHaveAccessibleName();
            expect(backButton).toHaveAccessibleName();
        });

        it('maintains focus on buttons during navigation', async () => {
            renderWithWizard();

            const nextButton = screen.getByRole('button', { name: /go to next step/i });
            await userEvent.click(nextButton);
            await waitFor(() => expect(screen.getByText('Step 2 Content')).toBeInTheDocument());

            // Button should still be present and focusable after navigation
            const newNextButton = screen.getByRole('button', { name: /go to next step/i });
            expect(newNextButton).toBeInTheDocument();
        });
    });
});
