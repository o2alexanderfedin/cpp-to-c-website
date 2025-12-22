import { describe, it, expect, vi } from 'vitest';
import { render, screen, fireEvent } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { ProgressIndicator } from './ProgressIndicator';

describe('ProgressIndicator', () => {
    describe('rendering', () => {
        it('should render the component', () => {
            render(<ProgressIndicator current={0} total={0} />);
            expect(screen.getByRole('progressbar')).toBeInTheDocument();
        });

        it('should display percentage correctly', () => {
            render(<ProgressIndicator current={5} total={10} />);
            expect(screen.getByText('50%')).toBeInTheDocument();
        });

        it('should display file count', () => {
            render(<ProgressIndicator current={5} total={10} />);
            expect(screen.getByText(/5.*10/)).toBeInTheDocument();
        });

        it('should show 0% when total is 0', () => {
            render(<ProgressIndicator current={0} total={0} />);
            expect(screen.getByText('0%')).toBeInTheDocument();
        });

        it('should show 100% when current equals total', () => {
            render(<ProgressIndicator current={10} total={10} />);
            expect(screen.getByText('100%')).toBeInTheDocument();
        });

        it('should not show current file when not provided', () => {
            render(<ProgressIndicator current={5} total={10} />);
            expect(screen.queryByTestId('current-file')).not.toBeInTheDocument();
        });

        it('should show current file when provided', () => {
            render(<ProgressIndicator current={5} total={10} currentFile="test.cpp" />);
            expect(screen.getByTestId('current-file')).toHaveTextContent('test.cpp');
        });
    });

    describe('progress bar', () => {
        it('should set correct aria-valuenow', () => {
            render(<ProgressIndicator current={5} total={10} />);
            const progressBar = screen.getByRole('progressbar');
            expect(progressBar).toHaveAttribute('aria-valuenow', '5');
        });

        it('should set correct aria-valuemin', () => {
            render(<ProgressIndicator current={5} total={10} />);
            const progressBar = screen.getByRole('progressbar');
            expect(progressBar).toHaveAttribute('aria-valuemin', '0');
        });

        it('should set correct aria-valuemax', () => {
            render(<ProgressIndicator current={5} total={10} />);
            const progressBar = screen.getByRole('progressbar');
            expect(progressBar).toHaveAttribute('aria-valuemax', '10');
        });

        it('should set correct width percentage', () => {
            render(<ProgressIndicator current={3} total={10} />);
            const progressBar = screen.getByTestId('progress-bar-fill');
            expect(progressBar).toHaveStyle({ width: '30%' });
        });

        it('should have 0% width when total is 0', () => {
            render(<ProgressIndicator current={0} total={0} />);
            const progressBar = screen.getByTestId('progress-bar-fill');
            expect(progressBar).toHaveStyle({ width: '0%' });
        });

        it('should have 100% width when complete', () => {
            render(<ProgressIndicator current={10} total={10} />);
            const progressBar = screen.getByTestId('progress-bar-fill');
            expect(progressBar).toHaveStyle({ width: '100%' });
        });
    });

    describe('cancel button', () => {
        it('should not render cancel button by default', () => {
            render(<ProgressIndicator current={5} total={10} />);
            expect(screen.queryByRole('button', { name: /cancel/i })).not.toBeInTheDocument();
        });

        it('should render cancel button when onCancel provided', () => {
            const onCancel = vi.fn();
            render(<ProgressIndicator current={5} total={10} onCancel={onCancel} />);
            expect(screen.getByRole('button', { name: /cancel/i })).toBeInTheDocument();
        });

        it('should call onCancel when cancel button clicked', async () => {
            const onCancel = vi.fn();
            render(<ProgressIndicator current={5} total={10} onCancel={onCancel} />);

            const cancelButton = screen.getByRole('button', { name: /cancel/i });
            await userEvent.click(cancelButton);

            expect(onCancel).toHaveBeenCalledTimes(1);
        });

        it('should disable cancel button when already cancelling', async () => {
            const onCancel = vi.fn();
            render(<ProgressIndicator current={5} total={10} onCancel={onCancel} isCancelling={true} />);

            const cancelButton = screen.getByRole('button', { name: /cancel/i });
            expect(cancelButton).toBeDisabled();
        });

        it('should show cancelling text when isCancelling is true', () => {
            const onCancel = vi.fn();
            render(<ProgressIndicator current={5} total={10} onCancel={onCancel} isCancelling={true} />);

            expect(screen.getByText(/cancelling/i)).toBeInTheDocument();
        });
    });

    describe('status message', () => {
        it('should show custom status message', () => {
            render(<ProgressIndicator current={5} total={10} statusMessage="Processing files..." />);
            expect(screen.getByText('Processing files...')).toBeInTheDocument();
        });

        it('should not show status message when not provided', () => {
            render(<ProgressIndicator current={5} total={10} />);
            expect(screen.queryByTestId('status-message')).not.toBeInTheDocument();
        });
    });

    describe('accessibility', () => {
        it('should have accessible name for progress bar', () => {
            render(<ProgressIndicator current={5} total={10} />);
            const progressBar = screen.getByRole('progressbar');
            expect(progressBar).toHaveAccessibleName();
        });

        it('should announce progress updates to screen readers', () => {
            render(<ProgressIndicator current={5} total={10} />);
            const progressBar = screen.getByRole('progressbar');
            expect(progressBar).toHaveAttribute('aria-label');
        });

        it('should have proper ARIA labels on cancel button', () => {
            const onCancel = vi.fn();
            render(<ProgressIndicator current={5} total={10} onCancel={onCancel} />);

            const cancelButton = screen.getByRole('button', { name: /cancel/i });
            expect(cancelButton).toHaveAccessibleName();
        });
    });

    describe('edge cases', () => {
        it('should handle negative current value', () => {
            render(<ProgressIndicator current={-1} total={10} />);
            expect(screen.getByText('0%')).toBeInTheDocument();
        });

        it('should handle current greater than total', () => {
            render(<ProgressIndicator current={15} total={10} />);
            expect(screen.getByText('100%')).toBeInTheDocument();
        });

        it('should handle very large numbers', () => {
            render(<ProgressIndicator current={500} total={1000} />);
            expect(screen.getByText('50%')).toBeInTheDocument();
        });

        it('should handle decimal percentages', () => {
            render(<ProgressIndicator current={1} total={3} />);
            expect(screen.getByText('33%')).toBeInTheDocument();
        });
    });

    describe('visual states', () => {
        it('should apply in-progress class when not complete', () => {
            render(<ProgressIndicator current={5} total={10} />);
            const container = screen.getByTestId('progress-indicator');
            expect(container).toHaveClass('in-progress');
        });

        it('should apply complete class when done', () => {
            render(<ProgressIndicator current={10} total={10} />);
            const container = screen.getByTestId('progress-indicator');
            expect(container).toHaveClass('complete');
        });

        it('should apply cancelling class when cancelling', () => {
            const onCancel = vi.fn();
            render(<ProgressIndicator current={5} total={10} onCancel={onCancel} isCancelling={true} />);
            const container = screen.getByTestId('progress-indicator');
            expect(container).toHaveClass('cancelling');
        });
    });
});
