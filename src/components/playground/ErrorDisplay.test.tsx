import { describe, it, expect, vi } from 'vitest';
import { render, screen, fireEvent } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { ErrorDisplay } from './ErrorDisplay';
import type { TranspileError } from '../../features/transpile/types';

describe('ErrorDisplay', () => {
    const mockErrors: TranspileError[] = [
        {
            filePath: '/src/main.cpp',
            message: 'Syntax error: expected ;',
            line: 42,
            column: 10,
        },
        {
            filePath: '/src/utils.cpp',
            message: 'Undefined reference to function',
            line: 15,
        },
        {
            filePath: '/src/parser.cpp',
            message: 'Template instantiation failed',
        },
    ];

    describe('rendering', () => {
        it('should render the component', () => {
            render(<ErrorDisplay errors={[]} />);
            expect(screen.getByRole('region', { name: /error list/i })).toBeInTheDocument();
        });

        it('should show no errors message when empty', () => {
            render(<ErrorDisplay errors={[]} />);
            expect(screen.getByText(/no errors detected/i)).toBeInTheDocument();
        });

        it('should display error count', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            expect(screen.getByText(/3 errors/i)).toBeInTheDocument();
        });

        it('should display singular error count', () => {
            render(<ErrorDisplay errors={[mockErrors[0]]} />);
            expect(screen.getByText(/1 error/i)).toBeInTheDocument();
        });

        it('should list all error file paths', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            expect(screen.getByText('/src/main.cpp')).toBeInTheDocument();
            expect(screen.getByText('/src/utils.cpp')).toBeInTheDocument();
            expect(screen.getByText('/src/parser.cpp')).toBeInTheDocument();
        });

        it('should display error messages', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            expect(screen.getByText('Syntax error: expected ;')).toBeInTheDocument();
            expect(screen.getByText('Undefined reference to function')).toBeInTheDocument();
        });

        it('should show line and column when available', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            expect(screen.getByText(/line 42, column 10/i)).toBeInTheDocument();
        });

        it('should show line only when column not available', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            expect(screen.getByText(/line 15/i)).toBeInTheDocument();
        });

        it('should not show line/column when not available', () => {
            render(<ErrorDisplay errors={[mockErrors[2]]} />);
            expect(screen.queryByText(/line/i)).not.toBeInTheDocument();
        });
    });

    describe('expandable details', () => {
        it('should collapse error details by default', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            const firstError = mockErrors[0];
            const details = screen.queryByText(firstError.message);
            // Message should be hidden initially
            expect(details?.closest('.error-details')).toHaveClass('collapsed');
        });

        it('should expand error details on click', async () => {
            render(<ErrorDisplay errors={mockErrors} />);

            const firstErrorItem = screen.getByText('/src/main.cpp').closest('.error-item');
            expect(firstErrorItem).toBeTruthy();

            await userEvent.click(firstErrorItem!);

            const details = screen.getByText('Syntax error: expected ;').closest('.error-details');
            expect(details).not.toHaveClass('collapsed');
        });

        it('should collapse expanded details on second click', async () => {
            render(<ErrorDisplay errors={mockErrors} />);

            const firstErrorItem = screen.getByText('/src/main.cpp').closest('.error-item');
            expect(firstErrorItem).toBeTruthy();

            // Expand
            await userEvent.click(firstErrorItem!);
            // Collapse
            await userEvent.click(firstErrorItem!);

            const details = screen.getByText('Syntax error: expected ;').closest('.error-details');
            expect(details).toHaveClass('collapsed');
        });

        it('should show expand/collapse indicator', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            const indicators = screen.getAllByTestId('expand-indicator');
            expect(indicators).toHaveLength(3);
        });
    });

    describe('copy to clipboard', () => {
        it('should render copy button when onCopy provided', () => {
            const onCopy = vi.fn();
            render(<ErrorDisplay errors={mockErrors} onCopy={onCopy} />);
            expect(screen.getByRole('button', { name: /copy.*clipboard/i })).toBeInTheDocument();
        });

        it('should not render copy button when onCopy not provided', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            expect(screen.queryByRole('button', { name: /copy.*clipboard/i })).not.toBeInTheDocument();
        });

        it('should call onCopy with formatted errors', async () => {
            const onCopy = vi.fn();
            render(<ErrorDisplay errors={mockErrors} onCopy={onCopy} />);

            const copyButton = screen.getByRole('button', { name: /copy.*clipboard/i });
            await userEvent.click(copyButton);

            expect(onCopy).toHaveBeenCalledTimes(1);
            const copiedText = onCopy.mock.calls[0][0];
            expect(copiedText).toContain('/src/main.cpp');
            expect(copiedText).toContain('Syntax error: expected ;');
        });

        it('should show confirmation after copy', async () => {
            const onCopy = vi.fn();
            render(<ErrorDisplay errors={mockErrors} onCopy={onCopy} />);

            const copyButton = screen.getByRole('button', { name: /copy.*clipboard/i });
            await userEvent.click(copyButton);

            expect(screen.getByText(/copied/i)).toBeInTheDocument();
        });
    });

    describe('filtering', () => {
        it('should filter errors by search term', async () => {
            render(<ErrorDisplay errors={mockErrors} showSearch={true} />);

            const searchInput = screen.getByRole('textbox', { name: /search/i });
            await userEvent.type(searchInput, 'main.cpp');

            expect(screen.getByText('/src/main.cpp')).toBeInTheDocument();
            expect(screen.queryByText('/src/utils.cpp')).not.toBeInTheDocument();
            expect(screen.queryByText('/src/parser.cpp')).not.toBeInTheDocument();
        });

        it('should not show search when showSearch is false', () => {
            render(<ErrorDisplay errors={mockErrors} showSearch={false} />);
            expect(screen.queryByRole('textbox', { name: /search/i })).not.toBeInTheDocument();
        });

        it('should show filtered count', async () => {
            render(<ErrorDisplay errors={mockErrors} showSearch={true} />);

            const searchInput = screen.getByRole('textbox', { name: /search/i });
            await userEvent.type(searchInput, 'Syntax');

            expect(screen.getByText(/1.*3 errors/i)).toBeInTheDocument();
        });
    });

    describe('accessibility', () => {
        it('should have proper ARIA labels', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            const region = screen.getByRole('region', { name: /error list/i });
            expect(region).toHaveAccessibleName();
        });

        it('should announce error count to screen readers', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            const errorCount = screen.getByText(/3 errors/i);
            expect(errorCount).toHaveAttribute('aria-live');
        });

        it('should have accessible error items', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            const errorItems = screen.getAllByRole('button');
            errorItems.forEach(item => {
                expect(item).toHaveAccessibleName();
            });
        });

        it('should support keyboard navigation', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            const firstErrorItem = screen.getByText('/src/main.cpp').closest('.error-item');
            expect(firstErrorItem).toHaveAttribute('tabIndex');
        });
    });

    describe('visual states', () => {
        it('should apply error class', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            const container = screen.getByTestId('error-display');
            expect(container).toHaveClass('has-errors');
        });

        it('should apply no-errors class when empty', () => {
            render(<ErrorDisplay errors={[]} />);
            const container = screen.getByTestId('error-display');
            expect(container).toHaveClass('no-errors');
        });

        it('should highlight errors with line numbers', () => {
            render(<ErrorDisplay errors={mockErrors} />);
            const errorWithLine = screen.getByText(/line 42/i).closest('.error-item');
            expect(errorWithLine).toHaveClass('has-location');
        });
    });

    describe('edge cases', () => {
        it('should handle empty file path', () => {
            const errorsWithEmpty: TranspileError[] = [{
                filePath: '',
                message: 'Unknown error',
            }];
            render(<ErrorDisplay errors={errorsWithEmpty} />);
            expect(screen.getByText(/unknown file/i)).toBeInTheDocument();
        });

        it('should handle very long error messages', () => {
            const longError: TranspileError[] = [{
                filePath: '/test.cpp',
                message: 'A'.repeat(500),
            }];
            render(<ErrorDisplay errors={longError} />);
            expect(screen.getByText('A'.repeat(500))).toBeInTheDocument();
        });

        it('should handle special characters in file paths', () => {
            const specialChars: TranspileError[] = [{
                filePath: '/src/test<>file.cpp',
                message: 'Error',
            }];
            render(<ErrorDisplay errors={specialChars} />);
            expect(screen.getByText('/src/test<>file.cpp')).toBeInTheDocument();
        });

        it('should handle duplicate file paths', () => {
            const duplicates: TranspileError[] = [
                { filePath: '/test.cpp', message: 'Error 1' },
                { filePath: '/test.cpp', message: 'Error 2' },
            ];
            render(<ErrorDisplay errors={duplicates} />);
            const filePaths = screen.getAllByText('/test.cpp');
            expect(filePaths).toHaveLength(2);
        });
    });
});
