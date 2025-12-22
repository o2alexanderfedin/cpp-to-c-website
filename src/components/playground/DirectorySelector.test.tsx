import { describe, it, expect, vi } from 'vitest';
import { render, screen, fireEvent } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { DirectorySelector } from './DirectorySelector';

describe('DirectorySelector', () => {
    describe('rendering', () => {
        it('should render the component', () => {
            render(<DirectorySelector onDirectorySelected={vi.fn()} />);
            expect(screen.getByRole('button', { name: /select directory/i })).toBeInTheDocument();
        });

        it('should render drag-drop zone', () => {
            render(<DirectorySelector onDirectorySelected={vi.fn()} />);
            expect(screen.getByText(/drag.*drop/i)).toBeInTheDocument();
        });

        it('should not show selected path when no directory selected', () => {
            render(<DirectorySelector onDirectorySelected={vi.fn()} />);
            expect(screen.queryByTestId('selected-path')).not.toBeInTheDocument();
        });

        it('should show selected path when directory is selected', () => {
            render(<DirectorySelector onDirectorySelected={vi.fn()} selectedPath="/test/path" />);
            expect(screen.getByTestId('selected-path')).toHaveTextContent('/test/path');
        });
    });

    describe('button click', () => {
        it('should call onDirectorySelected when button is clicked', async () => {
            const onDirectorySelected = vi.fn();
            const mockHandle = { kind: 'directory', name: 'test-dir' };

            // Mock showDirectoryPicker
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            render(<DirectorySelector onDirectorySelected={onDirectorySelected} />);

            const button = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(button);

            expect(window.showDirectoryPicker).toHaveBeenCalled();
            expect(onDirectorySelected).toHaveBeenCalledWith(mockHandle);
        });

        it('should handle picker cancellation gracefully', async () => {
            const onDirectorySelected = vi.fn();

            // Mock user canceling picker
            (window as any).showDirectoryPicker = vi.fn().mockRejectedValue(new DOMException('User cancelled', 'AbortError'));

            render(<DirectorySelector onDirectorySelected={onDirectorySelected} />);

            const button = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(button);

            expect(onDirectorySelected).not.toHaveBeenCalled();
            expect(screen.queryByRole('alert')).not.toBeInTheDocument();
        });

        it('should display error when picker fails', async () => {
            const onDirectorySelected = vi.fn();

            // Mock picker error
            (window as any).showDirectoryPicker = vi.fn().mockRejectedValue(new Error('Permission denied'));

            render(<DirectorySelector onDirectorySelected={onDirectorySelected} />);

            const button = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(button);

            expect(screen.getByRole('alert')).toHaveTextContent(/error/i);
        });
    });

    describe('drag and drop', () => {
        it('should highlight drop zone on drag over', () => {
            render(<DirectorySelector onDirectorySelected={vi.fn()} />);

            const dropZone = screen.getByTestId('drop-zone');
            fireEvent.dragOver(dropZone);

            expect(dropZone).toHaveClass('drag-active');
        });

        it('should remove highlight on drag leave', () => {
            render(<DirectorySelector onDirectorySelected={vi.fn()} />);

            const dropZone = screen.getByTestId('drop-zone');
            fireEvent.dragOver(dropZone);
            fireEvent.dragLeave(dropZone);

            expect(dropZone).not.toHaveClass('drag-active');
        });

        it('should call onDirectorySelected when directory is dropped', async () => {
            const onDirectorySelected = vi.fn();
            const mockHandle = { kind: 'directory', name: 'test-dir' };

            render(<DirectorySelector onDirectorySelected={onDirectorySelected} />);

            const dropZone = screen.getByTestId('drop-zone');

            const mockDataTransfer = {
                items: [{
                    kind: 'file',
                    getAsFileSystemHandle: vi.fn().mockResolvedValue(mockHandle)
                }]
            };

            fireEvent.drop(dropZone, { dataTransfer: mockDataTransfer });

            // Wait for async operation
            await new Promise(resolve => setTimeout(resolve, 0));

            expect(onDirectorySelected).toHaveBeenCalledWith(mockHandle);
        });

        it('should reject non-directory items', async () => {
            const onDirectorySelected = vi.fn();
            const mockHandle = { kind: 'file', name: 'test.txt' };

            render(<DirectorySelector onDirectorySelected={onDirectorySelected} />);

            const dropZone = screen.getByTestId('drop-zone');

            const mockDataTransfer = {
                items: [{
                    kind: 'file',
                    getAsFileSystemHandle: vi.fn().mockResolvedValue(mockHandle)
                }]
            };

            fireEvent.drop(dropZone, { dataTransfer: mockDataTransfer });

            await new Promise(resolve => setTimeout(resolve, 0));

            expect(onDirectorySelected).not.toHaveBeenCalled();
            expect(screen.getByRole('alert')).toHaveTextContent(/must be a directory/i);
        });
    });

    describe('accessibility', () => {
        it('should have proper ARIA label on button', () => {
            render(<DirectorySelector onDirectorySelected={vi.fn()} />);

            const button = screen.getByRole('button', { name: /select directory/i });
            expect(button).toHaveAccessibleName();
        });

        it('should have proper ARIA label on drop zone', () => {
            render(<DirectorySelector onDirectorySelected={vi.fn()} />);

            const dropZone = screen.getByTestId('drop-zone');
            expect(dropZone).toHaveAttribute('aria-label');
        });

        it('should announce errors to screen readers', async () => {
            const onDirectorySelected = vi.fn();
            (window as any).showDirectoryPicker = vi.fn().mockRejectedValue(new Error('Test error'));

            render(<DirectorySelector onDirectorySelected={onDirectorySelected} />);

            const button = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(button);

            const alert = screen.getByRole('alert');
            expect(alert).toHaveAttribute('aria-live', 'polite');
        });
    });

    describe('validation', () => {
        it('should validate selected directory handle', async () => {
            const onDirectorySelected = vi.fn();
            const mockHandle = null;

            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            render(<DirectorySelector onDirectorySelected={onDirectorySelected} />);

            const button = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(button);

            expect(onDirectorySelected).not.toHaveBeenCalled();
        });

        it('should pass custom validation function', async () => {
            const onDirectorySelected = vi.fn();
            const onValidate = vi.fn().mockResolvedValue(false);
            const mockHandle = { kind: 'directory', name: 'test-dir' };

            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            render(
                <DirectorySelector
                    onDirectorySelected={onDirectorySelected}
                    onValidate={onValidate}
                />
            );

            const button = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(button);

            expect(onValidate).toHaveBeenCalledWith(mockHandle);
            expect(onDirectorySelected).not.toHaveBeenCalled();
            expect(screen.getByRole('alert')).toHaveTextContent(/validation failed/i);
        });
    });
});
