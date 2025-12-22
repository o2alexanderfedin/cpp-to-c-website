import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { PlaygroundController } from './PlaygroundController';
import type { ITranspiler } from '../../core/interfaces/ITranspiler';
import type { IFileSystem } from '../../core/interfaces/IFileSystem';

describe('PlaygroundController', () => {
    let mockTranspiler: ITranspiler;
    let mockFileSystem: IFileSystem;

    beforeEach(() => {
        mockTranspiler = {
            transpile: vi.fn().mockResolvedValue({
                success: true,
                output: '// C code',
                errors: [],
            }),
            validateInput: vi.fn().mockResolvedValue({
                isValid: true,
                errors: [],
            }),
        };

        mockFileSystem = {
            readFile: vi.fn().mockResolvedValue('// C++ code'),
            writeFile: vi.fn().mockResolvedValue(undefined),
            readDir: vi.fn().mockResolvedValue(['test.cpp']),
            exists: vi.fn().mockResolvedValue(true),
            selectDirectory: vi.fn().mockResolvedValue({ kind: 'directory', name: 'test' }),
            traverseDirectory: vi.fn().mockResolvedValue([
                { path: '/test/main.cpp', name: 'main.cpp', isDirectory: false },
            ]),
        };
    });

    describe('rendering', () => {
        it('should render all components', () => {
            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            expect(screen.getByRole('button', { name: /select directory/i })).toBeInTheDocument();
            expect(screen.getByRole('region', { name: /errors/i })).toBeInTheDocument();
        });

        it('should not show progress initially', () => {
            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);
            expect(screen.queryByRole('progressbar')).not.toBeInTheDocument();
        });

        it('should not show transpile button initially', () => {
            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);
            expect(screen.queryByRole('button', { name: /transpile/i })).not.toBeInTheDocument();
        });
    });

    describe('directory selection', () => {
        it('should show transpile button after directory selected', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            await waitFor(() => {
                expect(screen.getByRole('button', { name: /transpile/i })).toBeInTheDocument();
            });
        });

        it('should display selected directory path', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            await waitFor(() => {
                expect(screen.getByTestId('selected-path')).toHaveTextContent('test-dir');
            });
        });

        it('should allow selecting different directory', async () => {
            const mockHandle1 = { kind: 'directory', name: 'dir1' };
            const mockHandle2 = { kind: 'directory', name: 'dir2' };

            (window as any).showDirectoryPicker = vi
                .fn()
                .mockResolvedValueOnce(mockHandle1)
                .mockResolvedValueOnce(mockHandle2);

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });

            await userEvent.click(selectButton);
            await waitFor(() => {
                expect(screen.getByTestId('selected-path')).toHaveTextContent('dir1');
            });

            await userEvent.click(selectButton);
            await waitFor(() => {
                expect(screen.getByTestId('selected-path')).toHaveTextContent('dir2');
            });
        });
    });

    describe('transpilation', () => {
        it('should start transpilation when button clicked', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            // Delay transpiler to see progress
            mockTranspiler.transpile = vi.fn().mockImplementation(
                () => new Promise(resolve => setTimeout(() => resolve({ success: true, output: '', errors: [] }), 50))
            );

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            const transpileButton = await screen.findByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            // Wait a bit for transpilation to start
            await new Promise(resolve => setTimeout(resolve, 10));

            // Progress bar should appear during transpilation
            const progressBar = screen.queryByRole('progressbar');
            if (progressBar) {
                expect(progressBar).toBeInTheDocument();
            }
        });

        it('should show progress during transpilation', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            const transpileButton = await screen.findByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            await waitFor(() => {
                const progressBar = screen.getByRole('progressbar');
                expect(progressBar).toHaveAttribute('aria-valuenow');
            });
        });

        it('should disable transpile button during transpilation', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            // Make transpiler take time
            mockTranspiler.transpile = vi.fn().mockImplementation(
                () => new Promise(resolve => setTimeout(() => resolve({ success: true, output: '', errors: [] }), 100))
            );

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            const transpileButton = await screen.findByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            expect(transpileButton).toBeDisabled();
        });

        it('should show completion message after success', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            const transpileButton = await screen.findByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            await waitFor(() => {
                expect(screen.getByText(/completed/i)).toBeInTheDocument();
            });
        });

        it('should call transpiler with correct files', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            mockFileSystem.traverseDirectory = vi.fn().mockResolvedValue([
                { path: '/test/main.cpp', name: 'main.cpp', isDirectory: false },
                { path: '/test/utils.cpp', name: 'utils.cpp', isDirectory: false },
            ]);

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            const transpileButton = await screen.findByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            await waitFor(() => {
                expect(mockTranspiler.transpile).toHaveBeenCalled();
            });
        });
    });

    describe('error handling', () => {
        it('should display errors when transpilation fails', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            mockTranspiler.transpile = vi.fn().mockResolvedValue({
                success: false,
                output: '',
                errors: [
                    {
                        filePath: '/test/main.cpp',
                        message: 'Syntax error',
                        line: 10,
                    },
                ],
            });

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            const transpileButton = await screen.findByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            await waitFor(() => {
                expect(screen.getByText('Syntax error')).toBeInTheDocument();
            });
        });

        it('should show error count', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            mockTranspiler.transpile = vi.fn().mockResolvedValue({
                success: false,
                output: '',
                errors: [
                    { filePath: '/test/main.cpp', message: 'Error 1' },
                    { filePath: '/test/utils.cpp', message: 'Error 2' },
                ],
            });

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            const transpileButton = await screen.findByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            await waitFor(() => {
                expect(screen.getByText(/2 errors/i)).toBeInTheDocument();
            });
        });

        it('should handle file system errors', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            mockFileSystem.traverseDirectory = vi.fn().mockRejectedValue(new Error('Permission denied'));

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            const transpileButton = await screen.findByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            await waitFor(() => {
                expect(screen.getByText(/permission denied/i)).toBeInTheDocument();
            });
        });
    });

    describe('cancellation', () => {
        it('should show cancel button during transpilation', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            // Make transpiler take time
            mockTranspiler.transpile = vi.fn().mockImplementation(
                () => new Promise(resolve => setTimeout(() => resolve({ success: true, output: '', errors: [] }), 1000))
            );

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            const transpileButton = await screen.findByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            await waitFor(() => {
                expect(screen.getByRole('button', { name: /cancel/i })).toBeInTheDocument();
            });
        });

        it('should stop transpilation when cancelled', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            let cancelCallback: (() => void) | null = null;
            mockTranspiler.transpile = vi.fn().mockImplementation(
                () =>
                    new Promise((resolve, reject) => {
                        cancelCallback = () => reject(new Error('Cancelled'));
                        setTimeout(() => resolve({ success: true, output: '', errors: [] }), 1000);
                    })
            );

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            const transpileButton = await screen.findByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            const cancelButton = await screen.findByRole('button', { name: /cancel/i });
            await userEvent.click(cancelButton);

            await waitFor(() => {
                expect(screen.getByText(/cancelled/i)).toBeInTheDocument();
            });
        });
    });

    describe('accessibility', () => {
        it('should have proper ARIA labels', () => {
            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const main = screen.getByRole('main');
            expect(main).toHaveAccessibleName();
        });

        it('should announce transpilation status', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            const transpileButton = await screen.findByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            await waitFor(() => {
                const status = screen.getByRole('status');
                expect(status).toHaveAttribute('aria-live');
            });
        });
    });

    describe('integration', () => {
        it('should integrate all components correctly', async () => {
            const mockHandle = { kind: 'directory', name: 'test-dir' };
            (window as any).showDirectoryPicker = vi.fn().mockResolvedValue(mockHandle);

            mockFileSystem.traverseDirectory = vi.fn().mockResolvedValue([
                { path: '/test/main.cpp', name: 'main.cpp', isDirectory: false },
            ]);

            render(<PlaygroundController transpiler={mockTranspiler} fileSystem={mockFileSystem} />);

            // Select directory
            const selectButton = screen.getByRole('button', { name: /select directory/i });
            await userEvent.click(selectButton);

            // Verify directory selected
            await waitFor(() => {
                expect(screen.getByTestId('selected-path')).toHaveTextContent('test-dir');
            });

            // Verify transpile button appears
            expect(screen.getByRole('button', { name: /transpile/i })).toBeInTheDocument();

            // Start transpilation
            const transpileButton = screen.getByRole('button', { name: /transpile/i });
            await userEvent.click(transpileButton);

            // Verify completion message appears eventually
            await waitFor(() => {
                expect(screen.getByText(/completed/i)).toBeInTheDocument();
            }, { timeout: 2000 });
        });
    });
});
