import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { Step4Results } from './Step4Results';
import type { WizardState } from './types';

// Mock WizardStepper
vi.mock('./WizardStepper', () => ({
  WizardStepper: () => <div data-testid="wizard-stepper">Wizard Stepper</div>,
}));

// Mock FileTreeView and DualPaneViewer
vi.mock('./FileTreeView', () => ({
  FileTreeView: ({ files, onFileSelect }: any) => (
    <div data-testid="file-tree">
      {files.map((f: any) => (
        <button key={f.path} onClick={() => onFileSelect(f)}>
          {f.name}
        </button>
      ))}
    </div>
  ),
}));

vi.mock('./DualPaneViewer', () => ({
  DualPaneViewer: ({ sourceContent, transpileContent }: any) => (
    <div data-testid="dual-pane">
      <div data-testid="source">{sourceContent}</div>
      <div data-testid="transpile">{transpileContent}</div>
    </div>
  ),
}));

describe('Step4Results', () => {
  const createMockState = (overrides?: Partial<WizardState>): WizardState => ({
    sourceDir: {} as any,
    sourceFiles: [
      {
        path: 'test.cpp',
        name: 'test.cpp',
        handle: {
          getFile: vi.fn().mockResolvedValue({
            text: vi.fn().mockResolvedValue('// C++ source'),
          }),
        } as any,
        size: 100,
      },
    ],
    targetDir: {} as any,
    targetOptions: { targetStandard: 'c99', includeACSL: true },
    transpilationResults: new Map([
      ['test.cpp', { success: true, cCode: '// C output' }],
    ]),
    currentFile: null,
    isTranspiling: false,
    selectedPreviewFile: null,
    ...overrides,
  });

  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('shows empty state when no transpilation results', () => {
    const emptyState = createMockState({ transpilationResults: new Map() });
    render(
      <Step4Results
        state={emptyState}
        onFileSelected={vi.fn()}
        onDownload={vi.fn()}
      />
    );

    expect(screen.getByText('No Results Yet')).toBeInTheDocument();
  });

  it('displays statistics', () => {
    const mockState = createMockState();
    const { container } = render(
      <Step4Results
        state={mockState}
        onFileSelected={vi.fn()}
        onDownload={vi.fn()}
      />
    );

    expect(screen.getByText('Total:')).toBeInTheDocument();
    expect(screen.getByText('Success:')).toBeInTheDocument();

    // Verify statistics are displayed (both total and success should be 1)
    const stats = container.querySelectorAll('.stat-value');
    expect(stats).toHaveLength(2); // total and success
    expect(stats[0].textContent).toBe('1'); // total
    expect(stats[1].textContent).toBe('1'); // success
  });

  it('displays failed count when there are failures', () => {
    const mockState = createMockState({
      sourceFiles: [
        {
          path: 'test1.cpp',
          name: 'test1.cpp',
          handle: {} as any,
          size: 100,
        },
        {
          path: 'test2.cpp',
          name: 'test2.cpp',
          handle: {} as any,
          size: 200,
        },
      ],
      transpilationResults: new Map([
        ['test1.cpp', { success: true, cCode: '// C output' }],
        ['test2.cpp', { success: false, error: 'Parse error' }],
      ]),
    });

    render(
      <Step4Results
        state={mockState}
        onFileSelected={vi.fn()}
        onDownload={vi.fn()}
      />
    );

    expect(screen.getByText('Failed:')).toBeInTheDocument();
  });

  it('renders file tree with transpiled files', () => {
    const mockState = createMockState();
    render(
      <Step4Results
        state={mockState}
        onFileSelected={vi.fn()}
        onDownload={vi.fn()}
      />
    );

    expect(screen.getByTestId('file-tree')).toBeInTheDocument();
    expect(screen.getByText('test.cpp')).toBeInTheDocument();
  });

  it('calls onFileSelected when file clicked', async () => {
    const handleFileSelect = vi.fn();
    const mockState = createMockState();

    render(
      <Step4Results
        state={mockState}
        onFileSelected={handleFileSelect}
        onDownload={vi.fn()}
      />
    );

    const fileButton = screen.getByText('test.cpp');
    await userEvent.click(fileButton);

    expect(handleFileSelect).toHaveBeenCalledWith('test.cpp');
  });

  it('loads and displays file content when file selected', async () => {
    const stateWithSelection = createMockState({
      selectedPreviewFile: 'test.cpp',
    });

    render(
      <Step4Results
        state={stateWithSelection}
        onFileSelected={vi.fn()}
        onDownload={vi.fn()}
      />
    );

    await waitFor(() => {
      expect(screen.getByTestId('source')).toHaveTextContent('// C++ source');
      expect(screen.getByTestId('transpile')).toHaveTextContent('// C output');
    });
  });

  it('shows loading state while loading file', async () => {
    const stateWithSelection = createMockState({
      selectedPreviewFile: 'test.cpp',
    });

    render(
      <Step4Results
        state={stateWithSelection}
        onFileSelected={vi.fn()}
        onDownload={vi.fn()}
      />
    );

    // Should show loading briefly
    expect(screen.getByText(/Loading file contents/i)).toBeInTheDocument();
  });

  it('displays error state when file load fails', async () => {
    const stateWithBadFile = createMockState({
      sourceFiles: [
        {
          path: 'bad.cpp',
          name: 'bad.cpp',
          handle: {
            getFile: vi.fn().mockRejectedValue(new Error('Read failed')),
          } as any,
          size: 100,
        },
      ],
      transpilationResults: new Map([
        ['bad.cpp', { success: true, cCode: '// C output' }],
      ]),
      selectedPreviewFile: 'bad.cpp',
    });

    render(
      <Step4Results
        state={stateWithBadFile}
        onFileSelected={vi.fn()}
        onDownload={vi.fn()}
      />
    );

    await waitFor(() => {
      expect(screen.getByText('Error Loading File')).toBeInTheDocument();
    });
  });

  it('shows failed transpilation in output pane', async () => {
    const stateWithError = createMockState({
      transpilationResults: new Map([
        ['test.cpp', { success: false, error: 'Parse error' }],
      ]),
      selectedPreviewFile: 'test.cpp',
    });

    render(
      <Step4Results
        state={stateWithError}
        onFileSelected={vi.fn()}
        onDownload={vi.fn()}
      />
    );

    await waitFor(() => {
      expect(screen.getByTestId('transpile')).toHaveTextContent('Parse error');
    });
  });

  it('handles missing source file gracefully', async () => {
    const stateWithMissingSource = createMockState({
      sourceFiles: [], // No source files
      transpilationResults: new Map([
        ['test.cpp', { success: true, cCode: '// C output' }],
      ]),
      selectedPreviewFile: 'test.cpp',
    });

    render(
      <Step4Results
        state={stateWithMissingSource}
        onFileSelected={vi.fn()}
        onDownload={vi.fn()}
      />
    );

    await waitFor(() => {
      expect(screen.getByText('Error Loading File')).toBeInTheDocument();
    });
  });

  it('clears content when selectedPreviewFile becomes null', async () => {
    const { rerender } = render(
      <Step4Results
        state={createMockState({ selectedPreviewFile: 'test.cpp' })}
        onFileSelected={vi.fn()}
        onDownload={vi.fn()}
      />
    );

    // Wait for content to load
    await waitFor(() => {
      expect(screen.getByTestId('source')).toHaveTextContent('// C++ source');
    });

    // Now clear selection
    rerender(
      <Step4Results
        state={createMockState({ selectedPreviewFile: null })}
        onFileSelected={vi.fn()}
        onDownload={vi.fn()}
      />
    );

    // Content should be cleared (but dual pane should still render with empty content)
    await waitFor(() => {
      expect(screen.getByTestId('source')).toHaveTextContent('');
    });
  });
});
