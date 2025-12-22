import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, fireEvent, waitFor } from '@testing-library/react';
import { Step2TargetSelection } from './Step2TargetSelection';
import type { WizardState } from './types';

// Mock WizardStepper
vi.mock('./WizardStepper', () => ({
  WizardStepper: () => <div data-testid="wizard-stepper">Stepper</div>
}));

// Mock PermissionIndicator
vi.mock('./PermissionIndicator', () => ({
  PermissionIndicator: ({ hasRead, hasWrite, onRequestPermission }: any) => (
    <div data-testid="permission-indicator">
      <span>Read: {hasRead ? 'granted' : 'denied'}</span>
      <span>Write: {hasWrite ? 'granted' : 'denied'}</span>
      {onRequestPermission && <button onClick={onRequestPermission}>Request</button>}
    </div>
  )
}));

// Mock permission utilities
vi.mock('./utils/checkDirectoryPermissions', () => ({
  checkDirectoryPermissions: vi.fn().mockResolvedValue({ read: true, write: true }),
  requestWritePermission: vi.fn().mockResolvedValue(true)
}));

describe('Step2TargetSelection', () => {
  const mockState: WizardState = {
    sourceDir: null,
    sourceFiles: [],
    targetDir: null,
    targetOptions: { targetStandard: 'c99', includeACSL: true },
    transpilationResults: new Map(),
    currentFile: null,
    isTranspiling: false,
    transpileStartTime: null,
    selectedPreviewFile: null
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('renders directory selection button', () => {
    render(
      <Step2TargetSelection
        state={mockState}
        onTargetDirSelected={vi.fn()}
        onOptionsChanged={vi.fn()}
      />
    );

    expect(screen.getByText('Select Target Directory')).toBeInTheDocument();
  });

  it('renders wizard stepper', () => {
    render(
      <Step2TargetSelection
        state={mockState}
        onTargetDirSelected={vi.fn()}
        onOptionsChanged={vi.fn()}
      />
    );

    expect(screen.getByTestId('wizard-stepper')).toBeInTheDocument();
  });

  it('renders step title and description', () => {
    render(
      <Step2TargetSelection
        state={mockState}
        onTargetDirSelected={vi.fn()}
        onOptionsChanged={vi.fn()}
      />
    );

    expect(screen.getByText('Step 2: Select Target Directory')).toBeInTheDocument();
    expect(screen.getByText(/Choose where transpiled C files will be saved/)).toBeInTheDocument();
  });

  it('displays selected directory name', () => {
    const mockDirHandle = { name: 'output' } as FileSystemDirectoryHandle;
    const stateWithDir = { ...mockState, targetDir: mockDirHandle };

    render(
      <Step2TargetSelection
        state={stateWithDir}
        onTargetDirSelected={vi.fn()}
        onOptionsChanged={vi.fn()}
      />
    );

    expect(screen.getByText('output')).toBeInTheDocument();
    expect(screen.getByText('Change Target Directory')).toBeInTheDocument();
  });

  it('shows permission indicator when directory is selected', () => {
    const mockDirHandle = { name: 'output' } as FileSystemDirectoryHandle;
    const stateWithDir = { ...mockState, targetDir: mockDirHandle };

    render(
      <Step2TargetSelection
        state={stateWithDir}
        onTargetDirSelected={vi.fn()}
        onOptionsChanged={vi.fn()}
      />
    );

    expect(screen.getByTestId('permission-indicator')).toBeInTheDocument();
  });

  it('does not show permission indicator when directory is not selected', () => {
    render(
      <Step2TargetSelection
        state={mockState}
        onTargetDirSelected={vi.fn()}
        onOptionsChanged={vi.fn()}
      />
    );

    expect(screen.queryByTestId('permission-indicator')).not.toBeInTheDocument();
  });

  it('shows transpilation options', () => {
    render(
      <Step2TargetSelection
        state={mockState}
        onTargetDirSelected={vi.fn()}
        onOptionsChanged={vi.fn()}
      />
    );

    expect(screen.getByText('Transpilation Options')).toBeInTheDocument();
    expect(screen.getByText(/Target C Standard/)).toBeInTheDocument();
    expect(screen.getByText(/Include ACSL annotations/)).toBeInTheDocument();
  });

  it('calls onOptionsChanged when C standard changes', () => {
    const handleChange = vi.fn();

    render(
      <Step2TargetSelection
        state={mockState}
        onTargetDirSelected={vi.fn()}
        onOptionsChanged={handleChange}
      />
    );

    const select = screen.getByRole('combobox');
    fireEvent.change(select, { target: { value: 'c11' } });

    expect(handleChange).toHaveBeenCalledWith({
      targetStandard: 'c11',
      includeACSL: true
    });
  });

  it('calls onOptionsChanged when ACSL checkbox changes', () => {
    const handleChange = vi.fn();

    render(
      <Step2TargetSelection
        state={mockState}
        onTargetDirSelected={vi.fn()}
        onOptionsChanged={handleChange}
      />
    );

    const checkbox = screen.getByRole('checkbox');
    fireEvent.click(checkbox);

    expect(handleChange).toHaveBeenCalledWith({
      targetStandard: 'c99',
      includeACSL: false
    });
  });

  it('disables button while selecting', async () => {
    // Mock showDirectoryPicker to create a delay
    const mockShowDirectoryPicker = vi.fn().mockImplementation(
      () => new Promise(resolve => setTimeout(() => resolve({ name: 'test' }), 100))
    );
    (window as any).showDirectoryPicker = mockShowDirectoryPicker;

    const { container } = render(
      <Step2TargetSelection
        state={mockState}
        onTargetDirSelected={vi.fn()}
        onOptionsChanged={vi.fn()}
      />
    );

    const button = screen.getByText('Select Target Directory') as HTMLButtonElement;
    fireEvent.click(button);

    // Button should be disabled during selection
    await waitFor(() => {
      expect(button.disabled).toBe(true);
    });

    delete (window as any).showDirectoryPicker;
  });

  it('shows error when showDirectoryPicker is not supported', async () => {
    // Remove showDirectoryPicker
    const originalShowDirectoryPicker = (window as any).showDirectoryPicker;
    delete (window as any).showDirectoryPicker;

    render(
      <Step2TargetSelection
        state={mockState}
        onTargetDirSelected={vi.fn()}
        onOptionsChanged={vi.fn()}
      />
    );

    const button = screen.getByText('Select Target Directory');
    fireEvent.click(button);

    await waitFor(() => {
      expect(screen.getByText(/Your browser does not support directory selection/)).toBeInTheDocument();
    });

    // Restore
    if (originalShowDirectoryPicker) {
      (window as any).showDirectoryPicker = originalShowDirectoryPicker;
    }
  });
});
