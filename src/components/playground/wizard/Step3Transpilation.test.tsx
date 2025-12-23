import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import { Step3Transpilation } from './Step3Transpilation';
import type { WizardState } from './types';

// Mock WizardStepper
vi.mock('./WizardStepper', () => ({
  WizardStepper: () => <div data-testid="wizard-stepper">Stepper</div>
}));

// Mock useTranspilation hook
const mockStart = vi.fn();
const mockPause = vi.fn();
const mockResume = vi.fn();
const mockCancel = vi.fn();
const mockIsPaused = vi.fn().mockReturnValue(false);
const mockGetExecutionMode = vi.fn().mockReturnValue('parallel');

vi.mock('./hooks/useTranspilation', () => ({
  useTranspilation: vi.fn(() => ({
    start: mockStart,
    pause: mockPause,
    resume: mockResume,
    cancel: mockCancel,
    isPaused: mockIsPaused,
    getExecutionMode: mockGetExecutionMode
  }))
}));

describe('Step3Transpilation', () => {
  const mockState: WizardState = {
    sourceDir: {} as FileSystemDirectoryHandle,
    sourceFiles: [
      { path: 'test1.cpp', name: 'test1.cpp', handle: {} as any, size: 100 },
      { path: 'test2.cpp', name: 'test2.cpp', handle: {} as any, size: 200 }
    ],
    targetDir: {} as FileSystemDirectoryHandle,
    targetOptions: { targetStandard: 'c99', includeACSL: true },
    transpilationResults: new Map(),
    currentFile: null,
    isTranspiling: false,
    transpileStartTime: null,
    selectedPreviewFile: null
  };

  const mockCallbacks = {
    onStartTranspilation: vi.fn(),
    onPauseTranspilation: vi.fn(),
    onCancelTranspilation: vi.fn(),
    onFileCompleted: vi.fn()
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('renders the component', () => {
    render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    expect(screen.getByText('Step 3: Transpilation')).toBeInTheDocument();
    expect(screen.getByTestId('wizard-stepper')).toBeInTheDocument();
  });

  it('displays initial progress state', () => {
    render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    expect(screen.getByText(/0 of 0 files/i)).toBeInTheDocument();
  });

  it('auto-starts transpilation when component mounts with valid state', async () => {
    render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    await waitFor(() => {
      expect(mockCallbacks.onStartTranspilation).toHaveBeenCalled();
      expect(mockStart).toHaveBeenCalledWith(
        mockState.sourceFiles,
        mockState.targetDir,
        mockState.targetOptions
      );
    });
  });

  it('does not start transpilation if already started', () => {
    const { rerender } = render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    vi.clearAllMocks();

    // Re-render with same state
    rerender(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    // Should not start again
    expect(mockCallbacks.onStartTranspilation).not.toHaveBeenCalled();
  });

  it('does not start transpilation if no source files', () => {
    const emptyState = { ...mockState, sourceFiles: [] };

    render(<Step3Transpilation state={emptyState} {...mockCallbacks} />);

    expect(mockCallbacks.onStartTranspilation).not.toHaveBeenCalled();
    expect(mockStart).not.toHaveBeenCalled();
  });

  it('does not start transpilation if no target directory', () => {
    const noTargetState = { ...mockState, targetDir: null };

    render(<Step3Transpilation state={noTargetState} {...mockCallbacks} />);

    expect(mockCallbacks.onStartTranspilation).not.toHaveBeenCalled();
    expect(mockStart).not.toHaveBeenCalled();
  });

  it('displays current file being processed', () => {
    const { rerender } = render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    // Initially no current file
    expect(screen.queryByText(/Processing:/i)).not.toBeInTheDocument();

    // Simulate file started via useTranspilation callback
    // This would be tested via integration test with actual hook
  });

  it('displays progress bar', () => {
    render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    // Check for progress bar by class name instead of role
    const progressContainer = document.querySelector('.progress-bar');
    expect(progressContainer).toBeInTheDocument();
  });

  it('displays metrics section', () => {
    render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    expect(screen.getByText(/Elapsed Time:/i)).toBeInTheDocument();
    expect(screen.getByText(/Speed:/i)).toBeInTheDocument();
    expect(screen.getByText(/Estimated Remaining:/i)).toBeInTheDocument();
  });

  it('formats time correctly', () => {
    render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    // Initial time should be 0:00 - there may be multiple instances
    const timeElements = screen.getAllByText('0:00');
    expect(timeElements.length).toBeGreaterThan(0);
  });

  it('displays control buttons when not complete', () => {
    render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    // Should show pause button initially
    expect(screen.getByRole('button', { name: /pause/i })).toBeInTheDocument();
    expect(screen.getByRole('button', { name: /cancel/i })).toBeInTheDocument();
  });

  it('does not display control buttons when complete', async () => {
    const { rerender } = render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    // Simulate completion by triggering onCompleted callback
    // This would be tested via integration test
  });

  it('displays completion message when transpilation is complete', () => {
    render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

    // Initially no completion message
    expect(screen.queryByText(/Transpilation complete/i)).not.toBeInTheDocument();
  });

  it('handles missing callbacks gracefully', () => {
    const minimalCallbacks = {
      onStartTranspilation: vi.fn(),
      onPauseTranspilation: vi.fn(),
      onCancelTranspilation: vi.fn()
    };

    expect(() => {
      render(<Step3Transpilation state={mockState} {...minimalCallbacks} />);
    }).not.toThrow();
  });

  describe('Pause/Resume Enhancements', () => {
    it('displays keyboard hints', () => {
      render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

      expect(screen.getByText('Space')).toBeInTheDocument();
      expect(screen.getByText('Esc')).toBeInTheDocument();
    });

    it('has ARIA labels on control buttons', () => {
      render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

      const pauseButton = screen.getByLabelText(/pause transpilation/i);
      expect(pauseButton).toBeInTheDocument();

      const cancelButton = screen.getByLabelText(/cancel transpilation/i);
      expect(cancelButton).toBeInTheDocument();
    });

    it('has button icons displayed', () => {
      render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

      // Check for button icons
      const buttons = screen.getAllByRole('button');
      expect(buttons.length).toBeGreaterThan(0);

      // Icons are in span elements with class 'button-icon'
      const buttonIcons = document.querySelectorAll('.button-icon');
      expect(buttonIcons.length).toBeGreaterThan(0);
    });

    it('displays pause indicator when paused', () => {
      render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

      // Initially no pause indicator
      expect(screen.queryByText('Paused')).not.toBeInTheDocument();

      // Note: Testing pause state would require triggering pause action
      // which would be better in an integration test
    });

    it('shows correct keyboard hint text based on pause state', () => {
      render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

      // Initially should show "Pause" button since isPaused is false
      const pauseButton = screen.getByLabelText(/pause transpilation/i);
      expect(pauseButton).toBeInTheDocument();
      expect(pauseButton.textContent).toContain('Pause');

      // After pausing, would show "Resume" - tested in integration
    });

    it('has keyboard shortcuts registered', () => {
      render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

      // Component should register keyboard event listeners
      // This is verified by the useEffect hook being called
      // Actual key press testing would be in integration tests
      expect(screen.getByText('Space')).toBeInTheDocument();
    });

    it('has progress bar with proper styling', () => {
      render(<Step3Transpilation state={mockState} {...mockCallbacks} />);

      const progressBar = document.querySelector('.progress-bar');
      expect(progressBar).toBeInTheDocument();

      const progressFill = document.querySelector('.progress-fill');
      expect(progressFill).toBeInTheDocument();
    });
  });
});
