import React from 'react';
import { render, screen, waitFor } from '@testing-library/react';
import { describe, it, expect, vi } from 'vitest';
import { Step1SourceSelection } from './Step1SourceSelection';
import type { WizardState, FileInfo } from './types';

// Mock child components
vi.mock('./WizardStepper', () => ({
  WizardStepper: () => <div data-testid="wizard-stepper">Stepper</div>
}));

vi.mock('../DirectorySelector', () => ({
  DirectorySelector: ({ onDirectorySelected }: any) => (
    <button onClick={() => onDirectorySelected({} as any)}>
      Select Directory
    </button>
  )
}));

vi.mock('./FileTreeView', () => ({
  FileTreeView: ({ files }: { files: FileInfo[] }) => (
    <div data-testid="file-tree">Tree with {files.length} files</div>
  )
}));

vi.mock('./FileStatistics', () => ({
  FileStatistics: ({ files }: { files: FileInfo[] }) => (
    <div data-testid="file-statistics">Stats for {files.length} files</div>
  )
}));

// Mock file discovery
vi.mock('./utils/fileDiscovery', () => ({
  discoverCppFiles: vi.fn().mockResolvedValue([
    { path: 'test.cpp', name: 'test.cpp', handle: {} as any, size: 100 },
    { path: 'main.cpp', name: 'main.cpp', handle: {} as any, size: 200 }
  ])
}));

describe('Step1SourceSelection', () => {
  const mockState: WizardState = {
    sourceDir: null,
    sourceFiles: [],
    targetDir: null,
    targetOptions: { targetStandard: 'c99', includeACSL: true },
    transpilationResults: new Map(),
    currentFile: null,
    isTranspiling: false,
    selectedPreviewFile: null
  };

  const mockOnSourceDirSelected = vi.fn();

  it('renders wizard stepper', () => {
    render(
      <Step1SourceSelection
        state={mockState}
        onSourceDirSelected={mockOnSourceDirSelected}
      />
    );

    expect(screen.getByTestId('wizard-stepper')).toBeInTheDocument();
  });

  it('renders title and description', () => {
    render(
      <Step1SourceSelection
        state={mockState}
        onSourceDirSelected={mockOnSourceDirSelected}
      />
    );

    expect(screen.getByText('Step 1: Select Source Directory')).toBeInTheDocument();
    expect(screen.getByText(/Select a directory containing your C\+\+ source code/)).toBeInTheDocument();
  });

  it('shows file tree and statistics after files discovered', () => {
    const stateWithFiles: WizardState = {
      ...mockState,
      sourceFiles: [
        { path: 'test.cpp', name: 'test.cpp', handle: {} as any, size: 100 },
        { path: 'main.cpp', name: 'main.cpp', handle: {} as any, size: 200 }
      ]
    };

    render(
      <Step1SourceSelection
        state={stateWithFiles}
        onSourceDirSelected={mockOnSourceDirSelected}
      />
    );

    expect(screen.getByTestId('file-tree')).toBeInTheDocument();
    expect(screen.getByTestId('file-statistics')).toBeInTheDocument();
  });

  it('hides file tree when no files', () => {
    render(
      <Step1SourceSelection
        state={mockState}
        onSourceDirSelected={mockOnSourceDirSelected}
      />
    );

    expect(screen.queryByTestId('file-tree')).not.toBeInTheDocument();
    expect(screen.queryByTestId('file-statistics')).not.toBeInTheDocument();
  });
});
