import { describe, it, expect, vi } from 'vitest';
import { render, screen, fireEvent } from '@testing-library/react';
import { ConflictWarning } from './ConflictWarning';
import type { FileConflict } from './utils/detectConflicts';

describe('ConflictWarning', () => {
  it('shows success message when no conflicts', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'main.cpp', targetFileName: 'main.c', exists: false }
    ];

    render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={1}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    expect(screen.getByText('No conflicts detected')).toBeInTheDocument();
    expect(screen.getByText(/All 1 files will be created as new files/)).toBeInTheDocument();
  });

  it('shows success message for multiple files with no conflicts', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'main.cpp', targetFileName: 'main.c', exists: false },
      { sourcePath: 'helper.cpp', targetFileName: 'helper.c', exists: false }
    ];

    render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={2}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    expect(screen.getByText('No conflicts detected')).toBeInTheDocument();
    expect(screen.getByText(/All 2 files will be created as new files/)).toBeInTheDocument();
  });

  it('shows warning when conflicts exist', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'main.cpp', targetFileName: 'main.c', exists: true },
      { sourcePath: 'helper.cpp', targetFileName: 'helper.c', exists: false }
    ];

    render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={2}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    expect(screen.getByText('File Conflicts Detected')).toBeInTheDocument();
    expect(screen.getByText(/1 of 2 files/)).toBeInTheDocument();
  });

  it('shows warning for all conflicts', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'a.cpp', targetFileName: 'a.c', exists: true },
      { sourcePath: 'b.cpp', targetFileName: 'b.c', exists: true },
      { sourcePath: 'c.cpp', targetFileName: 'c.c', exists: true }
    ];

    render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={3}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    expect(screen.getByText('File Conflicts Detected')).toBeInTheDocument();
    expect(screen.getByText(/3 of 3 files/)).toBeInTheDocument();
  });

  it('initially hides conflict list', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'main.cpp', targetFileName: 'main.c', exists: true }
    ];

    render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={1}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    // Button to show details exists
    expect(screen.getByText(/Show conflicting files/)).toBeInTheDocument();
    // But conflict details are not visible
    expect(screen.queryByText('main.c')).not.toBeInTheDocument();
  });

  it('toggles conflict list visibility', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'main.cpp', targetFileName: 'main.c', exists: true }
    ];

    render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={1}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    // Initially hidden
    expect(screen.queryByText('main.c')).not.toBeInTheDocument();

    // Click to show
    fireEvent.click(screen.getByText(/Show conflicting files/));
    expect(screen.getByText('main.c')).toBeInTheDocument();

    // Click to hide
    fireEvent.click(screen.getByText(/Hide conflicting files/));
    expect(screen.queryByText('main.c')).not.toBeInTheDocument();
  });

  it('displays all conflicting files in list', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'src/main.cpp', targetFileName: 'main.c', exists: true },
      { sourcePath: 'src/helper.cpp', targetFileName: 'helper.c', exists: true },
      { sourcePath: 'src/utils.cpp', targetFileName: 'utils.c', exists: false }
    ];

    render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={3}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    // Show details
    fireEvent.click(screen.getByText(/Show conflicting files/));

    // Only conflicting files should be shown
    expect(screen.getByText('main.c')).toBeInTheDocument();
    expect(screen.getByText('helper.c')).toBeInTheDocument();
    expect(screen.queryByText('utils.c')).not.toBeInTheDocument();

    // Source paths should be shown
    expect(screen.getByText(/src\/main.cpp/)).toBeInTheDocument();
    expect(screen.getByText(/src\/helper.cpp/)).toBeInTheDocument();
  });

  it('shows acknowledgment checkbox when conflicts exist', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'main.cpp', targetFileName: 'main.c', exists: true }
    ];

    render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={1}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    const checkbox = screen.getByRole('checkbox');
    expect(checkbox).toBeInTheDocument();
    expect(checkbox).not.toBeChecked();
    expect(screen.getByText(/I understand that 1 file will be overwritten/)).toBeInTheDocument();
  });

  it('calls onAcknowledgeChange when checkbox is toggled', () => {
    const handleChange = vi.fn();
    const conflicts: FileConflict[] = [
      { sourcePath: 'main.cpp', targetFileName: 'main.c', exists: true }
    ];

    render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={1}
        acknowledged={false}
        onAcknowledgeChange={handleChange}
      />
    );

    const checkbox = screen.getByRole('checkbox');
    fireEvent.click(checkbox);

    expect(handleChange).toHaveBeenCalledTimes(1);
    expect(handleChange).toHaveBeenCalledWith(true);
  });

  it('checkbox reflects acknowledged state', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'main.cpp', targetFileName: 'main.c', exists: true }
    ];

    const { rerender } = render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={1}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    let checkbox = screen.getByRole('checkbox');
    expect(checkbox).not.toBeChecked();

    rerender(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={1}
        acknowledged={true}
        onAcknowledgeChange={vi.fn()}
      />
    );

    checkbox = screen.getByRole('checkbox');
    expect(checkbox).toBeChecked();
  });

  it('uses plural form for multiple files', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'a.cpp', targetFileName: 'a.c', exists: true },
      { sourcePath: 'b.cpp', targetFileName: 'b.c', exists: true }
    ];

    render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={2}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    expect(screen.getByText(/I understand that 2 files will be overwritten/)).toBeInTheDocument();
  });

  it('shows warning icon for conflicts', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'main.cpp', targetFileName: 'main.c', exists: true }
    ];

    const { container } = render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={1}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    const warningDiv = container.querySelector('.conflict-warning.danger');
    expect(warningDiv).toBeInTheDocument();
  });

  it('shows success icon for no conflicts', () => {
    const conflicts: FileConflict[] = [
      { sourcePath: 'main.cpp', targetFileName: 'main.c', exists: false }
    ];

    const { container } = render(
      <ConflictWarning
        conflicts={conflicts}
        totalFiles={1}
        acknowledged={false}
        onAcknowledgeChange={vi.fn()}
      />
    );

    const successDiv = container.querySelector('.conflict-warning.success');
    expect(successDiv).toBeInTheDocument();
  });
});
