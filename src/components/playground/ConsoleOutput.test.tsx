/**
 * Unit tests for ConsoleOutput component
 *
 * Tests log display, formatting, and clear functionality.
 */

import { describe, it, expect, vi } from 'vitest';
import { render, screen, fireEvent } from '@testing-library/react';
import { ConsoleOutput } from './ConsoleOutput';
import type { ConsoleLogEntry } from '../../lib/playground/idbfs-types';

describe('ConsoleOutput', () => {
  const mockLogs: ConsoleLogEntry[] = [
    { timestamp: new Date('2026-01-18T10:00:00'), level: 'info', message: 'Info message' },
    { timestamp: new Date('2026-01-18T10:00:01'), level: 'success', message: 'Success message' },
    { timestamp: new Date('2026-01-18T10:00:02'), level: 'error', message: 'Error message' },
    { timestamp: new Date('2026-01-18T10:00:03'), level: 'warn', message: 'Warning message' },
  ];

  it('should render console title', () => {
    render(<ConsoleOutput logs={[]} />);
    expect(screen.getByText(/Console Output/i)).toBeInTheDocument();
  });

  it('should display empty message when no logs', () => {
    render(<ConsoleOutput logs={[]} />);
    expect(screen.getByText(/Console is empty/i)).toBeInTheDocument();
  });

  it('should display all log entries', () => {
    render(<ConsoleOutput logs={mockLogs} />);

    expect(screen.getByText('Info message')).toBeInTheDocument();
    expect(screen.getByText('Success message')).toBeInTheDocument();
    expect(screen.getByText('Error message')).toBeInTheDocument();
    expect(screen.getByText('Warning message')).toBeInTheDocument();
  });

  it('should display timestamps when enabled', () => {
    render(<ConsoleOutput logs={mockLogs} showTimestamps={true} />);

    // Check for timestamp format [HH:MM:SS]
    const timestamps = screen.getAllByText(/\[\d{2}:\d{2}:\d{2}\]/);
    expect(timestamps).toHaveLength(mockLogs.length);
  });

  it('should hide timestamps when disabled', () => {
    render(<ConsoleOutput logs={mockLogs} showTimestamps={false} />);

    // Should not find timestamp brackets
    const timestamps = screen.queryAllByText(/\[\d{2}:\d{2}:\d{2}\]/);
    expect(timestamps).toHaveLength(0);
  });

  it('should render clear button when onClear is provided', () => {
    const mockOnClear = vi.fn();
    render(<ConsoleOutput logs={mockLogs} onClear={mockOnClear} />);

    const clearButton = screen.getByLabelText(/Clear console/i);
    expect(clearButton).toBeInTheDocument();
  });

  it('should not render clear button when onClear is not provided', () => {
    render(<ConsoleOutput logs={mockLogs} />);

    const clearButton = screen.queryByLabelText(/Clear console/i);
    expect(clearButton).not.toBeInTheDocument();
  });

  it('should call onClear when clear button is clicked', () => {
    const mockOnClear = vi.fn();
    render(<ConsoleOutput logs={mockLogs} onClear={mockOnClear} />);

    const clearButton = screen.getByLabelText(/Clear console/i);
    fireEvent.click(clearButton);

    expect(mockOnClear).toHaveBeenCalledTimes(1);
  });

  it('should have proper ARIA attributes', () => {
    render(<ConsoleOutput logs={mockLogs} />);

    const consoleContent = screen.getByRole('log');
    expect(consoleContent).toHaveAttribute('aria-live', 'polite');
    expect(consoleContent).toHaveAttribute('aria-label');
  });

  it('should apply correct CSS classes for log levels', () => {
    render(<ConsoleOutput logs={mockLogs} />);

    const infoLog = screen.getByText('Info message').closest('.log-entry');
    const successLog = screen.getByText('Success message').closest('.log-entry');
    const errorLog = screen.getByText('Error message').closest('.log-entry');
    const warnLog = screen.getByText('Warning message').closest('.log-entry');

    expect(infoLog).toHaveClass('log-info');
    expect(successLog).toHaveClass('log-success');
    expect(errorLog).toHaveClass('log-error');
    expect(warnLog).toHaveClass('log-warn');
  });
});
