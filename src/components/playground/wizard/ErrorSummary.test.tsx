import { describe, it, expect, vi } from 'vitest';
import { render, screen } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { ErrorSummary } from './ErrorSummary';
import type { TranspileResult } from './types';

describe('ErrorSummary', () => {
  const mockOnFileSelect = vi.fn();

  it('returns null when there are no errors', () => {
    const results = new Map<string, TranspileResult>([
      ['src/main.cpp', { success: true, cCode: 'int main() {}' }],
      ['src/utils.cpp', { success: true, cCode: 'void foo() {}' }],
    ]);

    const { container } = render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    expect(container.firstChild).toBeNull();
  });

  it('displays error count in header', () => {
    const results = new Map<string, TranspileResult>([
      ['src/error1.cpp', { success: false, error: 'Parse error' }],
      ['src/error2.cpp', { success: false, error: 'Syntax error' }],
      ['src/success.cpp', { success: true, cCode: 'int main() {}' }],
    ]);

    render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    expect(screen.getByText(/Transpilation Errors \(2\)/i)).toBeInTheDocument();
  });

  it('displays error file paths as clickable links', () => {
    const results = new Map<string, TranspileResult>([
      ['src/error.cpp', { success: false, error: 'Parse error' }],
    ]);

    render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    const fileLink = screen.getByText('src/error.cpp');
    expect(fileLink).toBeInTheDocument();
    expect(fileLink.tagName).toBe('BUTTON');
  });

  it('calls onFileSelect when error file link is clicked', async () => {
    const user = userEvent.setup();
    const results = new Map<string, TranspileResult>([
      ['src/error.cpp', { success: false, error: 'Parse error' }],
    ]);

    render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    const fileLink = screen.getByText('src/error.cpp');
    await user.click(fileLink);

    expect(mockOnFileSelect).toHaveBeenCalledWith('src/error.cpp');
  });

  it('displays error messages', () => {
    const results = new Map<string, TranspileResult>([
      ['src/error.cpp', { success: false, error: 'Parse error at line 10' }],
    ]);

    render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    expect(screen.getByText('Parse error at line 10')).toBeInTheDocument();
  });

  it('displays "Unknown error" when error message is missing', () => {
    const results = new Map<string, TranspileResult>([
      ['src/error.cpp', { success: false }],
    ]);

    render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    expect(screen.getByText('Unknown error')).toBeInTheDocument();
  });

  it('displays diagnostics when available', () => {
    const results = new Map<string, TranspileResult>([
      [
        'src/error.cpp',
        {
          success: false,
          error: 'Parse error',
          diagnostics: [
            'Expected semicolon at line 5',
            'Undeclared identifier at line 10',
          ],
        },
      ],
    ]);

    render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    expect(screen.getByText(/View diagnostics \(2\)/i)).toBeInTheDocument();
  });

  it('expands diagnostics when details element is clicked', async () => {
    const user = userEvent.setup();
    const results = new Map<string, TranspileResult>([
      [
        'src/error.cpp',
        {
          success: false,
          error: 'Parse error',
          diagnostics: [
            'Expected semicolon at line 5',
            'Undeclared identifier at line 10',
          ],
        },
      ],
    ]);

    render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    const summary = screen.getByText(/View diagnostics \(2\)/i);
    await user.click(summary);

    expect(screen.getByText('Expected semicolon at line 5')).toBeVisible();
    expect(screen.getByText('Undeclared identifier at line 10')).toBeVisible();
  });

  it('does not display diagnostics section when diagnostics array is empty', () => {
    const results = new Map<string, TranspileResult>([
      ['src/error.cpp', { success: false, error: 'Parse error', diagnostics: [] }],
    ]);

    render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    expect(screen.queryByText(/View diagnostics/i)).not.toBeInTheDocument();
  });

  it('does not display diagnostics section when diagnostics is undefined', () => {
    const results = new Map<string, TranspileResult>([
      ['src/error.cpp', { success: false, error: 'Parse error' }],
    ]);

    render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    expect(screen.queryByText(/View diagnostics/i)).not.toBeInTheDocument();
  });

  it('displays multiple errors correctly', () => {
    const results = new Map<string, TranspileResult>([
      ['src/error1.cpp', { success: false, error: 'Parse error 1' }],
      ['src/error2.cpp', { success: false, error: 'Parse error 2' }],
      ['src/error3.cpp', { success: false, error: 'Parse error 3' }],
    ]);

    render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    expect(screen.getByText('src/error1.cpp')).toBeInTheDocument();
    expect(screen.getByText('src/error2.cpp')).toBeInTheDocument();
    expect(screen.getByText('src/error3.cpp')).toBeInTheDocument();
    expect(screen.getByText('Parse error 1')).toBeInTheDocument();
    expect(screen.getByText('Parse error 2')).toBeInTheDocument();
    expect(screen.getByText('Parse error 3')).toBeInTheDocument();
  });

  it('renders with warning icon emoji', () => {
    const results = new Map<string, TranspileResult>([
      ['src/error.cpp', { success: false, error: 'Parse error' }],
    ]);

    render(
      <ErrorSummary
        transpilationResults={results}
        onFileSelect={mockOnFileSelect}
      />
    );

    // Look for the warning icon (emoji character)
    expect(screen.getByText(/⚠️/)).toBeInTheDocument();
  });
});
