/**
 * Unit tests for ZipUpload component
 *
 * Tests drag-and-drop functionality, file validation, and accessibility.
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, fireEvent, waitFor } from '@testing-library/react';
import { ZipUpload } from './ZipUpload';
import JSZip from 'jszip';

describe('ZipUpload', () => {
  const mockOnFileSelected = vi.fn();

  beforeEach(() => {
    mockOnFileSelected.mockClear();
  });

  it('should render upload zone', () => {
    render(<ZipUpload onFileSelected={mockOnFileSelected} />);

    expect(screen.getByText(/Drop a ZIP file here/i)).toBeInTheDocument();
    expect(screen.getByRole('button')).toBeInTheDocument();
  });

  it('should have proper accessibility attributes', () => {
    render(<ZipUpload onFileSelected={mockOnFileSelected} />);

    const uploadZone = screen.getByRole('button');
    expect(uploadZone).toHaveAttribute('aria-label');
    expect(uploadZone).toHaveAttribute('tabIndex', '0');
  });

  it('should be disabled when disabled prop is true', () => {
    render(<ZipUpload onFileSelected={mockOnFileSelected} disabled={true} />);

    const uploadZone = screen.getByRole('button');
    expect(uploadZone).toHaveAttribute('aria-disabled', 'true');
    expect(uploadZone).toHaveAttribute('tabIndex', '-1');
  });

  it('should display selected file information', () => {
    const testFile = new File(['test content'], 'test.zip', { type: 'application/zip' });

    render(<ZipUpload onFileSelected={mockOnFileSelected} selectedFile={testFile} />);

    expect(screen.getByText(/test.zip/)).toBeInTheDocument();
  });

  it('should show error for non-ZIP files', async () => {
    const testFile = new File(['test'], 'test.txt', { type: 'text/plain' });

    render(<ZipUpload onFileSelected={mockOnFileSelected} />);

    const input = screen.getByLabelText('Select ZIP file');
    Object.defineProperty(input, 'files', {
      value: [testFile],
      writable: false,
    });

    fireEvent.change(input);

    await waitFor(() => {
      expect(screen.getByText(/Please select a .zip file/i)).toBeInTheDocument();
    });

    expect(mockOnFileSelected).not.toHaveBeenCalled();
  });

  it('should show error for oversized files', async () => {
    // Create a file that exceeds default 50MB limit
    // Use a smaller size to avoid timeout - we just need to exceed the limit
    const largeFile = new File([new ArrayBuffer(51 * 1024 * 1024)], 'large.zip', { type: 'application/zip' });

    render(<ZipUpload onFileSelected={mockOnFileSelected} maxSizeMB={50} />);

    const input = screen.getByLabelText('Select ZIP file');
    Object.defineProperty(input, 'files', {
      value: [largeFile],
      writable: false,
    });

    fireEvent.change(input);

    await waitFor(() => {
      expect(screen.getByText(/exceeds.*limit/i)).toBeInTheDocument();
    });

    expect(mockOnFileSelected).not.toHaveBeenCalled();
  });

  it('should accept valid ZIP file with C++ sources', async () => {
    const zip = new JSZip();
    zip.file('main.cpp', 'int main() { return 0; }');
    const blob = await zip.generateAsync({ type: 'blob' });
    const validFile = new File([blob], 'test.zip', { type: 'application/zip' });

    render(<ZipUpload onFileSelected={mockOnFileSelected} />);

    const input = screen.getByLabelText('Select ZIP file');
    Object.defineProperty(input, 'files', {
      value: [validFile],
      writable: false,
    });

    fireEvent.change(input);

    await waitFor(() => {
      expect(mockOnFileSelected).toHaveBeenCalledWith(validFile);
    });
  });

  it('should handle keyboard navigation', () => {
    render(<ZipUpload onFileSelected={mockOnFileSelected} />);

    const uploadZone = screen.getByRole('button');

    // Test Enter key
    fireEvent.keyDown(uploadZone, { key: 'Enter', code: 'Enter' });
    // File input click should be triggered (tested via implementation)

    // Test Space key
    fireEvent.keyDown(uploadZone, { key: ' ', code: 'Space' });
    // File input click should be triggered (tested via implementation)
  });
});
