import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { DownloadOptions } from './DownloadOptions';
import type { TranspileResult } from './types';
import * as downloadHelpers from './utils/downloadHelpers';

// Mock the download helpers
vi.mock('./utils/downloadHelpers', () => ({
  downloadFile: vi.fn(),
  createZipArchive: vi.fn(),
  downloadZip: vi.fn(),
  calculateTotalBytes: vi.fn(),
  formatBytes: vi.fn((bytes: number) => `${bytes} Bytes`),
}));

describe('DownloadOptions', () => {
  const mockResults = new Map<string, TranspileResult>([
    ['src/main.cpp', { success: true, cCode: 'int main() { return 0; }' }],
    ['src/utils.cpp', { success: true, cCode: 'void foo() {}' }],
    ['src/error.cpp', { success: false, error: 'Parse error' }],
  ]);

  beforeEach(() => {
    vi.clearAllMocks();
    // Mock calculateTotalBytes to return a predictable value
    vi.mocked(downloadHelpers.calculateTotalBytes).mockReturnValue(1024);
  });

  it('renders metrics correctly', () => {
    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile={null}
        selectedFileContent=""
        elapsedTime={5000}
        targetDirSelected={false}
      />
    );

    expect(screen.getByText(/Transpilation Summary/i)).toBeInTheDocument();
    expect(screen.getByText('2')).toBeInTheDocument(); // 2 successful files
    expect(screen.getByText(/File.*Transpiled/i)).toBeInTheDocument();
    expect(screen.getByText('1024 Bytes')).toBeInTheDocument(); // formatted bytes
    expect(screen.getByText('5.0s')).toBeInTheDocument(); // elapsed time
  });

  it('renders plural "Files" when multiple files transpiled', () => {
    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile={null}
        selectedFileContent=""
      />
    );

    expect(screen.getByText(/Files Transpiled/i)).toBeInTheDocument();
  });

  it('renders singular "File" when one file transpiled', () => {
    const singleResult = new Map<string, TranspileResult>([
      ['src/main.cpp', { success: true, cCode: 'int main() {}' }],
    ]);

    render(
      <DownloadOptions
        transpilationResults={singleResult}
        selectedFile={null}
        selectedFileContent=""
      />
    );

    expect(screen.getByText(/File Transpiled/i)).toBeInTheDocument();
    expect(screen.queryByText(/Files Transpiled/i)).not.toBeInTheDocument();
  });

  it('shows target directory info message when targetDirSelected is true', () => {
    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile={null}
        selectedFileContent=""
        targetDirSelected={true}
      />
    );

    expect(screen.getByText(/Files have been written to your target directory/i)).toBeInTheDocument();
  });

  it('does not show target directory info message when targetDirSelected is false', () => {
    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile={null}
        selectedFileContent=""
        targetDirSelected={false}
      />
    );

    expect(screen.queryByText(/Files have been written to your target directory/i)).not.toBeInTheDocument();
  });

  it('renders "Download All as ZIP" button', () => {
    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile={null}
        selectedFileContent=""
      />
    );

    expect(screen.getByText(/Download All as ZIP/i)).toBeInTheDocument();
  });

  it('calls createZipArchive and downloadZip when "Download All as ZIP" is clicked', async () => {
    const user = userEvent.setup();
    const mockZipBlob = new Blob(['mock zip'], { type: 'application/zip' });
    vi.mocked(downloadHelpers.createZipArchive).mockResolvedValue(mockZipBlob);

    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile={null}
        selectedFileContent=""
      />
    );

    const zipButton = screen.getByText(/Download All as ZIP/i);
    await user.click(zipButton);

    await waitFor(() => {
      expect(downloadHelpers.createZipArchive).toHaveBeenCalledWith(mockResults);
    });

    await waitFor(() => {
      expect(downloadHelpers.downloadZip).toHaveBeenCalledWith(mockZipBlob, 'transpiled-files.zip');
    });
  });

  it('shows loading state while creating ZIP', async () => {
    const user = userEvent.setup();
    let resolveZip: (blob: Blob) => void;
    const zipPromise = new Promise<Blob>((resolve) => {
      resolveZip = resolve;
    });
    vi.mocked(downloadHelpers.createZipArchive).mockReturnValue(zipPromise);

    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile={null}
        selectedFileContent=""
      />
    );

    const zipButton = screen.getByText(/Download All as ZIP/i);
    await user.click(zipButton);

    // Should show loading state
    expect(screen.getByText(/Creating ZIP\.\.\./i)).toBeInTheDocument();

    // Resolve the promise
    resolveZip!(new Blob(['mock']));

    // Should return to normal state
    await waitFor(() => {
      expect(screen.queryByText(/Creating ZIP\.\.\./i)).not.toBeInTheDocument();
      expect(screen.getByText(/Download All as ZIP/i)).toBeInTheDocument();
    });
  });

  it('disables "Download All as ZIP" button when no successful files', () => {
    const failedResults = new Map<string, TranspileResult>([
      ['src/error1.cpp', { success: false, error: 'Error 1' }],
      ['src/error2.cpp', { success: false, error: 'Error 2' }],
    ]);

    render(
      <DownloadOptions
        transpilationResults={failedResults}
        selectedFile={null}
        selectedFileContent=""
      />
    );

    const zipButton = screen.getByText(/Download All as ZIP/i);
    expect(zipButton).toBeDisabled();
  });

  it('renders "Download Current File" button when file is selected', () => {
    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile="src/main.cpp"
        selectedFileContent="int main() { return 0; }"
      />
    );

    expect(screen.getByText(/Download main\.cpp/i)).toBeInTheDocument();
  });

  it('does not render "Download Current File" button when no file is selected', () => {
    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile={null}
        selectedFileContent=""
      />
    );

    // Should only have "Download All as ZIP" button, not individual file download button
    expect(screen.getByText(/Download All as ZIP/i)).toBeInTheDocument();
    expect(screen.queryByRole('button', { name: /Download.*\.(cpp|c)/i })).not.toBeInTheDocument();
  });

  it('calls downloadFile when "Download Current File" is clicked', async () => {
    const user = userEvent.setup();

    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile="src/main.cpp"
        selectedFileContent="int main() { return 0; }"
      />
    );

    const fileButton = screen.getByText(/Download main\.cpp/i);
    await user.click(fileButton);

    expect(downloadHelpers.downloadFile).toHaveBeenCalledWith(
      'src/main.c', // Note: .cpp converted to .c
      'int main() { return 0; }'
    );
  });

  it('converts .cpp to .c when downloading current file', async () => {
    const user = userEvent.setup();

    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile="test.cpp"
        selectedFileContent="void test() {}"
      />
    );

    const fileButton = screen.getByText(/Download test\.cpp/i);
    await user.click(fileButton);

    expect(downloadHelpers.downloadFile).toHaveBeenCalledWith(
      'test.c',
      'void test() {}'
    );
  });

  it('converts .hpp to .h when downloading current file', async () => {
    const user = userEvent.setup();

    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile="header.hpp"
        selectedFileContent="#ifndef HEADER_H"
      />
    );

    const fileButton = screen.getByText(/Download header\.hpp/i);
    await user.click(fileButton);

    expect(downloadHelpers.downloadFile).toHaveBeenCalledWith(
      'header.h',
      '#ifndef HEADER_H'
    );
  });

  it('disables "Download Current File" button when no content available', () => {
    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile="src/main.cpp"
        selectedFileContent=""
      />
    );

    const fileButton = screen.getByText(/Download main\.cpp/i);
    expect(fileButton).toBeDisabled();
  });

  it('handles ZIP creation error gracefully', async () => {
    const user = userEvent.setup();
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
    const alertSpy = vi.spyOn(window, 'alert').mockImplementation(() => {});

    vi.mocked(downloadHelpers.createZipArchive).mockRejectedValue(new Error('ZIP creation failed'));

    render(
      <DownloadOptions
        transpilationResults={mockResults}
        selectedFile={null}
        selectedFileContent=""
      />
    );

    const zipButton = screen.getByText(/Download All as ZIP/i);
    await user.click(zipButton);

    await waitFor(() => {
      expect(consoleErrorSpy).toHaveBeenCalledWith('Failed to create ZIP:', expect.any(Error));
    });

    await waitFor(() => {
      expect(alertSpy).toHaveBeenCalledWith('Failed to create ZIP archive. Please try again.');
    });

    consoleErrorSpy.mockRestore();
    alertSpy.mockRestore();
  });
});
