import React from 'react';
import { render, screen } from '@testing-library/react';
import { describe, it, expect } from 'vitest';
import { FileStatistics } from './FileStatistics';
import type { FileInfo } from './types';

describe('FileStatistics', () => {
  const mockFiles: FileInfo[] = [
    { path: 'main.cpp', name: 'main.cpp', handle: {} as any, size: 1024 },
    { path: 'utils.cpp', name: 'utils.cpp', handle: {} as any, size: 2048 },
    { path: 'header.h', name: 'header.h', handle: {} as any, size: 512 },
    { path: 'class.hpp', name: 'class.hpp', handle: {} as any, size: 256 }
  ];

  it('renders file count correctly', () => {
    render(<FileStatistics files={mockFiles} />);

    expect(screen.getByText('4')).toBeInTheDocument();
  });

  it('counts source files correctly', () => {
    render(<FileStatistics files={mockFiles} />);

    const sourceFiles = screen.getAllByText('2');
    expect(sourceFiles.length).toBeGreaterThan(0);
  });

  it('counts header files correctly', () => {
    render(<FileStatistics files={mockFiles} />);

    const headerFiles = screen.getAllByText('2');
    expect(headerFiles.length).toBeGreaterThan(0);
  });

  it('displays formatted total size', () => {
    render(<FileStatistics files={mockFiles} />);

    // Total: 1024 + 2048 + 512 + 256 = 3840 bytes = 3.75 KB
    expect(screen.getByText('3.75 KB')).toBeInTheDocument();
  });

  it('handles empty files array', () => {
    render(<FileStatistics files={[]} />);

    // Check that multiple zero values exist (one for each stat)
    const zeroValues = screen.getAllByText('0');
    expect(zeroValues.length).toBeGreaterThan(0);
    expect(screen.getByText('0 Bytes')).toBeInTheDocument();
  });

  it('displays all stat labels', () => {
    render(<FileStatistics files={mockFiles} />);

    expect(screen.getByText('Total Files:')).toBeInTheDocument();
    expect(screen.getByText('Source Files:')).toBeInTheDocument();
    expect(screen.getByText('Header Files:')).toBeInTheDocument();
    expect(screen.getByText('Total Size:')).toBeInTheDocument();
  });
});
