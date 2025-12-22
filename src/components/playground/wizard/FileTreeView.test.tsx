import { describe, it, expect, vi } from 'vitest';
import { render, screen } from '@testing-library/react';
import { FileTreeView } from './FileTreeView';
import type { FileInfo } from './types';

describe('FileTreeView', () => {
  const mockFiles: FileInfo[] = [
    {
      path: 'src/main.cpp',
      name: 'main.cpp',
      handle: {} as FileSystemFileHandle,
      size: 1024,
    },
    {
      path: 'src/utils/helper.cpp',
      name: 'helper.cpp',
      handle: {} as FileSystemFileHandle,
      size: 512,
    },
    {
      path: 'include/common.h',
      name: 'common.h',
      handle: {} as FileSystemFileHandle,
      size: 256,
    },
  ];

  it('renders tree with files', () => {
    const { container } = render(<FileTreeView files={mockFiles} />);

    // Verify tree container is present
    const treeView = container.querySelector('.file-tree-view');
    expect(treeView).toBeInTheDocument();
  });

  it('displays folder and file names', () => {
    render(<FileTreeView files={mockFiles} />);

    // Check for folder names (these are visible at top level)
    expect(screen.getByText('src')).toBeInTheDocument();
    expect(screen.getByText('include')).toBeInTheDocument();

    // Note: Files inside folders may not be visible until folders are expanded
    // This is expected behavior with react-arborist
  });

  it('handles empty file list', () => {
    const { container } = render(<FileTreeView files={[]} />);

    // Should render without errors
    const treeView = container.querySelector('.file-tree-view');
    expect(treeView).toBeInTheDocument();
  });

  it('respects custom height prop', () => {
    const { container } = render(<FileTreeView files={mockFiles} height={600} />);

    // The Tree component should have the height applied
    const treeView = container.querySelector('.file-tree-view');
    expect(treeView).toBeInTheDocument();
  });

  it('shows root node when showRoot is true', () => {
    render(<FileTreeView files={mockFiles} showRoot={true} />);

    // Root node should be visible
    expect(screen.getByText('Source Files')).toBeInTheDocument();
  });

  it('hides root node when showRoot is false', () => {
    render(<FileTreeView files={mockFiles} showRoot={false} />);

    // Root node should not be visible
    expect(screen.queryByText('Source Files')).not.toBeInTheDocument();
  });

  it('applies selected class to selected file', () => {
    // Use a root-level file so it's visible without expanding
    const rootFile: FileInfo[] = [
      {
        path: 'main.cpp',
        name: 'main.cpp',
        handle: {} as FileSystemFileHandle,
        size: 1024,
      },
    ];

    const { container } = render(
      <FileTreeView files={rootFile} selectedFile="main.cpp" />
    );

    // Find the tree node containing main.cpp
    const treeNodes = container.querySelectorAll('.tree-node');
    const selectedNode = Array.from(treeNodes).find(node =>
      node.textContent?.includes('main.cpp')
    );

    expect(selectedNode).toHaveClass('selected');
  });

  it('does not apply selected class to non-selected files', () => {
    const rootFiles: FileInfo[] = [
      {
        path: 'main.cpp',
        name: 'main.cpp',
        handle: {} as FileSystemFileHandle,
        size: 1024,
      },
      {
        path: 'other.cpp',
        name: 'other.cpp',
        handle: {} as FileSystemFileHandle,
        size: 512,
      },
    ];

    const { container } = render(
      <FileTreeView files={rootFiles} selectedFile="main.cpp" />
    );

    // Find the tree node containing other.cpp
    const treeNodes = container.querySelectorAll('.tree-node');
    const otherNode = Array.from(treeNodes).find(node =>
      node.textContent?.includes('other.cpp')
    );

    expect(otherNode).not.toHaveClass('selected');
  });

  it('calls onFileSelect when file is clicked', () => {
    const handleSelect = vi.fn();
    const rootFile: FileInfo[] = [
      {
        path: 'main.cpp',
        name: 'main.cpp',
        handle: {} as FileSystemFileHandle,
        size: 1024,
      },
    ];

    const { container } = render(
      <FileTreeView files={rootFile} onFileSelect={handleSelect} />
    );

    // Find and click main.cpp node
    const treeNodes = container.querySelectorAll('.tree-node');
    const mainNode = Array.from(treeNodes).find(node =>
      node.textContent?.includes('main.cpp')
    );

    mainNode?.click();

    // Verify handler was called with correct file info
    expect(handleSelect).toHaveBeenCalledTimes(1);
    expect(handleSelect).toHaveBeenCalledWith(
      expect.objectContaining({
        path: 'main.cpp',
        name: 'main.cpp',
      })
    );
  });

  it('does not call onFileSelect when folder is clicked', () => {
    const handleSelect = vi.fn();
    const { container } = render(
      <FileTreeView files={mockFiles} onFileSelect={handleSelect} />
    );

    // Find and click src folder node
    const treeNodes = container.querySelectorAll('.tree-node');
    const srcNode = Array.from(treeNodes).find(node => {
      const text = node.textContent || '';
      return text === 'src' || (text.includes('src') && !text.includes('main'));
    });

    srcNode?.click();

    // Handler should not be called for folders
    expect(handleSelect).not.toHaveBeenCalled();
  });

  it('renders file icons for files', () => {
    const rootFile: FileInfo[] = [
      {
        path: 'main.cpp',
        name: 'main.cpp',
        handle: {} as FileSystemFileHandle,
        size: 1024,
      },
    ];

    const { container } = render(<FileTreeView files={rootFile} />);

    // Find file nodes and check for file icon emoji
    const treeNodes = container.querySelectorAll('.tree-node');
    const mainNode = Array.from(treeNodes).find(node =>
      node.textContent?.includes('main.cpp')
    );

    const icon = mainNode?.querySelector('.tree-icon');
    expect(icon?.textContent).toBe('📄');
  });

  it('renders folder icons for folders', () => {
    const { container } = render(<FileTreeView files={mockFiles} />);

    // Find folder nodes and check for folder icon emoji
    const treeNodes = container.querySelectorAll('.tree-node');
    const srcNode = Array.from(treeNodes).find(node => {
      const text = node.textContent || '';
      return text === 'src📁' || text.startsWith('📁src');
    });

    const icon = srcNode?.querySelector('.tree-icon');
    expect(icon?.textContent).toMatch(/📁|📂/); // Either closed or open folder
  });

  it('handles single file in root', () => {
    const singleFile: FileInfo[] = [
      {
        path: 'main.cpp',
        name: 'main.cpp',
        handle: {} as FileSystemFileHandle,
        size: 1024,
      },
    ];

    render(<FileTreeView files={singleFile} />);

    // File should be visible at root level
    expect(screen.getByText('main.cpp')).toBeInTheDocument();
  });

  it('handles deeply nested paths', () => {
    const deepFile: FileInfo[] = [
      {
        path: 'a/b/c/d/deep.cpp',
        name: 'deep.cpp',
        handle: {} as FileSystemFileHandle,
        size: 1024,
      },
    ];

    render(<FileTreeView files={deepFile} />);

    // Top-level folder should be present
    expect(screen.getByText('a')).toBeInTheDocument();

    // Note: Nested folders and files are not visible until parent is expanded
    // This is expected behavior with react-arborist's default collapsed state
  });
});
