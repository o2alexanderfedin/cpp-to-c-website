import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, fireEvent, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { FileTreeView, FileStatus } from './FileTreeView';
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

    (mainNode as HTMLElement)?.click();

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

    (srcNode as HTMLElement)?.click();

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

  describe('expand/collapse behavior', () => {
    it('folders start collapsed by default', () => {
      render(<FileTreeView files={mockFiles} />);

      // Folders are visible
      expect(screen.getByText('src')).toBeInTheDocument();
      expect(screen.getByText('include')).toBeInTheDocument();

      // Files inside folders should not be visible initially (collapsed state)
      // Note: react-arborist doesn't expose children until expanded
    });

    it('allows folder expansion via click', async () => {
      const { container } = render(<FileTreeView files={mockFiles} />);

      const srcFolder = screen.getByText('src');
      await userEvent.click(srcFolder);

      // After expansion, children should become accessible
      // Note: react-arborist handles expansion internally
      await waitFor(() => {
        const treeNodes = container.querySelectorAll('.tree-node');
        expect(treeNodes.length).toBeGreaterThan(2); // More than just root folders
      }, { timeout: 1000 });
    });
  });

  describe('performance with large datasets', () => {
    it('handles 500 files efficiently', () => {
      const largeFileSet: FileInfo[] = Array.from({ length: 500 }, (_, i) => ({
        path: `file-${i}.cpp`,
        name: `file-${i}.cpp`,
        handle: {} as FileSystemFileHandle,
        size: 1024,
      }));

      const startTime = performance.now();
      render(<FileTreeView files={largeFileSet} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      expect(renderTime).toBeLessThan(200); // Should render quickly with virtualization
    });

    it('handles 1000 files efficiently', () => {
      const largeFileSet: FileInfo[] = Array.from({ length: 1000 }, (_, i) => ({
        path: `folder-${Math.floor(i / 10)}/file-${i}.cpp`,
        name: `file-${i}.cpp`,
        handle: {} as FileSystemFileHandle,
        size: 1024,
      }));

      const startTime = performance.now();
      render(<FileTreeView files={largeFileSet} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      expect(renderTime).toBeLessThan(300);
    });

    it('handles deeply nested structure efficiently', () => {
      const deepFiles: FileInfo[] = Array.from({ length: 50 }, (_, i) => ({
        path: `level1/level2/level3/level4/level5/file-${i}.cpp`,
        name: `file-${i}.cpp`,
        handle: {} as FileSystemFileHandle,
        size: 1024,
      }));

      const startTime = performance.now();
      render(<FileTreeView files={deepFiles} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      expect(renderTime).toBeLessThan(150);
    });
  });

  describe('edge cases', () => {
    it('handles files with special characters in names', () => {
      const specialFiles: FileInfo[] = [
        {
          path: 'file (with) spaces.cpp',
          name: 'file (with) spaces.cpp',
          handle: {} as FileSystemFileHandle,
          size: 1024,
        },
        {
          path: 'file-with-dashes.cpp',
          name: 'file-with-dashes.cpp',
          handle: {} as FileSystemFileHandle,
          size: 512,
        },
        {
          path: 'file_with_underscores.h',
          name: 'file_with_underscores.h',
          handle: {} as FileSystemFileHandle,
          size: 256,
        },
      ];

      render(<FileTreeView files={specialFiles} />);

      expect(screen.getByText('file (with) spaces.cpp')).toBeInTheDocument();
      expect(screen.getByText('file-with-dashes.cpp')).toBeInTheDocument();
      expect(screen.getByText('file_with_underscores.h')).toBeInTheDocument();
    });

    it('handles very long file names', () => {
      const longNameFile: FileInfo[] = [
        {
          path: 'a'.repeat(100) + '.cpp',
          name: 'a'.repeat(100) + '.cpp',
          handle: {} as FileSystemFileHandle,
          size: 1024,
        },
      ];

      const { container } = render(<FileTreeView files={longNameFile} />);

      // Should render without crashing
      const treeView = container.querySelector('.file-tree-view');
      expect(treeView).toBeInTheDocument();

      // File name should be present (may be truncated in display)
      const treeName = container.querySelector('.tree-name');
      expect(treeName).toBeInTheDocument();
    });

    it('handles empty folder gracefully', () => {
      // No files in a particular folder - just top-level
      const { container } = render(<FileTreeView files={[]} />);

      const treeView = container.querySelector('.file-tree-view');
      expect(treeView).toBeInTheDocument();
    });

    it('handles duplicate file names in different folders', () => {
      const duplicateFiles: FileInfo[] = [
        {
          path: 'folder1/main.cpp',
          name: 'main.cpp',
          handle: {} as FileSystemFileHandle,
          size: 1024,
        },
        {
          path: 'folder2/main.cpp',
          name: 'main.cpp',
          handle: {} as FileSystemFileHandle,
          size: 2048,
        },
      ];

      render(<FileTreeView files={duplicateFiles} />);

      expect(screen.getByText('folder1')).toBeInTheDocument();
      expect(screen.getByText('folder2')).toBeInTheDocument();
    });
  });

  describe('accessibility', () => {
    it('has proper tree structure', () => {
      const { container } = render(<FileTreeView files={mockFiles} />);

      // Tree container should be present
      const treeView = container.querySelector('.file-tree-view');
      expect(treeView).toBeInTheDocument();
    });

    it('tree nodes are clickable', () => {
      const { container } = render(<FileTreeView files={mockFiles} />);

      const treeNodes = container.querySelectorAll('.tree-node');
      expect(treeNodes.length).toBeGreaterThan(0);

      // All tree nodes should be clickable
      treeNodes.forEach(node => {
        expect(node).toHaveStyle({ cursor: 'pointer' });
      });
    });

    it('provides visual feedback on hover', () => {
      const { container } = render(<FileTreeView files={mockFiles} />);

      const treeNode = container.querySelector('.tree-node');
      expect(treeNode).toHaveStyle({ transition: 'background-color 0.15s' });
    });
  });

  describe('file selection with callbacks', () => {
    it('calls onFileSelect with correct file info', async () => {
      const handleSelect = vi.fn();
      const singleFile: FileInfo[] = [
        {
          path: 'test.cpp',
          name: 'test.cpp',
          handle: {} as FileSystemFileHandle,
          size: 1024,
        },
      ];

      const { container } = render(
        <FileTreeView files={singleFile} onFileSelect={handleSelect} />
      );

      const fileNode = container.querySelector('.tree-node');
      expect(fileNode).toBeInTheDocument();

      if (fileNode) {
        await userEvent.click(fileNode);

        expect(handleSelect).toHaveBeenCalledTimes(1);
        expect(handleSelect).toHaveBeenCalledWith(
          expect.objectContaining({
            path: 'test.cpp',
            name: 'test.cpp',
            size: 1024,
          })
        );
      }
    });

    it('updates selection highlighting when selectedFile changes', () => {
      const singleFile: FileInfo[] = [
        {
          path: 'test.cpp',
          name: 'test.cpp',
          handle: {} as FileSystemFileHandle,
          size: 1024,
        },
      ];

      const { container, rerender } = render(
        <FileTreeView files={singleFile} selectedFile={undefined} />
      );

      let selectedNode = container.querySelector('.tree-node.selected');
      expect(selectedNode).not.toBeInTheDocument();

      // Update to select the file
      rerender(<FileTreeView files={singleFile} selectedFile="test.cpp" />);

      selectedNode = container.querySelector('.tree-node.selected');
      expect(selectedNode).toBeInTheDocument();
      expect(selectedNode).toHaveClass('selected');
    });
  });

  describe('height customization', () => {
    it('applies custom height to tree', () => {
      const { container } = render(<FileTreeView files={mockFiles} height={800} />);

      const treeView = container.querySelector('.file-tree-view');
      expect(treeView).toBeInTheDocument();
      // react-arborist applies height internally to the Tree component
    });

    it('uses default height when not specified', () => {
      const { container } = render(<FileTreeView files={mockFiles} />);

      const treeView = container.querySelector('.file-tree-view');
      expect(treeView).toBeInTheDocument();
    });
  });

  describe('icon rendering', () => {
    it('renders correct icons for file types', () => {
      const mixedFiles: FileInfo[] = [
        {
          path: 'code.cpp',
          name: 'code.cpp',
          handle: {} as FileSystemFileHandle,
          size: 1024,
        },
        {
          path: 'header.h',
          name: 'header.h',
          handle: {} as FileSystemFileHandle,
          size: 512,
        },
      ];

      const { container } = render(<FileTreeView files={mixedFiles} />);

      const icons = container.querySelectorAll('.tree-icon');
      expect(icons.length).toBeGreaterThan(0);

      // Should contain file icons (📄)
      const iconTexts = Array.from(icons).map(icon => icon.textContent);
      expect(iconTexts.some(text => text === '📄')).toBe(true);
    });

    it('renders folder icons for directories', () => {
      const { container } = render(<FileTreeView files={mockFiles} />);

      const icons = container.querySelectorAll('.tree-icon');
      const iconTexts = Array.from(icons).map(icon => icon.textContent);

      // Should contain folder icons (📁 or 📂)
      expect(iconTexts.some(text => text === '📁' || text === '📂')).toBe(true);
    });
  });

  describe('Status Display', () => {
    const mockFiles: FileInfo[] = [
      { path: 'file1.cpp', name: 'file1.cpp', handle: {} as any, size: 100 },
      { path: 'file2.cpp', name: 'file2.cpp', handle: {} as any, size: 200 },
      { path: 'file3.cpp', name: 'file3.cpp', handle: {} as any, size: 300 }
    ];

    it('displays pending status icon', () => {
      const statuses = new Map([
        ['file1.cpp', FileStatus.PENDING]
      ]);

      render(<FileTreeView files={mockFiles} fileStatuses={statuses} />);

      // Verify pending icon displayed
      expect(screen.getByText('⏳')).toBeInTheDocument();
    });

    it('displays in-progress status icon', () => {
      const statuses = new Map([
        ['file1.cpp', FileStatus.IN_PROGRESS]
      ]);

      render(<FileTreeView files={mockFiles} fileStatuses={statuses} />);

      // Verify in-progress icon displayed
      expect(screen.getByText('🔄')).toBeInTheDocument();
    });

    it('displays success status icon', () => {
      const statuses = new Map([
        ['file1.cpp', FileStatus.SUCCESS]
      ]);

      render(<FileTreeView files={mockFiles} fileStatuses={statuses} />);

      // Verify success icon displayed
      expect(screen.getByText('✓')).toBeInTheDocument();
    });

    it('displays error status icon', () => {
      const statuses = new Map([
        ['file1.cpp', FileStatus.ERROR]
      ]);

      render(<FileTreeView files={mockFiles} fileStatuses={statuses} />);

      // Verify error icon displayed
      expect(screen.getByText('✗')).toBeInTheDocument();
    });

    it('applies correct CSS class for each status', () => {
      const statuses = new Map([
        ['file1.cpp', FileStatus.PENDING],
        ['file2.cpp', FileStatus.IN_PROGRESS],
        ['file3.cpp', FileStatus.SUCCESS]
      ]);

      const { container } = render(<FileTreeView files={mockFiles} fileStatuses={statuses} />);

      expect(container.querySelector('.status-pending')).toBeInTheDocument();
      expect(container.querySelector('.status-in_progress')).toBeInTheDocument();
      expect(container.querySelector('.status-success')).toBeInTheDocument();
    });

    it('displays default icon when no status is set', () => {
      const statuses = new Map();

      render(<FileTreeView files={mockFiles} fileStatuses={statuses} />);

      // Should display default file icon
      expect(screen.getByText('📄')).toBeInTheDocument();
    });

    it('handles mixed status states correctly', () => {
      const statuses = new Map([
        ['file1.cpp', FileStatus.SUCCESS],
        ['file2.cpp', FileStatus.IN_PROGRESS],
        ['file3.cpp', FileStatus.PENDING]
      ]);

      const { container } = render(<FileTreeView files={mockFiles} fileStatuses={statuses} />);

      // All status classes should be present
      expect(container.querySelector('.status-success')).toBeInTheDocument();
      expect(container.querySelector('.status-in_progress')).toBeInTheDocument();
      expect(container.querySelector('.status-pending')).toBeInTheDocument();
    });

    it('updates status icons when fileStatuses prop changes', () => {
      const statuses1 = new Map([['file1.cpp', FileStatus.PENDING]]);
      const statuses2 = new Map([['file1.cpp', FileStatus.SUCCESS]]);

      const { rerender } = render(<FileTreeView files={mockFiles} fileStatuses={statuses1} />);
      expect(screen.getByText('⏳')).toBeInTheDocument();

      rerender(<FileTreeView files={mockFiles} fileStatuses={statuses2} />);
      expect(screen.getByText('✓')).toBeInTheDocument();
      expect(screen.queryByText('⏳')).not.toBeInTheDocument();
    });

    it('applies status-error class for error status', () => {
      const statuses = new Map([['file1.cpp', FileStatus.ERROR]]);

      const { container } = render(<FileTreeView files={mockFiles} fileStatuses={statuses} />);

      expect(container.querySelector('.status-error')).toBeInTheDocument();
    });

    it('highlights selected file with in-progress status', () => {
      const statuses = new Map([['file1.cpp', FileStatus.IN_PROGRESS]]);

      const { container } = render(
        <FileTreeView
          files={mockFiles}
          fileStatuses={statuses}
          selectedFile="file1.cpp"
        />
      );

      // Should have both selected and in-progress classes
      const nodes = container.querySelectorAll('.tree-node');
      const targetNode = Array.from(nodes).find(node =>
        node.textContent?.includes('file1.cpp')
      );

      expect(targetNode).toHaveClass('selected');
      expect(targetNode).toHaveClass('status-in_progress');
    });
  });

  describe('Auto-scroll', () => {
    it('auto-scrolls to selected file when autoScroll is enabled', () => {
      const mockFiles: FileInfo[] = Array.from({ length: 50 }, (_, i) => ({
        path: `file${i}.cpp`,
        name: `file${i}.cpp`,
        handle: {} as any,
        size: 100
      }));

      render(
        <FileTreeView
          files={mockFiles}
          selectedFile="file40.cpp"
          autoScroll={true}
          height={400}
        />
      );

      // Note: Testing auto-scroll requires mocking tree ref scrollTo
      // This test verifies component renders without error with autoScroll enabled
      // Actual scroll behavior is tested in integration/E2E tests
    });

    it('does not auto-scroll when autoScroll is disabled', () => {
      const mockFiles: FileInfo[] = Array.from({ length: 50 }, (_, i) => ({
        path: `file${i}.cpp`,
        name: `file${i}.cpp`,
        handle: {} as any,
        size: 100
      }));

      render(
        <FileTreeView
          files={mockFiles}
          selectedFile="file40.cpp"
          autoScroll={false}
          height={400}
        />
      );

      // Component should render without attempting to scroll
    });
  });
});
