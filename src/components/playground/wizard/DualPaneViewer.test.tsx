import { render, screen } from '@testing-library/react';
import { DualPaneViewer } from './DualPaneViewer';
import { vi } from 'vitest';

// Mock react-resizable-panels to avoid CSS parsing issues in jsdom
vi.mock('react-resizable-panels', () => ({
  Group: ({ children, ...props }: any) => <div data-group {...props}>{children}</div>,
  Panel: ({ children, ...props }: any) => <div data-panel {...props}>{children}</div>,
  Separator: ({ children, ...props }: any) => <div data-separator {...props}>{children}</div>,
}));

describe('DualPaneViewer', () => {
  it('renders both source and transpile panes', () => {
    render(
      <DualPaneViewer
        sourceContent="// C++ source"
        transpileContent="// C output"
      />
    );

    expect(screen.getByText('// C++ source')).toBeInTheDocument();
    expect(screen.getByText('// C output')).toBeInTheDocument();
  });

  it('displays filenames in headers', () => {
    render(
      <DualPaneViewer
        sourceContent="source"
        sourceFilename="test.cpp"
        transpileContent="output"
        transpileFilename="test.c"
      />
    );

    expect(screen.getByText('test.cpp')).toBeInTheDocument();
    expect(screen.getByText('test.c')).toBeInTheDocument();
  });

  it('shows empty states when no content', () => {
    render(
      <DualPaneViewer
        sourceContent=""
        transpileContent=""
      />
    );

    expect(screen.getByText('No source file selected')).toBeInTheDocument();
    expect(screen.getByText('No transpiled output')).toBeInTheDocument();
  });

  it('renders resize handle', () => {
    const { container } = render(
      <DualPaneViewer
        sourceContent="source"
        transpileContent="output"
      />
    );

    const handle = container.querySelector('.resize-handle');
    expect(handle).toBeInTheDocument();
  });

  it('applies default layout', () => {
    const { container } = render(
      <DualPaneViewer
        sourceContent="source"
        transpileContent="output"
        defaultLayout={[60, 40]}
      />
    );

    // Verify panels exist (detailed layout testing may require more setup)
    const panels = container.querySelectorAll('[data-panel]');
    expect(panels.length).toBe(2);
  });
});
