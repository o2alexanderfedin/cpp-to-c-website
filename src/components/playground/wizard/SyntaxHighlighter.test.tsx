import { render, screen, waitFor } from '@testing-library/react';
import { SyntaxHighlighter } from './SyntaxHighlighter';

describe('SyntaxHighlighter', () => {
  it('renders code with syntax highlighting', () => {
    const code = 'int main() {\n  return 0;\n}';
    render(<SyntaxHighlighter code={code} language="cpp" />);

    expect(screen.getByText('int')).toBeInTheDocument();
    expect(screen.getByText('main')).toBeInTheDocument();
  });

  it('displays line numbers by default', () => {
    const code = 'lineA\nlineB\nlineC';
    const { container } = render(<SyntaxHighlighter code={code} language="c" />);

    const lineNumbers = container.querySelector('.syntax-line-numbers');
    expect(lineNumbers).toBeInTheDocument();
    expect(lineNumbers?.querySelectorAll('.syntax-line-number').length).toBe(3);
  });

  it('hides line numbers when disabled', () => {
    const code = 'int x = 0;';
    const { container } = render(
      <SyntaxHighlighter code={code} language="c" lineNumbers={false} />
    );

    expect(container.querySelector('.syntax-line-numbers')).not.toBeInTheDocument();
  });

  it('shows loading state for large files', async () => {
    // Create a file with >1000 lines
    const code = Array(1001).fill('int x = 0;').join('\n');
    render(<SyntaxHighlighter code={code} language="c" />);

    // Should show loading initially
    expect(screen.getByText(/Preparing syntax highlighting/i)).toBeInTheDocument();

    // Should render after async delay
    await waitFor(() => {
      expect(screen.queryByText(/Preparing syntax highlighting/i)).not.toBeInTheDocument();
    });
  });

  it('renders small files immediately', () => {
    const code = Array(500).fill('int x = 0;').join('\n');
    render(<SyntaxHighlighter code={code} language="c" />);

    // Should NOT show loading for small files
    expect(screen.queryByText(/Preparing syntax highlighting/i)).not.toBeInTheDocument();
  });

  it('supports C++ language', () => {
    const code = '#include <iostream>';
    const { container } = render(<SyntaxHighlighter code={code} language="cpp" />);

    expect(container.textContent).toContain('#include');
    expect(container.querySelector('.prism-code.language-cpp')).toBeInTheDocument();
  });

  it('supports C language', () => {
    const code = '#include <stdio.h>';
    const { container } = render(<SyntaxHighlighter code={code} language="c" />);

    expect(container.textContent).toContain('#include');
    expect(container.querySelector('.prism-code.language-c')).toBeInTheDocument();
  });

  it('highlights specific lines', () => {
    const code = 'line 1\nline 2\nline 3';
    const { container } = render(
      <SyntaxHighlighter code={code} language="c" highlightLines={[2]} />
    );

    const highlightedLines = container.querySelectorAll('.highlighted');
    expect(highlightedLines.length).toBeGreaterThan(0);
  });

  it('uses showLineNumbers as an alias for lineNumbers', () => {
    const code = 'int x = 0;';
    const { container } = render(
      <SyntaxHighlighter code={code} language="c" showLineNumbers={false} />
    );

    expect(container.querySelector('.syntax-line-numbers')).not.toBeInTheDocument();
  });
});
