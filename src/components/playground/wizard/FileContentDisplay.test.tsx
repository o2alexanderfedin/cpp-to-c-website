import { render, screen } from '@testing-library/react';
import { FileContentDisplay } from './FileContentDisplay';

describe('FileContentDisplay', () => {
  it('renders file content with line numbers', () => {
    const content = 'lineA\nlineB\nlineC';
    const { container } = render(<FileContentDisplay content={content} />);

    // Check that content is in the document
    expect(container.textContent).toContain('lineA');
    expect(container.textContent).toContain('lineB');
    expect(container.textContent).toContain('lineC');

    // Check line numbers
    const lineNumbers = container.querySelector('.syntax-line-numbers');
    expect(lineNumbers).toBeInTheDocument();
    expect(lineNumbers?.querySelectorAll('.syntax-line-number').length).toBe(3);
  });

  it('displays filename in header', () => {
    render(
      <FileContentDisplay
        content="test"
        filename="example.cpp"
      />
    );

    expect(screen.getByText('example.cpp')).toBeInTheDocument();
  });

  it('displays language badge', () => {
    render(
      <FileContentDisplay
        content="test"
        filename="test.cpp"
        language="cpp"
      />
    );

    expect(screen.getByText('CPP')).toBeInTheDocument();
  });

  it('shows empty state when no content', () => {
    render(<FileContentDisplay content="" />);

    expect(screen.getByText('No file selected')).toBeInTheDocument();
  });

  it('shows custom empty message', () => {
    render(
      <FileContentDisplay
        content=""
        emptyMessage="Custom message"
      />
    );

    expect(screen.getByText('Custom message')).toBeInTheDocument();
  });

  it('renders without line numbers when disabled', () => {
    const content = 'line 1\nline 2';
    const { container } = render(
      <FileContentDisplay content={content} lineNumbers={false} />
    );

    // With syntax highlighting enabled, it uses .syntax-line-numbers
    expect(container.querySelector('.syntax-line-numbers')).not.toBeInTheDocument();
  });

  it('handles single line content', () => {
    const { container } = render(<FileContentDisplay content="single line" />);

    expect(container.textContent).toContain('single line');
    // Check there's one line number
    const lineNumbers = container.querySelector('.syntax-line-numbers');
    expect(lineNumbers?.querySelectorAll('.syntax-line-number').length).toBe(1);
  });

  it('handles empty lines in content', () => {
    const content = 'lineA\n\nlineC';
    const { container } = render(<FileContentDisplay content={content} />);

    // Should have 3 line numbers
    const lineNumbers = container.querySelector('.syntax-line-numbers');
    expect(lineNumbers?.querySelectorAll('.syntax-line-number').length).toBe(3);
  });

  // New tests for syntax highlighting integration
  it('uses syntax highlighting by default', () => {
    const code = 'int main() { return 0; }';
    const { container } = render(<FileContentDisplay content={code} language="cpp" />);

    // Should render SyntaxHighlighter (check for syntax-highlighter class)
    expect(container.querySelector('.syntax-highlighter')).toBeInTheDocument();
  });

  it('disables syntax highlighting when prop is false', () => {
    const code = 'int main() { return 0; }';
    const { container } = render(
      <FileContentDisplay
        content={code}
        language="cpp"
        enableSyntaxHighlighting={false}
      />
    );

    // Should use plain text rendering
    expect(container.querySelector('.syntax-highlighter')).not.toBeInTheDocument();
    expect(container.querySelector('.file-content-code')).toBeInTheDocument();
  });

  it('passes language prop to SyntaxHighlighter', () => {
    const code = '#include <stdio.h>';
    const { container } = render(
      <FileContentDisplay content={code} language="c" />
    );

    expect(container.querySelector('.prism-code.language-c')).toBeInTheDocument();
  });

  it('passes lineNumbers prop to SyntaxHighlighter', () => {
    const code = 'int x = 0;';
    const { container } = render(
      <FileContentDisplay content={code} lineNumbers={false} />
    );

    // When syntax highlighting is enabled and lineNumbers is false
    expect(container.querySelector('.syntax-line-numbers')).not.toBeInTheDocument();
  });
});
