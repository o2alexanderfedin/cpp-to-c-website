/**
 * Unit tests for TranspilerOptions component
 *
 * Tests option controls, callbacks, and accessibility.
 */

import { describe, it, expect, vi } from 'vitest';
import { render, screen, fireEvent } from '@testing-library/react';
import { TranspilerOptionsComponent } from './TranspilerOptions';
import type { TranspilerOptions } from '../../lib/playground/idbfs-types';

describe('TranspilerOptions', () => {
  const defaultOptions: TranspilerOptions = {
    generateACSL: false,
    usePragmaOnce: true,
    enableExceptions: true,
    enableRTTI: true,
    cppStandard: 'c++17',
  };

  it('should render all option controls', () => {
    const mockOnChange = vi.fn();
    render(<TranspilerOptionsComponent options={defaultOptions} onChange={mockOnChange} />);

    expect(screen.getByLabelText(/Generate ACSL/i)).toBeInTheDocument();
    expect(screen.getByLabelText(/pragma once/i)).toBeInTheDocument();
    expect(screen.getByLabelText(/Enable exceptions/i)).toBeInTheDocument();
    expect(screen.getByLabelText(/Enable RTTI/i)).toBeInTheDocument();
    expect(screen.getByLabelText(/C\+\+ standard/i)).toBeInTheDocument();
  });

  it('should reflect current option values', () => {
    const mockOnChange = vi.fn();
    render(<TranspilerOptionsComponent options={defaultOptions} onChange={mockOnChange} />);

    const acslCheckbox = screen.getByLabelText(/Generate ACSL/i) as HTMLInputElement;
    const pragmaCheckbox = screen.getByLabelText(/pragma once/i) as HTMLInputElement;
    const exceptionsCheckbox = screen.getByLabelText(/Enable exceptions/i) as HTMLInputElement;
    const rttiCheckbox = screen.getByLabelText(/Enable RTTI/i) as HTMLInputElement;
    const standardSelect = screen.getByLabelText(/C\+\+ standard/i) as HTMLSelectElement;

    expect(acslCheckbox.checked).toBe(false);
    expect(pragmaCheckbox.checked).toBe(true);
    expect(exceptionsCheckbox.checked).toBe(true);
    expect(rttiCheckbox.checked).toBe(true);
    expect(standardSelect.value).toBe('c++17');
  });

  it('should call onChange when ACSL checkbox is toggled', () => {
    const mockOnChange = vi.fn();
    render(<TranspilerOptionsComponent options={defaultOptions} onChange={mockOnChange} />);

    const acslCheckbox = screen.getByLabelText(/Generate ACSL/i);
    fireEvent.click(acslCheckbox);

    expect(mockOnChange).toHaveBeenCalledWith({
      ...defaultOptions,
      generateACSL: true,
    });
  });

  it('should call onChange when pragma once checkbox is toggled', () => {
    const mockOnChange = vi.fn();
    render(<TranspilerOptionsComponent options={defaultOptions} onChange={mockOnChange} />);

    const pragmaCheckbox = screen.getByLabelText(/pragma once/i);
    fireEvent.click(pragmaCheckbox);

    expect(mockOnChange).toHaveBeenCalledWith({
      ...defaultOptions,
      usePragmaOnce: false,
    });
  });

  it('should call onChange when C++ standard is changed', () => {
    const mockOnChange = vi.fn();
    render(<TranspilerOptionsComponent options={defaultOptions} onChange={mockOnChange} />);

    const standardSelect = screen.getByLabelText(/C\+\+ standard/i);
    fireEvent.change(standardSelect, { target: { value: 'c++20' } });

    expect(mockOnChange).toHaveBeenCalledWith({
      ...defaultOptions,
      cppStandard: 'c++20',
    });
  });

  it('should disable all controls when disabled prop is true', () => {
    const mockOnChange = vi.fn();
    render(<TranspilerOptionsComponent options={defaultOptions} onChange={mockOnChange} disabled={true} />);

    const acslCheckbox = screen.getByLabelText(/Generate ACSL/i) as HTMLInputElement;
    const standardSelect = screen.getByLabelText(/C\+\+ standard/i) as HTMLInputElement;

    expect(acslCheckbox.disabled).toBe(true);
    expect(standardSelect.disabled).toBe(true);
  });

  it('should have all C++ standard options', () => {
    const mockOnChange = vi.fn();
    render(<TranspilerOptionsComponent options={defaultOptions} onChange={mockOnChange} />);

    const standardSelect = screen.getByLabelText(/C\+\+ standard/i);
    const options = Array.from(standardSelect.querySelectorAll('option')).map(opt => opt.value);

    expect(options).toEqual(['c++11', 'c++14', 'c++17', 'c++20']);
  });
});
