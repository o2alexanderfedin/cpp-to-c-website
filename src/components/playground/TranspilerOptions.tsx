/**
 * Transpiler Options Component
 *
 * Provides UI controls for configuring transpiler behavior including
 * ACSL annotations, pragma once, exceptions, RTTI, and C++ standard version.
 *
 * Features:
 * - Checkbox controls for boolean options
 * - Dropdown for C++ standard selection
 * - Accessible form controls with proper labels
 * - Change callbacks for parent component
 *
 * @module TranspilerOptions
 */

import React, { useCallback } from 'react';
import type { TranspilerOptions } from '../../lib/playground/idbfs-types';

export interface TranspilerOptionsProps {
  /**
   * Current options
   */
  options: TranspilerOptions;

  /**
   * Callback when options change
   */
  onChange: (options: TranspilerOptions) => void;

  /**
   * Whether controls are disabled
   */
  disabled?: boolean;
}

/**
 * Transpiler Options Component
 */
export const TranspilerOptionsComponent: React.FC<TranspilerOptionsProps> = ({
  options,
  onChange,
  disabled = false,
}) => {
  /**
   * Handle checkbox change
   */
  const handleCheckboxChange = useCallback((field: keyof TranspilerOptions) => {
    return (event: React.ChangeEvent<HTMLInputElement>) => {
      onChange({
        ...options,
        [field]: event.target.checked,
      });
    };
  }, [options, onChange]);

  /**
   * Handle C++ standard change
   */
  const handleStandardChange = useCallback((event: React.ChangeEvent<HTMLSelectElement>) => {
    onChange({
      ...options,
      cppStandard: event.target.value as TranspilerOptions['cppStandard'],
    });
  }, [options, onChange]);

  return (
    <div className="transpiler-options">
      <div className="options-grid">
        {/* ACSL Annotations */}
        <label className="option-label">
          <input
            type="checkbox"
            checked={options.generateACSL ?? false}
            onChange={handleCheckboxChange('generateACSL')}
            disabled={disabled}
            aria-label="Generate ACSL annotations"
          />
          <span className="option-text">Generate ACSL annotations</span>
          <span className="option-description">
            Add formal specification annotations for verification
          </span>
        </label>

        {/* Pragma Once */}
        <label className="option-label">
          <input
            type="checkbox"
            checked={options.usePragmaOnce ?? true}
            onChange={handleCheckboxChange('usePragmaOnce')}
            disabled={disabled}
            aria-label="Use pragma once"
          />
          <span className="option-text">Use #pragma once</span>
          <span className="option-description">
            Use #pragma once instead of include guards
          </span>
        </label>

        {/* Exceptions */}
        <label className="option-label">
          <input
            type="checkbox"
            checked={options.enableExceptions ?? true}
            onChange={handleCheckboxChange('enableExceptions')}
            disabled={disabled}
            aria-label="Enable exceptions"
          />
          <span className="option-text">Enable exceptions</span>
          <span className="option-description">
            Support C++ exception handling
          </span>
        </label>

        {/* RTTI */}
        <label className="option-label">
          <input
            type="checkbox"
            checked={options.enableRTTI ?? true}
            onChange={handleCheckboxChange('enableRTTI')}
            disabled={disabled}
            aria-label="Enable RTTI"
          />
          <span className="option-text">Enable RTTI</span>
          <span className="option-description">
            Support Run-Time Type Information (dynamic_cast, typeid)
          </span>
        </label>
      </div>

      {/* C++ Standard */}
      <div className="standard-selector">
        <label htmlFor="cpp-standard" className="standard-label">
          C++ Standard:
        </label>
        <select
          id="cpp-standard"
          value={options.cppStandard ?? 'c++17'}
          onChange={handleStandardChange}
          disabled={disabled}
          className="standard-select"
          aria-label="Select C++ standard version"
        >
          <option value="c++11">C++11</option>
          <option value="c++14">C++14</option>
          <option value="c++17">C++17</option>
          <option value="c++20">C++20</option>
        </select>
      </div>

      <style>{`
        .transpiler-options {
          padding: 1.5rem;
          background: #f9fafb;
          border: 1px solid #e5e7eb;
          border-radius: 8px;
        }

        .options-grid {
          display: grid;
          grid-template-columns: repeat(auto-fit, minmax(min(100%, 250px), 1fr));
          gap: 1.25rem;
          margin-bottom: 1.5rem;
        }

        .option-label {
          display: flex;
          flex-direction: column;
          gap: 0.25rem;
          cursor: pointer;
          padding: 0.75rem;
          background: white;
          border: 1px solid #e5e7eb;
          border-radius: 6px;
          transition: all 0.2s ease;
        }

        .option-label:hover:not(:has(input:disabled)) {
          border-color: #9ca3af;
          background: #f9fafb;
        }

        .option-label:has(input:checked) {
          border-color: #667eea;
          background: #eef2ff;
        }

        .option-label:has(input:focus-visible) {
          outline: 2px solid #667eea;
          outline-offset: 2px;
        }

        .option-label input[type="checkbox"] {
          width: 18px;
          height: 18px;
          cursor: pointer;
          margin-right: 0.5rem;
        }

        .option-label input[type="checkbox"]:disabled {
          cursor: not-allowed;
          opacity: 0.5;
        }

        .option-text {
          font-weight: 600;
          color: #1f2937;
          font-size: 0.95rem;
          display: flex;
          align-items: center;
        }

        .option-text::before {
          content: '';
          display: inline-block;
          width: 18px;
          margin-right: 0.5rem;
        }

        .option-description {
          font-size: 0.8rem;
          color: #6b7280;
          margin-left: 1.625rem;
        }

        .standard-selector {
          display: flex;
          align-items: center;
          gap: 1rem;
          padding: 0.75rem;
          background: white;
          border: 1px solid #e5e7eb;
          border-radius: 6px;
        }

        .standard-label {
          font-weight: 600;
          color: #1f2937;
          font-size: 0.95rem;
        }

        .standard-select {
          padding: 0.5rem 0.75rem;
          border: 2px solid #e5e7eb;
          border-radius: 6px;
          font-size: 0.9rem;
          background: white;
          cursor: pointer;
          transition: border-color 0.2s ease;
          min-width: 120px;
        }

        .standard-select:hover:not(:disabled) {
          border-color: #9ca3af;
        }

        .standard-select:focus {
          outline: none;
          border-color: #667eea;
          box-shadow: 0 0 0 3px rgba(102, 126, 234, 0.1);
        }

        .standard-select:disabled {
          opacity: 0.5;
          cursor: not-allowed;
          background: #f3f4f6;
        }

        @media (max-width: 768px) {
          .transpiler-options {
            padding: 1rem;
          }

          .options-grid {
            grid-template-columns: 1fr;
            gap: 1rem;
          }

          .standard-selector {
            flex-direction: column;
            align-items: flex-start;
          }

          .standard-select {
            width: 100%;
          }
        }
      `}</style>
    </div>
  );
};
