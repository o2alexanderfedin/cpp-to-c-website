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

import React, { useCallback, useState } from 'react';
import type { TranspilerOptions, ACSLConfig } from '../../lib/playground/idbfs-types';

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
  // Track whether ACSL section is expanded
  const [acslExpanded, setAcslExpanded] = useState(false);

  // Check if any ACSL feature is enabled
  const hasACSLEnabled = options.acsl && Object.values(options.acsl).some(v => v === true);

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
   * Handle ACSL feature toggle
   */
  const handleACSLFeatureChange = useCallback((feature: keyof ACSLConfig) => {
    return (event: React.ChangeEvent<HTMLInputElement>) => {
      onChange({
        ...options,
        acsl: {
          ...options.acsl,
          [feature]: event.target.checked,
        },
      });
    };
  }, [options, onChange]);

  /**
   * Handle ACSL master toggle
   */
  const handleACSLMasterToggle = useCallback((event: React.ChangeEvent<HTMLInputElement>) => {
    const enabled = event.target.checked;
    if (enabled) {
      // Enable with sensible defaults
      onChange({
        ...options,
        acsl: {
          statements: true,
          typeInvariants: true,
          axiomatics: true,
          ghostCode: true,
          behaviors: true,
          memoryPredicates: true,
        },
        acslLevel: 'Basic',
        acslOutputMode: 'Inline',
      });
      setAcslExpanded(true);
    } else {
      // Disable all ACSL
      onChange({
        ...options,
        acsl: undefined,
        acslLevel: undefined,
        acslOutputMode: undefined,
      });
      setAcslExpanded(false);
    }
  }, [options, onChange]);

  /**
   * Handle ACSL level change
   */
  const handleACSLLevelChange = useCallback((event: React.ChangeEvent<HTMLInputElement>) => {
    onChange({
      ...options,
      acslLevel: event.target.value as TranspilerOptions['acslLevel'],
    });
  }, [options, onChange]);

  /**
   * Handle ACSL output mode change
   */
  const handleACSLOutputModeChange = useCallback((event: React.ChangeEvent<HTMLInputElement>) => {
    onChange({
      ...options,
      acslOutputMode: event.target.value as TranspilerOptions['acslOutputMode'],
    });
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
      {/* ACSL Section */}
      <div className="acsl-section">
        <div className="acsl-header">
          <label className="acsl-master-toggle">
            <input
              type="checkbox"
              checked={hasACSLEnabled}
              onChange={handleACSLMasterToggle}
              disabled={disabled}
              aria-label="Enable ACSL generation"
            />
            <span className="option-text">Enable ACSL Generation</span>
          </label>
          {hasACSLEnabled && (
            <button
              type="button"
              className="acsl-expand-btn"
              onClick={() => setAcslExpanded(!acslExpanded)}
              aria-label={acslExpanded ? "Collapse ACSL options" : "Expand ACSL options"}
              aria-expanded={acslExpanded}
            >
              {acslExpanded ? '▼' : '▶'}
            </button>
          )}
        </div>

        {hasACSLEnabled && acslExpanded && (
          <div className="acsl-controls">
            {/* Output Mode */}
            <div className="acsl-control-group">
              <label className="control-group-label">Output Mode:</label>
              <div className="radio-group">
                <label className="radio-label">
                  <input
                    type="radio"
                    name="acslOutputMode"
                    value="Inline"
                    checked={options.acslOutputMode === 'Inline' || !options.acslOutputMode}
                    onChange={handleACSLOutputModeChange}
                    disabled={disabled}
                  />
                  <span>Inline in C code</span>
                </label>
                <label className="radio-label">
                  <input
                    type="radio"
                    name="acslOutputMode"
                    value="Separate"
                    checked={options.acslOutputMode === 'Separate'}
                    onChange={handleACSLOutputModeChange}
                    disabled={disabled}
                  />
                  <span>Separate .acsl files</span>
                </label>
              </div>
            </div>

            {/* ACSL Level */}
            <div className="acsl-control-group">
              <label className="control-group-label">ACSL Level:</label>
              <div className="radio-group">
                <label className="radio-label">
                  <input
                    type="radio"
                    name="acslLevel"
                    value="Basic"
                    checked={options.acslLevel === 'Basic' || !options.acslLevel}
                    onChange={handleACSLLevelChange}
                    disabled={disabled}
                  />
                  <span>Basic (function contracts)</span>
                </label>
                <label className="radio-label">
                  <input
                    type="radio"
                    name="acslLevel"
                    value="Full"
                    checked={options.acslLevel === 'Full'}
                    onChange={handleACSLLevelChange}
                    disabled={disabled}
                  />
                  <span>Full (includes loop/class invariants)</span>
                </label>
              </div>
            </div>

            {/* ACSL Features */}
            <div className="acsl-control-group">
              <label className="control-group-label">Features:</label>
              <div className="features-grid">
                <label className="feature-label">
                  <input
                    type="checkbox"
                    checked={options.acsl?.statements ?? false}
                    onChange={handleACSLFeatureChange('statements')}
                    disabled={disabled}
                  />
                  <span>Statements</span>
                </label>
                <label className="feature-label">
                  <input
                    type="checkbox"
                    checked={options.acsl?.typeInvariants ?? false}
                    onChange={handleACSLFeatureChange('typeInvariants')}
                    disabled={disabled}
                  />
                  <span>Type Invariants</span>
                </label>
                <label className="feature-label">
                  <input
                    type="checkbox"
                    checked={options.acsl?.axiomatics ?? false}
                    onChange={handleACSLFeatureChange('axiomatics')}
                    disabled={disabled}
                  />
                  <span>Axiomatics</span>
                </label>
                <label className="feature-label">
                  <input
                    type="checkbox"
                    checked={options.acsl?.ghostCode ?? false}
                    onChange={handleACSLFeatureChange('ghostCode')}
                    disabled={disabled}
                  />
                  <span>Ghost Code</span>
                </label>
                <label className="feature-label">
                  <input
                    type="checkbox"
                    checked={options.acsl?.behaviors ?? false}
                    onChange={handleACSLFeatureChange('behaviors')}
                    disabled={disabled}
                  />
                  <span>Behaviors</span>
                </label>
                <label className="feature-label">
                  <input
                    type="checkbox"
                    checked={options.acsl?.memoryPredicates ?? false}
                    onChange={handleACSLFeatureChange('memoryPredicates')}
                    disabled={disabled}
                  />
                  <span>Memory Predicates</span>
                </label>
              </div>
            </div>
          </div>
        )}
      </div>

      <div className="options-grid">

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

        /* ACSL Section */
        .acsl-section {
          margin-bottom: 1.5rem;
          padding: 1rem;
          background: white;
          border: 1px solid #e5e7eb;
          border-radius: 6px;
        }

        .acsl-header {
          display: flex;
          align-items: center;
          justify-content: space-between;
        }

        .acsl-master-toggle {
          display: flex;
          align-items: center;
          gap: 0.5rem;
          cursor: pointer;
          flex: 1;
        }

        .acsl-master-toggle input[type="checkbox"] {
          width: 18px;
          height: 18px;
          cursor: pointer;
        }

        .acsl-expand-btn {
          padding: 0.25rem 0.5rem;
          background: transparent;
          border: 1px solid #e5e7eb;
          border-radius: 4px;
          cursor: pointer;
          font-size: 0.75rem;
          color: #667eea;
          transition: all 0.2s ease;
        }

        .acsl-expand-btn:hover {
          background: #eef2ff;
          border-color: #667eea;
        }

        .acsl-expand-btn:focus {
          outline: 2px solid #667eea;
          outline-offset: 2px;
        }

        .acsl-controls {
          margin-top: 1rem;
          padding-top: 1rem;
          border-top: 1px solid #e5e7eb;
          display: flex;
          flex-direction: column;
          gap: 1rem;
        }

        .acsl-control-group {
          display: flex;
          flex-direction: column;
          gap: 0.5rem;
        }

        .control-group-label {
          font-weight: 600;
          color: #1f2937;
          font-size: 0.9rem;
        }

        .radio-group {
          display: flex;
          flex-direction: column;
          gap: 0.5rem;
          padding-left: 0.5rem;
        }

        .radio-label {
          display: flex;
          align-items: center;
          gap: 0.5rem;
          cursor: pointer;
          padding: 0.25rem;
        }

        .radio-label input[type="radio"] {
          cursor: pointer;
        }

        .radio-label:hover {
          background: #f9fafb;
          border-radius: 4px;
        }

        .features-grid {
          display: grid;
          grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
          gap: 0.5rem;
          padding-left: 0.5rem;
        }

        .feature-label {
          display: flex;
          align-items: center;
          gap: 0.5rem;
          cursor: pointer;
          padding: 0.5rem;
          background: #f9fafb;
          border: 1px solid #e5e7eb;
          border-radius: 4px;
          transition: all 0.2s ease;
        }

        .feature-label:hover {
          background: white;
          border-color: #9ca3af;
        }

        .feature-label:has(input:checked) {
          background: #eef2ff;
          border-color: #667eea;
        }

        .feature-label input[type="checkbox"] {
          width: 16px;
          height: 16px;
          cursor: pointer;
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

          .features-grid {
            grid-template-columns: 1fr;
          }

          .acsl-header {
            flex-direction: row;
            gap: 0.5rem;
          }
        }
      `}</style>
    </div>
  );
};
