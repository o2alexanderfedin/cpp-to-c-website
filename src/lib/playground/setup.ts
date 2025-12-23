/**
 * Dependency Injection Setup for Playground
 *
 * Factory functions for creating production service instances
 * with proper configuration and wiring.
 *
 * Following SOLID principles:
 * - Dependency Inversion: Services depend on interfaces, not concrete implementations
 * - Single Responsibility: Each factory creates one service type
 * - Open/Closed: New services can be added without modifying existing code
 */

import { WasmTranspilerAdapter } from '../../adapters/WasmTranspilerAdapter';
import { BackendTranspilerAdapter } from '../../adapters/BackendTranspilerAdapter';
import { FileSystemAccessAdapter } from '../../adapters/FileSystemAccessAdapter';
import { MockFileSystem } from '../../adapters/MockFileSystem';
import { MockTranspiler } from '../../adapters/MockTranspiler';
import type { ITranspiler } from '../../core/interfaces/ITranspiler';
import type { IFileSystem } from '../../core/interfaces/IFileSystem';

/**
 * Configuration for playground services
 */
export interface PlaygroundConfig {
  /**
   * Backend API URL for transpilation
   * @example 'https://api.example.com' or '/api' for relative
   */
  apiUrl: string;

  /**
   * Whether to use mock implementations (for development/testing)
   * @default false
   */
  useMocks?: boolean;
}

/**
 * Create transpiler service instance
 *
 * @param config - Playground configuration
 * @returns Transpiler implementation (WASM, backend, or mock)
 */
export function createTranspiler(config: PlaygroundConfig): ITranspiler {
  if (config.useMocks) {
    return new MockTranspiler();
  }

  // Use WASM transpiler for browser-based transpilation
  return new WasmTranspilerAdapter();
}

/**
 * Create file system service instance
 *
 * @param config - Playground configuration
 * @returns File system implementation (File System Access API or mock)
 */
export function createFileSystem(config: PlaygroundConfig): IFileSystem {
  if (config.useMocks) {
    const mock = new MockFileSystem();

    // Add some sample files for testing
    mock.addFile('/example/main.cpp', `#include <iostream>

int main() {
    std::cout << "Hello, World!" << std::endl;
    return 0;
}
`);
    mock.addFile('/example/utils.h', `#ifndef UTILS_H
#define UTILS_H

class Utils {
public:
    static int add(int a, int b);
};

#endif
`);
    mock.addFile('/example/utils.cpp', `#include "utils.h"

int Utils::add(int a, int b) {
    return a + b;
}
`);

    return mock;
  }

  return new FileSystemAccessAdapter();
}

/**
 * Get default production configuration
 *
 * Uses environment variables or defaults to relative API path
 *
 * @returns Default playground configuration
 */
export function getDefaultConfig(): PlaygroundConfig {
  // Try to get API URL from environment (set during build)
  const apiUrl = import.meta.env.PUBLIC_API_URL || '';

  return {
    apiUrl,
    useMocks: false,
  };
}

/**
 * Get development configuration with mocks
 *
 * @returns Development playground configuration
 */
export function getDevConfig(): PlaygroundConfig {
  return {
    apiUrl: '',
    useMocks: true,
  };
}

/**
 * Create all playground services with production configuration
 *
 * Convenience function to create all services at once
 *
 * @param config - Optional configuration (uses defaults if not provided)
 * @returns Object containing all configured services
 */
export function createPlaygroundServices(config?: PlaygroundConfig) {
  const finalConfig = config || getDefaultConfig();

  return {
    transpiler: createTranspiler(finalConfig),
    fileSystem: createFileSystem(finalConfig),
    config: finalConfig,
  };
}

/**
 * Check if File System Access API is supported in current browser
 *
 * @returns true if File System Access API is available
 */
export function isFileSystemAccessSupported(): boolean {
  return (
    typeof window !== 'undefined' &&
    'showDirectoryPicker' in window &&
    typeof window.showDirectoryPicker === 'function'
  );
}

/**
 * Get browser compatibility tier
 *
 * @returns Browser tier (1 = full support, 2 = partial, 3 = minimal)
 */
export function getBrowserTier(): 1 | 2 | 3 {
  if (typeof window === 'undefined') {
    return 3;
  }

  // Tier 1: Chrome/Edge with File System Access API
  if (isFileSystemAccessSupported()) {
    return 1;
  }

  // Tier 2: Firefox/Safari with webkitdirectory (not implemented yet)
  // @ts-ignore - webkitdirectory is not in standard types
  if ('webkitdirectory' in document.createElement('input')) {
    return 2;
  }

  // Tier 3: Mobile or unsupported browsers
  return 3;
}

/**
 * Get browser compatibility message for user
 *
 * @param tier - Browser tier (optional, auto-detected if not provided)
 * @returns User-friendly compatibility message
 */
export function getBrowserCompatibilityMessage(tier?: 1 | 2 | 3): string {
  const browserTier = tier || getBrowserTier();

  switch (browserTier) {
    case 1:
      return 'Full support: Your browser supports all playground features including directory selection and file writing.';
    case 2:
      return 'Partial support: Your browser supports directory selection but not file writing. Use download instead.';
    case 3:
      return 'Limited support: Your browser has limited file system support. Consider using Chrome or Edge for the best experience.';
  }
}
