/**
 * Adapters - Mock and Production Implementations
 *
 * Central export point for all adapter implementations.
 * Use this for clean imports: `import { MockFileSystem, BackendTranspilerAdapter } from '@/adapters'`
 */

// Mock Implementations (for testing)
export { MockFileSystem } from './MockFileSystem';
export { MockTranspiler } from './MockTranspiler';
export { MockProgressReporter } from './MockProgressReporter';

// Production Implementations
export { WasmTranspilerAdapter } from './WasmTranspilerAdapter';
export { BackendTranspilerAdapter } from './BackendTranspilerAdapter';
export { FileSystemAccessAdapter } from './FileSystemAccessAdapter';
