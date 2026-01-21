/**
 * WASM Transpiler API - CLI Mode
 *
 * Uses Module.callMain() to invoke the transpiler CLI, not Embind bindings.
 * This matches the working playground-idbfs.html implementation.
 *
 * @module wasmTranspiler
 */

import JSZip from 'jszip';

export interface WASMModule {
  FS: EmscriptenFS;
  callMain(args: string[]): number;
  print: (text: string) => void;
  printErr: (text: string) => void;
}

export interface EmscriptenFS {
  mkdir(path: string): void;
  readdir(path: string): string[];
  readFile(path: string, options?: { encoding: 'utf8' }): string | Uint8Array;
  writeFile(path: string, data: string | Uint8Array): void;
  unlink(path: string): void;
  rmdir(path: string): void;
  filesystems: {
    IDBFS: unknown;
  };
  mount(type: unknown, options: Record<string, unknown>, mountpoint: string): void;
  syncfs(populate: boolean, callback: (err: Error | null) => void): void;
}

export type WASMModuleFactory = (config?: {
  noInitialRun?: boolean;
  print?: (text: string) => void;
  printErr?: (text: string) => void;
  onRuntimeInitialized?: () => void;
}) => Promise<WASMModule>;

export interface Diagnostic {
  line: number;
  column: number;
  message: string;
  severity: 'error' | 'warning' | 'note';
}

export interface TranspileResult {
  success: boolean;
  c: string;
  h: string;
  acsl: string;
  diagnostics: Diagnostic[];
  exitCode: number;
}

export interface TranspileOptions {
  generateACSL?: boolean;
  usePragmaOnce?: boolean;
  enableExceptions?: boolean;
  enableRTTI?: boolean;
  cppStandard?: 'c++11' | 'c++14' | 'c++17' | 'c++20';
  target?: string;
}

/**
 * Extract ZIP and prepare files for transpilation
 */
export async function extractZipFiles(
  zipFile: File,
  progressCallback?: (current: number, total: number, fileName: string) => void
): Promise<Map<string, string>> {
  const zip = await JSZip.loadAsync(zipFile);
  const files = new Map<string, string>();

  // Get all file entries (skip directories)
  const fileEntries: Array<{ path: string; entry: JSZip.JSZipObject }> = [];
  zip.forEach((relativePath, zipEntry) => {
    if (!zipEntry.dir) {
      fileEntries.push({ path: relativePath, entry: zipEntry });
    }
  });

  // Extract files
  for (let i = 0; i < fileEntries.length; i++) {
    const { path, entry } = fileEntries[i];
    const content = await entry.async('text');
    files.set(path, content);

    if (progressCallback) {
      progressCallback(i + 1, fileEntries.length, path);
    }
  }

  return files;
}

/**
 * Find main C++ source file in extracted files
 */
export function findMainCppFile(files: Map<string, string>): string | null {
  // Look for common main file names
  const mainCandidates = [
    'main.cpp',
    'src/main.cpp',
    'source/main.cpp',
  ];

  for (const candidate of mainCandidates) {
    if (files.has(candidate)) {
      return candidate;
    }
  }

  // Find first .cpp file
  for (const [path] of files) {
    if (path.match(/\.(cpp|cxx|cc)$/i)) {
      return path;
    }
  }

  return null;
}

/**
 * Write files to virtual filesystem
 */
function writeFilesToFS(module: WASMModule, files: Map<string, string>, baseDir: string): void {
  for (const [path, content] of files) {
    const fullPath = `${baseDir}/${path}`;
    const dir = fullPath.substring(0, fullPath.lastIndexOf('/'));

    // Create directory structure
    const parts = dir.split('/').filter(p => p);
    let current = '';
    for (const part of parts) {
      current += '/' + part;
      try {
        module.FS.mkdir(current);
      } catch (e: unknown) {
        const fsError = e as { code?: string };
        if (fsError.code !== 'EEXIST') throw e;
      }
    }

    // Write file
    module.FS.writeFile(fullPath, content);
  }
}

/**
 * Build CLI arguments from options
 */
function buildCLIArgs(options: TranspileOptions): string[] {
  const args = [
    '--source-dir=/project/src',
    '--output-dir=/project/output'
  ];

  if (options.generateACSL) {
    args.push('--generate-acsl', '--acsl-level=full');
  }

  if (options.usePragmaOnce !== false) {
    args.push('--use-pragma-once');
  }

  if (options.enableExceptions === false) {
    args.push('--enable-exceptions=off');
  }

  if (options.enableRTTI === false) {
    args.push('--enable-rtti=off');
  }

  // Clang arguments
  args.push(
    '--',
    '-target',
    options.target || 'x86_64-unknown-linux-gnu',
    '-I/project/include',
    `-std=${options.cppStandard || 'c++17'}`
  );

  return args;
}

/**
 * Parse diagnostics from stderr output
 */
function parseDiagnostics(stderrLines: string[]): Diagnostic[] {
  const diagnostics: Diagnostic[] = [];

  for (const line of stderrLines) {
    // Parse lines like: "file.cpp:10:5: error: message"
    const match = line.match(/^.*?:(\d+):(\d+):\s+(error|warning|note):\s+(.+)$/);
    if (match) {
      diagnostics.push({
        line: parseInt(match[1], 10),
        column: parseInt(match[2], 10),
        severity: match[3] as 'error' | 'warning' | 'note',
        message: match[4]
      });
    }
  }

  return diagnostics;
}

/**
 * Transpile from ZIP file using CLI approach
 */
export async function transpileFromZip(
  module: WASMModule,
  zipFile: File,
  progressCallback?: (stage: string, progress: number) => void,
  options: TranspileOptions = {}
): Promise<TranspileResult> {
  // Extract ZIP
  progressCallback?.('extracting', 0);
  const files = await extractZipFiles(zipFile, (current, total) => {
    progressCallback?.('extracting', (current / total) * 100);
  });

  progressCallback?.('mounting', 50);

  // Setup IDBFS
  try {
    module.FS.mkdir('/project');
  } catch (e: unknown) {
    const fsError = e as { code?: string };
    if (fsError.code !== 'EEXIST') throw e;
  }

  module.FS.mount(module.FS.filesystems.IDBFS, {}, '/project');

  // Sync from IndexedDB
  await new Promise<void>((resolve, reject) => {
    module.FS.syncfs(true, (err) => {
      if (err) reject(err);
      else resolve();
    });
  });

  // Write files to filesystem
  progressCallback?.('writing', 60);
  writeFilesToFS(module, files, '/project');

  // Create output directory
  try {
    module.FS.mkdir('/project/output');
  } catch (e: unknown) {
    const fsError = e as { code?: string };
    if (fsError.code !== 'EEXIST') throw e;
  }

  // Persist to IndexedDB
  await new Promise<void>((resolve, reject) => {
    module.FS.syncfs(false, (err) => {
      if (err) reject(err);
      else resolve();
    });
  });

  // Build CLI arguments
  const args = buildCLIArgs(options);

  // Capture stderr for diagnostics
  const stderrLines: string[] = [];
  const originalPrintErr = module.printErr;
  module.printErr = (text: string) => {
    stderrLines.push(text);
    originalPrintErr(text);
  };

  try {
    // Run transpiler
    progressCallback?.('transpiling', 75);
    let exitCode: number;
    try {
      exitCode = module.callMain(args);
    } catch (e: unknown) {
      const exitError = e as { name?: string; status?: number };
      if (exitError.name === 'ExitStatus') {
        exitCode = exitError.status ?? 1;
      } else {
        throw e;
      }
    }

    // Restore original printErr
    module.printErr = originalPrintErr;

    const success = exitCode === 0;

    // Read output files
    let cContent = '';
    let hContent = '';
    let acslContent = '';

    if (success) {
      const outputFiles = module.FS.readdir('/project/output').filter(f => f !== '.' && f !== '..');

      for (const file of outputFiles) {
        const content = module.FS.readFile(`/project/output/${file}`, { encoding: 'utf8' }) as string;

        if (file.endsWith('.c')) {
          cContent = content;
        } else if (file.endsWith('.h')) {
          hContent = content;
        } else if (file.endsWith('.acsl')) {
          acslContent = content;
        }
      }
    }

    progressCallback?.('complete', 100);

    return {
      success,
      c: cContent,
      h: hContent,
      acsl: acslContent,
      diagnostics: parseDiagnostics(stderrLines),
      exitCode
    };
  } finally {
    // Cleanup
    module.printErr = originalPrintErr;
  }
}
