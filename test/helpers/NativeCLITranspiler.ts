/**
 * Native CLI Transpiler Adapter
 *
 * Uses the native cpptoc CLI instead of WASM for testing.
 * This allows integration tests to use real transpilation while
 * WASM transpiler builds are in progress.
 */

import { execFile } from 'child_process';
import { promisify } from 'util';
import { writeFile, unlink, mkdtemp } from 'fs/promises';
import { join } from 'path';
import { tmpdir } from 'os';
import type { TranspileOptions, TranspileResult } from '@hupyy/cpptoc-wasm';

const execFileAsync = promisify(execFile);

const CLI_PATH = '/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build/cpptoc';

export class NativeCLITranspiler {
  transpile(code: string, options: TranspileOptions = {}): TranspileResult {
    // Create a sync wrapper using child_process.execFileSync
    const { execFileSync } = require('child_process');

    try {
      // Create temp directory
      const tempDir = require('fs').mkdtempSync(join(tmpdir(), 'cpptoc-test-'));
      const inputFile = join(tempDir, 'input.cpp');
      const outputC = join(tempDir, 'input.c');
      const outputH = join(tempDir, 'input.h');

      // Write C++ source to temp file
      require('fs').writeFileSync(inputFile, code, 'utf-8');

      // Build CLI arguments - CLI automatically discovers files in source-dir
      const args: string[] = ['--source-dir', tempDir, '--output-dir', tempDir];

      // Note: CLI doesn't have --target option (always outputs C code)
      // Note: CLI doesn't have --optimize option

      // Enable ACSL if any option is set
      if (options.acsl && (options.acsl.statements || options.acsl.typeInvariants ||
          options.acsl.axiomatics || options.acsl.ghostCode || options.acsl.behaviors)) {
        args.push('--generate-acsl');

        if (options.acsl.memoryPredicates) {
          args.push('--acsl-memory-predicates');
        }
      }

      // Run CLI
      const result = execFileSync(CLI_PATH, args, {
        encoding: 'utf-8',
        stdio: ['pipe', 'pipe', 'pipe']
      });

      // Log CLI output for debugging
      if (result) {
        console.log('CLI output:', result);
      }

      // Read output files
      const cCode = require('fs').readFileSync(outputC, 'utf-8');
      const hCode = require('fs').readFileSync(outputH, 'utf-8');

      // Clean up
      require('fs').unlinkSync(inputFile);
      require('fs').unlinkSync(outputC);
      require('fs').unlinkSync(outputH);
      require('fs').rmdirSync(tempDir);

      return {
        success: true,
        c: cCode,
        h: hCode,
        acsl: '',
        diagnostics: []
      };
    } catch (error: unknown) {
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';
      const stderr = (error as any).stderr || '';
      console.error('CLI Error:', errorMessage);
      if (stderr) console.error('CLI stderr:', stderr);
      return {
        success: false,
        c: '',
        h: '',
        acsl: '',
        diagnostics: [{
          line: 0,
          column: 0,
          message: `${errorMessage}\nStderr: ${stderr}`,
          severity: 'error'
        }]
      };
    }
  }

  getVersion(): string {
    return '1.22.0-native';
  }

  delete(): void {
    // No-op for native CLI
  }
}
