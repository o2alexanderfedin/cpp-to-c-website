/**
 * API Endpoint: /api/validate
 *
 * Validates C++ source code syntax without performing full transpilation.
 * Uses the cpptoc transpiler in a lightweight mode to check for syntax errors.
 *
 * Request:
 *   POST /api/validate
 *   Content-Type: application/json
 *   Body: { source: string }
 *
 * Response:
 *   200 OK: { valid: true, warnings?: string[] }
 *   200 OK: { valid: false, errors: string[], warnings?: string[] }
 *   500 Error: { valid: false, errors: [string] }
 */

import type { APIRoute } from 'astro';
import { exec } from 'child_process';
import { promisify } from 'util';
import { writeFile, unlink, mkdir } from 'fs/promises';
import { join } from 'path';
import { tmpdir } from 'os';
import { existsSync } from 'fs';

const execAsync = promisify(exec);

// Path to the transpiler binary
const TRANSPILER_PATH = '/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build/cpptoc';

// Timeout for validation (10 seconds - shorter than transpilation)
const VALIDATE_TIMEOUT = 10000;

interface ValidationRequest {
  source: string;
}

interface ValidationResponse {
  valid: boolean;
  errors?: string[];
  warnings?: string[];
}

/**
 * POST handler for validation
 */
export const POST: APIRoute = async ({ request }) => {
  let tmpInputFile: string | null = null;

  try {
    // Parse request body
    const body: ValidationRequest = await request.json();

    if (!body.source || typeof body.source !== 'string') {
      return new Response(
        JSON.stringify({
          valid: false,
          errors: ['Invalid request: source code is required']
        } as ValidationResponse),
        {
          status: 400,
          headers: { 'Content-Type': 'application/json' }
        }
      );
    }

    // Validate transpiler exists
    if (!existsSync(TRANSPILER_PATH)) {
      return new Response(
        JSON.stringify({
          valid: false,
          errors: [`Transpiler binary not found at ${TRANSPILER_PATH}`]
        } as ValidationResponse),
        {
          status: 500,
          headers: { 'Content-Type': 'application/json' }
        }
      );
    }

    // Create temporary directory and file
    const timestamp = Date.now();
    const tmpDir = join(tmpdir(), `cpptoc-validate-${timestamp}`);
    await mkdir(tmpDir, { recursive: true });

    tmpInputFile = join(tmpDir, 'input.cpp');

    // Write source to temporary file
    await writeFile(tmpInputFile, body.source, 'utf-8');

    // Run transpiler (it will validate syntax as part of transpilation)
    // We'll check if it succeeds or fails
    const cmd = `${TRANSPILER_PATH} ${tmpInputFile}`;

    try {
      const { stdout, stderr } = await execAsync(cmd, {
        timeout: VALIDATE_TIMEOUT,
        cwd: tmpDir,
        maxBuffer: 5 * 1024 * 1024 // 5MB buffer
      });

      // Parse output for warnings
      const warnings = stderr
        ? stderr.split('\n')
            .filter(line => line.trim().length > 0)
            .filter(line =>
              line.toLowerCase().includes('warning') ||
              line.toLowerCase().includes('note')
            )
        : [];

      // Cleanup
      if (tmpInputFile) await unlink(tmpInputFile).catch(() => {});

      return new Response(
        JSON.stringify({
          valid: true,
          warnings: warnings.length > 0 ? warnings : undefined
        } as ValidationResponse),
        {
          status: 200,
          headers: { 'Content-Type': 'application/json' }
        }
      );

    } catch (execError) {
      // Transpiler returned non-zero exit code = validation failed
      const error = execError as { stdout?: string; stderr?: string; message: string };

      // Parse errors from stderr
      const errorLines = error.stderr
        ? error.stderr.split('\n')
            .filter(line => line.trim().length > 0)
            .filter(line =>
              line.toLowerCase().includes('error') ||
              line.toLowerCase().includes('fatal')
            )
        : [];

      // Parse warnings
      const warningLines = error.stderr
        ? error.stderr.split('\n')
            .filter(line => line.trim().length > 0)
            .filter(line =>
              line.toLowerCase().includes('warning') ||
              line.toLowerCase().includes('note')
            )
        : [];

      // If no specific errors found, use the error message
      const errors = errorLines.length > 0
        ? errorLines
        : [error.message || 'Syntax validation failed'];

      // Cleanup
      if (tmpInputFile) await unlink(tmpInputFile).catch(() => {});

      return new Response(
        JSON.stringify({
          valid: false,
          errors,
          warnings: warningLines.length > 0 ? warningLines : undefined
        } as ValidationResponse),
        {
          status: 200,
          headers: { 'Content-Type': 'application/json' }
        }
      );
    }

  } catch (error) {
    // Cleanup on error
    if (tmpInputFile) await unlink(tmpInputFile).catch(() => {});

    const errorMessage = error instanceof Error
      ? error.message
      : 'Unknown error occurred';

    // Check for timeout
    if (errorMessage.includes('timeout') || errorMessage.includes('ETIMEDOUT')) {
      return new Response(
        JSON.stringify({
          valid: false,
          errors: [`Validation timeout (exceeded ${VALIDATE_TIMEOUT}ms)`]
        } as ValidationResponse),
        {
          status: 408,
          headers: { 'Content-Type': 'application/json' }
        }
      );
    }

    return new Response(
      JSON.stringify({
        valid: false,
        errors: [errorMessage]
      } as ValidationResponse),
      {
        status: 500,
        headers: { 'Content-Type': 'application/json' }
      }
    );
  }
};

/**
 * OPTIONS handler for CORS preflight
 */
export const OPTIONS: APIRoute = async () => {
  return new Response(null, {
    status: 204,
    headers: {
      'Access-Control-Allow-Origin': '*',
      'Access-Control-Allow-Methods': 'POST, OPTIONS',
      'Access-Control-Allow-Headers': 'Content-Type'
    }
  });
};
