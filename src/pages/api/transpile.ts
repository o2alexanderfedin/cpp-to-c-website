/**
 * API Endpoint: /api/transpile
 *
 * Accepts C++ source code and transpiles it to C using the cpptoc transpiler.
 *
 * Request:
 *   POST /api/transpile
 *   Content-Type: application/json
 *   Body: {
 *     source: string,
 *     options?: {
 *       sourcePath?: string,
 *       includeACSL?: boolean,
 *       acslLevel?: 'basic' | 'full',
 *       targetStandard?: string,
 *       enableExceptions?: boolean,
 *       enableRTTI?: boolean
 *     }
 *   }
 *
 * Response:
 *   200 OK: { success: true, cCode: string, diagnostics?: string[] }
 *   500 Error: { success: false, error: string }
 */

import type { APIRoute } from 'astro';
import { exec } from 'child_process';
import { promisify } from 'util';
import { writeFile, readFile, unlink, mkdir } from 'fs/promises';
import { join } from 'path';
import { tmpdir } from 'os';
import { existsSync } from 'fs';

const execAsync = promisify(exec);

// Path to the transpiler binary
const TRANSPILER_PATH = '/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build/cpptoc';

// Timeout for transpilation (30 seconds)
const TRANSPILE_TIMEOUT = 30000;

interface TranspileRequest {
  source: string;
  options?: {
    sourcePath?: string;
    includeACSL?: boolean;
    acslLevel?: 'basic' | 'full';
    targetStandard?: string;
    enableExceptions?: boolean;
    enableRTTI?: boolean;
  };
}

interface TranspileResponse {
  success: boolean;
  cCode?: string;
  error?: string;
  diagnostics?: string[];
}

/**
 * POST handler for transpilation
 */
export const POST: APIRoute = async ({ request }) => {
  let tmpInputFile: string | null = null;
  let tmpOutputFile: string | null = null;

  try {
    // Parse request body
    const body: TranspileRequest = await request.json();

    if (!body.source || typeof body.source !== 'string') {
      return new Response(
        JSON.stringify({
          success: false,
          error: 'Invalid request: source code is required'
        } as TranspileResponse),
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
          success: false,
          error: `Transpiler binary not found at ${TRANSPILER_PATH}`
        } as TranspileResponse),
        {
          status: 500,
          headers: { 'Content-Type': 'application/json' }
        }
      );
    }

    // Create temporary directory and files
    const timestamp = Date.now();
    const tmpDir = join(tmpdir(), `cpptoc-${timestamp}`);
    await mkdir(tmpDir, { recursive: true });

    const sourceName = body.options?.sourcePath
      ? body.options.sourcePath.split('/').pop() || 'input.cpp'
      : 'input.cpp';

    tmpInputFile = join(tmpDir, sourceName);
    tmpOutputFile = join(tmpDir, sourceName.replace(/\.(cpp|cc|cxx)$/i, '.c'));

    // Write source to temporary file
    await writeFile(tmpInputFile, body.source, 'utf-8');

    // Build command with options
    const args: string[] = [tmpInputFile];

    if (body.options?.includeACSL) {
      args.push('--generate-acsl');
      if (body.options.acslLevel === 'full') {
        args.push('--acsl-level=full');
      }
    }

    if (body.options?.enableExceptions === false) {
      args.push('--enable-exceptions=false');
    }

    if (body.options?.enableRTTI === false) {
      args.push('--enable-rtti=false');
    }

    // Execute transpiler
    const cmd = `${TRANSPILER_PATH} ${args.join(' ')}`;

    const { stdout, stderr } = await execAsync(cmd, {
      timeout: TRANSPILE_TIMEOUT,
      cwd: tmpDir,
      maxBuffer: 10 * 1024 * 1024 // 10MB buffer
    });

    // Read transpiled output
    let cCode: string;
    try {
      cCode = await readFile(tmpOutputFile, 'utf-8');
    } catch (readError) {
      // If output file doesn't exist, transpilation likely failed
      throw new Error(`Transpilation failed: output file not generated. ${stderr || ''}`);
    }

    // Collect diagnostics from stderr
    const diagnostics = stderr
      ? stderr.split('\n').filter(line => line.trim().length > 0)
      : [];

    // Cleanup temporary files
    if (tmpInputFile) await unlink(tmpInputFile).catch(() => {});
    if (tmpOutputFile) await unlink(tmpOutputFile).catch(() => {});

    return new Response(
      JSON.stringify({
        success: true,
        cCode,
        diagnostics: diagnostics.length > 0 ? diagnostics : undefined
      } as TranspileResponse),
      {
        status: 200,
        headers: { 'Content-Type': 'application/json' }
      }
    );

  } catch (error) {
    // Cleanup on error
    if (tmpInputFile) await unlink(tmpInputFile).catch(() => {});
    if (tmpOutputFile) await unlink(tmpOutputFile).catch(() => {});

    const errorMessage = error instanceof Error
      ? error.message
      : 'Unknown error occurred';

    // Check for timeout
    if (errorMessage.includes('timeout') || errorMessage.includes('ETIMEDOUT')) {
      return new Response(
        JSON.stringify({
          success: false,
          error: `Transpilation timeout (exceeded ${TRANSPILE_TIMEOUT}ms)`
        } as TranspileResponse),
        {
          status: 408,
          headers: { 'Content-Type': 'application/json' }
        }
      );
    }

    return new Response(
      JSON.stringify({
        success: false,
        error: errorMessage
      } as TranspileResponse),
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
