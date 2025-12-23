/**
 * Simple Transpiler - Main orchestration module
 * Coordinates parsing, IR building, and C code generation
 */

import { LibClangWrapper } from './libclang-wrapper';
import { ManualCppParser } from './transpiler-visitor';
import { CCodeGenerator, formatCCode } from './c-code-generator';
import type { TranspilerIR } from './transpiler-ir';

export interface TranspileOptions {
  acsl?: boolean;
  target?: 'c89' | 'c99' | 'c11' | 'c17';
  optimize?: boolean;
}

export interface Diagnostic {
  severity: 'error' | 'warning' | 'info';
  message: string;
  line?: number;
  column?: number;
}

export interface TranspileResult {
  success: boolean;
  c: string;
  h: string;
  acsl: string;
  diagnostics: Diagnostic[];
}

/**
 * Main transpiler class
 */
export class SimpleTranspiler {
  private libclang: LibClangWrapper;
  private generator: CCodeGenerator;
  private initialized: boolean = false;

  constructor() {
    this.libclang = new LibClangWrapper();
    this.generator = new CCodeGenerator();
  }

  /**
   * Initialize the transpiler (load WASM, setup FS)
   */
  async initialize(): Promise<void> {
    if (this.initialized) {
      return;
    }

    console.log('[Transpiler] Initializing...');
    await this.libclang.initialize();
    this.initialized = true;
    console.log('[Transpiler] Ready!');
  }

  /**
   * Transpile C++ source code to C
   */
  async transpile(cppCode: string, options: TranspileOptions = {}): Promise<TranspileResult> {
    try {
      // Ensure initialized
      if (!this.initialized) {
        await this.initialize();
      }

      console.log('[Transpiler] Starting transpilation...');
      console.log(`[Transpiler] Input: ${cppCode.length} characters`);

      // For MVP: Use manual parser instead of full libclang AST visitor
      // This gets us to a working transpiler faster
      const useManualParser = true;

      let ir: TranspilerIR;

      if (useManualParser) {
        console.log('[Transpiler] Using manual C++ parser (MVP mode)');
        ir = ManualCppParser.parse(cppCode);
      } else {
        // Future: Full libclang-based parsing
        console.log('[Transpiler] Parsing with libclang...');
        const tu = this.libclang.parse(cppCode);

        // Build IR from AST
        // const visitor = new SimpleTranspilerVisitor(this.libclang);
        // ... visit AST and build IR

        // For now, fallback to manual parser
        ir = ManualCppParser.parse(cppCode);

        // Cleanup
        this.libclang.disposeTranslationUnit(tu);
      }

      console.log(`[Transpiler] IR built: ${ir.classes.length} classes, ${ir.functions.length} functions`);

      // Generate C code
      console.log('[Transpiler] Generating C code...');
      const hCode = this.generator.generateHeader(ir);
      const cCode = this.generator.generateImplementation(ir);
      const acslCode = options.acsl !== false ? this.generator.generateACSL(ir) : '';

      // Format output
      const formattedH = formatCCode(hCode);
      const formattedC = formatCCode(cCode);
      const formattedACSL = formatCCode(acslCode);

      console.log('[Transpiler] Transpilation complete!');

      return {
        success: true,
        c: formattedC,
        h: formattedH,
        acsl: formattedACSL,
        diagnostics: []
      };

    } catch (error) {
      console.error('[Transpiler] Transpilation failed:', error);

      return {
        success: false,
        c: '',
        h: '',
        acsl: '',
        diagnostics: [{
          severity: 'error',
          message: error instanceof Error ? error.message : String(error)
        }]
      };
    }
  }

  /**
   * Cleanup resources
   */
  dispose(): void {
    if (this.initialized) {
      this.libclang.dispose();
      this.initialized = false;
      console.log('[Transpiler] Disposed');
    }
  }
}

/**
 * Singleton instance for easy use
 */
let transpilerInstance: SimpleTranspiler | null = null;

/**
 * Get or create transpiler instance
 */
export async function getTranspiler(): Promise<SimpleTranspiler> {
  if (!transpilerInstance) {
    transpilerInstance = new SimpleTranspiler();
    await transpilerInstance.initialize();
  }
  return transpilerInstance;
}

/**
 * Quick transpile function
 */
export async function transpile(cppCode: string, options?: TranspileOptions): Promise<TranspileResult> {
  const transpiler = await getTranspiler();
  return transpiler.transpile(cppCode, options);
}
