/**
 * C Code Generator
 * Generates C header and implementation files from IR
 */

import type { TranspilerIR, ClassIR, FunctionIR, MethodIR, ParamIR } from './transpiler-ir';

/**
 * Generates C code (header and implementation) from transpiler IR
 */
export class CCodeGenerator {
  /**
   * Generate C header file (.h)
   */
  generateHeader(ir: TranspilerIR, headerGuard: string = 'TRANSPILED_H'): string {
    let header = `#ifndef ${headerGuard}\n#define ${headerGuard}\n\n`;

    // Generate struct definitions for classes
    for (const cls of ir.classes) {
      header += this.generateStructDefinition(cls);
      header += '\n';
    }

    // Generate method/function declarations for classes
    for (const cls of ir.classes) {
      header += this.generateClassFunctionDeclarations(cls);
      header += '\n';
    }

    // Generate standalone function declarations
    for (const func of ir.functions) {
      header += this.generateFunctionDeclaration(func);
      header += '\n';
    }

    header += `#endif /* ${headerGuard} */\n`;
    return header;
  }

  /**
   * Generate C implementation file (.c)
   */
  generateImplementation(ir: TranspilerIR, headerName: string = 'transpiled.h'): string {
    let impl = `#include "${headerName}"\n\n`;

    // Generate method implementations for classes
    for (const cls of ir.classes) {
      impl += this.generateClassFunctionImplementations(cls);
      impl += '\n';
    }

    // Generate standalone function implementations
    for (const func of ir.functions) {
      impl += this.generateFunctionImplementation(func);
      impl += '\n';
    }

    return impl;
  }

  /**
   * Generate struct definition for a C++ class
   */
  private generateStructDefinition(cls: ClassIR): string {
    let struct = `/* Class: ${cls.name} */\n`;
    struct += `typedef struct ${cls.name} {\n`;

    // Add members
    for (const member of cls.members) {
      struct += `    ${member.type} ${member.name};\n`;
    }

    struct += `} ${cls.name};\n`;
    return struct;
  }

  /**
   * Generate function declarations for class methods
   */
  private generateClassFunctionDeclarations(cls: ClassIR): string {
    let decls = `/* ${cls.name} methods */\n`;

    for (const method of cls.methods) {
      decls += this.generateMethodDeclaration(cls.name, method);
      decls += '\n';
    }

    return decls;
  }

  /**
   * Generate single method declaration
   */
  private generateMethodDeclaration(className: string, method: MethodIR): string {
    const params = this.formatParameters(method.params);
    const thisParam = `${className}* this`;
    const allParams = params ? `${thisParam}, ${params}` : thisParam;

    return `${method.returnType} ${className}_${method.name}(${allParams});`;
  }

  /**
   * Generate function declaration
   */
  private generateFunctionDeclaration(func: FunctionIR): string {
    const params = this.formatParameters(func.params);
    return `${func.returnType} ${func.name}(${params});`;
  }

  /**
   * Generate function implementations for class methods
   */
  private generateClassFunctionImplementations(cls: ClassIR): string {
    let impls = `/* ${cls.name} method implementations */\n`;

    for (const method of cls.methods) {
      impls += this.generateMethodImplementation(cls.name, method);
      impls += '\n';
    }

    return impls;
  }

  /**
   * Generate single method implementation
   */
  private generateMethodImplementation(className: string, method: MethodIR): string {
    const params = this.formatParameters(method.params);
    const thisParam = `${className}* this`;
    const allParams = params ? `${thisParam}, ${params}` : thisParam;

    let impl = `${method.returnType} ${className}_${method.name}(${allParams}) {\n`;

    // Transform method body: replace member access 'x' with 'this->x'
    const transformedBody = this.transformMethodBody(method.body, className);
    impl += this.indentCode(transformedBody, 1);

    impl += '\n}\n';
    return impl;
  }

  /**
   * Generate standalone function implementation
   */
  private generateFunctionImplementation(func: FunctionIR): string {
    const params = this.formatParameters(func.params);

    let impl = `${func.returnType} ${func.name}(${params}) {\n`;
    impl += this.indentCode(func.body, 1);
    impl += '\n}\n';
    return impl;
  }

  /**
   * Format parameter list
   */
  private formatParameters(params: ParamIR[]): string {
    if (params.length === 0) {
      return 'void';
    }

    return params.map(p => `${p.type} ${p.name}`).join(', ');
  }

  /**
   * Transform method body to replace member access
   * Simple heuristic: replace 'identifier' with 'this->identifier' if it matches a member
   */
  private transformMethodBody(body: string, className: string): string {
    // For MVP, we'll do a simple transformation
    // In the real implementation, this would use proper AST analysis

    // Replace 'x' with 'this->x' for member access
    // This is a simplified heuristic - will need improvement
    let transformed = body;

    // Common pattern: return x; → return this->x;
    transformed = transformed.replace(/\breturn\s+(\w+)\s*;/g, 'return this->$1;');

    // Assignment pattern: x = value; → this->x = value;
    transformed = transformed.replace(/\b(\w+)\s*=/g, 'this->$1 =');

    return transformed;
  }

  /**
   * Indent code by specified levels
   */
  private indentCode(code: string, levels: number): string {
    const indent = '    '.repeat(levels);
    const lines = code.split('\n');

    return lines.map(line => {
      if (line.trim()) {
        return indent + line.trimStart();
      }
      return '';
    }).join('\n');
  }

  /**
   * Generate ACSL annotations (placeholder for MVP)
   */
  generateACSL(ir: TranspilerIR): string {
    let acsl = '/* ACSL Annotations (Basic) */\n\n';

    for (const cls of ir.classes) {
      acsl += `/*@ predicate valid_${cls.name}(${cls.name}* obj) =\n`;
      acsl += `  @   \\valid(obj);\n`;
      acsl += `  @ */\n\n`;
    }

    return acsl;
  }
}

/**
 * Generate formatted C code with proper style
 */
export function formatCCode(code: string): string {
  // Basic formatting - could be enhanced with prettier or clang-format
  let formatted = code;

  // Ensure consistent line endings
  formatted = formatted.replace(/\r\n/g, '\n');

  // Remove trailing whitespace
  formatted = formatted.split('\n')
    .map(line => line.trimEnd())
    .join('\n');

  // Ensure file ends with newline
  if (!formatted.endsWith('\n')) {
    formatted += '\n';
  }

  return formatted;
}
