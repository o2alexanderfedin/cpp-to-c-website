/**
 * Intermediate Representation (IR) types for C++ to C transpilation
 * Plain JavaScript objects representing parsed C++ constructs
 */

export interface ParamIR {
  name: string;
  type: string;
}

export interface MemberIR {
  name: string;
  type: string;
  access: 'public' | 'private' | 'protected';
}

export interface MethodIR {
  name: string;
  returnType: string;
  params: ParamIR[];
  body: string; // Source code snippet
  access: 'public' | 'private' | 'protected';
  isConstructor: boolean;
  isDestructor: boolean;
  isStatic: boolean;
  isVirtual: boolean;
}

export interface ClassIR {
  name: string;
  members: MemberIR[];
  methods: MethodIR[];
  baseClasses: string[];
}

export interface FunctionIR {
  name: string;
  returnType: string;
  params: ParamIR[];
  body: string;
}

export interface GlobalVariableIR {
  name: string;
  type: string;
  initializer?: string;
}

/**
 * Complete transpilation intermediate representation
 */
export interface TranspilerIR {
  classes: ClassIR[];
  functions: FunctionIR[];
  globalVariables: GlobalVariableIR[];
}
