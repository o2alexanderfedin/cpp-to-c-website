# libclang C API Reference for C++ to C Transpiler

## Table of Contents

1. [Introduction](#introduction)
2. [API Overview](#api-overview)
3. [Core Concepts](#core-concepts)
4. [AST Traversal](#ast-traversal)
5. [Cursor API](#cursor-api)
6. [Type System](#type-system)
7. [C++ Specific Features](#c-specific-features)
8. [Diagnostics](#diagnostics)
9. [Source Locations](#source-locations)
10. [Code Generation Patterns](#code-generation-patterns)
11. [LibTooling vs libclang](#libtooling-vs-libclang)
12. [Complete API Reference](#complete-api-reference)
13. [Resources](#resources)

---

## Introduction

libclang is the stable C interface to the Clang compiler's Abstract Syntax Tree (AST) parser. It provides a relatively small, stable API that exposes facilities for:

- Parsing source code into an Abstract Syntax Tree (AST)
- Loading already-parsed ASTs
- Traversing the AST
- Associating physical source locations with elements within the AST
- Extracting detailed type information
- Handling diagnostics (errors and warnings)

**Key Characteristics:**
- **Stable API**: The C interfaces in libclang are intended to be relatively stable, allowing programmers to use libclang without worrying as much about Clang upgrades breaking existing code
- **Language**: Pure C API (not C++)
- **Main Header**: All functionality is exposed through `clang-c/Index.h`
- **Use Cases**: IDEs, documentation generators, static analysis tools, and transpilers

---

## API Overview

### Typical Workflow

```c
// 1. Create an index (shared context for translation units)
CXIndex index = clang_createIndex(0, 0);

// 2. Parse source file into translation unit
CXTranslationUnit unit = clang_parseTranslationUnit(
    index,
    "source.cpp",
    nullptr,           // compiler arguments
    0,                 // number of arguments
    nullptr,           // unsaved files
    0,                 // number of unsaved files
    CXTranslationUnit_None  // options
);

// 3. Get root cursor
CXCursor cursor = clang_getTranslationUnitCursor(unit);

// 4. Traverse AST
clang_visitChildren(cursor, visitor_callback, client_data);

// 5. Cleanup
clang_disposeTranslationUnit(unit);
clang_disposeIndex(index);
```

---

## Core Concepts

### CXIndex
A shared context for translation units. Created once and reused for parsing multiple files.

### CXTranslationUnit
Represents a single parsed translation unit (source file + includes).

### CXCursor
A pointer to a node in the AST. The central concept in libclang - cursors represent all AST elements (declarations, expressions, statements, etc.).

**Important**: In libclang terminology, pointers to the AST are called "Cursors", and a Cursor can have a parent and children.

### CXType
Represents a complete C++ type, including qualifiers and pointers. Contains:
- `CXTypeKind kind` - The type classification
- Opaque data for additional type information

### CXString
Clang's string type with reference counting. Must be disposed after use.

**String Handling Pattern:**
```c
CXString str = clang_getCursorSpelling(cursor);
const char* cstr = clang_getCString(str);
// Use cstr...
clang_disposeString(str);  // MUST dispose!
```

**C++ Helper for String Output:**
```cpp
ostream& operator<<(ostream& stream, const CXString& str) {
    stream << clang_getCString(str);
    clang_disposeString(str);
    return stream;
}
```

---

## AST Traversal

### clang_visitChildren()

The primary function for traversing the AST using the visitor pattern.

**Signature:**
```c
unsigned clang_visitChildren(
    CXCursor parent,
    CXCursorVisitor visitor,
    CXClientData client_data
);
```

**Visitor Callback Signature:**
```c
typedef enum CXChildVisitResult (*CXCursorVisitor)(
    CXCursor cursor,        // Current cursor being visited
    CXCursor parent,        // Parent of current cursor
    CXClientData client_data  // User data passed through
);
```

### Traversal Control (CXChildVisitResult)

The visitor callback must return one of three values:

1. **CXChildVisit_Break** - Terminates the cursor traversal completely
2. **CXChildVisit_Continue** - Continues with the next sibling, WITHOUT visiting children of current cursor
3. **CXChildVisit_Recurse** - Recursively traverse the children of this cursor

### Basic Traversal Example

```c
CXChildVisitResult visitor(CXCursor cursor, CXCursor parent, CXClientData client_data) {
    // Get cursor kind
    CXCursorKind kind = clang_getCursorKind(cursor);

    // Get cursor spelling (name)
    CXString spelling = clang_getCursorSpelling(cursor);
    CXString kindName = clang_getCursorKindSpelling(kind);

    printf("Cursor '%s' of kind '%s'\n",
           clang_getCString(spelling),
           clang_getCString(kindName));

    clang_disposeString(spelling);
    clang_disposeString(kindName);

    // Recurse into children
    return CXChildVisit_Recurse;
}

// Usage
clang_visitChildren(rootCursor, visitor, nullptr);
```

### Filtering by Source File

To only process nodes from the main source file (excluding includes):

```c
CXChildVisitResult visitor(CXCursor cursor, CXCursor parent, CXClientData client_data) {
    CXSourceLocation loc = clang_getCursorLocation(cursor);

    if (!clang_Location_isFromMainFile(loc)) {
        return CXChildVisit_Continue;  // Skip includes
    }

    // Process cursor...
    return CXChildVisit_Recurse;
}
```

### Tracking Tree Depth

```c
CXChildVisitResult visitor(CXCursor cursor, CXCursor parent, CXClientData client_data) {
    unsigned int* level = (unsigned int*)client_data;

    // Print with indentation
    for (unsigned i = 0; i < *level; i++) {
        printf("  ");
    }

    CXString spelling = clang_getCursorSpelling(cursor);
    printf("%s\n", clang_getCString(spelling));
    clang_disposeString(spelling);

    // Recurse with incremented level
    unsigned int nextLevel = *level + 1;
    clang_visitChildren(cursor, visitor, &nextLevel);

    return CXChildVisit_Continue;
}
```

---

## Cursor API

### Cursor Identification

```c
// Get cursor kind
CXCursorKind clang_getCursorKind(CXCursor);

// Get human-readable kind name
CXString clang_getCursorKindSpelling(CXCursorKind Kind);

// Get cursor spelling (name)
CXString clang_getCursorSpelling(CXCursor);

// Get qualified name (with namespace/class scope)
CXString clang_getCursorDisplayName(CXCursor);
```

### Cursor Relationships

```c
// Get semantic parent (what semantically contains this cursor)
CXCursor clang_getCursorSemanticParent(CXCursor);

// Get lexical parent (where cursor is written in source)
CXCursor clang_getCursorLexicalParent(CXCursor);
```

**Semantic vs Lexical Parent:**

For most declarations, semantic and lexical parents are the same. They diverge for out-of-line definitions:

```cpp
class C {
    void f();  // Semantic parent: C, Lexical parent: C
};

// Out-of-line definition
void C::f() {  // Semantic parent: C, Lexical parent: translation unit
    // ...
}
```

**Key Difference:**
- **Semantic parent**: What the cursor logically belongs to (affects semantics)
- **Lexical parent**: Where the cursor is written in source (can change without affecting semantics)

### Cursor Properties

```c
// Check if cursor is null
unsigned clang_Cursor_isNull(CXCursor);

// Check if cursor represents a declaration
unsigned clang_isDeclaration(CXCursorKind);

// Check if cursor represents a reference
unsigned clang_isReference(CXCursorKind);

// Check if cursor represents an expression
unsigned clang_isExpression(CXCursorKind);

// Check if cursor represents a statement
unsigned clang_isStatement(CXCursorKind);

// Check if cursor is valid
unsigned clang_isInvalid(CXCursorKind);
```

### Getting Referenced Cursor

```c
// For references, get the declaration being referenced
CXCursor clang_getCursorReferenced(CXCursor);

// For declarations, get the definition
CXCursor clang_getCursorDefinition(CXCursor);
```

---

## Type System

### Type Extraction from Cursors

```c
// Get type of a cursor (primary function)
CXType clang_getCursorType(CXCursor);

// For function cursors, get return type directly
CXType clang_getCursorResultType(CXCursor);
```

### Type Properties

```c
// Get type kind enumeration
CXTypeKind clang_getTypeKind(CXType);

// Get human-readable type spelling
CXString clang_getTypeSpelling(CXType);

// Get type kind as string
CXString clang_getTypeKindSpelling(CXTypeKind Kind);

// Check if two types are identical
unsigned clang_equalTypes(CXType A, CXType B);
```

### Type Transformations

```c
// Get canonical type (remove syntactic sugar)
CXType clang_getCanonicalType(CXType T);

// Get unqualified type (remove const/volatile/restrict)
CXType clang_getUnqualifiedType(CXType T);

// For reference types, get referenced type
CXType clang_getNonReferenceType(CXType T);
```

### Type Qualifiers

```c
// Check for const qualifier
unsigned clang_isConstQualifiedType(CXType T);

// Check for volatile qualifier
unsigned clang_isVolatileQualifiedType(CXType T);

// Check for restrict qualifier
unsigned clang_isRestrictQualifiedType(CXType T);

// Get address space
unsigned clang_getAddressSpace(CXType T);
```

### Pointer and Reference Types

```c
// For pointer/reference types, get pointee type
CXType clang_getPointeeType(CXType T);
```

**Example:**
```c
CXType type = clang_getCursorType(cursor);
if (type.kind == CXType_Pointer) {
    CXType pointeeType = clang_getPointeeType(type);
    // Process pointee type...
}
```

### Array Types

```c
// Get element type of array
CXType clang_getArrayElementType(CXType T);

// Get array size (for constant arrays)
long long clang_getArraySize(CXType T);

// Get number of elements (for arrays/vectors)
long long clang_getNumElements(CXType T);

// Generic element type getter (arrays, complex, vector)
CXType clang_getElementType(CXType T);
```

### Function Types

```c
// Get return type of function type
CXType clang_getResultType(CXType T);

// Get number of parameters
int clang_getNumArgTypes(CXType T);

// Get parameter type at index
CXType clang_getArgType(CXType T, unsigned i);

// Check if function is variadic
unsigned clang_isFunctionTypeVariadic(CXType T);

// Get calling convention
CXCallingConv clang_getFunctionTypeCallingConv(CXType T);
```

**Example - Processing Function Parameters:**
```c
CXType funcType = clang_getCursorType(cursor);
int numParams = clang_getNumArgTypes(funcType);

for (int i = 0; i < numParams; i++) {
    CXType paramType = clang_getArgType(funcType, i);
    CXString paramSpelling = clang_getTypeSpelling(paramType);
    printf("Param %d: %s\n", i, clang_getCString(paramSpelling));
    clang_disposeString(paramSpelling);
}
```

### Type Layout and Size

```c
// Get size of type in bytes
long long clang_Type_getSizeOf(CXType T);

// Get alignment in bytes
long long clang_Type_getAlignOf(CXType T);

// Get field offset in bits
long long clang_Type_getOffsetOf(CXType T, const char* S);
```

### Type Declarations

```c
// Get cursor for type's declaration
CXCursor clang_getTypeDeclaration(CXType T);
```

**Example - Getting Class from Type:**
```c
CXType type = clang_getCursorType(cursor);
CXCursor typeDecl = clang_getTypeDeclaration(type);
// typeDecl is the class/struct declaration cursor
```

### Template Types

```c
// Get number of template arguments
int clang_Type_getNumTemplateArguments(CXType T);

// Get template argument as type
CXType clang_Type_getTemplateArgumentAsType(CXType T, unsigned i);

// From cursor: get number of template arguments
int clang_Cursor_getNumTemplateArguments(CXCursor C);

// From cursor: get template argument type
CXType clang_Cursor_getTemplateArgumentType(CXCursor C, unsigned i);
```

---

## C++ Specific Features

### CXCursorKind Enumeration (C++ Subset)

#### Declarations

```c
CXCursor_ClassDecl = 4              // C++ class
CXCursor_StructDecl = 2             // C/C++ struct
CXCursor_UnionDecl = 3              // C/C++ union
CXCursor_EnumDecl = 5               // Enumeration
CXCursor_FieldDecl = 6              // Field in struct/union/class
CXCursor_FunctionDecl = 8           // Function
CXCursor_VarDecl = 9                // Variable
CXCursor_ParmDecl = 10              // Function/method parameter
CXCursor_TypedefDecl = 20           // Typedef
CXCursor_CXXMethod = 21             // C++ class method
CXCursor_Namespace = 22             // C++ namespace
CXCursor_Constructor = 24           // C++ constructor
CXCursor_Destructor = 25            // C++ destructor
CXCursor_ConversionFunction = 26    // C++ conversion function
CXCursor_TemplateTypeParameter = 27 // Template type parameter
CXCursor_NonTypeTemplateParameter = 28  // Non-type template parameter
CXCursor_TemplateTemplateParameter = 29 // Template template parameter
CXCursor_FunctionTemplate = 30      // C++ function template
CXCursor_ClassTemplate = 31         // C++ class template
CXCursor_ClassTemplatePartialSpecialization = 32
CXCursor_NamespaceAlias = 33        // Namespace alias
CXCursor_UsingDirective = 34        // Using directive
CXCursor_UsingDeclaration = 35      // Using declaration
CXCursor_TypeAliasDecl = 36         // Type alias declaration
CXCursor_CXXAccessSpecifier = 39    // public/protected/private
```

#### References

```c
CXCursor_TypeRef = 43               // Type reference
CXCursor_CXXBaseSpecifier = 44      // Base class specifier
CXCursor_TemplateRef = 45           // Template reference
CXCursor_NamespaceRef = 46          // Namespace reference
CXCursor_MemberRef = 47             // Member reference
```

#### Expressions (starting at 100)

```c
CXCursor_UnexposedExpr = 100
CXCursor_DeclRefExpr = 101          // Reference to declaration
CXCursor_MemberRefExpr = 102        // Member reference
CXCursor_CallExpr = 103             // Function call
CXCursor_IntegerLiteral = 106
CXCursor_FloatingLiteral = 107
CXCursor_StringLiteral = 109
CXCursor_CXXBoolLiteralExpr = 112
CXCursor_CXXNullPtrLiteralExpr = 113
CXCursor_CXXThisExpr = 114
CXCursor_CXXThrowExpr = 115
CXCursor_CXXNewExpr = 116
CXCursor_CXXDeleteExpr = 117
CXCursor_UnaryExpr = 118
CXCursor_ArraySubscriptExpr = 119
CXCursor_BinaryOperator = 120
CXCursor_CompoundAssignOperator = 121
CXCursor_ConditionalOperator = 122  // Ternary operator
CXCursor_CStyleCastExpr = 123
CXCursor_InitListExpr = 125
CXCursor_CXXStaticCastExpr = 128
CXCursor_CXXDynamicCastExpr = 129
CXCursor_CXXReinterpretCastExpr = 130
CXCursor_CXXConstCastExpr = 131
CXCursor_CXXFunctionalCastExpr = 132
CXCursor_CXXConstructExpr = 133
CXCursor_LambdaExpr = 144
```

#### Statements (starting at 200)

```c
CXCursor_UnexposedStmt = 200
CXCursor_DeclStmt = 202             // Declaration statement
CXCursor_CompoundStmt = 203         // Compound statement { }
CXCursor_IfStmt = 205
CXCursor_SwitchStmt = 206
CXCursor_WhileStmt = 207
CXCursor_DoStmt = 208
CXCursor_ForStmt = 209
CXCursor_ReturnStmt = 212
CXCursor_CXXCatchStmt = 223
CXCursor_CXXTryStmt = 224
CXCursor_CXXForRangeStmt = 225      // Range-based for
CXCursor_NullStmt = 230
```

### C++ Class/Method Introspection

```c
// Constructor checks
unsigned clang_CXXConstructor_isConvertingConstructor(CXCursor C);
unsigned clang_CXXConstructor_isCopyConstructor(CXCursor C);
unsigned clang_CXXConstructor_isDefaultConstructor(CXCursor C);
unsigned clang_CXXConstructor_isMoveConstructor(CXCursor C);

// Method property checks
unsigned clang_CXXMethod_isConst(CXCursor C);
unsigned clang_CXXMethod_isStatic(CXCursor C);
unsigned clang_CXXMethod_isVirtual(CXCursor C);
unsigned clang_CXXMethod_isPureVirtual(CXCursor C);
unsigned clang_CXXMethod_isDefaulted(CXCursor C);
unsigned clang_CXXMethod_isDeleted(CXCursor C);
unsigned clang_CXXMethod_isExplicit(CXCursor C);
unsigned clang_CXXMethod_isCopyAssignmentOperator(CXCursor C);
unsigned clang_CXXMethod_isMoveAssignmentOperator(CXCursor C);

// Record (class/struct) checks
unsigned clang_CXXRecord_isAbstract(CXCursor C);

// Field checks
unsigned clang_CXXField_isMutable(CXCursor C);
```

### Template Handling

```c
// Get template cursor kind from specialization
CXCursorKind clang_getTemplateCursorKind(CXCursor C);

// Get the template from which specialization was derived
CXCursor clang_getSpecializedCursorTemplate(CXCursor C);
```

**Template Instantiation:**
libclang visits all explicit and implicit class template instantiations when visiting a ClassTemplateDecl. For specializations, the API returns:
- The primary template, or
- The class template partial specialization from which it was instantiated

### Enumeration Handling

```c
// Check if enum is scoped (enum class)
unsigned clang_EnumDecl_isScoped(CXCursor C);

// Get underlying integer type of enum
CXType clang_getEnumDeclIntegerType(CXCursor C);

// Get constant value
long long clang_getEnumConstantDeclValue(CXCursor C);
unsigned long long clang_getEnumConstantDeclUnsignedValue(CXCursor C);
```

### Access Specifiers

To determine access level (public/protected/private):

```c
enum CX_CXXAccessSpecifier clang_getCXXAccessSpecifier(CXCursor);
```

Values:
- `CX_CXXInvalidAccessSpecifier`
- `CX_CXXPublic`
- `CX_CXXProtected`
- `CX_CXXPrivate`

---

## Diagnostics

### Core Diagnostic Types

```c
// Single diagnostic with severity, location, text, ranges, and fix-its
typedef struct CXDiagnostic;

// Group of diagnostics
typedef struct CXDiagnosticSet;
```

### Severity Levels

```c
enum CXDiagnosticSeverity {
    CXDiagnostic_Ignored,  // Ignored diagnostic
    CXDiagnostic_Note,     // Note
    CXDiagnostic_Warning,  // Warning
    CXDiagnostic_Error,    // Error
    CXDiagnostic_Fatal     // Fatal error (parser recovery unlikely)
};
```

### Getting Diagnostics

```c
// Get number of diagnostics
unsigned clang_getNumDiagnostics(CXTranslationUnit Unit);

// Get individual diagnostic
CXDiagnostic clang_getDiagnostic(CXTranslationUnit Unit, unsigned Index);

// Get diagnostic set
CXDiagnosticSet clang_getDiagnosticSetFromTU(CXTranslationUnit Unit);

// Dispose diagnostic
void clang_disposeDiagnostic(CXDiagnostic Diagnostic);
void clang_disposeDiagnosticSet(CXDiagnosticSet Diags);
```

### Diagnostic Information Extraction

```c
// Get severity level
enum CXDiagnosticSeverity clang_getDiagnosticSeverity(CXDiagnostic);

// Get diagnostic text
CXString clang_getDiagnosticSpelling(CXDiagnostic);

// Get source location where caret would be printed
CXSourceLocation clang_getDiagnosticLocation(CXDiagnostic);

// Get category number (for grouping related diagnostics)
unsigned clang_getDiagnosticCategory(CXDiagnostic);

// Get category name
CXString clang_getDiagnosticCategoryText(CXDiagnostic);

// Get enabling compiler option (e.g., "-Wconversion")
CXString clang_getDiagnosticOption(CXDiagnostic, CXString* Disable);
```

### Diagnostic Ranges

```c
// Get number of source ranges
unsigned clang_getDiagnosticNumRanges(CXDiagnostic);

// Get source range highlighting problem
CXSourceRange clang_getDiagnosticRange(CXDiagnostic, unsigned Range);
```

### Fix-It Hints

```c
// Get number of fix-it suggestions
unsigned clang_getDiagnosticNumFixIts(CXDiagnostic);

// Get fix-it suggestion
CXString clang_getDiagnosticFixIt(
    CXDiagnostic Diagnostic,
    unsigned FixIt,
    CXSourceRange* ReplacementRange  // Output: range to replace
);
```

### Processing Diagnostics Example

```c
unsigned numDiags = clang_getNumDiagnostics(tu);

for (unsigned i = 0; i < numDiags; i++) {
    CXDiagnostic diag = clang_getDiagnostic(tu, i);

    CXDiagnosticSeverity severity = clang_getDiagnosticSeverity(diag);
    CXString spelling = clang_getDiagnosticSpelling(diag);

    printf("Diagnostic: %s\n", clang_getCString(spelling));

    // Check for fix-its
    unsigned numFixIts = clang_getDiagnosticNumFixIts(diag);
    for (unsigned j = 0; j < numFixIts; j++) {
        CXSourceRange range;
        CXString fixIt = clang_getDiagnosticFixIt(diag, j, &range);
        printf("  Fix-It: %s\n", clang_getCString(fixIt));
        clang_disposeString(fixIt);
    }

    clang_disposeString(spelling);
    clang_disposeDiagnostic(diag);
}
```

### Formatted Diagnostic Output

```c
// Format diagnostic with configurable options
CXString clang_formatDiagnostic(
    CXDiagnostic Diagnostic,
    unsigned Options  // CXDiagnostic_DisplayXXX flags
);
```

Display options:
- `CXDiagnostic_DisplaySourceLocation` - Include source location
- `CXDiagnostic_DisplayColumn` - Include column number
- `CXDiagnostic_DisplaySourceRanges` - Include source ranges
- `CXDiagnostic_DisplayOption` - Include command-line option
- `CXDiagnostic_DisplayCategoryId` - Include category ID
- `CXDiagnostic_DisplayCategoryName` - Include category name

---

## Source Locations

### Location Types

```c
typedef struct CXSourceLocation;   // Single point in source
typedef struct CXSourceRange;      // Range in source (start + end)
```

### Getting Locations

```c
// Get cursor location
CXSourceLocation clang_getCursorLocation(CXCursor);

// Get cursor extent (source range)
CXSourceRange clang_getCursorExtent(CXCursor);

// Get location from file/line/column
CXSourceLocation clang_getLocation(
    CXTranslationUnit tu,
    CXFile file,
    unsigned line,
    unsigned column
);

// Get location from file/offset
CXSourceLocation clang_getLocationForOffset(
    CXTranslationUnit tu,
    CXFile file,
    unsigned offset
);
```

### Extracting Location Information

```c
// Expand location into file, line, column, offset
void clang_getExpansionLocation(
    CXSourceLocation location,
    CXFile* file,           // Output
    unsigned* line,         // Output
    unsigned* column,       // Output
    unsigned* offset        // Output
);

// Alternative: file location
void clang_getFileLocation(
    CXSourceLocation location,
    CXFile* file,
    unsigned* line,
    unsigned* column,
    unsigned* offset
);

// Get filename from file handle
CXString clang_getFileName(CXFile SFile);
```

### Location Checks

```c
// Check if location is from main file
unsigned clang_Location_isFromMainFile(CXSourceLocation location);

// Check if location is in system header
unsigned clang_Location_isInSystemHeader(CXSourceLocation location);
```

### Source Range Operations

```c
// Get start of range
CXSourceLocation clang_getRangeStart(CXSourceRange range);

// Get end of range
CXSourceLocation clang_getRangeEnd(CXSourceRange range);

// Check if range is null
unsigned clang_Range_isNull(CXSourceRange range);
```

### Example - Extracting Location Info

```c
CXSourceLocation loc = clang_getCursorLocation(cursor);

CXFile file;
unsigned line, column, offset;
clang_getFileLocation(loc, &file, &line, &column, &offset);

CXString filename = clang_getFileName(file);
printf("Location: %s:%u:%u\n",
       clang_getCString(filename), line, column);
clang_disposeString(filename);
```

---

## Code Generation Patterns

### Important Note on Code Generation

**libclang is designed for parsing and analyzing code, NOT for generating code.** While libclang excels at parsing and traversing ASTs, it does NOT provide facilities to:
- Create new CXTokens programmatically
- Modify the AST
- Generate source code directly from AST nodes

### Recommended Approach for Transpilation

The standard approach for building a transpiler with libclang:

1. **Parse** source with libclang
2. **Traverse** AST to extract information
3. **Manually generate** output code based on extracted information

### Code Generation Strategy

```c
// 1. Parse input
CXIndex index = clang_createIndex(0, 0);
CXTranslationUnit unit = clang_parseTranslationUnit(/*...*/);

// 2. Extract information during traversal
struct TranspilerContext {
    FILE* output;
    // Track context (indentation, current scope, etc.)
    int indentLevel;
    // Store gathered information
    // ...
};

CXChildVisitResult visitor(CXCursor cursor, CXCursor parent, CXClientData data) {
    TranspilerContext* ctx = (TranspilerContext*)data;
    CXCursorKind kind = clang_getCursorKind(cursor);

    switch (kind) {
        case CXCursor_ClassDecl: {
            // Extract class information
            CXString name = clang_getCursorSpelling(cursor);
            // Generate C struct
            fprintf(ctx->output, "typedef struct %s {\n",
                    clang_getCString(name));
            clang_disposeString(name);

            // Visit members
            ctx->indentLevel++;
            clang_visitChildren(cursor, visitor, data);
            ctx->indentLevel--;

            fprintf(ctx->output, "} %s;\n", /*...*/);
            return CXChildVisit_Continue;
        }

        case CXCursor_CXXMethod: {
            // Extract method information
            CXType returnType = clang_getCursorResultType(cursor);
            CXString returnTypeSpelling = clang_getTypeSpelling(returnType);
            CXString methodName = clang_getCursorSpelling(cursor);

            // Generate C function
            fprintf(ctx->output, "%s %s_method(",
                    clang_getCString(returnTypeSpelling),
                    clang_getCString(methodName));

            // Add 'this' parameter
            // Extract other parameters
            // ...

            clang_disposeString(returnTypeSpelling);
            clang_disposeString(methodName);
            return CXChildVisit_Continue;
        }

        // Handle other cursor kinds...
    }

    return CXChildVisit_Recurse;
}

// 3. Run transpilation
TranspilerContext ctx = { .output = fopen("output.c", "w"), .indentLevel = 0 };
CXCursor root = clang_getTranslationUnitCursor(unit);
clang_visitChildren(root, visitor, &ctx);
fclose(ctx.output);
```

### Using Templates for Code Generation

Many projects combine libclang with template engines (like Jinja2 in Python):

1. Use libclang to parse and extract AST information
2. Store extracted data in intermediate structures
3. Pass data to template engine to generate output code

### Information to Extract for C++ to C Transpilation

For each C++ construct, extract:

**For Classes:**
- Class name
- Member variables (names, types, access levels)
- Member functions (signatures, access levels, virtual/static/const flags)
- Base classes
- Constructor/destructor signatures

**For Methods:**
- Return type
- Method name
- Parameters (names and types)
- const/static/virtual qualifiers
- Access level

**For Templates:**
- Template parameters
- Instantiations (if explicit)

**For Types:**
- Type spelling
- Pointer/reference levels
- const/volatile qualifiers
- Array dimensions

### Output Generation Helpers

```c
// Helper: Generate indentation
void print_indent(FILE* out, int level) {
    for (int i = 0; i < level; i++) {
        fprintf(out, "    ");
    }
}

// Helper: Convert C++ type to C type
const char* convert_type(CXType type) {
    // Handle type conversions
    CXTypeKind kind = type.kind;
    switch (kind) {
        case CXType_Bool: return "int";  // C doesn't have bool
        // ... other conversions
        default: {
            CXString spelling = clang_getTypeSpelling(type);
            // Return spelling (caller must free)
            return clang_getCString(spelling);
        }
    }
}

// Helper: Generate unique mangled name for method
void mangle_method_name(char* buffer, size_t size,
                       const char* className, const char* methodName) {
    snprintf(buffer, size, "%s_%s", className, methodName);
}
```

---

## LibTooling vs libclang

### Comparison

| Feature | libclang | LibTooling |
|---------|----------|------------|
| **Language** | C API | C++ API |
| **API Stability** | Stable, versioned | Less stable, evolves with Clang |
| **AST Access** | High-level, abstracted | Direct, low-level access |
| **Ease of Use** | Simpler, more limited | More complex, more powerful |
| **Precision** | Abstracted, some limitations | Full AST access, very precise |
| **Macro Handling** | Known issues/bugs | Better handling |
| **Code Completion** | Built-in support | Not built-in |
| **Bindings** | Python, many others | Primarily C++ |
| **Use Cases** | IDEs, simple analysis, bindings | Refactoring, complex analysis, transformation |

### Key Differences

**LibTooling:**
- The preferred way to access the C++ AST
- Much more powerful and precise
- Direct access to Clang's internals
- Better for complex refactoring and transformation tools
- Requires C++ and linking against Clang libraries

**libclang:**
- Stable C interface
- Higher level abstraction
- Easier to use for simpler tasks
- API unlikely to break between versions
- Known deficiencies are unlikely to be fixed (to maintain API stability)
- Better for language bindings and tools needing stability

### Recommendation for C++ to C Transpiler

**Use libclang if:**
- You need a stable API
- You want to use C (not C++)
- You want simpler, higher-level abstractions
- You need language bindings (Python, etc.)

**Use LibTooling if:**
- You need maximum precision and control
- You're comfortable with C++
- You need to handle complex macro scenarios
- You need to perform code transformations (less relevant for transpilers)

**For our C++ to C transpiler:**
- **libclang is recommended** because:
  - We need C API for WASM compilation
  - We need stability
  - The high-level abstractions are sufficient for transpilation
  - We don't need to modify the AST (only read it)

---

## Complete API Reference

### Index Management

```c
CXIndex clang_createIndex(int excludeDeclarationsFromPCH,
                         int displayDiagnostics);
void clang_disposeIndex(CXIndex index);
void clang_CXIndex_setGlobalOptions(CXIndex, unsigned options);
unsigned clang_CXIndex_getGlobalOptions(CXIndex);
CXIndex clang_createIndexWithOptions(const CXIndexOptions* options);
```

### Translation Unit Operations

```c
CXTranslationUnit clang_parseTranslationUnit(
    CXIndex CIdx,
    const char* source_filename,
    const char* const* command_line_args,
    int num_command_line_args,
    struct CXUnsavedFile* unsaved_files,
    unsigned num_unsaved_files,
    unsigned options
);

void clang_disposeTranslationUnit(CXTranslationUnit);

CXCursor clang_getTranslationUnitCursor(CXTranslationUnit);
CXFile clang_getFile(CXTranslationUnit tu, const char* file_name);
const char* clang_getFileContents(CXTranslationUnit tu, CXFile file, size_t* size);
```

### Cursor Traversal

```c
unsigned clang_visitChildren(CXCursor parent,
                             CXCursorVisitor visitor,
                             CXClientData client_data);
```

### Cursor Manipulation

```c
CXCursorKind clang_getCursorKind(CXCursor);
CXString clang_getCursorKindSpelling(CXCursorKind Kind);
CXString clang_getCursorSpelling(CXCursor);
CXString clang_getCursorDisplayName(CXCursor);
CXType clang_getCursorType(CXCursor C);
CXType clang_getCursorResultType(CXCursor C);
CXCursor clang_getCursorSemanticParent(CXCursor cursor);
CXCursor clang_getCursorLexicalParent(CXCursor cursor);
CXCursor clang_getCursorReferenced(CXCursor);
CXCursor clang_getCursorDefinition(CXCursor);
unsigned clang_isCursorDefinition(CXCursor);
unsigned clang_Cursor_isNull(CXCursor cursor);
unsigned clang_equalCursors(CXCursor, CXCursor);
int clang_Cursor_getNumArguments(CXCursor C);
CXCursor clang_Cursor_getArgument(CXCursor C, unsigned i);
```

### Type Operations

```c
CXType clang_getCursorType(CXCursor C);
CXString clang_getTypeSpelling(CXType CT);
CXType clang_getTypedefDeclUnderlyingType(CXCursor C);
CXType clang_getEnumDeclIntegerType(CXCursor C);
long long clang_getEnumConstantDeclValue(CXCursor C);
unsigned long long clang_getEnumConstantDeclUnsignedValue(CXCursor C);
CXType clang_getCanonicalType(CXType T);
unsigned clang_isConstQualifiedType(CXType T);
unsigned clang_isVolatileQualifiedType(CXType T);
unsigned clang_isRestrictQualifiedType(CXType T);
CXType clang_getPointeeType(CXType T);
CXCursor clang_getTypeDeclaration(CXType T);
CXString clang_getTypeKindSpelling(CXTypeKind K);
enum CXCallingConv clang_getFunctionTypeCallingConv(CXType T);
CXType clang_getResultType(CXType T);
int clang_getNumArgTypes(CXType T);
CXType clang_getArgType(CXType T, unsigned i);
unsigned clang_isFunctionTypeVariadic(CXType T);
CXType clang_getArrayElementType(CXType T);
long long clang_getArraySize(CXType T);
long long clang_Type_getSizeOf(CXType T);
long long clang_Type_getAlignOf(CXType T);
```

### C++ Specific

```c
unsigned clang_CXXConstructor_isConvertingConstructor(CXCursor C);
unsigned clang_CXXConstructor_isCopyConstructor(CXCursor C);
unsigned clang_CXXConstructor_isDefaultConstructor(CXCursor C);
unsigned clang_CXXConstructor_isMoveConstructor(CXCursor C);
unsigned clang_CXXField_isMutable(CXCursor C);
unsigned clang_CXXMethod_isConst(CXCursor C);
unsigned clang_CXXMethod_isDefaulted(CXCursor C);
unsigned clang_CXXMethod_isDeleted(CXCursor C);
unsigned clang_CXXMethod_isPureVirtual(CXCursor C);
unsigned clang_CXXMethod_isStatic(CXCursor C);
unsigned clang_CXXMethod_isVirtual(CXCursor C);
unsigned clang_CXXMethod_isCopyAssignmentOperator(CXCursor C);
unsigned clang_CXXMethod_isMoveAssignmentOperator(CXCursor C);
unsigned clang_CXXMethod_isExplicit(CXCursor C);
unsigned clang_CXXRecord_isAbstract(CXCursor C);
unsigned clang_EnumDecl_isScoped(CXCursor C);
enum CX_CXXAccessSpecifier clang_getCXXAccessSpecifier(CXCursor);
CXCursorKind clang_getTemplateCursorKind(CXCursor C);
CXCursor clang_getSpecializedCursorTemplate(CXCursor C);
```

### Template Arguments

```c
int clang_Cursor_getNumTemplateArguments(CXCursor C);
enum CXTemplateArgumentKind clang_Cursor_getTemplateArgumentKind(CXCursor C, unsigned I);
CXType clang_Cursor_getTemplateArgumentType(CXCursor C, unsigned I);
long long clang_Cursor_getTemplateArgumentValue(CXCursor C, unsigned I);
unsigned long long clang_Cursor_getTemplateArgumentUnsignedValue(CXCursor C, unsigned I);
```

### Source Locations

```c
CXSourceLocation clang_getCursorLocation(CXCursor);
CXSourceRange clang_getCursorExtent(CXCursor);
CXSourceLocation clang_getLocation(CXTranslationUnit tu, CXFile file,
                                   unsigned line, unsigned column);
void clang_getExpansionLocation(CXSourceLocation location,
                                CXFile* file, unsigned* line,
                                unsigned* column, unsigned* offset);
void clang_getFileLocation(CXSourceLocation location,
                           CXFile* file, unsigned* line,
                           unsigned* column, unsigned* offset);
CXString clang_getFileName(CXFile SFile);
unsigned clang_Location_isFromMainFile(CXSourceLocation location);
unsigned clang_Location_isInSystemHeader(CXSourceLocation location);
CXSourceLocation clang_getRangeStart(CXSourceRange range);
CXSourceLocation clang_getRangeEnd(CXSourceRange range);
```

### Diagnostics

```c
unsigned clang_getNumDiagnostics(CXTranslationUnit Unit);
CXDiagnostic clang_getDiagnostic(CXTranslationUnit Unit, unsigned Index);
CXDiagnosticSet clang_getDiagnosticSetFromTU(CXTranslationUnit Unit);
void clang_disposeDiagnostic(CXDiagnostic Diagnostic);
void clang_disposeDiagnosticSet(CXDiagnosticSet Diags);
CXString clang_formatDiagnostic(CXDiagnostic Diagnostic, unsigned Options);
enum CXDiagnosticSeverity clang_getDiagnosticSeverity(CXDiagnostic);
CXSourceLocation clang_getDiagnosticLocation(CXDiagnostic);
CXString clang_getDiagnosticSpelling(CXDiagnostic);
CXString clang_getDiagnosticOption(CXDiagnostic Diag, CXString* Disable);
unsigned clang_getDiagnosticCategory(CXDiagnostic);
CXString clang_getDiagnosticCategoryText(CXDiagnostic);
unsigned clang_getDiagnosticNumRanges(CXDiagnostic);
CXSourceRange clang_getDiagnosticRange(CXDiagnostic Diagnostic, unsigned Range);
unsigned clang_getDiagnosticNumFixIts(CXDiagnostic Diagnostic);
CXString clang_getDiagnosticFixIt(CXDiagnostic Diagnostic, unsigned FixIt,
                                  CXSourceRange* ReplacementRange);
```

### Token Operations

```c
CXString clang_getTokenSpelling(CXTranslationUnit, CXToken);
CXSourceLocation clang_getTokenLocation(CXTranslationUnit, CXToken);
CXSourceRange clang_getTokenExtent(CXTranslationUnit, CXToken);
void clang_tokenize(CXTranslationUnit TU, CXSourceRange Range,
                    CXToken** Tokens, unsigned* NumTokens);
void clang_disposeTokens(CXTranslationUnit TU, CXToken* Tokens,
                        unsigned NumTokens);
```

### String Operations

```c
const char* clang_getCString(CXString string);
void clang_disposeString(CXString string);
```

### Cursor Classification

```c
unsigned clang_isDeclaration(CXCursorKind);
unsigned clang_isReference(CXCursorKind);
unsigned clang_isExpression(CXCursorKind);
unsigned clang_isStatement(CXCursorKind);
unsigned clang_isAttribute(CXCursorKind);
unsigned clang_isInvalid(CXCursorKind);
unsigned clang_isTranslationUnit(CXCursorKind);
unsigned clang_isPreprocessing(CXCursorKind);
unsigned clang_isUnexposed(CXCursorKind);
```

---

## Resources

### Official Documentation

- [Libclang Tutorial - Clang 22.0.0](https://clang.llvm.org/docs/LibClang.html)
- [C Interface to Clang - Doxygen](https://clang.llvm.org/doxygen/group__CINDEX.html)
- [Type Information for CXCursors](https://clang.llvm.org/doxygen/group__CINDEX__TYPES.html)
- [Cursor Traversal](https://clang.llvm.org/doxygen/group__CINDEX__CURSOR__TRAVERSAL.html)
- [Diagnostic Reporting](https://clang.llvm.org/doxygen/group__CINDEX__DIAG.html)
- [C++ AST Introspection](https://clang.llvm.org/doxygen/group__CINDEX__CPP.html)
- [Physical Source Locations](https://clang.llvm.org/doxygen/group__CINDEX__LOCATIONS.html)
- [Choosing the Right Interface](https://clang.llvm.org/docs/Tooling.html)

### Tutorials and Examples

- [Using libclang to Parse C++ (libclang 101)](https://shaharmike.com/cpp/libclang/)
- [Baby steps with libclang: Walking an AST](https://bastian.rieck.me/blog/2015/baby_steps_libclang_ast/)
- [Implementing a code generator with libclang](https://szelei.me/code-generator/)
- [Introduction to libclang (Friday Q&A)](https://www.mikeash.com/pyblog/friday-qa-2014-01-24-introduction-to-libclang.html)

### Source Code References

- [clang/include/clang-c/Index.h - Complete API Header](https://github.com/llvm/llvm-project/blob/main/clang/include/clang-c/Index.h)
- [libclang-sample GitHub Repository](https://github.com/sabottenda/libclang-sample)

### Related Resources

- [Introduction to the Clang AST](https://clang.llvm.org/docs/IntroductionToTheClangAST.html)
- [Understanding the Clang AST](https://jonasdevlieghere.com/post/understanding-the-clang-ast/)
- [Clang's Expressive Diagnostics](https://clang.llvm.org/diagnostics.html)

### Language Bindings

- [Clang.jl - Julia bindings](https://juliainterop.github.io/Clang.jl/stable/)
- [clang.cindex - Python bindings](https://libclang.readthedocs.io/)

---

## Summary for C++ to C Transpiler

### Essential Functions to Use

1. **Initialization:**
   - `clang_createIndex()`
   - `clang_parseTranslationUnit()`
   - `clang_getTranslationUnitCursor()`

2. **AST Traversal:**
   - `clang_visitChildren()` - Core traversal
   - `clang_getCursorKind()` - Identify node type
   - `clang_getCursorSpelling()` - Get names

3. **Type Information:**
   - `clang_getCursorType()` - Get type from cursor
   - `clang_getTypeSpelling()` - Get type as string
   - `clang_getPointeeType()` - Handle pointers
   - `clang_getResultType()` / `clang_getNumArgTypes()` / `clang_getArgType()` - Function signatures

4. **C++ Features:**
   - `clang_CXXMethod_is*()` - Method properties
   - `clang_getCXXAccessSpecifier()` - Access levels
   - `clang_getCursorSemanticParent()` - Class relationships

5. **Diagnostics:**
   - `clang_getNumDiagnostics()` / `clang_getDiagnostic()`
   - `clang_getDiagnosticSpelling()`

6. **Cleanup:**
   - `clang_disposeString()` - For all CXString
   - `clang_disposeTranslationUnit()`
   - `clang_disposeIndex()`

### Key Cursor Kinds for Transpilation

- `CXCursor_ClassDecl` - Classes to convert to structs
- `CXCursor_CXXMethod` - Methods to convert to functions
- `CXCursor_Constructor` / `CXCursor_Destructor` - Special handling
- `CXCursor_FieldDecl` - Member variables
- `CXCursor_FunctionDecl` - Functions
- `CXCursor_VarDecl` - Variables
- `CXCursor_Namespace` - For name mangling

### Workflow Summary

1. Parse C++ source file with libclang
2. Traverse AST with `clang_visitChildren()`
3. For each cursor, extract:
   - Cursor kind (what it is)
   - Name/spelling
   - Type information
   - C++ specific properties
   - Location information
4. Generate equivalent C code manually based on extracted information
5. Handle diagnostics for error reporting

---

**Document Version:** 1.0
**Created:** 2025-12-23
**libclang Version Referenced:** Clang 22.0.0git / LLVM 15.x+
