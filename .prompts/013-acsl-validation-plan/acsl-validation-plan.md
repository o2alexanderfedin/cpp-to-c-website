# ACSL Annotation Validation Implementation Plan

**Plan Date:** 2025-12-19
**Epic:** ACSL Validation & Generation Infrastructure
**Research Input:** acsl-validation-research.md
**Objective:** Implement ACSL annotation generation for transpiled C++ code and establish comprehensive validation infrastructure

---

<plan>
  <summary>
    Implementation plan for ACSL annotation generation and validation infrastructure. The research revealed that while ACSL annotations exist for runtime library (Epic #15, v1.15.0), automatic ACSL generation for transpiler-generated C code is NOT implemented despite documentation references. This plan addresses both implementing ACSL generation for transpiled code AND establishing comprehensive validation using Frama-C integration testing.

    The plan combines: (1) ACSL generator implementation for C++ language constructs, (2) syntax validation infrastructure, (3) Frama-C CLI integration for semantic verification, (4) comprehensive test suite, and (5) CI/CD integration for continuous validation.
  </summary>

  <key_research_findings>
    <finding>
      **Runtime Library Only:** ACSL annotations exist for exception_runtime.h, rtti_runtime.h with 100% syntax validation and 65.7% WP proof coverage. No transpiler output annotations.
    </finding>
    <finding>
      **Documentation Gap:** SAFETY_CRITICAL_GUIDE.md references `--generate-acsl` flag (lines 369, 621, 693) but implementation does not exist in src/ directory.
    </finding>
    <finding>
      **Validation Infrastructure Mature:** Frama-C integration via CLI is production-ready with verify_acsl.sh (syntax), verify_exception_runtime_wp.sh (WP), run_all_verifications.sh (master suite).
    </finding>
    <finding>
      **Frama-C Version:** 31.0 (Gallium) installed, compatible with ACSL v1.22+. CLI patterns proven: `frama-c -cpp-extra-args="-Iruntime" file.h` for syntax, `frama-c -wp -wp-rte` for verification.
    </finding>
    <finding>
      **CI/CD Gap:** Verification scripts exist but not integrated in GitHub Actions workflow. No automated regression prevention.
    </finding>
  </key_research_findings>

  <phases>
    <phase number="1" name="acsl-generator-design-and-infrastructure">
      <objective>
        Design ACSL annotation generator architecture and create infrastructure for integrating with transpiler AST
      </objective>

      <background>
        Research finding: No ACSL generation capability exists. Documentation references `--generate-acsl` flag but implementation is missing. Runtime library annotations are manually written. Transpiler uses Clang AST for code analysis - this AST must be leveraged for ACSL generation.
      </background>

      <tasks>
        <task priority="critical" category="architecture">
          Design ACSLGenerator class architecture
          - Determine integration point in transpiler pipeline (post-AST analysis, pre-code emission)
          - Define visitor pattern for C++ AST nodes → ACSL annotation mapping
          - Specify annotation storage format (in-memory during transpilation, emit with C code)
          - Design CLI flag interface: `--generate-acsl` (boolean), `--acsl-level=<basic|full>` (verbosity)
        </task>

        <task priority="critical" category="implementation">
          Create ACSLGenerator base class (src/codegen/ACSLGenerator.h/.cpp)
          - AST visitor interface for function declarations, loop statements, class members
          - Annotation formatting utilities (comment block generation, ACSL syntax escaping)
          - Configuration storage (ACSL level, enabled annotation types)
          - Integration with CodeGenerator class (emit annotations with C code)
        </task>

        <task priority="high" category="implementation">
          Implement ACSLFunctionAnnotator (src/codegen/ACSLFunctionAnnotator.h/.cpp)
          - Generate function contracts (requires, ensures, assigns) from C++ function signatures
          - Extract preconditions from C++ asserts, explicit checks (if present)
          - Infer postconditions from return type and function semantics
          - Derive assigns clauses from parameter analysis (pointer/reference parameters)
        </task>

        <task priority="high" category="implementation">
          Implement ACSLLoopAnnotator (src/codegen/ACSLLoopAnnotator.h/.cpp)
          - Generate loop invariants from loop structure analysis
          - Derive loop assigns from loop body variable usage
          - Generate loop variant for termination proof (based on loop counter/iterator)
          - Handle nested loops with scoped invariants
        </task>

        <task priority="medium" category="implementation">
          Implement ACSLClassAnnotator (src/codegen/ACSLClassAnnotator.h/.cpp)
          - Generate predicates for class invariants (valid_ClassName)
          - Annotate vtable structure validity (for polymorphic classes)
          - Generate constructor postconditions (object initialization)
          - Generate destructor preconditions (object validity)
        </task>

        <task priority="medium" category="cli">
          Add CLI flags to transpiler main.cpp
          - `--generate-acsl` flag (enable ACSL generation, default: off)
          - `--acsl-level=<basic|full>` (annotation verbosity, default: basic)
          - `--acsl-output=<inline|separate>` (inline comments vs. separate .acsl file, default: inline)
          - Integration with existing argparse/CLI framework
        </task>

        <task priority="low" category="testing">
          Create ACSLGeneratorTest.cpp unit tests
          - Test annotation formatting utilities (comment block generation, escaping)
          - Test AST visitor dispatch (ensure correct annotator is called for each node type)
          - Test CLI flag parsing and configuration propagation
          - Mock AST nodes for testing without full transpiler run
        </task>
      </tasks>

      <deliverables>
        <deliverable>src/codegen/ACSLGenerator.h (base class, ~150 lines)</deliverable>
        <deliverable>src/codegen/ACSLGenerator.cpp (implementation, ~200 lines)</deliverable>
        <deliverable>src/codegen/ACSLFunctionAnnotator.h/cpp (~250 lines total)</deliverable>
        <deliverable>src/codegen/ACSLLoopAnnotator.h/cpp (~200 lines total)</deliverable>
        <deliverable>src/codegen/ACSLClassAnnotator.h/cpp (~300 lines total)</deliverable>
        <deliverable>src/main.cpp (CLI flag additions, ~50 lines modified)</deliverable>
        <deliverable>tests/codegen/ACSLGeneratorTest.cpp (~300 lines, 15+ test cases)</deliverable>
      </deliverables>

      <dependencies>
        <dependency>Transpiler AST infrastructure (exists - Clang AST)</dependency>
        <dependency>CodeGenerator class (exists - src/codegen/CodeGenerator.*)</dependency>
        <dependency>CLI framework (exists - argparse or similar)</dependency>
      </dependencies>

      <success_criteria>
        <criterion>ACSLGenerator class compiles and integrates with transpiler pipeline</criterion>
        <criterion>CLI flags are parsed and configuration is accessible to annotators</criterion>
        <criterion>Unit tests pass (15+ test cases covering annotation formatting and dispatch)</criterion>
        <criterion>No compilation warnings or errors introduced</criterion>
      </success_criteria>

      <execution_notes>
        **TDD Approach:**
        1. Write failing test for annotation formatting (e.g., function contract generation)
        2. Implement minimal ACSLGenerator code to pass test
        3. Refactor and add more tests incrementally

        **AST Integration:**
        - Reuse existing Clang AST traversal in transpiler
        - Insert ACSL generation visitor calls before C code emission
        - Annotations should be stored in intermediate representation, emitted with C code

        **ACSL Standard Compliance:**
        - Reference ACSL v1.22 specification for syntax rules
        - Use existing runtime library annotations as examples (exception_runtime.h, rtti_runtime.h)
        - Validate generated annotations against Frama-C parser (Phase 2)

        **Code Examples from Research:**
        - Function contract pattern: See acsl-validation-research.md, exception_runtime.h lines 57-109
        - Loop invariant pattern: See exception_runtime.cpp lines 81-84
        - Predicate pattern: See rtti_runtime.h lines 60-126
      </execution_notes>
    </phase>

    <phase number="2" name="acsl-syntax-validator-implementation">
      <objective>
        Create unit-level ACSL syntax validator for fast validation without requiring Frama-C installation
      </objective>

      <background>
        Research finding: Frama-C CLI provides authoritative syntax validation but is slow and requires external tool. For rapid development feedback, a lightweight syntax validator is needed. This validator will catch common errors (missing semicolons, invalid predicates, scope issues) before invoking Frama-C.
      </background>

      <tasks>
        <task priority="high" category="implementation">
          Design ACSLSyntaxValidator class (src/validation/ACSLSyntaxValidator.h/.cpp)
          - Regex-based or parser-based validation approach (recommend regex for MVP, parser for future)
          - Validation rules for each ACSL clause type (requires, ensures, assigns, loop invariant, etc.)
          - Error reporting with line numbers and suggestions
          - Support for both inline comments (`/*@ ... */`) and line comments (`//@`)
        </task>

        <task priority="high" category="validation-rules">
          Implement function contract validation
          - `requires` clause: Check predicate syntax, variable scope references
          - `ensures` clause: Check return value references (`\result`), variable scope
          - `assigns` clause: Check location syntax (`\nothing`, variable lists, `*ptr`)
          - Detect missing semicolons, unbalanced parentheses, undefined predicates
        </task>

        <task priority="high" category="validation-rules">
          Implement loop annotation validation
          - `loop invariant`: Check predicate syntax, loop variable references
          - `loop assigns`: Check location syntax, ensure all modified variables listed
          - `loop variant`: Check expression syntax, ensure decreasing integer expression
          - Validate nesting (loop annotations must be inside function with contract)
        </task>

        <task priority="medium" category="validation-rules">
          Implement predicate and logic validation
          - Predicate definitions: Check syntax `predicate name(params) = expression;`
          - Logic operators: Validate `\valid`, `\valid_read`, `\null`, `\forall`, `\exists`
          - Type consistency: Detect ACSL `integer` vs. C `int` mismatches
          - Built-in predicate usage: Ensure `\valid(ptr)` has pointer argument
        </task>

        <task priority="medium" category="implementation">
          Implement error reporting and suggestions
          - Error message format: `file:line:column: error: description`
          - Suggestions: "Did you mean '\result' instead of 'result'?"
          - Warning level: Syntax errors vs. style warnings
          - Batch validation: Report all errors, don't stop at first
        </task>

        <task priority="high" category="testing">
          Create ACSLSyntaxValidatorTest.cpp unit tests
          - Valid annotation test cases (20+ examples from runtime library)
          - Invalid annotation test cases (20+ common errors: missing semicolons, typos, scope issues)
          - Test fixtures: valid_annotations.txt, invalid_annotations.txt
          - Edge cases: Nested annotations, multiline comments, Unicode characters
        </task>

        <task priority="low" category="documentation">
          Document validator limitations
          - Regex-based validator cannot catch all semantic errors (e.g., type mismatches)
          - Frama-C is authoritative, this validator is fast pre-check only
          - List of error types caught vs. deferred to Frama-C
          - Examples of false positives/negatives
        </task>
      </tasks>

      <deliverables>
        <deliverable>src/validation/ACSLSyntaxValidator.h (~100 lines, interface + validation rules enum)</deliverable>
        <deliverable>src/validation/ACSLSyntaxValidator.cpp (~400 lines, validation logic)</deliverable>
        <deliverable>tests/validation/ACSLSyntaxValidatorTest.cpp (~500 lines, 40+ test cases)</deliverable>
        <deliverable>tests/fixtures/valid_annotations.txt (20+ valid ACSL examples)</deliverable>
        <deliverable>tests/fixtures/invalid_annotations.txt (20+ invalid ACSL examples with expected errors)</deliverable>
        <deliverable>docs/ACSL_SYNTAX_VALIDATOR.md (validator guide, limitations, error catalog)</deliverable>
      </deliverables>

      <dependencies>
        <dependency>ACSL v1.22 specification (for syntax rules)</dependency>
        <dependency>C++ regex library or parser library (std::regex or custom)</dependency>
        <dependency>Runtime library annotations for test case extraction (exception_runtime.h, rtti_runtime.h)</dependency>
      </dependencies>

      <success_criteria>
        <criterion>Validator catches 90%+ of common syntax errors (validated against known invalid annotations)</criterion>
        <criterion>Zero false positives on runtime library annotations (exception_runtime.h, rtti_runtime.h pass)</criterion>
        <criterion>Error messages are clear and actionable (tested with developer review)</criterion>
        <criterion>Validation performance: &lt;100ms for typical file (~500 lines with 10 annotations)</criterion>
        <criterion>Unit tests achieve 95%+ code coverage on validator logic</criterion>
      </success_criteria>

      <execution_notes>
        **TDD Approach:**
        1. Write test with valid annotation (from runtime library), expect validator to pass
        2. Write test with invalid annotation (e.g., missing semicolon), expect specific error
        3. Implement validation rule to pass test
        4. Refactor regex patterns for clarity and performance

        **Regex vs. Parser Decision:**
        - MVP: Use regex for speed and simplicity (sufficient for common errors)
        - Future: Consider parser-based approach if regex becomes unmaintainable
        - Regex patterns inspired by Frama-C parser error messages

        **Error Message Quality:**
        - Study Frama-C error output for consistency (see research: verify_acsl.sh output)
        - Include context: Show annotation text with error position highlighted
        - Provide fix suggestions where possible

        **Test Fixture Generation:**
        - Extract valid annotations from runtime/exception_runtime.h (lines 57-109)
        - Extract valid annotations from runtime/rtti_runtime.h (lines 60-126)
        - Create invalid variants by introducing errors (remove semicolons, typo predicates, etc.)

        **Validation Scope:**
        - Syntax only: This phase does NOT validate semantics (type consistency, scope correctness)
        - Defer semantic validation to Phase 4 (optional) or rely on Frama-C (Phase 3)
      </execution_notes>
    </phase>

    <phase number="3" name="frama-c-integration-and-cli-wrapper">
      <objective>
        Create FramaCValidator wrapper for Frama-C CLI invocation and integrate with test suite for authoritative validation
      </objective>

      <background>
        Research finding: Frama-C CLI integration is proven in runtime library validation (verify_acsl.sh, verify_exception_runtime_wp.sh). Patterns exist for syntax validation (exit code 0/1), WP verification (XML output parsing), and value analysis. This phase formalizes the integration for transpiler-generated code validation.
      </background>

      <tasks>
        <task priority="critical" category="implementation">
          Design FramaCValidator class (src/validation/FramaCValidator.h/.cpp)
          - CLI invocation: Execute `frama-c` with configurable arguments
          - Process management: Timeout handling (configurable, default 60s), signal handling (SIGTERM/SIGKILL)
          - Output parsing: Parse stdout/stderr for errors, warnings, proof results
          - Exit code interpretation: 0 = success, non-zero = errors (capture error details)
        </task>

        <task priority="critical" category="cli-invocation">
          Implement Frama-C syntax validation mode
          - CLI command: `frama-c -cpp-extra-args="-I{include_dirs}" {file_path}`
          - Timeout: 10 seconds (syntax check should be fast)
          - Output capture: Stderr for error messages, stdout for warnings
          - Error extraction: Parse `[kernel] user error:` lines with file:line:column
          - Return: ValidationResult { success: bool, errors: vector&lt;string&gt;, warnings: vector&lt;string&gt; }
        </task>

        <task priority="high" category="cli-invocation">
          Implement Frama-C WP verification mode
          - CLI command: `frama-c -wp -wp-rte -cpp-extra-args="-I{dirs} -U__cplusplus -x c -std=gnu11" -wp-prover {prover} -wp-timeout {timeout} -wp-out {xml_path} {file}`
          - Provers: alt-ergo (default), z3 (fallback), cvc4 (optional)
          - Timeout: Configurable per proof obligation (default 60s)
          - XML output parsing: Extract proof statistics (proved, unknown, timeout, failed)
          - Return: WPResult { total_obligations: int, proved: int, unknown: int, timeout: int, failed: int }
        </task>

        <task priority="medium" category="cli-invocation">
          Implement Frama-C value analysis mode
          - CLI command: `frama-c -val -cpp-extra-args="-I{dirs}" -val-show-progress {files...}`
          - Output parsing: Extract alarms (buffer overflow, null deref, division by zero, etc.)
          - Alarm classification: Error vs. warning (configurable severity)
          - Return: ValueAnalysisResult { alarms: vector&lt;Alarm&gt;, summary: string }
        </task>

        <task priority="high" category="implementation">
          Implement graceful degradation (Frama-C optional)
          - Detection: Check if `frama-c` binary exists in PATH
          - Fallback: If not found, skip Frama-C validation with warning (log to stderr)
          - Configuration: Environment variable `SKIP_FRAMAC_VALIDATION=1` to explicitly disable
          - CMake integration: Optional dependency, tests skip if Frama-C unavailable
        </task>

        <task priority="medium" category="optimization">
          Implement validation result caching
          - Cache key: Hash of file content + Frama-C version + validation mode
          - Cache storage: `.framac-cache/` directory with JSON manifests
          - Cache invalidation: On file modification, Frama-C version change
          - Performance gain: Skip re-validation of unchanged files (estimated 90% speedup for incremental builds)
        </task>

        <task priority="medium" category="implementation">
          Add verbose logging and debugging
          - Log Frama-C CLI command before execution (for reproducibility)
          - Log Frama-C stdout/stderr in verbose mode (`--verbose-validation` flag)
          - Log validation timing (syntax, WP, value analysis duration)
          - Debug mode: Save Frama-C output to files for inspection (`--debug-validation` flag)
        </task>

        <task priority="high" category="testing">
          Create FramaCValidatorTest.cpp integration tests
          - Test syntax validation on valid/invalid files (use runtime library as test cases)
          - Test WP verification on simple annotated functions (expect known proof results)
          - Test graceful degradation (mock Frama-C not found, expect skip with warning)
          - Test timeout handling (mock slow Frama-C process, expect timeout error)
          - Test output parsing (fixture files with known Frama-C output)
        </task>

        <task priority="low" category="documentation">
          Write FRAMA_C_INTEGRATION.md developer guide
          - Frama-C installation instructions (Ubuntu, macOS, Docker)
          - Minimum version requirement: Frama-C 31.0+ (Gallium)
          - SMT solver setup: alt-ergo, z3 (installation guides)
          - CLI usage examples (syntax, WP, value analysis)
          - Troubleshooting: Common errors and fixes (missing includes, timeout tuning, etc.)
        </task>
      </tasks>

      <deliverables>
        <deliverable>src/validation/FramaCValidator.h (~150 lines, interface + result structs)</deliverable>
        <deliverable>src/validation/FramaCValidator.cpp (~600 lines, CLI invocation + parsing logic)</deliverable>
        <deliverable>tests/validation/FramaCValidatorTest.cpp (~400 lines, 20+ test cases)</deliverable>
        <deliverable>tests/fixtures/framac_output_syntax_error.txt (sample Frama-C error output for parsing tests)</deliverable>
        <deliverable>tests/fixtures/framac_output_wp_results.xml (sample WP XML for parsing tests)</deliverable>
        <deliverable>docs/FRAMA_C_INTEGRATION.md (~300 lines, installation + usage + troubleshooting)</deliverable>
      </deliverables>

      <dependencies>
        <dependency>Frama-C 31.0+ installed on development machines and CI/CD (optional for unit tests)</dependency>
        <dependency>Alt-Ergo or Z3 SMT solver installed (for WP verification)</dependency>
        <dependency>POSIX process API (fork/exec or std::system for CLI invocation)</dependency>
        <dependency>C++17 filesystem library (for cache management, file hashing)</dependency>
      </dependencies>

      <success_criteria>
        <criterion>FramaCValidator successfully validates runtime library files (exception_runtime.h, rtti_runtime.h)</criterion>
        <criterion>Syntax validation matches Frama-C CLI exit codes and error messages</criterion>
        <criterion>WP verification reproduces 65.7% proof coverage for exception runtime (as documented)</criterion>
        <criterion>Graceful degradation: Tests pass even if Frama-C not installed (skip with warning)</criterion>
        <criterion>Caching reduces validation time by 80%+ for unchanged files</criterion>
        <criterion>Documentation enables developer to install and use Frama-C within 30 minutes</criterion>
      </success_criteria>

      <execution_notes>
        **TDD Approach:**
        1. Write test invoking FramaCValidator on runtime/exception_runtime.h (expect success)
        2. Implement CLI invocation to pass test
        3. Write test invoking FramaCValidator on fixture with syntax error (expect specific error)
        4. Implement error parsing to pass test
        5. Iterate for WP verification, value analysis modes

        **Frama-C CLI Examples from Research:**
        - Syntax: `frama-c -cpp-extra-args="-Iruntime" runtime/exception_runtime.h` (verify_acsl.sh line 20)
        - WP: `frama-c -wp -wp-rte -cpp-extra-args="-Iruntime -U__cplusplus -x c -std=gnu11" -wp-prover alt-ergo -wp-timeout 60 -wp-out output.xml file.c` (verify_exception_runtime_wp.sh lines 49-59)
        - Value: `frama-c -val -cpp-extra-args="-Iruntime" -val-show-progress runtime/*.c runtime/*.h` (run_all_verifications.sh lines 112-137)

        **Output Parsing Strategy:**
        - Syntax errors: Regex match `\[kernel\] user error: (.+):(\d+):(\d+): (.+)`
        - WP results: Parse XML (Why3 format) or text summary (`Proved: 23/35`)
        - Value alarms: Regex match `\[value\] (.+):(\d+): alarm: (.+)`

        **Caching Implementation:**
        - Use SHA-256 hash of file content as cache key
        - Store cache in `.framac-cache/{hash}.json` with validation results
        - Cache entry includes: Frama-C version, validation mode, timestamp, results
        - Invalidate cache if file mtime changed or Frama-C version changed

        **Graceful Degradation Rationale:**
        - Developers may not have Frama-C installed initially
        - CI/CD may not have Frama-C in base image (optional installation)
        - Tests should not fail if Frama-C is unavailable (warning instead)
        - Environment variable `SKIP_FRAMAC_VALIDATION=1` for explicit opt-out
      </execution_notes>
    </phase>

    <phase number="4" name="integration-test-suite-and-end-to-end-validation">
      <objective>
        Integrate ACSL generation and validation into comprehensive end-to-end test suite covering transpiler output
      </objective>

      <background>
        Research finding: Existing ACSL validation tests only cover runtime library (verify_acsl.sh for 3 files). No tests exist for transpiler-generated code annotations. This phase creates comprehensive integration tests that: (1) transpile C++ code with `--generate-acsl`, (2) validate syntax with ACSLSyntaxValidator, (3) validate with Frama-C CLI, (4) verify end-to-end workflow.
      </background>

      <tasks>
        <task priority="critical" category="test-infrastructure">
          Create ACSLIntegrationTest.cpp test framework
          - Test harness: Transpile C++ code → generate C with ACSL → validate syntax → validate with Frama-C
          - Test fixtures: C++ source files covering language constructs (classes, loops, functions, templates)
          - Expected outputs: C code with ACSL annotations (golden files for regression testing)
          - Assertion utilities: Compare generated annotations against expected (line-by-line or AST diff)
        </task>

        <task priority="critical" category="test-cases">
          Add function contract generation tests (10+ test cases)
          - Simple function: `int add(int a, int b)` → requires, ensures, assigns
          - Pointer parameters: `void process(int *data, size_t len)` → `\valid(data + (0..len-1))`
          - Return value contracts: `int* allocate(size_t n)` → ensures `\result == \null || \valid(\result + (0..n-1))`
          - Non-returning functions: `void fatal_error(const char *msg)` → ensures `\false`
          - Function with side effects: `void modify_global()` → assigns global_state
        </task>

        <task priority="critical" category="test-cases">
          Add loop annotation generation tests (8+ test cases)
          - Simple for loop: `for (int i = 0; i < n; i++)` → loop invariant, loop variant `n - i`, loop assigns
          - While loop: `while (condition)` → loop invariant (inferred from condition), loop assigns
          - Nested loops: Inner/outer invariants, scoped assigns
          - Iterator loops: `for (auto& item : container)` → loop invariant referencing iterator validity
          - Infinite loops: `while (true)` → no loop variant (or variant constant 0)
        </task>

        <task priority="high" category="test-cases">
          Add class invariant generation tests (6+ test cases)
          - Simple class: `class Point { int x, y; }` → predicate `valid_Point`
          - Class with pointers: `class Buffer { char *data; size_t size; }` → `\valid(data + (0..size-1))`
          - Polymorphic class: `class Base { virtual void f(); }` → vtable validity predicate
          - Constructor contracts: `Point(int x, int y)` → ensures `valid_Point(this)`
          - Destructor contracts: `~Buffer()` → requires `valid_Buffer(this)`
          - RTTI-enabled class: Include type_info validity predicates
        </task>

        <task priority="high" category="test-cases">
          Add negative tests (intentionally invalid annotations, 5+ test cases)
          - Missing semicolon in contract → ACSLSyntaxValidator catches error
          - Undefined predicate reference → Frama-C catches error
          - Type mismatch in logic expression → Frama-C catches error
          - Out-of-scope variable in postcondition → Frama-C catches error
          - Invalid assigns clause (non-modifiable location) → Frama-C catches error
        </task>

        <task priority="high" category="integration">
          Integrate with CMake build system
          - Add CMake test target: `make test-acsl-integration`
          - Configure Frama-C dependency: Optional (skip tests if not found) or required (fail if missing)
          - Test parallelization: Run independent test cases concurrently (CTest parallel execution)
          - Test output: JUnit XML for CI/CD integration
        </task>

        <task priority="medium" category="regression">
          Create regression test suite (golden file comparison)
          - Golden files: Pre-generated C code with ACSL annotations (manually reviewed)
          - Regression detection: Compare transpiler output against golden files (diff-based)
          - Update mechanism: `make update-acsl-golden-files` to regenerate after intentional changes
          - Version control: Commit golden files to git for change tracking
        </task>

        <task priority="medium" category="ci-cd">
          Add GitHub Actions workflow for ACSL validation
          - Workflow file: `.github/workflows/acsl-validation.yml`
          - Trigger: On pull request, push to main/develop branches
          - Jobs: (1) Syntax validation (fast, required), (2) Frama-C validation (slow, optional/nightly)
          - Frama-C installation: Use apt-get (Ubuntu) or cached Docker image
          - Artifact upload: Validation reports (XML, HTML) for failed builds
        </task>

        <task priority="low" category="documentation">
          Document test suite organization and usage
          - Test categories: Function contracts, loop annotations, class invariants, negative tests
          - Running tests: `make test-acsl-integration`, `ctest -R acsl`
          - Adding new tests: Template for test case creation, golden file generation
          - Debugging failures: Verbose mode, intermediate file inspection
        </task>
      </tasks>

      <deliverables>
        <deliverable>tests/integration/ACSLIntegrationTest.cpp (~800 lines, 35+ test cases)</deliverable>
        <deliverable>tests/fixtures/cpp/ (C++ source files for test cases, 30+ files)</deliverable>
        <deliverable>tests/fixtures/golden/ (Expected C code with ACSL annotations, 30+ files)</deliverable>
        <deliverable>tests/CMakeLists.txt (CMake test configuration, ~100 lines added)</deliverable>
        <deliverable>.github/workflows/acsl-validation.yml (GitHub Actions workflow, ~80 lines)</deliverable>
        <deliverable>docs/ACSL_INTEGRATION_TESTING.md (test suite guide, ~200 lines)</deliverable>
      </deliverables>

      <dependencies>
        <dependency>Phase 1: ACSL generator implementation (must be complete to generate annotations)</dependency>
        <dependency>Phase 2: ACSLSyntaxValidator (for syntax validation step)</dependency>
        <dependency>Phase 3: FramaCValidator (for Frama-C validation step)</dependency>
        <dependency>CMake test infrastructure (exists in transpiler)</dependency>
        <dependency>GitHub Actions CI/CD (exists in transpiler)</dependency>
      </dependencies>

      <success_criteria>
        <criterion>All integration tests pass with generated ACSL annotations (35+ test cases)</criterion>
        <criterion>Syntax validation achieves 100% pass rate on generated annotations (zero syntax errors)</criterion>
        <criterion>Frama-C validation achieves ≥80% pass rate (syntax + basic semantic checks)</criterion>
        <criterion>Negative tests correctly detect and report errors (5+ error types validated)</criterion>
        <criterion>CMake integration: `make test-acsl-integration` runs all tests, exits 0 on success</criterion>
        <criterion>CI/CD workflow: GitHub Actions runs validation on every PR, reports failures</criterion>
        <criterion>Regression tests detect changes: Modify generator → diff detected → test fails</criterion>
      </success_criteria>

      <execution_notes>
        **TDD Approach:**
        1. Create C++ test fixture (e.g., `simple_function.cpp`)
        2. Write expected C code with ACSL annotations (golden file: `simple_function.c.golden`)
        3. Write test: Transpile C++ → compare output to golden file → validate with Frama-C
        4. Run test (expect failure initially)
        5. Implement ACSL generator for this construct
        6. Run test again (expect pass)
        7. Iterate for next language construct

        **Test Case Coverage:**
        - Function contracts: 10 test cases (simple, pointers, returns, side effects, non-returning)
        - Loop annotations: 8 test cases (for, while, nested, iterator, infinite)
        - Class invariants: 6 test cases (simple, pointers, polymorphic, constructors, destructors, RTTI)
        - Negative tests: 5 test cases (syntax errors, semantic errors, scope errors)
        - Edge cases: 6 test cases (templates, constexpr, inline, static, extern, etc.)
        - Total: 35+ test cases covering core language constructs

        **Golden File Management:**
        - Store in `tests/fixtures/golden/`
        - Naming convention: `{test_name}.c.golden`
        - Manual review: Each golden file must be reviewed for correctness before commit
        - Update mechanism: `make update-acsl-golden-files` regenerates all golden files
        - Version control: Commit golden files, review changes in pull requests

        **CMake Integration Pattern:**
        ```cmake
        # Add ACSL integration tests (optional Frama-C dependency)
        find_program(FRAMAC_EXECUTABLE frama-c)
        if(FRAMAC_EXECUTABLE)
          add_test(NAME acsl_integration_test_function_contracts
                   COMMAND acsl_integration_test --test=function_contracts)
          # ... more tests ...
        else()
          message(WARNING "Frama-C not found, skipping ACSL integration tests")
        endif()
        ```

        **CI/CD Workflow Strategy:**
        - Tier 1 (every PR): Syntax validation only (fast, 2-5 minutes)
        - Tier 2 (nightly): Frama-C WP verification (slow, 10-30 minutes)
        - Tier 3 (release): Full verification suite with value analysis (very slow, 30-60 minutes)
        - Fail fast: Stop on first validation error for quick feedback
        - Artifact upload: Save Frama-C output for failed builds (HTML reports, XML certificates)

        **Example Test Structure:**
        ```cpp
        TEST(ACSLIntegrationTest, SimpleFunctionContract) {
          // Transpile C++ to C with ACSL
          TranspilerOptions opts;
          opts.generate_acsl = true;
          opts.acsl_level = ACSLLevel::Basic;
          string output = transpile_file("tests/fixtures/cpp/simple_function.cpp", opts);

          // Syntax validation
          ACSLSyntaxValidator syntax_validator;
          ASSERT_TRUE(syntax_validator.validate(output)) << "Syntax validation failed";

          // Frama-C validation
          FramaCValidator framac;
          auto result = framac.validate_syntax(output);
          ASSERT_TRUE(result.success) << "Frama-C validation failed: " << result.errors;

          // Golden file comparison (optional regression check)
          string golden = read_file("tests/fixtures/golden/simple_function.c.golden");
          EXPECT_EQ(normalize_whitespace(output), normalize_whitespace(golden));
        }
        ```
      </execution_notes>
    </phase>

    <phase number="5" name="semantic-validation-advanced">
      <objective>
        Add semantic validation beyond syntax: type consistency checking, variable scope verification, contract completeness analysis
      </objective>

      <background>
        Research finding: Current validation relies on Frama-C for semantic checks (type consistency, scope verification). However, Frama-C reports semantic errors late (after syntax validation, during WP). Early semantic validation can catch errors faster and provide better error messages. This phase is OPTIONAL for MVP - Frama-C provides sufficient semantic validation, but custom checks can improve developer experience.
      </background>

      <tasks>
        <task priority="medium" category="architecture">
          Design ACSLSemanticValidator class (src/validation/ACSLSemanticValidator.h/.cpp)
          - Integration with transpiler AST (access to type information, symbol tables)
          - Validation rules: Type consistency, scope verification, contract completeness
          - Error reporting: Semantic errors with suggestions (e.g., "variable 'x' not in scope, did you mean 'this->x'?")
          - Extensibility: Plugin architecture for custom semantic checks
        </task>

        <task priority="medium" category="implementation">
          Implement type consistency validation
          - Check ACSL logic types vs. C types (integer vs. int, real vs. float/double)
          - Verify predicate argument types match definition
          - Validate `\result` type matches function return type
          - Check pointer arithmetic in `\valid` expressions (e.g., `\valid(ptr + (0..n-1))` requires integer `n`)
        </task>

        <task priority="medium" category="implementation">
          Implement variable scope verification
          - Verify all variables in `requires` clause are function parameters or global
          - Verify all variables in `ensures` clause are parameters, return value (`\result`), or global
          - Verify loop invariant references only loop-scoped variables and outer scope
          - Detect out-of-scope references (e.g., local variable in postcondition)
        </task>

        <task priority="low" category="implementation">
          Implement contract completeness checks
          - Verify all pointer parameters have `\valid` or `\null` precondition
          - Verify all modified global variables are listed in `assigns` clause
          - Verify functions returning pointers have `\result == \null || \valid(\result)` postcondition
          - Warn if function has no contract (missing preconditions/postconditions)
        </task>

        <task priority="low" category="implementation">
          Implement loop annotation completeness checks
          - Verify loop invariant references loop counter/iterator
          - Verify loop variant decreases on each iteration (heuristic check)
          - Verify all loop-modified variables are in `loop assigns` clause
          - Warn if loop has no invariant (may make verification difficult)
        </task>

        <task priority="low" category="implementation">
          Implement predicate consistency checks
          - Verify all predicates are defined before use (topological sort)
          - Detect recursive predicates (may cause Frama-C issues)
          - Check predicate arity matches usage (correct number of arguments)
          - Validate predicate return type is boolean
        </task>

        <task priority="medium" category="testing">
          Create ACSLSemanticValidatorTest.cpp unit tests
          - Type consistency tests (10+ cases: valid types, invalid type mismatches)
          - Scope verification tests (8+ cases: valid scope, out-of-scope references)
          - Completeness tests (6+ cases: complete contracts, incomplete contracts with warnings)
          - Predicate consistency tests (4+ cases: valid predicates, recursive predicates, undefined predicates)
        </task>

        <task priority="low" category="integration">
          Integrate semantic validator into validation pipeline
          - Validation order: Syntax → Semantic → Frama-C
          - Early exit: Stop on semantic errors before invoking Frama-C (faster feedback)
          - Warning vs. error: Configurable strictness (fail on warnings or allow)
          - CLI flag: `--strict-acsl-validation` to enforce all semantic checks
        </task>
      </tasks>

      <deliverables>
        <deliverable>src/validation/ACSLSemanticValidator.h (~120 lines, interface + error types)</deliverable>
        <deliverable>src/validation/ACSLSemanticValidator.cpp (~500 lines, validation logic)</deliverable>
        <deliverable>tests/validation/ACSLSemanticValidatorTest.cpp (~350 lines, 28+ test cases)</deliverable>
        <deliverable>docs/ACSL_SEMANTIC_VALIDATION.md (semantic validation guide, ~150 lines)</deliverable>
      </deliverables>

      <dependencies>
        <dependency>Transpiler AST (for type information, symbol tables)</dependency>
        <dependency>Phase 1: ACSL generator (to have annotations to validate)</dependency>
        <dependency>Phase 2: ACSLSyntaxValidator (semantic validation builds on syntax validation)</dependency>
        <dependency>Clang type system integration (for C++ type → ACSL type mapping)</dependency>
      </dependencies>

      <success_criteria>
        <criterion>Semantic validator catches type mismatches before Frama-C (10+ test cases pass)</criterion>
        <criterion>Scope verification detects out-of-scope references (8+ test cases pass)</criterion>
        <criterion>Completeness checks warn on incomplete contracts (6+ test cases pass)</criterion>
        <criterion>Integration: Semantic validation runs before Frama-C, reports errors early</criterion>
        <criterion>False positive rate: &lt;5% (minimal spurious errors on valid annotations)</criterion>
      </success_criteria>

      <execution_notes>
        **MVP Scope Decision:**
        - This phase is OPTIONAL for MVP
        - Frama-C already provides semantic validation (type checking, scope verification)
        - Semantic validator adds value by providing faster feedback and better error messages
        - Recommend: Defer to future work unless Frama-C error messages are insufficient

        **TDD Approach:**
        1. Write test with type mismatch (e.g., `requires x > 0` where `x` is pointer)
        2. Expect semantic validator to catch error
        3. Implement type checking logic to pass test
        4. Write test with valid type (expect validation to pass)
        5. Iterate for scope verification, completeness checks

        **AST Integration:**
        - Leverage Clang AST for type information (QualType, TypeInfo)
        - Access symbol table for scope verification (Sema::LookupName)
        - Analyze function parameters, local variables, globals for scope checks

        **Type Mapping (C++ → ACSL):**
        - `int`, `long`, `short` → `integer` (infinite precision) or C type (machine integers)
        - `float`, `double` → `real` (logic) or C type (floating point)
        - Pointers: `T*` → `\valid(ptr)` predicate (not a type)
        - Structs: C type, no ACSL equivalent (use predicates for invariants)

        **Completeness Heuristics:**
        - Pointer parameters: If no `\valid` or `\null` in precondition, warn "Missing pointer validity check"
        - Modified globals: Compare `assigns` clause with global variables accessed (static analysis)
        - Return value: If returning pointer, suggest `\result == \null || \valid(\result)`
        - Loop invariant: If loop modifies array, suggest invariant on array bounds

        **Error Message Quality:**
        - Provide context: Show function signature, annotation text, error location
        - Suggest fixes: "Variable 'data' not in scope. Did you mean 'this->data'?"
        - Reference ACSL spec: "ACSL requires 'integer' type in logic expressions, not 'int'. See ACSL v1.22 §2.2.1"

        **Performance Considerations:**
        - Semantic validation may be slow (AST traversal, symbol table lookups)
        - Cache AST analysis results where possible
        - Parallelize validation across multiple files
        - Provide progress reporting for large codebases
      </execution_notes>
    </phase>

    <phase number="6" name="documentation-examples-and-maintenance">
      <objective>
        Create comprehensive documentation, examples, and maintenance guides for ACSL generation and validation infrastructure
      </objective>

      <background>
        Research finding: Epic #15 includes excellent documentation (ACSL_ANNOTATIONS.md, FORMAL_VERIFICATION_GUIDE.md, SAFETY_CRITICAL_GUIDE.md) but focuses on runtime library only. Documentation must be extended to cover transpiler ACSL generation, validation workflows, troubleshooting, and best practices.
      </background>

      <tasks>
        <task priority="high" category="user-documentation">
          Write ACSL_GENERATION_GUIDE.md (user-facing guide)
          - Introduction: What is ACSL, why generate annotations, use cases
          - Getting started: Enable `--generate-acsl` flag, basic example
          - Annotation levels: `--acsl-level=basic` vs. `--acsl-level=full`
          - Customization: How to add custom predicates, override generated annotations
          - Frama-C integration: How to validate generated annotations
          - Troubleshooting: Common issues (Frama-C errors, performance, false positives)
        </task>

        <task priority="high" category="developer-documentation">
          Write ACSL_VALIDATOR_IMPLEMENTATION.md (developer-facing guide)
          - Architecture: ACSLGenerator, ACSLSyntaxValidator, FramaCValidator classes
          - Adding new annotation types: Extend ACSLFunctionAnnotator, ACSLLoopAnnotator, etc.
          - Adding new validation rules: Extend ACSLSyntaxValidator, ACSLSemanticValidator
          - Testing: How to add test cases, update golden files
          - Maintenance: Update validation rules when ACSL spec evolves
        </task>

        <task priority="high" category="documentation">
          Update existing documentation to reflect ACSL generation
          - SAFETY_CRITICAL_GUIDE.md: Correct `--generate-acsl` flag documentation (lines 369, 621, 693)
          - FORMAL_VERIFICATION_GUIDE.md: Add section on transpiler-generated code validation
          - ACSL_ANNOTATIONS.md: Add section on automatic annotation generation
          - README.md: Add note on ACSL generation capability
        </task>

        <task priority="medium" category="examples">
          Create annotated C++ examples (examples/acsl/)
          - Simple function: `int factorial(int n)` with preconditions/postconditions
          - Pointer safety: `void process_buffer(char *data, size_t len)` with `\valid` annotations
          - Class invariants: `class Stack` with overflow/underflow contracts
          - Loop invariants: `void bubble_sort(int *arr, size_t n)` with sorted subarray invariant
          - RTTI example: `dynamic_cast` with type hierarchy predicates
          - Exception safety: `void may_throw()` with exception specifications
        </task>

        <task priority="medium" category="documentation">
          Document common ACSL validation errors and fixes
          - Error catalog: Syntax errors, semantic errors, scope errors, type errors
          - For each error: Example code, error message, fix suggestion
          - Common Frama-C errors: Missing includes, timeout tuning, proof failures
          - Performance issues: Large files, complex annotations, slow provers
        </task>

        <task priority="medium" category="documentation">
          Create Frama-C troubleshooting guide
          - Installation issues: Dependencies, version compatibility
          - CLI errors: Missing arguments, incorrect flags, preprocessor issues
          - Proof failures: Timeout tuning, prover selection, annotation strengthening
          - Value analysis: Alarm interpretation, false positives, precision tuning
          - Performance: Parallelization, caching, incremental verification
        </task>

        <task priority="low" category="examples">
          Create side-by-side comparison: with/without ACSL
          - Same C++ code transpiled: (1) without `--generate-acsl`, (2) with `--generate-acsl`
          - Highlight differences: Annotations added, verification potential
          - Show Frama-C validation: Proof results, alarms detected
          - Demonstrate value: Safety guarantees, certification compliance
        </task>

        <task priority="low" category="documentation">
          Create ACSL best practices guide
          - When to use ACSL: Safety-critical code, certification requirements, contract-based design
          - Annotation granularity: How much to annotate (balance completeness vs. maintainability)
          - Proof strategies: How to write provable contracts (avoid over-specification)
          - Performance: Keep annotations simple, avoid quantifiers when possible
          - Maintenance: Keep annotations synchronized with code changes
        </task>
      </tasks>

      <deliverables>
        <deliverable>docs/ACSL_GENERATION_GUIDE.md (user guide, ~500 lines)</deliverable>
        <deliverable>docs/ACSL_VALIDATOR_IMPLEMENTATION.md (developer guide, ~400 lines)</deliverable>
        <deliverable>docs/ACSL_TROUBLESHOOTING.md (error catalog + fixes, ~350 lines)</deliverable>
        <deliverable>docs/ACSL_BEST_PRACTICES.md (best practices guide, ~250 lines)</deliverable>
        <deliverable>examples/acsl/simple_function.cpp (annotated example, 6+ examples)</deliverable>
        <deliverable>examples/acsl/README.md (examples index with explanations)</deliverable>
        <deliverable>Updated: docs/SAFETY_CRITICAL_GUIDE.md (fix `--generate-acsl` references)</deliverable>
        <deliverable>Updated: docs/FORMAL_VERIFICATION_GUIDE.md (add transpiler validation section)</deliverable>
        <deliverable>Updated: docs/ACSL_ANNOTATIONS.md (add automatic generation section)</deliverable>
      </deliverables>

      <dependencies>
        <dependency>Phase 1-5: ACSL generation and validation implementation (to document features)</dependency>
        <dependency>Test suite results (to document common errors, best practices)</dependency>
        <dependency>Frama-C integration experience (to write troubleshooting guide)</dependency>
      </dependencies>

      <success_criteria>
        <criterion>User can enable ACSL generation and validate output within 15 minutes (using guide)</criterion>
        <criterion>Developer can add new annotation type within 1 hour (using implementation guide)</criterion>
        <criterion>Common errors have documented solutions (10+ error/fix pairs in troubleshooting guide)</criterion>
        <criterion>Examples compile, transpile, and validate successfully with Frama-C</criterion>
        <criterion>Documentation is accurate (no stale references to unimplemented features)</criterion>
      </success_criteria>

      <execution_notes>
        **Documentation Structure:**
        - User-facing guides: Focus on "what" and "why" (ACSL_GENERATION_GUIDE.md, BEST_PRACTICES.md)
        - Developer-facing guides: Focus on "how" (ACSL_VALIDATOR_IMPLEMENTATION.md)
        - Troubleshooting: Focus on "when things go wrong" (ACSL_TROUBLESHOOTING.md)
        - Examples: Focus on "show me" (examples/acsl/)

        **Example Selection Criteria:**
        - Cover core language constructs (functions, loops, classes)
        - Demonstrate common safety properties (pointer validity, array bounds, type safety)
        - Show realistic use cases (buffer processing, data structures, algorithms)
        - Include both simple (factorial) and complex (RTTI, exceptions) examples

        **Error Catalog Format:**
        ```markdown
        ### Error: Missing semicolon in requires clause

        **Symptom:** ACSLSyntaxValidator error: "Expected ';' after requires clause"

        **Example:**
        \`\`\`c
        /*@ requires x > 0  // Missing semicolon
            ensures \result > 0; */
        int increment(int x);
        \`\`\`

        **Fix:** Add semicolon after precondition
        \`\`\`c
        /*@ requires x > 0;  // Corrected
            ensures \result > 0; */
        int increment(int x);
        \`\`\`

        **Prevention:** ACSLSyntaxValidator catches this automatically.
        ```

        **Troubleshooting Guide Sections:**
        1. Installation issues (Frama-C, SMT solvers)
        2. CLI invocation errors (preprocessor, include paths)
        3. Syntax validation errors (common typos, missing elements)
        4. Semantic validation errors (type mismatches, scope issues)
        5. WP proof failures (timeouts, unprovable obligations)
        6. Value analysis issues (alarms, precision)
        7. Performance problems (slow validation, large files)

        **Best Practices Guide Topics:**
        - **When to annotate:** Safety-critical code, public APIs, complex algorithms
        - **Annotation granularity:** Start with preconditions/postconditions, add invariants as needed
        - **Provability:** Avoid over-specification (too strong contracts are unprovable)
        - **Maintainability:** Keep annotations close to code, update synchronously
        - **Performance:** Simple annotations verify faster, avoid quantifiers
        - **Certification:** Follow DO-178C/ISO 26262 guidelines for annotation completeness
      </execution_notes>
    </phase>
  </phases>

  <execution_strategy>
    <phasing>
      <sequential_dependencies>
        Phase 1 (ACSL Generator) must complete before Phase 4 (Integration Tests) - need generator to produce annotations
        Phase 2 (Syntax Validator) must complete before Phase 4 (Integration Tests) - need validator for test assertions
        Phase 3 (Frama-C Wrapper) must complete before Phase 4 (Integration Tests) - need Frama-C integration for validation
        Phase 5 (Semantic Validator) can run in parallel with Phase 4 (optional, advanced)
        Phase 6 (Documentation) should run last (requires implementation complete to document features)
      </sequential_dependencies>

      <parallel_opportunities>
        - Phase 2 (Syntax Validator) and Phase 3 (Frama-C Wrapper) can develop in parallel (independent)
        - Phase 1 subtasks: ACSLFunctionAnnotator, ACSLLoopAnnotator, ACSLClassAnnotator can develop in parallel
        - Phase 4 test categories: Function contracts, loop annotations, class invariants can test in parallel
      </parallel_opportunities>

      <critical_path>
        Phase 1 (ACSL Generator) → Phase 4 (Integration Tests) → Phase 6 (Documentation)
        - This path blocks all downstream work
        - Prioritize critical path tasks to unblock dependent phases
      </critical_path>

      <optional_phases>
        Phase 5 (Semantic Validator) is optional for MVP
        - Frama-C provides semantic validation already
        - Custom semantic validator adds faster feedback and better error messages
        - Defer to future work if schedule is tight
      </optional_phases>
    </phasing>

    <testing_strategy>
      <tdd_methodology>
        All implementation follows TDD:
        1. Write failing test for feature
        2. Implement minimal code to pass test
        3. Refactor while keeping tests green
        4. Iterate with more test cases
      </tdd_methodology>

      <test_coverage_targets>
        - Unit tests: 95%+ code coverage on generator and validator logic
        - Integration tests: 100% coverage of supported C++ constructs (functions, loops, classes)
        - Negative tests: 100% coverage of common error types (syntax, semantic, scope)
        - Regression tests: Golden file comparison for all test cases
      </test_coverage_targets>

      <test_categorization>
        - **Unit tests:** Fast, no external dependencies (e.g., ACSLGeneratorTest, ACSLSyntaxValidatorTest)
        - **Integration tests:** Medium speed, may use Frama-C (e.g., ACSLIntegrationTest)
        - **Regression tests:** Golden file comparison (e.g., generated code matches expected)
        - **CI/CD tests:** Syntax validation (fast, every PR), WP verification (slow, nightly)
      </test_categorization>
    </testing_strategy>

    <performance_considerations>
      <annotation_generation>
        - ACSL generation adds minimal overhead to transpilation (AST traversal already exists)
        - Estimated impact: &lt;5% transpilation time increase
        - Optimization: Generate annotations lazily (only when requested via CLI flag)
      </annotation_generation>

      <syntax_validation>
        - Regex-based validator: Fast (&lt;100ms per file with 10 annotations)
        - Optimization: Cache validation results, skip unchanged files
        - Parallelization: Validate files concurrently
      </syntax_validation>

      <framac_validation>
        - Syntax check: Fast (seconds per file)
        - WP verification: Slow (60s timeout per proof obligation)
        - Value analysis: Medium (depends on code size)
        - Optimization: Cache Frama-C results, run WP verification on nightly builds only
        - Parallelization: Run Frama-C on multiple files concurrently
      </framac_validation>

      <ci_cd_impact>
        - Tier 1 (every PR): Syntax validation only (~5 minutes total)
        - Tier 2 (nightly): WP verification (~30 minutes total)
        - Tier 3 (release): Full verification suite (~60 minutes total)
        - Strategy: Run expensive validations asynchronously, don't block PRs
      </ci_cd_impact>
    </performance_considerations>

    <risk_mitigation>
      <risk name="ACSL generation complexity">
        <description>Generating correct ACSL for all C++ constructs may be very complex (templates, SFINAE, etc.)</description>
        <mitigation>Start with core constructs (functions, loops, classes), defer advanced features (templates) to future work</mitigation>
        <fallback>Provide manual annotation interface, allow users to override generated annotations</fallback>
      </risk>

      <risk name="Frama-C proof failures">
        <description>Generated annotations may be syntactically correct but unprovable by Frama-C WP</description>
        <mitigation>Focus on syntax validation for MVP, treat WP proof failures as warnings not errors</mitigation>
        <fallback>Document unprovable patterns, provide annotation tuning guide for users</fallback>
      </risk>

      <risk name="Performance degradation">
        <description>Frama-C validation may be too slow for CI/CD, blocking development workflow</description>
        <mitigation>Implement caching, run expensive validations on nightly builds only, not every PR</mitigation>
        <fallback>Make Frama-C validation optional (`SKIP_FRAMAC_VALIDATION=1` environment variable)</fallback>
      </risk>

      <risk name="Frama-C installation complexity">
        <description>Developers may struggle to install Frama-C, SMT solvers (especially on Windows)</description>
        <mitigation>Provide Docker image with Frama-C pre-installed, comprehensive installation guide</mitigation>
        <fallback>Graceful degradation: Skip Frama-C tests if tool not available (warning, not error)</fallback>
      </risk>

      <risk name="Documentation maintenance burden">
        <description>ACSL generation adds complexity, documentation may become outdated as features evolve</description>
        <mitigation>Generate documentation from code where possible (CLI help text, error messages), automate example testing</mitigation>
        <fallback>Establish documentation review process, update docs in same PR as code changes</fallback>
      </risk>
    </risk_mitigation>
  </execution_strategy>

  <metadata>
    <confidence level="high">
      Plan is based on proven Frama-C integration patterns from Epic #15 (runtime library validation). ACSL generation design follows industry-standard AST visitor pattern. Testing strategy follows TDD best practices. Dependencies are clearly identified. Risks have mitigation strategies.
    </confidence>

    <effort_estimation>
      <phase_estimates>
        - Phase 1 (ACSL Generator): 40-60 hours (critical, complex AST integration)
        - Phase 2 (Syntax Validator): 20-30 hours (medium complexity, regex-based)
        - Phase 3 (Frama-C Wrapper): 25-35 hours (medium complexity, CLI integration proven)
        - Phase 4 (Integration Tests): 35-50 hours (high test coverage, golden files)
        - Phase 5 (Semantic Validator): 30-40 hours (optional, complex AST analysis)
        - Phase 6 (Documentation): 20-30 hours (comprehensive guides, examples)
        - **Total (MVP, excluding Phase 5): 140-205 hours (~4-5 weeks for solo developer)**
        - **Total (Full, including Phase 5): 170-245 hours (~5-6 weeks for solo developer)**
      </phase_estimates>

      <team_parallelization>
        With 2 developers:
        - Developer 1: Phase 1 (ACSL Generator), Phase 4 (Integration Tests)
        - Developer 2: Phase 2 (Syntax Validator) + Phase 3 (Frama-C Wrapper) in parallel
        - Timeline: ~3-4 weeks (40% time reduction)

        With 3 developers:
        - Developer 1: Phase 1 (ACSL Generator)
        - Developer 2: Phase 2 (Syntax Validator) + Phase 3 (Frama-C Wrapper)
        - Developer 3: Phase 4 (Integration Tests) + Phase 6 (Documentation)
        - Timeline: ~2-3 weeks (50% time reduction)
      </team_parallelization>
    </effort_estimation>

    <dependencies>
      <external_dependencies>
        - Frama-C 31.0+ (Gallium) - Already installed (research confirms)
        - Alt-Ergo 2.6.2+ or Z3 4.8+ SMT solver - Required for WP verification
        - ACSL v1.22+ specification - Reference documentation
        - C++17 compiler (Clang/GCC) - Already exists in transpiler
        - CMake 3.15+ - Already exists in transpiler
      </external_dependencies>

      <internal_dependencies>
        - Transpiler AST infrastructure (Clang AST) - Exists
        - CodeGenerator class (src/codegen/CodeGenerator.*) - Exists
        - Test infrastructure (CMake, test harness) - Exists
        - CI/CD pipeline (GitHub Actions) - Exists
        - Runtime library ACSL annotations (for test case examples) - Exists (Epic #15)
      </internal_dependencies>
    </dependencies>

    <open_questions>
      <question priority="high">
        **Q1: What is the target ACSL coverage for transpiler-generated code?**
        - Options: (1) Basic (function contracts only), (2) Full (function + loop + class invariants)
        - Trade-off: Completeness vs. complexity vs. maintainability
        - Recommendation: Start with Basic (MVP), add Full incrementally
        - Decision needed: Before Phase 1 implementation begins
      </question>

      <question priority="high">
        **Q2: Should ACSL generation be enabled by default or opt-in?**
        - Options: (1) Default on (`--no-acsl` to disable), (2) Default off (`--generate-acsl` to enable)
        - Trade-off: Convenience vs. safety (unexpected annotation generation)
        - Recommendation: Default off for MVP (explicit opt-in), reconsider after user feedback
        - Decision needed: Before Phase 1 CLI implementation
      </question>

      <question priority="medium">
        **Q3: How to handle C++ constructs with no direct ACSL equivalent (templates, constexpr)?**
        - Options: (1) Skip annotation (warn user), (2) Generate partial annotation, (3) Generate placeholder comment
        - Trade-off: Completeness vs. correctness (partial annotations may be misleading)
        - Recommendation: Skip with warning for MVP, document limitations
        - Decision needed: During Phase 1 implementation (case-by-case)
      </question>

      <question priority="medium">
        **Q4: Should Frama-C validation be mandatory or optional in CI/CD?**
        - Options: (1) Mandatory (PR fails if Frama-C validation fails), (2) Optional (warning only)
        - Trade-off: Strictness vs. flexibility (early development may have many failures)
        - Recommendation: Optional for MVP (warning), mandatory after stabilization
        - Decision needed: Before Phase 4 CI/CD workflow implementation
      </question>

      <question priority="low">
        **Q5: Should Phase 5 (Semantic Validator) be in MVP scope?**
        - Options: (1) Include in MVP, (2) Defer to future work
        - Trade-off: Completeness vs. schedule (Phase 5 is 30-40 hours)
        - Recommendation: Defer to future work (Frama-C provides sufficient semantic validation)
        - Decision needed: Before scheduling Phase 5
      </question>

      <question priority="low">
        **Q6: What is the minimum Frama-C version to support?**
        - Options: (1) 31.0+ only (Gallium), (2) 30.0+ (backward compatibility)
        - Trade-off: Latest features vs. broader compatibility
        - Recommendation: 31.0+ only for MVP (current installed version), test backward compatibility later
        - Decision needed: Before Phase 3 Frama-C wrapper implementation
      </question>
    </open_questions>

    <assumptions>
      <assumption>
        **Assumption 1: Transpiler AST provides sufficient information for ACSL generation**
        - Basis: Clang AST includes type information, symbol tables, function signatures
        - Risk: Low (AST is comprehensive for C++ analysis)
        - Validation: Verify during Phase 1 implementation
      </assumption>

      <assumption>
        **Assumption 2: Frama-C CLI is stable and output format is consistent**
        - Basis: Epic #15 verification scripts work reliably
        - Risk: Low (Frama-C is mature, industry-standard tool)
        - Validation: Monitor Frama-C updates, test compatibility
      </assumption>

      <assumption>
        **Assumption 3: ACSL v1.22 is sufficient for transpiler-generated code**
        - Basis: Runtime library annotations use ACSL v1.22 successfully
        - Risk: Low (ACSL v1.22 is comprehensive specification)
        - Validation: Identify any unsupported constructs during Phase 1
      </assumption>

      <assumption>
        **Assumption 4: Syntax validation is sufficient for MVP (semantic validation optional)**
        - Basis: Frama-C provides semantic validation (type checking, scope verification)
        - Risk: Medium (custom semantic validator improves developer experience)
        - Validation: User feedback during MVP testing
      </assumption>

      <assumption>
        **Assumption 5: CI/CD can accommodate Frama-C installation**
        - Basis: Frama-C is available via apt-get (Ubuntu), Docker images exist
        - Risk: Low (GitHub Actions supports custom dependencies)
        - Validation: Test CI/CD workflow during Phase 4
      </assumption>
    </assumptions>

    <success_metrics>
      <metric name="ACSL Generation Coverage">
        Target: 80%+ of transpiled C++ constructs have ACSL annotations (functions, loops, classes)
        Measurement: Count annotated constructs / total constructs in test suite
      </metric>

      <metric name="Syntax Validation Accuracy">
        Target: 95%+ syntax validation accuracy (true positives + true negatives)
        Measurement: Confusion matrix on test suite (valid/invalid annotations)
      </metric>

      <metric name="Frama-C Integration Success Rate">
        Target: 100% syntax validation pass rate, 80%+ WP proof success rate
        Measurement: Frama-C CLI exit codes, WP proof statistics
      </metric>

      <metric name="Test Coverage">
        Target: 95%+ code coverage on generator and validator logic
        Measurement: Code coverage tool (gcov, lcov)
      </metric>

      <metric name="Performance Impact">
        Target: &lt;10% increase in transpilation time with ACSL generation enabled
        Measurement: Benchmark transpilation time with/without `--generate-acsl`
      </metric>

      <metric name="Documentation Quality">
        Target: User can enable ACSL generation within 15 minutes using guide
        Measurement: Usability testing with new developer
      </metric>

      <metric name="CI/CD Regression Prevention">
        Target: 100% of ACSL-related regressions caught by CI/CD before merge
        Measurement: Monitor CI/CD validation failures, false negative rate
      </metric>
    </success_metrics>
  </metadata>
</plan>
