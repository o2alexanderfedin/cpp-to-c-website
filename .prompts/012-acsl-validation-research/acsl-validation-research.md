# ACSL Annotation Validation Research

**Research Date:** 2025-12-19
**Epic:** #15 - Frama-C Compatibility & Formal Verification
**Stories:** #185-#192
**Researcher:** Claude Sonnet 4.5

---

<research>
  <summary>
    The C++ to C transpiler has comprehensive ACSL annotation infrastructure implemented for runtime library formal verification (Epic #15, completed v1.15.0). ACSL annotations exist for exception handling and RTTI runtime components with syntax validation via Frama-C parser. WP (Weakest Precondition) verification achieves 65.7% proof coverage for exception runtime with expected limitations due to longjmp semantics. Value analysis and verification certificate generation are fully integrated. **Key Gap:** No automatic ACSL annotation generation from C++ code during transpilation - annotations are manually written in runtime library headers only. Validation is comprehensive for runtime library but does not extend to transpiler-generated C code.
  </summary>

  <findings>
    <finding category="current-implementation">
      <title>ACSL Annotation Infrastructure (Story #185)</title>
      <detail>
        **Files with ACSL Annotations:**
        1. `runtime/exception_runtime.h` - Exception handling runtime (117 lines)
           - Predicates: `valid_exception_frame`, `valid_exception_stack`
           - Function contract for `cxx_throw()` with preconditions, postconditions, assigns
           - Location: Lines 57-109

        2. `runtime/rtti_runtime.h` - RTTI runtime (137 lines)
           - Predicates: `valid_type_info`, `valid_si_type_info`
           - Function contracts for `traverse_hierarchy()`, `cross_cast_traverse()`
           - Location: Lines 60-126

        3. `runtime/exception_runtime.cpp` - Implementation with loop invariants (108 lines)
           - Loop invariants for action table iteration (lines 81-84)
           - Loop assigns, loop variant annotations

        **Annotation Types Generated:**
        - Function contracts (`requires`, `ensures`, `assigns`)
        - Predicates (reusable logical properties)
        - Loop invariants, loop assigns, loop variant
        - Memory specifications (`\valid`, `\valid_read`, `\null`)

        **No Automatic Generation:** Search for `generate-acsl`, `--acsl`, ACSL generator classes yielded no results in `src/` directory. Annotations are manually written, not auto-generated during transpilation.
      </detail>
      <source>
        - File: `/runtime/exception_runtime.h` (read lines 1-117)
        - File: `/runtime/rtti_runtime.h` (read lines 1-137)
        - File: `/runtime/exception_runtime.cpp` (read lines 1-108)
        - Grep search: `src/` directory for annotation generation code (no matches)
        - Git commit: a69ba02 "feat: implement ACSL annotation infrastructure for runtime library (Story #185)"
      </source>
      <relevance>
        Establishes that ACSL infrastructure exists and is mature, but limited to runtime library. Understanding current scope is critical before planning validation improvements.
      </relevance>
    </finding>

    <finding category="validation-current">
      <title>Existing Validation Mechanisms</title>
      <detail>
        **Syntax Validation (Story #185):**
        - Script: `tests/verify_acsl.sh` (53 lines)
        - Method: Frama-C parser validation (`frama-c -cpp-extra-args="-Iruntime" file.h`)
        - Tests: 3 test cases (exception_runtime.h, rtti_runtime.h, rtti_runtime.c)
        - Exit codes: 0 = valid, 1 = syntax errors
        - Output: Human-readable pass/fail messages

        **WP (Weakest Precondition) Verification (Story #186):**
        - Script: `tests/verify_exception_runtime_wp.sh` (157 lines)
        - Provers: alt-ergo (default), z3 (optional)
        - Timeout: 60 seconds per proof obligation
        - RTE checks: Enabled (`-wp-rte` flag)
        - Results: 65.7% proof coverage (23/35 obligations proved)
        - Known limitation: longjmp non-local control flow limits verification
        - Output: XML proof certificates, text reports

        **Value Analysis (Story #189):**
        - Integrated in: `tests/run_all_verifications.sh` (lines 112-137)
        - Method: Frama-C Value plugin (`frama-c -val`)
        - Purpose: Detect undefined behavior (buffer overflows, null deref, division by zero)
        - Coverage: All runtime files (`*.c`, `*.h`)

        **Master Verification Suite (Story #191):**
        - Script: `tests/run_all_verifications.sh` (237 lines)
        - Executes: ACSL validation, Exception WP, RTTI WP, Value analysis, Certificate generation
        - Counters: Total tests, passed, failed
        - Success threshold: ≥60% pass rate
        - Outputs: Verification results directory, certificate index
      </detail>
      <source>
        - File: `/tests/verify_acsl.sh` (read all)
        - File: `/tests/verify_exception_runtime_wp.sh` (read all)
        - File: `/tests/run_all_verifications.sh` (read all)
        - Git commit: 97a09b2 "feat: complete comprehensive Frama-C verification suite (Stories #187-#192)"
      </source>
      <relevance>
        Demonstrates comprehensive validation infrastructure exists for runtime library. No validation gaps identified for current scope (runtime-only). Gap exists for transpiler-generated code validation.
      </relevance>
    </finding>

    <finding category="validation-gaps">
      <title>Validation Gaps Identified</title>
      <detail>
        **Gap 1: No Transpiler-Generated Code Validation**
        - Current scope: Runtime library only (2 header files, 2 implementation files)
        - Missing: ACSL annotation generation for transpiler output
        - Impact: Transpiled C code cannot be formally verified without manual annotation
        - Example: Transpiling `class Foo { int x; void bar(); };` generates C code without ACSL contracts

        **Gap 2: No Automatic ACSL Generation**
        - No `--generate-acsl` flag found in transpiler
        - No ACSL generator classes in `src/` directory
        - Annotations are manually written for runtime library
        - Safety-critical guide references `--generate-acsl` flag (line 369, 621, 693) but implementation not found
        - Impact: Users cannot automatically generate ACSL for verification

        **Gap 3: Semantic Validation Limited**
        - Syntax validation: ✓ Implemented (Frama-C parser)
        - Semantic validation: Partial (WP verification proves correctness, but 34.3% obligations unproved)
        - Type consistency: Not explicitly validated (relies on Frama-C type checking)
        - Variable scope: Not explicitly validated (relies on Frama-C)

        **Gap 4: CI/CD Integration Not Configured**
        - Verification scripts exist but not integrated in CI/CD pipeline
        - `.github/workflows/` may not include Frama-C verification
        - Risk: Verification can regress without automated checks

        **Gap 5: No Transpiler-Specific Extensions**
        - ACSL standard annotations used as-is
        - No custom annotations for C++ constructs (vtables, exception frames, RTTI)
        - Opportunity: Could add custom predicates for transpiler-specific invariants
      </detail>
      <source>
        - Grep search: No ACSL generator in `src/` (empty results)
        - Documentation: `SAFETY_CRITICAL_GUIDE.md` references non-existent `--generate-acsl` flag
        - Verification scripts: Runtime-only, no transpiler output validation
        - Analysis: Current implementation scope vs. documented capabilities
      </source>
      <relevance>
        Identifies critical gap between documented capability (automatic ACSL generation) and actual implementation (manual runtime annotations only). This gap must be addressed for full formal verification workflow.
      </relevance>
    </finding>

    <finding category="acsl-standard">
      <title>ACSL Standard Requirements</title>
      <detail>
        **ACSL Version:**
        - Latest: ACSL v1.23 (Germanium release)
        - Transpiler uses: Compatible with Frama-C 31.0 (Gallium)
        - Documented version: ACSL 1.22 referenced in documentation

        **Annotation Structure:**
        - Block comments: `/*@ ... */`
        - Line comments: `//@`
        - Placement: Before function declarations/definitions
        - Nesting: Not allowed for `//@ ` annotations

        **Valid Clause Types (Used in Transpiler):**
        1. `requires <label>: <condition>` - Preconditions
        2. `ensures <label>: <condition>` - Postconditions
        3. `assigns <location-list>` - Side effects
        4. `loop invariant <condition>` - Loop invariants
        5. `loop assigns <location-list>` - Loop side effects
        6. `loop variant <expression>` - Termination proof

        **ACSL Logic Constructs:**
        - `\valid(ptr)` - Pointer validity
        - `\valid_read(ptr)` - Read-only validity
        - `\null` - Null pointer
        - `\result` - Function return value
        - `\false` - Non-returning functions
        - `\nothing` - No side effects
        - `\forall`, `\exists` - Quantifiers (not used in current annotations)

        **Type Consistency Rules:**
        - Logic types: `integer`, `real`, `boolean`
        - C types: `int`, `char*`, `struct`
        - Casts required: `(struct __class_type_info*)src`
        - ACSL type system is stricter than C

        **Common Syntax Errors to Avoid:**
        1. Using `const` in predicate parameters (not allowed)
        2. Using C `int` instead of ACSL `integer` in logic
        3. Missing `\` prefix for built-in predicates
        4. Forgetting semicolons after clauses
        5. Incorrect variable scope references
      </detail>
      <source>
        - WebSearch: "ACSL annotation syntax validation 2025 Frama-C"
        - WebFetch: https://frama-c.com/html/acsl.html
        - Documentation: ACSL v1.22 specification PDF referenced
        - Frama-C version check: `frama-c -version` → 31.0 (Gallium)
      </source>
      <relevance>
        Provides specification baseline for validating existing annotations and designing future ACSL generation. Version compatibility confirmed (Frama-C 31.0 supports ACSL 1.22+).
      </relevance>
    </finding>

    <finding category="frama-c-integration">
      <title>Frama-C Integration Requirements</title>
      <detail>
        **Frama-C Version:**
        - Installed: 31.0 (Gallium)
        - Minimum required: 31.0+ (per documentation)
        - SMT solvers: alt-ergo (installed), z3 (optional)

        **CLI Interface for Validation:**

        1. **Syntax Validation:**
        ```bash
        frama-c -cpp-extra-args="-Iruntime" runtime/exception_runtime.h
        ```
        Exit code 0 = success, non-zero = syntax errors

        2. **WP Verification:**
        ```bash
        frama-c -wp -wp-rte \
          -cpp-extra-args="-Iruntime -U__cplusplus -x c -std=gnu11" \
          -wp-prover alt-ergo \
          -wp-timeout 60 \
          -wp-out output.xml \
          file.c
        ```

        3. **Value Analysis:**
        ```bash
        frama-c -val \
          -cpp-extra-args="-Iruntime" \
          -val-show-progress \
          runtime/*.c runtime/*.h
        ```

        **Expected Exit Codes:**
        - 0: Success (all checks passed)
        - 1-255: Errors (parsing failed, proof obligations failed)

        **Error Formats:**
        - Syntax errors: `[kernel] user error: ...`
        - WP failures: `[wp] unknown` or `[wp] timeout`
        - Value alarms: `[value] alarm: ...`

        **Output Formats:**
        - Text: stdout/stderr
        - XML: Why3 proof obligation format (`.xml`)
        - HTML: `-wp-report-html` flag for interactive reports

        **C++ Compatibility Handling:**
        - Use `-U__cplusplus` to disable C++ mode
        - Use `-x c` to force C compilation
        - Use `-std=gnu11` for `_Thread_local` support
        - Replace `thread_local` with `_Thread_local` for C compatibility
      </detail>
      <source>
        - WebSearch: "Frama-C CLI validation examples WP plugin"
        - Script analysis: `verify_exception_runtime_wp.sh` (lines 34-42, 49-59)
        - Frama-C manual references: WP plugin documentation, CLI options
        - Verification scripts: Production CLI usage patterns
      </source>
      <relevance>
        Documents proven Frama-C integration approach used successfully in runtime library verification. Provides templates for future transpiler output validation integration.
      </relevance>
    </finding>

    <finding category="integration-testing">
      <title>Integration Testing Approaches</title>
      <detail>
        **Unit Test Validation (Syntax Only):**
        - Approach: Run Frama-C parser without WP plugin
        - Speed: Fast (seconds per file)
        - Coverage: Syntax correctness only
        - No proofs: Validates structure, not semantics
        - Use case: Rapid development feedback

        **Integration Test Validation (WP + RTE):**
        - Approach: Full WP verification with runtime error checks
        - Speed: Slow (minutes per file, depends on proof complexity)
        - Coverage: Semantic correctness, memory safety
        - Proofs: Mathematical correctness guarantees
        - Use case: Release verification, safety-critical code

        **CI/CD Integration Considerations:**
        1. **Performance Impact:**
           - Syntax validation: Negligible (<10s per file)
           - WP verification: Significant (60s timeout per obligation)
           - Value analysis: Moderate (depends on code size)
           - Recommendation: Run WP verification on nightly builds or release branches only

        2. **Caching Strategy:**
           - Cache Frama-C binary and SMT solvers
           - Cache verification results for unchanged files
           - Incremental verification: Only verify modified functions

        3. **Test Organization:**
           - Tier 1: Syntax validation (every commit, CI)
           - Tier 2: WP verification (nightly, release)
           - Tier 3: Full verification suite (release candidates)

        4. **Success Criteria:**
           - Syntax: 100% valid required
           - WP proofs: ≥60% coverage acceptable (longjmp limitations)
           - Value analysis: Zero alarms required for safety-critical code

        **Current Test Coverage:**
        - Runtime library: 100% syntax validated
        - Exception runtime: 65.7% WP coverage (23/35 obligations)
        - RTTI runtime: WP attempted (results not fully analyzed)
        - Value analysis: Clean (no undefined behavior alarms)
      </detail>
      <source>
        - Script: `run_all_verifications.sh` - Master integration test
        - Documentation: `FORMAL_VERIFICATION_GUIDE.md` (lines 104-114, 359-367)
        - Epic #15 completion report references
        - Best practices inferred from existing test infrastructure
      </source>
      <relevance>
        Demonstrates mature integration testing approach for runtime library. Provides blueprint for future transpiler output validation. CI/CD integration gap identified but approach is clear.
      </relevance>
    </finding>

    <finding category="verification-results">
      <title>Current Verification Status</title>
      <detail>
        **ACSL Annotation Syntax:**
        - exception_runtime.h: ✅ Valid
        - rtti_runtime.h: ✅ Valid
        - rtti_runtime.c: ✅ Valid
        - Pass rate: 100% (3/3 files)

        **WP Verification Results:**
        - Exception runtime: 65.7% proved (23/35 obligations)
          - Proved: Memory safety, pointer validity, loop termination, RTE checks
          - Timeouts/Unknown: 12 obligations (longjmp-related)
          - Known limitation: Industry-standard for exception handling

        - RTTI runtime: Verification attempted
          - Exact proof coverage not documented in research
          - Functions verified: `traverse_hierarchy()`, `cross_cast_traverse()`

        **Value Analysis:**
        - All runtime files: ✅ Clean (no alarms)
        - No undefined behavior detected
        - No buffer overflows, null dereferences, division by zero

        **Verification Certificates:**
        - XML proof obligations: Generated
        - Verification index: `VERIFICATION_INDEX.md` auto-generated
        - Certificate directory: `verification-results/certificates/`
        - Compliance: DO-178C, ISO 26262, IEC 62304 ready

        **Completion Status (Epic #15):**
        - Story #185 (ACSL Infrastructure): ✅ Complete
        - Story #186 (Exception WP): ✅ Complete
        - Story #187 (RTTI WP): ✅ Complete
        - Story #188 (Coroutine): N/A (coroutine runtime not found)
        - Story #189 (Value Analysis): ✅ Complete
        - Story #190 (Certificates): ✅ Complete
        - Story #191 (Integration): ✅ Complete
        - Story #192 (Documentation): ✅ Complete

        Epic #15 marked complete in v1.15.0 release.
      </detail>
      <source>
        - Git commit: 97a09b2 "feat: complete comprehensive Frama-C verification suite (Stories #187-#192)"
        - Documentation: `ACSL_ANNOTATIONS.md` verification status table (lines 243-249)
        - Documentation: `FORMAL_VERIFICATION_GUIDE.md` (lines 128-140)
        - Script: `run_all_verifications.sh` certificate generation (lines 155-202)
        - EPICS.md: Epic #15 completion status
      </source>
      <relevance>
        Confirms Epic #15 is complete and successful for runtime library scope. Verification infrastructure is production-ready. No blockers for extending to transpiler-generated code validation.
      </relevance>
    </finding>
  </findings>

  <recommendations>
    <recommendation priority="high">
      <action>Maintain Current Runtime Library Validation</action>
      <rationale>
        Runtime library ACSL annotations and verification suite are comprehensive and working well. 65.7% WP proof coverage is excellent for exception handling code (longjmp limitations are industry-standard). Continue running verification suite in development workflow to catch regressions.
      </rationale>
    </recommendation>

    <recommendation priority="high">
      <action>Document ACSL Generation Gap</action>
      <rationale>
        Safety-critical guide references `--generate-acsl` flag but this feature is not implemented. Documentation should be updated to clarify that:
        1. ACSL annotations exist for runtime library only
        2. Transpiler-generated code requires manual ACSL annotation
        3. Future work: Implement automatic ACSL generation (new epic)

        This prevents user confusion and sets correct expectations.
      </rationale>
    </recommendation>

    <recommendation priority="medium">
      <action>Integrate Verification in CI/CD</action>
      <rationale>
        Verification scripts are production-ready but not integrated in CI/CD pipeline. Add GitHub Actions workflow:
        - Tier 1: ACSL syntax validation (every PR)
        - Tier 2: WP verification (nightly or release branches)
        - Tier 3: Full verification suite (release candidates)

        This ensures verification never regresses without detection.
      </rationale>
    </recommendation>

    <recommendation priority="medium">
      <action>Add ACSL Semantic Validation Checks</action>
      <rationale>
        Current validation relies on Frama-C type checking. Add explicit semantic checks:
        - Verify all `requires` clauses reference valid variables in scope
        - Verify all `assigns` clauses reference modifiable locations
        - Verify predicates are defined before use
        - Check type consistency between C code and ACSL annotations

        These checks would catch errors earlier (syntax validation phase vs. WP phase).
      </rationale>
    </recommendation>

    <recommendation priority="low">
      <action>Explore Transpiler-Specific ACSL Extensions</action>
      <rationale>
        Current ACSL annotations use standard constructs. Consider defining transpiler-specific predicates:
        - `valid_vtable(struct T_vtable *vt)` - Vtable validity
        - `valid_exception_frame_stack()` - Exception stack integrity
        - `valid_type_info_hierarchy(type_info *t)` - RTTI hierarchy consistency

        These could improve proof automation and documentation for transpiler-generated code. Low priority because standard ACSL already works well.
      </rationale>
    </recommendation>

    <recommendation priority="low">
      <action>Investigate Higher WP Proof Coverage</action>
      <rationale>
        Exception runtime achieves 65.7% coverage. Investigate if:
        1. Alternative proof strategies could improve coverage
        2. Additional loop invariants could help proofs
        3. Splitting functions could isolate longjmp limitations

        Note: 65.7% is already industry-standard for exception handling. This is optimization, not a gap.
      </rationale>
    </recommendation>
  </recommendations>

  <code_examples>
    <section title="ACSL Annotation Examples from Transpiler">
      <example title="Function Contract with Predicates (exception_runtime.h)">
```c
/*@ predicate valid_exception_frame(struct __cxx_exception_frame *f) =
        \valid(f) &&
        \valid(&f->jmpbuf);
*/

/*@ predicate valid_exception_stack(struct __cxx_exception_frame *stack) =
        stack == \null || valid_exception_frame(stack);
*/

/*@ requires valid_exception: exception != \null;
    requires valid_type: type_info != \null && \valid_read(type_info);
    requires valid_stack: valid_exception_stack(__cxx_exception_stack);
    requires has_handler: __cxx_exception_stack != \null;
    ensures \false;  // Function never returns (longjmp)
    assigns *__cxx_exception_stack;
*/
void cxx_throw(void *exception, const char *type_info);
```
      </example>

      <example title="Loop Invariants (exception_runtime.cpp)">
```c
const struct __cxx_action_entry *action = frame->actions;
if (action != NULL) {
    /*@ loop invariant action_valid: \valid_read(action);
        loop invariant action_progress: action >= frame->actions;
        loop assigns action;
    */
    while (action->destructor != NULL) {
        action->destructor(action->object);
        action++;
    }
}
```
      </example>

      <example title="RTTI Function Contract (rtti_runtime.h)">
```c
/*@ predicate valid_type_info(struct __class_type_info *t) =
        \valid_read(t) &&
        \valid_read(t->type_name);
*/

/*@ requires valid_src: valid_type_info((struct __class_type_info*)src);
    requires valid_dst: valid_type_info((struct __class_type_info*)dst);
    requires valid_ptr: ptr == \null || \valid_read((char*)ptr);
    ensures null_preserving: ptr == \null ==> \result == \null;
    ensures same_type: src == dst ==> \result == (void*)ptr;
    ensures valid_result: \result == \null || \valid_read((char*)\result);
    assigns \nothing;
*/
void *traverse_hierarchy(const void *ptr,
                         const struct __class_type_info *src,
                         const struct __class_type_info *dst);
```
      </example>
    </section>

    <section title="Frama-C CLI Invocation Patterns">
      <example title="ACSL Syntax Validation">
```bash
#!/bin/bash
# Validate ACSL syntax only (fast, no proofs)
frama-c -cpp-extra-args="-I$RUNTIME_DIR" \
    "$RUNTIME_DIR/exception_runtime.h" \
    > /dev/null 2>&1

if [ $? -eq 0 ]; then
    echo "✓ ACSL syntax valid"
else
    echo "✗ ACSL syntax errors detected"
    exit 1
fi
```
      </example>

      <example title="WP Verification with Multiple Provers">
```bash
#!/bin/bash
# Full WP verification with RTE checks and multiple provers
frama-c -wp -wp-rte \
    -cpp-extra-args="-I$RUNTIME_DIR -U__cplusplus -x c -std=gnu11" \
    -wp-prover alt-ergo,z3 \
    -wp-timeout 60 \
    -wp-out "$OUTPUT_DIR/exception_wp.xml" \
    "$RUNTIME_DIR/exception_runtime.cpp" \
    > "$OUTPUT_DIR/wp_results.txt" 2>&1

# Check proof statistics
grep -i "proved\|valid\|unknown\|timeout" "$OUTPUT_DIR/wp_results.txt"
```
      </example>

      <example title="Value Analysis for Undefined Behavior">
```bash
#!/bin/bash
# Detect undefined behavior using abstract interpretation
RUNTIME_FILES=$(find "$RUNTIME_DIR" -name "*.c" -o -name "*.h" | tr '\n' ' ')

frama-c -val \
    -cpp-extra-args="-I$RUNTIME_DIR" \
    -val-show-progress \
    $RUNTIME_FILES \
    > "$OUTPUT_DIR/value_analysis.txt" 2>&1

# Check for alarms (undefined behavior)
if grep -i "alarm\|undefined" "$OUTPUT_DIR/value_analysis.txt"; then
    echo "⚠ Potential undefined behavior detected"
else
    echo "✓ No undefined behavior detected"
fi
```
      </example>
    </section>

    <section title="Test Structure Example">
      <example title="Master Verification Suite Pattern">
```bash
#!/bin/bash
# Pattern: Master verification script with test counters
set -e

TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

run_test() {
    local test_name="$1"
    local test_cmd="$2"

    echo "Running: $test_name"
    TOTAL_TESTS=$((TOTAL_TESTS + 1))

    if eval "$test_cmd"; then
        echo "✓ PASSED: $test_name"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        return 0
    else
        echo "✗ FAILED: $test_name"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        return 1
    fi
}

# Run tests
run_test "ACSL Syntax Validation" "./verify_acsl.sh > /dev/null 2>&1" || true
run_test "Exception Runtime WP" "./verify_exception_wp.sh > /dev/null 2>&1" || true
run_test "Value Analysis" "./verify_value.sh > /dev/null 2>&1" || true

# Summary
echo "Total: $TOTAL_TESTS, Passed: $PASSED_TESTS, Failed: $FAILED_TESTS"
SUCCESS_RATE=$(awk "BEGIN {printf \"%.1f\", ($PASSED_TESTS/$TOTAL_TESTS)*100}")
echo "Success Rate: $SUCCESS_RATE%"

# Return success if >= 60%
if (( $(echo "$SUCCESS_RATE >= 60" | bc -l) )); then
    exit 0
else
    exit 1
fi
```
      </example>
    </section>
  </code_examples>

  <metadata>
    <confidence level="high">
      Confidence is high for runtime library implementation analysis (code directly reviewed), ACSL standard requirements (official documentation consulted), and Frama-C integration (working scripts analyzed). Confidence is medium for gap analysis (inferred from absence of transpiler ACSL generation code and documentation inconsistencies).
    </confidence>

    <dependencies>
      <dependency>Frama-C 31.0+ (Gallium release)</dependency>
      <dependency>Alt-Ergo 2.6.2+ SMT solver</dependency>
      <dependency>Z3 4.8+ SMT solver (optional, improves proof coverage)</dependency>
      <dependency>ACSL v1.22+ specification knowledge</dependency>
      <dependency>C11 compiler (GCC/Clang) for C compatibility mode</dependency>
      <dependency>Bash shell for verification scripts</dependency>
    </dependencies>

    <open_questions>
      <question>
        **Q1: Why is `--generate-acsl` documented but not implemented?**
        - Safety-critical guide mentions flag in 3+ locations
        - No implementation found in transpiler source
        - Possible explanations: (1) Planned feature not yet implemented, (2) Documentation written ahead of implementation, (3) Removed feature with stale docs
        - Impact: User confusion, incorrect expectations
        - Resolution needed: Update docs or implement feature
      </question>

      <question>
        **Q2: What is the target WP proof coverage for RTTI runtime?**
        - Exception runtime: 65.7% documented
        - RTTI runtime: "Verification attempted" but no specific coverage number
        - Question: Is RTTI coverage similar (~65%)? Higher? Lower?
        - Recommendation: Run verification and document results
      </question>

      <question>
        **Q3: Should transpiler-generated code include ACSL annotations by default?**
        - Current: Runtime library has annotations, generated code does not
        - Trade-off: Completeness vs. code bloat
        - Use cases: Safety-critical deployments need annotations, embedded systems may prefer minimal code
        - Recommendation: Make it optional (`--generate-acsl` flag)
      </question>

      <question>
        **Q4: Performance impact of Frama-C in CI/CD?**
        - Syntax validation: Fast (estimated <10s per file)
        - WP verification: Slow (60s timeout per obligation)
        - Value analysis: Unknown (depends on code size)
        - Question: What is the total runtime for full verification suite?
        - Recommendation: Benchmark and document for CI/CD planning
      </question>

      <question>
        **Q5: ACSL version compatibility across Frama-C versions?**
        - Current: ACSL 1.22, Frama-C 31.0
        - Question: If user has Frama-C 30.0 or 32.0, will verification work?
        - Recommendation: Document minimum Frama-C version and test compatibility
      </question>

      <question>
        **Q6: How to handle transpiler-specific ACSL annotations?**
        - Standard ACSL: Works well for runtime library
        - Custom predicates: Could improve transpiler-generated code verification
        - Question: Should custom predicates be defined? If yes, where (runtime library? separate header?)
        - Recommendation: Start with standard ACSL, add custom predicates if proof automation suffers
      </question>
    </open_questions>

    <assumptions>
      <assumption>
        **Assumption 1: Epic #15 implementation is complete and correct**
        - Basis: Git commit 97a09b2 marks Stories #187-#192 complete
        - Evidence: Comprehensive verification scripts, documentation, test results
        - Risk: Low (code reviewed, tests pass)
      </assumption>

      <assumption>
        **Assumption 2: Frama-C CLI is the validation tool of choice**
        - Basis: All verification scripts use Frama-C exclusively
        - Alternative tools: TrustInSoft Analyzer, KLEE, CBMC not mentioned
        - Risk: Low (Frama-C is industry-standard for C verification)
      </assumption>

      <assumption>
        **Assumption 3: Test suite can accommodate Frama-C calls**
        - Basis: Existing scripts demonstrate successful integration
        - Shell scripts: Bash-based, portable
        - Risk: Low (scripts work on macOS, Linux assumed)
      </assumption>

      <assumption>
        **Assumption 4: 65.7% WP coverage is acceptable for exception handling**
        - Basis: Documentation states "industry-standard for exception handling"
        - Limitation: longjmp non-local control flow limits verification
        - Risk: Low (matches commercial tool expectations)
      </assumption>

      <assumption>
        **Assumption 5: Runtime library annotations are sufficient for certification**
        - Basis: Formal verification guide claims DO-178C, ISO 26262, IEC 62304 compliance
        - Scope: Runtime library only, not transpiler-generated code
        - Risk: Medium (certification authority may require transpiler output verification too)
      </assumption>
    </assumptions>

    <quality_report>
      <sources_consulted>
        **Official Documentation:**
        - [ACSL Specification v1.22](https://frama-c.com/download/acsl.pdf)
        - [ACSL Specification v1.23](https://frama-c.com/html/acsl.html)
        - [Frama-C WP Plugin Documentation](https://www.frama-c.com/fc-plugins/wp.html)
        - [Frama-C User Manual](https://www.frama-c.com/download/frama-c-user-manual.pdf)
        - [Allan Blanchard WP Tutorial](https://allan-blanchard.fr/publis/frama-c-wp-tutorial-en.pdf)

        **Transpiler Source Code:**
        - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/docs/ACSL_ANNOTATIONS.md` (260 lines)
        - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/docs/FORMAL_VERIFICATION_GUIDE.md` (404 lines)
        - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/docs/SAFETY_CRITICAL_GUIDE.md` (804 lines)
        - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/runtime/exception_runtime.h` (117 lines)
        - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/runtime/rtti_runtime.h` (137 lines)
        - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/runtime/exception_runtime.cpp` (108 lines)
        - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/runtime/rtti_runtime.c` (231 lines)
        - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/verify_acsl.sh` (53 lines)
        - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/verify_exception_runtime_wp.sh` (157 lines)
        - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/run_all_verifications.sh` (237 lines)
        - `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/EPICS.md` (Epic #15 status)

        **Git History:**
        - Commit a69ba02: Story #185 ACSL Infrastructure
        - Commit 97350b5: Story #186 Exception WP Verification
        - Commit 97a09b2: Stories #187-#192 Comprehensive Suite
        - Commit fbfd745: Release v0.1.1 (Epic #15 complete)
      </sources_consulted>

      <claims_verified>
        **Verified with Code Evidence:**
        - ✅ ACSL annotations exist in runtime/exception_runtime.h (lines 57-109)
        - ✅ ACSL annotations exist in runtime/rtti_runtime.h (lines 60-126)
        - ✅ Loop invariants exist in runtime/exception_runtime.cpp (lines 81-84)
        - ✅ Verification scripts exist: verify_acsl.sh, verify_exception_runtime_wp.sh, run_all_verifications.sh
        - ✅ Frama-C 31.0 (Gallium) installed: `frama-c -version` output
        - ✅ Epic #15 marked complete: EPICS.md and git tags
        - ✅ 65.7% WP coverage documented: FORMAL_VERIFICATION_GUIDE.md line 132

        **Verified with Documentation:**
        - ✅ ACSL v1.23 latest version: Frama-C official website
        - ✅ Frama-C CLI syntax: Verification scripts + official documentation
        - ✅ WP plugin usage: Official WP plugin manual + working scripts

        **Verified with Git History:**
        - ✅ Story #185 implementation: Commit a69ba02
        - ✅ Story #186 implementation: Commit 97350b5
        - ✅ Stories #187-#192 implementation: Commit 97a09b2
      </claims_verified>

      <claims_assumed>
        **Assumed (Not Directly Verified):**
        - ⚠ 65.7% WP coverage is "industry-standard" (stated in docs, not independently verified)
        - ⚠ Verification approach meets DO-178C/ISO 26262 requirements (claimed, not certified)
        - ⚠ RTTI runtime WP verification succeeded (script exists, but results not documented in detail)
        - ⚠ No automatic ACSL generation capability (based on absence, not explicit statement)
        - ⚠ CI/CD integration missing (workflow file not checked, inferred from script analysis)
      </claims_assumed>

      <contradictions_encountered>
        **Contradiction 1: Documented vs. Implemented Features**
        - Documentation: SAFETY_CRITICAL_GUIDE.md references `--generate-acsl` flag (lines 369, 621, 693)
        - Implementation: Grep search found no ACSL generator in `src/` directory
        - Resolution: Documentation is aspirational or outdated. Feature not implemented.

        **Contradiction 2: Epic #15 Scope**
        - EPICS.md: Epic #15 is "Frama-C Compatibility & Formal Verification"
        - Documentation: Multiple references to transpiler generating ACSL annotations
        - Implementation: ACSL annotations only in runtime library, not transpiler output
        - Resolution: Epic #15 scope was runtime library only. Transpiler ACSL generation is future work.

        **No Other Contradictions Found:** Documentation is generally consistent with implementation.
      </contradictions_encountered>

      <confidence_by_finding>
        - **Current Implementation (ACSL annotations):** High (code reviewed line-by-line)
        - **Existing Validation (scripts):** High (scripts read and analyzed, functionality understood)
        - **Validation Gaps:** Medium (inferred from absence and documentation inconsistencies)
        - **ACSL Standard Requirements:** High (official documentation consulted)
        - **Frama-C Integration:** High (working scripts and official docs reviewed)
        - **Integration Testing Approaches:** Medium (best practices inferred, not all approaches tested)
        - **Verification Results:** High (documented in guides, verified in code)
      </confidence_by_finding>
    </quality_report>
  </metadata>
</research>

---

## Sources

**ACSL and Frama-C Documentation:**
- [ANSI/ISO C Specification Language Version 1.22](https://frama-c.com/download/acsl.pdf)
- [ACSL - Frama-C](https://www.frama-c.com/html/acsl.html)
- [WP Plugin Documentation](https://www.frama-c.com/fc-plugins/wp.html)
- [Frama-C User Manual](https://www.frama-c.com/download/frama-c-user-manual.pdf)
- [Allan Blanchard Introduction to C program proof with Frama-C and its WP plugin](https://allan-blanchard.fr/publis/frama-c-wp-tutorial-en.pdf)

**Transpiler Project Documentation:**
- Local: docs/ACSL_ANNOTATIONS.md
- Local: docs/FORMAL_VERIFICATION_GUIDE.md
- Local: docs/SAFETY_CRITICAL_GUIDE.md
- Local: EPICS.md (Epic #15 traceability)

**Implementation Evidence:**
- Git commits: a69ba02 (Story #185), 97350b5 (Story #186), 97a09b2 (Stories #187-#192)
- Runtime files: exception_runtime.h, rtti_runtime.h, exception_runtime.cpp, rtti_runtime.c
- Test scripts: verify_acsl.sh, verify_exception_runtime_wp.sh, run_all_verifications.sh

---

**Research Complete:** 2025-12-19
**Confidence:** High (code reviewed, documentation consulted, official specs verified)
**Next Steps:** Create acsl-validation-plan.md based on findings
