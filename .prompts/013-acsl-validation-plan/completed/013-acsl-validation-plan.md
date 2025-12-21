# ACSL Annotation Validation Implementation Plan

<objective>
Create an implementation plan for ACSL annotation validation and Frama-C integration testing in the C++ to C transpiler.

Purpose: Ensure generated ACSL annotations are syntactically and semantically valid for formal verification with Frama-C
Input: Research findings from acsl-validation-research.md
Output: acsl-validation-plan.md with phased implementation approach
</objective>

<context>
Research findings: @.prompts/012-acsl-validation-research/acsl-validation-research.md

Key findings to incorporate:
- Current ACSL generation implementation (from Epic #15)
- Identified validation gaps
- Frama-C integration requirements
- Test suite modification needs
</context>

<planning_requirements>
The plan must address:

**Validation Requirements**:
1. Syntax validation for all ACSL annotation types generated
2. Semantic validation (type checking, scope verification)
3. Integration with existing test suite
4. Both unit tests (without Frama-C) and integration tests (with Frama-C CLI)

**Technical Constraints**:
- Must work with existing transpiler architecture
- Cannot break existing ACSL generation (Epic #15 complete)
- Should integrate with CMake build system
- CI/CD friendly (fast validation, clear error reporting)

**Success Criteria**:
- All generated ACSL annotations pass Frama-C syntax check
- Invalid annotations are caught in tests before deployment
- Clear error messages guide debugging
- Minimal performance impact on test suite
- Documentation for maintaining validation tests
</planning_requirements>

<output_structure>
Save to: `.prompts/013-acsl-validation-plan/acsl-validation-plan.md`

Structure the plan using this XML format:

```xml
<plan>
  <summary>
    Implementation approach for ACSL validation combining unit-level syntax checks with Frama-C integration testing.
  </summary>

  <phases>
    <phase number="1" name="syntax-validation-unit-tests">
      <objective>Create unit tests for ACSL syntax validation without requiring Frama-C</objective>
      <tasks>
        <task priority="high">Design ACSL syntax validator class (regex-based or parser-based)</task>
        <task priority="high">Implement validation for function contracts (requires, ensures)</task>
        <task priority="high">Implement validation for loop annotations (invariant, variant, assigns)</task>
        <task priority="medium">Implement validation for memory specifications</task>
        <task priority="medium">Add unit tests for each validator component</task>
        <task priority="low">Create validator test fixtures with valid/invalid examples</task>
      </tasks>
      <deliverables>
        <deliverable>ACSLSyntaxValidator class (header + implementation)</deliverable>
        <deliverable>ACSLSyntaxValidatorTest.cpp with 20+ test cases</deliverable>
        <deliverable>Test fixtures: valid_annotations.txt, invalid_annotations.txt</deliverable>
      </deliverables>
      <dependencies>None - can start immediately</dependencies>
      <execution_notes>
        Use existing test infrastructure from transpiler.
        Follow TDD: write failing tests first, implement validators to pass.
        Reference ACSL specification for syntax rules.
      </execution_notes>
    </phase>

    <phase number="2" name="frama-c-integration-wrapper">
      <objective>Create wrapper for Frama-C CLI invocation in test suite</objective>
      <tasks>
        <task priority="high">Design FramaCValidator class for CLI invocation</task>
        <task priority="high">Implement Frama-C process execution with timeout</task>
        <task priority="high">Parse Frama-C output for errors and warnings</task>
        <task priority="medium">Add graceful degradation (skip if Frama-C not installed)</task>
        <task priority="medium">Implement caching to avoid re-validation</task>
        <task priority="low">Add verbose logging for debugging</task>
      </tasks>
      <deliverables>
        <deliverable>FramaCValidator class (header + implementation)</deliverable>
        <deliverable>FramaCValidatorTest.cpp with CLI invocation tests</deliverable>
        <deliverable>Documentation: FRAMA_C_INTEGRATION.md</deliverable>
      </deliverables>
      <dependencies>
        - Frama-C installation (optional for unit tests, required for integration tests)
        - Phase 1 validator (can reuse error reporting patterns)
      </dependencies>
      <execution_notes>
        Frama-C CLI: `frama-c -wp -wp-prover none file.c`
        Exit codes: 0 = success, non-zero = errors
        Parse stderr for error messages and line numbers.
        Consider using Bash tool to prototype CLI invocations.
      </execution_notes>
    </phase>

    <phase number="3" name="integration-test-suite">
      <objective>Add Frama-C validation to existing ACSL generation tests</objective>
      <tasks>
        <task priority="high">Identify existing ACSL generation tests (from Epic #15)</task>
        <task priority="high">Add FramaCValidator calls to integration tests</task>
        <task priority="high">Create test cases for each ACSL annotation type</task>
        <task priority="medium">Add negative tests (intentionally invalid annotations)</task>
        <task priority="medium">Integrate with CMake test targets</task>
        <task priority="low">Add CI/CD workflow step for Frama-C validation</task>
      </tasks>
      <deliverables>
        <deliverable>Enhanced ACSLIntegrationTest.cpp with Frama-C validation</deliverable>
        <deliverable>CMakeLists.txt updates for Frama-C test targets</deliverable>
        <deliverable>CI workflow: .github/workflows/frama-c-validation.yml</deliverable>
      </deliverables>
      <dependencies>
        - Phase 2 FramaCValidator complete
        - Existing ACSL generation tests identified
      </dependencies>
      <execution_notes>
        Tests should:
        1. Generate C code with ACSL annotations (existing)
        2. Validate syntax with unit validator (Phase 1)
        3. Validate with Frama-C CLI (Phase 2)
        4. Report clear errors if validation fails

        Skip Frama-C tests gracefully if tool not available.
      </execution_notes>
    </phase>

    <phase number="4" name="semantic-validation">
      <objective>Add semantic checks beyond syntax (type consistency, scope verification)</objective>
      <tasks>
        <task priority="high">Implement type checking for ACSL expressions</task>
        <task priority="high">Verify variable scope in annotations</task>
        <task priority="medium">Check completeness of function contracts</task>
        <task priority="medium">Validate loop variant decreases</task>
        <task priority="low">Add cross-function contract consistency checks</task>
      </tasks>
      <deliverables>
        <deliverable>ACSLSemanticValidator class (header + implementation)</deliverable>
        <deliverable>ACSLSemanticValidatorTest.cpp with type/scope tests</deliverable>
        <deliverable>Integration with existing validation pipeline</deliverable>
      </deliverables>
      <dependencies>
        - Phase 1 syntax validator (semantic checks build on syntax)
        - Access to transpiler AST (for type and scope information)
      </dependencies>
      <execution_notes>
        This is more complex than syntax validation.
        May require integration with Clang AST analysis.
        Consider deferring to future work if too complex initially.
        Frama-C itself will catch many semantic errors, so focus on high-value checks.
      </execution_notes>
    </phase>

    <phase number="5" name="documentation-and-maintenance">
      <objective>Document validation system and provide maintenance guide</objective>
      <tasks>
        <task priority="high">Write ACSL_VALIDATION_GUIDE.md (user-facing)</task>
        <task priority="high">Write FRAMA_C_INTEGRATION.md (developer-facing)</task>
        <task priority="medium">Document common validation errors and fixes</task>
        <task priority="medium">Add troubleshooting section for Frama-C issues</task>
        <task priority="low">Create examples of valid vs invalid annotations</task>
      </tasks>
      <deliverables>
        <deliverable>docs/ACSL_VALIDATION_GUIDE.md</deliverable>
        <deliverable>docs/FRAMA_C_INTEGRATION.md</deliverable>
        <deliverable>docs/ACSL_TROUBLESHOOTING.md</deliverable>
        <deliverable>examples/acsl/ with valid/invalid annotation examples</deliverable>
      </deliverables>
      <dependencies>
        - All implementation phases complete
        - Validation system tested and working
      </dependencies>
      <execution_notes>
        Documentation should include:
        - How to run validation tests
        - How to interpret validation errors
        - How to add new validation tests
        - Frama-C installation instructions
        - CI/CD setup guide
      </execution_notes>
    </phase>
  </phases>

  <execution_strategy>
    <sequential_phases>
      Phases must be executed in order due to dependencies:
      1 → 2 → 3 → 4 → 5
    </sequential_phases>

    <optional_phases>
      Phase 4 (semantic validation) can be deferred if too complex.
      Frama-C itself provides semantic validation, so Phase 1-3 are sufficient for MVP.
    </optional_phases>

    <testing_strategy>
      - Follow TDD for all validation code
      - Each validator component gets dedicated test file
      - Integration tests verify end-to-end workflow
      - Negative tests confirm error detection works
    </testing_strategy>

    <performance_considerations>
      - Frama-C CLI can be slow on large files
      - Use caching to avoid re-validation
      - Run Frama-C tests in parallel where possible
      - Consider making Frama-C validation optional for rapid iteration
    </performance_considerations>
  </execution_strategy>

  <metadata>
    <confidence level="high">
      Plan is based on standard testing patterns and Frama-C documentation.
      Phases are incremental and testable.
      Dependencies are clearly identified.
    </confidence>
    <dependencies>
      - Frama-C installed on development machines and CI/CD (version 27.0+ recommended)
      - CMake build system (already exists)
      - Existing ACSL generation code from Epic #15
      - Test infrastructure (exists)
    </dependencies>
    <open_questions>
      - Should semantic validation (Phase 4) be in scope for MVP?
      - What Frama-C version should be minimum requirement?
      - Should validation be mandatory (fail tests) or warning-only initially?
      - How to handle transpiler-specific ACSL extensions not in standard?
    </open_questions>
    <assumptions>
      - Epic #15 ACSL generation is functionally correct (no major bugs)
      - Frama-C CLI is stable and has predictable output format
      - Test suite can accommodate additional validation steps
      - CI/CD environment can install Frama-C (or skip validation gracefully)
    </assumptions>
  </metadata>
</plan>
```
</output_structure>

<summary_requirements>
Create `.prompts/013-acsl-validation-plan/SUMMARY.md`

**One-liner**: 5-phase plan for ACSL validation: syntax checks → Frama-C integration → semantic validation

**Key Findings**:
- Phase 1: Unit-level syntax validation (no Frama-C needed)
- Phase 2: Frama-C CLI wrapper for integration tests
- Phase 3: Integration with existing test suite
- Phase 4: Semantic validation (optional/advanced)
- Phase 5: Documentation and maintenance guide

**Decisions Needed**:
- Is Phase 4 (semantic validation) in scope for MVP?
- Minimum Frama-C version requirement?
- Validation failure policy (fail tests vs warnings)?

**Blockers**: None (Frama-C installation is dependency, not blocker)

**Next Step**: Execute Phase 1 (syntax validation unit tests)
</summary_requirements>

<success_criteria>
- Plan addresses both syntax and semantic validation
- Phases are sequential and buildable incrementally
- Frama-C integration is clearly specified with CLI examples
- Testing strategy follows TDD methodology
- Performance considerations documented
- Metadata captures uncertainties (semantic validation scope, Frama-C version)
- SUMMARY.md created with phase breakdown
- Ready for implementation (Do prompts can execute each phase)
</success_criteria>
