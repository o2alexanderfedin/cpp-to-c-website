# ACSL Validation Plan Summary

**Date:** 2025-12-19
**Status:** Planning Complete, Ready for Implementation
**Epic:** ACSL Validation & Generation Infrastructure

---

## One-Liner

6-phase implementation plan for ACSL annotation generation and validation: ACSL generator design → syntax validation → Frama-C integration → end-to-end testing → semantic validation (optional) → documentation

---

## Key Findings from Research

### Critical Gap Identified
- **Runtime Library Only:** ACSL annotations exist for exception_runtime.h and rtti_runtime.h (Epic #15, v1.15.0) with 100% syntax validation and 65.7% WP proof coverage
- **No Transpiler ACSL Generation:** Documentation references `--generate-acsl` flag but implementation does NOT exist in src/ directory
- **Impact:** Transpiled C++ code cannot be formally verified without manual ACSL annotation

### Mature Infrastructure
- **Frama-C Integration:** Proven CLI patterns via verify_acsl.sh (syntax), verify_exception_runtime_wp.sh (WP), run_all_verifications.sh (master suite)
- **Version:** Frama-C 31.0 (Gallium), compatible with ACSL v1.22+
- **Results:** 100% syntax validation, 65.7% WP proof coverage on runtime library

### Gap Analysis
1. **No automatic ACSL generation** for transpiler output (must implement)
2. **No validation for transpiled code** (only runtime library validated)
3. **CI/CD not integrated** (scripts exist but not in GitHub Actions)
4. **Documentation inconsistency** (references non-existent `--generate-acsl` flag)

---

## Implementation Phases

### Phase 1: ACSL Generator Design and Infrastructure (40-60 hours)
**Objective:** Design and implement ACSL annotation generator integrated with transpiler AST

**Key Deliverables:**
- `ACSLGenerator` base class (src/codegen/ACSLGenerator.h/.cpp)
- `ACSLFunctionAnnotator` - Generate function contracts (requires, ensures, assigns)
- `ACSLLoopAnnotator` - Generate loop invariants, variants, assigns
- `ACSLClassAnnotator` - Generate class invariant predicates
- CLI flags: `--generate-acsl`, `--acsl-level=<basic|full>`, `--acsl-output=<inline|separate>`
- Unit tests: ACSLGeneratorTest.cpp (15+ test cases)

**Success Criteria:**
- ACSL generator integrates with transpiler pipeline
- CLI flags parsed and configuration accessible
- Unit tests pass with 95%+ code coverage

**Dependencies:** Transpiler AST infrastructure (Clang), CodeGenerator class

---

### Phase 2: ACSL Syntax Validator Implementation (20-30 hours)
**Objective:** Create lightweight syntax validator for fast validation without Frama-C

**Key Deliverables:**
- `ACSLSyntaxValidator` class (src/validation/ACSLSyntaxValidator.h/.cpp)
- Validation rules: function contracts, loop annotations, predicates, logic operators
- Error reporting: file:line:column format with suggestions
- Unit tests: ACSLSyntaxValidatorTest.cpp (40+ test cases)
- Test fixtures: valid_annotations.txt, invalid_annotations.txt

**Success Criteria:**
- Catches 90%+ of common syntax errors
- Zero false positives on runtime library annotations
- Validation performance: <100ms for typical file
- Clear, actionable error messages

**Dependencies:** ACSL v1.22 specification, runtime library annotations for test cases

---

### Phase 3: Frama-C Integration and CLI Wrapper (25-35 hours)
**Objective:** Create FramaCValidator wrapper for authoritative Frama-C CLI validation

**Key Deliverables:**
- `FramaCValidator` class (src/validation/FramaCValidator.h/.cpp)
- Syntax validation mode: `frama-c -cpp-extra-args` with error parsing
- WP verification mode: `frama-c -wp -wp-rte` with XML output parsing
- Value analysis mode: `frama-c -val` with alarm detection
- Graceful degradation: Skip if Frama-C not installed (warning)
- Result caching: .framac-cache/ directory for performance
- Integration tests: FramaCValidatorTest.cpp (20+ test cases)
- Documentation: FRAMA_C_INTEGRATION.md

**Success Criteria:**
- Validates runtime library successfully (matches existing scripts)
- WP verification reproduces 65.7% proof coverage for exception runtime
- Caching reduces validation time by 80%+ for unchanged files
- Graceful degradation works (tests pass without Frama-C)

**Dependencies:** Frama-C 31.0+ (optional), Alt-Ergo/Z3 SMT solvers (optional)

---

### Phase 4: Integration Test Suite and End-to-End Validation (35-50 hours)
**Objective:** Comprehensive end-to-end testing of ACSL generation and validation

**Key Deliverables:**
- `ACSLIntegrationTest.cpp` (35+ test cases)
- Test categories:
  - Function contracts (10 cases): simple, pointers, returns, side effects, non-returning
  - Loop annotations (8 cases): for, while, nested, iterator, infinite
  - Class invariants (6 cases): simple, pointers, polymorphic, constructors, destructors, RTTI
  - Negative tests (5 cases): syntax errors, semantic errors, scope errors
  - Edge cases (6 cases): templates, constexpr, inline, static, extern
- C++ test fixtures (30+ files in tests/fixtures/cpp/)
- Golden files (30+ files in tests/fixtures/golden/)
- CMake integration: `make test-acsl-integration`
- CI/CD workflow: .github/workflows/acsl-validation.yml
- Documentation: ACSL_INTEGRATION_TESTING.md

**Success Criteria:**
- All integration tests pass (35+ test cases)
- Syntax validation: 100% pass rate on generated annotations
- Frama-C validation: ≥80% pass rate
- Negative tests correctly detect errors (5+ error types)
- CI/CD workflow runs on every PR

**Dependencies:** Phase 1 (ACSL generator), Phase 2 (syntax validator), Phase 3 (Frama-C wrapper)

---

### Phase 5: Semantic Validation - Advanced (30-40 hours) [OPTIONAL for MVP]
**Objective:** Add semantic validation beyond syntax (type consistency, scope verification)

**Key Deliverables:**
- `ACSLSemanticValidator` class (src/validation/ACSLSemanticValidator.h/.cpp)
- Type consistency validation: ACSL logic types vs. C types
- Variable scope verification: ensure variables in annotations are in scope
- Contract completeness checks: pointer validity, assigns completeness
- Loop annotation completeness: invariants reference loop variables
- Predicate consistency: defined before use, no recursion
- Unit tests: ACSLSemanticValidatorTest.cpp (28+ test cases)
- Documentation: ACSL_SEMANTIC_VALIDATION.md

**Success Criteria:**
- Semantic validator catches type mismatches (10+ test cases)
- Scope verification detects out-of-scope references (8+ test cases)
- Completeness checks warn on incomplete contracts (6+ test cases)
- False positive rate: <5%

**Dependencies:** Phase 1 (ACSL generator), Phase 2 (syntax validator), Transpiler AST (type info, symbol tables)

**MVP Decision:** **Defer to future work** - Frama-C already provides semantic validation; custom validator adds faster feedback but increases complexity (30-40 hours). Recommend implementing only if Frama-C error messages prove insufficient during Phase 4 testing.

---

### Phase 6: Documentation, Examples, and Maintenance (20-30 hours)
**Objective:** Comprehensive documentation, examples, and maintenance guides

**Key Deliverables:**
- `ACSL_GENERATION_GUIDE.md` - User-facing guide (~500 lines)
- `ACSL_VALIDATOR_IMPLEMENTATION.md` - Developer guide (~400 lines)
- `ACSL_TROUBLESHOOTING.md` - Error catalog + fixes (~350 lines)
- `ACSL_BEST_PRACTICES.md` - Best practices (~250 lines)
- Annotated examples (examples/acsl/): 6+ examples (factorial, buffer processing, Stack class, bubble sort, RTTI, exceptions)
- Update existing docs:
  - SAFETY_CRITICAL_GUIDE.md (fix `--generate-acsl` references)
  - FORMAL_VERIFICATION_GUIDE.md (add transpiler validation section)
  - ACSL_ANNOTATIONS.md (add automatic generation section)

**Success Criteria:**
- User can enable ACSL generation within 15 minutes (using guide)
- Developer can add new annotation type within 1 hour (using implementation guide)
- Common errors have documented solutions (10+ error/fix pairs)
- Examples compile, transpile, and validate successfully with Frama-C

**Dependencies:** Phase 1-5 complete (to document features)

---

## Execution Strategy

### Sequential Dependencies
```
Phase 1 (ACSL Generator)
  ↓
Phase 4 (Integration Tests) → Phase 6 (Documentation)
  ↑
  ├── Phase 2 (Syntax Validator)
  └── Phase 3 (Frama-C Wrapper)
```

**Critical Path:** Phase 1 → Phase 4 → Phase 6 (blocks all downstream work)

### Parallel Opportunities
- Phase 2 (Syntax Validator) and Phase 3 (Frama-C Wrapper) can develop **in parallel** (independent)
- Phase 1 subtasks: ACSLFunctionAnnotator, ACSLLoopAnnotator, ACSLClassAnnotator can develop **in parallel**
- Phase 4 test categories can execute **in parallel** (function contracts, loop annotations, class invariants)

### Timeline Estimates
- **Solo Developer (MVP, excluding Phase 5):** 140-205 hours (~4-5 weeks)
- **Solo Developer (Full, including Phase 5):** 170-245 hours (~5-6 weeks)
- **2 Developers (MVP):** ~3-4 weeks (40% time reduction via parallelization)
- **3 Developers (MVP):** ~2-3 weeks (50% time reduction)

---

## Decisions Needed

### High Priority (Block Phase 1 Start)
1. **Q1: What is the target ACSL coverage?**
   - Options: (a) Basic (function contracts only), (b) Full (function + loop + class invariants)
   - Recommendation: **Basic for MVP**, add Full incrementally
   - Impact: Affects Phase 1 scope and effort

2. **Q2: Should ACSL generation be default on or opt-in?**
   - Options: (a) Default on (`--no-acsl` to disable), (b) Default off (`--generate-acsl` to enable)
   - Recommendation: **Default off for MVP** (explicit opt-in), reconsider after user feedback
   - Impact: Affects CLI design in Phase 1

### Medium Priority (Block Phase 4 Start)
3. **Q3: How to handle C++ constructs with no direct ACSL equivalent?**
   - Examples: Templates, constexpr, SFINAE
   - Recommendation: **Skip with warning for MVP**, document limitations
   - Impact: Affects test coverage in Phase 4

4. **Q4: Should Frama-C validation be mandatory or optional in CI/CD?**
   - Options: (a) Mandatory (PR fails), (b) Optional (warning only)
   - Recommendation: **Optional for MVP**, mandatory after stabilization
   - Impact: Affects CI/CD workflow in Phase 4

### Low Priority (Can decide during implementation)
5. **Q5: Should Phase 5 (Semantic Validator) be in MVP scope?**
   - Recommendation: **Defer to future work** (Frama-C provides sufficient semantic validation)
   - Impact: Reduces MVP timeline by 30-40 hours

6. **Q6: What is the minimum Frama-C version to support?**
   - Recommendation: **31.0+ only for MVP** (current installed version)
   - Impact: Affects Phase 3 implementation

---

## Blockers

**No Critical Blockers Identified**

### Potential Risks (Mitigated)
1. **ACSL generation complexity** (templates, advanced C++) → Mitigation: Start with core constructs, defer advanced features
2. **Frama-C proof failures** (unprovable annotations) → Mitigation: Treat WP failures as warnings, focus on syntax validation for MVP
3. **Performance degradation** (slow Frama-C) → Mitigation: Caching, run expensive validations on nightly builds only
4. **Frama-C installation complexity** → Mitigation: Docker image, graceful degradation (skip if not installed)
5. **Documentation maintenance burden** → Mitigation: Generate docs from code, automate example testing

---

## Success Metrics

| Metric | Target | Measurement |
|--------|--------|-------------|
| ACSL Generation Coverage | 80%+ of transpiled constructs annotated | Count annotated/total in test suite |
| Syntax Validation Accuracy | 95%+ (TP + TN) | Confusion matrix on test suite |
| Frama-C Integration Success | 100% syntax pass, 80%+ WP proof pass | Frama-C CLI exit codes, WP stats |
| Test Coverage | 95%+ code coverage | gcov/lcov on generator/validator |
| Performance Impact | <10% transpilation time increase | Benchmark with/without `--generate-acsl` |
| Documentation Quality | User setup <15 minutes | Usability testing with new developer |
| CI/CD Regression Prevention | 100% ACSL regressions caught | Monitor CI/CD failures, false negative rate |

---

## Next Steps

### Immediate (Start Phase 1)
1. **Create Epic/Issues in GitHub:** Break down Phase 1 into user stories/tasks
2. **Decision on Q1 & Q2:** Determine ACSL coverage level and CLI default behavior
3. **Setup development branch:** Create `feature/acsl-generation` branch from develop
4. **Implement ACSLGenerator base class:** Start with TDD (write failing test, implement, refactor)

### Phase 1 Kickoff Tasks (First Week)
- [ ] Design ACSLGenerator class architecture (2-4 hours)
- [ ] Create ACSLGenerator.h/.cpp skeleton (2 hours)
- [ ] Implement CLI flag parsing for `--generate-acsl` (4 hours)
- [ ] Create ACSLGeneratorTest.cpp with first test (annotation formatting) (3 hours)
- [ ] Implement ACSLFunctionAnnotator skeleton (6 hours)
- [ ] **Total first week:** ~17-19 hours (foundation established)

### Validation Checkpoint (End of Phase 1)
- Review generated annotations manually (compare to runtime library quality)
- Run transpiler with `--generate-acsl` on sample C++ code
- Validate generated ACSL syntax with Frama-C CLI (manual verification before Phase 2)
- Adjust design if fundamental issues discovered

---

## References

**Research Input:**
- acsl-validation-research.md (comprehensive findings on Epic #15, validation gaps, Frama-C integration)

**Key Source Files:**
- Runtime library annotations: /runtime/exception_runtime.h (lines 57-109), /runtime/rtti_runtime.h (lines 60-126)
- Validation scripts: /tests/verify_acsl.sh, /tests/verify_exception_runtime_wp.sh, /tests/run_all_verifications.sh
- Documentation: /docs/ACSL_ANNOTATIONS.md, /docs/FORMAL_VERIFICATION_GUIDE.md, /docs/SAFETY_CRITICAL_GUIDE.md

**External Resources:**
- ACSL v1.22 Specification: https://frama-c.com/download/acsl.pdf
- Frama-C WP Plugin Documentation: https://www.frama-c.com/fc-plugins/wp.html
- Allan Blanchard WP Tutorial: https://allan-blanchard.fr/publis/frama-c-wp-tutorial-en.pdf

---

**Plan Status:** ✅ Complete and Ready for Implementation
**Confidence Level:** High (based on proven Frama-C patterns from Epic #15)
**Estimated Timeline (MVP):** 4-5 weeks solo, 2-3 weeks with team of 3
**Recommended MVP Scope:** Phases 1-4, 6 (defer Phase 5 semantic validation to future work)
