# ACSL Validation Research Summary

**Date:** 2025-12-19
**Epic:** #15 - Frama-C Compatibility & Formal Verification
**Research Phase:** Complete

---

## One-Liner

**ACSL annotation infrastructure is complete and production-ready for runtime library (Epic #15, v1.15.0) with comprehensive Frama-C validation achieving 65.7% WP proof coverage, but automatic ACSL generation for transpiler-generated C code is not implemented despite documentation references.**

---

## Key Findings

### 1. Current ACSL Implementation Status

**✅ Complete for Runtime Library (Story #185)**
- **Files Annotated:**
  - `runtime/exception_runtime.h` - Exception handling contracts
  - `runtime/rtti_runtime.h` - RTTI hierarchy contracts
  - `runtime/exception_runtime.cpp` - Implementation with loop invariants

- **Annotation Types:**
  - Function contracts (`requires`, `ensures`, `assigns`)
  - Predicates (`valid_exception_frame`, `valid_type_info`)
  - Loop invariants, assigns, variants

- **Quality:** 100% syntax valid, manually written, production-ready

### 2. Validation Infrastructure Status

**✅ Comprehensive Suite Implemented (Stories #186-#191)**

| Validation Type | Status | Coverage | Script |
|-----------------|--------|----------|--------|
| ACSL Syntax | ✅ Complete | 100% (3/3 files) | `verify_acsl.sh` |
| WP Verification | ✅ Complete | 65.7% (23/35 obligations) | `verify_exception_runtime_wp.sh` |
| Value Analysis | ✅ Complete | Clean (no alarms) | `run_all_verifications.sh` |
| Certificates | ✅ Complete | Auto-generated | `run_all_verifications.sh` |

**Key Result:** 65.7% WP proof coverage is industry-standard for exception handling (longjmp limitations expected).

### 3. Validation Gaps Identified

**🔴 Gap 1: No Transpiler ACSL Generation**
- **Issue:** Documentation references `--generate-acsl` flag (3+ locations in SAFETY_CRITICAL_GUIDE.md)
- **Reality:** No ACSL generator found in `src/` directory
- **Impact:** Users cannot automatically annotate transpiled C code for verification
- **Scope:** Annotations exist for runtime library only, not transpiler output

**🟡 Gap 2: CI/CD Integration Missing**
- **Issue:** Verification scripts not integrated in CI/CD pipeline
- **Impact:** Verification can regress without detection
- **Solution:** Add GitHub Actions workflow (syntax validation on PR, WP on nightly builds)

**🟡 Gap 3: Documentation Inconsistency**
- **Issue:** Documented capability does not match implementation
- **Impact:** User confusion, incorrect expectations
- **Solution:** Update docs to clarify ACSL scope (runtime library vs. future transpiler generation)

### 4. Frama-C Integration Requirements

**✅ Successfully Integrated**
- **Version:** Frama-C 31.0 (Gallium) installed and working
- **Provers:** Alt-Ergo (default), Z3 (optional)
- **CLI Patterns:** Proven syntax validation, WP verification, value analysis
- **C++ Compatibility:** Handled via `-U__cplusplus -x c -std=gnu11` flags

**Dependencies:**
- Frama-C 31.0+
- Alt-Ergo 2.6.2+
- Z3 4.8+ (optional)
- Bash shell for scripts

### 5. ACSL Standard Compliance

**✅ Fully Compliant**
- **Version:** ACSL 1.22+ (compatible with Frama-C 31.0)
- **Annotation Structure:** Standard `/*@ ... */` format
- **Clause Types:** All standard clauses used correctly (requires, ensures, assigns, loop invariant, loop assigns, loop variant)
- **Logic Constructs:** Proper use of `\valid`, `\valid_read`, `\null`, `\result`, `\false`, `\nothing`

---

## Decisions Needed

None. Research provides input for planning phase (Epic #16 or future work on transpiler ACSL generation).

---

## Blockers

**None for Current Scope (Runtime Library)**
- Runtime library ACSL validation is complete and working
- No blockers for maintaining current verification suite

**For Future Work (Transpiler ACSL Generation):**
1. **Design Decision:** Automatic ACSL generation strategy
   - Generate annotations during transpilation? (inline in C code)
   - Separate annotation files? (.acsl companion files)
   - On-demand generation? (CLI flag like `--generate-acsl`)

2. **Technical Dependency:** AST analysis for contract extraction
   - C++ preconditions → ACSL `requires`
   - C++ postconditions → ACSL `ensures`
   - C++ invariants → ACSL loop invariants

3. **External Dependency:** Frama-C installation
   - Required for validation
   - Not all users may have Frama-C installed
   - Consider Frama-C as optional dependency vs. required

---

## Recommendations

### High Priority
1. **Maintain Runtime Validation:** Continue running verification suite in development
2. **Fix Documentation:** Update SAFETY_CRITICAL_GUIDE.md to clarify ACSL scope
3. **Integrate in CI/CD:** Add GitHub Actions workflow for automated verification

### Medium Priority
4. **Add Semantic Checks:** Explicit validation of ACSL clause references and scope
5. **Document Gap:** Create Epic for transpiler ACSL generation (future work)

### Low Priority
6. **Explore Custom Predicates:** Transpiler-specific ACSL predicates for vtables, exception frames
7. **Optimize WP Coverage:** Investigate alternative proof strategies for >65.7% coverage

---

## Next Step

**Create planning document:** `013-acsl-validation-plan/013-acsl-validation-plan.md`

**Planning Topics:**
1. Documentation update plan (fix `--generate-acsl` references)
2. CI/CD integration plan (GitHub Actions workflow)
3. Future epic scope (automatic ACSL generation for transpiler output)

---

**Research Complete**
**Status:** ✅ All objectives met
**Confidence:** High (code reviewed, documentation verified, official specs consulted)
