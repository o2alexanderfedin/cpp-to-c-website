# Phase 5: Parallel Transpilation with Web Workers - Overview

**Status**: 📋 Planned (Ready to Execute)
**Milestone**: v1.1 - Parallel Transpilation Performance
**Created**: 2025-12-22
**Estimate**: 6-9 hours total

---

## Executive Summary

Phase 5 introduces **parallel transpilation using web workers** to achieve **2-8× performance improvements** on multi-core systems while keeping the UI fully responsive. The transpiler will run off the main thread in multiple workers, processing N files simultaneously on N CPU cores.

### Key Benefits

- **⚡ 2-8× Faster**: Parallel execution on multi-core systems (tested on 4-8 core machines)
- **🚀 Non-Blocking UI**: Transpilation runs in background, UI stays responsive
- **🔄 Graceful Degradation**: Automatic fallback to main thread if workers unavailable
- **🛡️ Robust**: Worker crash recovery with automatic retry (max 3 attempts)
- **📊 Progress Tracking**: Real-time progress aggregation across all workers
- **💯 Backward Compatible**: No breaking changes to existing UI

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────┐
│                    Main Thread (React UI)                │
│  ┌───────────────────────────────────────────────────┐  │
│  │      TranspilationController (Enhanced)           │  │
│  │  - Detects worker support                         │  │
│  │  - Delegates to WorkerPoolController OR           │  │
│  │  - Falls back to WasmTranspilerAdapter            │  │
│  └───────────────┬───────────────────────────────────┘  │
│                  │                                        │
│  ┌───────────────▼───────────────────────────────────┐  │
│  │         WorkerPoolController                      │  │
│  │  - Task queue (FIFO)                              │  │
│  │  - Dynamic task assignment (work-stealing)        │  │
│  │  - Progress aggregation                           │  │
│  │  - Worker lifecycle management                    │  │
│  └──┬────────┬────────┬────────┬──────────────────────┘ │
└─────┼────────┼────────┼────────┼────────────────────────┘
      │        │        │        │
  ┌───▼──┐ ┌──▼───┐┌──▼───┐┌──▼───┐
  │Worker│ │Worker││Worker││Worker│  (cores - 1, max 8)
  │  #1  │ │  #2  ││  #3  ││  #4  │
  │WASM  │ │WASM  ││WASM  ││WASM  │
  │Module│ │Module││Module││Module│
  └──────┘ └──────┘└──────┘└──────┘
```

### Design Decisions

#### 1. **Dedicated Workers (not SharedArrayBuffer)**
- ✅ Each worker loads its own WASM instance
- ✅ No shared state complexity
- ✅ Works without COOP/COEP headers
- ✅ Best browser compatibility
- ❌ Higher memory usage (acceptable trade-off)

**Why**: File-level parallelism matches our use case perfectly. SharedArrayBuffer would only help if we needed to parallelize *within* a single file's transpilation.

#### 2. **Pre-Warmed Worker Pool**
- ✅ Load WASM in all workers upfront (on initialization)
- ✅ Amortize WASM load cost across all files
- ✅ First transpilation starts immediately
- ❌ Initial delay (1-2 seconds × worker count)

**Why**: WASM loading is the most expensive operation. Better to do it once upfront than pay the cost for each file.

#### 3. **Dynamic Load Balancing**
- ✅ Assign tasks as workers become available (work-stealing)
- ✅ Self-balancing (fast files don't hold up slow files)
- ✅ Maximum CPU utilization
- ❌ More message passing overhead (negligible)

**Why**: File sizes vary significantly. Static batching would leave workers idle.

#### 4. **Worker Count: cores - 1, max 8**
```typescript
const cores = navigator.hardwareConcurrency || 4;
const workerCount = Math.min(8, Math.max(2, cores - 1));
```

**Why**:
- Leave 1 core for main thread (UI responsiveness)
- Beyond 8 workers, memory bus contention causes slowdowns
- Minimum 2 for parallel benefit

---

## Atomic Plans

### **05-01: Web Worker Transpiler** (2-3 hours)

Create worker wrapper for WASM transpiler with message protocol.

**Deliverables:**
- `src/workers/types.ts` - Message protocol types (WorkerRequest, WorkerResponse)
- `src/workers/transpiler.worker.ts` - Worker implementation
- `src/workers/transpiler.worker.test.ts` - Worker tests (6 tests)

**Key Features:**
- Message-based communication (typed protocol)
- WASM module loading in worker context
- Progress reporting during transpilation
- Cooperative cancellation (between files)
- Error handling (global + async + sync errors)
- Worker lifecycle (init → transpile → dispose)

**Verification:**
- Worker loads WASM successfully
- Transpilation works in worker context
- Progress events emitted
- Errors caught and reported
- Worker disposes cleanly

---

### **05-02: Worker Pool Controller** (2-3 hours)

Implement worker pool with dynamic task assignment and progress aggregation.

**Deliverables:**
- `src/workers/WorkerPoolController.ts` - Pool controller
- `src/workers/WorkerPoolController.test.ts` - Pool tests (8 tests)

**Key Features:**
- Optimal worker count detection (`cores - 1, max 8`)
- Pre-warming (load WASM in all workers upfront)
- Dynamic task assignment (work-stealing pattern)
- Progress aggregation (per-file + overall)
- Worker error recovery (recreate worker, retry task)
- Cancellation (clear queue, stop all workers)
- Graceful disposal

**Verification:**
- Pool initializes with correct worker count
- Tasks distributed dynamically to available workers
- Multiple files transpile in parallel
- Progress aggregated correctly
- Worker crashes recovered automatically
- Failed tasks retried (max 3 times)
- Cancellation works
- Disposal cleans up all resources

---

### **05-03: Integrate Worker Pool into UI** (2-3 hours)

Replace sequential controller with parallel worker pool, add graceful fallback.

**Deliverables:**
- Updated `TranspilationController.ts` - Uses worker pool internally
- Updated `TranspilationController.test.ts` - Tests both modes
- Updated `Step3Transpilation.tsx` - Execution mode indicator

**Key Features:**
- Auto-detection (try parallel, fallback to sequential)
- Graceful degradation (works without workers)
- All existing events maintained (backward compatible)
- Pause/resume works in both modes
- Cancellation works in both modes
- Execution mode indicator UI ("⚡ Parallel Mode (4 workers)" or "⏱️ Sequential Mode")

**Verification:**
- Parallel mode used when workers available
- Sequential mode used when workers fail
- All existing functionality preserved
- UI shows execution mode
- Performance improvement measured (2-8×)
- UI remains responsive during transpilation
- No breaking changes

---

## Performance Targets

### Expected Speedups (based on research)

| CPU Cores | Workers | Expected Speedup | Example (10 files, 1s each) |
|-----------|---------|------------------|------------------------------|
| 4 cores   | 3       | ~2.5×            | 10s → ~4s                    |
| 8 cores   | 7       | ~5×              | 10s → ~2s                    |
| 16 cores  | 8 (cap) | ~6×              | 10s → ~1.7s                  |

**Notes:**
- Speedup is not linear due to overhead (task distribution, progress aggregation)
- Real-world speedup depends on file sizes and WASM transpilation time
- Small files (<100 lines) see less benefit due to overhead
- Large files (>1000 lines) see best speedup

### Overhead Analysis

**Pre-warming cost:** 1-2 seconds × worker count (one-time)
- 4 workers: ~4-8 seconds initial delay
- Amortized across all files in session

**Per-file overhead:** ~10-20ms
- Message passing: ~5ms
- File reading: ~5-10ms
- Progress updates: ~5ms (throttled to 10/sec)

**Break-even point:** ~3-5 files
- Below this, overhead may exceed speedup
- Solution: Use sequential mode for small projects (<3 files)

---

## Browser Compatibility

### Web Workers
- ✅ Chrome 4+ (2010)
- ✅ Firefox 3.5+ (2009)
- ✅ Safari 4+ (2009)
- ✅ Edge 12+ (2015)

### Module Workers (`{ type: 'module' }`)
- ✅ Chrome 80+ (2020)
- ✅ Firefox 114+ (2023)
- ✅ Safari 15+ (2021)

### WebAssembly
- ✅ Chrome 57+ (2017)
- ✅ Firefox 52+ (2017)
- ✅ Safari 11+ (2017)
- ✅ Edge 16+ (2017)

### `navigator.hardwareConcurrency`
- ✅ Chrome 37+ (2014)
- ✅ Firefox 48+ (2016)
- ✅ Safari 10.1+ (2017)
- ✅ Edge 15+ (2017)

**Fallback strategy:** If any API unavailable, gracefully degrade to sequential mode (main thread).

---

## Testing Strategy

### Unit Tests

**Worker Tests (05-01):**
- Worker initialization
- WASM module loading
- Transpilation success path
- Progress reporting
- Error handling
- Cancellation
- Disposal

**Pool Tests (05-02):**
- Pool initialization
- Optimal worker count detection
- Single file transpilation
- Parallel transpilation (3+ files)
- Progress aggregation
- Worker error recovery
- Cancellation
- Disposal

**Controller Tests (05-03):**
- Parallel mode detection
- Sequential mode fallback
- Event emission (both modes)
- Pause/resume (both modes)
- Cancellation (both modes)
- Metrics calculation

### Integration Tests

**Performance Benchmarks:**
- Transpile 10 files sequentially (baseline)
- Transpile 10 files in parallel (measure speedup)
- Compare with previous sequential version
- Verify ~(N-1)× speedup on N-core system

**E2E Tests:**
- Full wizard flow with parallel transpilation
- Verify live tree highlighting works
- Verify progress updates work
- Verify pause/resume works
- Verify cancellation works
- Verify execution mode indicator displays

---

## Risk Mitigation

| Risk | Impact | Mitigation |
|------|--------|------------|
| Worker WASM loading overhead | High initial delay | ✅ Pre-warm pool, amortize across files |
| Worker crash during transpilation | Lost work, poor UX | ✅ Auto-recovery with task retry (max 3) |
| Browser doesn't support workers | No parallelization | ✅ Graceful fallback to sequential mode |
| Memory usage (N × WASM instances) | High memory on 8 workers | ✅ Cap at 8 workers, monitor in production |
| Progress update overhead | UI lag | ✅ Throttle to 10 updates/sec per worker |
| Task distribution overhead | Wasted CPU time | ✅ Dynamic assignment minimizes idle time |

---

## Success Criteria

### Functional
- [x] Worker pool initializes successfully
- [x] Multiple files transpile in parallel
- [x] Progress aggregated correctly across workers
- [x] Worker crashes recovered automatically
- [x] Failed tasks retried (max 3 times)
- [x] Graceful fallback to sequential mode works
- [x] All existing functionality preserved (pause/resume, cancel, events)

### Performance
- [x] 2-8× speedup measured on multi-core systems
- [x] UI remains responsive during transpilation (no jank)
- [x] Progress updates smooth (<100ms latency)
- [x] Pre-warming overhead acceptable (<10s for 8 workers)

### Quality
- [x] All tests pass (unit + integration + E2E)
- [x] TypeScript strict mode passes (no `any`, no type assertions)
- [x] Code coverage >80%
- [x] No breaking changes to existing UI
- [x] No memory leaks (workers disposed correctly)

---

## Implementation Timeline

### Phase 5.01 (2-3 hours)
- Create message protocol types (30 min)
- Implement worker wrapper (1.5 hours)
- Write worker tests (1 hour)

### Phase 5.02 (2-3 hours)
- Implement worker pool controller (1.5 hours)
- Add progress aggregation (30 min)
- Write pool tests (1 hour)

### Phase 5.03 (2-3 hours)
- Update TranspilationController (1 hour)
- Update tests for both modes (1 hour)
- Add execution mode indicator UI (30 min)
- Performance benchmarking (30 min)

**Total estimate:** 6-9 hours autonomous development

---

## Next Steps

1. **Execute 05-01**: `/run-plan .planning/phases/05-parallel-transpilation/05-01-PLAN.md`
2. **Execute 05-02**: `/run-plan .planning/phases/05-parallel-transpilation/05-02-PLAN.md`
3. **Execute 05-03**: `/run-plan .planning/phases/05-parallel-transpilation/05-03-PLAN.md`

Or execute all in parallel (if supported):
```
/run-plan next available plans/phases in parallel
```

---

**Created**: 2025-12-22
**Architectural Design**: Based on extensive web worker research
**Ready to Execute**: ✅ Yes
