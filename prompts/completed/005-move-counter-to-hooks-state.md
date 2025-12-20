<objective>
Refactor the counter-based hook context detection system to store counter files in `~/.claude/hooks/state/` instead of alongside transcript files in the transcripts directory.

**Purpose**: Keep the transcripts directory clean by separating session data (transcripts) from hook state (counters). This improves organization and makes counter files easier to locate for debugging.

**End Goal**: Counter files stored in a dedicated state directory with session identification via `$PPID` instead of transcript path derivation.
</objective>

<context>
**Current Implementation**:
- Counter files currently stored as: `{transcript_path%.jsonl}.skill-enforcement-depth`
- Example: `~/.claude/projects/-Users-...-website/ee2e8b38-e6c0-471b-a1e2-67e69e60198b.skill-enforcement-depth`
- Location derived from `$transcript_path` parameter passed to hooks

**Files to Modify**:
@~/.claude/hooks/SessionStart/reset-skill-counter.sh
@~/.claude/hooks/PreToolUse/skill-enforcement-start.sh
@~/.claude/hooks/PostToolUse/skill-enforcement-end.sh
@~/.claude/hooks/validators/approach1-auto-approve.sh

**Reference Documentation**:
@.prompts/002-hook-counter-implementation-do/SUMMARY.md - Current implementation details
@~/.claude/hooks/validators/README.md - Hook system documentation

**User Requirements**:
- Move counter files to: `~/.claude/hooks/state/`
- Use `$PPID` (parent process ID) for session uniqueness
- Maintain all existing functionality (multi-instance safety, crash recovery, etc.)
</context>

<requirements>
**Functional Requirements**:
1. Create new directory: `~/.claude/hooks/state/` (if it doesn't exist)
2. Change counter file naming from transcript-based to PPID-based:
   - Old: `{transcript_path%.jsonl}.skill-enforcement-depth`
   - New: `~/.claude/hooks/state/counter-{PPID}.depth`
3. Update all 4 hook files to use new counter file path
4. Preserve all existing functionality:
   - SessionStart resets counter to 0
   - PreToolUse increments for enforced skills
   - PostToolUse decrements with floor at 0
   - Bash validator checks counter for early return
   - Multi-instance safety (each Claude instance has unique $PPID)
   - Crash recovery (SessionStart resets counter each session)

**Quality Requirements**:
- No breaking changes to hook behavior
- Maintain backward compatibility during transition (old counter files can be ignored/cleaned up manually)
- Debug logging should show new counter file path
- All error handling preserved (missing file → default to 0)

**Verification Requirements**:
- Test that counter files appear in `~/.claude/hooks/state/`
- Test that `$PPID` provides unique identification across multiple Claude instances
- Verify SessionStart, PreToolUse, PostToolUse, and Bash validator all use consistent path
</requirements>

<implementation>
**Session Identification Strategy**:
```bash
# Use parent process ID for uniqueness
SESSION_ID="$PPID"
COUNTER_FILE="$HOME/.claude/hooks/state/counter-${SESSION_ID}.depth"
```

**Why $PPID works**:
- Each Claude Code instance runs as a separate process with unique parent PID
- Multiple Claude windows = different $PPID values = isolated counters
- Persists for session lifetime (doesn't change during session)
- No need for transcript path parsing

**Directory Creation** (in SessionStart hook):
```bash
# Ensure state directory exists
mkdir -p "$HOME/.claude/hooks/state"
```

**Changes Per File**:

1. **SessionStart/reset-skill-counter.sh**:
   - Remove transcript_path parameter usage
   - Add `SESSION_ID="$PPID"`
   - Add `mkdir -p ~/.claude/hooks/state`
   - Update COUNTER_FILE path to new location
   - Preserve all debug logging logic

2. **PreToolUse/skill-enforcement-start.sh**:
   - Remove transcript_path parameter usage
   - Add `SESSION_ID="$PPID"`
   - Update COUNTER_FILE path to new location
   - Preserve increment logic and debug logging

3. **PostToolUse/skill-enforcement-end.sh**:
   - Remove transcript_path parameter usage
   - Add `SESSION_ID="$PPID"`
   - Update COUNTER_FILE path to new location
   - Preserve decrement logic with floor at 0

4. **validators/approach1-auto-approve.sh**:
   - Remove second parameter (transcript_path) extraction
   - Add `SESSION_ID="$PPID"`
   - Update COUNTER_FILE path to new location
   - Preserve early return logic when depth=0
   - Keep all existing blocking rules

**What NOT to change**:
- ❌ Don't modify settings.json hook configurations (parameters still work, just unused)
- ❌ Don't change ENFORCED_SKILLS whitelist
- ❌ Don't change blocking logic or allowed operations
- ❌ Don't change counter increment/decrement behavior
- ❌ Don't remove debug logging functionality

**Why this approach**:
- Cleaner separation: session data (transcripts) vs hook state (counters)
- Easier debugging: all counter files in one known location
- Simpler path logic: no transcript path parsing needed
- Same guarantees: multi-instance safety via unique $PPID per instance
</implementation>

<output>
Modify existing files (create backups first):

1. `~/.claude/hooks/SessionStart/reset-skill-counter.sh`
   - Backup: `reset-skill-counter.sh.transcript-based.bak`
   - Changes: Use $PPID, create state dir, new counter path

2. `~/.claude/hooks/PreToolUse/skill-enforcement-start.sh`
   - Backup: `skill-enforcement-start.sh.transcript-based.bak`
   - Changes: Use $PPID, new counter path

3. `~/.claude/hooks/PostToolUse/skill-enforcement-end.sh`
   - Backup: `skill-enforcement-end.sh.transcript-based.bak`
   - Changes: Use $PPID, new counter path

4. `~/.claude/hooks/validators/approach1-auto-approve.sh`
   - Backup: `approach1-auto-approve.sh.v3.0.bak` (already has .bak from v2.1)
   - Changes: Use $PPID, new counter path
   - Update version to v3.1

Update documentation:

5. `~/.claude/hooks/validators/README.md`
   - Update "Counter File Location" section
   - Document new path: `~/.claude/hooks/state/counter-{PPID}.depth`
   - Update architecture diagram
   - Add cleanup instructions for old counter files
   - Update version to v3.1
</output>

<verification>
Before declaring complete, verify:

1. **File Modifications**:
   - [ ] All 4 hook files updated with new counter path logic
   - [ ] All backups created successfully
   - [ ] Version updated to v3.1 in approach1-auto-approve.sh
   - [ ] README.md updated with new architecture

2. **Functionality Testing**:
   - [ ] Start new Claude session → SessionStart creates `~/.claude/hooks/state/` directory
   - [ ] Check counter file exists: `~/.claude/hooks/state/counter-{PPID}.depth`
   - [ ] Counter initialized to 0
   - [ ] Normal chat mode: `gh workflow run` approved (depth=0)
   - [ ] Start enforced skill → counter increments
   - [ ] During skill: work item ops blocked, admin ops allowed
   - [ ] Skill completes → counter decrements to 0

3. **Multi-Instance Testing**:
   - [ ] Open two Claude sessions in different terminals
   - [ ] Each session has different $PPID → different counter files
   - [ ] Start skill in session 1 → only session 1 counter increments
   - [ ] Run gh command in session 2 → approved (session 2 counter still 0)

4. **Path Verification**:
   - [ ] All 4 hooks use identical counter file path derivation
   - [ ] Counter files appear in `~/.claude/hooks/state/` not transcripts dir
   - [ ] Debug logs (if enabled) show new counter file paths

5. **Edge Cases**:
   - [ ] Missing state directory → automatically created
   - [ ] Missing counter file → defaults to 0 (approve)
   - [ ] Non-numeric counter → sanitized to 0

6. **Cleanup** (optional):
   - [ ] Document how to clean up old transcript-based counter files
   - [ ] Consider adding cleanup script to remove `*.skill-enforcement-depth` from transcript dirs
</verification>

<success_criteria>
- ✓ All 4 hook files modified with backups created
- ✓ Counter files now stored in `~/.claude/hooks/state/`
- ✓ Session identification via $PPID (no transcript path dependency)
- ✓ All existing functionality preserved (increment/decrement/blocking/etc.)
- ✓ Multi-instance safety verified (unique $PPID per instance)
- ✓ Crash recovery still works (SessionStart resets counter)
- ✓ Documentation updated with new architecture
- ✓ All 12 original integration tests still pass with new location
- ✓ Cleaner transcript directory (no .skill-enforcement-depth files)
</success_criteria>
