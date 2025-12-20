<objective>
Implement counter-based hook context detection system for Claude Code that enables context-aware blocking of GitHub CLI commands only when invoked from work item execution skills (execute-epic, execute-user-story, etc.), while allowing all gh commands in normal chat usage.

**Purpose**: Solve the false positive problem where transcript-based detection incorrectly blocks gh commands long after a skill has completed. Counter-based tracking provides exact execution state (skill active vs inactive) through increment/decrement on skill start/end.

**Output**: Complete hook system with 4 files created, settings.json updated, crash-safety guaranteed, and comprehensive testing performed.
</objective>

<context>
**Research Foundation**:
@.prompts/001-hook-context-detection-research/hook-context-detection-research.md

**Key Research Findings**:
- Transcript-based approach has false positives (old skill invocations remain in transcript)
- Counter approach provides exact state tracking (0 = inactive, >0 = active)
- SessionStart hook ensures crash recovery (resets counter each session)
- Multi-instance safety guaranteed (counter file derived from unique $TRANSCRIPT_PATH)

**User Requirements from Intake**:
- Full implementation with testing and documentation
- ENFORCED_SKILLS whitelist: execute-epic, execute-user-story, execute-next-story, suggest-next-story, plus all epic/story/task/spike/bug skills
- Allow `gh workflow run` for CI/CD deployment (add to administrative operations)
- Update approach1-auto-approve.sh in-place with backup

**Existing Hook**:
@~/.claude/hooks/validators/approach1-auto-approve.sh (v2.1 - currently blocks without context detection)
</context>

<requirements>
**Functional Requirements**:
1. Create SessionStart hook that initializes counter to 0 at session start
2. Create PreToolUse hook for Skill tool that increments counter when enforced skill starts
3. Create PostToolUse hook for Skill tool that decrements counter when enforced skill ends
4. Update approach1-auto-approve.sh to check counter and bypass all blocking when counter = 0
5. Update ~/.claude/settings.json with all hook configurations
6. Add `gh workflow run` to allowed administrative operations
7. Prevent negative counters (floor at 0)

**Quality Requirements**:
- Atomic file operations (no race conditions)
- Crash-safe (counter stuck → only affects current session, SessionStart resets next session)
- Multi-instance safe (each Claude session has unique counter file)
- Debug logging support (use existing CLAUDE_HOOK_DEBUG_LOG pattern from approach1)
- Portable paths (use ~/ notation, environment variables)

**ENFORCED_SKILLS Whitelist**:
```bash
ENFORCED_SKILLS=(
  "execute-epic"
  "execute-user-story"
  "execute-next-story"
  "suggest-next-story"
  "epic-to-user-stories"
  "prd-to-epics"
)
```

**Constraints**:
- Backup current approach1-auto-approve.sh to approach1-auto-approve.sh.bak before modifying
- Preserve all existing blocking logic in approach1 (only add counter check at the beginning)
- Use existing environment variable patterns (CLAUDE_SKILLS_LIB_DIR, CLAUDE_HOOK_DEBUG_LOG)
- Follow existing hook file structure and conventions from approach1
</requirements>

<implementation>
**Architecture Pattern**:
```
Session Lifecycle:
1. SessionStart: counter = 0 (clean slate)
2. Skill starts: PreToolUse(Skill) → counter++
3. Bash commands: PreToolUse(Bash) → if counter > 0, apply blocking
4. Skill ends: PostToolUse(Skill) → counter--
5. Normal chat: PreToolUse(Bash) → counter = 0, approve all
```

**Counter File Location**:
```bash
# Derive from transcript path for session uniqueness
TRANSCRIPT_PATH="${1:-}"  # or "${2:-}" depending on hook position
COUNTER_FILE="${TRANSCRIPT_PATH%.jsonl}.skill-enforcement-depth"
```

**Critical Implementation Details**:

1. **SessionStart Hook**:
   - Parameter: `$transcript_path` (first parameter)
   - Action: `echo "0" > "$COUNTER_FILE"`
   - Return: `{"decision": "approve"}` (required for SessionStart hooks)

2. **PreToolUse Hook for Skill**:
   - Parameters: `$tool_input.skill` (skill name), `$transcript_path`
   - Check if skill in ENFORCED_SKILLS array
   - If yes: read current count, increment, write back
   - Return: `{"decision": "approve"}` (always approve skill invocation)
   - Debug log: skill name, old count → new count

3. **PostToolUse Hook for Skill**:
   - Parameters: Same as PreToolUse
   - Check if skill in ENFORCED_SKILLS array
   - If yes: read current count, decrement (floor at 0), write back
   - No decision return needed (PostToolUse hooks don't return decisions)
   - Debug log: skill name, old count → new count

4. **Updated approach1-auto-approve.sh**:
   - Add second parameter: `$transcript_path`
   - Derive counter file path at beginning
   - Read counter: `DEPTH=$(cat "$COUNTER_FILE" 2>/dev/null || echo "0")`
   - Early return if depth = 0: `{"decision": "approve", "reason": "Not in enforced skill context (depth=0)"}`
   - Otherwise: continue with existing blocking logic
   - Add `gh workflow run` to `is_allowed_gh_operation()` function

**What to Avoid and WHY**:
- ❌ Using global counter files (not session-unique) → multi-instance collisions
- ❌ Allowing negative counters → state corruption
- ❌ Forgetting to handle missing COUNTER_FILE → use `|| echo "0"` fallback
- ❌ Using flock for single-instance usage → unnecessary complexity, Claude is single-threaded
- ❌ Hardcoded paths → breaks portability

**Integration Points**:
- `~/.claude/settings.json` - Hook configuration
- `~/.claude/hooks/SessionStart/` - New directory for session hooks
- `~/.claude/hooks/PreToolUse/` - Add skill-enforcement-start.sh
- `~/.claude/hooks/PostToolUse/` - New directory + skill-enforcement-end.sh
- `~/.claude/hooks/validators/approach1-auto-approve.sh` - Modify existing (with backup)

**settings.json Structure**:
```json
{
  "hooks": {
    "SessionStart": [
      {
        "type": "command",
        "command": "~/.claude/hooks/SessionStart/reset-skill-counter.sh \"$transcript_path\""
      }
    ],
    "PreToolUse": [
      {
        "matcher": "Skill",
        "hooks": [
          {
            "type": "command",
            "command": "~/.claude/hooks/PreToolUse/skill-enforcement-start.sh \"$tool_input.skill\" \"$transcript_path\""
          }
        ]
      },
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "~/.claude/hooks/validators/approach1-auto-approve.sh \"$tool_input.command\" \"$transcript_path\""
          }
        ]
      }
    ],
    "PostToolUse": [
      {
        "matcher": "Skill",
        "hooks": [
          {
            "type": "command",
            "command": "~/.claude/hooks/PostToolUse/skill-enforcement-end.sh \"$tool_input.skill\" \"$transcript_path\""
          }
        ]
      }
    ]
  }
}
```
</implementation>

<output>
**Create New Files**:
1. `~/.claude/hooks/SessionStart/reset-skill-counter.sh`
   - Executable permissions (chmod +x)
   - Shebang: `#!/bin/bash`
   - Accepts $transcript_path parameter
   - Initializes counter to 0
   - Returns approve decision
   - Debug logging if CLAUDE_HOOK_DEBUG_LOG set

2. `~/.claude/hooks/PreToolUse/skill-enforcement-start.sh`
   - Executable permissions
   - Accepts $tool_input.skill and $transcript_path parameters
   - Increments counter for enforced skills
   - Always approves (returns approve decision)
   - Debug logging

3. `~/.claude/hooks/PostToolUse/skill-enforcement-end.sh`
   - Executable permissions
   - Accepts same parameters as PreToolUse
   - Decrements counter for enforced skills (floor at 0)
   - No decision return (PostToolUse behavior)
   - Debug logging

**Modify Existing Files**:
4. `~/.claude/hooks/validators/approach1-auto-approve.sh`
   - Create backup: `~/.claude/hooks/validators/approach1-auto-approve.sh.bak`
   - Add transcript_path parameter handling
   - Add counter check at beginning with early return if depth=0
   - Add `gh workflow run` to allowed operations
   - Update version to v3.0
   - Preserve all existing logic

5. `~/.claude/settings.json`
   - Backup to `~/.claude/settings.json.bak`
   - Add SessionStart hook configuration
   - Add Skill matcher for PreToolUse
   - Update Bash PreToolUse to pass $transcript_path
   - Add PostToolUse hook configuration
   - Preserve existing settings

**Documentation**:
6. `~/.claude/hooks/validators/README.md`
   - Update to document counter-based approach
   - Add architecture diagram
   - Document crash recovery behavior
   - Add troubleshooting section for counter issues
   - Update version history
</output>

<verification>
**Before Declaring Complete**:

1. **File Creation Verification**:
   - [ ] All 3 new hook files created with correct paths
   - [ ] All hook files have executable permissions (chmod +x)
   - [ ] All hook files have proper shebang (#!/bin/bash)
   - [ ] Backup files created for approach1-auto-approve.sh and settings.json

2. **Logic Verification**:
   - [ ] ENFORCED_SKILLS array matches user requirements
   - [ ] Counter increment/decrement logic prevents negatives
   - [ ] Early return in approach1 when depth=0
   - [ ] `gh workflow run` added to allowed operations
   - [ ] Debug logging present in all hooks

3. **Integration Testing**:
   - [ ] Test 1: Normal chat - `gh workflow run deploy.yml` should APPROVE
   - [ ] Test 2: Start execute-epic → counter should be 1
   - [ ] Test 3: During epic - `gh issue create` should BLOCK
   - [ ] Test 4: During epic - `gh workflow run` should APPROVE (administrative)
   - [ ] Test 5: Epic completes → counter should be 0
   - [ ] Test 6: After epic - `gh issue create` should APPROVE

4. **Crash Recovery Testing**:
   - [ ] Test 7: Start execute-epic, kill Claude mid-execution
   - [ ] Test 8: Start new session → counter should reset to 0
   - [ ] Test 9: Normal gh commands work after recovery

5. **Multi-Instance Testing**:
   - [ ] Test 10: Open two Claude sessions in different directories
   - [ ] Test 11: Start execute-epic in session 1
   - [ ] Test 12: Run gh workflow run in session 2 → should APPROVE (different counter)

6. **Edge Cases**:
   - [ ] Missing counter file → fallback to "0" works
   - [ ] Empty counter file → fallback to "0" works
   - [ ] Non-numeric counter value → sanitize or reset
   - [ ] Nested skills (if applicable) → counter depth tracks correctly

7. **Documentation Verification**:
   - [ ] README.md updated with counter approach
   - [ ] Architecture diagram present
   - [ ] Troubleshooting section added
   - [ ] All file paths use portable notation (~/)

**Testing Script Template**:
```bash
#!/bin/bash
# Save as: test-counter-hooks.sh

echo "=== Counter Hook Integration Tests ==="

# Test 1: Normal chat (counter should be 0)
echo "Test 1: Normal chat context"
# TODO: Verify counter file doesn't exist or = 0

# Test 2: Execute skill
echo "Test 2: Start execute-epic skill"
# TODO: Invoke skill, check counter = 1

# Test 3: Block during skill
echo "Test 3: gh issue create during epic"
# TODO: Attempt gh command, verify blocked

# Test 4: Allow admin ops
echo "Test 4: gh workflow run during epic"
# TODO: Attempt workflow run, verify approved

# Add remaining tests...
```
</verification>

<success_criteria>
- ✓ All 3 new hook files created and executable
- ✓ approach1-auto-approve.sh updated with backup preserved
- ✓ settings.json configured with all hooks
- ✓ ENFORCED_SKILLS whitelist matches user requirements
- ✓ `gh workflow run` added to allowed operations
- ✓ Counter prevents negative values
- ✓ Debug logging functional
- ✓ All 12 integration tests pass
- ✓ Crash recovery verified (counter resets next session)
- ✓ Multi-instance isolation verified (separate counters)
- ✓ README.md updated with architecture and troubleshooting
- ✓ SUMMARY.md created with implementation details and test results
</success_criteria>

<summary_requirements>
Create `.prompts/002-hook-counter-implementation-do/SUMMARY.md` with:

**One-liner**: Counter-based hook context detection implemented with 4 hooks, 12 passing tests, and guaranteed crash-safety through SessionStart reset

**Version**: v1.0 - Initial implementation (2025-12-19)

**Files Created**:
- `~/.claude/hooks/SessionStart/reset-skill-counter.sh` - Initializes counter to 0
- `~/.claude/hooks/PreToolUse/skill-enforcement-start.sh` - Increments on skill start
- `~/.claude/hooks/PostToolUse/skill-enforcement-end.sh` - Decrements on skill end
- `~/.claude/hooks/validators/approach1-auto-approve.sh` (v3.0) - Updated with counter check
- `~/.claude/settings.json` - Configured all hook bindings

**Key Achievements**:
- ✓ No false positives (counter tracks exact skill execution state)
- ✓ Crash-safe (SessionStart resets counter each session)
- ✓ Multi-instance safe (unique counter per session)
- ✓ CI/CD friendly (`gh workflow run` allowed during enforcement)
- ✓ Zero negative counters (floor protection)
- ✓ Comprehensive testing (12 scenarios validated)

**Test Results**: All 12 integration tests passing
- Normal chat: gh commands approved ✓
- During skills: work item ops blocked, admin ops allowed ✓
- Crash recovery: counter resets next session ✓
- Multi-instance: isolated counters verified ✓

**Decisions Needed**: None - implementation complete and tested

**Blockers**: None

**Next Step**: Monitor production usage for edge cases, consider adding metrics/telemetry to track counter depth over time
</summary_requirements>
