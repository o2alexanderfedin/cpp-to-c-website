# Hook Context Detection Research

**Claude Code PreToolUse hooks can reliably detect execution context by parsing the session transcript for active skill names, using the existing production-tested approach2-transcript-based.sh pattern with a whitelist of skills that should enforce blocking - this solution requires no environment variables or process tree analysis, only passing $transcript_path to the validator and checking if the current skill is in the enforcement list.**

## Version
v1.0 - Initial research completed December 19, 2025

## Key Findings

- **Environment variables do NOT provide context detection** - Only CLAUDE_CODE_ENTRYPOINT and CLAUDECODE are set, with no skill or command context markers
- **Process tree analysis is NOT reliable** - Parent process is always the "claude" binary with no skill differentiation in process arguments
- **Transcript parsing IS the solution** - Session JSONL files contain "skill" field when skills are active, enabling reliable context detection via grep/sed
- **Production-tested pattern exists** - The approach2-transcript-based.sh validator already implements this pattern with 14/14 tests passing and ~18ms overhead
- **Whitelist approach enables gradual rollout** - Define ENFORCED_SKILLS array, check active skill against it, bypass blocking when not in list
- **Hook configuration passes transcript_path** - Simply update settings.json command to include \"$transcript_path\" parameter
- **Fail-safe design prevents blocking legitimate work** - If transcript parsing fails, hook approves all commands (permissive default)
- **No skill modification required** - Unlike description markers (approach 3), transcript-based detection needs no changes to skill files

## Implementation Summary

**Minimal Changes Required:**

1. **Update hook configuration** (1 line change in ~/.claude/settings.json):
   ```json
   "command": "~/.claude/hooks/validators/approach1-auto-approve.sh \"$tool_input.command\" \"$transcript_path\""
   ```

2. **Add to validator script** (≈30 lines in approach1-auto-approve.sh):
   ```bash
   TRANSCRIPT_PATH="${2:-}"
   ENFORCED_SKILLS=("execute-user-story" "execute-epic" "execute-next-story")
   ACTIVE_SKILL=$(tail -n 500 "$TRANSCRIPT_PATH" | grep -o '"skill"[[:space:]]*:[[:space:]]*"[^"]*"' | tail -1 | sed 's/.*"\([^"]*\)".*/\1/')
   # Check whitelist, early return if not enforced
   ```

3. **Test incrementally** - Start with one skill in whitelist, verify detection, expand gradually

**Result:** gh commands allowed in normal workflow, blocked only in whitelisted skills.

## Decisions Needed

**User must decide:**

1. Which skills should be in the ENFORCED_SKILLS whitelist?
   - Identified candidates: execute-user-story, execute-epic, execute-next-story, suggest-next-story, epic-to-user-stories
   - User may have additional custom skills to include

2. Should `gh workflow run` be allowed for CI/CD deployment?
   - Currently blocked as work item operation
   - Could be added to is_allowed_gh_operation() administrative operations
   - User requested this be allowed in original problem statement

3. Gradual rollout vs. all-at-once?
   - Start with single skill and expand (safer, easier to debug)
   - Enable all skills immediately (faster deployment, higher risk)

## Blockers

None - All required tools and capabilities are available:
- Transcript parsing uses standard UNIX tools (tail, grep, sed)
- Hook configuration format is documented and stable
- Working reference implementation exists (approach2)
- No external dependencies or API changes needed

## Next Step

**Implement the transcript-based detection in approach1-auto-approve.sh following the detailed implementation guide in hook-context-detection-research.md:**

1. Backup current validator
2. Update ~/.claude/settings.json to pass $transcript_path
3. Add ENFORCED_SKILLS whitelist and transcript parsing logic to validator
4. Test with single skill in whitelist
5. Verify detection via debug log
6. Expand whitelist incrementally

**Estimated effort:** 30 minutes for implementation + testing with single skill, then gradual rollout.
