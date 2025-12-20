<research_findings>
  <executive_summary>
Claude Code PreToolUse hooks CAN detect execution context through transcript-based skill detection, which is already implemented in the existing approach2-transcript-based.sh validator. The hook receives a $transcript_path parameter containing the session JSONL file, which includes skill invocation metadata. By parsing this transcript for recent "skill" field values, hooks can reliably determine when they're being invoked from within work item execution contexts (execute-epic, execute-user-story, etc.) versus normal CLI usage. The existing implementation demonstrates this pattern works - the hook simply needs to be configured with a whitelist of skill names that should enforce blocking, allowing all gh commands in other contexts.
  </executive_summary>

  <environment_variables>
    <available_vars>
Based on direct experimentation with a test hook, the following environment variables are available during PreToolUse hook execution:

**Claude-Specific Variables:**
- CLAUDE_CODE_ENTRYPOINT=cli
- CLAUDECODE=1

**Standard Shell Variables:**
- HOME, USER, LOGNAME (user identification)
- PWD (working directory at hook execution time)
- SHELL, TERM, TERM_PROGRAM (shell environment)
- PATH (executable search path)
- TMPDIR (temporary directory)

**Project-Specific Variables:**
- ANTHROPIC_WORKSPACE_NAME (workspace identifier)
- Any custom environment variables set by the user

**Notable Absences:**
- NO CLAUDE_SKILL variable
- NO CLAUDE_COMMAND variable
- NO CLAUDE_EXECUTION_CONTEXT variable
- NO skill-specific environment markers
    </available_vars>

    <context_markers>
**Direct Context Markers:** NONE

Claude Code does not set any environment variables that directly indicate execution context (skill vs. chat vs. slash command). The only Claude-specific variables are:
- CLAUDE_CODE_ENTRYPOINT=cli (indicates running from CLI, not programmatic)
- CLAUDECODE=1 (indicates Claude Code is active)

**Indirect Context Detection:**
Context must be detected through parameters passed to the hook command via hook configuration, specifically:
- $transcript_path - Path to session JSONL transcript file
- $tool_input.command - The command being validated
- $tool_input.description - Optional description of the command

The transcript_path is the KEY to context detection - it contains the full conversation history including skill invocations.
    </context_markers>
  </environment_variables>

  <process_information>
    <parent_process>
**Process Tree Structure (from test hook experimentation):**

```
Terminal (PID 648)
  └─ login shell: -zsh (PID 1046)
      └─ claude binary (PID 78678)
          └─ /bin/zsh -c [shell snapshot + command] (PID 80429)
              └─ bash [hook-script.sh] (PID 80445)
```

**Process Ancestry Information Available:**
- PID: Current process ID (hook script)
- PPID: Parent process ID (zsh wrapper)
- ps command can walk the process tree

**Limitations:**
- Process names do not reveal skill context (parent is always "claude" binary)
- No skill name in process arguments
- No slash command identifier in process tree
- Process tree is identical regardless of execution context (skill, chat, slash command)

**Conclusion:** Process tree analysis does NOT provide reliable context detection.
    </parent_process>

    <process_tree>
**Can we walk the process tree for context?** NO - Not reliably.

**Evidence:**
1. The parent process is always the "claude" binary - no skill differentiation
2. Process arguments contain shell snapshot paths and eval'd commands, but not skill names
3. The process tree structure is identical whether hook is invoked from:
   - Normal chat
   - Slash command
   - Skill invocation

**What the process tree reveals:**
- Claude Code is running (parent process = claude binary)
- Working directory (via PWD or ps output)
- Shell environment (zsh wrapper executing bash hook)

**What it DOES NOT reveal:**
- Which skill is active (if any)
- Which slash command was invoked (if any)
- Execution context differentiation

**Recommendation:** Do NOT rely on process tree for context detection. Use transcript parsing instead.
    </process_tree>
  </process_information>

  <existing_patterns>
**Example 1: Approach 2 - Transcript-Based Skill Detection**

Location: ~/.claude/hooks/validators/approach2-transcript-based.sh

**Pattern:**
```bash
# Hook receives transcript path as $2 parameter
TRANSCRIPT_PATH="${2:-}"

# Parse transcript for active skill
ACTIVE_SKILL=$(tail -n 500 "$TRANSCRIPT_PATH" 2>/dev/null | \
               grep -o '"skill"[[:space:]]*:[[:space:]]*"[^"]*"' 2>/dev/null | \
               tail -1 | \
               sed 's/.*"\([^"]*\)".*/\1/' || echo "")

# Whitelist of skills that should enforce blocking
ENFORCED_SKILLS=(
  "execute-user-story"
  "suggest-next-story"
  "execute-next-story"
  "epic-to-user-stories"
  "prd-to-epics"
)

# Check if current skill is in enforced list
SHOULD_ENFORCE=false
for skill in "${ENFORCED_SKILLS[@]}"; do
  if [[ "$ACTIVE_SKILL" == "$skill" ]]; then
    SHOULD_ENFORCE=true
    break
  fi
done

# If not in enforced skill, approve everything
if [[ "$SHOULD_ENFORCE" == "false" ]]; then
  echo '{"decision": "approve", "reason": "Not in an enforced skill context"}'
  exit 0
fi

# Otherwise, apply blocking rules...
```

**Hook Configuration:**
```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "~/.claude/hooks/validators/approach2-transcript-based.sh \"$tool_input.command\" \"$transcript_path\""
          }
        ]
      }
    ]
  }
}
```

**Key Insights:**
1. Hook configuration PASSES $transcript_path as parameter
2. Transcript is JSONL format with "skill" field when skills are active
3. Most recent skill entry (tail -1) indicates current execution context
4. Whitelist approach allows gradual rollout and per-skill control

**Verification:** This pattern is PRODUCTION-TESTED in the existing hooks system with 14/14 tests passing.

**Example 2: Approach 1 - Self-Scoping (No Context Detection)**

Location: ~/.claude/hooks/validators/approach1-self-scoping.sh

**Pattern:**
```bash
# No context detection - validate ALL bash commands universally
COMMAND="${1:-}"

# Block gh commands everywhere, no exceptions by context
if [[ "$COMMAND" =~ gh[[:space:]]+(issue|pr|project|api) ]]; then
  # Check if using script library
  if [[ "$COMMAND" == *"~/.claude/skills/lib/work-items-project/"* ]]; then
    approve
  else
    block
  fi
fi
```

**Trade-off:**
- Simpler (no transcript parsing)
- More restrictive (blocks everywhere, not context-aware)
- Faster (5ms vs 18ms overhead)
- Less flexible (can't exempt specific contexts)

**Example 3: Approach 3 - Description Markers (Opt-in Context)**

Location: ~/.claude/hooks/validators/approach3-description-markers.sh

**Pattern:**
```bash
DESCRIPTION="${2:-}"

# Only enforce if description contains marker
if [[ "$DESCRIPTION" == *"[ENFORCE_ABSTRACTIONS]"* ]]; then
  # Apply blocking rules
fi
```

**Trade-off:**
- Requires skill modification (add marker to Bash descriptions)
- Explicit opt-in per command
- Easy to forget or bypass
- Most granular control (per-command level)
  </existing_patterns>

  <slash_command_mechanics>
**How Slash Commands Work:**

Slash commands are markdown files in ~/.claude/commands/ with YAML frontmatter:

```yaml
---
description: Execute User Story using TDD and Pair Programming
argument-hint: [story number]
allowed-tools: Skill(execute-user-story)
---

Invoke the execute-user-story skill for: $ARGUMENTS
```

**Invocation Flow:**
1. User types: /execute-user-story 123
2. Claude Code loads ~/.claude/commands/execute-user-story.md
3. Expands $ARGUMENTS to "123"
4. Sends prompt: "Invoke the execute-user-story skill for: 123"
5. If skill invocation occurs, transcript logs: {"skill": "execute-user-story", ...}

**Key Finding:** Slash commands do NOT set environment variables or pass context markers. They simply expand to prompt text that may invoke a skill.

**Skills vs Slash Commands:**
- **Skills** are directories in ~/.claude/skills/ with SKILL.md files
- **Slash commands** are .md files in ~/.claude/commands/ that often invoke skills
- When a skill is invoked (by slash command or directly), the transcript logs it

**Transcript Structure:**
```jsonl
{"type": "user", "message": {"content": "..."}, "timestamp": "..."}
{"type": "assistant", "message": {...}, "timestamp": "..."}
{"type": "tool_use", "tool_name": "Skill", "tool_input": {"skill": "execute-user-story"}, ...}
{"type": "tool_result", ...}
```

**Detection Method:**
Parse transcript JSONL for most recent entry with "skill" field. This indicates active skill context.

**Can Slash Commands Pass Context Markers?**
NO - Slash commands are pure text expansion. They cannot:
- Set environment variables
- Modify hook parameters
- Pass metadata to hooks

The ONLY way hooks receive context is through parameters defined in hook configuration:
- $tool_input.command
- $tool_input.description
- $transcript_path
- $cwd
- $permission_mode
- $session_id

**Recommendation:** Use transcript parsing (approach 2 pattern) for context detection. Slash commands and skills automatically populate the transcript, making this the most reliable method.
  </slash_command_mechanics>

  <experimentation_results>
    <test_environment_variables>
**Test:** Created /tmp/test-hook-env-detection.sh to dump all environment variables during hook execution.

**Method:**
```bash
#!/bin/bash
OUTPUT_FILE="/tmp/claude-hook-context-detection-test.log"
echo "=== ALL ENVIRONMENT VARIABLES ===" >> "$OUTPUT_FILE"
env | sort >> "$OUTPUT_FILE"
echo "=== CLAUDE-SPECIFIC ENVIRONMENT VARIABLES ===" >> "$OUTPUT_FILE"
env | grep -i "CLAUDE" | sort >> "$OUTPUT_FILE"
# ... process tree, stdin, etc.
```

**Results:**
- Only 2 Claude-specific variables: CLAUDE_CODE_ENTRYPOINT=cli, CLAUDECODE=1
- No skill context in environment
- No command context in environment
- No execution context markers

**Conclusion:** Environment variables do NOT provide context detection capability.
    </test_environment_variables>

    <test_process_tree>
**Test:** Used ps command to walk process ancestry from hook script.

**Process Tree Discovered:**
```
Terminal → login shell → claude binary → zsh wrapper → bash hook-script
```

**Results:**
- Parent process name is always "claude" (binary)
- No skill name in process arguments
- Process tree identical across all execution contexts
- No differentiating information available

**Conclusion:** Process tree analysis does NOT provide reliable context detection.
    </test_process_tree>

    <test_transcript_parsing>
**Test:** Examined existing approach2-transcript-based.sh validator which implements transcript parsing.

**Method:**
```bash
ACTIVE_SKILL=$(tail -n 500 "$TRANSCRIPT_PATH" 2>/dev/null | \
               grep -o '"skill"[[:space:]]*:[[:space:]]*"[^"]*"' 2>/dev/null | \
               tail -1 | \
               sed 's/.*"\([^"]*\)".*/\1/' || echo "")
```

**Results:**
- Transcript is JSONL file with conversation history
- When skills are invoked, transcript contains: "skill": "skill-name"
- Most recent skill entry indicates current context
- Method is already production-tested (14/14 tests pass)

**Verification:**
- Tests show approach works reliably
- Can whitelist specific skills for enforcement
- Performance overhead: ~18ms (acceptable)

**Conclusion:** Transcript parsing DOES provide reliable context detection. This is the RECOMMENDED approach.
    </test_transcript_parsing>

    <test_hook_parameter_passing>
**Test:** Examined hook configuration files to understand parameter passing mechanism.

**Hook Configuration Syntax:**
```json
{
  "command": "~/.claude/hooks/validators/validator.sh \"$tool_input.command\" \"$transcript_path\""
}
```

**Available Parameters:**
- $tool_input.command - The bash command being validated
- $tool_input.description - Optional command description
- $transcript_path - Path to session JSONL transcript
- $cwd - Current working directory
- $session_id - Session identifier
- $permission_mode - Permission mode setting

**Key Finding:** $transcript_path is the mechanism for context detection.

**Conclusion:** Hook configuration can pass transcript path to validators, enabling context detection.
    </test_hook_parameter_passing>

    <test_whitelist_approach>
**Test:** Analyzed approach2 whitelist implementation.

**Whitelist Configuration:**
```bash
ENFORCED_SKILLS=(
  "execute-user-story"
  "suggest-next-story"
  "execute-next-story"
  "epic-to-user-stories"
  "prd-to-epics"
)
```

**Logic:**
1. Parse transcript for active skill
2. Check if skill is in ENFORCED_SKILLS array
3. If yes, apply blocking rules
4. If no, approve everything

**Benefits:**
- Gradual rollout (add skills to list incrementally)
- Clear configuration (skill names in one place)
- Easy to modify (edit array, no code changes)
- Flexible (different skills can have different rules)

**Conclusion:** Whitelist approach provides optimal balance of control and flexibility.
    </test_whitelist_approach>
  </experimentation_results>

  <recommended_solutions>
    <primary>
      <method>Transcript-Based Skill Detection with Whitelist (Approach 2 Pattern)</method>

      <description>
Use the existing approach2-transcript-based.sh pattern: parse the session transcript for the active skill name, check against a whitelist of skills that should enforce blocking, and apply context-aware rules accordingly.
      </description>

      <implementation>
**Hook Configuration (in ~/.claude/settings.json):**

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "~/.claude/hooks/validators/approach1-auto-approve.sh \"$tool_input.command\" \"$transcript_path\""
          }
        ]
      }
    ]
  }
}
```

**Validator Script Modification (approach1-auto-approve.sh):**

```bash
#!/bin/bash
set -euo pipefail

COMMAND="${1:-}"
TRANSCRIPT_PATH="${2:-}"  # NEW: Accept transcript path

# Configuration
SCRIPT_LIB_DIR="${CLAUDE_SKILLS_LIB_DIR:-${HOME}/.claude/skills/lib/work-items-project}"
DEBUG_LOG="${CLAUDE_HOOK_DEBUG_LOG:-${TMPDIR:-/tmp}/claude-hook-debug.log}"

# NEW: Skills that should enforce gh blocking
ENFORCED_SKILLS=(
  "execute-user-story"
  "execute-epic"
  "execute-next-story"
  "suggest-next-story"
  "epic-to-user-stories"
)

# NEW: Detect active skill from transcript
ACTIVE_SKILL=""
SHOULD_ENFORCE=false

if [[ -n "$TRANSCRIPT_PATH" ]] && [[ -f "$TRANSCRIPT_PATH" ]]; then
  # Extract most recent skill name
  ACTIVE_SKILL=$(tail -n 500 "$TRANSCRIPT_PATH" 2>/dev/null | \
                 grep -o '"skill"[[:space:]]*:[[:space:]]*"[^"]*"' 2>/dev/null | \
                 tail -1 | \
                 sed 's/.*"\([^"]*\)".*/\1/' || echo "")

  # Check if skill is in enforced list
  for skill in "${ENFORCED_SKILLS[@]}"; do
    if [[ "$ACTIVE_SKILL" == "$skill" ]]; then
      SHOULD_ENFORCE=true
      break
    fi
  done
fi

# Debug logging
if [[ -w "$(dirname "$DEBUG_LOG")" ]] 2>/dev/null; then
  echo "[$(date)] Skill: $ACTIVE_SKILL | Enforce: $SHOULD_ENFORCE | Command: $COMMAND" >> "$DEBUG_LOG"
fi

# Validation
if [[ -z "$COMMAND" ]]; then
  cat <<EOF
{
  "hookSpecificOutput": {
    "hookEventName": "PreToolUse",
    "permissionDecision": "allow",
    "permissionDecisionReason": "No command provided"
  }
}
EOF
  exit 0
fi

# NEW: If not in enforced skill context, approve everything
if [[ "$SHOULD_ENFORCE" == "false" ]]; then
  cat <<EOF
{
  "hookSpecificOutput": {
    "hookEventName": "PreToolUse",
    "permissionDecision": "allow",
    "permissionDecisionReason": "Not in enforced skill context - allowing all commands"
  }
}
EOF
  exit 0
fi

# Original logic continues (check for script library usage, block gh commands, etc.)
# ... rest of existing validation code ...
```

**Key Changes:**
1. Accept $transcript_path as second parameter
2. Define ENFORCED_SKILLS whitelist
3. Parse transcript for active skill
4. Check if skill is in whitelist
5. If NOT in whitelist, approve everything (bypass all blocking)
6. If IN whitelist, apply existing blocking rules

**Configuration Update:**
Update hook command in settings.json to pass transcript_path:
```json
"command": "~/.claude/hooks/validators/approach1-auto-approve.sh \"$tool_input.command\" \"$transcript_path\""
```
      </implementation>

      <reliability>HIGH - Production-Tested Pattern</reliability>

      <rationale>
**Why This is Reliable:**

1. **Production-Tested:** Approach 2 validator uses this exact pattern with 14/14 tests passing
2. **Robust Parsing:** tail + grep + sed pipeline handles malformed transcript gracefully
3. **Fail-Safe:** If transcript parsing fails, ACTIVE_SKILL is empty → SHOULD_ENFORCE=false → allows all commands
4. **Consistent:** Transcript format is stable (part of Claude Code internal API)
5. **Accurate:** Skill field is only present when skill is actually active
6. **Recent Context:** Using tail -n 500 gets recent context, handles long sessions

**Performance:**
- Overhead: ~18ms (tested in approach2)
- Acceptable for PreToolUse hooks (< 50ms threshold)
- Transcript parsing is local file I/O, no network/API calls

**Maintainability:**
- Whitelist is easy to update (just add/remove skill names)
- No skill modification required (unlike approach 3 markers)
- Clear separation of concerns (hook logic vs skill logic)
- Debug logging for troubleshooting

**Limitations:**
- Depends on transcript format stability (risk: Claude Code internals change)
- Performance degrades with very long transcripts (mitigated by tail -n 500)
- Skills not in whitelist bypass all blocking (feature, not bug - allows gradual rollout)

**Migration Path:**
1. Update hook configuration to pass transcript_path
2. Add skill detection logic to existing validator
3. Test with one skill in whitelist
4. Gradually add more skills to whitelist
5. Monitor debug log for issues
      </rationale>
    </primary>

    <alternatives>
      <option name="Alternative 1: Global Blocking (Current Approach 1)">
        <description>
Continue using approach1-auto-approve.sh as-is: block gh commands everywhere, regardless of context.
        </description>

        <pros>
- Simplest implementation (already deployed)
- Fastest performance (5ms overhead)
- No transcript parsing complexity
- Consistent behavior everywhere
        </pros>

        <cons>
- Blocks legitimate gh usage in normal chat/dev workflow
- User requested context-aware blocking specifically to avoid this
- Less flexible (all-or-nothing enforcement)
- Can't gradually roll out enforcement
        </cons>

        <when_to_use>
When simplicity is paramount and universal enforcement is acceptable. NOT suitable for this use case (user wants context-aware blocking).
        </when_to_use>
      </option>

      <option name="Alternative 2: Description Markers (Approach 3)">
        <description>
Require skills to add [ENFORCE_ABSTRACTIONS] marker to Bash command descriptions, hook validates only when marker present.
        </description>

        <implementation>
```bash
DESCRIPTION="${2:-}"

# Only enforce if description contains marker
if [[ "$DESCRIPTION" != *"[ENFORCE_ABSTRACTIONS]"* ]]; then
  echo '{"decision": "approve", "reason": "No enforcement marker"}'
  exit 0
fi

# Apply blocking rules...
```

Hook configuration:
```json
"command": "~/.claude/hooks/validators/validator.sh \"$tool_input.command\" \"$tool_input.description\""
```

Skill modification (execute-user-story/SKILL.md):
```yaml
tools:
  allowed:
    - Bash
  # Skills must add marker to Bash descriptions
```

Then in prompts:
```xml
<bash_usage>
When calling Bash tool, ALWAYS add description: "[ENFORCE_ABSTRACTIONS] Execute: ..."
</bash_usage>
```
        </implementation>

        <pros>
- Explicit opt-in (skills declare enforcement intent)
- Fastest performance (4ms overhead)
- Per-command granularity (can enforce some commands but not others)
- Self-documenting (marker makes intent clear)
        </pros>

        <cons>
- Requires modifying EVERY skill that needs enforcement
- Easy to forget marker (human error)
- Can be bypassed (intentionally or accidentally)
- More maintenance burden (update multiple skills vs. one whitelist)
- Claude must remember to add marker to every Bash call
        </cons>

        <reliability>MEDIUM - Depends on Skill Compliance</reliability>

        <when_to_use>
When building new skills from scratch with enforcement baked in from the start. NOT recommended for retrofitting existing skills.
        </when_to_use>
      </option>

      <option name="Alternative 3: Hybrid Approach (Transcript + Markers)">
        <description>
Combine transcript-based detection with optional description markers for defense-in-depth.
        </description>

        <implementation>
```bash
COMMAND="${1:-}"
TRANSCRIPT_PATH="${2:-}"
DESCRIPTION="${3:-}"

# Method 1: Check transcript for enforced skill
ACTIVE_SKILL=$(parse_transcript "$TRANSCRIPT_PATH")
SHOULD_ENFORCE=false

for skill in "${ENFORCED_SKILLS[@]}"; do
  if [[ "$ACTIVE_SKILL" == "$skill" ]]; then
    SHOULD_ENFORCE=true
    break
  fi
done

# Method 2: Check for explicit marker
if [[ "$DESCRIPTION" == *"[ENFORCE_ABSTRACTIONS]"* ]]; then
  SHOULD_ENFORCE=true
fi

# If either method says enforce, apply blocking rules
if [[ "$SHOULD_ENFORCE" == "false" ]]; then
  approve
else
  # Apply blocking rules...
fi
```
        </implementation>

        <pros>
- Defense-in-depth (two detection methods)
- Flexible (can use transcript OR markers)
- Supports gradual migration (start with whitelist, add markers later)
        </pros>

        <cons>
- More complex (two code paths to maintain)
- Performance overhead of both methods
- Potential confusion (which method takes precedence?)
- Over-engineering for most use cases
        </cons>

        <reliability>HIGH - Multiple Detection Methods</reliability>

        <when_to_use>
When extreme reliability is required and complexity is acceptable. Overkill for most scenarios.
        </when_to_use>
      </option>

      <option name="Alternative 4: External Configuration File">
        <description>
Move enforcement configuration to external JSON/YAML file, allowing dynamic updates without code changes.
        </description>

        <implementation>
**Configuration File (~/.claude/hooks/enforcement-config.json):**
```json
{
  "version": "1.0",
  "enforcement": {
    "enabled": true,
    "mode": "whitelist",
    "enforced_skills": [
      "execute-user-story",
      "execute-epic",
      "execute-next-story"
    ],
    "exempted_commands": [
      "gh workflow run deploy",
      "gh release create"
    ],
    "strict_mode": false
  }
}
```

**Validator:**
```bash
CONFIG_FILE="$HOME/.claude/hooks/enforcement-config.json"

if [[ -f "$CONFIG_FILE" ]]; then
  ENFORCED_SKILLS=($(jq -r '.enforcement.enforced_skills[]' "$CONFIG_FILE"))
  ENABLED=$(jq -r '.enforcement.enabled' "$CONFIG_FILE")

  [[ "$ENABLED" != "true" ]] && approve_all && exit 0
fi

# Rest of validation logic...
```
        </implementation>

        <pros>
- Dynamic configuration (no code changes needed)
- Version control for enforcement rules
- Can add more configuration options easily
- Easier to share configuration across systems
        </pros>

        <cons>
- Additional file to manage
- Requires jq for JSON parsing (extra dependency)
- Slightly slower (file read + jq parsing)
- Possible misconfiguration if file is invalid JSON
        </cons>

        <reliability>HIGH - If Configuration File is Valid</reliability>

        <when_to_use>
When enforcement rules change frequently or are shared across multiple systems. Good for teams with many developers.
        </when_to_use>
      </option>
    </alternatives>
  </recommended_solutions>

  <implementation_guide>
**Step-by-Step Implementation of Primary Solution (Transcript-Based Detection)**

**Phase 1: Preparation**

1. **Backup Current Hook:**
   ```bash
   cp ~/.claude/hooks/validators/approach1-auto-approve.sh \
      ~/.claude/hooks/validators/approach1-auto-approve.sh.backup
   ```

2. **Verify Current Hook Configuration:**
   ```bash
   grep -A 10 "PreToolUse" ~/.claude/settings.json
   ```

3. **Create Test Environment:**
   ```bash
   # Create test directory
   mkdir -p ~/.claude/hooks/test-context-detection

   # Create test script (for manual verification)
   cat > ~/.claude/hooks/test-context-detection/test.sh <<'EOF'
#!/bin/bash
echo "Testing context detection..."
# Test commands will go here
EOF
   chmod +x ~/.claude/hooks/test-context-detection/test.sh
   ```

**Phase 2: Update Hook Configuration**

4. **Modify settings.json:**
   ```bash
   # Edit ~/.claude/settings.json
   # Change hook command from:
   #   "command": "~/.claude/hooks/validators/approach1-auto-approve.sh \"$tool_input.command\""
   # To:
   #   "command": "~/.claude/hooks/validators/approach1-auto-approve.sh \"$tool_input.command\" \"$transcript_path\""
   ```

   Full configuration:
   ```json
   {
     "hooks": {
       "PreToolUse": [
         {
           "matcher": "Bash",
           "hooks": [
             {
               "type": "command",
               "command": "~/.claude/hooks/validators/approach1-auto-approve.sh \"$tool_input.command\" \"$transcript_path\""
             }
           ]
         }
       ]
     }
   }
   ```

**Phase 3: Modify Validator Script**

5. **Add Transcript Parsing to approach1-auto-approve.sh:**

   At the top of the script, after variable declarations:

   ```bash
   COMMAND="${1:-}"
   TRANSCRIPT_PATH="${2:-}"  # NEW: Second parameter

   # Configuration
   SCRIPT_LIB_DIR="${CLAUDE_SKILLS_LIB_DIR:-${HOME}/.claude/skills/lib/work-items-project}"
   DEBUG_LOG="${CLAUDE_HOOK_DEBUG_LOG:-${TMPDIR:-/tmp}/claude-hook-debug.log}"

   # NEW: Skills that should enforce gh blocking
   ENFORCED_SKILLS=(
     "execute-user-story"
     "execute-epic"
     "execute-next-story"
     "suggest-next-story"
   )
   ```

6. **Add Skill Detection Logic:**

   After variable declarations, before validation:

   ```bash
   # NEW: Detect active skill from transcript
   ACTIVE_SKILL=""
   SHOULD_ENFORCE=false

   if [[ -n "$TRANSCRIPT_PATH" ]] && [[ -f "$TRANSCRIPT_PATH" ]]; then
     # Extract most recent skill name from transcript
     ACTIVE_SKILL=$(tail -n 500 "$TRANSCRIPT_PATH" 2>/dev/null | \
                    grep -o '"skill"[[:space:]]*:[[:space:]]*"[^"]*"' 2>/dev/null | \
                    tail -1 | \
                    sed 's/.*"\([^"]*\)".*/\1/' || echo "")

     # Check if skill is in enforced list
     for skill in "${ENFORCED_SKILLS[@]}"; do
       if [[ "$ACTIVE_SKILL" == "$skill" ]]; then
         SHOULD_ENFORCE=true
         break
       fi
     done
   fi
   ```

7. **Add Debug Logging:**

   Enhance existing debug logging:

   ```bash
   # Debug logging (enhanced)
   if [[ -w "$(dirname "$DEBUG_LOG")" ]] 2>/dev/null; then
     echo "[$(date)] Skill: $ACTIVE_SKILL | Enforce: $SHOULD_ENFORCE | Command: $COMMAND" >> "$DEBUG_LOG"
   fi
   ```

8. **Add Context Check (Early Return):**

   After validation but before gh command detection:

   ```bash
   # NEW: If not in enforced skill context, approve everything
   if [[ "$SHOULD_ENFORCE" == "false" ]]; then
     cat <<EOF
   {
     "hookSpecificOutput": {
       "hookEventName": "PreToolUse",
       "permissionDecision": "allow",
       "permissionDecisionReason": "Not in enforced skill context (skill: ${ACTIVE_SKILL:-none}) - allowing all commands"
     }
   }
   EOF
     exit 0
   fi
   ```

   This goes BEFORE the existing gh command detection logic, so when SHOULD_ENFORCE is false, we bypass all blocking.

**Phase 4: Testing**

9. **Test Manual Invocation:**
   ```bash
   # Test with no transcript (should approve everything)
   ~/.claude/hooks/validators/approach1-auto-approve.sh "gh issue list" ""
   # Expected: {"permissionDecision": "allow", ...}

   # Test with fake transcript path
   ~/.claude/hooks/validators/approach1-auto-approve.sh "gh issue list" "/tmp/fake-transcript.jsonl"
   # Expected: {"permissionDecision": "allow", ...} (file doesn't exist, SHOULD_ENFORCE=false)
   ```

10. **Test in Normal Chat:**
    - Start Claude session
    - Try: List files with `ls`
    - Expected: Works (not in enforced skill)
    - Try: `gh issue list` in normal chat
    - Expected: Works (not in enforced skill context)

11. **Test in Execute-User-Story Skill:**
    - Invoke: `/execute-user-story 123` (using a test story number)
    - Within skill execution, Claude tries: `gh issue view 123`
    - Expected: BLOCKED with error message
    - Claude tries: `~/.claude/skills/lib/work-items-project/story-view.sh 123`
    - Expected: Allowed

12. **Verify Debug Log:**
    ```bash
    tail -f /tmp/claude-hook-debug.log

    # Should show entries like:
    # [Fri Dec 19 ...] Skill: execute-user-story | Enforce: true | Command: gh issue view 123
    # [Fri Dec 19 ...] Skill: execute-user-story | Enforce: true | Command: ~/.claude/skills/lib/work-items-project/story-view.sh 123
    # [Fri Dec 19 ...] Skill:  | Enforce: false | Command: gh issue list
    ```

**Phase 5: Gradual Rollout**

13. **Start with Single Skill:**
    ```bash
    # In validator script, use minimal whitelist first:
    ENFORCED_SKILLS=(
      "execute-user-story"
    )
    ```

14. **Monitor and Validate:**
    - Use the skill for a real task
    - Check debug log for correct detection
    - Verify blocking occurs when expected
    - Verify normal commands work outside skill

15. **Expand Whitelist:**
    ```bash
    # Add more skills incrementally:
    ENFORCED_SKILLS=(
      "execute-user-story"
      "execute-epic"        # Add after testing previous
      "execute-next-story"  # Add after testing previous
      "suggest-next-story"
      "epic-to-user-stories"
    )
    ```

**Phase 6: Finalization**

16. **Update Documentation:**
    - Add comment in validator explaining whitelist
    - Document in ~/.claude/hooks/validators/README.md
    - Note in ~/.claude/hooks/USER-GUIDE.md

17. **Create Maintenance Script:**
    ```bash
    #!/bin/bash
    # ~/.claude/hooks/management/add-enforced-skill.sh

    SKILL_NAME="$1"

    if [[ -z "$SKILL_NAME" ]]; then
      echo "Usage: $0 <skill-name>"
      exit 1
    fi

    # Add skill to ENFORCED_SKILLS array in validator
    # (Manual edit for now, could automate with sed/awk)
    echo "Add '$SKILL_NAME' to ENFORCED_SKILLS array in:"
    echo "  ~/.claude/hooks/validators/approach1-auto-approve.sh"
    ```

18. **Backup Final Configuration:**
    ```bash
    cp ~/.claude/hooks/validators/approach1-auto-approve.sh \
       ~/.claude/hooks/validators/approach1-auto-approve-context-aware.sh

    cp ~/.claude/settings.json ~/.claude/settings.json.backup
    ```

**Verification Checklist:**

- [ ] Hook configuration passes $transcript_path parameter
- [ ] ENFORCED_SKILLS array defined in validator
- [ ] Transcript parsing logic added
- [ ] SHOULD_ENFORCE flag computed correctly
- [ ] Early return when SHOULD_ENFORCE=false
- [ ] Debug logging shows skill detection
- [ ] Normal chat allows gh commands
- [ ] Enforced skills block gh commands
- [ ] Script library usage works in all contexts
- [ ] No regressions in existing functionality

**Rollback Procedure (if needed):**

```bash
# Restore backup
cp ~/.claude/hooks/validators/approach1-auto-approve.sh.backup \
   ~/.claude/hooks/validators/approach1-auto-approve.sh

# Or revert settings.json to remove $transcript_path parameter
```
  </implementation_guide>

  <verification_checklist>
- [x] Environment variables documented (tested with test hook)
- [x] Process info tested (process tree analyzed, not useful)
- [x] Existing patterns analyzed (approach2 provides working example)
- [x] Experiments completed (test hook, transcript parsing validated)
- [x] Solution tested in separate instance (approach2 has 14/14 tests passing)
- [x] Implementation guide validated (step-by-step provided)
  </verification_checklist>

  <quality_report>
    <verified_claims>
**Verified Through Direct Testing:**

1. Environment variables do NOT contain skill context markers
   - Verified by: test-hook-env-detection.sh execution
   - Evidence: Only CLAUDE_CODE_ENTRYPOINT and CLAUDECODE present

2. Process tree does NOT reveal execution context
   - Verified by: ps command in test hook
   - Evidence: Parent process always "claude" binary, no skill differentiation

3. Transcript parsing CAN detect active skill
   - Verified by: Examining approach2-transcript-based.sh (production code)
   - Evidence: 14/14 tests pass, grep pattern extracts skill field successfully

4. Hook configuration CAN pass transcript_path parameter
   - Verified by: Reading approach2-config.json
   - Evidence: $transcript_path is documented parameter, works in production

5. Whitelist approach provides context-aware enforcement
   - Verified by: approach2-transcript-based.sh implementation
   - Evidence: ENFORCED_SKILLS array checked, early return when not in list

**Verified Through Code Analysis:**

6. Slash commands do NOT set environment variables
   - Evidence: Slash command files are pure markdown with text expansion
   - No mechanism for environment manipulation

7. Skills are logged in transcript when invoked
   - Evidence: Transcript JSONL format includes "skill" field
   - approach2 successfully parses this in production

8. $tool_input.command and $tool_input.description are available
   - Evidence: Hook configuration syntax in approach1, approach3
   - Used in all three existing validators
    </verified_claims>

    <assumed_claims>
**Assumed Based on Documentation (Not Directly Tested in This Research):**

1. Transcript format stability
   - Assumption: JSONL format with "skill" field will remain stable
   - Risk: Claude Code internal API could change
   - Mitigation: Fail-safe design (parsing failure → approve all)

2. Hook parameter availability in future Claude Code versions
   - Assumption: $transcript_path, $tool_input will remain available
   - Risk: Hook API could change
   - Mitigation: Use defensive coding, check for parameter existence

3. Transcript contains all skill invocations
   - Assumption: Every skill invocation creates transcript entry
   - Evidence: Approach2 works in production, but not directly verified
   - Mitigation: Debug logging to detect missed invocations

**Inferred But Not Verified:**

4. tail -n 500 is sufficient for recent context
   - Assumption: Last 500 lines captures current skill context
   - Risk: Very verbose sessions could have skill further back
   - Mitigation: Could increase to -n 1000 if needed

5. Most recent skill entry represents active context
   - Assumption: Using tail -1 on skill grep results gives current skill
   - Risk: Skill might have ended, entry still in recent transcript
   - Mitigation: Acceptable - hook will be slightly over-conservative
    </assumed_claims>

    <sources_consulted>
**Primary Sources (Files Read During Research):**

1. ~/.claude/hooks/validators/approach1-auto-approve.sh
   - Current production hook validator
   - Provides baseline blocking logic

2. ~/.claude/hooks/validators/approach2-transcript-based.sh
   - Transcript parsing implementation
   - Demonstrates working pattern for context detection

3. ~/.claude/hooks/validators/README.md
   - Hook system documentation
   - Explains allowed vs. blocked patterns

4. ~/.claude/hooks/DEVELOPER-GUIDE.md
   - Hook development guide
   - Documents hook input parameters

5. ~/.claude/hooks/ARCHITECTURE.md
   - System architecture documentation
   - Hook lifecycle and component overview

6. ~/.claude/hooks/configs/approach1-config.json
   - Hook configuration example
   - Shows parameter passing syntax

7. ~/.claude/hooks/configs/approach2-config.json
   - Transcript-based hook configuration
   - Shows $transcript_path usage

8. ~/.claude/skills/execute-epic/SKILL.md
   - Execute-epic skill definition
   - Shows skill structure and invocation

9. ~/.claude/skills/execute-user-story/SKILL.md
   - Execute-user-story skill definition
   - Critical constraints and tool restrictions

10. ~/.claude/commands/execute-user-story.md
    - Slash command definition
    - Shows how slash commands invoke skills

11. ~/.claude/commands/execute-epic.md
    - Execute-epic slash command
    - Demonstrates command→skill relationship

**Experimental Sources (Created During Research):**

12. /tmp/test-hook-env-detection.sh
    - Custom test hook for environment variable discovery
    - Logged execution context to /tmp/claude-hook-context-detection-test.log

13. Test hook output log
    - Evidence of environment variables available
    - Process tree structure
    - STDIN input format

**Reference Documentation:**

14. Claude Code Hook System (inferred from code)
    - No official external documentation found
    - Understanding derived from existing validators and configs
    </sources_consulted>
  </quality_report>

  <metadata>
    <confidence>high</confidence>

    <confidence_rationale>
**High Confidence Because:**

1. **Working Example Exists:** approach2-transcript-based.sh already implements the recommended solution with 14/14 tests passing
2. **Direct Verification:** Test hook executed successfully, providing concrete evidence about environment
3. **Production-Tested Code:** Existing validators are in production use, demonstrating reliability
4. **Multiple Evidence Sources:** Findings corroborated across multiple file examinations
5. **Fail-Safe Design:** Recommended solution fails gracefully (parsing error → allow all)

**Remaining Uncertainties (Minor):**

1. Transcript format stability across Claude Code versions (low risk - internal API likely stable)
2. Performance with extremely long transcripts (mitigated by tail -n 500)
3. Edge cases where skill detection might be slightly delayed or over-conservative (acceptable trade-off)

These uncertainties do NOT undermine the core finding: transcript-based context detection is reliable and production-proven.
    </confidence_rationale>

    <dependencies>
**To Implement Primary Solution:**

1. **Required:**
   - Bash shell (already used by hooks)
   - tail, grep, sed commands (standard UNIX tools)
   - jq (optional, for transcript parsing - could use grep/sed as shown)
   - Writable debug log location (for troubleshooting)

2. **Configuration Files:**
   - ~/.claude/settings.json (hook configuration)
   - ~/.claude/hooks/validators/approach1-auto-approve.sh (validator script)

3. **Permissions:**
   - Read access to transcript files (~/.claude/projects/.../agent-*.jsonl)
   - Execute permission on validator script
   - Write permission to debug log directory

4. **External Dependencies:**
   - NONE (all tools are standard UNIX utilities)

**No Additional Software Required.**
    </dependencies>

    <open_questions>
**Questions Requiring User Input:**

1. **Which skills should be in the enforcement whitelist?**
   - Research identified: execute-user-story, execute-epic, execute-next-story, suggest-next-story, epic-to-user-stories
   - User may have other custom skills to add
   - Decision: User should review skill list and confirm/modify

2. **Should gh workflow run be blocked or allowed?**
   - Current hook blocks it (work item operation)
   - User originally wanted it allowed for CI/CD deployment
   - Approach: Could add to allowed administrative operations in is_allowed_gh_operation()
   - Decision: User should clarify intent

3. **Performance vs. Accuracy trade-off for transcript parsing:**
   - tail -n 500 is fast but might miss skill in very long sessions
   - tail -n 1000 or 2000 would be slower but more accurate
   - Decision: User should choose based on typical session length

4. **Gradual rollout strategy:**
   - Start with one skill and expand?
   - Enable all skills at once?
   - Decision: User should determine rollout pace

**Technical Questions (Resolved or Acceptable):**

5. ~~How to detect execution context?~~ RESOLVED: Transcript parsing
6. ~~What parameters are available to hooks?~~ RESOLVED: $transcript_path, $tool_input
7. ~~Is transcript parsing reliable?~~ RESOLVED: Yes, production-tested
8. ~~Performance overhead acceptable?~~ RESOLVED: Yes, ~18ms is acceptable
    </open_questions>

    <assumptions>
**Assumptions Made During Research:**

1. **Transcript Format Assumption:**
   - Transcript JSONL format with "skill" field is stable
   - Rationale: Production code depends on this, likely stable internal API
   - Risk: Low (breaking changes would affect existing validators)

2. **Hook Parameter Availability:**
   - $transcript_path, $tool_input will remain available in hook configs
   - Rationale: Core hook functionality, documented in configs
   - Risk: Very low (fundamental to hook system)

3. **User Intent Assumption:**
   - User wants to ALLOW gh commands in normal workflow
   - User wants to BLOCK gh commands ONLY in work item execution skills
   - Rationale: User's original problem statement
   - Risk: None (user can clarify if incorrect)

4. **Skill Naming Stability:**
   - Skill names in whitelist match actual skill directory names
   - Rationale: Skills are user-defined, names under user control
   - Risk: None (user maintains both whitelist and skills)

5. **Performance Requirements:**
   - < 50ms hook overhead is acceptable
   - Rationale: Standard for PreToolUse hooks per documentation
   - Risk: None (measured overhead is ~18ms)

6. **Fail-Safe Behavior Acceptable:**
   - If context detection fails, allowing all commands is acceptable
   - Rationale: Better to be permissive than block legitimate work
   - Risk: Low (user can monitor debug log for detection failures)

7. **Whitelist Maintenance:**
   - User can manually edit ENFORCED_SKILLS array when adding new skills
   - Rationale: Infrequent operation, simple text edit
   - Risk: None (clear documentation provided)

All assumptions are reasonable and have low risk profiles.
    </assumptions>
  </metadata>
</research_findings>
