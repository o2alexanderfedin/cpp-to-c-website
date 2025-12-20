---
type: meta-prompt
created: 2025-12-19
purpose: Analyze actual development time from git history and file timestamps
output: JSON file with real time-based effort analysis
---

# Actual Development Time Analysis Meta-Prompt

## Objective

Analyze the C++ to C transpiler project's **actual development time** based on commit timestamps, file modifications, and git history. This provides ground truth data to compare against the effort estimates in `project_effort_analysis.json`.

## Rationale

The previous analysis (`007-project-effort-analysis.md`) used:
- Industry benchmarks (LOC/hour estimates)
- Documented phase timelines (weeks)
- Theoretical effort calculations

This analysis will use:
- **Real commit timestamps** to determine actual working sessions
- **File modification patterns** to identify development phases
- **Time gaps analysis** to distinguish active work from idle time
- **Contributor activity** to understand actual hours spent

## Three-Phase Approach

### Phase 1: Git History Analysis

**Goal**: Extract all temporal data from git repository.

**Tasks**:

1. **Complete Commit History**:
   ```bash
   cd .. && git log --all --format="%ai|%an|%ae|%s|%H" --numstat > /tmp/full_commit_history.txt
   cd .. && git log --all --format="%ai|%H|%s" --reverse > /tmp/chronological_commits.txt
   ```

2. **Per-File Timeline**:
   ```bash
   # For each major file category, get modification timeline
   cd ..
   for file in src/**/*.cpp src/**/*.h; do
     git log --follow --format="%ai|%H" -- "$file" | head -1
   done > /tmp/file_creation_times.txt

   # Get file modification distribution by date
   git log --all --format="%ai" --name-only | grep -v "^$" > /tmp/files_by_date.txt
   ```

3. **Author Activity Timeline**:
   ```bash
   cd ..
   # Commits per day per author
   git log --all --format="%ai|%an" | \
     awk -F'|' '{split($1,d," "); print d[1]"|"$2}' | \
     sort | uniq -c > /tmp/commits_per_day_author.txt

   # Active hours analysis (commits by hour of day)
   git log --all --format="%ai|%an" | \
     awk -F'|' '{split($1,t," "); split(t[2],h,":"); print h[1]"|"$2}' | \
     sort | uniq -c > /tmp/commits_by_hour.txt
   ```

4. **Development Session Detection**:
   ```bash
   cd ..
   # Gap analysis: time between consecutive commits
   git log --all --format="%ai" --reverse | \
     awk 'NR>1 {print prev"|"$0} {prev=$0}' > /tmp/commit_gaps.txt
   ```

5. **Epic/Phase Timeline Extraction**:
   ```bash
   cd ..
   # Find epic completion reports and extract dates
   grep -r "Completion Date\|completion_date\|Date:" EPIC_*.md *_COMPLETION_REPORT.md | \
     sort > /tmp/epic_dates.txt

   # Extract phase markers from commit messages
   git log --all --format="%ai|%s" | \
     grep -i "phase\|epic\|story" > /tmp/phase_commits.txt
   ```

### Phase 2: Temporal Analysis & Calculation

**Goal**: Convert raw timestamps into meaningful development time metrics.

**Key Concepts**:

1. **Active Development Session**:
   - Consecutive commits within 4 hours = single session
   - Gap > 4 hours = new session (sleep, break, other work)
   - Session duration = first commit to last commit in session

2. **Daily Active Time**:
   - Multiple sessions per day are summed
   - Maximum 16 hours/day (sanity cap)
   - Minimum 0.25 hours/session (single commit)

3. **Phase Duration**:
   - Start: First commit mentioning phase/epic
   - End: Last commit for that phase/epic
   - Active time: Sum of all sessions within phase date range

**Calculation Algorithms**:

```python
# Session Detection Algorithm
def detect_sessions(commits):
    """
    commits: list of (timestamp, hash, message)
    returns: list of (start_time, end_time, commit_count)
    """
    sessions = []
    current_session = None
    SESSION_GAP_HOURS = 4

    for i, commit in enumerate(commits):
        if current_session is None:
            current_session = {
                'start': commit.timestamp,
                'end': commit.timestamp,
                'commits': [commit]
            }
        else:
            gap_hours = (commit.timestamp - current_session['end']).total_seconds() / 3600

            if gap_hours <= SESSION_GAP_HOURS:
                # Continue current session
                current_session['end'] = commit.timestamp
                current_session['commits'].append(commit)
            else:
                # End session, start new one
                sessions.append(current_session)
                current_session = {
                    'start': commit.timestamp,
                    'end': commit.timestamp,
                    'commits': [commit]
                }

    if current_session:
        sessions.append(current_session)

    return sessions

# Session Duration Calculation
def calculate_session_duration(session):
    """
    Calculate actual working time in session
    """
    commit_count = len(session['commits'])
    duration_seconds = (session['end'] - session['start']).total_seconds()

    # Heuristics:
    # - Single commit: 15 minutes minimum
    # - Multiple commits: actual duration + 30 min buffer (post-last-commit work)

    if commit_count == 1:
        return 0.25  # 15 minutes
    else:
        hours = duration_seconds / 3600
        buffered_hours = hours + 0.5  # Add 30 min buffer
        return min(buffered_hours, 8.0)  # Cap at 8 hours per session

# Daily Aggregation
def aggregate_by_day(sessions):
    """
    Group sessions by calendar day, sum hours
    """
    daily_hours = {}

    for session in sessions:
        day = session['start'].date()
        hours = calculate_session_duration(session)

        if day in daily_hours:
            daily_hours[day] += hours
        else:
            daily_hours[day] = hours

    # Apply daily cap
    for day in daily_hours:
        daily_hours[day] = min(daily_hours[day], 16.0)

    return daily_hours

# Phase Time Calculation
def calculate_phase_time(commits, phase_pattern):
    """
    Find all commits for a phase, calculate total active time
    """
    phase_commits = [c for c in commits if matches_pattern(c.message, phase_pattern)]

    if not phase_commits:
        return 0, None, None

    start_date = phase_commits[0].timestamp
    end_date = phase_commits[-1].timestamp

    # Get all commits within phase date range
    phase_range_commits = [
        c for c in commits
        if start_date <= c.timestamp <= end_date
    ]

    sessions = detect_sessions(phase_range_commits)
    daily_hours = aggregate_by_day(sessions)
    total_hours = sum(daily_hours.values())

    return total_hours, start_date, end_date
```

**Calculation Steps**:

1. Parse all commits into timeline
2. Detect development sessions (4-hour gap threshold)
3. Calculate session durations (with heuristics)
4. Aggregate to daily hours (16-hour daily cap)
5. Map commits to phases/epics
6. Sum phase hours
7. Calculate productivity metrics (LOC/hour actual)

### Phase 3: JSON Generation & Comparison

**Goal**: Output actual time data and compare with estimates.

**Output Location**: `../actual_time_analysis.json`

**JSON Structure**:

```json
{
  "project": {
    "name": "C++ to C Transpiler",
    "analysis_date": "2025-12-19",
    "analysis_type": "actual_time_based",
    "repository": "cpp-to-c-transpiler",
    "analysis_version": "1.0"
  },
  "timeline": {
    "first_commit": "YYYY-MM-DD HH:MM:SS",
    "last_commit": "YYYY-MM-DD HH:MM:SS",
    "calendar_days": 0,
    "active_days": 0,
    "total_commits": 0,
    "total_sessions": 0,
    "average_session_duration_hours": 0
  },
  "actual_effort": {
    "total_hours": 0,
    "total_days_equivalent": 0,
    "total_weeks_equivalent": 0,
    "average_hours_per_day": 0,
    "active_days_worked": 0,
    "calculation_method": "session_based_with_gaps"
  },
  "sessions": {
    "total_count": 0,
    "average_duration_hours": 0,
    "median_duration_hours": 0,
    "shortest_session_hours": 0,
    "longest_session_hours": 0,
    "sessions_by_day_of_week": {},
    "sessions_by_hour_of_day": {}
  },
  "daily_breakdown": [
    {
      "date": "YYYY-MM-DD",
      "hours_worked": 0,
      "sessions": 0,
      "commits": 0,
      "files_modified": 0,
      "loc_added": 0,
      "loc_removed": 0,
      "primary_activity": "implementation|testing|documentation|research"
    }
  ],
  "phases_actual": [
    {
      "phase_number": 0,
      "phase_name": "Phase 1: Requirements & Research",
      "start_date": "YYYY-MM-DD",
      "end_date": "YYYY-MM-DD",
      "calendar_days": 0,
      "active_hours": 0,
      "sessions": 0,
      "commits": 0,
      "identification_method": "commit_message_pattern|epic_dates|file_path_analysis"
    }
  ],
  "epics_actual": [
    {
      "epic_number": 0,
      "epic_name": "",
      "start_date": "YYYY-MM-DD",
      "end_date": "YYYY-MM-DD",
      "active_hours": 0,
      "sessions": 0,
      "commits": 0,
      "stories_identified": []
    }
  ],
  "productivity_metrics": {
    "actual_loc_per_hour": 0,
    "actual_commits_per_hour": 0,
    "actual_files_per_hour": 0,
    "actual_tests_per_hour": 0,
    "actual_docs_pages_per_hour": 0
  },
  "comparison_with_estimates": {
    "estimated_total_hours": 0,
    "actual_total_hours": 0,
    "variance_hours": 0,
    "variance_percentage": 0,
    "efficiency_multiplier": 0,
    "notes": "Actual vs estimated comparison"
  },
  "activity_patterns": {
    "most_productive_hour": 0,
    "most_productive_day_of_week": "",
    "average_gap_between_sessions_hours": 0,
    "longest_continuous_work_period_hours": 0,
    "work_schedule_type": "full_time|part_time|burst|consistent"
  },
  "methodology": {
    "session_gap_threshold_hours": 4,
    "minimum_session_duration_hours": 0.25,
    "maximum_session_duration_hours": 8,
    "maximum_daily_hours": 16,
    "single_commit_default_hours": 0.25,
    "post_commit_buffer_hours": 0.5,
    "assumptions": []
  },
  "confidence": {
    "overall": "high|medium|low",
    "session_detection": "high|medium|low",
    "phase_mapping": "high|medium|low",
    "notes": ""
  },
  "raw_data_files": [
    "/tmp/full_commit_history.txt",
    "/tmp/chronological_commits.txt",
    "/tmp/commits_per_day_author.txt",
    "/tmp/commit_gaps.txt"
  ]
}
```

## Execution Instructions

### Step 1: Data Collection

Run all bash scripts to collect raw git data:

```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c

# Full commit history with stats
git log --all --format="%ai|%an|%ae|%s|%H" --numstat > /tmp/full_commit_history.txt

# Chronological commits
git log --all --format="%ai|%H|%s" --reverse > /tmp/chronological_commits.txt

# Commits per day
git log --all --format="%ai|%an" | \
  awk -F'|' '{split($1,d," "); print d[1]"|"$2}' | \
  sort | uniq -c > /tmp/commits_per_day_author.txt

# Commits by hour of day
git log --all --format="%ai" | \
  awk '{split($2,h,":"); print h[1]}' | \
  sort | uniq -c > /tmp/commits_by_hour.txt

# Epic/phase dates
grep -r "Completion Date\|completion_date\|Date:" EPIC_*.md *_COMPLETION_REPORT.md 2>/dev/null | \
  sort > /tmp/epic_dates.txt

# Phase-related commits
git log --all --format="%ai|%s" | \
  grep -i "phase\|epic\|story" > /tmp/phase_commits.txt
```

### Step 2: Parse and Analyze

1. Load chronological commits
2. Parse timestamps (ISO 8601 format)
3. Apply session detection algorithm
4. Calculate session durations
5. Aggregate by day, week, phase
6. Map commits to epics/phases (by message pattern + dates)
7. Calculate actual productivity metrics

### Step 3: Generate Comparison

Compare with `project_effort_analysis.json`:

```javascript
estimated_hours = json.summary.total_effort_hours
actual_hours = calculated_from_sessions

efficiency_multiplier = estimated_hours / actual_hours
variance = estimated_hours - actual_hours
variance_pct = (variance / estimated_hours) * 100
```

### Step 4: Output Files

Generate:
1. `../actual_time_analysis.json` - Complete actual time breakdown
2. `../time_comparison_report.md` - Human-readable comparison
3. Keep raw data files in `/tmp/` for verification

## Key Metrics to Calculate

1. **Total Active Hours**: Sum of all session durations
2. **Calendar Days**: First commit to last commit
3. **Active Days**: Days with at least one commit
4. **Average Hours/Day**: Total hours / active days
5. **Sessions Count**: Number of detected work sessions
6. **Average Session Duration**: Mean session length
7. **Actual LOC/Hour**: Total LOC / total hours
8. **Efficiency Multiplier**: Estimated hours / actual hours

## Success Criteria

- ✅ All commits parsed with timestamps
- ✅ Sessions detected with reasonable gap threshold
- ✅ Daily hours calculated with caps applied
- ✅ Phase/epic times mapped from commit data
- ✅ Productivity metrics calculated from actuals
- ✅ Comparison with estimates completed
- ✅ JSON output valid and complete
- ✅ Results are reasonable (no 24-hour days, etc.)

## Notes for Executor

- **Session gaps**: 4 hours is typical for meals, breaks, context switches
- **Single commits**: Assume 15 minutes minimum (thinking + coding + commit)
- **Daily caps**: 16 hours max per day (extreme, but possible)
- **Session caps**: 8 hours max per session (reasonable work block)
- **Epic mapping**: Use commit message patterns + epic completion dates
- **Validation**: Cross-check totals against calendar duration
- **Conservative approach**: When uncertain, use higher time estimates

## Expected Insights

This analysis will reveal:
- **Actual working patterns** (burst vs steady, time of day preferences)
- **Real productivity rates** (LOC/hour based on actual time)
- **Efficiency gains** (if actual << estimated, AI boost is quantified)
- **Phase durations** (which phases took most real time)
- **Work intensity** (hours per active day)
- **Schedule patterns** (full-time vs part-time development)
