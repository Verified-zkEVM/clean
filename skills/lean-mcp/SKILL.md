# Lean LSP via mcporter - Skill

This skill enables interactive inspection of Lean proof states using the Lean Language Server Protocol via mcporter.

## When to use this skill

- You're stuck on a Lean proof and need to see the exact goal state after simplifications
- Your `rw` or `simp` commands aren't matching the expected pattern  
- You want to understand what a tactic is actually doing
- You need to verify a proof compiles without waiting for full `lake build`

## Setup (one-time)

```bash
npm install -g mcporter
# uv should already be installed (check with: which uv)
```

The `config/mcporter.json` in the repo is already configured for the `lean-lsp` MCP server.

## Key Commands

### 1. View proof state at a line (MOST IMPORTANT)

```bash
mcporter call lean-lsp.lean_goal \
  file_path:/absolute/path/to/File.lean \
  line:123
```

Returns:
- `goals_before`: Goal state at the start of the line
- `goals_after`: Goal state at the end of the line (after tactic executes)
- Shows exactly how the tactic transforms the goal

**Example**:
```bash
cd /mnt/data-2tb/tmp/clean
mcporter call lean-lsp.lean_goal \
  file_path:/mnt/data-2tb/tmp/clean/Clean/Examples/FibonacciWithChannels.lean \
  line:728
```

### 2. Get diagnostics (errors/warnings)

```bash
mcporter call lean-lsp.lean_diagnostic_messages \
  file_path:/absolute/path/to/File.lean \
  start_line:100 end_line:150
```

### 3. Try multiple tactics without modifying the file

```bash
mcporter call lean-lsp.lean_multi_attempt \
  file_path:/path/to/File.lean \
  line:123 \
  'snippets:["simp", "rw [foo]", "exact bar"]'
```

Returns the goal state after each tactic, so you can see which one makes progress.

### 4. Get type/documentation for a symbol

```bash
mcporter call lean-lsp.lean_hover_info \
  file_path:/path/to/File.lean \
  line:123 column:10
```

Column should be at the START of the identifier you want to inspect.

### 5. Search for theorems/lemmas

```bash
# Natural language search via LeanSearch
mcporter call lean-lsp.lean_leansearch \
  query:"sum of two even numbers is even" \
  num_results:5

# Type signature search via Loogle  
mcporter call lean-lsp.lean_loogle \
  query:"(?a → ?b) → List ?a → List ?b" \
  num_results:8

# Semantic search via LeanFinder
mcporter call lean-lsp.lean_leanfinder \
  query:"I have h : n < m and need n + 1 < m + 1" \
  num_results:5
```

## All Available Tools

Run `mcporter list lean-lsp --schema` to see all 18 available tools with full documentation.

Key tools include:
- `lean_goal` - proof states (use this the most!)
- `lean_diagnostic_messages` - errors/warnings
- `lean_hover_info` - type information
- `lean_completions` - autocompletions
- `lean_multi_attempt` - try multiple tactics
- `lean_local_search` - search project declarations
- `lean_leansearch`, `lean_loogle`, `lean_leanfinder` - theorem search
- `lean_state_search`, `lean_hammer_premise` - find relevant lemmas for goals

## Workflow Tips

1. **When a proof step fails**: Use `lean_goal` to see the exact goal state before and after the tactic
2. **When rewrite doesn't match**: Check `goals_after` the previous line to see the exact pattern
3. **When stuck**: Try `lean_multi_attempt` with several candidate tactics
4. **When looking for lemmas**: Use `lean_local_search` first (fast), then external search tools if needed

## Common Issues

- **Timeouts**: The first call after opening a file can be slow (LSP server starting). Subsequent calls are fast.
- **File paths**: Must be absolute paths (not relative)
- **Line numbers**: 1-indexed (first line is 1, not 0)
- **Column numbers**: 1-indexed, should point to the START of an identifier for hover info
