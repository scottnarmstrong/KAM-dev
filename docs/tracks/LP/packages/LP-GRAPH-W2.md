# Package LP-GRAPH-W2: LP source dependency graph, wave 2 (the LP1 and LP1-H closure)

The continuation of LP-GRAPH-W1. **Writer tag `kam-lp`; you are the extractor.** Wave-1 reviews (batch R1, six
codex-2 sessions) run in parallel with you. Do not touch wave-1 packets or the review files. If a wave-1 review later
rewrites a record that a wave-2 record depends on, the writer reconciles it.

## Read

- The skill `/root/.claude/skills/build-proof-dependency-graph/SKILL.md`, with every file it references.
- `docs/graph/LP/` in full: `SPEC.md` as settled in W1, `README.md`, `packets/slices.json`,
  `packets/anchor-binding.tsv`, the tools.
- The W1 handoff `docs/tracks/LP/audits/LP-GRAPH-W1-handoff.md`, especially "Wave 2 inherits":
  - the Q5 split of (35);
  - the 13 deferred items;
  - the 7 wave-2 reused definitions;
  - the LP1/LP1-H anchors and the 4 osculating characterizations;
  - the 5 wave-2 externals;
  - LP-imports (the N and P imports).
- The precedent `docs/graph/W/`.

## Scope

Extract wave 2 as `packets/slices.json` marks it: MAIN Lemmas 7–16, the LP1 and LP1-H anchors (T15 + L16), the
imports slice and the wave-2 externals. Use the same mode as W1: writer-tag extraction from compact specs, with
`EXTRACTOR: kam-lp`.
1. Write the packets and run the dry run.
2. Extract the nodes, edges and route records. **L12/L13 is the first route alternative.** MAIN's two drift suppliers
   are the nonresonant Lemma 12 route and the Lemma 13 route the Lean proof uses. Model them per the skill's route
   rules and SPEC §7.
3. Run the slice linter on each slice until it exits 0. Assemble waves 1+2 and run the assembly lint, with
   `--require-all-reachable` for the roots served so far.
4. Update the LEAN_STATUS overlay for wave 2 against the sealed anchors on main.
5. Write the review packets for batch R2, in the R1 format, and stop at the review gate.
   - No self-review, and nothing marked REVIEWED.

## Branch and worktree

Same as W1: `/root/code/KAM-inp-lp-graph`, branch `inp-lp-graph`. This is docs-only work under `docs/graph/LP/`.
Commit after each step. Six read-only R1 reviewers are working in this worktree, each writing only its own file under
`docs/graph/LP/reviews/`. Never edit those files and never run state-changing git on them. Commit only your own paths,
with `git add <paths>`, never `git add -A`.

## Rules

- No Lean edits, and never read Lean bodies. Never kill processes by name. Never search the whole filesystem.
- **Hard rules (verbatim):**
  1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration
     failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
     proof will not elaborate at default heartbeats, report it as a design signal.
  2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
     preserving public import paths as cheap facades.

## Handoff

Write `docs/tracks/LP/audits/LP-GRAPH-W2-handoff.md` (committed) and `.drafts/handoff-LP-GRAPH-W2.md`, then
`touch .drafts/READY-LP-GRAPH-W2`.
