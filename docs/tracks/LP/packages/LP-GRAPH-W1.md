# Package LP-GRAPH-W1: LP source dependency graph, post-freeze setup and wave 1 (the LP0 closure)

**Why now.** LP was frozen and sealed on main at `f46b94fb` (D62). The owner's standing rule: once the LP graph is
published, every LP landing gets its LEAN_STATUS sync within the hour. The graph is owed now. root-b8 accepted all
the defaults Q1–Q8 (`docs/graph/LP/README.md`, "Orchestrator rulings"). **The writer tag is `kam-lp`.** You are the
extractor for this package, working under the writer's direction.

## Method (binding)

Read `/root/.claude/skills/build-proof-dependency-graph/SKILL.md` in full, with every file it references. Follow it
exactly. Then read:
- `docs/graph/LP/` in full: `SPEC.md`, `README.md` (especially "First commands after the freeze"), `CORPUS.sha256`,
  `IMPORTS.sha256`, `draft/*`, `packets/slices.json`, `tools/`.
- The precedent graph `docs/graph/W/`, the most recent one, finished after W's seal (D61), for layout, header,
  LEAN_STATUS and assembly/lint commands. Also `docs/graph/K/SPEC.md` for roles.

**Inputs:**
- `docs/tracks/LP/source/MAIN.md` and `AMENDMENTS.md`, both pinned.
- `manifest/frozen-anchors.json` on this branch: the 128 LP entries of D62, identity fields only. Per the skill,
  never read Lean bodies.
- `docs/tracks/LP/FREEZE.md`.

## Scope of this package

1. **Post-freeze setup** (README steps 1–3).
   - Re-check the pins.
   - Build the anchor map from the frozen manifest: the 39 theorem anchors (5 headline: LP0, LP1, LP1-H, LP2, LP2-H;
     34 characterizations, which are roots per Q2) and the bound frozen definitions (the reused track-P/I frozen
     definitions bound as LP anchor nodes per Q6).
   - Settle and record Q1–Q8 per the rulings. Fill SPEC §1/§8 and its change log.
   - Write `header.txt` from the K/W pattern.
2. **Q7:** write the small Markdown pre-extractor that MAIN.md needs, in `docs/graph/LP/tools/`.
3. **Q3–Q5:** do the statement splits exactly as SPEC proposes. Lemma 3 splits into static and dynamic parts. The
   unused Lemma 4 clauses and display (35) split off (N4).
4. **Wave 1 extraction:** the LP0 closure, as the slices in `packets/slices.json` mark it. That is MAIN §1, Lemmas 1–6
   and the amendments, with the slices `LP-adef-pl`, `LP-athm` and the wave-1 slices.
   - Write the packets, run the dry run, extract the nodes, edges and route records, and run the skill's linter until
     it exits 0.
   - Assemble the wave and run the assembly lint.
   - Produce the wave's LEAN_STATUS against the sealed anchors on main, in the precedent's format and with its sync
     command.
5. **Stop at the review gate.** Each slice needs an independent review, codex-2 per D57, which the orchestrator
   launches, one session per reviewer, in parallel batches. Write the review packets the skill prescribes, then touch
   `.drafts/READY-LP-GRAPH-W1`.
   - Do **not** self-review.
   - Do not mark any node REVIEWED.

## Branch and worktree

Use the worktree `/root/code/KAM-inp-lp-freeze` (on the HC volume, with the build of the landed freeze). Create a new
branch `inp-lp-graph` from the current `inp`; it contains f46b94fb's content. This is docs-only work under
`docs/graph/LP/`. Never edit anything under `KAM/` or `manifest/`. Never run lean or lake except the read-only queries
the skill explicitly allows; any you run goes through `/root/code/KAM-inp/.drafts/LP/lp_lean.sh`.

## Rules

- No Lean edits. Never kill processes by name. Never search the whole filesystem.
- **Hard rules (verbatim):**
  1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration
     failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
     proof will not elaborate at default heartbeats, report it as a design signal.
  2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
     preserving public import paths as cheap facades.
- Commit after each step on `inp-lp-graph`.

## Handoff

Write `docs/tracks/LP/audits/LP-GRAPH-W1-handoff.md` (committed) with:
- the setup decisions;
- the wave-1 node, edge and route counts;
- the linter output;
- the LEAN_STATUS of wave 1;
- the review packets;
- open issues.

Also write `.drafts/handoff-LP-GRAPH-W1.md`, then `touch .drafts/READY-LP-GRAPH-W1`.
