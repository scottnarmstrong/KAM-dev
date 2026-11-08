# Package LP-GRAPH-R1APPLY: finish applying review batch R1 to wave 1 and prepare the delta reviews

**Writer tag `kam-lp`; you assist the writer.** Work in `/root/code/KAM-inp-lp-graph` on branch `inp-lp-graph`. The
wave-2 extractor (LP-GRAPH-W2) works in the same worktree. **Touch only the paths named below. Commit with
`git add <paths>`, never `git add -A`. Do not edit wave-2 packets, and do not commit `DEPGRAPH.md` or
`DEPGRAPH_COVERAGE.md`:** the W2 extractor assembles waves 1+2 at its end.

## State

- Batch R1 (eight codex-2 reviews in `docs/graph/LP/reviews/LP-*-review-1.md`) is done. Commit `93bdb95a` applied it
  for LP-adef-pl, LP-athm, LP-m1, LP-m2a and LP-m2b with `inp_depgraph_apply_review.py` and
  `inp_depgraph_mark_reviewed.py` (both in `/mnt/HC_Volume_106379410/orchestrator-tools/`). That replaced 34 records
  and marked the passed records REVIEWED. The `repaired.json` files are in `packets/`.
- The tools **crash** on the three small slices:
  - `LP-ext`: a parse error on the coverage blocks;
  - `LP-amend` and `LP-m78`: they have no nodes, and the mark tool needs a `repaired.json`.

## Tasks

1. **Finish the three small slices** (reviewer tag `sol-review-LP-R1-small`):
   - `LP-ext`: one FAIL, `lpM:ext-ftc`. Restrict the contract to zero derivative, using the review's replacement
     fragment. Mark the passed records.
   - `LP-amend`: one FAIL, `lpA:N2`. Apply its replacement, including the source fields of `lpM:L6` and of the
     shared U that the review names. Mark the rest.
   - `LP-m78`: all 12 items PASS; mark them.

   Either fix the tools' handling of node-less slices **in a copy under `docs/graph/LP/tools/`** (do not edit the
   shared orchestrator-tools), or apply exactly what the tools would have done by hand. Record which you chose.
2. **Lint.** Run `inp_depgraph_slice_check.py` on all eight wave-1 slices (exit 0). Assemble waves 1+2 into a
   **scratch** path, for example `.drafts/r1/DEPGRAPH.md`, and run `proof_depgraph.py` on it. Do not overwrite the
   committed `DEPGRAPH.md`. Record the outputs in `docs/graph/LP/reports/R1-apply.txt`.
3. **Delta-review packets.** Write `docs/graph/LP/reviews/R1-delta-packets.md` with one packet per slice that had
   replaced records: the 34 records already replaced plus the 2 above. Use the R1 format, with tags
   `sol-delta1-LP-<slice>`; each delta review must be a fresh, different session. Each delta reviewer checks only the
   replaced records against MAIN and AMENDMENTS and the original review's complaint. List the record IDs per packet.
4. **Source-defect sections.** If any review lists a suspected source defect, list it in
   `docs/graph/LP/reports/R1-errata.txt` (location, quoted text, why) for the orchestrator's ledger.

## Rules

Docs only. No Lean, and never read Lean bodies. Never search the whole filesystem. Never kill processes by name.

**Hard rules (verbatim):**
1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure is
   a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not
   elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.

## Handoff

Write `docs/tracks/LP/audits/LP-GRAPH-R1APPLY-handoff.md` (committed), then `touch .drafts/READY-LP-GRAPH-R1APPLY`.
