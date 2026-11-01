# Package LP-FREEZE8R: draft 8 (LP3 anchors) regenerated against the landed LP freeze (D62)

Freeze preparation. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md`.

## Context

- **D62:** draft 7 r1 is frozen and sealed on main (landing in progress: branch `inp-lp-freeze`, record
  `docs/tracks/LP/FREEZE.md`). The LP definitions, including the two F1 maps `spatialSourceBarycentric*`, now live in
  `KAM/Frozen/Planetary/{StrongAMD,Spatial}/Defs/`, and the implementation imports them.
- **Draft 8** (LP-FREEZE8, branch `inp-lp-freeze8`) has the two LP3 anchors `…_exponentialSafety_noArith`. Its
  checks used stand-ins and the pre-freeze definition texts. Its regeneration against revision 1 was paused at a WIP
  point (see `inp-lp-freeze8` and `docs/tracks/LP/audits/LP-FREEZE8-handoff.md`).
- **Draft 8 is not approved.** It needs its statement audit (`docs/tracks/LP/freeze/AUDIT-DRAFT8-BRIEF.md`), then the
  owner's approval.

## Task

1. On a new branch `inp-lp-freeze8r` from the current `inp` after the freeze lands, cherry-pick or merge the draft-8
   material from `inp-lp-freeze8`:
   - `FREEZE-PROPOSAL-DRAFT8.md` and `freeze/draft8/`;
   - the scripts in `.drafts/freeze8/`;
   - the two providers.

   Do **not** bring in `inp-lp-freeze8`'s merge of `inp-lp-freeze7`; the frozen tree on `inp` replaces it.
2. Regenerate both anchor texts and the manifest entry drafts against the **frozen** definitions:
   - imports become the frozen definition modules;
   - `definition_closure` lists the frozen files, now real on `inp`;
   - no new definition.

   The texts must be exactly LP1 and LP2 of D62 (the frozen anchor texts) with the three LP3 changes. LP3-2 keeps the
   F1 form.
3. Rerun the checks against **real modules**: no stand-ins and no simulation, since the frozen modules now exist.
   - (a) each anchor text elaborates in a scratch module that imports exactly its frozen dependencies;
   - (c) each anchor is stated verbatim and closed by `exact` of `lp3_{planar,spatial}_strongAMD_safety_source` (its
     type Expr-equal), with `#print axioms`;
   - the providers' Expr-equality and the exact seal bodies.

   Record everything in `docs/tracks/LP/freeze/verification-draft-8.txt`.
4. **Plan for one pass.** Draft 8 will be installed already sealed in one pass, like D62. List the exact files and
   manifest entries (2 anchors and 2 providers) in the proposal.

## Rules

- Nothing under `KAM/Frozen/` or `manifest/` until the owner approves draft 8.
- No premise added and nothing weakened.
- `lp_lean.sh` and `lp_build.sh` only (4 GB cap), one at a time.
- **Hard rules (verbatim):**
  1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration
     failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
     proof will not elaborate at default heartbeats, report it as a design signal.
  2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
     preserving public import paths as cheap facades.

## Handoff

`docs/tracks/LP/audits/LP-FREEZE8R-handoff.md` (committed), then `touch .drafts/READY-LP-FREEZE8R`.
