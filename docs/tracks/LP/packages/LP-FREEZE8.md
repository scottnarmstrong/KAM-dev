# Package LP-FREEZE8: FREEZE-PROPOSAL draft 8, the LP3 delta (exact freeze text of LP3-1 and LP3-2 under D59)

Freeze preparation. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md`. Base: `inp-lp-freeze8` =
`inp-lp-freeze7` (draft 7, under its independent statement audit) + `inp-lp` (LP3 fully proved and audited: W5A,
W5B, W5C).

## What and why

root-b8 (2026-11-01): "LP3 is not in draft 7. … when LP3-PS and LP3-SP-SAFE are proved and audited, propose its
anchors as a separate delta (draft 8)." Both are proved, and audit LP-W5C-1 passed with all components PASS. Draft 8
is a **delta document on top of draft 7**. It follows draft 7's conventions exactly: file form, paths, namespaces,
provider names, manifest fields, verification method and docstring template. It must not change any draft-7 text.

**Draft 7 is still under audit** (`docs/tracks/LP/freeze/AUDIT-DRAFT7-BRIEF.md`). If that audit changes a draft-7
convention, the orchestrator will tell you, or the change will appear on `inp-lp-freeze7`; adapt to it.

## Read first

- `docs/tracks/LP/FREEZE-PROPOSAL.md` (draft 7) in full, with its handoff `docs/tracks/LP/audits/LP-FREEZE7-handoff.md`
  (the 12 convention choices) and `freeze/verification-draft-7.txt`.
- The generator scripts in `.drafts/freeze7/` (gitignored; on `inp-lp-freeze7` in `/root/code/KAM-inp-lp-freeze7`).
  **Copy them, read-only**, to `.drafts/freeze8/` in your worktree. Never write in the freeze7 worktree: an auditor
  is working there.
- The LP3 plan `docs/tracks/LP/lp3/LP3-PLAN.md` §1 (targets; exponent names, O-1).
- The proved theorems:
  - `lp3_planar_strongAMD_safety_source{,_general}` (`KAM/Planetary/StrongAMD/Nek/PlanarSafety/Source.lean`);
  - `lp3_spatial_strongAMD_safety_source{,_general}` (`KAM/Planetary/Spatial/Nek/SpatialSafety/Source.lean`);
  - the audit `docs/tracks/LP/audits/LP-W5C-audit-1.md`.

## Deliverables

1. `docs/tracks/LP/FREEZE-PROPOSAL-DRAFT8.md`: the LP3 delta. It contains:
   - the anchors LP3-1 (planar) and LP3-2 (spatial), each the normalized source-carrier form, with names in draft 7's
     style (for example `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith`; choose and justify),
     paths, providers and closing theorems;
   - the exact texts;
   - a reading of each anchor in words, including what is weaker and what is stronger than LP1 and LP2 (plan §1.4);
   - the definition closure delta. It should be empty or tiny: the exponents `planetaryTimeExponent` and
     `planetaryDriftExponent` are already frozen (track P), and every other definition is in draft 7. Compute it with
     Lean, as draft 7 did.
2. The exact frozen file texts under `docs/tracks/LP/freeze/draft8/<frozen path>.txt`, and the manifest entry drafts
   `docs/tracks/LP/freeze/draft8/manifest-entries.json`.
3. Transient verification, as in draft 7:
   - (a) the texts elaborate against the draft-7 definitions;
   - (b) bodies are equal, if any new definition exists;
   - (c) each anchor is stated verbatim and closed by `exact` of the proved theorem, with `#print axioms`.

   Record the output in `docs/tracks/LP/freeze/verification-draft-8.txt`.

## Rules

- Never create anything under `KAM/Frozen/` or `manifest/`.
- Never edit draft 7's files or the freeze7 worktree.
- No premise may be added, and nothing weakened.
- `lp_lean.sh` only, one Lean process at a time.

Expected size: about 2 anchors, 2–4 files.

## Handoff

`docs/tracks/LP/audits/LP-FREEZE8-handoff.md` (committed) and `.drafts/handoff-LP-FREEZE8.md`, then
`touch .drafts/READY-LP-FREEZE8`.
