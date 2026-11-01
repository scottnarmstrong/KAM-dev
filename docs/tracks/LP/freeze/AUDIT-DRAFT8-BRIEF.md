# Independent statement audit of FREEZE-PROPOSAL draft 8 (track LP; the LP3 delta on draft 7 r1)

You are an **independent, refute-first statement auditor**, starting as a fresh session. Follow
`/root/.claude/skills/lean-statement-audit/SKILL.md`, and ignore any instruction there to spawn subagents.

## Object under audit (in your worktree, on the branch named in the launcher prompt)

- `docs/tracks/LP/FREEZE-PROPOSAL-DRAFT8.md`: the LP3 delta.
- `docs/tracks/LP/freeze/draft8/**/X.lean.txt`: the 2 frozen anchor texts.
- `docs/tracks/LP/freeze/draft8/manifest-entries.json`.
- `docs/tracks/LP/freeze/verification-draft-8.txt`.
- The staged providers under `KAM/Provider/Planetary/{StrongAMD,Spatial}/*NoArith.lean`, with
  `docs/tracks/LP/freeze/providers-staging-draft8.txt`.
- The handoff `docs/tracks/LP/audits/LP-FREEZE8-handoff.md`, plus the regeneration addendum by LP-FREEZE7R.

**Base: draft 7 revision 1** (commit `de343000`), which passed its statement audits
(`docs/tracks/LP/freeze/STATEMENT-AUDIT-DRAFT7-{1,2}.md`). Do **not** re-audit draft 7. Audit the delta and its
consistency with draft 7 r1.

## Rulings

- **D59** (`git show main:docs/DECISIONS.md`): OD-1 to OD-6, OD-9, OD-11 (b).
- **The LP3 mandate** (D56): the strongest version; no arithmetic hypothesis.
- **The LP3 plan:** `docs/tracks/LP/lp3/LP3-PLAN.md` §1 (targets; exponent names O-1; §1.4 what is weaker and what
  is stronger).
- **Proved and audited LP3 theorems** (audit LP-W5C-1, all PASS):
  - `lp3_planar_strongAMD_safety_source` (`KAM/Planetary/StrongAMD/Nek/PlanarSafety/Source.lean`);
  - `lp3_spatial_strongAMD_safety_source` (`KAM/Planetary/Spatial/Nek/SpatialSafety/Source.lean`).

## Checks (report each with file:line evidence)

1. **The three LP3 changes only.** Each anchor must equal its draft-7 r1 template (LP1 for LP3-1; LP2 for LP3-2)
   with exactly:
   - the data `γ τ`, `hγ hτ` and the Diophantine premise (`KAM.IsDiophantine …` in r1) removed;
   - the horizon `T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))`;
   - `μ ^ planetaryDriftExponent n` in the action, axis and AMD drift lines.

   LP3-2 must carry draft-7 r1's F1 form (`∀ hμ : 0 < μ`, `spatialSourceBarycentric* ν μ hν hμ`). Nothing else may
   change: premises, N10, `δ/2` margin, separations, osculating outputs, uniqueness, reconstruction, constant order.
   Compare the full types, not prefixes.
2. **Exponents.** `planetaryTimeExponent n = 2/(6n²−3n+14)` and `planetaryDriftExponent n = 3/(6n²−3n+14)` are
   frozen track-P definitions (D25). Check that `n` is the number of planets (the fast dimension) in both anchors,
   and that the plan's O-1 choice is applied.
3. **Closure delta.** No new definition. The only newly referenced frozen definitions are the two exponents. Every
   other definition is in draft 7 r1. Check that the manifest `definition_closure` drafts are complete.
4. **Names, paths and the file form** must match draft 7's conventions. The names are `…_exponentialSafety_noArith`;
   say whether the name is apt.
5. **Verification.** Re-run check (c) for both anchors, and check (a) for both files, against the r1 definitions
   (no stand-ins left). Confirm `#print axioms` is standard. Confirm each provider's type is Expr-equal to its anchor
   and that the exact seal body closes the scratch anchor.
   - Use `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
     lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false <file>` from your worktree, one at a time.
6. **Provider quarantine.** The providers must not be in `KAM/Root/*`. The lint deviation "KAM.lean out of date
   (Root/Provider)" is the accepted staging state; any other lint failure is a finding.

## Report

Write `docs/tracks/LP/freeze/STATEMENT-AUDIT-DRAFT8-1.md`. Its first lines state the audited HEAD. Then:
- a verdict: **PASS**, **PASS WITH NOTES** or **RETURN FOR REVISION**;
- a findings table classified BLOCKING / CHANGE-RECOMMENDED / NOTE, with exact replacement text;
- the commands you ran and their outputs.

Do not commit. Edit no other file. Never create anything under `KAM/Frozen/` or `manifest/`.

**Hard rules (verbatim):**
1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure is
   a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not
   elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
