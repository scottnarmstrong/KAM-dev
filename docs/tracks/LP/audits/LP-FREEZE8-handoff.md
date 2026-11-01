# Handoff LP-FREEZE8: FREEZE-PROPOSAL draft 8 (the LP3 delta on draft 7) and provider staging

Branch `inp-lp-freeze8` (worktree `/root/code/KAM-inp-lp-freeze8`), base `ced282aa`. Commits: `e877f867` (draft-8
texts, manifest drafts, verification) and `f431d047` (staged providers). Nothing was created or edited under
`KAM/Frozen/` or `manifest/` (not even transiently); `git diff ced282aa HEAD -- KAM/Frozen manifest KAM.lean KAM/Root
README.md lakefile.lean` is empty. Nothing was written in `/root/code/KAM-inp-lp-freeze7` (only read; its
`.drafts/freeze7/` scripts were copied to `.drafts/freeze8/`).

## Result

Draft 8 is ready for an independent statement audit. **No premise was added, nothing was weakened, no new definition
is needed.**

- **Anchors (2):** LP3-1 `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith`
  (`KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean`), closed by
  `KAM.Planetary.StrongAMD.lp3_planar_strongAMD_safety_source`; LP3-2
  `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith`
  (`KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean`), closed by
  `KAM.Planetary.Spatial.lp3_spatial_strongAMD_safety_source`. Providers
  `KAM.Provider.Planetary.{StrongAMD,Spatial}.<name>` in `KAM/Provider/Planetary/{StrongAMD,Spatial}/<File>.lean`.
- **Texts:** normalized source-carrier form (OD-3 `hνmax`, `hνle`; OD-11 (b) carriers). LP3-1 = draft-7 LP1 with
  exactly the three LP3 changes (no `γ τ hγ hτ` and no Diophantine premise; `μ ^ (-planetaryTimeExponent n)`;
  `μ ^ planetaryDriftExponent n` in the action, axis and AMD drift lines). LP3-2 = draft-7 LP2 with the draft-7 r1 F1
  change (see below) and the same three changes. Both asserted by the generator (whitespace-normalized equality) and
  shown as unified diffs.
- **Definition closure delta:** 0 new definitions, 0 new characterizations. Newly referenced already-frozen
  definitions: `KAM.Planetary.planetaryTimeExponent`, `KAM.Planetary.planetaryDriftExponent` (track P, D25; plan
  O-1 recommendation). Everything else is draft-7 (r1). `KAM.Fourier.modeSize` is not used by LP3.
- **Name choice** `…_noArith` (FREEZE-PROPOSAL-DRAFT8 §2): names the distinguishing property ("no arithmetic
  hypothesis", D56/OD-12 wording, the brief's suggestion); keeps the `…_exponentialSafety` family prefix; avoids
  `resonant/nonresonant` (MAIN's T15/T19 are "nonresonant"), `uniform` (ambiguous), `nekhoroshev` (method, not content).
  Alternatives offered: `…_noArithmetic`, `…_noDiophantine`.

## Orchestrator updates applied (2026-11-01)

1. **Draft-7 audit returned (STATEMENT-AUDIT-DRAFT7-1, F1, F2, N2).** As instructed, LP3-2 uses the same F1
   convention exactly: `∀ μ : ℝ, ∀ hμ : 0 < μ, μ ≤ μ₀ →`, `spatialSourceBarycentricPositions ν μ hν hμ (z t).1`,
   `spatialSourceBarycentricVelocities ν μ hν hμ (z t).2`. The two new maps are treated as **draft-7 revision-1**
   definitions (conventional frozen paths `KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentric{Positions,
   Velocities}.lean`, in the manifest closure). Because their r1 files do not exist yet, checks (a), (c), the
   closure and the manifest use **stand-ins** with the auditor's exact declaration text (docstrings mine); draft 8
   must be regenerated (`python3 .drafts/freeze8/gen8.py --write`, then `mk_checks8.py`, `run8.sh`,
   `mk_manifest8.py`, `mk_verification8.py`, `mk_proposal8.py`) once LP-FREEZE7R's r1 files exist. LP3-1 is unaffected
   (planar maps are frozen). F2 touches only draft-7 files. N2's freeze sentence is adopted in draft 8 too.
2. **Providers staged** (separate commit `f431d047`), recorded in `docs/tracks/LP/freeze/providers-staging-draft8.txt`.

## Files

- `docs/tracks/LP/FREEZE-PROPOSAL-DRAFT8.md` — the delta proposal (rulings, anchor table, exact texts, readings,
  weaker/stronger table, closure delta, manifest, rebase/seal plan, notes).
- `docs/tracks/LP/freeze/draft8/KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean.txt`,
  `…/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean.txt` — the exact frozen file texts.
- `docs/tracks/LP/freeze/draft8/manifest-entries.json` — 2 entry drafts (draft-7 schema).
- `docs/tracks/LP/freeze/verification-draft-8.txt` — commands and outputs of every check.
- `KAM/Provider/Planetary/StrongAMD/PlanarStrongAMDExponentialSafetyNoArith.lean` (111 lines),
  `KAM/Provider/Planetary/Spatial/SpatialStrongAMDExponentialSafetyNoArith.lean` (117 lines) — staged providers.
- `docs/tracks/LP/freeze/providers-staging-draft8.txt` — provider staging record.
- This handoff (copy `.drafts/handoff-LP-FREEZE8.md`).
- Scripts (gitignored, `.drafts/freeze8/`): `gen8.py`, `mk_checks8.py`, `closure_delta8.py`, `mk_manifest8.py`,
  `mk_proposal8.py`, `mk_verification8.py`, `mk_providers8.py`, `run8.sh`, `proposal8_template.md`; draft-7 machinery
  copied read-only (`gen.py`, `records.json`, `spec/`, `closure.lean`, `mk_bc.py`).

## Checks run (exact commands; full outputs in the verification / staging files)

All Lean through the wrappers, one process at a time.

- **Build** (LP3 oleans were not in this worktree's snapshot): `/root/code/KAM-inp/.drafts/LP/lp_build.sh
  /root/code/KAM-inp-lp-freeze8 KAM.Planetary.StrongAMD.Nek.PlanarSafety.Source
  KAM.Planetary.Spatial.Nek.SpatialSafety.Source` — exit 0; "Build completed successfully (9369 jobs)." and
  "(9429 jobs)."
- **Closure** (`lp_lean.sh … .drafts/freeze8/c8_verification.lean` with `#kamClosure` of the anchors as elaborated,
  and `closure8.lean` over the implementation theorems; both exit 0): 104 = 81 draft-7 (r1) + 23 frozen, resp.
  102 = 79 + 23; 0 other.
- **(a)** `lp_lean.sh … .drafts/freeze8/a8/<module>.lean` (2 files, draft-7 dependency texts + r1 stand-ins inlined):
  2/2 exit 0; only "declaration uses `sorry`", one per file.
- **(b)** not applicable (no new definition).
- **(c)** `lp_lean.sh … .drafts/freeze8/c8_verification.lean` exit 0: both anchors verbatim close by `exact` of the
  implementation theorem; LP3-1 `TYPE_EQV`; LP3-2 `TYPE_NOT_EQV` syntactically (r1 source maps vs raw maps) and
  `TYPE_EQV` after delta-expanding exactly the two r1 maps; axioms `[propext, Classical.choice, Quot.sound]` for both.
- **Provider build**: `lp_build.sh /root/code/KAM-inp-lp-freeze8 KAM.Planetary.Spatial.SourceBarycentric
  KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafetyNoArith
  KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafetyNoArith` — exit 0 (9070 / 9370 / 9431 jobs), no
  warning in these files. (`SourceBarycentric` = TRANSIENT stand-in, see below.)
- **Provider check** `lp_lean.sh … .drafts/freeze8/providers8_check.lean` exit 0: each scratch anchor with its exact
  seal body `by exact KAM.Provider.….<name> hn ν hν hνmax hνle A hA hAord δ hδ` elaborates; `#sameDecl` scratch vs
  provider: `TYPE_EQV THEOREM REDUCIBILITY_SAME` for both.
- **Axioms** (`#print axioms`): `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith`,
  `KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith`, both Draft8Check anchors and both
  Draft8Seal anchors: each `[propext, Classical.choice, Quot.sound]`.
- **Short names** `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py
  /root/code/KAM-inp-lp-freeze8 <the two provider modules>`: exit 0, "short-name check OK".
- **Lint** `/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-freeze8`:
  - at the draft-8 state (no Lean change): **exit 0** — "check_lean_modules: PASS (3801 Lean files …)",
    "FROZEN-ANCHOR GUARD OK", "ABI HASHES OK (177 frozen declarations …)";
  - with the providers staged (HEAD): **exit 1**, only "KAM.lean is out of date; run scripts/gen_root_imports.py
    (KAM/Root/Provider.lean)"; check_lean_modules PASS, guard OK, ABI OK. See the conflict below.

## Items not done / conflicts (STOP-and-report items)

1. **Root generator vs provider quarantine (lint exit 1 at HEAD).** `scripts/gen_root_imports.py` skips
   (`quarantined()`) only providers of anchors that are `DRAFT_SORRY` in `manifest/frozen-anchors.json`. Staged
   providers without a manifest entry would be imported by `KAM/Root/Provider.lean`, which the orchestrator's
   instruction ("no module imports them") and AGENTS rule 9 forbid. I did **not** regenerate the roots; lint therefore
   reports the root as out of date. Options for the orchestrator: (a) accept until the freeze commit (the manifest
   entries then quarantine them and lint passes), (b) keep the providers on a branch that is only merged at freeze, or
   (c) extend the generator's quarantine (e.g. to all `KAM/Provider/**` modules not yet sealed) — a scripts change
   outside this package. LP-FREEZE7R's part B will hit the same issue.
2. **Spatial provider depends on LP-FREEZE7R.** It imports `KAM.Planetary.Spatial.SourceBarycentric` (LP-FREEZE7R's
   new implementation module, not on any branch yet). I built and checked it against a **transient, uncommitted**
   stand-in at that path holding exactly the auditor's two declarations, then deleted it. On this branch alone the
   spatial provider does not build until that module lands; if LP-FREEZE7R's declarations differ from the auditor's
   text, rerun `lp_build.sh` and `providers8_check.lean`.
3. Not in scope: anything under `KAM/Frozen/`, `manifest/`; hashes (`TBD at freeze`); the statement audit.

## AUDIT FOCUS

- **The three LP3 changes only** (diffs in §3 of the proposal / §0b of the verification): especially that all three
  drift lines changed, the Diophantine premise is removed entirely, the `let T` exponent sign
  `μ ^ (-planetaryTimeExponent n)`, and that every other clause (N10, `δ/2` margin, separations, osculating outputs,
  uniqueness, Newtonian reconstruction) is untouched.
- **LP3-2 under F1:** `∀ hμ : 0 < μ` replaces `0 < μ →` (same proposition; binder named); the reconstruction maps get
  the anchor's own `hν` and `hμ`. Check against LP-FREEZE7R's final LP2 r1 text — the two must match.
- **Constants' dependence** `(n, ν, A, δ)` only; quantifier order unchanged from LP1/LP2 (constants before `μ` and
  `z₀`).
- **Exponents:** `planetaryTimeExponent n = 2/(6n²−3n+14)`, `planetaryDriftExponent n = 3·(that)/2`; `n` = number of
  planets (fast dimension) in both planar and spatial anchors (LP3-PLAN §1.3).
- **Unused normalization premises** `hνmax`, `hνle` (OD-3) — present, unused, as for LP1/LP2.
- **Manifest closure of LP3-2** grows by planar track-P files only because the frozen `PlanetaryTimeExponent.lean`
  imports them (file closure, not semantic; §4.3).
- **Stand-ins** for the r1 maps in all checks (verification §0 lists their exact text).

## Uncertainties

- Draft 8's correctness for LP3-2 is conditional on draft 7 r1 adopting exactly the auditor's F1 text; regeneration
  is scripted.
- As in draft 7 (N1), check (a) simulates module environments in one scratch file and drops the provider import; the
  provider staging check exercises the provider graph only partially (no real frozen module exists).

## Suspected errata, deviations, design signals

- **Errata in MAIN:** none new.
- **Deviations:** none from the LP3 statements (W5C-audited) except the r1 F1 convention for LP3-2 (orchestrator
  instruction; no added premise).
- **Implementation docstring nit:** the LP3 Source modules cite `LP:MAIN L15 (502–506)`; MAIN's 502–506 is Theorem 15
  (`T15`, as the anchors write).
- **Draft-7 generator drift (for LP-FREEZE7R):** `inp-lp` corrected the `spatialKeplerAxis` implementation docstring
  (and `Spatial/Model.lean`'s module docstring) after draft 7 was generated; draft 7's `gen.py` asserts the old
  docstring (`DOC_EDITS`) and fails on the merged tree. Draft-7 texts are unaffected (draft 8 reads `records.json`,
  checked byte-identical to the committed draft-7 files).
- **Commit trailer:** commits end with `Co-Authored-By: Claude Opus 5.5` (the model actually used), not the brief's
  Sonnet line.
- **Design signals:** none (no heartbeat issue; scratch files ≤ 949 lines; provider files ≤ 117 lines).
