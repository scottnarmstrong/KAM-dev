# LP-W4E: combined audit handoff for LP-SP-SAFE + LP-SP-SRC (parts A and B, with SRCB2): the spatial theorem LP2 (MAIN Theorem 19) and its source-carrier restatement

Branch `inp-lp-w4e` (worktree `/root/code/KAM-inp-lp-w4e`) = `inp-lp-w4d` (W4D, under audit) + `inp-lp-spsrcb2`
(SP-SAFE c9553935, SP-SRC part A 14a1b9e0, part B 6e84c27a, SRCB2 1f078521) + `inp-lp` (W4C merged, landing
requested). Nothing in track LP is frozen.

**Package diff:** `git diff inp-lp-w4d HEAD -- KAM` (9 files, about 1,460 lines). It covers:
- `KAM/Planetary/Spatial/SpatialSafety.lean` and its parts `SpatialSafety/{Constants,Orientation,Bridge,Aligned,Main}`;
- `SpatialSafety/Source.lean`;
- `KAM/Planetary/Spatial/SourceCarrier.lean`;
- the regenerated root.

After W4D lands, `git diff inp-lp...HEAD -- KAM` shows the same.

**Prover handoffs:** `docs/tracks/LP/audits/LP-SP-SAFE-handoff.md`, `LP-SP-SRC-handoff.md`, `LP-SP-SRCB-handoff.md` and
`LP-SP-SRCB2-handoff.md`. **Briefs:** `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-SP-{SAFE,SRC,SRCB2}.md`.

**Paper-level statement reviews already done** (independent Opus; they do not replace this audit):
- `docs/tracks/LP/freeze/STATEMENT-REVIEW-4.md`: §3c LP2 passes for fidelity; R4.1 was blocking for §3d.
- `STATEMENT-REVIEW-5.md`: §3d after R4.1 (A), PASS WITH NOTES. It ran no Lean; this audit's replay and axiom check
  are the first independent ones.

**Source:** `docs/tracks/LP/source/MAIN.md` Theorem 19 (599–603), Lemmas 14, 16 and 18, and §1 (6)–(9) with `d = 3`,
read with `source/AMENDMENTS.md` (N2, N6, N7, N10, N12). The planar twins (landed and audited) are
`KAM/Planetary/StrongAMD/PlanarSafety/*`, `StrongAMD/SourceCarrier.lean` and `PlanarSafety/Source.lean`.

## Orchestrator checks (kam-lp)

- `lp_build.sh` of the 8 modules: built. `lp_lint.sh`: exit 0. Short-name check: OK.
- `#print axioms` of `lp2_spatial_strongAMD_safety{,_normalized,_halfInteger}` and `lp2_spatial_strongAMD_safety_source{,_general}`:
  `[propext, Classical.choice, Quot.sound]` (prover checks; the orchestrator re-checked LP2).
- Every module docstring carries the SPEC §4 sentence.

## REPORT FORMAT

Two sections, then a combined verdict:
- **LP-SP-SAFE** (LP2);
- **LP-SP-SRC** (carriers part A, and the restatement B as amended by SRCB2).

## AUDIT FOCUS

**LP-SP-SAFE (LP2):**
- **No added premise.** Check the binder list against the brief and FREEZE-PROPOSAL §3c. In particular there is no
  prograde, small-inclination, nonzero total angular momentum, secular-confinement, alignment, normal-form or
  stopped-action premise. The only orientation premise, `L = |L| • e₃`, lives in the internal
  `spatial_safety_of_aligned`, which `lp2_…` discharges by a constructed rotation. `L ≠ 0` is derived.
- **Rotation invariance (`Orientation`).** Every clause of the safe state is invariant, including the osculating
  `|𝐞^osc − 𝐞|`, and the uniqueness predicate is transported with `Rᵀ` in both directions.
- **`Bridge`.** It joins the SP-LIFT and SP-NRR interfaces. The two writings of ball (47) are equal. The chart
  Hamiltonians `spLiftChartHam` and `lpChartHamNM` give equal fields on the open `spLiftChartSafe`.
  `fast (w 0).2 = Λ z₀`.
- **Constant order.** All constants, `Aelem` and both N10 inequalities are chosen before `μ`, `z₀`.
- **`hstop` discharge.** `SpatialStoppedOn` is CONF's antecedent by `rfl`. Both time directions use `uIcc 0 t`. The
  time bound matches NRR's.
- **Conclusions** vs MAIN (7)–(9) + L16 (no orbit crossing, no collision, Newtonian reconstruction with masses
  `(1, μν)`).

**LP-SP-SRC (carriers and the (b) restatement):**
- Part A: the carriers are exactly `SpatialNegativeEnergy` (canonical) and SP-OSC's `SpatialOscPhase` (osculating).
  Every source definition is a thin `rfl` restriction. Check the characterization theorems, including the
  non-strict `e ≤ 1` on the canonical carrier, which allows radial orbits.
- Part B with SRCB2: both theorem types equal STATEMENT-REVIEW-4's R4.1 (A) text, which review 5 confirmed byte for
  byte. No `spatialKeplerAxis/Action/EccVector` is applied to a physical state; only sign conditions inside guarded
  carrier predicates use the raw energy and osculating formulas (R5.1). Check the dependent binders `h₀ → hch →
  orderedStrongThreshold` and the single `∃ hs`.

**Known open documentation items (please confirm or extend):**
- R4.6: two docstring misnomers, at `KAM/Planetary/Spatial/Elements.lean:35` and `Model.lean:21` (landed files,
  outside this diff). The orchestrator will fix them in this package's notes round.
- R4.2: under OD-11 (b), the anchor name for the §3d surface is an owner choice.

## Source defects, deviations, design signals

The provers report no MAIN defect for `d = 3`. Deviations:
- the generated root;
- `exists_spatialBudget_radius`, a spatial copy of the planar budget lemma;
- `SpatialSafeState/Sol` helper definitions that unfold to the statement clauses;
- the duplicate LIFT/NRR names, joined in `Bridge` rather than renamed.

No design signals: every module builds in under 30 s under the 4 GB cap.
