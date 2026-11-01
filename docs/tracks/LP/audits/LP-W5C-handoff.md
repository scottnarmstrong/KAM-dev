# LP-W5C: combined audit handoff for LP3-PS + LP3-SP-SAFE + LP3-SRC, the LP3 headline theorems (sharp strong-AMD safety with NO arithmetic hypothesis, planar LP3-1 and spatial LP3-2) and their source-carrier restatements

Branch `inp-lp-w5c` (worktree `/root/code/KAM-inp-lp-w5c`) = `inp-lp-lp3src` (LP3-PS e032c059, LP3-SP-SAFE d39c3195,
LP3-SRC 402de5f7) + `inp-lp-w5b` + `inp-lp`. Nothing in track LP is frozen.

**Package diff:** `git diff inp-lp-w5b HEAD -- KAM` (11 files, about 1,510 lines). After W5B lands, `git diff inp-lp HEAD
-- KAM` shows the same. It covers:
- `KAM/Planetary/StrongAMD/Nek/PlanarSafety{,/Orientation,/Prograde,/Main,/Source}`;
- `KAM/Planetary/Spatial/Nek/SpatialSafety{,/Orientation,/Aligned,/Main,/Source}`;
- the regenerated root.

**Prover handoffs:** `docs/tracks/LP/audits/LP3-{PS,SP-SAFE,SRC}-handoff.md`. Each includes a token diff of the new
headline type against its template. **Briefs:** `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP3-{PS,SP-SAFE,SRC}.md`.

**Plan:** `docs/tracks/LP/lp3/LP3-PLAN.md` §1.1–§1.4 (the target statements and what is weaker or stronger), and §3.

**Templates:** all audited and landed.
- LP1: `StrongAMD/PlanarSafety/*` (audit LP-PS-1).
- LP2: `Spatial/SpatialSafety/*` (audit LP-W4E-1).
- The (b) restatements `PlanarSafety/Source.lean` and `SpatialSafety/Source.lean` (LP-SRC; LP-W4E-1).

**Suppliers:** planar audited (W5A); spatial in W5B.

**Rulings:** D59 (`git show main:docs/DECISIONS.md`). OD-11 (b), with the spatial restatement through
`spatialSource*`. OD-3 keeps `hνmax`, `hνle` in the normalized forms. The exponents use the `planetary*` names
(plan O-1).

## Orchestrator checks (kam-lp)

- `lp_build.sh` of the 10 modules: built. `lp_lint.sh`: exit 0. Short-name check: OK.
- `#print axioms` of `lp3_planar_strongAMD_safety{,_normalized}`, `lp3_spatial_strongAMD_safety{,_normalized}` and the
  four `…_source{,_general}` theorems: `[propext, Classical.choice, Quot.sound]` (prover checks).

## REPORT FORMAT

Three sections (LP3-PS, LP3-SP-SAFE, LP3-SRC), each with a verdict, then a combined verdict.

## AUDIT FOCUS

**Statement fidelity, the main point.** Each LP3 headline type must equal its template with exactly three changes:
1. The data `γ τ`, `hγ hτ` and the Diophantine premise are removed.
2. `T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))`.
3. `μ ^ planetaryDriftExponent n` replaces `√μ` in the action, axis and AMD lines.

Everything else must be token-identical. That covers the premises, all 13 conclusion clauses, `let T`, the constant
order (every constant before `μ` and `z₀`, now depending on `(n, ν, 𝒜, δ)` only) and both N10 inequalities.

Verify the prover token diffs independently. There must be **no** prograde, inclination, nonzero angular momentum,
alignment, secular or arithmetic premise.

**Proof structure:**
- `hstop` must be discharged by the audited suppliers `lp_stopped_drift_nek_hstop` (planar) and
  `spatial_stopped_drift_nek` (spatial).
- The drift-scale-generic re-statements of the LP1/LP2 safe-state predicates must unfold correctly:
  `nekPlanarState/Sol` in the planar case, and the LP2 predicates with a parameter `ρ` in the spatial case.
  Neither changes the landed LP1/LP2 files.
- Orientation: the planar reflection, and the spatial rotation alignment with `L ≠ 0` derived.
- The constants: `AΛ` absorbs `B₀^{b_n}`, with `c = B₀^{−a_n}` and `T₀ = 1`. Check the N10 inequalities for the
  `min` constants.

**LP3-SRC:** each of the four (b) theorems must equal its template (§3b planar, §3d spatial after SRCB2) with only the
three LP3 changes. It is proved from the LP3 theorem.

**What is weaker (plan §1.4):** the time exponent is `a_n = 2/(6n²−3n+14)` instead of `1/(2(τ+1))`, and the drift is
`μ^{b_n}` instead of `√μ`. What is stronger: there is no arithmetic hypothesis, and the theorem is uniform over the
whole compact sharp sublevel. Confirm that nothing else changed.

## Source defects, deviations, design signals

No MAIN defect reported. Deviations: the generated root, and the parallel drift-scale-generic predicates
(`nekPlanarState/Sol`; the LP2 predicates with parameter `ρ`) instead of edits to landed files. No design signals.
