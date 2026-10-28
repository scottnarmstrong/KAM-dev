# P12-A prover handoff (branch inp-p12a, 3e1ba0a; off inp; offloaded package run by the main orchestrator; prover on claude-10)


**Files:** new `KAM/Planetary/PlanarAssembly/Geometry.lean` (~326 lines). Nothing else touched (KAM.lean not edited).

**Declarations (verbatim from P1213Signatures.lean, namespace `KAM.Planetary.PlanarAssembly`):** `kepler_h`, `action_center`,
`compact_cell`, `compact_cell_isCompact` (stepP:p12:ft-cpt), `forward_tube` (bpP:p12:forward-tube). The remaining
signature declarations (collar, product_chart, fast_diffeo, radius_choices, birkhoff_mono_radius = P12-B; total_chart,
perturbation, ... = Data) are not in this package's row and were not touched. The Tube prelude was not copied (the real
`axisMax` etc. live in KAM.Planetary.Newtonian.Tube; Geometry does not need them).

**Approach:** compactness: closed (continuity of fast/slow coordinates) and contained in an explicit box; coordinate
bound `|x| ≤ 1+δ` from `Γ ≤ δ`. forward_tube: δ0 = min Λ_i/4; compact cell at δ0 lies in `poincareProdDom 2`;
`IsCompact.uniformContinuousOn_of_continuous` (via `analyticOnNhd_poincareProd`) gives δ1 for ε = ζ; δ = min δ0 (δ1/2) (δ1²/4).
Fast angles reduced to [0,2π) by `k = ⌊fast w.1 / 2π⌋`, `w' = w - fastShift k` (`planetBlock_shift`, `poincareProd_lattice`);
`circularPoint_eq_poincareProd` identifies the circular point with the chart of `assemble Λ φ 0 0`, which is within δ1 of w'.
Result: domain, norm bound `< ζ`, and tube membership with the same angle φ_i = fast w.1 i/(2π).
Imports: Mathlib, Poincare.Product, Poincare.Tube, frozen CircularTube/FastShift defs only (no theorem anchors/providers).

**Checks:**
- `LEAN_NUM_THREADS=1 lake env lean` on the file: no errors/warnings.
- gate: `inp_lake_build.sh /root/code/KAM-inp-p12a KAM.Planetary.PlanarAssembly.Geometry` → "Build completed successfully (9112 jobs)" (only warning is the pre-existing one in KAM/Kepler/Mass.lean:524).
- `scripts/lint_sources.sh`: no forbidden patterns, no long lines, check_lean_modules PASS, frozen guard OK, ABI hashes OK. It prints
  "KAM.lean is out of date; run scripts/gen_root_imports.py" — expected (new module; rule 10 forbids me editing KAM.lean; the orchestrator must regenerate).
- `#print axioms` of `forward_tube` and `compact_cell_isCompact`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / design signals:** none; no heartbeat issues. No suspected errata, no deviations from signatures
(binder-for-binder copy; the only additions are private helper lemmas).

AUDIT FOCUS (design docs/tracks/P/design/P1213-LEAN-DESIGN.md row P12-A and node table; audits DESIGN-P1213-design-audit-{1,2}.md; signatures .drafts/design/P1213Signatures.lean): (1) statements = signature file exactly (kepler_h, action_center, compact_cell, compact_cell_isCompact, forward_tube); (2) proofs sound (Product, Poincare/Tube circularPoint_eq_poincareProd, frozen definitions incl. the FROZEN KAM.Planetary.fastShift, Mathlib compactness consumed as designed); no added premises; (3) hygiene (no EuclideanSpace). Audit ONLY KAM/Planetary/PlanarAssembly/Geometry.lean.
