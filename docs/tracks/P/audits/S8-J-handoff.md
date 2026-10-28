# S8-J prover handoff (branch inp-s8j, 803cd10; off inp (S8-A, S8-M on inp); offloaded package run by the main orchestrator; prover on claude-10)


**Files:** new `KAM/Planetary/SecularForm/ModelTransfer.lean` (167 lines). Nothing else touched.

**Proved (signatures verbatim from P810Signatures.lean; only a whitespace line break inside the
`same_jets_on` statement to respect the 100-column lint):** `same_jets_on`, `same_jets`,
`birkhoff_transfer`, `same_jets_transfer`. Helpers: `mem_slowDom_iff'`, `realDisc_subset_slowDom`,
`jets_core`.

**Approach.**
- `jets_core`: on `realDisc D a r` (r from `perturbation_analytic`) the moving and fixed secular
  functions differ by `modelDelta D I` (S8-M `identification`, integrability from S8-A). So the two
  slow functions agree up to an additive constant near the point; `iteratedFDeriv (k+1)` is unchanged
  via `iteratedFDeriv_succ_eq_comp_right` and `fderiv_add_const` (no smoothness needed).
- `same_jets_on`: the functions of `I` are eventually equal near `x.2.1` (realDisc open), then
  `EventuallyEq.iteratedFDeriv`. `same_jets`: apply `jets_core` at `(0, action a, 0)`.
- `birkhoff_transfer`: unfold the frozen def; integrability via `hInt`, average shift via `hAvg`
  (the disc `delta ≤ r0` gives the hypotheses on the smaller discs).
- `same_jets_transfer`: `birkhoff_transfer` with `identification` discharging both premises.

**Checks.**
- `inp_lake_build.sh /root/code/KAM-inp-s8j KAM.Planetary.SecularForm.ModelTransfer`:
  `Built KAM.Planetary.SecularForm.ModelTransfer`, no warnings in my file.
- `scripts/lint_sources.sh`: no over-long lines; `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK`. Only message: `KAM.lean is out of date` (generated; not edited, orchestrator regenerates).
- `#print axioms` of all four: `[propext, Classical.choice, Quot.sound]`.

**Deviations / notes.**
- Imports: S8-A (`Analytic`), S8-M (`Momentum`), frozen `HasSecularBirkhoffForm`. I did NOT import
  `Symmetry` (S8-Y): it declares `SecularForm.planetBlock_assemble`, which collides with the same name in
  `AnalyticReal` (import error). `mem_slowDom_iff'` re-proves the chart-domain characterization locally.
  **Erratum-like note for the orchestrator:** `AnalyticReal.planetBlock_assemble` and
  `Symmetry.planetBlock_assemble` clash, so no module can import both S8-A and S8-Y until one is renamed
  (a later package, e.g. S8-4/S8-Q, will hit this).
- Module is smaller than the design estimate (~350) since smoothness was not needed.
- No heartbeat or line-cap issues. No suspected source errata.
- Uncertainties: none.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S8-J and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements = design signatures exactly (same_jets_on, same_jets, birkhoff_transfer, same_jets_transfer; the same_jets_on line break must be whitespace-only); (2) proofs sound (S8-A, S8-M and the frozen HasSecularBirkhoffForm consumed as designed; no frozen file edited); no added premises; (3) hygiene incl. AGENTS.md ambient-type rule (no EuclideanSpace) and scripts/lint_sources.sh. Audit ONLY KAM/Planetary/SecularForm/ModelTransfer.lean.
