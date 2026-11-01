# LP3-CELL handoff

## Files
New: `KAM/Planetary/StrongAMD/Nek/Cells.lean` (~230 lines). Generated: `KAM/Root/Planetary.lean` (via `gen_root_imports.py`). Commit 4d6256d1 on `inp-lp-lp3cell`. No existing file edited. No MAIN lemma transcribed (infrastructure; docstring says so).
Imports: sealed frozen `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` (D58), `KAM.Planetary.Exponential.{Hamiltonian,Perturbation,KeplerData}` (no provider import, checked), `Nek.Kepler`.

## Declarations (namespace `KAM.Planetary.StrongAMD`, generic in `k`; `hn : 2 ≤ n`, `hk : 1 ≤ k`)
1. `PartialConvexConclusion h G D μ P : Prop`: verbatim transcription of the frozen conclusion after `IsPartialPerturbation G' D ρ P` (∀ C>0, ∀ z, IsSolutionOn … → innerCore → ∀ t ∈ Icc 0 (min C …), slow premise → drift ≤ μ^b/2).
2. `cell_threshold_uniform` (statement 1): for `ι` a `Fintype`, cells `G G' D ρ`, constants `gp mp Mp` (for `h`) and `gn mn Mn` (for `-h`), all frozen premises for each `j` and for `h`, `-h`: `∃ μ₀ > 0, ∀ μ ∈ (0,μ₀), ∀ j, ∀ P, IsPartialPerturbation (G' j) (D j) (ρ j) P → PartialConvexConclusion h (G j) (D j) μ P ∧ PartialConvexConclusion (-h) (G j) (D j) μ (-P)`. `IsPartialPerturbation … (-P)` follows from `… P`: used `KAM.Planetary.isPartialPerturbation_neg_of` (Exponential/Perturbation.lean:199). Helper `exists_pos_le_forall_fintype`.
3. `isSolutionOn_reverse_neg` (statement 2): `IsSolutionOn (degenerateHamiltonian (realPart h) (fun _ x => (P (complexifyPhase x)).re) μ) {I | fast I ∈ G} (Icc t 0) w → IsSolutionOn (degenerateHamiltonian (realPart (-h)) (fun _ x => ((-P) (complexifyPhase x)).re) μ) {I | fast I ∈ G} (Icc 0 (-t)) (fun s => w (-s))`. Any `t`; reuses `hamiltonianVectorField_neg`.
4. `cell_drift_two_sided` (statement 3): same premises as 2; `∃ μ₀>0, ∀ μ∈(0,μ₀), ∀ j P, IsPartialPerturbation … → ∀ w t, |t| ≤ μ⁻¹ exp(μ^{-partialTimeExponent n}) → IsSolutionOn (h,P-field) {fast ∈ G j} (uIcc 0 t) w → fast (w 0).2 ∈ innerCore (G j) (μ^b) → (∀ u ∈ uIcc 0 t, slow pair ∈ innerCore (D j) (μ^b)) → ‖fast (w t).2 − fast (w 0).2‖ ≤ μ^b/2`.
5. `kepler_cell_drift` (statement 4): `∃ ρ₀>0` (depends on `ν,U` only: `hν`, `U` compact, `U ⊆ chamber ν`), `∀ {ι : Type} [Fintype ι] G G' D ρ`, domain premises, `G' j ⊆ cthickening ρ₀ U`, `ρ j ≤ ρ₀`, `∃ μ₀>0, …` the statement-3 conclusion for `h = planetaryKeplerC ν`. Fast premises from `lp3_kepler_data` (same `g m M` for `h` and `-h`).

## Deviations / choices
- Hypothesis in 3, 4 is `IsSolutionOn … (uIcc 0 t) w` (two-sided `HasDerivAt` on the closed interval) rather than "on an open interval containing"; this is weaker hence the theorem is stronger, and equals the frozen orbit premises transported to `uIcc 0 t`. Also covers `t = 0` trivially (needs only `μ>0`).
- Statements 3, 4 are existential in `μ₀` (not a conditional helper taking `μ₀`); they still carry the distinct, non-source names.
- Statement 4's `ι : Type` (universe 0) in the `∀ {ι}`.
- Constants for `h` and `-h` are separate (`gp/gn` etc.) to match what the frozen theorem needs; the Kepler instance supplies equal constants.

## Checks
- `lp_build.sh /root/code/KAM-inp-lp-lp3cell KAM.Planetary.StrongAMD.Nek.Kepler` then `… KAM.Planetary.StrongAMD.Nek.Cells`: `✔ Built KAM.Planetary.StrongAMD.Nek.Cells`, "Build completed successfully (9301 jobs)"; no warnings from Cells.lean.
- `#print axioms` (via `lp_lean.sh` on `.drafts/ax_cells.lean`): all four theorems `[propext, Classical.choice, Quot.sound]`. No `sorryAx`: the sealed anchor is complete.
- lint: `lp_lint.sh` exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK)
- `main_shortname_check.py … Cells.lean`: exit 0 ("short-name check OK")

## AUDIT FOCUS
- `PartialConvexConclusion` against the frozen conclusion text (note `μ^(-partialTimeExponent n)`, `min C …`, and `Icc 0 t` slow premise).
- Quantifier order in 2 and 4: `μ₀` after all cell data, before `μ, j, P`; in 5 `ρ₀` before the family.
- Sign convention of the reversed field for `(-h, -P)`: `-P` enters as `((-P) (complexifyPhase x)).re`, matching the frozen application to `-P`.
- Slow-pair premise is tested on the whole `uIcc 0 t` (backward: via `-u`).
- Open/convex/collar premises for each cell are hypotheses (supplied by the callers).

## Not done / errata / design signals
Nothing omitted. No source defects found. No heartbeat issues; file ≈230 lines.
