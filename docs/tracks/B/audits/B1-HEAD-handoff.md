# Handoff B1-HEAD (branch inp-b1head)

## Files (new, all under KAM/EffectiveStability/)
- Torus.lean (136 lines): `torus_confinement`
- Oscillator.lean (146): `oscillator_confinement`
- ObservableTransfer.lean (132): `torus_observable_transfer`, `oscillator_observable_transfer`
- Examples.lean (58): `torus_confinement_example`, `oscillator_confinement_example`

## Statements
`torus_confinement` and `oscillator_confinement`: byte-identical (docstring, binders, conclusion) to
`docs/tracks/B/freeze/elaboration-draft-1.lean.txt` (checked by substring test of the full text up to `sorry`). No signature change.
Corollaries: all headline binders, then `(A : (Fin n → ℝ) × (Fin n → ℝ) → Fin m → ℝ) (L : Matrix (Fin m) (Fin n) ℝ) (d : Fin m → ℝ)`
and `hA` (torus: `∀ w, (∀ j, |w.2 j| ≤ b j) → ∀ i, |A (Ψ w) i - (L.mulVec w.2) i| ≤ d i`;
oscillator: `w ∈ oscClosed b → ... (L.mulVec (oscAct w))`), inserted just before `w₀`. Conclusion = the headline conclusion
(same T₁, z) ∧ `∀ t, |t| ≤ T → ∀ i, |A (z t) i - A (z 0) i| ≤ 2 * d i + |t| * ∑ j, |L i j| * η j`.
Examples:
- `torus_confinement_example (T) (hT : 0 ≤ T) (w₀) (hw₀ : ∀ j, |w₀.2 j| ≤ 1) : ∃ z, z 0 = w₀ ∧ ∀ t, |t| ≤ T → ∀ j, |(z t).2 j - w₀.2 j| ≤ 0`
  (Ψ = Ψinv = id, R = 0, H = ∑ w.2 j², η = 0, V = univ, a = 1, b = 2, ε = 1).
- `oscillator_confinement_example (T) (hT : 0 ≤ T) : ∃ z, z 0 = 0 ∧ ∀ t, |t| ≤ T → ∀ j, oscillatorAction (z t).2 (z t).1 j = 0`
  (harmonic oscillator, w₀ = 0, a = 0, b = 1). Both hold for all T ≥ 0, so T = 0 is covered.

## Approach
Torus: D = cyl(b+ε); K = H∘Ψ is C² on D, F = X_K is C¹; angle-periodicity of K on open D gives periodicity of dK (fderiv_comp_add_right +
EventuallyEq.fderiv_eq); drift via `fderiv_angle_eq_of_eventuallyEq`; `exists_confined_solution_periodic`; z = Ψ∘w by `hasDerivAt_comp_chart`;
uniqueness by `gen_uniqueness_inter` (W = V, J₂ = Ioo(-T₁,T₁)); bounds via hΨinv on D. Oscillator: same with D = osc(b+ε),
`exists_confined_solution_compact` with g = oscAct, {|oscAct| ≤ b} = oscClosed b, drift via `fderiv_oscAct` + `bracket_action_eq_of_eventuallyEq`.
Corollaries: obtain headline, then `observable_transfer_bound` with J₀ = w₀.2 (resp. oscAct w₀), J = (Ψinv (z t)).2 (resp. oscAct of it); hA applied
at w₀ (a ≤ b from margin) and at Ψinv (z t) (≤ a + ηT ≤ b), using Ψ(Ψinv(z t)) = z t.

## Checks
- `b_build.sh` Torus, Oscillator, ObservableTransfer, Examples (in order): all "Build completed successfully", no warnings.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS (4489 files), 25 tests OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- `#print axioms` (untracked scratch .drafts/axioms_scratch.lean), all six declarations: [propext, Classical.choice, Quot.sound].
- No maxHeartbeats, no sorry/axiom, all files far under 1500 lines.

## Design signals / uncertainties / errata
None. No heartbeat issues; each module built in ~2 s. No source defects found. No deviations.

## AUDIT FOCUS (kam-b1)
Track B (program B, overnight D71; nothing frozen). The two headline theorems are the B0 text audited in
docs/tracks/B/freeze/STATEMENT-REVIEW-1.md (PASS WITH NOTES) and given in docs/tracks/B/FREEZE-PROPOSAL.md /
freeze/elaboration-draft-1.lean.txt. Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B1-HEAD.md. Dependencies (already
audited, PASS WITH NOTES): B1-CORE, B1-TRANSFER (docs/tracks/B/audits/). Check: (1) BYTE-identity of
`torus_confinement` and `oscillator_confinement` (docstring through `:= by`) with the elaboration file; (2) the
proofs use only the stated premises, never assume the existence interval or the confinement conclusion (plan §7
Brief 2 reviewer duty: trace how Torus/Oscillator call the first-exit/continuation engine), periodicity of the chart
field derived correctly from `hHΨ`/`hRper` on the open translation-invariant domain, the uniqueness clause covers
every V-solution on an order-connected I ∋ 0; (3) corollaries: distinct names, faithful plan (B1-transfer),
no conclusion-shaped premise; (4) examples genuinely instantiate the headlines (nonvacuity; T = 0, η = 0, zero
action); (5) module hygiene (AGENTS rules 3, 4, 7), names; (6) axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
