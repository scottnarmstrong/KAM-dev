# N11-L1 prover handoff (branch inp-n11l1, 8f924ce0; offloaded package run by the main orchestrator)


## Files
- NEW `KAM/Nekhoroshev/Partial/EnergyIdentity.lean` (429 lines, all lines <= 100 cols), branch `inp-n11l1`, committed.
  No other file touched (KAM.lean not regenerated: `lint_sources.sh` prints "KAM.lean is out of date" only because of the new module; orchestrator must run gen_root_imports.py).

## Important: no signed declarations
`N11Signatures.lean` contains NO declaration for N11-L1 (nor does the design row beyond "omega-free identity and
transverse pairing estimate"). I therefore designed the exports from the graph nodes `stepN:p11:ef-id` (eq:lie) and
`stepN:p11:ef-C` of blueprint-N/parts/p11c-partial-stability.tex L101-107. L2 (Energy.lean) must be written against
these statements; please audit them (they are UNSIGNED).

## Declarations (public)
- `ext_class_liftFast` : `RealFastConvex b.Ic R m M h → ext_class b R s (liftFast h)`.
- `ext_class_add` : sum of `ext_class` functions is `ext_class`.
- `energy_identity` (ef-id, eq:lie): for an `ExtOrbit b r (liftFast h + g + fs) J y`, `τ ∈ J`:
  `HasDerivAt (fun t => fs (extCx (y t))) (∑ i, dtheta i fs z * freq h (fastAction z) i + extBracket b.c fs g z) τ`, `z = extCx (y τ)`.
  (Equivalent to ∂θ fs·ω = F' − {fs,g}_c; no bound on ω.)
- `energy_identity_re`: the same for the real part, with `KAM.frequencyMap h (fastAction (y τ))` and `(dtheta i fs z).re`.
- `transverse_pairing` (ef-C): with `P` an `IsOrthProj` fixing `resSpan Λ`, `hgb : WBound g ζ`, `hsupp`, `0, t₁ ∈ J`,
  sup-hypotheses B₁ (|Re {fs,g}|), B₂ (euclid of Re ∂θ fs), B₃ (euclid(ω(I(τ))−ω(I(0)))), B₄ (euclid(P ω(I(0)))) on `uIcc 0 t₁`:
  `|ω0 ⬝ᵥ (ΔI − P ΔI)| ≤ |Re fs(y t₁) − Re fs(y 0)| + |t₁|*(B₁ + (B₃+B₄)*B₂)`, `ΔI = fastAction (y t₁) − fastAction (y 0)`.
  Matches the displayed bound of ef-C: `C ≤ |F(t*)−F(0)| + |t*|(sup|{f,g}| + MΔ sup‖∂θ f‖ + 5/4 δ sup‖∂θ f‖)` with B₃ = MΔ, B₄ = 5δ/4.
  Proof avoids Π⊥ pointwise: Φ = (ω0−Pω0)·I + Re fs∘y has derivative Re{fs,g} + (ω(I)−ω0+Pω0)·∂θ fs (uses `real_system_resonant`
  for P ∂θ g = ∂θ g), then mean value on `uIcc 0 t₁` (two-sided time handled).
  The bounds B₃ (mean-value from Hessian) and B₄ (≤ 5δ/4 from NearResonance), B₁ (bracket lemma at the half-radius tube), B₂ (real_system_bounds) are left to L2 as hypotheses (they are estimates, not conclusions).
Private helpers: wvec, wvec_add, apply_wvec_self (antisymmetry), fastCLM, freq_real, fderiv_hamiltonian, hasDerivAt_orbit, hasDerivAt_fast, ...

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-n11l1 KAM.Nekhoroshev.Partial.EnergyIdentity`: Build completed successfully, no warnings in my file.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only "KAM.lean is out of date" (generated file, not edited by rule).
- `#print axioms` of energy_identity, energy_identity_re, transverse_pairing, ext_class_liftFast, ext_class_add: [propext, Classical.choice, Quot.sound].
- No maxHeartbeats, no sorry/axiom, no EuclideanSpace; all names unique in KAM (grepped).

## Uncertainties / errata / deviations
- Unsigned exports (above): L2's consumer statement may need adjusting.
- The identity is stated in complex form (dtheta/freq) and, separately, real form; reality of ω on real points is proved (`freq_real`).
- Blueprint: no defect found. Note ef-C uses "Π self-adjoint" ; here via `IsOrthProj.symm` (Part 7 carrier).
- Deviation: `transverse_pairing` states C through the dual form `ω0⬝(ΔI−PΔI)` instead of Π⊥ΔI; equal for `P` orthogonal projection.

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-L1 (omega-free identity, transverse pairing estimate) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. The handoff states a deviation: transverse_pairing states C through the dual form omega0 . (dI - P dI) instead of Pi_perp dI (equal for P an orthogonal projection): check against the signature and the blueprint p11c L101-107 (stepN:p11:ef-C) and that L2's consumption is unaffected. Audit ONLY KAM/Nekhoroshev/Partial/EnergyIdentity.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
