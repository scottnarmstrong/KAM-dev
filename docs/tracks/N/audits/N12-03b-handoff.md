# N12-03b prover handoff (branch inp-n1203b, 6b0a10f; contains inp-n1203a (N12-03a, audited after hygiene fix); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- NEW `KAM/Nekhoroshev/Averaging/PicardDerivatives.lean` (~240 lines; imports PicardFamilies + Mathlib ParametricIntegral). No other file touched; KAM.lean not regenerated (lint reports it out of date: orchestrator regenerates).

## IMPORTANT: no signatures existed
`/root/code/KAM-inp/.drafts/design/N12Signatures.lean` contains NO declarations for `PicardDerivatives`
(only the final `ext_dep`). The statements below are my own, derived from the design's proof plan (§6 "Local dependence
obligation"). Please have the audit check that they are the right interface for N12-03c.

## Nodes
- `#parameter-integral`: `KAM.Nekhoroshev.hasFDerivAt_intervalIntegral_comp`: if `U τ` has derivative `U' τ z` and `F` has
  derivative `F' (U τ z)` at `U τ z` for τ∈[[0,t]], z in a neighbourhood B of x, with uniform bounds `‖F'‖≤Λ`, `‖U'‖≤M`, and
  `τ ↦ F (U τ z)` (z∈B), `τ ↦ F'(U τ x) ∘ U' τ x` continuous on [[0,t]], then
  `HasFDerivAt (z ↦ ∫₀ᵗ F (U τ z)) (∫₀ᵗ F'(U τ x) ∘ U' τ x) x`. Proof: `hasFDerivAt_integral_of_dominated_of_fderiv_le''`
  (interval version of the named Mathlib theorem), constant bound Λ·M, chain rule.
  (Derivative of a Picard iterate = id + this, applied by 03c; F' is a free derivative function, so 03c supplies `fderiv ℝ F`.)
- `#linear`: `linear_family`: for `G : ℝ → E → E →L[ℝ] E` continuous on `Icc (-a) a ×ˢ closedBall x₀ r`, `‖G‖≤Λ`
  there, `0≤a`, `0≤Λ`, `aΛ<1`, `E` complete: ∃ Y continuous on that set, `‖Y t x‖ ≤ 1/(1-aΛ)`, and
  `Y t x = id + ∫₀ᵗ (G τ x).comp (Y τ x)` on `Icc × closedBall`. Proof: contraction `voltMap` (const aΛ) on
  `PicardBase x₀ a r →ᵇ (E →L[ℝ] E)` (whole complete space, no trap needed), then extension as in 03a.
  Helpers: `voltInt, voltFun, voltMap, contractingWith_voltMap, norm_integral_voltInt_le`, etc.

## Checks
- `inp_lake_build.sh . KAM.Nekhoroshev.Averaging.PicardDerivatives`: Build completed successfully, no warnings from my file.
- `#print axioms` for both theorems: propext, Classical.choice, Quot.sound.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only noted "KAM.lean out of date"
  and long-line notices in PicardFamilies.lean (136, 318; not mine).
- No sorry/axiom/maxHeartbeats.

## Uncertainties / errata / deviations
- Interface choices above (see IMPORTANT). `linear_family` adds hypothesis `0 ≤ Λ` (needed for degenerate empty ball).
- 03c must still do the induction on iterates (Y_{m+1}=id+∫DF(u_m)Y_m, bounds ‖Y_m‖≤1/(1-q)) using the parameter-integral lemma.
- No source errata. No heartbeat design signals.

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-03b and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design (#parameter-integral, #linear: parameter derivative and continuous Volterra fixed family); (2) proofs sound (hasFDerivAt_integral_of_dominated_of_fderiv_le used with all its hypotheses discharged); no added premises; (3) hygiene (lint incl. 100-char lines, no trailing blank lines). Audit ONLY the PicardDerivatives module(s) (compare with branch inp-n1203a).
