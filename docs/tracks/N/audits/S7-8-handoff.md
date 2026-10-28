# S7-8 prover handoff (branch inp-s78, 24b6809; base inp-n68b; offloaded package run by the main orchestrator; prover on claude-12)


## Files (new)
- `KAM/Nekhoroshev/Stability/ResonantStabilityHess.lean` (163 lines): `norm_apply_le_euclid`, `contDiffOn_realPart`,
  `fderiv_realPart`, `hessBound_of_complex` (complex Hessian bound on `V_rD` => real `HessBound` on `U_rD`,
  `K:real-restriction`), `freqLipschitz_of_complex` (`FreqLipschitz (cpx D) r (√n M) h`, via `lipschitz` and Hessian symmetry).
- `KAM/Nekhoroshev/Stability/ResonantStabilityCore.lean` (~172 lines): `prop2_core`: the transfer step. Premises are
  the *typing data* of a conjugacy `Ψ` (holomorphy, maps-to, reality, symplecticity, `H∘Ψ = h+g+f_*`), the RS data of
  `g, f_*`, (T1) with `d ≤ ρ'/4`, (T2), and the arithmetic time hypothesis `hT`; it applies `resonant_lemma2`
  (radius `r/2`, `δ' = mr/8`) and `transfer` (`Nrm = euclid`, `ϱ = r/2 - ρ'`, `adm I t := I = I₀ ∧ (Λ=univ ∨ time bound)`).
- `KAM/Nekhoroshev/Stability/ResonantStability.lean` (~400 lines): `resonant_prop2` (signature verbatim), with case
  lemmas `prop2_caseA` (κ ≥ 6, `normal_form` + `preimage_nfl`), `prop2_caseB` (κ < 6, Ψ = id), `prop2_caseC`
  (Λ = ℤⁿ, Ψ = id, g = f, f_* = 0, η = 0), bundled hypotheses `Prop2Hyp`, numerics `Prop2Hyp.nums`, small helpers
  (`reMap_id`, `reMap_eq_of`, `euclid_re_le`, `mem_realStrip_of_mem`, `prop2_idData`).
No change to any signature; `resonant_prop2` is exactly the signature-file statement.

## Approach
As Steps p2-red .. p2-concl. Case A: `normal_form` (D := cpx D, L = √n M); `g` bounded by `|g₀| + 16cε² ≤ 5ε/4`
(`projections` twice for `homRes = P_Λ T_K`, `wbound_add`), `η = e^{-κ/6} ε ≤ ε/2`, `ζ = 2ε`; T1 from normal_form (c)
with `d = ρ'/4`, `√n q K ε/α ≤ ρ'/4` from `hc1`, (b); T2 = `preimage_nfl`. Case B: `η = ε`, `e^{κ/6} ≤ 3`.
Time arithmetic: `|t| 12 Ω η ≤ s̃ m (r/2)²`.
Design signal: the first monolithic version of `resonant_prop2` exceeded default heartbeats (single declaration);
fixed by splitting into `Prop2Hyp.nums`, three case lemmas and a 10-line assembly (no heartbeat options).

## Checks
- Gate build `KAM.Nekhoroshev.Stability.ResonantStability{Hess,Core,}`: success, no `sorry`; only unused-variable linter
  warnings (`hδ`, `hd0` in `prop2_core`).
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated file, not edited, per rules); module check PASS,
  frozen-anchor guard OK, ABI hashes OK.
- No `set_option`, no sorry/axiom. Files ≤ 400 lines.

## Uncertainties / errata / deviations
- None new. Time condition in `adm` carries `I = I₀` so that `Ω` (a bound only on the ball about the given `I₀`) is used only at `I₀`.
- Extra hypotheses of `prop2_core` (`hss : s' ≤ s`, `hε0`) are typing/standing data, not conclusion-shaped.
- Blueprint's note that K:real-restriction is an unlisted step is realised by `hessBound_of_complex`.

## Axioms
`#print axioms KAM.Stability.resonant_prop2`: [propext, Classical.choice, Quot.sound].
Final gate build (before a whitespace-only line-wrap edit, re-checked with `lake env lean`: 0 errors) succeeded; lint: only long-line notes (now fixed) and the expected "KAM.lean out of date".

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row S7-8 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md; signatures .drafts/design/NPart67Signatures.lean; blueprint-N p7 resonant-prop2): (1) statement = design signature and blueprint (Proposition 2, resonant stability), consuming N6-8, S7-6, S7-3, S7-4 as designed, no added premise; (2) proof sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Nekhoroshev/Stability/ResonantStability*.lean (compare with branch inp-n68b).
