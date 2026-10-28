# N6-8a prover handoff (branch inp-n68a, 7359a1c; contains inp-n67 (N6-1..N6-7, audited); offloaded package run by the main orchestrator; prover on claude-12; session 1 of package N6-8)


Branch `inp-n68a`, worktree `/root/code/KAM-inp-n68a`. `NormalForm` is NOT written (session 2).

## Files (all new, each ≤ 333 lines; no `maxHeartbeats`, no `sorry`/`axiom`)
`Arith` facade → `ArithBase` (schedule, Step 0, Cases A/B, floor facts, (b)), `ArithInduct` ((6.1), (6.2),
induction constant, decomposition norm, (a)), `ArithDisp` (displacement sums, closed-form radii,
schedule positivity/monotonicity). `Steps` facade → `StepsSeq` (`NFHyp`, `nfState`, `NFInv`,
decomposition), `StepsInduct` (`nf_hyp`, `nf_inv_succ`, `nf_inv_all`), `StepsOut` (per-step properties,
chain identity, displacement sums, final state), `StepsCaseB` (reality, Case B). All under
`KAM/Nekhoroshev/NormalForm/`. The signature file has no `Arith`/`Steps` declarations (only `nfSteps`,
which belongs to `NormalForm`), so the interface below is my design; all `N` below is passed as a
parameter with `hN : N = ⌊2πKs/(12 log 2)⌋₊`, so session 2 defines `nfSteps` and passes `rfl`.

## Interface for `NormalForm` (session 2)
- `NFHyp D r s K α L p ε Λ h f` bundles the source premises of `normal_form` (hp hα hK hL hr hs hh hnr
  hlip hrad hf hfb hε0 hi hii); session 2 builds it from the theorem's hypotheses.
- Schedule (Arith): `nfRho r N i`, `nfSig s N i` (`r/8`,`s/6` at `i=0`, else `r/(8N)`,`s/(4N)`), `nfR`, `nfS`
  (`rᵢ₊₁ = rᵢ - 2ρᵢ`), `nfEps1` (`ε₁ = 2⁷qε²/(ᾱrs)`), `nfB ε₁ ε` (`B₀ = ε`, `Bᵢ₊₁ = ε₁/4ⁱ`),
  `nfBound`. Closed forms `nfR_final`/`nfS_final` (`r_{N+1} = r/2`, `s_{N+1} = s/6`, `N ≥ 1`),
  `nfR_half_le`/`nfS_sixth_le` (`r/2 ≤ r_{N+1}`, `s/6 ≤ s_{N+1}` for all `N`, incl. `N = 0`).
- Sequence (StepsSeq): `nfG/nfF D r s K Λ h f N i` (= `g_{i-1}`, `f_i`), `nfPhi … i` (= `iterMap` at step `i`),
  `nfG_eq_sum`, `isDecomp_nfG`, `NFInv … i`, `nfInv_zero`.
- Case A: `nf_inv_all H hN hA : ∀ i ≤ N+1, NFInv … i`, where `hA : exp(-(2πKs)/6) ≤ iterU α p ε (r/8) (s/6)`.
  `nf_step_props H hN hi hinv` (i ≤ N): on `Uᵢ₊₁ = Dom (nfR (i+1)) (nfS (i+1))`: holomorphy, `MapsTo … Uᵢ`,
  symplectic, integer translations, injective, θ/I displacement bounds `qBᵢ/(ᾱρᵢ)`, `qBᵢ/(eᾱσᵢ)`,
  and `H_i ∘ Φ_i = h + g_i + f_{i+1}`. `nf_chain_identity`: `(h+f) ∘ chain nfPhi m = h + g_m + f_{m+1}` on
  `U_{m+1}` (use `telescope` with `U i = Dom (nfR i) (nfS i)` and `d i` from `nf_step_props`).
  `nf_disp_sums`: `∑_{i≤N} qBᵢ/(eᾱσᵢ) ≤ qKε/α` and `∑ qBᵢ/(ᾱρᵢ) ≤ 10qε/(ᾱr)` (the sums `telescope` needs,
  with `d i` literally those summands). `nf_final_f` (b): `InClass`+`WBound D (r/2) (s/6) f_{N+1} (e^{-κ/6}ε)`.
  `nf_final_g` (`InClass D (r/2) (s/6) g_N`), `nf_final_g_diff` (a): `WBound … (g_N - homRes K Λ f) (16(2qK/(αr))ε²)`,
  `nf_final_g_zero` (`N = 0 → g_N = homRes K Λ f`, the exact-correction clause). `nf_real`, `nf_phi_real`: reality.
- Case B: `nfCaseB_hyp` (the `IterHyp` for losses `(r/4,s/3)`, `g = 0`), `nfCaseB_bound` ((b) on `(r/2,s/6)`),
  `nfCaseB_g` (`iterG K Λ 0 f = homRes K Λ f`), `nfCaseB_disp` ((c): `10qε/(ᾱr)`, `qKε/α`), plus `iterative_direct_a/e` on
  `nfCaseB_hyp` for the map, injectivity, reality. Case B is `¬ hA`: `iterU … < exp(-(2πKs)/6)`.
- Case split in `NormalForm`: Case B (`¬hA`), `N = 0` (Case A, `nf_final_g_zero`; `nfSteps K s = 0`), `N ≥ 1`.
  For `nfSteps K s = 0 ∨ iterU … < exp(…)` the exact-correction clause follows from `nf_final_g_zero`/`nfCaseB_g`.
  Not done here (left to `NormalForm`): the coefficient-vanishing clause `coeff g I k = 0, k ∉ Λ ∩ zBall` for `g = g_N`
  (needs coefficient additivity over `nfG_eq_sum` and `homRes = projMode (Λ ∩ zBall)`), the `Ψ`-assembly and `nonresonant_case`.

## Approach
`Arith`: each displayed inequality is a standalone real lemma stated through `iterU`/`nfBound`, matching the shape of
`iterative_direct_d` so `Steps` rewrites nothing; no `nlinarith`; `Real.exp_one_gt_d9`/`log_two_gt_d9` for `2<e`, `ln2>2/3`.
Carried bounds are closed form (`B₁ = ε₁`, `Bᵢ = 4^{1-i}ε₁`) so no recursion for the bound sequence; the
starNorm of step `i` is bounded through the weights (`w₀ ≤ 5/(8N)`, `wⱼ ≤ 1`, `star_sum_le`, geometric sum). Deviation from the
blueprint (harmless): weights `wⱼ ≤ 1` instead of `≤ 1/2`, so `|g_{i-1}|_* ≤ 5ε/(8N) + 4ε₁/3` and `u ≤ 1/16` still holds
(`5/256 + 4/768 < 1/16`); `(6.1)` is used in the sharper form `ε₁ ≤ ε/κ` for displacement and `ε₁ ≤ ε/4` elsewhere.
`Steps`: invariant `NFInv i` = class+bound of `f_i` and of the parts `homRes f_j` (`j<i`); `nf_hyp` builds the `IterHyp`
via `iterHyp_of_source` (monotone `FreqLipschitz`, `hrad` from `R i ≤ r`); `nf_inv_succ` applies `iterative_direct_c/d`.

## Checks
- Gate: `inp_lake_build.sh /root/code/KAM-inp-n68a KAM.Nekhoroshev.NormalForm.Steps KAM.Nekhoroshev.NormalForm.Arith`:
  `Build completed successfully (3238 jobs)`, no warnings or sorry; each module also elaborated individually with `lake env lean` (no warnings).
- `scripts/lint_sources.sh`: PASS except the expected `KAM.lean is out of date` (generated; not edited, per rule 10).
- `#print axioms` (nf_hyp, nf_inv_all, nf_step_props, nf_chain_identity, nf_disp_sums, nf_final_f, nf_final_g,
  nf_final_g_diff, nf_real, nfCaseB_bound, nfCaseB_disp, iterU_first, nfBound_caseA, induct_step, disp_I):
  all `[propext, Classical.choice, Quot.sound]`.

## Uncertainties, errata, deviations
- No errata found in the pinned source for these steps. Noted blueprint looseness (not defects): weight `≤ 1/2` (we use 1);
  `1.17` displacement constant is `7/6` here (`1 + 1/6`, using `8N ≤ κ`), and the θ-sum bound is `8 + 4/3 ≤ 10`.
- Case B with `N` large: the hypothesis `hA` is only used at `i = 0`; for `i ≥ 1` the lemmas need only `N ≥ 1`.
- No heartbeat problems; no design signals.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row N6-8 and the **N6-8** proof-plan paragraph (Arith: every displayed inequality of Steps nf-first, nf-case (Cases A/B), nf-N ((6.1),(6.2)), nf-induct; Steps: the step sequence); audits DESIGN-N67-design-audit-{1,2}.md; signatures .drafts/design/NPart67Signatures.lean; blueprint-N p6 normal-form): (1) statements = design signatures and blueprint; facades Arith and Steps only re-export; the interface exposed for NormalForm (session 2) is adequate and adds no premise that the theorem's hypotheses cannot supply; (2) proofs sound, numerics correct; (3) hygiene (lint incl. 100-char lines; no file over 600 lines as planned). Audit ONLY the Arith* and Steps* modules (compare with branch inp-n67).
