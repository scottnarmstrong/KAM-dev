# GAP-P11a-HOM prover handoff (branch inp-g11hom, ef583e86; off inp; graph-gap programme package run by the main orchestrator)


## Files (all new, append-only; no landed file edited; KAM.lean untouched)
- `KAM/Planetary/MaximalStep/HomologicalNodes.lean` (311 lines)
- `KAM/Planetary/MaximalStep/RealLipschitzNodes.lean` (278 lines)
- `KAM/Planetary/WeakKAM/LipSumNodes.lean` (227 lines)
All three need adding to the root by `scripts/gen_root_imports.py` (lint reports "KAM.lean is out of date").

## Node -> declaration
| node | declaration | notes |
|---|---|---|
| `stepP:p11a:hm-div` | `hm_div_node` | `divisor_perturb` without `0 ≤ L` (derived from `‖Dω(b)‖ ≤ L` at the point `b`). The three PROVED nodes hm-coeff/hm-a/hm-bc take its output `hdiv`; they can now cite this. |
| `stepP:p11a:hm-bracket` | `hm_bracket_node` (core `hm_bracket_solve`) | For `φ₀ = p11Solve P₀`, `φ₁ⱼ = p11Solve P₁ⱼ`: `{N_b,φ} = -(ω·∂θφ₀ + Σ(ω·∂θφ₁ᵢ)ηᵢ) = -((P₀+ΣP₁ᵢηᵢ) - (⟨P₀⟩+Σ⟨P₁ᵢ⟩ηᵢ))`, both equalities, all `b ∈ E+t`, all `(θ,η)`. No `hdiv` premise. |
| `bpP:p11a:homological-maximal` | `homological_maximal_node` (def `HmMaxSolution`, `HmZeroMeanTrig`) | `∃ φ₀ φ₁, HmMaxSolution … P₀ φ₀ ∧ (∀ j, HmMaxSolution … (P₁ j) (φ₁ j)) ∧ bracket`. `HmMaxSolution` = zero-mean admissible trig poly on ℂᴺ×B, equation `ω·∂θφ = P-⟨P⟩` for all θ, uniqueness, (a)(b)(c)(d)(e). Premises: only source ones; `0 ≤ L`, `0 ≤ M`, `hdiv` (D/2 on B) and `n ≥ 1` are not assumed. |
| `stepP:p11a:rl-const` | `rl_const_node` | `Λ=⨆‖Dφ₁‖ ≤ 2πT ⨆ᵢ Σ_{0<|k|₁≤T}‖φ̂ᵢₖ‖` and under the decay bound `≤ 2TM₁Λ_{r*}/D` (`p11Lambda n rs`). |
| `bpP:p11a:real-lipschitz` | `real_lipschitz_node` | `∀|t|≤1,θ`: `‖DΘᵗ-1‖ ≤ e^Λ-1`, `Θᵗ(θ+k)=Θᵗ(θ)+k`, `‖Θᵗ-θ‖ ≤ ⨆‖φ₁‖`; plus both rl-const clauses. `Θᵗ = p11RealFlow φ₁ t`. |
| `stepP:p11a:pl4-terms` | `pl4_terms_node` (core `pl4_terms_ctx`) | separate rates `a_j/t_{j+1} ≤ (2ς₀Q₀2^{τ+1}/(C_Q t₀)) g₄^j`, `α_j/t_{j+1} ≤ (s₀Q₀2^{τ+1}/(32t₀))(2 q g₄)^j`, `g₄ = g₁2^τ` (`g₁ = selectionG…0`, `g₄ = selectionG…3`, `q = selectionQ`, `ς₀ = strip/24`). Binders as `param_lip_sum`. |
| `stepP:p11a:pl4-sum` | `pl4_sum_node` (core `pl4_sum_ctx`) | summability, `S_b ≤ (32/31)Q₀Ξ(2/C_Q+1/32) ≤ (46/1000)·2⁻¹⁰ ≤ 2⁻¹⁰/16`. |
`c2-conv#bracket` untouched (closed by LEAN_REF per plan).

## Approach
Assemble landed lemmas (`differentiableOn_solve`, `fderiv_solve`, `solve_unique`, `norm_solve_le`, `homological_maximal_param/_real`, `p11_normal_affine_bracket`, `real_lipschitz`, `wbud_*`, `free_radius`). The scalar clause bundle is re-assembled from the component lemmas (not from `homological_maximal`) because that theorem needs `1 ≤ n` (unused in its proof) and gives periodicity/uniqueness only on the strip. Empty `E` is handled by `hmMaxSolution_of_empty`; `0 ≤ M` is derived at a point of `B` otherwise. Imported (not re-proved) `coeff_zero_real`, `fderiv_pi_apply` via `StepReal`/`StepBound`.

## Checks
- Gate build `KAM.Planetary.MaximalStep.HomologicalNodes`, `…RealLipschitzNodes`, `KAM.Planetary.WeakKAM.LipSumNodes`: `Build completed successfully (9174 jobs)`, no warnings in these files (checked with `lake env lean`).
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK, no long lines; only message: `KAM.lean is out of date` (expected; I did not edit it).
- `#print axioms` of all seven node theorems: `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, no heartbeat options; no design signals.

## Uncertainties / deviations / suspected errata
1. `rl_const_node`/`real_lipschitz_node` take `0 ≤ M₁` (and `0<r_*`, `0<D`): the source treats `M₁` as a norm bound, so the sign is implicit; without it the second inequality can fail when no nonzero mode `≤ T` exists. Please rule it an implicit hypothesis (possible erratum: state `M₁ ≥ 0`).
2. "Real trigonometric polynomial of degree ≤ T" is formalised as `RealTrigPolyDeg` (each component is a finite Fourier sum supported on `|k|₁ ≤ T`, real-valued); `φ̂` is `KAM.torusCoeff`. `max_i` is `⨆ i`, `sup` is `⨆ x`.
3. In `HmMaxSolution` the P-datum is "admissible trig poly" = `p11AngleClass rs B P` plus `truncate T P = P` on `univ ×ˢ B`, as in the landed `homological_maximal`; the reality clause (d) is stated as an implication whose antecedents are "ω real" and "P real" (ω real is also a premise of the node).
4. (c) is stated at the landed form `(j:ℝ)^j·Λ_δ·M/(π·D·(t-t')^j)` (equal to the source expression).
5. pl4 nodes: the numerical conclusion uses `46/1000` for `0.046`.

ORCHESTRATOR RULING (OVERNIGHT 02:30, 02:40): graph-gap programme, second plan (/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P2.md, sections GAP-P11a2-hom and GAP-P11a14). Scope: hm-div (export without divisor_perturb's extra 0 <= L premise, or derive it), hm-bracket, homological-maximal, rl-const, real-lipschitz, pl4-terms (separate g4^j and (2q g4)^j rates), pl4-sum (the intermediate (32/31) Q0 Xi (...) form and the final bound). KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? Judge explicitly each premise the handoff discloses (e.g. 0 <= M1 for rl-const/real-lipschitz: is it implied by the source's standing data, where M1 is a norm bound?). An export that takes a proved dependency's OUTPUT as a premise is a FAIL. List each failing node precisely. Audit ONLY KAM/Planetary/MaximalStep/HomologicalNodes.lean, KAM/Planetary/MaximalStep/RealLipschitzNodes.lean and KAM/Planetary/WeakKAM/LipSumNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
Orchestrator ruling OVERNIGHT 03:15 (owner to review): the premise 0 <= M1 of rl-const/real-lipschitz is accepted as a candidate source erratum (audit 1 F1 shows the standalone statement needs it); it is not a finding in round 2.
