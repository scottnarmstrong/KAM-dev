# GAP-P7 prover handoff (branch inp-gp7, 9782b582; off inp; graph-gap programme package run by the main orchestrator)


## Files (new, append-only; no landed file, KAM.lean, frozen or manifest file touched)
- `KAM/Kepler/ScalingNodes.lean` (~245 lines)
- `KAM/Planetary/Poincare/ChartNodes.lean` (~530 lines)
`KAM.lean` is stale until `scripts/gen_root_imports.py` is run (lint reports it; I did not edit it).

## Node -> declaration (all unsigned; every docstring cites its node)
| node | declaration |
|---|---|
| stepP:p7:pc-eq | `KAM.Planetary.SecularForm.pc_eq` (statement via def `ChartHamiltonEq`; moving b=true / fixed b=false, μ=ε) |
| bpP:p7:product-chart | `SecularForm.product_chart_full` (a)–(d); quotient bijection via `exists_quotient_bijection` + def `fastLatticeSetoid` |
| stepP:p7:la-ham | `SecularForm.la_ham` (H∘Ψ∘polarMap = keplerActionHam(fast z.2) + μ f̂∘polarMap; h∘polarMap depends only on Λ; both models) |
| stepP:p7:d25-e | `KAM.Planetary.d25_e` (statement via def `D25Polar`) |
| bpP:p7:d25 | `KAM.Planetary.d25` (a)–(e) + converse/uniqueness mod 2πk |
| stepP:p7:po-el#circular | `KAM.Planetary.po_el_circular` |
| stepP:p7:rg-scale | `KAM.Kepler.rg_scale` |
| stepI:p7:ci-alg | `KAM.Kepler.ci_alg` |
| stepI:p7:sc-alg | `KAM.Kepler.sc_alg` |
| stepI:p7:sc-flow | `KAM.Kepler.sc_flow` |

## Approach
Pure composition of landed declarations (ProductInterface, Product, Lattice, D25, Chart, Symplectic,
Equation, Energy, Mass, Orbit, Means). No new mathematics was needed.
- `pc_eq`: `H∘Ψ =ᶠ hProd + μ f̂` near w (O_n open) gives X_{H∘Ψ} = X_h + μ X_f̂; X_h from `product_chart`.
- `product_chart_full` (c) orbit transfer is proved directly from `pc_share`'s field identity + chain rule.
- `d25_e`: polar existence via `Complex.arg`; F = g + eccAnom from `poincare_facts_polar`, `keplerLong_eq_add_eccAnom`.
- Kepler: `scaleMK_*`, `delaunayMK_means` (m=1), `orbitMapR_*`; `actionMK_sq` was not needed (rg_scale proves Λ/m = √(κ·axis) by direct field arithmetic). Private helpers re-proved privately (const-mul field lemma, planeSq analyticity, differentiability of kE / energyMK off Q=0).

## Interpretation choices (flag for audit)
1. sc_alg: `DS_kᵀ J DS_k = J` stated as `IsSymplecticOn 1 (scaleMK 1 k) univ` (invariance of `symplecticForm`, equivalent); `DS_k = diag` as `fderiv … u = (k⁻¹•u.1, k•u.2)`. Unconditional in Q (no Q ≠ 0 needed).
2. sc_flow: field identities assume `0 < planeLength z.1` (collision-free); flow clause is pointwise (HasDerivAt at t given the E₁-equation at k²t). Averages stated for orbitMapR orbits of strength one with a = elemA = L²; a_k = axisMK 1 k (S_k ·) = L²/k.
3. product_chart_full (a): "1-chart" given both as `IsChart 1 (poincareProdCast …)` (equal-dimension form) and as analytic+symplectic of `poincareProd` on Phase(n+n)→Phase(n*2). Quotient diffeo: bijection from `Quotient (fastLatticeSetoid n)` onto `regionProd` plus the existing local-analytic-inverse clause (pc_prod's) — no separate "global manifold diffeo" structure exists in KAM.
4. product_chart_full (c): f̂ = `perturbation D b` independent of μ by the quantifier order (one f̂ for all μ). Orbit transfer stated pointwise on a set J.
5. d25 (b): F_i(w) := `poincareF (planetBlock w i)`; "analytic on O₂" as AnalyticOnNhd of `w' ↦ poincareF (planetBlock w' i)` on `poincareProdDom 2`. (e): ρ_i := √(2Γ_i); both existence of g and the conclusions for every such g.
6. la_ham uses `polarMap` as Θ_n and states `H∘Ψ∘Θ` (the chartPullback with c=1 is not typed across Phase(n+n)→Phase(n*2)).

## Checks
- `inp_lake_build.sh … KAM.Kepler.ScalingNodes KAM.Planetary.Poincare.ChartNodes`: Build completed successfully (9125 jobs); no warnings in either file.
- `sh scripts/lint_sources.sh`: no violations in my files (after splitting two >100-col lines); only report is the expected "KAM.lean is out of date"; check_lean_modules PASS; frozen guard OK; ABI hashes OK.
- `#print axioms` of all ten declarations: `[propext, Classical.choice, Quot.sound]` only.
- No `maxHeartbeats`, no sorry/axiom; no provider or DRAFT_SORRY import.

## Uncertainties / errata / deviations
- No errata found; no node needed genuinely new mathematics; no heartbeat/design signals; both files far below 1500 lines.
- Public non-theorem names introduced: `fastLatticeSetoid`, `ChartHamiltonEq`, `D25Polar` (grep-checked unique).
- Not yet done by me (orchestrator): regenerate KAM.lean; record LEAN_REF/LEAN_STATUS in docs/graph.

ORCHESTRATOR RULING (OVERNIGHT 01:20): graph-gap programme for the landed parts. This package appends UNSIGNED exports whose job is to state the LITERAL conclusion of each listed graph node, built from landed declarations. Package definition: section '**GAP-P7:**' of /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md (its estimates are UNVERIFIED). KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL for that node; list each such node precisely. Audit ONLY KAM/Kepler/ScalingNodes.lean and KAM/Planetary/Poincare/ChartNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
