# GAP-P8b prover handoff (branch inp-gp8b, e89eae66; off inp; graph-gap programme package run by the main orchestrator)


**Files:** new `KAM/Planetary/SecularForm/AnalyticNodes.lean` (~435 lines, module, no landed file edited).
Not touched: `KAM.lean` (lint reports it out of date: the orchestrator must run `scripts/gen_root_imports.py`).

## Node -> declaration (namespace `KAM.Planetary.SecularForm`)
| node | declaration |
|---|---|
| `stepP:p8:pa-unif` | `perturbation_unif`: ∃ r, 0<r, r<ρ₀/2 (`rho D a / 2`), Re s_ij ≥ (a_j−a_i)²/2 for all t on `polydisc D a r`; at real points `separationC = planeSq(q_i−q_j)`, `(a_j−a_i)/√2 ≤ planeLength(q_i−q_j)`, `poincareProd(assemble …) ∈ collisionFreeDomain n` for every angle t |
| `stepP:p8:pa-hol` | `perturbation_hol` (under 0<r, r<ρ₀, the pa-unif separation bound): holomorphy per angle, joint continuity, `2π`-periodicity (via `perturbationC_periodic`), and equality with `fFix`/`fMov ∘ poincareProd` at real points |
| (periodicity clause) | `perturbationC_periodic`: update of any one angle by `2π` leaves `perturbationC` unchanged on `polydisc` |
| `stepP:p8:pa-avg` | `perturbation_avg_node` (same hypotheses; the conjunction of `perturbation_avg` and `perturbation_avg_complex`): `secularC` holomorphic, real at real points, `secular` real analytic on `realDisc`, and `∀ k, iteratedFDeriv ℝ k (secular D b) x = avg (fun t => iteratedFDeriv ℝ k (fun y => perturbation D b (assemble y.2.1 t y.2.2 y.1)) x)` |
| `bpP:p8:perturbation-analytic` | `perturbation_analytic_full`: one radius r<ρ₀/2 carrying all of the above, for both models `b : Bool` |

## Approach
pa-unif shrinks the landed `exists_radius` radius to `min r (ρ/4)`. Collision freedom uses the landed
`poincare_holomorphic` (5th clause) for the product-chart domain, `poincareProd_mem_regionProd` for |q_i|>0,
and the separation bound for |q_i−q_j|>0. Derivative formula: `perturbation∘assemble` is jointly analytic on an
open set containing `cell × realDisc` (via `analyticOnNhd_fMov/fFix_poincareProd` and a linear `assembleCLM`),
then differentiation under the integral. `e_diff` is stated on `Vec d` only, so `hasFDerivAt_cell_integral` and
`e_diff` were re-proved privately for a general proper normed space (`hasFDerivAt_cell_integral_gen`,
`cell_iteratedFDeriv_integral`; textual adaptation), plus a private slice lemma (adaptation of
`PairJet/Diff.lean` `p11cPJ_iteratedFDeriv_slice`). All helpers are private.

## Checks
- `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-gp8b KAM.Planetary.SecularForm.AnalyticNodes`:
  Build completed successfully; no sorry, no new warnings in my file.
- `scripts/lint_sources.sh`: `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`; only
  message: "KAM.lean is out of date" (generated; not edited by me).
- `#print axioms` of `perturbation_unif`, `perturbationC_periodic`, `perturbation_hol`, `perturbation_avg`,
  `perturbation_analytic_full`: all `[propext, Classical.choice, Quot.sound]`.
- No heartbeat options; lines ≤ 100; file well under 1500 lines.

## Uncertainties / deviations
- pa-hol and pa-avg take the pa-unif conclusion (radius, `r<rho`, separation bound) as hypotheses, as the nodes'
  SOURCE_HYPOTHESES list it (it is a source premise of those steps, not their conclusion); the bundle discharges
  it. 
- "real at real points" is stated as the equality `perturbationC … (inclusion x) = (real value : ℂ)`.
- The node text says "ρ* < ρ₀/2" with ρ₀ = `rho D a`; that is what `perturbation_unif` uses.
- Landed `perturbation_analytic` (r < rho, not rho/2) is untouched; the new bundle is a separate declaration.

## Suspected errata
None found.

ORCHESTRATOR RULING (OVERNIGHT 01:20): graph-gap programme for the landed parts. This package appends UNSIGNED exports whose job is to state the LITERAL conclusion of each listed graph node, built from landed declarations. Package definition: section '**GAP-P8b:**' of /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md (its estimates are UNVERIFIED). KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL for that node; list each such node precisely. Audit ONLY KAM/Planetary/SecularForm/AnalyticNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.

## Round 3 (audit 2: pa-avg needs one node-named export)
Appended ONE theorem `perturbation_avg_node` to `KAM/Planetary/SecularForm/AnalyticNodes.lean` (591
lines): pa-avg's whole literal conclusion (DEPGRAPH.md:14943-14945), i.e. `perturbation_avg`'s
conclusion ∧ `perturbation_avg_complex`'s conclusion, same hypotheses, proved by pairing them. Node
table: pa-avg -> `perturbation_avg_node`. Nothing else changed. Build through the gate: completed
successfully; `#print axioms perturbation_avg_node`: [propext, Classical.choice, Quot.sound]; no line
over 100 columns; no heartbeat options.
