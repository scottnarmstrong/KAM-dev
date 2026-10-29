# GAP-P8a prover handoff (branch inp-gp8a, 783cc445; off inp; graph-gap programme package run by the main orchestrator)


**Files:** new `KAM/Planetary/SecularForm/ModelTransferNodes.lean` (~470 lines). No landed file edited; `KAM.lean`
untouched (lint reports "KAM.lean is out of date": orchestrator must run `scripts/gen_root_imports.py`).
No `sorry`/axiom, no heartbeat overrides, all lines <= 100.

## Node -> declaration (all in `KAM.Planetary.SecularForm`, unsigned, docstrings cite the node id)
| node | declaration | note |
|---|---|---|
| `stepP:p8:id-diff` | `identification_diff` | diff = (2m0)^-1 planeSq(sum momentum); p^(i)=pmom continuous in own angle; diff continuous |
| `stepP:p8:id-avg` | `identification_avg` | (2pi)^-n ∫_cell diff = modelDelta; both forms (κG/2)Σm⁴/Λ² and (G/2)Σ m²/axis |
| `stepP:p8:id-int` | `identification_int` | iff + avg subtracts (any slowDom point); ∃ ρ*<ρ0/2 with both integrable on realDisc |
| `bpP:p8:identification` | `identification_full` | general part on slowDom + on realDisc(ρ*): S_mov=S_fix+δ unconditional, ⟨H_mov∘Ψ⟩=h+μS_mov=h+μS_fix+μδ, ⟨H_fix∘Ψ⟩=h+εS_fix (h = `keplerActionHam D Λ`) |
| `bpP:p8:same-jets#jets` | `same_jets_jets` (projection of `same_jets_full`) | all-order (ξ,η)-jets with Λ-derivatives; (a) S_mov=C0+δ+quad+quad+O(|(ξ,η)|⁴) with same `coeffs`, analytic remainder; (b) (ξ,η)-fderivs equal, Λ-fderivs differ by fderiv δ |
| `bpP:p8:same-jets#transfer` | `same_jets_transfer_full` (projection of `same_jets_full`) | HasSecularBirkhoffForm iff (P0↦P0-δ) under realDisc hypothesis; composition clause S_mov∘χ−S_fix∘χ=δ(Λ) for Λ-preserving χ into realDisc |
| `bpP:p8:same-jets` | `same_jets_full` | primary statement: jets (a),(b), HasSecularBirkhoffForm iff and composition clause, all at ONE common radius ρ*; `same_jets_jets`/`same_jets_transfer_full` are projections of it |
| `stepP:p8:q4-c` | `quartic_c_node` | c1 = G mi mj radialR1(a_i,a_j)/(2Λi²), c2 likewise (source form is G=m0=1) |
| `bpP:p8:quartic` | `quartic_full` | ∃c: analyticity, jet of S_fix and S_mov, c1/c2 via radialR1; `quartic_scaling`; `quartic_pair_scaling` (a); sufficient subdomain ⊆ separatedDomain; sqrt-chart conversion (a) |

## Approach
Pure assembly of landed results (`identification`, `lemma64`, `perturbation_analytic(_full)`, `quadratic_form`,
`same_jets*`, `jets_core`, `quartic`, `quartic_scaling`, `quartic_pair_scaling`, `quartic_sqrt_chart_conversion`).
New mathematics only: averaged Hamiltonians (const + μ·avg), δ forms, fderiv identities, subdomain inequality.
Private helpers: `radius_integrable`, `delta_forms`, `avg_const_*`, `hProd_assemble_eq`, `avg_hamiltonians`,
`first_order_at`, `differentiableAt_modelDelta`, `pos_of_realDisc`, `mem_separatedDomain_of_small`.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-gp8a KAM.Planetary.SecularForm.ModelTransferNodes`: Build completed successfully (only pre-existing warnings in other files).
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only complaint is KAM.lean out of date (expected, generated).
- `#print axioms` of all 9 exports: `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / deviations (for the auditor)
1. ρ*: each node states `∃ r, 0<r ∧ r<ρ0/2 …` (r ≤ the radius of `perturbation_analytic_full`, shrunk by min with the radius of `perturbation_analytic` / `quadratic_form`), not literally the radius of that lemma.
2. (revised) `same_jets_full` states jets/(a)/(b), the transfer iff and the composition clause at one common ρ*; the `#jets` and `#transfer` exports are its projections. Every export builds the dependency outputs (`identification`, `radius_integrable`, `quadratic_form`, `perturbation_analytic_full`) inside its proof and takes only source hypotheses (V, r0, μ0, P0, Ω, β, χ, U as in the node) as premises; quantifier domains are slowDom / all axes / all actionDomain as in the source; the iff and uniform constants stay literal.
3. (b) "same secular equations / frequencies differ by μ∂_Λδ" is stated at the level of fderivs of S (Hamilton's equations are linear in these); "Λ constant" is structural (S has no λ argument). Not stated via an ODE/vector-field of the averaged Hamiltonian.
4. "same σ_j, Ω_j" is implied by equal `coeffs D (axis D Λ)`; no separate eigenvalue statement.
5. q4-c carries the factor G (source states G=m0=1); the quartic bundle's S_mov jet is obtained from `same_jets` (k=4).
6. Composition clause: χ is any map Λ-preserving into realDisc (symplecticity unused, so omitted).
7. `identification_int` / `id-int` node: "both integrable" is only on realDisc(ρ*), as in the source.
No suspected source errata.

ORCHESTRATOR RULING (OVERNIGHT 01:20, 01:35): graph-gap programme for the landed parts. This package appends UNSIGNED exports whose job is to state the LITERAL conclusion of each listed graph node, built from landed declarations; nodes already PROVED or BYPASSED in the graph are skipped. Package definition: section '**GAP-P8a:**' of /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md. KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.
This branch also contains GAP-P8b (SecularForm/AnalyticNodes.lean, audited separately and being fixed additively); do not audit that file.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? An export that takes a proved dependency's OUTPUT as a premise is a FAIL (export from the source hypotheses and build the dependency inside). A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL for that node; list each such node precisely. Also verify that every node the handoff lists as 'already closed' is PROVED or BYPASSED in docs/graph/P/DEPGRAPH.md or docs/graph/P/packets/AMENDMENTS.md. Audit ONLY KAM/Planetary/SecularForm/ModelTransferNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
