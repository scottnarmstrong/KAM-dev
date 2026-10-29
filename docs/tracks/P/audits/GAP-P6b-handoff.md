# GAP-P6b prover handoff (branch inp-gp6b, 5430d9f9; off inp; graph-gap programme package run by the main orchestrator)


Files: new `KAM/Planetary/Newtonian/AssemblyNodes.lean` (~270 lines, namespace `KAM.Planetary`). No landed file edited.
KAM.lean NOT regenerated (rule 10): lint reports "KAM.lean is out of date" until the orchestrator runs
`scripts/gen_root_imports.py`.

## Node -> declaration
| node | declaration |
|---|---|
| stepP:p6:rc-a | `rc_a_lengths` (ℓ(Q_{i+1}-Q_0)=ℓ(q_i)>0; ℓ(Q_{j+1}-Q_{i+1})=ℓ(q_j-q_i)>0 for i≠j; symmetry for all i j : Fin (n+1)); only hypothesis NoCollision on J |
| rc-sun | `rc_sun_hasDerivAt` (Q_0' = -(μ/m0)·Σp_j, and that equals V_0) |
| rc-planets | `rc_planets_hasDerivAt` (Q_{i+1}' = V_{i+1}) |
| rc-vplanet | `rc_vplanet_hasDerivAt` (sum over l ≠ i.succ of G·M_l (Q_l-Q_i)/ℓ³) |
| rc-vsun | `rc_vsun_hasDerivAt` (Σ_{l : Fin n}, with M_{l+1} = `actualMasses … l.succ`) |
| ot-curve | `ot_curve` (generic H: NoColl and HasDerivAt X_H along t ↦ K(φ+t•w); covers moving and fixed) |
| ma-tube | `ma_tube` (S ⊆ U_η ∧ MeasurableSet S) |
| ma-coll | `ma_coll` (NoColl (K φ).1 whenever range K ⊆ S ⊆ U_{ζ*}) |
| ma-pair | `ma_pair` (PairBounds (tubeD γ) (tubeBigD γ A) of barycentric positions of K(φ+t•w)) |
| mp-a | `mp_a_box` (U_η ⊆ box; every S ⊆ U_η has vol ≤ ofReal((2(a_max+η))^{2n})·ofReal((2(P_max+η))^{2n}) < ⊤) |
| mp-b | `mp_b_measure` (liouville_lattice clauses: NullMeasurable, vol formula, 0<vol, finite if ⊆ U_η), `mp_b_measurableSet` (Borel clause) |
| bpP:p6:measure-positive | `measure_positive` (a) ∧ (b) |

## Approach
rc-* project `reconstruction`; rc-vsun re-proves the `Σ_{l≠0}` → `Σ_{l:Fin n}` reindexing locally (the landed
helper is private). ot-curve unfolds the 8th clause of `IsPhysicalTorus`. ma-* reuse `circularTube_pair_bounds`,
`circularTube_pairBounds_barycentric`, `circularTube_mono`. mp-a: `circularTube_norm_lt`, `Real.volume_pi_ball`,
`Measure.volume_eq_prod`, `Measure.prod_prod`. mp-b: `liouville_lattice(_measurableSet)`.

## Deviations / notes (all strengthenings or statement choices)
- P_max stated as ⨆ m_i√(G m0/a_i) (source form); Lean's `circularTube_norm_lt` uses |m_i|, rewritten using m_i>0.
- ma-coll / ma-pair drop the unused `hS2` torus premise and measurability (stronger); they quantify over any K with
  range K ⊆ S (the K from (S2) is a special case). ma-tube keeps `AxisData` as an unused-in-proof typing premise.
- Exponent `n*2` (= 2n) is kept syntactically.
- rc-a assumes only NoCollision on J (source also lists G,m0,m,μ, derivative; unnecessary).
- mp-b hypothesis "A Lebesgue measurable" = `NullMeasurableSet`; Borel clause is a separate lemma.
- No erratum found; no node needed new mathematics; no heartbeat issues.

## Checks
- Gate build `KAM.Planetary.Newtonian.AssemblyNodes`: success, no warnings in my file.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK, no >100-column lines
  (after fix); only KAM.lean-out-of-date (expected, rule 10).
- `#print axioms` of all 13 declarations: [propext, Classical.choice, Quot.sound].
- No maxHeartbeats, no sorry/axiom, no EuclideanSpace, file ≪ 1500 lines.

ORCHESTRATOR RULING (OVERNIGHT 01:20): graph-gap programme for the landed parts. This package appends UNSIGNED exports whose job is to state the LITERAL conclusion of each listed graph node, built from landed declarations. Package definition: section '**GAP-P6b:**' of /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md (its estimates are UNVERIFIED). KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL for that node; list each such node precisely. Audit ONLY KAM/Planetary/Newtonian/AssemblyNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
