# GAP-P11a-SQ prover handoff (branch inp-g11sq, c2244490; off inp; graph-gap programme package run by the main orchestrator)


## Files (all new, append-only; no landed file edited)
- `KAM/Planetary/WeakKAM/ScheduleNodes.lean` (`fe_supp`)
- `KAM/Planetary/Quantitative/TheoremNodes.lean` (`sel_data_gamma`, `qt_order`, `qt_reduce`)
- `KAM/Planetary/Quantitative/KamInputNodes.lean` (`kam_input_B0`, `kam_input`)

## Node -> declaration (namespace KAM.Planetary)
| node | declaration | note |
|---|---|---|
| bpP:p11a:sel-data | `sel_data_gamma` | 2*selectionGamma d = p11GammaStar n rho mu beta (p11CDio n n rho mu (diam K) vartheta beta M tau) loss (and 2γ ≤ γ_*) |
| stepP:p11a:fe-supp | `fe_supp` | premises: SelectionExtensionChain, 0<t0, 0≤τ, t0 ≤ ϑ/√n, j<ν, tsupport χ ⊆ {infDist(·,K_j) ≤ t_j/2}. Conclusions: ⊆ {infDist(·,K) ≤ ϑ/(2√n)}; ⊆ {Euclid dist to K ≤ ϑ/2}; ⊆ K_ϑ; K_ϑ ⊆ V (real points of the 2ϑ collar; proved, not assumed); ⊆ selectionRealCollar K_j t_j |
| stepP:p11a:qt-order | `qt_order` | 0<γ, 0<thresholds, 0<vol K, 0<diam K, and K_ϑ ⊆ V (the ϑ-thickening in Euclidean distance inside {y | realInclusion y ∈ actionNbhd K (2ϑ)}) |
| stepP:p11a:qt-reduce | `qt_reduce` | ∃ ds m0, ds.h = h ∧ qbcOfSelection ds m0 = d ∧ selectionM₀ ds ≤ m0 ∧ (∀ ε>0, sup|f| ≤ ε → SelectionPerturbation ds f ε) ∧ selectionGamma ds = d.gamma ∧ thresholds d ≤ selectionAdmissible ds |
| bpP:p11:kam-input | `kam_input` (+ `kam_input_B0`) | N = n+n, d.rho = 2, d.Valid. γ = d.gamma, ε_adm = thresholds d, both >0; ∃ cDelta>0; for every QuantitativeInput d h f, ε_f ≤ ε_adm, sup|f| ≤ ε_f (ε_f ≥ 0 is derived, not assumed): ∃ Q with K1 (compact, ⊆K, meas), K2 (IsLatticeTorus, Diophantine γ τ), K3 (‖u‖ ≤ Δ = p11c_displacement), K4 (InjOn on unitCube×good, Borel image, 2^{-2N} bound); `p11c_B0 d = μ(μ+1)+2` (K5 exponent, proved for ρ=2, μ≥1 in `kam_input_B0`); ∃ c_*>0 ∀ β∈(0,min{1,M}], c_* β^{B0} ≤ thresholds{d with beta:=β}; ∃ c_D, κ_D=1/2, a_D=G0 ≥ 0 with Δ ≤ c_D ε^κ β^{-a} for ε ≤ thresholds{β} |

Closed nodes (sp-1..5, qt-zero, qt-iter, qt-k5) skipped per brief. At start no declaration for any of these nodes existed in KAM (grep of full and short names).

## Approach
Pure assembly of landed lemmas: `qbc_gamma_sel`, `p11c_zero_two_gamma`, `p11c_zero_cDio_eq`, `p11c_selData_exists`, `polyBudget_threshold_le`, `weak_kam_quantitative`, `displacement_power_flat`, `qb_beta`, `QuantitativeFamily.lower`, `mem_selectionRealCollar_of_infDist`. No new mathematics, no new public helper beyond `kam_input_B0`.

## Checks
- Gate builds (`inp_lake_build.sh`, LEAN_NUM_THREADS=1): `KAM.Planetary.WeakKAM.ScheduleNodes`, `KAM.Planetary.Quantitative.TheoremNodes`, `KAM.Planetary.Quantitative.KamInputNodes`: "Build completed successfully", no warnings in these files.
- `scripts/lint_sources.sh`: check_lean_modules PASS (1217 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message: "KAM.lean is out of date; run scripts/gen_root_imports.py" (expected: new modules; KAM.lean not edited per brief).
- `#print axioms` of kam_input, kam_input_B0, qt_reduce, qt_order, sel_data_gamma, fe_supp: [propext, Classical.choice, Quot.sound] each.
- Lines ≤ 100 columns; no maxHeartbeats, sorry, axiom.

## Uncertainties / notes
- `qt_order`: the source "nothing in (A1)-(A4) or ε_f ≤ ε_adm mentions a conclusion" is a meta-statement, not exported. `QuantitativeInput` writes K_ϑ (Euclid) as its "V" for the bounds (A3)/(A4); the real V = U∩ℝ^N is `{y | realInclusion y ∈ actionNbhd K (2ϑ)}`, which is what `qt_order` proves K_ϑ ⊆.
- `kam_input`: Δ(ε_f; d) is `p11c_displacement d cDelta ε_f` with cDelta from `weak_kam_quantitative` (depends on (N,μ,τ,s,C1) only); constants c_*, c_D are uniform in β because β is quantified after them over the datum `{d with beta := b}`.
- K4 "injective" is derived from the bi-Lipschitz field `lower`; hypotheses `d.rho = 2` is used only for the B0 identity.
- Suspected errata: none. Deviations: none.

ORCHESTRATOR RULING (OVERNIGHT 02:30, 02:40): graph-gap programme, second plan (/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P2.md). This package appends UNSIGNED exports stating the LITERAL conclusion of each listed graph node. Scope (ruling 02:40): sel-data, fe-supp, qt-order (K_theta subset V), qt-reduce (gamma(d') = gamma(d)), kam-input (must prove the (K5) exponent identity B0 = mu(mu+1)+2 for rho = 2, mu >= 1). sel-data is a definition node that also asserts properties: the export states those properties. KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses (plus any premise a ruling above explicitly allows), with quantifiers in the source's order? An export that takes a proved dependency's OUTPUT as a premise is a FAIL (export from the source hypotheses and build the dependency inside). A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL; list each such node precisely. Audit ONLY KAM/Planetary/Quantitative/KamInputNodes.lean, KAM/Planetary/Quantitative/TheoremNodes.lean and KAM/Planetary/WeakKAM/ScheduleNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
