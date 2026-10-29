# GAP-P5b prover handoff (branch inp-gp5b, 3372c73a; off inp; graph-gap programme package run by the main orchestrator)


Files (new): KAM/Planetary/PGAssembly/LocationNodes.lean, KAM/Planetary/PGAssembly/LowerNodes.lean
(imports Lower + PGMeasure.Collar). No landed file edited; KAM.lean not regenerated (lint says
"KAM.lean is out of date": run scripts/gen_root_imports.py when landing).

## Node map (namespace KAM.Planetary)
| node | declaration |
|---|---|
| stepP:p5:lo-range, lo-act, lo-disc | ALREADY CLOSED (PROVED under `location`, Chart.lean) |
| bpP:p5:kset (relative closedness + σ-compact) | `pgD0_relClosed` (LocationNodes): ∃ closed C, pgD0 = pgActionDomain ∩ C; and IsSigmaCompact |
| stepP:p5:tc-freq | `tc_freq_node`: ∃ Cw (independent of r,mu), norm bounds Cw, Cw*mu, IsDiophantine (min γ1 γ2) τ, τ = n+1 > a+b |
| bpP:p5:torus-conv | `torus_conv_node`: IsCylinderTorus + Diophantine + bounds + range ⊆ cylinder, for J ∈ pgD0 (ω = ω₀(J) ∈ Ω_*) |
| stepP:p5:lo-bad | `lo_bad_ratio` (LowerNodes): ratio form with l2 = r²/2, constant (A+Cdio Cγ)/meas V + 6bκ1 times √r |
| stepP:p5:lo-lost | `lo_lost_budget`: meas(D×[0,1)^n \ L) ≤ c_n C_b √r meas D, meas D ≤ meas F', and the F' form; L = outputRepresentative (Phase coords angle,action) |
| stepP:p4:dc-prod | `dc_prod_node`: Re(D_rK) = N_rK(D_t) × (l1-rK,l2+rK)^b ⊆ V × (0,∞)^b (iff-free equality; needs l1<l2, source λ1<λ2) |

Approach: reuse landed declarations (frequency_bounds, torus_conv spec, location, budget,
volume_pgActionDomain, collar, realNbhd_joinedActions); private lbn_* helpers re-prove the
private lo_core_bad / lo_ell_pow of Lower.lean. Hypotheses: only d, admissible (r,mu), and for
dc-prod the source collar hypotheses; nothing derived is a premise.

Checks: `lake build` through the gate of both modules: success. `#print axioms` of all six:
[propext, Classical.choice, Quot.sound]. scripts/lint_sources.sh: check_lean_modules PASS,
frozen guard OK, ABI OK; only message: KAM.lean out of date (expected). Lines ≤ 100.

Deviations / uncertainties:
- tc-freq/torus-conv use an existential C_w (as the plan says), not the source's displayed
  C_w = (M_ω+A_N)/2π+1; the uniform constant is r,mu-independent. `frequency_bounds`' constant
  has different form.
- torus-conv is indexed by J ∈ D₀ rather than ω ∈ Ω_* (K_ω = physicalTorus J); the torus is the
  chosen family `pgFamily`.
- lo-lost is stated in (angle, action) coordinates of Phase, with L as `outputRepresentative`;
  the "adding the bad-action part" clause is the closed `lower`, not re-exported.
- No errata suspected. No set_option, no sorry.

ORCHESTRATOR RULING (OVERNIGHT 01:20, 01:35): graph-gap programme for the landed parts. This package appends UNSIGNED exports whose job is to state the LITERAL conclusion of each listed graph node, built from landed declarations; nodes already PROVED or BYPASSED in the graph are skipped. Package definition: section '**GAP-P5b:**' of /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md. KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? An export that takes a proved dependency's OUTPUT as a premise is a FAIL (export from the source hypotheses and build the dependency inside). A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL for that node; list each such node precisely. Audit ONLY KAM/Planetary/PGAssembly/LocationNodes.lean and KAM/Planetary/PGAssembly/LowerNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
