# GAP-P9b prover handoff (branch inp-gp9b, cf40e885; off inp; graph-gap programme package run by the main orchestrator)


Files: new `KAM/Planetary/SecularSpectrum/GoodSetNodes.lean` (~150 lines). Nothing else touched
(KAM.lean not regenerated; lint reports it out of date, as expected).

All nodes were NOT_STARTED in DEPGRAPH on this branch (no AMENDMENTS entries): none already closed.

| node | declaration |
|---|---|
| stepP:p9:gs-c (zero set closed, nowhere dense, null; hyp: A open connected, Phi4 not identically 0) | `SecularSpectrum.good_zero_set_small` |
| stepP:p9:gs-c (uniformity on compacts, via finite K4 and continuity) | `SecularSpectrum.good_uniform_nonresonance` (uses landed `min_mode_continuous_positive`) |
| bpP:p9:good-set (b) 2σ_j ≠ 0 | `two_sigma_ne_zero`; diagonalize hypotheses on action''ball: `good_diagonalize_data` |
| bpP:p9:good-set (a)-(c) | `good_set_bundle` (a: symmetric poly, char-poly polynomial, analytic, label-free; b: iff NR4, simple spectrum, 2σ≠0, diagonalize data; c: dichotomy + compact-uniform bound) |
| bpP:p9:dict | NOT closed. Only n=1 ⇒ coeffs = 0 exists already (`Nondegeneracy.coeffs_one`, `sigma_one`). `sorted(2•coeffs)=2•σ` not proved (no charpoly-smul lemma in Mathlib; Ω_j=2σ_j with frozen Birkhoff form needs separate work). Optional per plan. |

Checks: gate build of `KAM.Planetary.SecularSpectrum.GoodSetNodes` succeeds, no warnings in the file.
`#print axioms good_set_bundle`, `good_zero_set_small`: propext, Classical.choice, Quot.sound.
`scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK; only "KAM.lean out of date".
No heartbeat overrides, lines ≤100, no sorry/EuclideanSpace.

Notes: the bundle's (c) states the dichotomy; the nonzero branch hypothesis is only "not identically
zero" (dichotomy produced inside the proof). `good_uniform_nonresonance` needs `2 ≤ n` (landed
`min_mode_continuous_positive` guard). No errata, no deviations.

ORCHESTRATOR RULING (OVERNIGHT 01:20, 01:35): graph-gap programme for the landed parts. This package appends UNSIGNED exports whose job is to state the LITERAL conclusion of each listed graph node, built from landed declarations; nodes already PROVED or BYPASSED in the graph are skipped. Package definition: section '**GAP-P9b:**' of /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md. KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.
bpP:p9:dict is OPTIONAL in the plan (it is a convention/remark node, plan section 2 item 6) and is NOT in this package's required scope; its remaining open state is not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? An export that takes a proved dependency's OUTPUT as a premise is a FAIL (export from the source hypotheses and build the dependency inside). A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL for that node; list each such node precisely. Audit ONLY KAM/Planetary/SecularSpectrum/GoodSetNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
