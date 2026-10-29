# GAP-P10a prover handoff (branch inp-gp10a, 67f7f681; off inp; graph-gap programme package run by the main orchestrator)


Files: new `KAM/Planetary/Nondegeneracy/GoodAxesNodes.lean` (~250 lines). No landed file edited; KAM.lean not
edited (lint reports it out of date: orchestrator must run scripts/gen_root_imports.py).

## Node map (namespace KAM.Planetary.Nondegeneracy)
- `bpP:p10:conv#data` supplements: `isOpen_simpleAxes` (U_n open), `goodAxes_subset_simpleAxes` (G_n ⊆ U_n),
  `isOpen_goodAxes` (G_n open, n ≥ 2), `nu_action_eq` (ν_i(Λ(a)) = √(G m0)·a_i^(-3/2)).
- `stepP:p10:n2-t`: `n2_t_node` (1 < t, r = t + 1/t + 2, r − 3 < t; t = σ0/σ1, r = tr²/det).
- `bpP:p10:n2`: `n2_node` (Λ-ratio identity Λ1/Λ0 = (m1/m0)√(a1/a0); r formula; r > Λ1/Λ0+2; t ≥ r−3;
  hierarchy ⇒ r > 6 ∧ nr4 σ ∧ good σ ≠ 0; ∀ M ∃ ε>0 uniform in a: a0/a1 < ε ⇒ M < r ∧ M < t). Helper `action_ratio_eq`.
- `stepP:p10:sa-loc`: `sorted_local_branch` (analytic ordered branches s, R on a ball ⊆ U_n, s x = σ x).
- `stepP:p10:sa-n2`: `simpleAxes_two_eq_axes` (U_2 = A_2).
- `bpP:p10:sorted-analytic`: `sorted_analytic_node` (analytic on U_n ∧ StrictMono σ on U_n ∧ U_2 = A_2), helper
  `sorted_strictMono_simple`.
- `bpP:p10:good-set`: `good_set_node` (open, dense, null complement, simple + local analytic branches at all of G_n,
  nr4 (2σ) on G_n, uniform lower bound c>0 on |k·2σ| over every compact K ⊆ G_n and k ∈ K_4, closed ball clause).

## Already closed (not exported)
`stepP:p10:weyl-pert` (PROVED, weyl), `gp-choice`, `gp-loc`, `gp-nr` (PROVED under good_point).

## Checks
- Gate build `KAM.Planetary.Nondegeneracy.GoodAxesNodes`: success, no warnings in my file, no sorry.
- `#print axioms` (run, then removed) of all exports: propext, Classical.choice, Quot.sound.
- `scripts/lint_sources.sh`: no line-length/module/frozen failure; only "KAM.lean is out of date".
- Hypotheses audited against the source: each export takes only data/axes membership (and 2 ≤ n where the
  source says so); no dependency output is a premise.

## Uncertainties / errata / deviations
- None found. Interpretation: "uniformly on compacts" = positive uniform lower bound c on |k·2σ| over K_4 for each
  compact K ⊆ G_n, plus nr4(2σ) pointwise. "r,t → ∞ as a1/a2 → 0" = the ε-form uniform in a. The good-set ball clause
  reuses landed `good_set` (centre named `r`, radius `2*a0`).
- good_set_node/isOpen_goodAxes need 2 ≤ n (source n ≥ 2).

ORCHESTRATOR RULING (OVERNIGHT 01:20, 01:35): graph-gap programme for the landed parts. This package appends UNSIGNED exports whose job is to state the LITERAL conclusion of each listed graph node, built from landed declarations; nodes already PROVED or BYPASSED in the graph are skipped. Package definition: section '**GAP-P10a:**' of /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md. KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites, and give a per-node verdict: does the named declaration state that node's literal conclusion under only the source's hypotheses, with quantifiers in the source's order? An export that takes a proved dependency's OUTPUT as a premise is a FAIL (export from the source hypotheses and build the dependency inside). A node whose export is weaker, conditional on an unsourced premise, or a different statement is a FAIL for that node; list each such node precisely. Also verify that every node the handoff lists as 'already closed' is PROVED or BYPASSED in docs/graph/P/DEPGRAPH.md or docs/graph/P/packets/AMENDMENTS.md. Audit ONLY KAM/Planetary/Nondegeneracy/GoodAxesNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
