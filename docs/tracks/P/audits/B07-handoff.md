# B07 prover handoff (branch inp-p11b-b07, 9ddace1d; contains B04 (round 2 passed) and B06 (on inp); offloaded P11B package run by the main orchestrator)


**Files:** new `KAM/Planetary/WeakKAM/Admissible.lean` (≈324 lines; imports Schedule, Cutoff, StripBudget). No other file touched.

**Declarations (verbatim from P11BSignatures.lean):** selectionM₀, selectionChat, selectionCDio, selectionGamma,
selectionT₀, selectiont₀, selectionXi, selectionThetaMax, selectionLambdaMax, selectionAdmissible, adm_params,
selectionAdapted, SelectionAdmissibility (adm-params); theorems adm_choice (ac-lam, ac-list), free_radius
(fr-small, fr-list, fr-other).

**Helpers (distinct new names, grepped unique):** selectionCN_pos, selectionDGVector_nonneg, selectionM₀_nonneg,
selectionAdm_diam_pos, selectionChat_pos, selectionCDio_pos, selectionGamma_pos, selectionT₀_pos (1 ≤ T₀),
selectiont₀_pos, selectionXi_pos, selectionThetaMax_pos, selectionLambdaMax_pos, selectionAdmissible_pos,
selectionAdmissibility_of_bounds (conditional helper: A1–A6 for any (s₀, ε₀) with ε₀/s₀ ≤ λmax, s₀ ≤ λmax/(nC₁)).

**Approach:** positivity chain from the data (diam K > 0 from positive volume; gap>0 from tau_gap; selectionExtensionC_pos from B04;
selectionVarpi_pos_le_one from B03). The shared helper proves each A-clause from the three branches of the λmax minimum;
adm_choice and free_radius reduce to it (ε₀/s₀ ≤ λmax by balancing; adapted radius via sqrt identities).

**Checks:** gate build `KAM.Planetary.WeakKAM.Admissible` succeeded (no errors/warnings in this file);
`#print axioms adm_choice` and `free_radius`: propext, Classical.choice, Quot.sound. lint_sources.sh: only
"KAM.lean is out of date" (generated; not edited per rules), other checks PASS; a >100-char line was fixed afterwards and rebuilt.
No sorry, no maxHeartbeats, no EuclideanSpace.

**Notes:** B06 `Initial` is not imported: A7 is deliberately outside SelectionAdmissibility (the separate `initial` theorem).
No signature changes, no extra hypotheses needed, no suspected errata, no deviations, no heartbeat design signals.

AUDIT FOCUS (design docs/tracks/P/design/P11B-LEAN-DESIGN.md row B07 (adm-params, adm-choice, free-radius) and its node table and proof plan; P11B design audits; signatures /root/code/KAM-inp/.drafts/design/P11BSignatures.lean): (1) every B07 declaration = signature file EXACTLY, and the B07 slice COMPLETE: every graph node the node table maps to Admissible is established; where a node is EXPORTED under its own name, its statement must be the node's literal conclusion (a weaker exported lemma under the node's name is a defect); where the design keeps a step internal, it may stay internal; (2) proof soundness: the power_law explicit scalar constants, B02 schedule, B04 smooth_cutoff and c-prime positivity, B06 initial consumed as designed; no added premises; (3) hygiene (no EuclideanSpace; no reused public short name; no root shadow; lines <= 100). Audit ONLY KAM/Planetary/WeakKAM/Admissible.lean.
