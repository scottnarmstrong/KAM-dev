# P11A-W4 prover handoff (branch inp-p11aw4, 980e204; contains inp-p11aw3 (P11A-W3, audited); offloaded package run by the main orchestrator; prover on claude-12)


Files: KAM/Planetary/WeakMeasure/ScalarSublevel.lean (new, ~358 lines). Committed on inp-p11aw4.
Proved: bpP:p11a:scalar-sublevel -> KAM.Planetary.scalar_sublevel (signature verbatim from P11ASignatures.lean).
Steps as lemmas: ss-phi = p11Phi, p11Phi_continuous (1-Lipschitz); ss-nodes = p11_exists_node(_zero)
(nodes in E with phi = iL/q, via IVT + sSup of E ∩ Iic s); ss-gaps = p11_gap_prod, p11_prod_erase_nat;
ss-dd inline in scalar_sublevel using W3 divided_difference and p11_sum_inv_factorial (Nat.sum_range_choose).
Approach: L=vol E; L=0 trivial; else nodes, gaps t_j-t_i >= (j-i)L/q, beta <= q!|S| <= eps (2q/L)^q, take q-th root.
Checks: gate build `KAM.Planetary.WeakMeasure.ScalarSublevel` succeeded (only pre-existing W3 unused-var warning);
scripts/lint_sources.sh: line-length check clean, check_lean_modules PASS, frozen guard OK, ABI hashes OK;
only message "KAM.lean is out of date" (expected, not edited per brief).
#print axioms KAM.Planetary.scalar_sublevel: [propext, Classical.choice, Quot.sound].
No sorry/axiom/maxHeartbeats; no provider/theorem-anchor imports (imports Mathlib + W3).
Uncertainties: none. Errata: none. Deviations: none. Design signals: none (default heartbeats).

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-W4 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements = design signatures (distribution-function continuity, quantile nodes and gaps); (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY WeakMeasure/ScalarSublevel*.lean (compare with branch inp-p11aw3).
