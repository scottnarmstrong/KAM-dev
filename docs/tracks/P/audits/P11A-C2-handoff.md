# P11A-C2 prover handoff (branch inp-p11ac2, 50589b7; contains inp-p11ac1 (audited); offloaded package run by the main orchestrator; prover on claude-12)


Files: new `KAM/Planetary/MaximalStep/Loss.lean` (201 lines). Imports Constants, FourierCutoffTail; no provider/theorem anchor.
Nodes: `bpP:p11a:loss-choice` -> `KAM.Planetary.loss_choice` (steps lc-exponent, lc-estimate, lc-mono inline / private `loss_anti_aux`);
`bpP:p11a:loss-sum` -> `KAM.Planetary.loss_sum`. Signatures verbatim.
Approach: loss_choice: with d=p11Loss, pi*T*d = log(2c/a)+n log(pi T), exp(-pi T d) = a/(2c)(pi T)^-n, so error = a/2((piT)^-n + (piT d)^-n) <= a since pi T>3, pi T d >= 1 (log(pi T)>1). T-antitone via log(v/u) <= v/u-1 (n <= A + n log u). alpha-antitone via log monotonicity.
loss_sum: termwise bound from log(piT0 theta^j) split; comparison with (A+Bj) theta^-j/(pi T0); tsum_geometric and tsum_coe_mul_geometric_of_norm_lt_one.
Checks: gate build KAM.Planetary.MaximalStep.Loss succeeded (no warnings in Loss); lint_sources.sh: only "KAM.lean is out of date" (generated, not edited), modules/frozen/ABI PASS.
#print axioms loss_choice, loss_sum: [propext, Classical.choice, Quot.sound].
Uncertainties: none. Errata/deviations: none. Design signals: none. (Unrelated: deprecation warnings `if_pos`/`if_neg` in C1's FourierCutoffTail.lean.)

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-C2 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements = design signatures (loss_choice, loss_sum; monotonic loss; geometric and arithmetico-geometric sums); constants as designed; (2) proofs sound; no added premises; (3) hygiene. Audit ONLY KAM/Planetary/MaximalStep/Loss.lean (compare with branch inp-p11ac1).
