# S7-7 prover handoff (branch inp-s77, 1e47a63; contains inp-n68b (N6-8, audited) and N6-1..N6-7; S7-1..S7-6 on inp; offloaded package run by the main orchestrator; prover on claude-12)


Files (new): KAM/Nekhoroshev/Stability/Nonresonant.lean (212 lines), KAM/Nekhoroshev/Stability/NonresonantAux.lean (138 lines).
KAM.lean NOT edited (lint reports it out of date: expected, orchestrator regenerates).

Node bpN:p7:nonresonant -> `KAM.Stability.nonresonant`, signature verbatim from NPart67Signatures.lean (`hn : 1 ≤ n` unused: unused-variable warning only).

Approach
- Aux: `thetaGradR_realH_re` (own copy of the private Gradient lemma), `norm_thetaGradR_le` (‖∂_θ u^ℝ‖ ≤ M/(e s) from theta_derivative),
  `thetaGradR_realH_add`, `thetaGradR_snd`/`thetaGradR_h_add` (h(I) has zero θ-gradient), `drift_bound`
  (‖(z t).2-(z 0).2‖ ≤ |t|·B if ‖∂_θ G^ℝ‖ ≤ B on W_ϱ; mean value, no exit argument).
- κ<6: drift ≤ |t| ε/(e s) ≤ r/5 ≤ r/2 directly (e^{κ/6} ≤ e); normal_form not needed.
- κ≥6: normal_form (Λ={0}, D=cpx D), preimage_nfl, transfer (Nrm=‖·‖, ϱ=15r/32, d=conjExp p K ε/α, adm = time bound);
  g θ-independent: resonant_gradient with resSpan {0}=⊥ (WBound g from `homological` homRes bound + (a) + wbound_add);
  (T3) by drift_bound with B = e^{-κ/6}ε/(e s/6); 6/(5e) < 15/32 via exp_one_gt_d9; ϱ+2d ≤ 31r/64 ≤ r/2.
- Deviation from design: `exit_ball` and `nonresonant_case` are not used (uniform gradient bound on the whole strip makes the
  first-exit argument unnecessary). D nonempty obtained from hz0 (used to get d ≤ r/2^7 via preimage_nfl).

Checks
- `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-s77 KAM.Nekhoroshev.Stability.Nonresonant` : Build completed successfully (3269 jobs), no sorry.
- scripts/lint_sources.sh: PASS except "KAM.lean is out of date" (not mine to edit).
- #print axioms KAM.Stability.nonresonant: [propext, Classical.choice, Quot.sound].

Uncertainties/errata: none found; no heartbeat issues.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row S7-7 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md; signatures .drafts/design/NPart67Signatures.lean; blueprint-N p7 nonresonant (Prop 1)): (1) statement = design signature and blueprint (Proposition 1, nonresonant stability); consumes N6-8 normal_form/nonresonant_case, S7-2, S7-3, S7-4 as designed, no added premise; (2) proof sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Nekhoroshev/Stability/Nonresonant*.lean (compare with branch inp-n68b).
