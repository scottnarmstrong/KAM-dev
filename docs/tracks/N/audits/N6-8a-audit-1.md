# Independent package audit N6-8a — audit 1

**Overall: PASS WITH NOTES for the scoped Arith*/Steps* infrastructure.** No blocking proof, statement, carrier, premise, or numerical defect found. This is not a seal-ready proof of `normal_form`, `nonresonant_case`, or any frozen Nekhoroshev anchor: those declarations are outside this session's deliverable. There is no provider export or frozen anchor in this package, so provider/frozen type-equality and seal-body probes are not applicable.

## Scope and comparison authority

Audited `/root/code/KAM-inp-n68a` at HEAD `7359a1c0edbb756e5209f2e96fbc7250425f29f7`, using the package brief, AGENTS.md, PLAN, DECISIONS, N6-8a handoff and its narrower AUDIT FOCUS, track-N statements, design v2 §7/§7.1 and Appendix A, both DESIGN-N67 design audits, and blueprint-N Part 6. The user's explicit report path overrides the generic brief's instruction to write in the main inp worktree.

`git diff inp...HEAD` was inspected. Intake `inp` was `ef8fc426c638557035e6101216aad4ef8b8a570e`; Git warned `multiple merge bases, using 33c688a1d1c9d25d7099f328479f4f53b0301bb4`. The other merge base was `66c3746f8b9043a5ce0287413f8f775e025dc0ac`. The broad diff has 11 files/1,861 inserted lines, including already-owned Iterative/IterativeReal infrastructure. As the focus requires, detailed proof review is ONLY the nine Arith*/Steps* files, also compared with `inp-n67` (`2675e0a54e803aa88ac46391116b2ff4465f3754`, common base `66c3746f8b9043a5ce0287413f8f775e025dc0ac`). That scoped diff is nine new files/1,710 lines. Unrelated inherited changes in the broader inp-n67 comparison are not N6-8a findings.

Inputs checked:

| Input | SHA-256 |
|---|---|
| Design v2 | `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2` |
| Supplied `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` | `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f` |
| Blueprint `p6-normal-form.tex` | `1c9c5e640ba0825040f1a2ad1de3aac9b38df9dbfcc1b280245ed53c3f2533ac` |
| N6-8a handoff | `b82b45076dd9577ec6f1420c552ed8373100c87d2715c949ccfbba7ee2e20669` |

## Fidelity, definition classification and consumer attachment

The signature file has no separate Arith/Steps signatures. Its exact `normal_form` source premises (L400–405) map field-for-field to `NFHyp` (StepsSeq L35–51). A fresh probe constructs that structure directly from the literal signature binders, and instantiates `nf_inv_all` at the planned floor with `rfl`. No nonresonance, Lipschitz, radius, smallness, reality, or step-invariant assumption is being silently added to the final theorem. The `NFInv` premises of intermediate helpers are paid by `nfInv_zero`/`nf_inv_succ`/`nf_inv_all` in Case A, and Case B uses the independently derived `nfCaseB_hyp`.

All **16 new definitions and one Prop structure** are classified below and individually in the declaration ledger:

- `nfRho`, `nfSig`, `nfR`, `nfS`: actual scheduled losses and recursive radii. They are total for all natural indices; at N=0, positive-index losses use Lean's total division and equal zero. No proof treats those as positive losses: admissible positive steps require i≤N and i>0, hence N≥1. At N=0 only step 0 is applied; the larger final domain is restricted to r/2,s/6. Negative/out-of-range radii carry no analytic claim.
- `nfEps1`, `nfB`, `nfBound`: explicit real arithmetic expressions, not disguised norms or arbitrary analytic objects. Their denominators/nonnegative inputs are guarded in uses; `nfBound` is used only after u≤1/4 or u≤1/256, so its inverse denominator is positive.
- `nfState`, `nfG`, `nfF`, `nfPhi`: genuine recursive iterG/iterF/iterMap constructions on the stipulated carrier. The total upstream flow is only used analytically where a derived IterHyp supplies its validity. No fallback value proves a map property.
- `nfGj`, `nfRj`, `nfSj`, `nfMj`: actual resonant increments, their original domains and carried bounds, indexed by Fin i.
- `NFHyp`: exactly source premises/typing data; no desired normal-form conclusion or instance is bundled.
- `NFInv`: an explicitly named derived Prop recording class/bound information of the actual sequence and past parts. It is proved by induction, rather than assumed at the final source interface.

The facades Arith and Steps contain only public imports and module boilerplate. All ambient actions/angles are `Fin n → ℂ`, real points `Fin n → ℝ`, modes `Fin n → ℤ`; max norms and geometric widths retain the 2π factors. The pair at index i is `(g_(i-1),f_i)`, so blueprint g_N is Lean `nfG ... (N+1)`, not `nfG ... N`.

For the future NormalForm consumer, `nf_step_props` supplies the exact U_(i+1)→U_i maps, holomorphy, symplecticity, integer translations, injectivity and two component displacements. `nf_disp_sums` has literally the two summands needed by `telescope`; `nfR_anti`/`nfS_anti` supply nesting and existing `isOpen_Dom` supplies openness. `nf_chain_identity` uses the correct composition order. `nf_final_f`, `nf_final_g`, `nf_final_g_diff` retain the final widths and constants. The stronger global equalities `nf_final_g_zero` and `nfCaseB_g` supply both required EqOn correction cases from design audit F2. `nf_real`/`nf_phi_real` expose conditional reality. The symmetry and reality premises are exactly the target's conditional clause.

Still owned by session 2: define `nfSteps`, prove coefficient support of the finite resonant sum using upstream projections/coefficient linearity, assemble Ψ and its chain properties/reality, and prove the full `normal_form`/`nonresonant_case` statements. Their absence is explicit scope, not a paid proof obligation. No root/graph/frozen theorem completion follows from this audit.

## Numerical review and notes

1. **Valid proof-route deviation:** StepsInduct L55–100 uses later weights ≤1 instead of the blueprint's ≤1/2, while retaining w0≤5/(8N). The resulting normalized estimate is `5/256 + (4/3)/256 = 19/768 < 1/16`. Smallness of the actual decomposition still follows; no theorem conclusion weakens. `induct_step` uses the exact rational `128/127*(1/16+1/256+1/8) = 49/254 < 1/4`, not an assumed decimal bound.
2. **Valid stronger arithmetic:** `eps1_le_div` proves ε1≤ε/κ; `eps1_le_quarter` follows for κ≥6. The floor proofs use non-strict 8N≤κ, sufficient for both sums. The action tail is ≤1/6 of qKε/(eα), giving factor 7/6 instead of 1.17; the angle factor is ≤8+4/3≤10. The zero-step case is separately handled in sums and correction bounds. All final numerical constants match the design.
3. **Minor handoff count:** the handoff says every file is ≤333 lines; ArithDisp has **334** lines. Every scoped file is below the planned 600-line target and the 1,500-line hard limit. This has no proof impact.
4. **Minor blueprint endpoint wording:** `blueprint-N/parts/p6-normal-form.tex:186` says “κ≥12 ln2 N>8N” while allowing N≥0. The sub-inequality `12 ln2 N>8N` is false at N=0 (0>0); for N≥1 it is true. Replace the universal chained inequality by `κ≥12 ln2 N≥8N`, and state strictness for N≥1 if needed. Lean `floor_facts` correctly proves the non-strict universal inequality. This is a blueprint wording defect, not a new suspected defect in the pinned paper.

## Declaration ledger

All names below are in `KAM.NormalForm`. Each row is a manually declared public definition/structure/theorem; constructor/projection names generated from NFHyp are covered by that structure's row. Four private support theorems are checked by the module replay; they are not public interface declarations. No named Arith/Steps declaration is frozen in the design signature file.

| Blueprint node / role | Declaration (local module:line) | Verdict | Reason |
|---|---|---|---|
| nf-first / nf-N | `nfRho` (ArithBase.lean:34) | PASS | Exact two-stage action loss; total division at N=0 is unused for positive step indices. |
| nf-first / nf-N | `nfSig` (ArithBase.lean:37) | PASS | Exact two-stage strip loss; same guarded N=0 behavior. |
| nf-N | `nfR` (ArithBase.lean:40) | PASS | Recursive action radii, subtracting twice each loss. |
| nf-N | `nfS` (ArithBase.lean:45) | PASS | Recursive strip widths, subtracting twice each loss. |
| nf-case (6.1) | `nfEps1` (ArithBase.lean:50) | PASS | Exact carried quadratic bound, including 2π. |
| nf-induct | `nfB` (ArithBase.lean:53) | PASS | B0=ε and B(i+1)=ε1/4^i; bounds rather than actual norms. |
| iterative (d) / nf-case | `nfBound` (ArithBase.lean:58) | PASS | Exact numerical expression of iterative_direct_d. |
| arithmetic / restriction support | `conjExp_pos'` (ArithBase.lean:67) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| arithmetic / restriction support | `exp_one_gt` (ArithBase.lean:71) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| arithmetic / restriction support | `two_div_exp_lt` (ArithBase.lean:76) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| arithmetic / restriction support | `log_two_gt` (ArithBase.lean:80) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| arithmetic / restriction support | `coef_mul_eq` (ArithBase.lean:85) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| arithmetic / restriction support | `small_iff_iterU` (ArithBase.lean:94) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| nf-first | `iterU_first` (ArithBase.lean:104) | PASS | Derives u0≤1/16 from (i),(ii); ε=0 allowed. |
| arithmetic / restriction support | `iterU_double` (ArithBase.lean:124) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| arithmetic / restriction support | `inv_one_sub_le` (ArithBase.lean:131) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| arithmetic / restriction support | `hi_mul` (ArithBase.lean:135) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| arithmetic / restriction support | `iterU_nonneg` (ArithBase.lean:144) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| arithmetic / restriction support | `nfEps1_nonneg` (ArithBase.lean:164) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| nf-case A | `nfBound_caseA` (ArithBase.lean:172) | PASS | Remainder bound ≤ quadratic ε1 under the first-step branch test. |
| nf-case B | `nfBound_caseB` (ArithBase.lean:204) | PASS | Doubled losses; correct negative exponential sign. |
| nf-N, zero steps | `quarter_lt_exp` (ArithBase.lean:245) | PASS | κ<12 log 2 implies 1/4<exp(-κ/6). |
| nf-N | `floor_facts` (ArithBase.lean:253) | PASS | Floor inequalities and 8N≤κ; valid also at N=0. |
| nf-concl (b) | `final_b` (ArithBase.lean:270) | PASS | Geometric carried bound ≤ exp(-κ/6) ε, including N=0. |
| nf-disp (c) | `disp_I` (ArithDisp.lean:32) | PASS | Action sum ≤qKε/α; tail≤(qKε/(eα))/6, N=0 handled separately. |
| nf-disp (c) | `disp_theta` (ArithDisp.lean:96) | PASS | Angle sum ≤10qε/(2παr), via 8+4/3≤10. |
| nf-disp (c), B | `disp_B` (ArithDisp.lean:150) | PASS | Both single-step displacement constants preserved. |
| nf-N / schedule support | `nfR_succ_closed` (ArithDisp.lean:186) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfS_succ_closed` (ArithDisp.lean:196) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfR_final` (ArithDisp.lean:207) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfS_final` (ArithDisp.lean:214) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfRho_nonneg` (ArithDisp.lean:223) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfSig_nonneg` (ArithDisp.lean:227) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfRho_ne_zero` (ArithDisp.lean:231) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfSig_ne_zero` (ArithDisp.lean:234) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfRho_pos` (ArithDisp.lean:237) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfSig_pos` (ArithDisp.lean:244) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfR_anti` (ArithDisp.lean:251) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfS_anti` (ArithDisp.lean:257) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfR_le_three` (ArithDisp.lean:263) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfS_le_two` (ArithDisp.lean:268) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfR_gt_two_rho` (ArithDisp.lean:273) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfS_gt_two_sig` (ArithDisp.lean:288) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfR_half_le` (ArithDisp.lean:303) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N / schedule support | `nfS_sixth_le` (ArithDisp.lean:308) | PASS | Elementary schedule identity/order/positivity with explicit guards; final equalities require N≥1, lower bounds allow N=0. |
| nf-N | `exp_sigma_le` (ArithDisp.lean:314) | PASS | Tail factor ≤1/8 from lower floor inequality and N≥1. |
| nf-case (6.1) | `eps1_le_div` (ArithInduct.lean:31) | PASS | Sharper ε1≤ε/κ, needed for angle displacement. |
| nf-case (6.1) | `eps1_le_quarter` (ArithInduct.lean:46) | PASS | ε1≤ε/4 follows from κ≥6. |
| nf-N (6.2) | `eps_le_sixtwo` (ArithInduct.lean:55) | PASS | Linear smallness with N≥1 and 8N≤κ. |
| nf-N (6.2) | `eps1_sixtwo` (ArithInduct.lean:74) | PASS | Quadratic smallness u(ε1)≤1/256. |
| nf-induct | `induct_step` (ArithInduct.lean:101) | PASS | Exact rational estimate 49/254<1/4; no decimal assumption. |
| arithmetic / restriction support | `iterU_mono` (ArithInduct.lean:133) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| arithmetic / restriction support | `iterU_lin` (ArithInduct.lean:140) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| arithmetic / restriction support | `sum_inv4_le` (ArithInduct.lean:145) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| nf-induct | `star_sum_le` (ArithInduct.lean:156) | PASS | Valid weaker intermediate weight bound 1; geometric sum 4/3. |
| nf-induct | `w0_le` (ArithInduct.lean:179) | PASS | First weight ≤5/(8N), retaining enough slack. |
| nf-induct | `star_small` (ArithInduct.lean:200) | PASS | 5/256+1/192=19/768≤1/16, with weaker later weights. |
| nf-concl (a) | `concl_a` (ArithInduct.lean:229) | PASS | Retains 16*(2qK/(αr))*ε²; κ≥8 required only for N≥1 branch. |
| arithmetic / restriction support | `realOn_mono'` (StepsCaseB.lean:36) | PASS | True algebraic, positivity, geometric-sum or domain-restriction helper; its explicit premises are discharged at uses. |
| nf-real (d) | `nf_real` (StepsCaseB.lean:41) | PASS | Inductive reality follows from upstream e; symmetry/reality premises remain conditional. |
| nf-real (d) | `nf_phi_real` (StepsCaseB.lean:70) | PASS | Each actual step preserves real points on its input domain. |
| nf-case B | `isDecomp_zero` (StepsCaseB.lean:97) | PASS | Empty Fin 0 decomposition, no hidden proof fields. |
| nf-case B | `nfCaseB_hyp` (StepsCaseB.lean:106) | PASS | Doubled-loss admissibility derived without assuming the branch test. |
| nf-case B / (b) | `nfCaseB_bound` (StepsCaseB.lean:121) | PASS | Correct exponential bound, restricted from s/3 to s/6. |
| nf-case B / (a) | `nfCaseB_g` (StepsCaseB.lean:140) | PASS | Global exact homRes equality, stronger than target EqOn. |
| nf-case B / (c) | `nfCaseB_disp` (StepsCaseB.lean:145) | PASS | Both coordinate bounds on the exact final domain. |
| nf-N | `nf_floor` (StepsInduct.lean:38) | PASS | Source hypotheses supply floor_facts input. |
| nf-N (6.2) | `nf_sixtwo` (StepsInduct.lean:46) | PASS | Both smallness estimates derived, not assumed. |
| nf-induct | `nf_star` (StepsInduct.lean:55) | PASS | Nonnegative decomposition norm and u(star)≤1/16 derived for 1≤i≤N. |
| nf-first / nf-induct | `nf_hyp` (StepsInduct.lean:104) | PASS | Builds IterHyp from source premises plus derived invariant; local Lipschitz/radius premises restricted correctly. |
| nf-case / nf-induct | `nf_inv_succ` (StepsInduct.lean:142) | PASS | Actual iterative c,d imply next carried invariant; hA used only at i=0. |
| nf-induct | `nf_inv_all` (StepsInduct.lean:190) | PASS | Closes all invariant premises for every i≤N+1 in Case A. |
| nf-concl | `nf_step_props` (StepsOut.lean:42) | PASS | All needed map properties and identity on U_(i+1); displacement components match sums. |
| nf-concl | `nf_chain_identity` (StepsOut.lean:84) | PASS | Correct composition order and shifted g_(m) indexing. |
| nf-disp | `nf_disp_sums` (StepsOut.lean:109) | PASS | Exact two summand expressions required by telescope. |
| nf-concl (b) | `nf_final_f` (StepsOut.lean:125) | PASS | Class and exponential bound on r/2,s/6, including zero-step restriction. |
| nf-concl (a), exact case | `nf_final_g_zero` (StepsOut.lean:141) | PASS | Global equality when N=0, stronger than required EqOn. |
| nf-concl support | `sum_inClass_wbound` (StepsOut.lean:161) | PASS | Finite sum class and summed bounds; hs>0 is available at s/6. |
| nf-concl | `nf_final_g` (StepsOut.lean:180) | PASS | Class of finite resonant sum on final domain. |
| nf-concl (a) | `nf_final_g_diff` (StepsOut.lean:197) | PASS | Correct quadratic correction constant; separate N=0 argument avoids κ≥8 assumption. |
| normal-form premises | `NFHyp` (StepsSeq.lean:35) | PASS | Exactly the 15 source/typing hypotheses of the v2 normal_form signature. |
| nf-induct | `nfState` (StepsSeq.lean:60) | PASS | Actual recursive iterG/iterF updates; pair at i is (g_(i-1),f_i). |
| nf-induct | `nfG` (StepsSeq.lean:68) | PASS | First projection of the actual state; index shifted by one from blueprint g_i. |
| nf-induct | `nfF` (StepsSeq.lean:71) | PASS | Second projection of the actual state. |
| nf-induct | `nfPhi` (StepsSeq.lean:74) | PASS | Actual iterMap with current remainder and scheduled losses. |
| nf-induct | `nfGj` (StepsSeq.lean:78) | PASS | Fin i indexed actual homRes increments. |
| nf-induct | `nfRj` (StepsSeq.lean:84) | PASS | Actual action radius of each part. |
| nf-induct | `nfSj` (StepsSeq.lean:87) | PASS | Actual strip width of each part. |
| nf-induct | `nfMj` (StepsSeq.lean:90) | PASS | Carried bound for each part. |
| nf-induct / sequence support | `nfG_zero` (StepsSeq.lean:97) | PASS | Exact state identity from recursion; no source premise added. |
| nf-induct / sequence support | `nfF_zero` (StepsSeq.lean:99) | PASS | Exact state identity from recursion; no source premise added. |
| nf-induct / sequence support | `nfG_succ` (StepsSeq.lean:101) | PASS | Exact state identity from recursion; no source premise added. |
| nf-induct / sequence support | `nfF_succ` (StepsSeq.lean:104) | PASS | Exact state identity from recursion; no source premise added. |
| nf-induct / sequence support | `nfG_eq_sum` (StepsSeq.lean:110) | PASS | Exact state identity from recursion; no source premise added. |
| nf-induct support | `nfB_nonneg` (StepsSeq.lean:120) | PASS | Nonnegativity/geometric bound follows from carried bounds. |
| nf-induct support | `nfB_le_eps1` (StepsSeq.lean:125) | PASS | Nonnegativity/geometric bound follows from carried bounds. |
| nf-induct | `NFInv` (StepsSeq.lean:131) | PASS | Derived invariant of remainder and earlier resonant parts, not an input to the final target. |
| nf-first | `nfInv_zero` (StepsSeq.lean:139) | PASS | Base invariant supplied by hf,hfb; empty past-part obligation. |
| nf-induct | `isDecomp_nfG` (StepsSeq.lean:143) | PASS | Exact finite decomposition from invariant and radius monotonicity. |
| nf-induct support | `FreqLipschitz.mono'` (StepsSeq.lean:156) | PASS | Valid radius restriction of the source Lipschitz predicate. |

## Independent hygiene and verification receipts

The checks below were independently rerun in this worktree, not copied from the prover's receipts. No auditor-started Lean command overlapped another. The compile gate's own command is `nice -n 5 lake build ...`; the environment sets LEAN_NUM_THREADS=1. Lint itself was launched at nice 5 so its ABI Lean child inherits that priority and the one-thread environment.

### Targeted build

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n68a KAM.Nekhoroshev.NormalForm.Steps KAM.Nekhoroshev.NormalForm.Arith
[inp-gate] slot 1 acquired 07:47:37 for KAM.Nekhoroshev.NormalForm.Steps KAM.Nekhoroshev.NormalForm.Arith
Build completed successfully (3238 jobs).
exit 0
```

### Kernel replay

One invocation, including both facades and every lemma module:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.NormalForm.Arith KAM.Nekhoroshev.NormalForm.ArithBase KAM.Nekhoroshev.NormalForm.ArithInduct KAM.Nekhoroshev.NormalForm.ArithDisp KAM.Nekhoroshev.NormalForm.Steps KAM.Nekhoroshev.NormalForm.StepsSeq KAM.Nekhoroshev.NormalForm.StepsInduct KAM.Nekhoroshev.NormalForm.StepsOut KAM.Nekhoroshev.NormalForm.StepsCaseB
replaying KAM.Nekhoroshev.NormalForm.StepsCaseB
replaying KAM.Nekhoroshev.NormalForm.StepsOut
replaying KAM.Nekhoroshev.NormalForm.StepsInduct
replaying KAM.Nekhoroshev.NormalForm.StepsSeq
replaying KAM.Nekhoroshev.NormalForm.Steps
replaying KAM.Nekhoroshev.NormalForm.ArithDisp
replaying KAM.Nekhoroshev.NormalForm.ArithInduct
replaying KAM.Nekhoroshev.NormalForm.ArithBase
replaying KAM.Nekhoroshev.NormalForm.Arith
exit 0
```

### Axioms and independent consumer probes

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-n68a-1-probe.lean
exit 0
83 axiom outputs; no warnings or errors.
```

The scratch probe imported only the built Steps facade, printed axioms of every new public theorem, constructed NFHyp from the literal v2 normal_form signature premises, applied nf_inv_all with the planned floor and rfl, and independently checked the N=0 final radii 3r/4,2s/3. Exact axiom output:

```text
'KAM.NormalForm.conjExp_pos'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.exp_one_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.two_div_exp_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.log_two_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.coef_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.small_iff_iterU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.iterU_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.iterU_double' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.inv_one_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.hi_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.iterU_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfEps1_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfBound_caseA' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfBound_caseB' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.quarter_lt_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.floor_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.final_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.disp_I' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.disp_theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.disp_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfR_succ_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfS_succ_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfR_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfS_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfRho_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfSig_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfRho_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfSig_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfRho_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfSig_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfR_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfS_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfR_le_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfS_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfR_gt_two_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfS_gt_two_sig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfR_half_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfS_sixth_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.exp_sigma_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.eps1_le_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.eps1_le_quarter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.eps_le_sixtwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.eps1_sixtwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.induct_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.iterU_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.iterU_lin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.sum_inv4_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.star_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.w0_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.star_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.concl_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.realOn_mono'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_phi_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.isDecomp_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfCaseB_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfCaseB_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfCaseB_g' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfCaseB_disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_sixtwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_star' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_inv_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_inv_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_step_props' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_chain_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_disp_sums' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_final_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_final_g_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.sum_inClass_wbound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_final_g' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_final_g_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfG_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfF_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfG_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfF_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfG_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfB_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfB_le_eps1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfInv_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.isDecomp_nfG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.FreqLipschitz.mono'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Source/import/protected-path hygiene

The local KAM import closure contains 86 modules; it contains no provider and no frozen theorem anchor, DRAFT_SORRY or otherwise. Its eight frozen definition imports (`ActionNbhd`, `ComplexStrip`, `HamiltonianVectorField`, `HamiltonianVectorFieldC`, `IsDiophantine`, `IsPrimaryOnStrip`, `IsRealOnReals`, `OmegaZero`) were read and checked against manifest state SEALED. No illicit proof source enters the package.

All nine scoped modules have copyright, module/import/docstring/public-section boilerplate; definitions are exposed through the section annotation. No forbidden proof escape, budget override, EuclideanSpace carrier, or nlinarith tactic occurs. All lines meet the 100-character rule. Counts use Python Unicode characters:

| File under KAM/Nekhoroshev/NormalForm | Lines | Maximum line width |
|---|---:|---:|
| Arith.lean | 20 | 99 |
| ArithBase.lean | 297 | 100 |
| ArithDisp.lean | 334 | 100 |
| ArithInduct.lean | 256 | 98 |
| Steps.lean | 22 | 98 |
| StepsCaseB.lean | 164 | 93 |
| StepsInduct.lean | 203 | 100 |
| StepsOut.lean | 250 | 99 |
| StepsSeq.lean | 164 | 98 |

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no diff; exit 0, apart from the recorded merge-base warning)
git diff --check inp...HEAD
(no whitespace diagnostics; exit 0, apart from that warning)
git diff --check
(no output; exit 0)
```

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (458 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

Disposition: PASS with the explicitly permitted generated-root exception. The sole failure is the expected `KAM.lean is out of date` diagnostic. The 100-character scan, forbidden-token/resource checks, module checks, source guard and all 144 ABI hashes pass. The generated root was not regenerated.



## Errata, deviations and limits

No new suspected pinned-source erratum was established by this scoped code/blueprint audit. The existing blueprint sourcegap at p6 L172 reports Pos93 p.194's positive exponent in Case B; this package uses the corrected negative exponent. The original paper was not independently re-audited here. The separate blueprint zero-step strictness issue and the two harmless arithmetic route deviations are recorded above. No frozen statement, premise, norm, carrier, generated file or source was altered.

Only this report is the auditor's persistent repository change. The pre-existing untracked N6-8a handoff is preserved. Auditor probe/inventory files are removed after verification. No state-changing git, delegation, library clean/rebuild, cache update or resource-budget override was used. All auditor Lean work, including the lint ABI subprocess, was serialized with LEAN_NUM_THREADS=1 and nice priority 5; unrelated campaign sessions were not controlled.
