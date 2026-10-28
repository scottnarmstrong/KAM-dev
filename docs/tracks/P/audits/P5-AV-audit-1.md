# P5-AV independent audit 1

**Overall: PASS WITH NOTES for P5-AV infrastructure.** The signed averaging slice is complete and its proof uses the intended upstream averaging theorem. No material mathematical or interface defect was found. This package does not implement or seal a frozen theorem. In particular, **P-G / `properlyDegenerateKAM`: not seal-ready on the evidence of this package**; its manifest state remains `DRAFT_SORRY`. Frozen provider-type and seal-body probes are therefore not applicable to this slice, rather than silently counted as passing.

Audited worktree: `/root/code/KAM-inp-p5av`, HEAD `a05a4da2c925a5430a4de470e6494c13235fb468`, 2026-10-28. Scope: exactly the 16 `KAM/Planetary/PGAssembly/Averaging*.lean` files, 165 explicit public declarations (137 theorems, 26 definitions, one abbreviation, one structure). This report is the only repository edit. Audit probes were confined to this worktree's `.lake/abi-scratch/` and removed afterwards.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the supplied package audit brief and handoff/AUDIT FOCUS, P45 design Sections 2–5 and P5-AV row (502), Revision 4 (1986–2001), P45 design audits 1–3, current `/root/code/KAM-inp/.drafts/design/P45Signatures.lean` (967–1066), blueprint-P/parts/p5-pg-assembly.tex (169–179), graph packet's averaging records, the P-G track statement and relevant frozen definitions/anchor. Earlier design-audit conclusions were checked against the present proof, not treated as proof receipts.

## Scope and protected paths

`git diff inp...HEAD` warns that there are multiple merge bases and chooses `afb6301ada1fe4b0bd140a128551240afb925275`; `git merge-base --all inp HEAD` also lists `fb4f8fd5f66d30a1241f68e28ee3357cd46412c0`. The resulting full comparison contains 72 files, 10639 insertions and 154 deletions, including inherited packages and 44 generated-root additions. Those unrelated implementations are outside this audit's express scope.

`git diff inp...HEAD -- KAM/Frozen manifest README.md` has no diff output (only the merge-base warning). The literal brief's combined protected-path check including `KAM.lean` is **nonempty**, due to inherited generated-root integration. Package-local history does not edit that generated root; its latest root change is `fb4f8fd5` (P5-FI/S8-X integration). This is an integration note, not an averaging proof defect, and was not repaired in this report-only audit.

Commit `a324b554` renames signed `avg` to `pg_avg` in Averaging.lean and explains the name in its docstring. The current external signature already uses `pg_avg`. Commit `a05a4da2` touches 13 averaging modules and substitutes exactly these six identifiers and their references:

```
blockFast_append -> pgAv_blockFast_append
blockSlow_append -> pgAv_blockSlow_append
avgB -> pgAvB
avgPsi -> pgAvPsi
norm_dotC_le -> pgAv_norm_dotC_le
strip_mono -> pgAv_strip_mono
```

Independent before/after comparison, applying only those whole-identifier substitutions and ignoring comments/whitespace, finds no other Lean-code change in either commit. The handoff attributes the signed rename to the helper commit; the actual signed-rename commit is `a324b554`.

## Fidelity and proof analysis

All 20 signed declarations match their live fixture after removing whitespace: `PGAveraging`, `averagingDomain`, `realAverageMap`, `AveragingSpec`, `pgOscNormalize`, `pgOscUnnormalize`, `pgOscP`, `pgOscH`, `pgOscE`, `pgOscEpsilon`, `pgOscWidth`, `pgOscAlpha`, `pg_osc_hyp`, `pg_osc_bound`, `pg_osc_positive`, `pg_osc_zero`, `pg_osc_normalization`, `pg_osc_domain`, `pg_avg`, `pgAvg`. Definitions were compared including bodies; theorem comparisons include the complete telescope and result, excluding proof bodies. The signature fixture SHA256 is `586ed2e3188b154d5cc6d44d3f85b420ef85ddd7faaa2bcbb6d6ca6db7d0f304`. Seven fresh-name theorem copies of the signed statements elaborate with `by exact` applications of the implemented exports, preserving all explicit arguments in order. No extra assumption, changed carrier, enlarged constant dependence or weakened signed conclusion was found.

| Node | Implementing declarations | Verdict | Reason |
|---|---|---|---|
| bpP:p5:avg | PGAveraging, AveragingSpec, pg_avg, pgAvg | PASS | Joint map/remainder witness satisfies every signed clause; chosen record uses that existence proof. |
| stepP:p5:av-dict | pgOsc*, pg_osc_normalization, pg_osc_domain, avg_diff/inj/maps/periodic/real_mem/sympl, avg_chart | PASS | Exact mixed normalization, half-domain, conformal cancellation and physical lattice. |
| stepP:p5:av-R1 | core_divisor, pg_osc_divisor | PASS | Actual frozen Diophantine predicate, full complex-neighbourhood loss, corrected F7 divisor. |
| stepP:p5:av-R2 | gammaBar_sq, pg_osc_small, two_pi_avgB_le, avg_rem_fourier, avg_rem_pointwise | PASS | Existing G and radius bounds suffice; no new smallness threshold assumed. |
| stepP:p5:av-id | pg_osc_zero, avg_hamil, avg_disp | PASS | Normalized actual average, exact Hamiltonian identity and signed 12/18 constants. |

Let c=2*pi, L=LP, w=pgWidth, e=pgOscRadius, K=Kbar, gamma=gammaBar. The map T scales fast angles by c, fast actions by 1, and both oscillator blocks by sqrt(c). AveragingNorm.lean:98 proves T*Omega=c*Omega, including both oscillator coordinates; its inverse identities hold everywhere, including zero-dimensional ambient blocks. The P2 data are exactly H0/c, P(Tz)/L, L*mu/c, e/sqrt(c), w/c, and gamma/(2*c*K^tau). AveragingDom.lean:62 proves equality of the exact transformed half-domain with the signed physical domain.

AveragingDiv.lean:100 proves the divisor throughout the complex rhoBar-neighbourhood. The real core supplies gamma/|k|_1^tau; the derivative bound on the enclosing ball loses at most K*M0*rhoBar=gamma/(2*K^tau); H0/c divides the frequency by c. It does not reuse the excessive divisor rejected by design audit F7. AveragingSmall.lean:66 obtains OscHyp.small using G^2 >= 2^14*(1+b)*M0 and K*r^5 <= 1. These are conclusions of prior threshold/scales proofs, not new source premises.

AveragingBound.lean:176 proves the zero Fourier coefficient by an actual Lebesgue change of variables from [0,1]^a to [0,c]^a, including the normalization factor c^(-a). AveragingHamil.lean:54 applies the P2 Hamiltonian identity to T^-1 z, uses that zero coefficient, expands `pgRemainder = complexAverage - jetPolynomial`, and multiplies by c. The original extension, constructed average and jet functions remain attached throughout. Its `hm` premise is a distinctly named conditional transport lemma's input and is supplied by the same P2 witness in pg_avg; no hard step becomes a premise of pg_avg.

AveragingRem.lean:66 bounds the physical quadratic remainder by

```
1600*(1+b)*M0*(L*mu)^2*K^(2*tau+1)/(gamma^2*w) <= L*mu*r^5.
```

It uses rhoBar*w <= e^2, the first gamma branch and G^2*w >= 1600*(1+b)*M0. The exponential term is L*mu*r^5. AveragingFourier.lean:33 transports each Fourier coefficient with the factor c and inverse oscillator scaling. Its width identity is exact: Weighted.modeWeight((w/c)/6)=exp((w/6)*|k|_1). Summability is proved before using the weighted sum. The pointwise estimate uses oscClass plus the upstream norm_le_of_wsum theorem on the same half-domain, not merely a bound on real angles.

AveragingDisp.lean:56 states exactly **12** for fast actions and **18** for the product max norm of both oscillator blocks. Lines 167–175 derive 6 from the P2 fast-action constant 3 and then weaken to 12. Each oscillator constant 9 becomes 18; the product norm is a maximum, so no extra dimension or sqrt(2) factor enters here. The source's subsequent bounds proportional to r^(11/2) are numerical consequences of the parameter choices, not separately named exports in this signed slice. Indeed L*mu <= r^6, K>=1 and the first gamma branch give L*mu*K^tau/gamma <= r^(11/2)/G. The physical disc comparison using sqrt(2) belongs to the later location proof.

Revision 4 is respected: AveragingReal.lean:206 proves reality everywhere on the extension tube using holomorphic reflection, connectedness, conjugation invariance, and equality on a nonempty open real subset inside the original cylinder. The only call to `PGExtension.agrees` (line 264) supplies the cylinder-closure guard explicitly. No equality with arbitrary values of total d.P outside that cylinder is inferred. AveragingHyp.lean:151 then obtains RealOn for the actual normalized Hamiltonian perturbation.

Every module is reachable from Averaging.lean through the explicit imports, including the formerly untracked AveragingHamil.lean; there are no duplicate declarations or orphaned modules. A whole-KAM textual use scan finds six auxiliary leaf exports with no current consumer: `realInclusion_smul`, `actionNbhd_mono_left`, `actionNbhd_checkedCore_subset`, `continuous_pgOscNormalize`, `conjPi_conjPi`, `avgB_nonneg`. They are unused proved helpers, not dangling references or competing constructions. The intended downstream export `pgAvg` also has no current consumer in this checkout. This is harmless surplus infrastructure; all required helper definitions and module imports are present. A repository-wide declaration-name scan found no public short-name reuse with the 165 names elsewhere under KAM. The generated root was not rebuilt or regenerated: compatibility here is supported by name/import inspection and the targeted build, not claimed as a fresh root-build receipt.

## Definition classification (all 28)

| Declaration | Classification and whole-carrier meaning |
|---|---|
| PGAveraging | Produced-output record containing two functions, with no assumed specification field. |
| averagingDomain | Literal complex action neighbourhood, physical strip and oscillator max-norm half-box. |
| realAverageMap | Total real-part restriction of the complex map; on the certified real slice its inclusion equals the map. No claim of global real-valuedness of an arbitrary record. |
| AveragingSpec | Output proposition, not source data; all signed analytic, geometric, Fourier and displacement clauses are retained. |
| pgOscNormalize | Everywhere-defined diagonal linear normalization T, including oscillator sqrt(c) scales. |
| pgOscUnnormalize | Everywhere-defined inverse diagonal normalization; nonzero scales follow from pi>0. |
| pgOscP | Literal extension composed with T and divided by LP; LP>=1 rules out zero division in applications. |
| pgOscH | Literal H0/c on the whole complex action carrier. |
| pgOscE | Literal L*mu/c, not a fitted remainder estimate. |
| pgOscEpsilon | Literal e/sqrt(c). |
| pgOscWidth | Literal w/c; preserves the geometric/coefficient dictionary. |
| pgOscAlpha | Literal gamma/(4*pi*K^tau); admissibility proves positivity and valid denominators. |
| pgAvg | Classical choice of the joint averaging witness; choose_spec provides its specification. |
| avgV | Abbreviation for the exact P2 half-domain, not a replacement physical domain. |
| pgAvPsi | Everywhere-defined composition T o Psi o T^-1. |
| avgRem | Everywhere-defined physical remainder c*(R o T^-1). |
| diagCLM | Continuous linear diagonal multiplication on Fin n -> C. |
| oscScaleFst | Explicit coefficients c on fast and sqrt(c) on slow positions. |
| oscScaleSnd | Explicit coefficients 1 on fast and sqrt(c) on slow momenta. |
| oscNormCLM | CLM representation of T, equal to pgOscNormalize everywhere. |
| oscUnnormCLM | CLM representation of inverse T, equal to pgOscUnnormalize everywhere. |
| conjPi | Pointwise complex conjugation, with involution and norm preservation proved. |
| pkC | Concatenation of position and momentum vectors. |
| upkC | Exact inverse complex block split. |
| pkR | Real concatenation, compatible with complex inclusion. |
| upkR | Exact inverse real block split. |
| pgBase | Closed-cylinder inner box used as the real tube base; all fast angles are included. |
| pgAvB | Exact upstream quadratic-plus-exponential remainder expression. |

All are the intended functions/sets/records on their declared carriers. Total division outside admissibility in parameter formulas is ordinary Lean totalization, and no proof uses zero-denominator fallback values. Unconstrained values of upstream extension functions outside their specified tubes are not used to assert analytic or physical conclusions.

## Full declaration ledger

All names below are in KAM.Planetary. Locations are relative to KAM/Planetary/PGAssembly/. Conditional auxiliary transport lemmas are checked as such; they do not independently replace the unconditional source existence theorem. In the axiom column A means exactly [propext, Classical.choice, Quot.sound], B means exactly [propext, Quot.sound], and a dash marks a definition/structure rather than a printed theorem.

| Node / local obligation | Declaration and locator | Verdict | Reason | Axioms |
|---|---|---|---|---|
| bpP:p5:avg | `pg_avg` (Averaging.lean:28) | PASS | Joint upstream witnesses and complete signed output | A |
| bpP:p5:avg | `pgAvg` (Averaging.lean:47) | PASS | Joint upstream witnesses and complete signed output | — |
| av-dict / av-id | `torusCoeff_const_mul` (AveragingBound.lean:29) | PASS | Actual Fourier coefficients, unit bound and average identification | A |
| av-dict / av-id | `oscUnpack_flat` (AveragingBound.lean:37) | PASS | Actual Fourier coefficients, unit bound and average identification | A |
| av-dict / av-id | `normalize_assemble` (AveragingBound.lean:54) | PASS | Actual Fourier coefficients, unit bound and average identification | A |
| av-dict / av-id | `realInclusion_smul` (AveragingBound.lean:60) | PASS | Actual Fourier coefficients, unit bound and average identification | A |
| av-dict / av-id | `torusCoeff_pgOscP` (AveragingBound.lean:64) | PASS | Actual Fourier coefficients, unit bound and average identification | A |
| av-dict / av-id | `pg_P_torus_bound` (AveragingBound.lean:86) | PASS | Actual Fourier coefficients, unit bound and average identification | A |
| av-dict / av-id | `actionNbhd_checkedCore_le` (AveragingBound.lean:105) | PASS | Actual Fourier coefficients, unit bound and average identification | A |
| av-dict / av-id | `modeWeight_osc` (AveragingBound.lean:112) | PASS | Actual Fourier coefficients, unit bound and average identification | A |
| av-dict / av-id | `pg_osc_bound` (AveragingBound.lean:119) | PASS | Actual Fourier coefficients, unit bound and average identification | A |
| av-dict / av-id | `pg_osc_zero` (AveragingBound.lean:176) | PASS | Actual Fourier coefficients, unit bound and average identification | A |
| av-dict | `avgV` (AveragingConj.lean:31) | PASS | Conditional transport on the exact half-domain; input discharged in pg_avg | — |
| av-dict | `avg_diff` (AveragingConj.lean:35) | PASS | Conditional transport on the exact half-domain; input discharged in pg_avg | A |
| av-dict | `avg_inj` (AveragingConj.lean:43) | PASS | Conditional transport on the exact half-domain; input discharged in pg_avg | A |
| av-dict | `avg_maps` (AveragingConj.lean:50) | PASS | Conditional transport on the exact half-domain; input discharged in pg_avg | A |
| av-dict | `avg_periodic` (AveragingConj.lean:59) | PASS | Conditional transport on the exact half-domain; input discharged in pg_avg | A |
| av-dict | `avg_real_mem` (AveragingConj.lean:74) | PASS | Conditional transport on the exact half-domain; input discharged in pg_avg | A |
| av-dict | `realAverageMap_spec` (AveragingConj.lean:87) | PASS | Conditional transport on the exact half-domain; input discharged in pg_avg | A |
| av-dict | `symplFormC_normalize` (AveragingConj.lean:97) | PASS | Conditional transport on the exact half-domain; input discharged in pg_avg | A |
| av-dict | `symplFormC_unnormalize` (AveragingConj.lean:105) | PASS | Conditional transport on the exact half-domain; input discharged in pg_avg | A |
| av-dict | `avg_sympl` (AveragingConj.lean:113) | PASS | Conditional transport on the exact half-domain; input discharged in pg_avg | A |
| bpP:p5:avg | `PGAveraging` (AveragingDefs.lean:33) | PASS | Exact signed definition, including body | — |
| bpP:p5:avg | `averagingDomain` (AveragingDefs.lean:37) | PASS | Exact signed definition, including body | — |
| bpP:p5:avg | `realAverageMap` (AveragingDefs.lean:42) | PASS | Exact signed definition, including body | — |
| bpP:p5:avg | `AveragingSpec` (AveragingDefs.lean:46) | PASS | Exact signed definition, including body | — |
| bpP:p5:avg | `pgOscNormalize` (AveragingDefs.lean:82) | PASS | Exact signed definition, including body | — |
| bpP:p5:avg | `pgOscUnnormalize` (AveragingDefs.lean:86) | PASS | Exact signed definition, including body | — |
| bpP:p5:avg | `pgOscP` (AveragingDefs.lean:90) | PASS | Exact signed definition, including body | — |
| bpP:p5:avg | `pgOscH` (AveragingDefs.lean:92) | PASS | Exact signed definition, including body | — |
| bpP:p5:avg | `pgOscE` (AveragingDefs.lean:93) | PASS | Exact signed definition, including body | — |
| bpP:p5:avg | `pgOscEpsilon` (AveragingDefs.lean:94) | PASS | Exact signed definition, including body | — |
| bpP:p5:avg | `pgOscWidth` (AveragingDefs.lean:95) | PASS | Exact signed definition, including body | — |
| bpP:p5:avg | `pgOscAlpha` (AveragingDefs.lean:97) | PASS | Exact signed definition, including body | — |
| av-id | `avg_rem_diff` (AveragingDisp.lean:29) | PASS | Regularity/chart transport or signed physical 12/18 estimate | A |
| av-id | `avg_chart` (AveragingDisp.lean:38) | PASS | Regularity/chart transport or signed physical 12/18 estimate | A |
| av-id | `avg_disp` (AveragingDisp.lean:56) | PASS | Regularity/chart transport or signed physical 12/18 estimate | A |
| av-R1 | `pgAnalytic_dfast` (AveragingDiv.lean:29) | PASS | Real core plus controlled complex frequency loss and scaling | A |
| av-R1 | `modeSize_ge_one` (AveragingDiv.lean:36) | PASS | Real core plus controlled complex frequency loss and scaling | A |
| av-R1 | `pgAv_norm_dotC_le` (AveragingDiv.lean:44) | PASS | Real core plus controlled complex frequency loss and scaling | A |
| av-R1 | `dotC_sub` (AveragingDiv.lean:55) | PASS | Real core plus controlled complex frequency loss and scaling | A |
| av-R1 | `freq_pgOscH` (AveragingDiv.lean:59) | PASS | Real core plus controlled complex frequency loss and scaling | A |
| av-R1 | `core_divisor` (AveragingDiv.lean:72) | PASS | Real core plus controlled complex frequency loss and scaling | A |
| av-R1 | `dotC_div_const` (AveragingDiv.lean:88) | PASS | Real core plus controlled complex frequency loss and scaling | A |
| av-R1 | `pgOsc_K_eq` (AveragingDiv.lean:92) | PASS | Real core plus controlled complex frequency loss and scaling | A |
| av-R1 | `pg_osc_divisor` (AveragingDiv.lean:101) | PASS | Real core plus controlled complex frequency loss and scaling | A |
| av-dict | `sqrt_two_pi_pos` (AveragingDom.lean:27) | PASS | Exact block/domain scaling with positive scales | A |
| av-dict | `blockFast_normalize_fst` (AveragingDom.lean:29) | PASS | Exact block/domain scaling with positive scales | A |
| av-dict | `blockSlow_normalize_fst` (AveragingDom.lean:32) | PASS | Exact block/domain scaling with positive scales | A |
| av-dict | `blockFast_normalize_snd` (AveragingDom.lean:36) | PASS | Exact block/domain scaling with positive scales | A |
| av-dict | `blockSlow_normalize_snd` (AveragingDom.lean:39) | PASS | Exact block/domain scaling with positive scales | A |
| av-dict | `norm_real_smul_lt_iff` (AveragingDom.lean:43) | PASS | Exact block/domain scaling with positive scales | A |
| av-dict | `strip_smul_iff` (AveragingDom.lean:47) | PASS | Exact block/domain scaling with positive scales | A |
| av-dict | `pg_osc_positive` (AveragingDom.lean:54) | PASS | Exact block/domain scaling with positive scales | A |
| av-dict | `pg_osc_domain` (AveragingDom.lean:62) | PASS | Exact block/domain scaling with positive scales | A |
| av-dict / av-R1 / av-R2 | `pgAnalytic_LP_ge_one` (AveragingFacts.lean:30) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `pgAnalytic_M0_ge_one` (AveragingFacts.lean:34) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `pgAnalytic_rho_lt` (AveragingFacts.lean:38) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `pgAnalytic_rho_pos` (AveragingFacts.lean:42) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `pgOscRadius_le_delta` (AveragingFacts.lean:46) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `pgWidth_eq` (AveragingFacts.lean:49) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_r_lt_exp` (AveragingFacts.lean:51) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_r_lt_exp_fifth` (AveragingFacts.lean:55) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_mu_mem` (AveragingFacts.lean:58) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_Kbar_pos` (AveragingFacts.lean:61) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_Kbar_mul_width` (AveragingFacts.lean:67) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_Kbar_ge_one` (AveragingFacts.lean:70) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_gamma_pos` (AveragingFacts.lean:78) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_rhoBar_pos` (AveragingFacts.lean:81) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_dyn` (AveragingFacts.lean:89) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_rhoBar_le_rho` (AveragingFacts.lean:108) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_rhoBar_lt_delta` (AveragingFacts.lean:113) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_rhoBar_width` (AveragingFacts.lean:117) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `av_K_r5` (AveragingFacts.lean:122) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `checkedCore_subset_V` (AveragingFacts.lean:126) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `actionNbhd_mono_left` (AveragingFacts.lean:129) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `actionNbhd_checkedCore_subset` (AveragingFacts.lean:132) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-dict / av-R1 / av-R2 | `mem_oscDom_pg` (AveragingFacts.lean:142) | PASS | Projection of existing source/threshold facts or elementary set identity | A |
| av-R2 | `unnormalize_assemble` (AveragingFourier.lean:27) | PASS | Same-mode transport, summability and pointwise bound | A |
| av-R2 | `torusCoeff_avgRem` (AveragingFourier.lean:33) | PASS | Same-mode transport, summability and pointwise bound | A |
| av-R2 | `modeWeight_osc_sixth` (AveragingFourier.lean:49) | PASS | Same-mode transport, summability and pointwise bound | A |
| av-R2 | `avg_rem_fourier` (AveragingFourier.lean:57) | PASS | Same-mode transport, summability and pointwise bound | A |
| av-R2 | `avg_rem_pointwise` (AveragingFourier.lean:124) | PASS | Same-mode transport, summability and pointwise bound | A |
| av-id | `avgV_subset_zero_dom` (AveragingHamil.lean:29) | PASS | Same-domain identity transport and actual averaged jet/remainder | A |
| av-id | `blockSlow_unnormalize_fst` (AveragingHamil.lean:43) | PASS | Same-domain identity transport and actual averaged jet/remainder | A |
| av-id | `blockSlow_unnormalize_snd` (AveragingHamil.lean:47) | PASS | Same-domain identity transport and actual averaged jet/remainder | A |
| av-id | `blockFast_unnormalize_snd` (AveragingHamil.lean:51) | PASS | Same-domain identity transport and actual averaged jet/remainder | A |
| av-id | `avg_hamil` (AveragingHamil.lean:54) | PASS | Same-domain identity transport and actual averaged jet/remainder | A |
| av-dict / av-R1 / av-R2 | `pgAv_strip_mono` (AveragingHyp.lean:29) | PASS | Proved analytic/periodic/real/divisor/smallness inputs to OscHyp | A |
| av-dict / av-R1 / av-R2 | `normalize_eq_assemble` (AveragingHyp.lean:33) | PASS | Proved analytic/periodic/real/divisor/smallness inputs to OscHyp | A |
| av-dict / av-R1 / av-R2 | `normalize_mem_extensionDomain` (AveragingHyp.lean:38) | PASS | Proved analytic/periodic/real/divisor/smallness inputs to OscHyp | A |
| av-dict / av-R1 / av-R2 | `pgOscNormalize_real` (AveragingHyp.lean:67) | PASS | Proved analytic/periodic/real/divisor/smallness inputs to OscHyp | A |
| av-dict / av-R1 / av-R2 | `natAdd_ne_castAdd` (AveragingHyp.lean:74) | PASS | Proved analytic/periodic/real/divisor/smallness inputs to OscHyp | B |
| av-dict / av-R1 / av-R2 | `pgOscNormalize_shift` (AveragingHyp.lean:81) | PASS | Proved analytic/periodic/real/divisor/smallness inputs to OscHyp | A |
| av-dict / av-R1 / av-R2 | `oscFunction_smul` (AveragingHyp.lean:96) | PASS | Proved analytic/periodic/real/divisor/smallness inputs to OscHyp | A |
| av-dict / av-R1 / av-R2 | `pg_osc_bound_smul` (AveragingHyp.lean:100) | PASS | Proved analytic/periodic/real/divisor/smallness inputs to OscHyp | A |
| av-dict / av-R1 / av-R2 | `pg_osc_class` (AveragingHyp.lean:127) | PASS | Proved analytic/periodic/real/divisor/smallness inputs to OscHyp | A |
| av-dict / av-R1 / av-R2 | `pg_osc_real` (AveragingHyp.lean:151) | PASS | Proved analytic/periodic/real/divisor/smallness inputs to OscHyp | A |
| av-dict / av-R1 / av-R2 | `pg_osc_hyp` (AveragingHyp.lean:166) | PASS | Proved analytic/periodic/real/divisor/smallness inputs to OscHyp | A |
| av-dict | `pgAvPsi` (AveragingMap.lean:29) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | — |
| av-dict | `avgRem` (AveragingMap.lean:33) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | — |
| av-dict | `oscUnnormCLM` (AveragingMap.lean:37) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | — |
| av-dict | `pgOscUnnormalize_eq` (AveragingMap.lean:41) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `pgOscUnnormalize_eq_fun` (AveragingMap.lean:47) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `differentiable_pgOscUnnormalize` (AveragingMap.lean:51) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `continuous_pgOscUnnormalize` (AveragingMap.lean:55) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `pgOscNormalize_add` (AveragingMap.lean:59) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `pgOscUnnormalize_add` (AveragingMap.lean:63) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `pgOscNormalize_injective` (AveragingMap.lean:67) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `pgOscUnnormalize_injective` (AveragingMap.lean:70) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `pgOscNormalize_lattice` (AveragingMap.lean:74) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `pgOscUnnormalize_lattice` (AveragingMap.lean:81) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `pgOscUnnormalize_real` (AveragingMap.lean:88) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `pgOscNormalize_mem_range` (AveragingMap.lean:95) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `mem_averagingDomain_iff` (AveragingMap.lean:100) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `isOpen_averagingDomain` (AveragingMap.lean:110) | PASS | Everywhere-defined conjugation/linear algebra and exact domain | A |
| av-dict | `pgAv_blockFast_append` (AveragingNorm.lean:28) | PASS | Explicit diagonal scaling, inverse and conformal factor | B |
| av-dict | `pgAv_blockSlow_append` (AveragingNorm.lean:31) | PASS | Explicit diagonal scaling, inverse and conformal factor | B |
| av-dict | `append_blocks` (AveragingNorm.lean:34) | PASS | Explicit diagonal scaling, inverse and conformal factor | B |
| av-dict | `diagCLM` (AveragingNorm.lean:38) | PASS | Explicit diagonal scaling, inverse and conformal factor | — |
| av-dict | `diagCLM_apply` (AveragingNorm.lean:41) | PASS | Explicit diagonal scaling, inverse and conformal factor | A |
| av-dict | `oscScaleFst` (AveragingNorm.lean:44) | PASS | Explicit diagonal scaling, inverse and conformal factor | — |
| av-dict | `oscScaleSnd` (AveragingNorm.lean:47) | PASS | Explicit diagonal scaling, inverse and conformal factor | — |
| av-dict | `oscNormCLM` (AveragingNorm.lean:51) | PASS | Explicit diagonal scaling, inverse and conformal factor | — |
| av-dict | `pgOscNormalize_eq` (AveragingNorm.lean:55) | PASS | Explicit diagonal scaling, inverse and conformal factor | A |
| av-dict | `pgOscNormalize_eq_fun` (AveragingNorm.lean:60) | PASS | Explicit diagonal scaling, inverse and conformal factor | A |
| av-dict | `differentiable_pgOscNormalize` (AveragingNorm.lean:63) | PASS | Explicit diagonal scaling, inverse and conformal factor | A |
| av-dict | `continuous_pgOscNormalize` (AveragingNorm.lean:67) | PASS | Explicit diagonal scaling, inverse and conformal factor | A |
| av-dict | `pgOscUnnormalize_normalize` (AveragingNorm.lean:70) | PASS | Explicit diagonal scaling, inverse and conformal factor | A |
| av-dict | `pgOscNormalize_unnormalize` (AveragingNorm.lean:84) | PASS | Explicit diagonal scaling, inverse and conformal factor | A |
| av-dict | `pg_osc_normalization` (AveragingNorm.lean:98) | PASS | Explicit diagonal scaling, inverse and conformal factor | A |
| av-dict (Revision 4 reality) | `conjPi` (AveragingReal.lean:32) | PASS | Packing/conjugation and guarded reflection on connected tube | — |
| av-dict (Revision 4 reality) | `conjPi_conjPi` (AveragingReal.lean:34) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `conjPi_add` (AveragingReal.lean:37) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `norm_conjPi` (AveragingReal.lean:40) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `continuous_conjPi` (AveragingReal.lean:43) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `conjPi_realInclusion` (AveragingReal.lean:46) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `differentiableAt_conj_conj_pi` (AveragingReal.lean:50) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `differentiableOn_conj_conj_pi` (AveragingReal.lean:76) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `pkC` (AveragingReal.lean:85) | PASS | Packing/conjugation and guarded reflection on connected tube | — |
| av-dict (Revision 4 reality) | `upkC` (AveragingReal.lean:88) | PASS | Packing/conjugation and guarded reflection on connected tube | — |
| av-dict (Revision 4 reality) | `upkC_pkC` (AveragingReal.lean:90) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `pkC_upkC` (AveragingReal.lean:93) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `continuous_pkC` (AveragingReal.lean:95) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `continuous_upkC` (AveragingReal.lean:102) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `differentiable_upkC` (AveragingReal.lean:105) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `pkR` (AveragingReal.lean:111) | PASS | Packing/conjugation and guarded reflection on connected tube | — |
| av-dict (Revision 4 reality) | `upkR` (AveragingReal.lean:113) | PASS | Packing/conjugation and guarded reflection on connected tube | — |
| av-dict (Revision 4 reality) | `upkC_realInclusion` (AveragingReal.lean:115) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `pkC_realInclusion₂` (AveragingReal.lean:118) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `upkR_pkR` (AveragingReal.lean:125) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `continuous_upkR` (AveragingReal.lean:128) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `pgBase` (AveragingReal.lean:134) | PASS | Packing/conjugation and guarded reflection on connected tube | — |
| av-dict (Revision 4 reality) | `isPreconnected_pgBase` (AveragingReal.lean:137) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `isPreconnected_extensionDomain` (AveragingReal.lean:174) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `conj_mem_extensionDomain` (AveragingReal.lean:189) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-dict (Revision 4 reality) | `ext_P_real` (AveragingReal.lean:202) | PASS | Packing/conjugation and guarded reflection on connected tube | A |
| av-R2 | `pgAvB` (AveragingRem.lean:30) | PASS | Exact P2 constant and quantitative quadratic remainder bound | — |
| av-R2 | `avgB_nonneg` (AveragingRem.lean:34) | PASS | Exact P2 constant and quantitative quadratic remainder bound | A |
| av-R2 | `pg_osc_min_eq` (AveragingRem.lean:52) | PASS | Exact P2 constant and quantitative quadratic remainder bound | A |
| av-R2 | `two_pi_avgB_le` (AveragingRem.lean:66) | PASS | Exact P2 constant and quantitative quadratic remainder bound | A |
| av-R2 | `rpow_half_sq` (AveragingSmall.lean:28) | PASS | Elementary powers and existing G/radius bounds supply smallness | A |
| av-R2 | `rpow_five_halves_sq` (AveragingSmall.lean:37) | PASS | Elementary powers and existing G/radius bounds supply smallness | A |
| av-R2 | `gammaBar_sq` (AveragingSmall.lean:40) | PASS | Elementary powers and existing G/radius bounds supply smallness | A |
| av-R2 | `pg_osc_small` (AveragingSmall.lean:66) | PASS | Elementary powers and existing G/radius bounds supply smallness | A |

## Independent validation receipts

All Lean/Lake/checker invocations in this audit were serialized, with LEAN_NUM_THREADS=1 and nice -n 5. Waiting for the compile gate was allowed; no resource override, full-library build or cache mutation was requested.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5av KAM.Planetary.PGAssembly.Averaging
```

Output includes `[inp-gate] slot 2 acquired 17:29:36 for KAM.Planetary.PGAssembly.Averaging` and ends `Build completed successfully (9240 jobs).` Exit 0. The wrapper runs nice -n 5 lake build. Build warnings are style warnings (unused variables/simp arguments and unnecessary simpa), including in inherited dependencies, with no errors, sorry warnings or default-heartbeat failures.

2. Signature and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5AVProbe.lean
```

Exit 0; seven fresh-name signed theorem copies accepted exact export applications. All 137 explicit public theorems printed axioms: 133 printed A and four printed B (as identified individually in the ledger). No sorryAx or other additional axiom occurs. Sample exact output:

```
'KAM.Planetary.pg_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pg_osc_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pg_osc_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.avg_hamil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.avg_disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgAv_blockFast_append' depends on axioms: [propext, Quot.sound]
```

Additional chosen-output probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5AVChoice.lean
```

Exit 0. The example `AveragingSpec d r mu (pgAvg d r mu h)` is proved directly by `(pg_avg d r mu h).choose_spec`. Exact axiom output:

```
'KAM.Planetary.pgAvg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation over all 16 audited modules:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.Averaging KAM.Planetary.PGAssembly.AveragingBound KAM.Planetary.PGAssembly.AveragingConj KAM.Planetary.PGAssembly.AveragingDefs KAM.Planetary.PGAssembly.AveragingDisp KAM.Planetary.PGAssembly.AveragingDiv KAM.Planetary.PGAssembly.AveragingDom KAM.Planetary.PGAssembly.AveragingFacts KAM.Planetary.PGAssembly.AveragingFourier KAM.Planetary.PGAssembly.AveragingHamil KAM.Planetary.PGAssembly.AveragingHyp KAM.Planetary.PGAssembly.AveragingMap KAM.Planetary.PGAssembly.AveragingNorm KAM.Planetary.PGAssembly.AveragingReal KAM.Planetary.PGAssembly.AveragingRem KAM.Planetary.PGAssembly.AveragingSmall
```

Exit 0. Exact verbose output:

```
replaying KAM.Planetary.PGAssembly.AveragingSmall
replaying KAM.Planetary.PGAssembly.AveragingRem
replaying KAM.Planetary.PGAssembly.AveragingReal
replaying KAM.Planetary.PGAssembly.AveragingNorm
replaying KAM.Planetary.PGAssembly.AveragingMap
replaying KAM.Planetary.PGAssembly.AveragingHyp
replaying KAM.Planetary.PGAssembly.AveragingHamil
replaying KAM.Planetary.PGAssembly.AveragingFourier
replaying KAM.Planetary.PGAssembly.AveragingFacts
replaying KAM.Planetary.PGAssembly.AveragingDom
replaying KAM.Planetary.PGAssembly.AveragingDiv
replaying KAM.Planetary.PGAssembly.AveragingDisp
replaying KAM.Planetary.PGAssembly.AveragingDefs
replaying KAM.Planetary.PGAssembly.AveragingConj
replaying KAM.Planetary.PGAssembly.AveragingBound
replaying KAM.Planetary.PGAssembly.Averaging
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the expressly permitted generated-root exception. Exact output:

```
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (760 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module check, frozen-anchor guard and all 144 frozen declaration ABI hashes pass. No generated file was changed.

5. Static checks: no forbidden proof escape, resource override or EuclideanSpace in any audited file. All 16 have copyright, module, public imports, module docstring and exposed public noncomputable section. Files range from 52 to 278 physical lines (well below 1500); no 100-character line violation in this slice. Import-closure inspection traversed 194 KAM modules and found **no provider import and no frozen theorem import**. Frozen definition imports are permitted. All 16 modules are reachable; 165 explicit names are distinct and not redeclared elsewhere under KAM. No new global instance or alternate norm/carrier was installed.

## Notes, uncertainties, suspected defects and deviations

- Generated-root lint exception and inherited nonempty KAM.lean comparison are reported above; neither is silently repaired. No frozen declaration or manifest was changed.
- **Inherited blueprint imprecision, already documented by Revision 4:** blueprint-P/parts/p5-pg-assembly.tex, extension lemma (line 30) and step ext-per (line 35), states “$\tilde P=P$ at real points” on the enlarged extension domain. Such points may lie outside closure(cylinder V r0), where the total input function is unconstrained. This is the prior source imprecision described in P45 design Revision 4: equality needs the original cylinder-closure guard. The averaging implementation respects the repaired interface and proves extended-tube reality by reflection instead. This is not a new pinned-paper erratum, and no PDF was independently consulted in this package audit.
- **Minor local documentation defects:** AveragingDisp.lean:15 says the constants 12 and 18 are “each with a factor-two slack”. Only the fast 6-to-12 bound has that slack; the oscillator calculation gives exactly 18. AveragingRem.lean:12 and AveragingFourier.lean:12 tag the remainder estimates av-R1, whereas the blueprint's remainder/smallness step is av-R2. These are nonsemantic locator/prose issues; no fix was made under report-only scope.
- The handoff's “no uncertainties / deviations” omits these minor prose issues and the exact commit attribution for the rename. No mathematical deviation from the signed interface was found.
- No claim of full P-G proof, anchor sealing, graph closure or independently rebuilt generated-root compatibility follows from this audit. The complete signed P5-AV infrastructure is accepted; later assembly packages retain their own obligations.

Final workspace/diff check: `git diff --check` exits 0, and the report itself has no trailing whitespace. `git status --short` shows only this new report and the preexisting untracked `P5-AV-handoff.md`; no tracked repository file changed. All audit-owned scratch files were deleted.
