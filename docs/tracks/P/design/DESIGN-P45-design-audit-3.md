# Independent delta design audit 3: P45

Overall verdict: **PASS**.

Audited HEAD `e1281e008078f0ce080cfd0d4a167f092ad8d01c`, compared with Revision 2 (`145a2ce0af84347d8f675bf7b65169b9301991d9`) and the assigned blueprint/graph contracts. F7 and F8 are resolved; prior F1–F6 and N2 repairs are preserved, and the N1 design-interface gate is now satisfied. No new material design defect was found in the revision. This approves the audited signatures and package design, not proof bodies, provider sealing or root closure.

## Scope and earlier findings

Read the current AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, exact audit brief, both earlier audit reports, Revision 3 diff/section, shared signatures, and designer handoff. Rechecked the changed adapter against P5:170–178 and the authoritative inp graph record `stepP:p5:av-R1`; compared the actual P2/P3 fixture theorem types with current P23Signatures. Re-read the actual frozen Diophantine/neighbourhood definitions used by the correction and checked the literal frozen main statement. `S:L` refers to `/root/code/KAM-inp/.drafts/design/P45Signatures.lean:L`; `D:L` refers to the design Markdown.

An independent normalized declaration comparison finds exactly one added declaration (`pgOscAlpha`), exactly one changed declaration (`pg_osc_hyp`), and no removed declarations. `pgD0` moved without changing its definition. All other declarations, including prior repairs and upstream fixtures, retain their previous types and bodies. The updated prose, node ownership, package inputs/outputs, DAG and validation claims were also checked.

| Earlier finding | Verdict | Current evidence |
|---|---|---|
| F1 — collar scope/conclusions | PASS, closed | S:307–329 retains all-positive-radius compactness and exact difference; conditional measure, lower measure and neighbourhood clauses remain. |
| F2 — coefficient continuity/symmetry | PASS, closed | S:632–648 retains joint parameter continuity and complex beta symmetry as outputs accompanying birkhoff_ext. |
| F3 — radius-2 bounds | PASS, closed | S:696–700 and PGAnalyticSpec retain radius-2 bound domain, distinct from radius-1 inverse domain. |
| F4 — source μ range | PASS, closed | PGAnalyticSpec still proves muStar≤mu0; no unconstrained μ enters freq_inj. |
| F5 — explicit numerical constants | PASS, closed | dioConstant/dio_one and pgMeasureUpper1/2/pgBudget/budget retain their explicit data-only formulas; positive enclosing Ry enlargement remains declared. |
| F6 — polar null coverage | PASS, closed | S:512–520 retains the numeric volume and null complement of the polar image. |
| F7 — excessive divisor constant | PASS, closed | S:1027–1033 supplies gammaBar/(4*pi*Kbar^tau), exactly the source cutoff/neighbourhood bound after Hamiltonian scaling; D:337–377 updates every affected numerical estimate. |
| F8 — package cycle | PASS, closed | S:919–921 and D:190,500–505,520–522 place unchanged pgD0 in Parameters before both KAMInputs and Family; Family no longer owns it. |
| N1 — concrete upstream interfaces | PASS, closed as a design gate | Exact P23 fixtures and both typed applications remain; the averaging application now receives the corrected α. No extra frozen input is introduced. |
| N2 — helper ownership | PASS, closed | ext_conn precedes collar, beta_inverse precedes slow resonance work, and section_measure_le_of_pairwise_dist remains exported. Abstract/actual cut-measure ownership remains separated. |

## Changed mathematics and consumer verification

**F7 fidelity.** Write c=2*pi, K=Kbar, gamma=gammaBar, rho=rhoBar, w=pgWidth, e=pgOscRadius, L=LP. At a core point the actual frozen IsDiophantine predicate supplies gamma/|k|₁^tau. For 0<|k|₁≤K this is at least gamma/K^tau. The derivative bound M0 and `rho=gamma/(2*M0*K^(tau+1))` give a loss at most `K*M0*rho=gamma/(2*K^tau)` throughout the frozen complex action neighbourhood. Dividing H0 by c divides its frequency by c. The supplied constant is therefore `gamma/(2*c*K^tau)`, exactly pgOscAlpha. The earlier quadratic-H0 counterexample no longer contradicts the signature. No source premise, carrier or Diophantine predicate was strengthened or replaced.

**Remainder and smallness.** The delivered averaging theorem bounds its quadratic remainder by `400*(1+b)*mu'^2/(c*alpha*min(rho*s0,epsilon0^2))`. With `mu'=L*mu/c`, `s0=w/c`, `epsilon0=e/sqrt(c)` and physical remainder multiplied by c, this becomes

```text
800*(1+b)*L^2*mu^2*K^tau / (gamma*min(rho*w,e^2)).
```

The existing radius output gives rho*w≤e². Substituting rho and the first branch of gamma gives

```text
1600*(1+b)*M0*L^2*mu^2*K^(2*tau+1)/(gamma^2*w)
  ≤ [1600*(1+b)*M0/(G^2*w)]*L*mu*r^5
  ≤ L*mu*r^5.
```

The existing G bound supplies the last step. The exponential term is L*mu*r^5, so their sum is the unchanged exported 2*L*mu*r^5. Independently, substitution into OscHyp.small reduces it to the sufficient condition `G^2≥2^14*(1+b)*M0*K*r^5`; existing G and K*r^5≤1 bounds supply it. Positivity of widths, μ, K, gamma and normalization scales is available under admissibility, so these divisions do not invoke junk values.

**Displacements.** Conjugation by T multiplies each oscillator coordinate by sqrt(c), leaves fast actions unchanged, and multiplies fast angles by c. The delivered inequalities consequently give physical fast-action displacement ≤6*L*mu*K^tau/(gamma*w) and each oscillator block ≤18*L*mu*K^tau/(gamma*e). These imply the unchanged AveragingSpec constants 12 and 18. The common conformal factor cancels in `T∘Psi∘T⁻¹`. The zero-mode identity, weighted width w/6 and exact half-domain equality are unchanged. The corrected hypothesis record can therefore supply the actual averaged_remainder application without changing its type or adding assumptions.

**F8 consumers and packages.** pgD0 uses only pgActionDomain, params, the P4 real frequency formula and the P1 two-scale predicate. The declared Parameters imports now supply all four before KAMInputs references pgD0 in pg_kam_dictionary. Family remains downstream and consumes the same predicate. All 36 named local packages have strictly earlier named package inputs; the largest estimated module is 750 lines. The separate 1,286-line fixture is also below the Lean cap. The provider remains quarantined, and no reverse import into Parameters is required.

The unchanged P3 scale dictionary still matches its actual KamHyp and joint two_scale_kam output: s=w/60, sbar=w/15, geometric total width w/(24*pi), L=initialL=C1/mu, and the same D0/rhoHat/Ehat. P1 cyl_pipeline consumes the same chart/lattice data with the same period-one frequency. Raw input-cell Lipschitz bounds serve null-image arguments; the output cell serves measure transfer. No averaging-cell-preservation premise was added. Searches still find no direct P4/P5 label consumer in I or N; P3b's frequency/measure dictionary remains unchanged.

## Declaration-by-declaration disposition

All 202 explicit declarations are inventoried below (69 theorem stubs); the two derivative/planetary frequency names are distinguished by namespace. Unchanged rows carry forward the prior independent type audit after exact declaration comparison; altered rows were checked directly as above. Every PASS is a design-contract verdict, not a proved-body receipt.

| Lean name (S line) | Blueprint role | Verdict | Reason |
|---|---|---|---|
| `KAM.NormalForm.zBall` (38) | `bpP:p2:osc-averaging / exact divisor fixture` | PASS | Exact delivered NormalForm fixture; no carrier change. |
| `KAM.NormalForm.freq` (39) | `bpP:p2:osc-averaging / exact divisor fixture` | PASS | Exact delivered NormalForm fixture; no carrier change. |
| `KAM.NormalForm.dotC` (40) | `bpP:p2:osc-averaging / exact divisor fixture` | PASS | Exact delivered NormalForm fixture; no carrier change. |
| `KAM.NormalForm.DivisorBound` (41) | `bpP:p2:osc-averaging / exact divisor fixture` | PASS | Exact delivered NormalForm fixture; no carrier change. |
| `twoScaleDiophantine` (50) | `bpP:p1:two-scale` | PASS | Source formula/carrier; no changed norm or global instance. |
| `IsLatticeTorus` (59) | `bpP:p1:lattice-torus` | PASS | Exact delivered P23 fixture. |
| `CPhase` (68) | `bpP:p2:conv / carrier fixture` | PASS | Exact delivered P23 fixture. |
| `CHam` (69) | `bpP:p2:conv / carrier fixture` | PASS | Exact delivered P23 fixture. |
| `geometricWidth` (70) | `bpP:p3:period-dictionary` | PASS | Exact delivered P23 fixture. |
| `realBase` (71) | `bpP:p3:conv` | PASS | Exact delivered P23 fixture. |
| `coefficientDom` (72) | `bpP:p3:conv` | PASS | Exact delivered P23 fixture. |
| `realTube` (74) | `bpP:p3:conv` | PASS | Exact delivered P23 fixture. |
| `firstBlock` (76) | `bpP:p2:conv / coordinate fixture` | PASS | Exact delivered P23 fixture. |
| `lastBlock` (78) | `bpP:p2:conv / coordinate fixture` | PASS | Exact delivered P23 fixture. |
| `oscPack` (80) | `bpP:p2:osc-averaging / packing` | PASS | Exact delivered P23 fixture. |
| `oscUnpack` (83) | `bpP:p2:osc-averaging / unpacking` | PASS | Exact delivered P23 fixture. |
| `oscFunction` (86) | `bpP:p2:osc-averaging / Fourier carrier` | PASS | Exact delivered P23 fixture. |
| `oscParams` (87) | `bpP:p2:osc-averaging / parameter domain` | PASS | Exact delivered P23 fixture. |
| `oscDom` (91) | `bpP:p2:osc-averaging / domain` | PASS | Exact delivered P23 fixture. |
| `oscBound` (93) | `bpP:p2:osc-averaging / norm` | PASS | Exact delivered P23 fixture. |
| `oscClass` (96) | `bpP:p2:osc-averaging / analyticity` | PASS | Exact delivered P23 fixture. |
| `OscHyp` (100) | `bpP:p2:osc-averaging` | PASS | Exact delivered P23 fixture. |
| `averaged_remainder` (115) | `bpP:p2:averaged-remainder` | PASS | Exact delivered P23 fixture. |
| `ScaleData` (144) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `constants` (157) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `cutoff` (163) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `rhoHat` (164) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `eHat` (165) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `kamConstant` (166) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `complementConstant` (167) | `bpP:p3:two-scale-kam` | PASS | Exact delivered P23 fixture. |
| `initialL` (168) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `realFreq` (169) | `bpP:p3:conv` | PASS | Exact delivered P23 fixture. |
| `dioBase` (171) | `bpP:p3:two-scale-kam` | PASS | Exact delivered P23 fixture. |
| `omegaSet` (174) | `bpP:p3:two-scale-kam` | PASS | Exact delivered P23 fixture. |
| `KamHyp` (177) | `bpP:p3:interface` | PASS | Exact delivered P23 fixture. |
| `limitmap_data` (203) | `bpP:p3:limit-phi` | PASS | Exact delivered P23 fixture. |
| `two_scale_kam` (204) | `bpP:p3:two-scale-kam` | PASS | Exact delivered P23 fixture. |
| `blockFast` (250) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `blockSlow` (251) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `blockFast_real` (252) | `bpP:p4:conv#data` | PASS | Matches source role; no additional defect found. |
| `blockSlow_real` (253) | `bpP:p4:conv#data` | PASS | Matches source role; no additional defect found. |
| `PGData` (256) | `bpP:p5:order` | PASS | Literal frozen premises; connected includes nonempty. |
| `pgBoundaryA` (288) | `bpP:p5:order` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgBoundaryD` (290) | `bpP:p5:order` | PASS | Source formula/carrier; no changed norm or global instance. |
| `realNbhd` (293) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `innerCore` (296) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `actionShell` (299) | `bpP:p4:conv#shell` | PASS | Source formula/carrier; no changed norm or global instance. |
| `joinedActions` (301) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `unitCube` (304) | `bpP:p1:torus-union` | PASS | Source formula/carrier; no changed norm or global instance. |
| `collar` (307) | `bpP:p4:collar` | PASS | F1 resolved: scoped compactness, differences and measures. |
| `ext_deriv` (328) | `bpP:p4:ext-deriv` | PASS | Derivative analyticity; partial-C1 Lipschitz work is separately packaged. |
| `ext_conn` (332) | `bpP:p4:ext-conn` | PASS | Matches source role; no additional defect found. |
| `realNbhd_joinedActions` (335) | `bpP:p4:domain-collar / helper` | PASS | Exact max-norm product, including empty factors. |
| `lip_compact_c1` (339) | `bpP:p4:lip-compact / conditional helper` | PASS | Distinct conditional helper; does not replace partial-C1 result. |
| `lip_compact` (346) | `bpP:p4:lip-compact` | PASS | Matches source role; no additional defect found. |
| `lip_inverse` (354) | `bpP:p4:lip-inverse` | PASS | Matches source role; no additional defect found. |
| `pgInverse` (365) | `bpP:p4:lip-inverse` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgInverseL` (368) | `bpP:p4:lip-inverse` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgInverseR` (371) | `bpP:p4:lip-inverse` | PASS | Source formula/carrier; no changed norm or global instance. |
| `beta_inverse` (374) | `bpP:p4:beta-inverse` | PASS | Dropping symmetry is a true stronger adjugate estimate. |
| `secularPolynomial` (379) | `bpP:p4:freq` | PASS | Source formula/carrier; no changed norm or global instance. |
| `slowFrequency` (385) | `bpP:p4:freq` | PASS | Source formula/carrier; no changed norm or global instance. |
| `freq` (390) | `bpP:p4:freq` | PASS | Source formula/carrier; no changed norm or global instance. |
| `MeasureData` (399) | `bpP:p4:data` | PASS | Unchanged faithful type; corrected averaging adapter supplies its input. |
| `affine_slab` (447) | `bpP:p4:affine-slab` | PASS | Matches source role; no additional defect found. |
| `latticeWeight` (452) | `bpP:p4:lattice-tail` | PASS | Source formula/carrier; no changed norm or global instance. |
| `lattice_tail` (454) | `bpP:p4:lattice-tail` | PASS | Matches source role; no additional defect found. |
| `resonanceBad` (463) | `bpP:p4:two-scale-diophantine-measure` | PASS | Source formula/carrier; no changed norm or global instance. |
| `latticeS` (469) | `bpP:p4:lattice-tail` | PASS | Source formula/carrier; no changed norm or global instance. |
| `measure_c1` (471) | `bpP:p4:two-scale-diophantine-measure` | PASS | Source formula/carrier; no changed norm or global instance. |
| `measure_c2` (476) | `bpP:p4:two-scale-diophantine-measure` | PASS | Source formula/carrier; no changed norm or global instance. |
| `two_scale_diophantine_measure` (478) | `bpP:p4:two-scale-diophantine-measure` | PASS | Matches source role; no additional defect found. |
| `domain_collar_helper` (488) | `bpP:p4:domain-collar / helper` | PASS | Matches source role; no additional defect found. |
| `oscillatorPolar` (496) | `bpP:p4:s-disc#chart` | PASS | General a,b formula agrees with P7 at a=b. |
| `polarMap` (502) | `bpP:p4:disc-measure / P7 specialization` | PASS | Owner snapshot; specialization bridge explicit. |
| `oscillatorPolar_eq_polarMap` (506) | `bpP:p4:disc-measure / P7 specialization` | PASS | Matches source role; no additional defect found. |
| `polarCellMap` (509) | `bpP:p4:s-disc#chart` | PASS | Source formula/carrier; no changed norm or global instance. |
| `disc_measure` (512) | `bpP:p4:disc-measure` | PASS | F6 resolved: numeric volume and null-image coverage. |
| `disc_measure_image` (521) | `bpP:p4:disc-measure` | PASS | Positive-action cell injectivity; exact (2*pi)^n factor. |
| `disc_measure_shell` (527) | `bpP:p4:disc-measure` | PASS | Matches source role; no additional defect found. |
| `PGComplexPhase` (533) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `assembleComplex` (535) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `extensionDomain` (538) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGExtension` (543) | `bpP:p5:ext` | PASS | Produced witness, no extra provider assumption. |
| `ext` (568) | `bpP:p5:ext` | PASS | Matches source role; no additional defect found. |
| `pgExtension` (570) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgWidth` (572) | `bpP:p5:consts` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgOscRadius` (574) | `bpP:p5:consts` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexAverage` (576) | `bpP:p5:consts` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexAverage_real` (582) | `bpP:p5:birkhoff-ext` | PASS | Uses actual frozen normalized secularAverage. |
| `jetP0` (588) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `jetOmega` (590) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `jetBeta` (593) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `jetPolynomial` (598) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgRemainder` (602) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `consts` (606) | `bpP:p5:consts` | PASS | Matches source role; no additional defect found. |
| `birkhoff_ext` (616) | `bpP:p5:birkhoff-ext` | PASS | Unchanged outputs; F2 completed by regularity companion. |
| `birkhoff_ext_parameter_regularity` (632) | `bpP:p5:birkhoff-ext` | PASS | F2 resolved: joint continuity and complex symmetry. |
| `uniform_remainder` (649) | `bpP:p5:uniform-remainder` | PASS | Matches source role; no additional defect found. |
| `lip_complex` (654) | `bpP:p5:lip-complex` | PASS | Matches source role; no additional defect found. |
| `complexFast` (661) | `bpP:p5:bilip` | PASS | Source formula/carrier; no changed norm or global instance. |
| `bilip` (664) | `bpP:p5:bilip` | PASS | Matches source role; no additional defect found. |
| `dioConstant` (670) | `bpP:p5:dio-one` | PASS | F5 resolved: explicit chosen-inverse formula. |
| `dio_one` (673) | `bpP:p5:dio-one` | PASS | F5 resolved: explicit constant estimate. |
| `PGAnalytic` (680) | `bpP:p5:freq-data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `analyticDomain` (693) | `bpP:p5:freq-inj` | PASS | Radius-1 inverse domain unchanged; separate radius-2 bound domain now supplied. |
| `analyticBoundDomain` (696) | `bpP:p5:freq-data` | PASS | F3 resolved: radius-2 bound domain only. |
| `complexIntegrable` (702) | `bpP:p5:freq-inj` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexFrequency` (705) | `bpP:p5:freq-inj` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGAnalyticSpec` (709) | `bpP:p5:freq-data` | PASS | F3/F4 resolved: radius-2 bounds; muStar≤mu0. |
| `freq_data` (739) | `bpP:p5:freq-data` | PASS | Produces corrected output specification; no new assumption. |
| `pgAnalytic` (741) | `bpP:p5:freq-data` | PASS | Choice from output witness, not an added hypothesis. |
| `pgCU` (743) | `bpP:p5:freq-inj` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexFrequency_real` (746) | `bpP:p5:freq-inj` | PASS | Identifies derivatives only on V; no boundary claim. |
| `freq_inj` (751) | `bpP:p5:freq-inj` | PASS | F4 resolved: source interval now covers the entire claim. |
| `IsChart` (763) | `bpP:p1:chart` | PASS | Owner snapshot, same analytic and frozen symplectic predicates. |
| `fullShift` (766) | `bpP:p1:period-convert` | PASS | Source formula/carrier; no changed norm or global instance. |
| `angleScale` (768) | `bpP:p1:period-convert` | PASS | Source formula/carrier; no changed norm or global instance. |
| `disc_measure_chart` (770) | `bpP:p4:disc-measure` | PASS | Analytic/symplectic polar chart, determinant and lattice injectivity. |
| `resonanceBad_eq` (781) | `bpP:p4:two-scale-diophantine-measure` | PASS | Matches source role; no additional defect found. |
| `local_real_complexification` (785) | `bpP:p5:ext-loc / helper` | PASS | Matches source role; no additional defect found. |
| `compact_real_complexification` (792) | `bpP:p5:ext-loc / helper` | PASS | Matches source role; no additional defect found. |
| `real_slice_identity` (801) | `bpP:p5:ext-glue / helper` | PASS | Matches source role; no additional defect found. |
| `connected_complex_tube` (808) | `bpP:p5:be-jet / helper` | PASS | Matches source role; no additional defect found. |
| `fourth_jet_unique` (813) | `bpP:p5:be-coef / helper` | PASS | Matches source role; no additional defect found. |
| `schwarz_order_five` (820) | `bpP:p5:ur-schwarz / helper` | PASS | Matches source role; no additional defect found. |
| `schur_inverse_blocks` (826) | `bpP:p5:fi-inv / helper` | PASS | Matches source role; no additional defect found. |
| `finite_measure_coordinate_cut` (834) | `bpP:p5:st-ivt / helper` | PASS | Matches source role; no additional defect found. |
| `section_measure_le_of_pairwise_dist` (839) | `bpP:p4:ext-tonelli` | PASS | N2 resolved: arbitrary real sections, including nonmeasurable sets. |
| `ext_tonelli` (844) | `bpP:p4:ext-tonelli` | PASS | Product-coordinate Tonelli; auxiliary diameter helper is N2. |
| `log_power_dominated` (850) | `bpP:p5:kam-cond#scales / helper` | PASS | Matches source role; no additional defect found. |
| `kam_c1` (854) | `bpP:p5:kam-hyp#C1` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGScales` (859) | `bpP:p5:kam-cond` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgTau` (864) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgK0` (866) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgChat` (869) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGScaleSpec` (871) | `bpP:p5:kam-cond` | PASS | Source formula/carrier; no changed norm or global instance. |
| `kam_cond` (879) | `bpP:p5:kam-cond` | PASS | Matches source role; no additional defect found. |
| `pgScales` (881) | `bpP:p5:kam-cond` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGParameters` (884) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `params` (900) | `bpP:p5:params` | PASS | Literal formulas; K0 data-only; period-one gamma thresholds. |
| `checkedCore` (912) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgActionDomain` (915) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgD0` (919) | `bpP:p5:kset` | PASS | F8 closed: same predicate; early Parameters owner/imports. |
| `admissible` (923) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgCgamma` (927) | `bpP:p5:rstar#Cgamma` | PASS | Source formula/carrier; no changed norm or global instance. |
| `rstar` (930) | `bpP:p5:rstar` | PASS | Data-only preliminary threshold; final measure shrink separated. |
| `pgRstar` (953) | `bpP:p5:rstar` | PASS | Source formula/carrier; no changed norm or global instance. |
| `param_facts` (955) | `bpP:p5:param-facts` | PASS | Other source guards are in rstar; no new frozen premise. |
| `r_k` (962) | `bpP:p5:rK` | PASS | Matches source role; no additional defect found. |
| `PGAveraging` (967) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `averagingDomain` (971) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `realAverageMap` (975) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `AveragingSpec` (979) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgOscNormalize` (1012) | `bpP:p5:avg / conformal normalization` | PASS | Correct conformal factor 2*pi, including oscillator scaling. |
| `pgOscUnnormalize` (1016) | `bpP:p5:avg / inverse normalization` | PASS | Exact inverse of normalization on the full carrier. |
| `pgOscP` (1020) | `bpP:p5:avg / normalized perturbation` | PASS | New adapter definition; correct constrained carrier and scaling. |
| `pgOscH` (1022) | `bpP:p5:avg / normalized Hamiltonian` | PASS | Unchanged faithful type; corrected averaging adapter supplies its input. |
| `pgOscE` (1023) | `bpP:p5:avg / normalized size` | PASS | New adapter definition; correct constrained carrier and scaling. |
| `pgOscEpsilon` (1024) | `bpP:p5:avg / oscillator radius` | PASS | New adapter definition; correct constrained carrier and scaling. |
| `pgOscWidth` (1025) | `bpP:p5:avg / geometric width` | PASS | New adapter definition; correct constrained carrier and scaling. |
| `pgOscAlpha` (1027) | `stepP:p5:av-R1 / bpP:p5:avg` | PASS | F7 closed: cutoff, neighbourhood half-loss and 2*pi scaling. |
| `pg_osc_hyp` (1029) | `stepP:p5:av-R1 / av-R2` | PASS | Correct α; existing G/radius guards supply the source record. |
| `pg_osc_bound` (1034) | `bpP:p5:avg / unit perturbation` | PASS | Original weighted bound survives normalized Fourier slice. |
| `pg_osc_positive` (1037) | `bpP:p5:avg / positivity` | PASS | Follows from existing thresholds and positive data. |
| `pg_osc_zero` (1039) | `stepP:p5:av-id` | PASS | Actual Fourier zero mode equals actual normalized average. |
| `pg_osc_normalization` (1047) | `stepP:p5:av-dict` | PASS | Correct inverse identities and conformal form identity. |
| `pg_osc_domain` (1053) | `stepP:p5:av-dict` | PASS | Exact scaled half-domain equality in the max norm. |
| `avg` (1062) | `bpP:p5:avg` | PASS | Source contract unchanged; corrected concrete P2 adapter applies. |
| `pgAvg` (1065) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `phi` (1068) | `bpP:p5:phi` | PASS | Source formula/carrier; no changed norm or global instance. |
| `phiDomain` (1071) | `bpP:p5:phi` | PASS | Source formula/carrier; no changed norm or global instance. |
| `phi_chart` (1075) | `bpP:p5:phi-chart` | PASS | Matches source role; no additional defect found. |
| `oscillatorPolarComplex` (1082) | `bpP:p5:kam-hyp / polar bridge` | PASS | Source formula/carrier; no changed norm or global instance. |
| `oscillatorPolarComplex_real` (1087) | `bpP:p5:kam-hyp / polar bridge` | PASS | Matches source role; no additional defect found. |
| `kamH` (1092) | `bpP:p5:kam-hyp` | PASS | Source formula/carrier; no changed norm or global instance. |
| `kamF` (1095) | `bpP:p5:kam-hyp` | PASS | Source formula/carrier; no changed norm or global instance. |
| `kam_hyp` (1101) | `bpP:p5:kam-hyp` | PASS | Matches source role; no additional defect found. |
| `location` (1120) | `bpP:p5:location` | PASS | Matches source role; no additional defect found. |
| `pgKamScale` (1126) | `bpP:p5:kam-hyp / bpP:p3:constants` | PASS | Correct field order; L definitionally initialL. |
| `pg_kam_hyp` (1131) | `bpP:p5:kam-hyp` | PASS | Widths, inverse rows, complex derivative maps match P3. |
| `pg_kam_dictionary` (1134) | `bpP:p5:kam-cond / exact P3 dictionary` | PASS | Same numerical/D0 equalities; Parameters now supplies pgD0. |
| `PGFamily` (1143) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `physicalTorus` (1146) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGFamilySpec` (1150) | `bpP:p5:torus-conv` | PASS | Unchanged faithful type; corrected averaging adapter supplies its input. |
| `torus_conv` (1172) | `bpP:p5:torus-conv` | PASS | Unchanged quantitative joint-family contract and P1 transport. |
| `pgFamily` (1175) | `bpP:p5:torus-conv` | PASS | Choice from output witness, not an added hypothesis. |
| `kset` (1178) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `rawUnion` (1182) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `outputRepresentative` (1186) | `bpP:p5:cell-transfer` | PASS | Source formula/carrier; no changed norm or global instance. |
| `cell_transfer` (1190) | `bpP:p5:cell-transfer` | PASS | Output cell; mixed-lattice counting; whole unions by definition. |
| `kamMeasureConstant` (1197) | `bpP:p3:two-scale-kam / p5:budget` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgMeasureUpper1` (1199) | `bpP:p5:budget#constant` | PASS | F5 resolved: positive-volume denominator and same inverse bounds. |
| `pgMeasureUpper2` (1208) | `bpP:p5:budget#constant` | PASS | F5 resolved: exact slow lattice constant. |
| `pgBudget` (1211) | `bpP:p5:budget` | PASS | F5 resolved: explicit data-only sum; no family dependence. |
| `budget` (1217) | `bpP:p5:budget` | PASS | F5 resolved: bound uses that explicit sum. |
| `pgLoss` (1225) | `bpP:p5:lower` | PASS | Exact printed sum, once its component contracts are repaired. |
| `lower` (1229) | `bpP:p5:lower` | PASS | Matches source role; no additional defect found. |
| `finalRadius` (1234) | `bpP:p5:rstar / final shrink` | PASS | Source formula/carrier; no changed norm or global instance. |
| `strictness` (1237) | `bpP:p5:strictness` | PASS | Whole-torus deletion; added finalRadius is explicit source smallness. |
| `frequency_bounds` (1245) | `bpP:p5:torus-conv / frequencies` | PASS | Matches source role; no additional defect found. |
| `main` (1251) | `bpP:p5:main` | PASS | Exact frozen telescope and conclusion retained. |

| Typed application | Verdict | Reason |
|---|---|---|
| averaged_remainder (S:1058–1060) | PASS | Corrected pg_osc_hyp supplies α; entire instantiated application elaborates. |
| two_scale_kam (S:1139–1140) | PASS | Exact KamHyp and definitionally reflexive initialL argument remain; application elaborates. |

## Remaining note and scoped verdicts

**N3 — Informational: design approval is not proof closure.** All theorem bodies remain sorry. The twelve scoped SOURCE_GAPs and all adapter/analytic proofs remain implementation obligations, exactly as the design states. No additional design correction is requested for this note. Provider sealing, a proof audit and axiom/kernel validation of actual proofs remain separate work.

- **Consumers: PASS** for the audited interfaces and quantified source premises; corrected P2 and unchanged P3/P1 carriers, domains, frequencies and numerical guards match.
- **Frozen objects: PASS.** The actual frozen predicates and Hamiltonian are used; PGData/main remain unchanged. Literal main telescope/conclusion comparison passes with only the declaration name replaced. No parallel solution predicate, boundary identity on arbitrary total source functions, or new frozen premise is introduced.
- **Definitions/structures: PASS.** pgOscAlpha is a scalar formula; its positive-domain use is guarded by admissibility. The moved pgD0 has unchanged meaning. No new structure, global function/matrix instance, unsafe construction or conclusion-shaped input is added.
- **Packages: PASS.** F8's cycle is removed, named wave ordering is consistent, line estimates remain below 1,500, and source/produced-witness/provider boundaries are preserved.

## Independent validation and handoff

1. HEAD/diff: `e1281e008078f0ce080cfd0d4a167f092ad8d01c`; one design-document revision, 66 insertions and 24 deletions. No state-changing git operation.
2. Appendix A/shared signature identity: True. SHA256 `f4c7752bf23b8b149e4e5c0f1fac5288b4c32c10d19c4a17d3afe79af1c13ca2`. Lines 1,286; explicit declarations 202; theorem stubs 69. Added pgOscAlpha; changed pg_osc_hyp; pgD0 moved unchanged; no other declaration delta.
3. Exact frozen telescope/conclusion comparison: True. P4/P5 local/current-inp blueprint identity: True. Current P23 SHA256 `7d7dae4308ea9ec0ca763a2a21ce4b83280bdbb4b91d2c4f5e7567b71085e834`, unchanged from the audited upstream snapshot; both complete fixture theorem types match after whitespace normalization.
4. `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p45 .lake/abi-scratch/P45R3AuditSignatures.lean`: **exit 0**, exactly **69 declaration-uses-sorry warnings**, no errors or other warnings. Submitted signatures run **once**, LEAN_NUM_THREADS=1, nice -n 5, through the required gate. Both actual upstream applications elaborate. Log: `/tmp/p45-r3-audit-signatures.log`.
5. `#print axioms KAM.Planetary.main`: `[propext, sorryAx, Classical.choice, Quot.sound]`. This is the stub's axiom list; no proved-provider receipt is asserted.
6. Independent package check: **36 packages**, **0 named dependency-wave violations**, largest estimate **750 lines**. The modified Parameters/KAMInputs/Family outputs and explicit DAG agree. This static rerun is independent of the designer's static receipt.
7. Mathlib/API regression: no new library declaration or import is introduced by this delta. The unchanged interfaces retain audit 2's successful 22 #check probes, and P2/P3 applications are freshly elaborated in item 4. Those probes were not rerun during this delta; they are earlier independent checks, not new receipts.
8. `PATH=/root/code/KAM-inp-design-p45/.drafts/scratch/gated-bin:$PATH LEAN_NUM_THREADS=1 scripts/lint_sources.sh`: **exit 0**. Exact summaries: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. The ABI subprocess used the existing required-gate wrapper, serially after the signature run. Log: `/tmp/p45-r3-audit-lint.log`. This fresh independent receipt supersedes audit 2's incomplete validation for the current revision; it does not retroactively change that earlier receipt.
9. Final checks: **202/202 declaration rows**, balanced fenced blocks, no trailing whitespace, terminal newline present, `git diff --check` **exit 0**. Git status contains only the two pre-existing untracked audit reports and this new report; no tracked file changed. The manually created scratch signature was deleted. Original shared signatures and both earlier audit report hashes are unchanged. No production Lean module changed; signature elaboration is the targeted Lean check, with no production build target.

Only `docs/tracks/P/design/DESIGN-P45-design-audit-3.md` is the persistent audit edit. Earlier audit reports, original shared signatures, design, blueprints, graph, frozen files, manifest, README and generated root are untouched. Scratch probes are removed after checks. No heartbeat/recursion/synthesis override, clean/update/cache retrieval, production rebuild or concurrent Lean invocation was issued.

**Errata/deviations and uncertainty:** no new suspected defect in a pinned paper. F7/F8 were design transcription/ownership defects and are now repaired. The previously recorded blueprint muStar≤mu0 omission and the positive enclosing Ry enlargement remain explicitly declared. Inherited CP10/CP11 paper allegations were not independently re-adjudicated against pinned PDFs in this delta. Source gaps remain unpaid; this report does not promote them to established results.
