# Lean design: quantitative weak KAM assembly and planar quartic torsion

Design v1, 2026-10-28; branch `inp-design-p11c`. Planning evidence only: no proof, frozen declaration, or root theorem is closed here. Authority: `DESIGN-P11C.md` and `DESIGN-COMMON.md`, including their 2026-10-28 global-review additions. Format model: N `PART145-LEAN-DESIGN.md` and its two audits. Appendix A is the complete standalone signatures file; every theorem body is `sorry`.

## 1. Decisions

1. Two independent branches: `KAM/Planetary/Quantitative/` assembles p11a-5; `KAM/Planetary/PlanarTorsion/` proves p11b. Neither imports the other. Parts 12–13 consume their outputs; no provider belongs to this scope.
2. Keep all numerical constants explicit. `thresholds` is the monotone minorant, never the larger p11a-3 threshold. `QuantitativeData.NumericalValid` is the budget's weaker numerical surface; `.Valid` additionally requires beta ≤ 1 and tau > N−1. The zero perturbation case uses `zero_case`, without the positive-size iteration.
3. The uniform displacement constant is chosen outside all varying K, beta, M, M0, thickness, rho, h and f binders. Its only allowed parameters are `(N,mu,tau,s,C1)`. Diophantine frequencies, torus families, lower Lipschitz bounds and displacement are outputs. `QuantitativeInput` contains precisely the analytic and finite-type input projections, with the **gradient's max-to-max Hessian norm**, not the norm of a bilinear form.
4. Use the existing physical `poincareProd`, `fFix`, `fMov`, frozen `Phase`, `assemble`, `oscillatorAction`, `secularAverage`, `HasSecularBirkhoffForm`, `IsDiophantine` and `hamiltonianVectorField`. Local `p11c_*` names are coordinate/integral adapters and finite explicit formulas; they are not new assumed representations. Bridges to Parts 8–10 must be proved before their consumers dispatch. The three standalone Part-1 definition excerpts retain the exact existing names and bodies; production imports their original owning modules.
5. Close the p11b flow applicability gaps by **new real theorems**, with source premises only: `real_analytic_hamiltonian_local_flow`, `real_lie_taylor`, `full_lift_hamiltonian`. Do not apply `KAM.Canonical.symplectic` or `taylor_lie` without `SmallField`, `gaugeInterior`, holomorphy and trajectory hypotheses. Those complex theorems inform the proof, not an unjustified application.
6. For planar eigenvectors, use the explicit nonzero vector `(-Q12,Q11-sigma1)`, normalize it, and take its positive quarter-turn. Positivity of Q12 proves nonvanishing on the entire axis cone. `global_planar_frame` replaces the unpaid covering-space argument. It gives the same sorted, oriented eigenframe required by the Birkhoff construction; no simply-connectedness premise is necessary for this stronger planar result.
7. `beta_def` uses only the spectral projector and the six quartic coefficients. Its factors are **8 on the diagonal and 4 off diagonal**, with frozen action `(x²+y²)/2`; Omega is **2 sigma**. Asymptotics retain **−117/16**, relative O(alpha²), physical mass factors, homogeneity degree −2, and mass-ratio-only uniform constants.
8. `patch` retains the full Part-10 frequency attachment and Birkhoff conclusion. `torsion_patch_geometry` is a distinct helper and cannot replace that node. Likewise `hasSecularBirkhoffForm_of_sixth_order` is explicitly conditional and cannot replace `birkhoff_form`.

## 2. Carriers and standing structures

| Object | Exact carrier / definition | Meaning |
|---|---|---|
| Real / complex actions | `Fin N → ℝ` / `Fin N → ℂ` | Pi max norm |
| Physical / canonical phase | frozen `Phase d` | positions first, momenta second |
| Full planar phase | `Phase (2+2)` | `(lambda,x;Lambda,y) = assemble Lambda lambda y x` |
| Slow planar phase | `Phase 2` | `(x,y)`, Euclidean length as `p11c_slowLength`, no norm instance |
| Euclidean action lengths | `KAM.Nekhoroshev.euclid` | existing finite-coordinate formula; no new representation |
| Fourier / character modes | `Fin N → ℤ`, planar `Fin 2 → ℤ` | l1 mode norm |
| Quartic coefficients | `QuarticFamily O` | analytic real coefficient functions on O, evaluated over finite exponent vectors of degree exactly 4 |
| KAM data | `QuantitativeData N` | numerical data and K; validity predicates contain no output |
| KAM input | `QuantitativeInput d h f` | A1–A4; pointwise derivative bounds replace suprema equivalently |
| KAM output | `QuantitativeFamily d H cDelta eps` | data-valued result, never a theorem input in place of weak KAM |
| Budget rates | `BudgetRates`, `RateBounds` | eight independent nonnegative rates; exact B=2H+aC |
| Physical data | `PlanarData`, `.Valid` | G,m0,m1,m2 positive, kappa=G*m0 |
| Normalization output | `PlanarBirkhoffResult` | existential F, chi, T and domain; exact physical composition, frozen averaged expansion |
| Same-patch output | `PlanarFrequencyPatch` | compact positive-volume action patch, analytic R-nondegenerate combined frequency, uniform NR4, finite type |

No global instances are introduced on functions or matrices. Matrix regularity is entrywise. Total functions are only claimed analytic on the displayed open domains; integral identities carry integrability through the physical domain. The standalone signature's finite-set sums are executable mathematical definitions, not assumed CAS certificates.

## 3. Reuse and upstream interface (to reconcile)

`U` means an upstream declaration has not yet been delivered in this checkout. These are **requested shapes**, not invented full upstream statements. Do not dispatch a dependent package until names, carriers and hypotheses are reconciled with that writer's signatures. All unqualified P names below mean `KAM.Planetary`; delivered N/K names keep their namespaces.

| ID | Upstream graph nodes / exact names | Supply / consume |
|---|---|---|
| U1 | Part 1 `IsChart`, `IsLatticeTorus`, `unitCube`; `torus_union_lower`, `torus_union_measurableSet_of_injOn`, `torus_union_saturation`, `torus_orbit` | Exact `PPart1Signatures.lean` definitions/types. Supply compact good set, primary lattice, both Lipschitz inequalities, smooth Hamiltonian; consume Borel cell image, measure bounds, saturation, explicit global solutions and local uniqueness. Evaluation here is `(theta,b)`, whereas `torus_union` orders `(b,theta)`; compose the product swap isometry explicitly. |
| U2 | `KAM.Kepler.keplerLong`, `keplerPhi_keplerLong`, `analyticOnNhd_keplerLong`; `poincare`, `poincareV`, `poincareProd`, `poincareProd_symplectic`, `analyticOnNhd_fFix_poincareProd`, `analyticOnNhd_fMov_poincareProd` | Existing `KAM/Kepler/Equation.lean`, `Planetary/Poincare/Chart.lean`, `Product.lean`, exact delivered Kepler signature names. The unit-axis orbital formula is identified by `orbit_poincare_bridge`; never replace the chart by a formal orbit assumption. |
| U3 | `KAM.ODE.gen_local`, `gen_maximal`, `gen_continuation_compact`, `gen_uniqueness`, `IsSolutionIn` | Existing real ODE types. Supply analytic polynomial field, locally uniform derivative bounds, confining compact ball, maximal solution. Consume existence/continuation/uniqueness. Continuation cannot itself create the initial solution. |
| U4 | `KAM.Canonical.flow_b`, `flow_e`, `flow_symplFormC`, `symplectic`, `lie_derivative`, `taylor_lie` | Existing complex types inspected; direct use requires their actual `SmallField`/gauge hypotheses. New real bridge modules reproduce the variational/integral argument with real analytic hypotheses. No field-bound or complexification premise is added to p11b. |
| U5 | `KAM.uniform_limits`, `KAM.holomorphic_analytic_real`, `KAM.Weighted.holomorphic_parametric_integral`, `KAM.Weighted.uniform_limit_holomorphic` | RealFlow.Analytic supplies local complex extensions, compact common parameter domains, uniform Picard bounds and derivative convergence. Consume holomorphic parameter integrals, holomorphic limits and real analytic restriction. `uniform_limits` alone does not create derivative convergence; prove it by local Cauchy estimates first. |
| U11a1 | `index_def`, `diophantine_measure`, `power_law`, `gamma_inverse` (U) | Same scalar `(c·omega)^rho`, diagonal Euclidean derivative norm, top operator norm, max diameter and l1 Fourier divisors. Supply A2/A3, use 2 gamma for `zero_case`. Consume loss ≤ epsLoss and inverse-gamma exponent `(mu+1)/rho`. `QuantitativeInput` is the local source projection; bridge it to the upstream index predicate once, with no changed norm. |
| U11a2 | `fourier_cutoff` (U) | cN exactly `2*(1+1/pi)*(3*N/(e*pi))^(N-1)`. The numerical copy here belongs to the threshold adapter; identify it with the upstream definition. |
| U11a3 | `sel_data`, `schedule_consts`, `schedule`, `smooth_cutoff`, `adm_params`, `adm_budget`, `adm_budget_beta`, `parameter_selection` (U) | Supply numerical data and A1–A4, strictly positive eps branch, gamma chosen from data. Consume the iteration and compact H-infinity, data-only thresholds, cutoff constants. `p11c_oldThreshold` and mollifier constants are literal numerical projections to identify with upstream, not a second iteration. `ab_gamma`, `ab_T0`, `ab_t0`, `ab_lam`, `abb_spec` are proof fragments of `adm_budget`/`adm_budget_beta`, not extra assumptions. |
| U11a4 | `situation`, `free_radius`, `limit_torus`, `displacement`, `evaluation_bilipschitz`, `displacement_power`; `sec_limit_data` (U) | Supply eps>0 ≤ old threshold, schedule, selected set. Consume primary analytic embedded Lagrangian tori on common strips, HasDerivAt, both Lipschitz inequalities, action margin, Borel measure bounds and uniform displacement. The small initial action radius is chosen internally; never an input to `weak_kam_quantitative`. |
| U8a | `laplace_def`, `laplace`, `perturbation_analytic`, `e_diff`, `e_taylor` (U) | Supply positive axes, noncollision compact torus, local analytic domain. Identify `p11c_laplace` with normalized Part-8 integral; consume coefficient series, differentiated averages, uniform analytic Taylor remainders. Radian mean is `(2*pi)^(-2)` with frozen `secularAverage`; no factor of two change. |
| U8b | `coeffs`, `quadratic_form`, `quartic`, `evenness`, `symmetries`, `same_jets`, `identification`, `conv_data` (U) | Identify Q with the actual second homogeneous physical jet (`quadratic_physical_bridge`), and c with the actual fourth jet (`quartic_explicit`). Identify actions with the existing axis/action dictionary. Moving/fixed secular difference is exactly `sum m_i^4*kappa²/Lambda_i²/(2*m0)`. Supply the physical definitions; consume even jets, analytic remainder and independence of coupling. `qf_diag`/`qf_pair` are proof fragments, not new interfaces. |
| U9 | `n2`, `local_analytic`, `diagonalize`, `lift`, `good`, `good_set`, `e_id` (U) | Supply actual Q with positive off-diagonal entry and simple sorted spectrum. Identify `p11c_Q`, `p11c_sigma`, projector and inverse rotation lift with upstream spectral objects; prove equalities, never assume them. `p11c_phi4` is the finite-mode product adapter; prove its nonzero locus equals upstream Phi4's locus. Consume NR4 and diagonalization. The global frame replaces the angle-lifting proof fragment. |
| U10 | `good_point`, `generic`, `interface` (U) | Supply nonzero analytic torsion determinant and finite-mode product on connected axis cone. Consume analytic zero-set nullity and the **same** patch with Part-10 frequency data, including positive-volume action image and finite type of `(nu,2sigma)`. `PlanarFrequencyPatch` is this part's required output projection; it does not invent the upstream theorem. |
| MK | `Matrix.det_fin_two`, `AnalyticOnNhd`, `iteratedFDeriv`, `MvPolynomial.eval`, `MvPolynomial.totalDegree`, `intervalIntegral.integral_deriv_eq_sub`, `HasFDerivAt.comp_hasDerivAt`, `IsCompact.exists_isMinOn` | Mathlib search performed locally. Algebra uses finite polynomial identities; analysis uses exact derivatives/integrals. The multivariable analytic zero-set measure theorem was not found under a ready-made Mathlib name; U9/U10 must supply that proof, not just the identity theorem's empty-interior consequence. |

## 4. Complete scoped node table

The graph is absent from this design worktree, so the read-only integration graph `/root/code/KAM-inp/docs/graph/P/DEPGRAPH.md` is the scope authority, SHA-256 `14e720a80bc40bfec284dd0acbb83f93ac5bd9b3750f21a34bd592af852e9f64`. It contains **83** nodes with statement sources in the two assigned files. No graph edits are made. Table locators retain their labels and line ranges. `a5` abbreviates `blueprint-P/parts/p11a5-quantitative-theorem.tex`; `b` abbreviates `blueprint-P/parts/p11b-planar-torsion.tex`.

Proof-step rows name a local proof fragment in the listed theorem/package, not a new theorem with its conclusion as a hypothesis. Their exact obligations remain the labelled source step and graph contract. Data rows name concrete definitions; external computation rows name method rather than a new assumption. Inputs use the reuse table above and the graph's direct dependencies.

| Graph node | Lean declaration / local proof fragment | Package | Statement locator | Proof locator |
|---|---|---|---|---|
| `bpP:p11a:thresholds` | `thresholds; QuantitativeData.gamma; numerical definitions` | Q1 | `a5#bpP:p11a:thresholds@L23-L33` | `-` |
| `bpP:p11a:budget` | `budget; qb_comp; qb_mono; qb_poly; qb_beta` | Q2–Q4 | `a5#bpP:p11a:budget@L37-L46` | `a5#bpP:p11a:budget@L47-L55` |
| `stepP:p11a:qb-comp` | `qb_comp/qb_mono/qb_poly/qb_beta — local qb-comp` | Q2–Q4 | `a5#stepP:p11a:qb-comp@L48-L48` | `a5#stepP:p11a:qb-comp@L48-L48` |
| `stepP:p11a:qb-mono` | `qb_comp/qb_mono/qb_poly/qb_beta — local qb-mono` | Q2–Q4 | `a5#stepP:p11a:qb-mono@L50-L50` | `a5#stepP:p11a:qb-mono@L50-L50` |
| `stepP:p11a:qb-poly` | `qb_comp/qb_mono/qb_poly/qb_beta — local qb-poly` | Q2–Q4 | `a5#stepP:p11a:qb-poly@L52-L52` | `a5#stepP:p11a:qb-poly@L52-L52` |
| `stepP:p11a:qb-beta` | `qb_comp/qb_mono/qb_poly/qb_beta — local qb-beta` | Q2–Q4 | `a5#stepP:p11a:qb-beta@L54-L54` | `a5#stepP:p11a:qb-beta@L54-L54` |
| `bpP:p11a:zero-case` | `zero_case; p11c_zeroGood` | Q5 | `a5#bpP:p11a:zero-case@L61-L63` | `a5#bpP:p11a:zero-case@L64-L68` |
| `stepP:p11a:zc-set` | `zero_case — local zc-set` | Q5 | `a5#stepP:p11a:zc-set@L65-L65` | `a5#stepP:p11a:zc-set@L65-L65` |
| `stepP:p11a:zc-tori` | `zero_case — local zc-tori` | Q5 | `a5#stepP:p11a:zc-tori@L67-L67` | `a5#stepP:p11a:zc-tori@L67-L67` |
| `bpP:p11a:weak-kam-quantitative` | `weak_kam_quantitative; QuantitativeFamily; budget; displacement_power_flat` | Q6 | `a5#bpP:p11a:weak-kam-quantitative@L72-L91` | `a5#bpP:p11a:weak-kam-quantitative@L92-L110` |
| `stepP:p11a:qt-order` | `weak_kam_quantitative / budget / displacement_power_flat — local qt-order` | Q6 | `a5#stepP:p11a:qt-order@L93-L93` | `a5#stepP:p11a:qt-order@L93-L93` |
| `stepP:p11a:qt-reduce` | `weak_kam_quantitative / budget / displacement_power_flat — local qt-reduce` | Q6 | `a5#stepP:p11a:qt-reduce@L95-L95` | `a5#stepP:p11a:qt-reduce@L95-L95` |
| `stepP:p11a:qt-zero` | `weak_kam_quantitative / budget / displacement_power_flat — local qt-zero` | Q6 | `a5#stepP:p11a:qt-zero@L97-L97` | `a5#stepP:p11a:qt-zero@L97-L97` |
| `stepP:p11a:qt-iter` | `weak_kam_quantitative / budget / displacement_power_flat — local qt-iter` | Q6 | `a5#stepP:p11a:qt-iter@L99-L99` | `a5#stepP:p11a:qt-iter@L99-L99` |
| `stepP:p11a:qt-k2` | `weak_kam_quantitative / budget / displacement_power_flat — local qt-k2` | Q6 | `a5#stepP:p11a:qt-k2@L101-L101` | `a5#stepP:p11a:qt-k2@L101-L101` |
| `stepP:p11a:qt-k3` | `weak_kam_quantitative / budget / displacement_power_flat — local qt-k3` | Q6 | `a5#stepP:p11a:qt-k3@L103-L103` | `a5#stepP:p11a:qt-k3@L103-L103` |
| `stepP:p11a:qt-k4` | `weak_kam_quantitative / budget / displacement_power_flat — local qt-k4` | Q6 | `a5#stepP:p11a:qt-k4@L105-L105` | `a5#stepP:p11a:qt-k4@L105-L105` |
| `stepP:p11a:qt-k5` | `weak_kam_quantitative / budget / displacement_power_flat — local qt-k5` | Q6 | `a5#stepP:p11a:qt-k5@L107-L107` | `a5#stepP:p11a:qt-k5@L107-L107` |
| `stepP:p11a:qt-k6` | `weak_kam_quantitative / budget / displacement_power_flat — local qt-k6` | Q6 | `a5#stepP:p11a:qt-k6@L109-L109` | `a5#stepP:p11a:qt-k6@L109-L109` |
| `bpP:p11a:sec-q-thm#data` | `QuantitativeData; QuantitativeInput; NumericalValid; Valid` | Q1/Q5 | `a5#bpP:p11a:sec-q-thm#data@L73-L80` | `-` |
| `bpP:p11b:e-ode` | `real_analytic_hamiltonian_local_flow (new real bridge)` | R1–R3 | `b#bpP:p11b:e-ode@L20-L20` | `-` |
| `bpP:p11b:e-ca` | `finite exact polynomial identities; no assumed certificate` | T2/T4/T7 | `b#bpP:p11b:e-ca@L23-L23` | `-` |
| `bpP:p11b:sec-set#data` | `PlanarData; p11c_hatFix; p11c_hatMov; p11c_secular; frozen coordinates` | T1 | `b#bpP:p11b:sec-set#data@L14-L16` | `-` |
| `bpP:p11b:orbit` | `orbit; orbit_analytic; orbit_poincare_bridge; p11c_orbitJet` | T2 | `b#bpP:p11b:orbit@L28-L36` | `b#bpP:p11b:orbit@L37-L41` |
| `stepP:p11b:or-kep` | `orbit; orbit_analytic — local or-kep` | T2 | `b#stepP:p11b:or-kep@L38-L38` | `b#stepP:p11b:or-kep@L38-L38` |
| `stepP:p11b:or-pos` | `orbit; orbit_analytic — local or-pos` | T2 | `b#stepP:p11b:or-pos@L39-L39` | `b#stepP:p11b:or-pos@L39-L39` |
| `stepP:p11b:or-an` | `orbit; orbit_analytic — local or-an` | T2 | `b#stepP:p11b:or-an@L40-L40` | `b#stepP:p11b:or-an@L40-L40` |
| `bpP:p11b:laplace-red` | `laplace_red; laplace_up; laplace_rational_reduction; laplace_reduction_denominator` | T3 | `b#bpP:p11b:laplace-red@L43-L56` | `b#bpP:p11b:laplace-red@L57-L62` |
| `stepP:p11b:lr-1` | `laplace_red; laplace_up; laplace_rational_reduction; laplace_reduction_denominator — local lr-1` | T3 | `b#stepP:p11b:lr-1@L58-L58` | `b#stepP:p11b:lr-1@L58-L58` |
| `stepP:p11b:lr-2` | `laplace_red; laplace_up; laplace_rational_reduction; laplace_reduction_denominator — local lr-2` | T3 | `b#stepP:p11b:lr-2@L59-L59` | `b#stepP:p11b:lr-2@L59-L59` |
| `stepP:p11b:lr-3` | `laplace_red; laplace_up; laplace_rational_reduction; laplace_reduction_denominator — local lr-3` | T3 | `b#stepP:p11b:lr-3@L60-L60` | `b#stepP:p11b:lr-3@L60-L60` |
| `stepP:p11b:lr-red` | `laplace_red; laplace_up; laplace_rational_reduction; laplace_reduction_denominator — local lr-red` | T3 | `b#stepP:p11b:lr-red@L61-L61` | `b#stepP:p11b:lr-red@L61-L61` |
| `bpP:p11b:pair-jet` | `pair_jet; pair_series; pair_quadratic_consistency; p11c_pairCoeffs` | T4/T5 | `b#bpP:p11b:pair-jet@L64-L91` | `b#bpP:p11b:pair-jet@L92-L98` |
| `stepP:p11b:pj-formal` | `pair_jet; pair_series; pair_quadratic_consistency — local pj-formal` | T4/T5 | `b#stepP:p11b:pj-formal@L93-L93` | `b#stepP:p11b:pj-formal@L93-L93` |
| `stepP:p11b:pj-bin` | `pair_jet; pair_series; pair_quadratic_consistency — local pj-bin` | T4/T5 | `b#stepP:p11b:pj-bin@L94-L94` | `b#stepP:p11b:pj-bin@L94-L94` |
| `stepP:p11b:pj-avg` | `pair_jet; pair_series; pair_quadratic_consistency — local pj-avg` | T4/T5 | `b#stepP:p11b:pj-avg@L95-L95` | `b#stepP:p11b:pj-avg@L95-L95` |
| `stepP:p11b:pj-red` | `pair_jet; pair_series; pair_quadratic_consistency — local pj-red` | T4/T5 | `b#stepP:p11b:pj-red@L96-L96` | `b#stepP:p11b:pj-red@L96-L96` |
| `stepP:p11b:pj-cons` | `pair_jet; pair_series; pair_quadratic_consistency — local pj-cons` | T4/T5 | `b#stepP:p11b:pj-cons@L97-L97` | `b#stepP:p11b:pj-cons@L97-L97` |
| `bpP:p11b:quartic-explicit` | `quartic_explicit; p11c_coeffs; p11c_homogeneousPart` | T6 | `b#bpP:p11b:quartic-explicit@L100-L109` | `b#bpP:p11b:quartic-explicit@L110-L116` |
| `stepP:p11b:qe-conv` | `quartic_explicit — local qe-conv` | T6 | `b#stepP:p11b:qe-conv@L111-L113` | `b#stepP:p11b:qe-conv@L111-L113` |
| `stepP:p11b:qe-an` | `quartic_explicit — local qe-an` | T6 | `b#stepP:p11b:qe-an@L114-L114` | `b#stepP:p11b:qe-an@L114-L114` |
| `stepP:p11b:qe-c12` | `quartic_explicit — local qe-c12` | T6 | `b#stepP:p11b:qe-c12@L115-L115` | `b#stepP:p11b:qe-c12@L115-L115` |
| `bpP:p11b:sec-bnf#data` | `QuarticFamily; p11c_NR4; p11c_n0; p11c_rotation; p11c_bracket` | T1/T7 | `b#bpP:p11b:sec-bnf#data@L120-L124` | `-` |
| `bpP:p11b:char` | `char; character_bracket; character_polynomial; average_action_polynomial` | T7 | `b#bpP:p11b:char@L126-L128` | `b#bpP:p11b:char@L129-L132` |
| `stepP:p11b:ch-mon` | `char; character_bracket; character_polynomial; average_action_polynomial — local ch-mon` | T7 | `b#stepP:p11b:ch-mon@L130-L130` | `b#stepP:p11b:ch-mon@L130-L130` |
| `stepP:p11b:ch-bra` | `char; character_bracket; character_polynomial; average_action_polynomial — local ch-bra` | T7 | `b#stepP:p11b:ch-bra@L131-L131` | `b#stepP:p11b:ch-bra@L131-L131` |
| `bpP:p11b:homological` | `homological; p11c_chi` | T8 | `b#bpP:p11b:homological@L134-L138` | `b#bpP:p11b:homological@L139-L142` |
| `stepP:p11b:ho-def` | `homological — local ho-def` | T8 | `b#stepP:p11b:ho-def@L140-L140` | `b#stepP:p11b:ho-def@L140-L140` |
| `stepP:p11b:ho-eq` | `homological — local ho-eq` | T8 | `b#stepP:p11b:ho-eq@L141-L141` | `b#stepP:p11b:ho-eq@L141-L141` |
| `bpP:p11b:flow` | `flow; p11c_flow; real_analytic_hamiltonian_local_flow` | T9 | `b#bpP:p11b:flow@L144-L146` | `b#bpP:p11b:flow@L147-L150` |
| `stepP:p11b:fl-bd` | `flow; real_analytic_hamiltonian_local_flow — local fl-bd` | T9 | `b#stepP:p11b:fl-bd@L148-L148` | `b#stepP:p11b:fl-bd@L148-L148` |
| `stepP:p11b:fl-an` | `flow; real_analytic_hamiltonian_local_flow — local fl-an` | T9 | `b#stepP:p11b:fl-an@L149-L149` | `b#stepP:p11b:fl-an@L149-L149` |
| `bpP:p11b:lie` | `lie; real_lie_taylor` | T10 | `b#bpP:p11b:lie@L152-L159` | `b#bpP:p11b:lie@L160-L164` |
| `stepP:p11b:li-tay` | `real_lie_taylor; lie — local li-tay` | T10 | `b#stepP:p11b:li-tay@L161-L161` | `b#stepP:p11b:li-tay@L161-L161` |
| `stepP:p11b:li-ord` | `real_lie_taylor; lie — local li-ord` | T10 | `b#stepP:p11b:li-ord@L162-L162` | `b#stepP:p11b:li-ord@L162-L162` |
| `stepP:p11b:li-sum` | `real_lie_taylor; lie — local li-sum` | T10 | `b#stepP:p11b:li-sum@L163-L163` | `b#stepP:p11b:li-sum@L163-L163` |
| `bpP:p11b:lift-map` | `lift_map; full_lift_hamiltonian; p11c_liftFlow; p11c_rotationLift` | T11 | `b#bpP:p11b:lift-map@L166-L172` | `b#bpP:p11b:lift-map@L173-L176` |
| `stepP:p11b:lm-ham` | `full_lift_hamiltonian; lift_map — local lm-ham` | T11 | `b#stepP:p11b:lm-ham@L174-L174` | `b#stepP:p11b:lm-ham@L174-L174` |
| `stepP:p11b:lm-prop` | `full_lift_hamiltonian; lift_map — local lm-prop` | T11 | `b#stepP:p11b:lm-prop@L175-L175` | `b#stepP:p11b:lm-prop@L175-L175` |
| `bpP:p11b:sec-beta#data` | `p11c_Q; p11c_sigma; p11c_projector; quadratic_physical_bridge` | T12 | `b#bpP:p11b:sec-beta#data@L180-L182` | `-` |
| `bpP:p11b:beta-def` | `beta_def; p11c_beta; beta_properties` | T13 | `b#bpP:p11b:beta-def@L184-L192` | `-` |
| `bpP:p11b:beta-formula` | `beta_formula` | T13 | `b#bpP:p11b:beta-formula@L194-L197` | `b#bpP:p11b:beta-formula@L198-L203` |
| `stepP:p11b:bf-gram` | `beta_formula — local bf-gram` | T13 | `b#stepP:p11b:bf-gram@L199-L201` | `b#stepP:p11b:bf-gram@L199-L201` |
| `stepP:p11b:bf-avg` | `beta_formula — local bf-avg` | T13 | `b#stepP:p11b:bf-avg@L202-L202` | `b#stepP:p11b:bf-avg@L202-L202` |
| `bpP:p11b:birkhoff-form` | `birkhoff_form; PlanarBirkhoffResult; hasSecularBirkhoffForm_of_sixth_order` | T15/T16 | `b#bpP:p11b:birkhoff-form@L205-L215` | `b#bpP:p11b:birkhoff-form@L216-L222` |
| `stepP:p11b:bt-rot` | `global_planar_frame; birkhoff_form — local bt-rot` | T14–T16 | `b#stepP:p11b:bt-rot@L217-L217` | `b#stepP:p11b:bt-rot@L217-L217` |
| `stepP:p11b:bt-rot#lift` | `global_planar_frame; birkhoff_form — local bt-rot#lift` | T14–T16 | `b#stepP:p11b:bt-rot#lift@L217-L217` | `b#stepP:p11b:bt-rot#lift@L217-L217` |
| `stepP:p11b:bt-K` | `global_planar_frame; birkhoff_form — local bt-K` | T14–T16 | `b#stepP:p11b:bt-K@L218-L218` | `b#stepP:p11b:bt-K@L218-L218` |
| `stepP:p11b:bt-nf` | `global_planar_frame; birkhoff_form — local bt-nf` | T14–T16 | `b#stepP:p11b:bt-nf@L219-L219` | `b#stepP:p11b:bt-nf@L219-L219` |
| `stepP:p11b:bt-avg` | `global_planar_frame; birkhoff_form — local bt-avg` | T14–T16 | `b#stepP:p11b:bt-avg@L220-L220` | `b#stepP:p11b:bt-avg@L220-L220` |
| `stepP:p11b:bt-frozen` | `global_planar_frame; birkhoff_form — local bt-frozen` | T14–T16 | `b#stepP:p11b:bt-frozen@L221-L221` | `b#stepP:p11b:bt-frozen@L221-L221` |
| `bpP:p11b:remain` | `remain; actual moving/fixed physical averages` | T17 | `b#bpP:p11b:remain@L224-L226` | `b#bpP:p11b:remain@L224-L226` |
| `bpP:p11b:asymptotics` | `asymptotics; asymptotics_uniform_ratio; asymptotics_general_axes` | T18/T19 | `b#bpP:p11b:asymptotics@L230-L238` | `b#bpP:p11b:asymptotics@L239-L248` |
| `stepP:p11b:as-in` | `asymptotics; asymptotics_uniform_ratio; asymptotics_general_axes — local as-in` | T18/T19 | `b#stepP:p11b:as-in@L240-L242` | `b#stepP:p11b:as-in@L240-L242` |
| `stepP:p11b:as-pi` | `asymptotics; asymptotics_uniform_ratio; asymptotics_general_axes — local as-pi` | T18/T19 | `b#stepP:p11b:as-pi@L243-L243` | `b#stepP:p11b:as-pi@L243-L243` |
| `stepP:p11b:as-c` | `asymptotics; asymptotics_uniform_ratio; asymptotics_general_axes — local as-c` | T18/T19 | `b#stepP:p11b:as-c@L244-L245` | `b#stepP:p11b:as-c@L244-L245` |
| `stepP:p11b:as-ent` | `asymptotics; asymptotics_uniform_ratio; asymptotics_general_axes — local as-ent` | T18/T19 | `b#stepP:p11b:as-ent@L246-L246` | `b#stepP:p11b:as-ent@L246-L246` |
| `stepP:p11b:as-det` | `asymptotics; asymptotics_uniform_ratio; asymptotics_general_axes — local as-det` | T18/T19 | `b#stepP:p11b:as-det@L247-L247` | `b#stepP:p11b:as-det@L247-L247` |
| `bpP:p11b:torsion` | `torsion; beta_properties` | T20 | `b#bpP:p11b:torsion@L250-L253` | `b#bpP:p11b:torsion@L254-L258` |
| `stepP:p11b:to-an` | `torsion — local to-an` | T20 | `b#stepP:p11b:to-an@L255-L255` | `b#stepP:p11b:to-an@L255-L255` |
| `stepP:p11b:to-pt` | `torsion — local to-pt` | T20 | `b#stepP:p11b:to-pt@L256-L256` | `b#stepP:p11b:to-pt@L256-L256` |
| `stepP:p11b:to-id` | `torsion — local to-id` | T20 | `b#stepP:p11b:to-id@L257-L257` | `b#stepP:p11b:to-id@L257-L257` |
| `bpP:p11b:patch` | `patch; PlanarFrequencyPatch; PlanarBirkhoffResult; torsion_patch_geometry` | T21 | `b#bpP:p11b:patch@L260-L262` | `b#bpP:p11b:patch@L263-L265` |

`bpP:p11a:physical-interface` is present in a5 L115–133 but absent from the supplied 83-node graph slice. It is still designed: `physical_interface` (Q7), statement `a5#bpP:p11a:physical-interface@L115-L123`, proof `a5#bpP:p11a:physical-interface@L124-L133`; its `pi-zero`, `pi-a`, `pi-b`, `pi-c`, `pi-d` are local fragments. Report the coverage discrepancy to the graph owner; do not create graph nodes here.

## 5. Conventions, departures and statement preservation

- KAM angles and Diophantine divisors are period one; all planar secular/oscillator angles are radians. The finite character action is `exp(-i theta)`; its **character covariance** is `exp(+i k·phi)`, hence `{F_k,N0}=i(k·Omega)F_k` and `{N0,chi}=−(F−average F)`. The full flow uses the frozen sign convention with q=x and p=y.
- No `sSup` of an unbounded family is used in a theorem without its validity conditions. The only scalar suprema in numerical definitions are finite derivative-index maxima or compactly controlled sets. The cutoff uses the source's normalized polynomial bump, including `0^0=1`.
- The finite-type input uses an attained diagonal direction on a Euclidean unit sphere: equivalent to beta ≤ the maximum on that sphere, because N≥1, compactness and continuity hold. At order zero the derivative is independent of the direction. The top M bound quantifies **independent** unit directions; M0 quantifies the diagonal norm. These cannot be interchanged.
- Source real sup bounds are written pointwise; real measure subtractions are written `volume K ≤ volume H + ofReal epsLoss` (compact sets have finite measure). Bounds on images use ENNReal throughout; no `toReal` of infinite volume occurs.
- K1–K4 are bundled as an output structure. K5 is `budget` together with `qb_poly`, K6 is `displacement_power_flat`; these data-only results precede the assembly. They are not hypotheses of the KAM theorem. Borel cell image, compact closed-cell representatives, equivariance and injectivity give the source compact quotient and disjoint embedded torus statements without building a second torus predicate or an explicit quotient manifold.
- The generic real-flow bridges strengthen the usable infrastructure, without changing any p11b premise. The source's simply-connected O_a is dropped only after proving the explicit **global** eigenframe on A2. `birkhoff_form` accepts any given good open axis neighbourhood Oa of the cube and produces O' with compact closure inside its action image. The slow radius and remainder constant are chosen before Oa, so they depend only on the physical data and the compact cube. Only simply-connectedness is dropped: the explicit global frame makes the stronger statement true. Its concrete quartic F, chi and T are still exhibited.
- `PlanarBirkhoffResult` exhibits **the same T** for both actual perturbations, with `T = rotationLift ∘ liftFlow chi`, action preservation, angle translation covariance, injectivity, symplecticity and image in the actual analytic physical domain. Total physical formulas supply a legitimate extension outside the tube. No conclusion about global analyticity outside that tube is claimed. Source radii rhoK,r1,r2 are proof-local choices; take their positive minimum and shrink as specified below.
- In `lie`, the slow-independent C is arbitrary rather than assumed analytic. It cancels from the displayed estimate and its slow Poisson bracket is zero; this strictly stronger helper statement is true without that unused regularity premise. The Hamiltonian's slow-dependent terms retain the exact analytic and jet hypotheses.
- The full `patch` conclusion includes `PlanarFrequencyPatch`, not only a nonzero determinant. Its index is positive, its amount is independent of coupling, and all mu≥mu0 are covered. R-nondegeneracy of the separate frequency blocks follows by padding a nonzero coefficient vector with zeros in the combined-frequency clause. The source's stability invocation consumes the already delivered U10 stability theorem with this positive amount; it is not assumed as a new property of the physical system.
- The statement `hasSecularBirkhoffForm_of_sixth_order` is deliberately conditional and separately named. Its hypotheses are proved within `birkhoff_form` from actual transformed averages. For p_j²+q_j²<r0², `|z|₂²<2r0²≤r*²`. Choose delta≤r0 and delta²≤eps/(64C); `|z|₂≤2‖(p,q)‖∞` gives `C|z|₂⁶≤64C‖(p,q)‖∞⁶≤eps‖(p,q)‖∞⁴`. Symmetry is a separate output for P-G, never a clause silently inserted into the frozen predicate.

## 6. Source gaps, blueprint issues and errata

All four SOURCE_GAP-bearing scoped records remain explicit proof obligations. The global review (section “Suspected blueprint defects and source limitations”, L252–264) additionally highlights the two complex-flow applicability problems. This design neither edits nor claims to repair the source graph.

| Gap / exact source text | Why the cited result does not apply | Concrete design response |
|---|---|---|
| `fl-bd`, b L148: “the solution cannot blow up (`gen-continuation`)” | Continuation needs an existing maximal solution and uniform local data; the displayed scalar inequality creates neither. | R1 local existence + `KAM.ODE.gen_maximal`; T9 derives coefficient bounds on a compact parameter neighbourhood, then bounds `(delta,M,L)` on the confining ball and applies `gen_continuation_compact`. Include the zero initial slow variable separately. |
| `li-tay`, b L161: “Part N, lie-derivative, taylor” | Those exact N declarations require a small holomorphic field and gauge-interior domain. Source K and coefficients are real analytic; those complex inputs are absent. | `real_lie_taylor` proves the real chain-rule and order-two integral Taylor formula on a supplied actual solution. T10 constructs that solution by `flow`; no complex smallness premise is added. |
| `lm-prop`, b L175: “Hamiltonian flows are symplectic” citing N symplectic/canonical | Again no complex domain/small-field hypothesis; the full field also has partial_Lambda chi in the angle block. | R2–R3 prove analytic dependence and real variational symplecticity. `full_lift_hamiltonian` verifies all full Hamilton equations, including the angle integral; T11 applies real form invariance to the assembled coordinates. |
| `bt-rot#lift`, b L217: “lifts analytically to the angle psi ... (covering S1→S1)” | A local eigenline choice has not yet supplied a global vector or analytic angle; the graph records this as an unproved step. | T14 `global_planar_frame`: Q12>0 makes the explicit eigenvector nonzero globally. The angle itself is bypassed; the matrix, orientation and ordered diagonalization used by every consumer are proved. Keep the source's gap record unchanged; any later BYPASSED graph status needs its own review. |

Other reported issues/departures:

- a5 L150–154 records a stale Part-11 citation: the threshold used is the **minorant**, whose beta-power bound is `bpP:p11a:budget` (d), not merely `adm-budget-beta` for the larger threshold. No inference transfers a lower bound from a larger number to a smaller one.
- a5 L96 uses an actual M0 that may vanish. Use the fixed positive upper bound M0 directly, or a positive number ≤M0 bounding the actual value; retain the monotonicity bridge. Never call a theorem requiring M0>0 with actual value zero.
- The pointwise bound `Delta≤2^-18` is **not** a domain margin relative to vartheta. `QuantitativeFamily.lattice` carries the actual domain; U11a4 supplies the sharper action bound through the internally chosen s0≤vartheta. Q7 uses that domain, not a comparison between 2^-18 and vartheta.
- b L212 allows r0=r*/sqrt2 for the frozen open discs. For Part 12's **closed** cylinder choose r0=r*/2; equality at the larger endpoint would lose a closure margin. Preserve both statements separately.
- `p11c_phi4` is an adapter for the **nonzero locus** of the Part-9 product, not an assertion that two possibly differently normalized polynomials are definitionally equal. Prove the locus bridge and keep the invariant beta independent of frame sign.
- No new pinned-source erratum is asserted. The inherited candidate E-P-CP11-2 concerns CP11 (B.6), term `37 alpha^4 beta_4^(9)` versus `alpha^3`. It is already recorded; this design derives the coefficients from Kepler averaging and does not use that printed formula. CP11 (8.2)–(8.4) are provenance cross-checks, not replacement proofs. No pinned PDF was independently re-audited in this design task.

## 7. Modules, import DAG and packages

Every row is one prover package and one exact `.lean` module under the indicated directory; estimates are 150–800 lines. Split again before reaching 1500. Include the hard rules below in every issued Lean brief. All modules have copyright, `module`, public interface imports, module documentation and an exposed public section for unfolding definitions. No production file is created by this design.

| Package | Exact path under `KAM/Planetary/` | Contents / named inputs | Lines | Wave |
|---|---|---|---:|---:|
| Q1 | `Quantitative/Thresholds.lean` | Data, validity, explicit constants and thresholds; U11a2/3 numerical adapters | 500 | 1 |
| Q2 | `Quantitative/BudgetCompare.lean` | qb_comp, qb_mono; Q1, adm_params numerical equality | 500 | 2 |
| Q3 | `Quantitative/BudgetPower.lean` | qb_poly and the exact rates/exponent; Q1, U11a3 adm_budget proof fragments | 650 | 2 |
| Q4 | `Quantitative/Budget.lean` | qb_beta, budget, displacement_power_flat; Q2/Q3, U11a1 gamma_inverse | 300 | 3 |
| Q5 | `Quantitative/Zero.lean` | QuantitativeInput and Family in preceding interface module (Q0 below), zero_case; Q1/Q0, U11a1 power_law, U1 | 450 | 3 |
| Q0 | `Quantitative/Interface.lean` | A1–A4 projections, family output; Q1, exact U1 definitions | 300 | 2 |
| Q6 | `Quantitative/Assembly.lean` | weak_kam_quantitative; Q4/Q5, U11a3 parameter_selection, U11a4 free_radius/limit/displacement/evaluation | 400 | 4 |
| Q7 | `Quantitative/Physical.lean` | physical_interface; Q6, U1 measure/saturation/orbit, ODE uniqueness | 450 | 5 |
| T1 | `PlanarTorsion/Setting.lean` | physical adapters, PlanarData, slow lengths/actions; U2/frozen defs | 250 | 1 |
| T2 | `PlanarTorsion/OrbitJet.lean` | orbit, orbit_analytic, orbit_poincare_bridge; T1, regular Kepler exact equation | 650 | 2 |
| T3 | `PlanarTorsion/LaplaceReduction.lean` | laplace_red/up/rational_reduction; U8a laplace_def, integration by parts | 650 | 1 |
| T4 | `PlanarTorsion/PairCoefficients.lean` | explicit A,B,p1..6; pair_series, consistency; T3, U8a Laplace series | 550 | 2 |
| T5 | `PlanarTorsion/PairJet.lean` | actual averaged interaction pair_jet; T2/T4, U8a differentiation, U8b symmetries | 750 | 3 |
| T6 | `PlanarTorsion/Quartic.lean` | c1..6 and quartic_explicit; T5, U8b exact eccentric conversion, evenness/same_jets | 650 | 4 |
| T7 | `PlanarTorsion/Characters.lean` | QuarticFamily, characters, polynomial/covariance/bracket clauses; T1, exact finite monomial algebra | 650 | 2 |
| T8 | `PlanarTorsion/Homological.lean` | finite chi, reality, homological equation; T7, NR4 source premises | 350 | 3 |
| R1 | `PlanarTorsion/RealFlow/Local.lean` | existing real local/maximal ODE and compact-neighbourhood bounds; U3 | 450 | 1 |
| R2 | `PlanarTorsion/RealFlow/Analytic.lean` | real analytic parametric Picard convergence on common neighbourhoods; R1, U5 exact analytic-limit/parametric-integral declarations | 750 | 2 |
| R3 | `PlanarTorsion/RealFlow/Variational.lean` | variational equation, Hessian symmetry, frozen form conservation, real_analytic_hamiltonian_local_flow; R2, U4 argument | 650 | 3 |
| T9 | `PlanarTorsion/QuarticFlow.lean` | flow and compact-uniform cubic displacement/inverse; T7, R3, gen_continuation_compact | 650 | 4 |
| T10 | `PlanarTorsion/NormalForm.lean` | real_lie_taylor, lie, sixth-order remainder; T8/T9, U8a Taylor | 650 | 5 |
| T11 | `PlanarTorsion/Lift.lean` | full_lift_hamiltonian, lift_map; T9/R3, U9 inverse rotation lift adapter; no complex SmallField shortcut | 650 | 5 |
| T12 | `PlanarTorsion/SpectralAdapter.lean` | actual quadratic_physical_bridge, Q/sigma/projector; T4/T1, U8b/U9 | 350 | 3 |
| T13 | `PlanarTorsion/Beta.lean` | beta_def/formula/properties, Gram averages g,g²; T6/T7/T12 | 650 | 5 |
| T14 | `PlanarTorsion/Frame.lean` | global_planar_frame and concrete rotationLift; T12, positive Q12/U9 | 450 | 4 |
| T15 | `PlanarTorsion/FrozenBridge.lean` | hasSecularBirkhoffForm_of_sixth_order, elementary disc conversion; frozen definitions only | 250 | 1 |
| T16 | `PlanarTorsion/Birkhoff.lean` | PlanarBirkhoffResult, birkhoff_form; T10/T11/T13/T14/T15, U8b physical domain/average | 700 | 6 |
| T17 | `PlanarTorsion/TorsionBound.lean` | remain via compact positivity; T13, Mathlib compact minimum | 150 | 6 |
| T18 | `PlanarTorsion/AsymptoticEntries.lean` | as_in/as_pi/as_c/as_ent; T4/T6/T12/T13 | 700 | 6 |
| T19 | `PlanarTorsion/Asymptotics.lean` | asymptotics, mass-ratio uniformity, homogeneity; T18 | 500 | 7 |
| T20 | `PlanarTorsion/Generic.lean` | torsion; T19, U9 analytic null set, U10 good_point/generic | 350 | 8 |
| T21 | `PlanarTorsion/Patch.lean` | geometry helper and full patch; T20/T16/T17, U10 interface | 450 | 9 |

These are **local waves**, conditional on the named external interfaces. Q5 follows Q0 (wave 2); no file is imported before its package completes. There are 32 packages, about 16,400 estimated lines, each file ≤750 in this plan. Wave counts are scheduling estimates, not proof receipts.

Import DAG (`A → B` means B imports A):

```text
Thresholds → {Interface,BudgetCompare,BudgetPower}
{BudgetCompare,BudgetPower} → Budget
Interface → Zero; {Budget,Zero,upstream iteration+limit} → Assembly → Physical
Setting → {OrbitJet,Characters,SpectralAdapter}; LaplaceReduction → PairCoefficients
{OrbitJet,PairCoefficients} → PairJet → Quartic
Characters → Homological; RealFlow.Local → Analytic → Variational
{Characters,Variational} → QuarticFlow
{Homological,QuarticFlow} → NormalForm; {QuarticFlow,Variational} → Lift
{PairCoefficients,upstream quadratic/spectrum} → SpectralAdapter → Frame
{Quartic,Characters,SpectralAdapter} → Beta
{NormalForm,Lift,Beta,Frame,FrozenBridge} → Birkhoff
Beta → TorsionBound; {PairCoefficients,Quartic,SpectralAdapter,Beta} → AsymptoticEntries
AsymptoticEntries → Asymptotics → Generic
{Generic,Birkhoff,TorsionBound,upstream interface} → Patch
```

The split between `Lift` and `Frame` is important: `Lift` proves the chi-flow lift and takes the already existing Part-9 inverse-rotation lift only for composition; this part's explicit `p11c_rotationLift` is owned by `Frame`. The standalone signatures place formulas in dependency order; implementation ownership stays as in this table. No file imports any provider or DRAFT_SORRY anchor. All frozen imports are definitions.

### Proof instructions that determine package feasibility

Q2: name Tbar,tflat,Xibar separately and prove the three branch comparisons independently; use the derivative sign of `s*Tbar` on (0,1]. Q3: preserve the two cases a_s=0 and a_s>0, constants before the family, and the exact maxima D,G,L,J,X,H. Q6: choose cDelta from U11a4 before the remaining data, split eps=0 first, then use the internally chosen free radius on the positive branch. Q7: use `IsSolutionIn` and connected J containing zero, rather than an undefined flow object.

T2/T5: prove analytic jet identification before running finite algebra. A CAS output or numerical quadrature is not a theorem. Expand Kepler through degree four, binomial inverse-radius through degree four, then use exact Fourier averaging and T3 recurrence to reduce every coefficient. Keep the nonzero denominator guards 0<alpha<1 and half-integer s explicit. The alpha-series receipt uses actual Taylor coefficients, not the ellipses of a printed expansion as assumptions.

R2 is substantial new analysis: extend each real analytic coefficient locally to a complex neighbourhood, use compactness to obtain a common neighbourhood, and prove analytic Picard convergence there. This is a **proof of the real bridge**, not an added complex hypothesis on any source theorem. For joint time analyticity, complex time Picard on a small disc is required; real-time smooth dependence alone is insufficient. R3 proves the real variational equation by differentiating the integral equation, then `d/dt Omega(Yu,Yv)=0` with symmetric Hessian. Patch local maps by uniqueness. Default-heartbeat failure means split the package by estimate, never change an option.

T9: take coefficient bounds on a compact neighbourhood of K, not merely at K if analytic dependence on I is needed. Prove cubic field bound, obtain a maximal solution first, use `u'=2 z·X<=2C u²` (zero case separately), then continuation on a compact confining ball. The inverse time-one map must be defined on the image, using the backwards trajectory; do not demand that image lie in the original small ball.

T10: retain vanishing 5-jet and degree 4+4−2=6; analytic remainders yield uniform sixth-order bounds on compact parameter neighbourhoods. T11: verify the full field including angle shift `integral partial_I chi`, and use the assembled `(phi,q;I,p)` order. T16: shrink to an O' with compact closure inside the good action set, bound the physical analytic neighbourhood by rhoK, and take r*≤min(rhoK/sqrt2,r1,r2). Translation invariance of the radian torus average identifies the average of the **actual** `fhat ∘ T`. Apply T15 only afterwards.

T18/T19: small-alpha negative Delta_Q permits the projector bounds. Do not replace its O(alpha^1/2) relative error by O(alpha²). The final relative errors improve only after combining the c and projector orders. Normalize the physical scales before choosing the O constants, so the uniform statement really depends on m1/m2 alone. T20: empty interior is insufficient for the full-measure clause; it needs the multivariable analytic null-set proof. T21 invokes the extra-condition form of U10 interface, and extracts a strictly positive minimum on the compact inner cube.

## 8. Provider assembly and consumers

No frozen theorem is closed here, so **no provider file is proposed**. In particular this document must not be counted as P-G, P-PLANAR or P-FIXED proof closure.

Part 12 takes `patch`, then `birkhoff_form` on its chosen cube; specializes `r0=r*/2`, uses `HasSecularBirkhoffForm` verbatim for the actual pullback perturbation, `beta_properties` for symmetry and `remain` for a positive uniform determinant lower bound. Its own remaining tasks are joint holomorphic extension near the closed cylinder, hperiod, fast diffeomorphism, boundary collar and exact P-G provider assembly. Part 13 takes `weak_kam_quantitative`, `budget`, `displacement_power_flat`, `physical_interface` and its own physical chart transport. No Part-13 Hamiltonian hypothesis is replaced by the KAM output.

## 9. Risks and validation

The major risk is new real analytic parametric flow infrastructure (R2/R3), followed by exact quartic jet extraction (T5), analytic zero-set nullity (U9/U10), and matching the simultaneously designed U11a1–4 interfaces. All are named unpaid proof obligations. The gate checks **types only**; every result still uses `sorryAx`. This design does not claim source-completeness of the old direct Rus01/Rus05 specialization route: the current blueprint uses the new explicit cutoff/iteration route.

Validation receipts and the final signature hash are recorded below after the final gated elaboration. Only this design document is committed; signatures, check logs and handoff remain untracked/ignored.

## 10. Hard rules for every Lean brief (verbatim)

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
   proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
3. **Every `.lean` file is a Lean module**: copyright comment, `module`, imports (`public import` for the
   interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold.
4. **No `axiom`, `admit`, `unsafe`, `opaque`; `sorry` only** as the manifest-bound body of a frozen statement in
   `KAM/Frozen/`. No recursion-depth or synthesis-heartbeat overrides either.
5. **Frozen files are read-only.** Never edit anything under `KAM/Frozen/` or `manifest/`. If a frozen
   declaration looks wrong, stop and report; never add a premise or substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing
   data and explicit owner rulings. Conditional helpers get distinct names and never stand in for a source result.
7. **Ambient types:** `Fin n → ℝ`, `Fin n → ℂ`, Fourier indices `Fin n → ℤ`. Never `EuclideanSpace`.
8. **Builds:** one targeted `nice -n 5 lake build <Module>` at a time; never `lake clean`; never rebuild the
   library from scratch in a worktree (worktrees use a copy-on-write overlay on `main`'s build snapshot). A wait
   on the compile gate is expected, not a hang.
9. **Providers are quarantined.** `KAM/Provider/<Name>.lean` proves its frozen theorem as `KAM.Provider.<name>`;
   no module except the frozen anchor may import a provider or a `DRAFT_SORRY` anchor (the root file skips them).
10. **Never edit `README.md`** (generated) or `KAM.lean` (generated by `scripts/gen_root_imports.py`).
11. **Errata:** report every suspected defect in a pinned source (location, quoted text, why it is wrong) in your
    handoff; the orchestrator records it in `docs/errata/ledger.json`. Deviations you introduce are reported too.


The signature-only draft exception is explicitly authorized by DESIGN-COMMON.md; every proof body here is `sorry`, outside production sources. Elaboration in this task is exclusively through `inp_sig_check.sh`, superseding ordinary build commands for this design task.

## 11. Validation receipts

- Scoped graph inventory: **83/83**, no duplicate node rows; physical-interface source-only addition recorded separately.
- Both assigned blueprint files are byte-identical between the design and integration worktrees (SHA-256 a5 `f4ea938ec9baf0a280fded708fc7b2bbac4584a6347ad9d49da1291c73ad9b1d`, b `f8ce70a3460c855e1e04ea1a8d39c7a32a550f38b8097ca993a6a17efe012bf1`).
- Final signature command: `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p11c .drafts/scratch/P11CReceipt.lean`: **exit 0**, exactly **44** declaration-uses-sorry warnings, no errors and no other warnings. Receipt `.drafts/scratch/P11C-receipt.log`; source prefix byte-identical to Appendix A, with only three appended axiom queries.
- `#print axioms` for `weak_kam_quantitative`, `birkhoff_form`, `patch`: each reports `[propext, sorryAx, Classical.choice, Quot.sound]`. These are draft signature receipts, not proved results.
- `scripts/lint_sources.sh`: **exit 0**. Output: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. Its ABI subprocess was routed through a task-local `lake` shim to the required `inp_sig_check.sh` gate; no direct Lean/build invocation was used.
- Targeted check is signature elaboration, as explicitly required by the brief; no production module build or library rebuild is appropriate to this Markdown-only change.
- `git -C /root/code/KAM-inp-design-p11c diff --check`: exit 0. Appendix A extraction equals both untracked signature copies byte for byte. Every theorem body is `sorry`; no proof/heartbeat override/global instance was introduced.
- No proof closure is asserted. All 44 theorem bodies are `sorry`; no production Lean file was edited.

## Appendix A. Complete signatures

Standalone deliverable: `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` (untracked). 815 lines; SHA-256 `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079`. The scratch validation copy has the same source prefix and appends three `#print axioms` queries; those queries are not part of this deliverable.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module
public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.RealHamiltonian
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.ODE.Basic
public import KAM.Strip.RealRestriction
/-!
# P11C signatures: quantitative assembly and planar quartic torsion
Design evidence only. All theorem bodies are sorry. Upstream excerpts are identified below;
no upstream theorem statement is fabricated. The new real-flow bridges are local proof obligations.
-/
@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary
open KAM KAM.Kepler KAM.ODE

/- Exact definition excerpts from PPart1Signatures, until Hamiltonian/Chart and Transport land.
These are NOT new production owners. -/
def IsChart {d : ℕ} (c : ℝ) (Ψ : Phase d → Phase d) (O : Set (Phase d)) : Prop :=
  AnalyticOnNhd ℝ Ψ O ∧ IsSymplecticOn c Ψ O

def IsLatticeTorus {d : ℕ} (L : (Fin d → ℤ) → Phase d) (G : Phase d → ℝ)
    (O : Set (Phase d)) (w : Fin d → ℝ) (K : (Fin d → ℝ) → Phase d) : Prop :=
  (AnalyticOnNhd ℝ K univ ∧ ∀ θ, K θ ∈ O ∧ DifferentiableAt ℝ G (K θ)) ∧
  (∀ θ (k : Fin d → ℤ), K (θ + fun i => (k i : ℝ)) = K θ + L k) ∧
  (∀ θ θ', K θ = K θ' → ∃ k : Fin d → ℤ, θ' = θ + fun i => (k i : ℝ)) ∧
  (∀ θ, Injective (fderiv ℝ K θ)) ∧
  (∀ θ u v, symplecticForm (fderiv ℝ K θ u) (fderiv ℝ K θ v) = 0) ∧
  (∀ θ t, HasDerivAt (fun s : ℝ => K (θ + s • w))
    (hamiltonianVectorField G (K (θ + t • w))) t)

def unitCube (d : ℕ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Ico (0 : ℝ) 1

/- Quantitative/Thresholds: local numerical projection of sec-q-thm#data.
The cutoff constant below is its explicit source formula, not an arbitrary positive input. -/
structure QuantitativeData (N : ℕ) where
  mu : ℕ
  rho : ℕ
  tau : ℝ
  vartheta : ℝ
  s : ℝ
  beta : ℝ
  M : ℝ
  M0 : ℝ
  C1 : ℝ
  epsLoss : ℝ
  K : Set (Fin N → ℝ)

def QuantitativeData.NumericalValid {N : ℕ} (d : QuantitativeData N) : Prop :=
  1 ≤ N ∧ 1 ≤ d.mu ∧ (d.rho = 1 ∨ d.rho = 2) ∧
  (N : ℝ) * d.mu / d.rho - 1 < d.tau ∧ 0 ≤ d.tau ∧
  0 < d.vartheta ∧ d.vartheta ≤ 1 ∧ 0 < d.s ∧ d.s ≤ 1 ∧
  1 ≤ d.C1 ∧ 0 < d.M0 ∧ 0 < d.beta ∧ d.beta ≤ d.M ∧
  IsCompact d.K ∧ 0 < d.epsLoss ∧ ENNReal.ofReal d.epsLoss < volume d.K

def QuantitativeData.Valid {N : ℕ} (d : QuantitativeData N) : Prop :=
  d.NumericalValid ∧ (N : ℝ) - 1 < d.tau ∧ d.beta ≤ 1

def p11c_bump (mu : ℕ) (x : ℝ) : ℝ := (max 0 (1 - x ^ 2)) ^ (mu + 1)
def p11c_mollifier (mu : ℕ) (x : ℝ) : ℝ :=
  p11c_bump mu x / ∫ y : ℝ, p11c_bump mu y

def p11c_mollifierMass (mu j : ℕ) : ℝ := ∫ x : ℝ, |iteratedDeriv j (p11c_mollifier mu) x|
def p11c_cutoffDerivative (N mu k : ℕ) : ℝ :=
  (N : ℝ) ^ k * sSup {v : ℝ | ∃ a : Fin N → ℕ,
    (∑ i, a i) = k ∧ v = ∏ i, p11c_mollifierMass mu (a i)}
def p11c_cutoffConstant (N mu : ℕ) : ℝ :=
  sqrt N * sSup {v : ℝ | ∃ k ≤ mu, v = (4 : ℝ) ^ k *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * p11c_cutoffDerivative N mu j *
      ((k - j : ℕ) : ℝ) ^ (k - j)}

def QuantitativeData.diameter {N : ℕ} (d : QuantitativeData N) : ℝ := Metric.diam d.K
def QuantitativeData.varpi {N : ℕ} (d : QuantitativeData N) : ℝ :=
  (2 : ℝ) ^ (-(2 * (2 * (d.tau + 1) * (d.mu + 1) + N + 4)))
def QuantitativeData.cN (N : ℕ) : ℝ :=
  2 * (1 + 1 / π) * (3 * N / (exp 1 * π)) ^ (N - 1)
def QuantitativeData.A0 {N : ℕ} (d : QuantitativeData N) : ℝ := log (16 * cN N / d.varpi)
def QuantitativeData.cDio {N : ℕ} (d : QuantitativeData N) : ℝ :=
  2 ^ (N + 2) * d.mu * (sqrt N * d.diameter) ^ (N - 1) * (d.M / d.beta) *
    (1 + (4 + 1 / d.vartheta) * sqrt N * d.diameter) * d.beta ^ (-(1 / (d.mu : ℝ))) *
    (N : ℝ) ^ ((d.rho : ℝ) / (2 * d.mu)) * 2 * 3 ^ (N - 1) *
      (1 + 1 / ((d.rho : ℝ) * (d.tau + 1) / d.mu - N))
def QuantitativeData.gamma {N : ℕ} (d : QuantitativeData N) : ℝ :=
  min ((1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (d.beta / 4) ^ (1 / (d.rho : ℝ)))
    ((d.epsLoss / d.cDio) ^ ((d.mu : ℝ) / d.rho)) / 2

def QuantitativeData.tbar {N : ℕ} (d : QuantitativeData N) : ℝ :=
  1 + 16 / (π * d.s) * (|d.A0| + N * log (32 * N / d.s))
def QuantitativeData.tflat {N : ℕ} (d : QuantitativeData N) : ℝ :=
  min (d.vartheta / sqrt N) (d.gamma * d.tbar ^ (-d.tau - 1) / (4 * d.C1))
def QuantitativeData.xibar {N : ℕ} (d : QuantitativeData N) : ℝ :=
  (2 : ℝ) ^ (d.tau + 1) * (1 + 1 / (d.s / 24) + 1 / d.tflat + d.tbar * (d.s / 24))
def QuantitativeData.thetaMax {N : ℕ} (d : QuantitativeData N) : ℝ :=
  if d.rho = 1 then d.beta / 2 else min d.beta (d.beta / (2 ^ (d.mu + 1) * (2 * d.M0 + d.beta)))
def QuantitativeData.lambdaFlat {N : ℕ} (d : QuantitativeData N) : ℝ :=
  min (min (d.tflat / 8)
    (min (d.varpi / 2) ((2 : ℝ) ^ (-10 : ℤ) / d.xibar) *
      (π * d.gamma * (d.s / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * d.tbar ^ d.tau))))
    (d.thetaMax * d.tflat ^ d.mu / (4 * p11c_cutoffConstant N d.mu))
def thresholds {N : ℕ} (d : QuantitativeData N) : ℝ := d.lambdaFlat ^ 2 / (2 * N * d.C1)

/-- Old threshold's numerical projection, for comparison only (adm_params reconciliation). -/
def p11c_oldThreshold {N : ℕ} (d : QuantitativeData N) : ℝ :=
  let T := max 1 (16 / (π * d.s) * (d.A0 + N * log (32 * N / d.s)))
  let t := min (d.vartheta / sqrt N) (d.gamma * T ^ (-d.tau - 1) / (4 * d.C1))
  let X := (2 : ℝ) ^ (d.tau + 1) * (1 + t / (d.s / 24) + (d.s / 24) / t + T * (d.s / 24))
  let l := min (min (d.C1 * t / 8) (min (d.varpi / 2) ((2 : ℝ) ^ (-10 : ℤ) / X) *
    (π * d.gamma * (d.s / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * T ^ d.tau))))
    (d.thetaMax * t ^ d.mu / (4 * p11c_cutoffConstant N d.mu))
  l ^ 2 / (2 * N * d.C1)

/-- Product order on the numerical entries: d' has no worse data. K is compared by diameter. -/
def BudgetOrder {N : ℕ} (d d' : QuantitativeData N) : Prop :=
  d.mu = d'.mu ∧ d.rho = d'.rho ∧ d.tau = d'.tau ∧
  d.beta ≤ d'.beta ∧ d.vartheta ≤ d'.vartheta ∧ d.s ≤ d'.s ∧ d.epsLoss ≤ d'.epsLoss ∧
  d'.M ≤ d.M ∧ d'.diameter ≤ d.diameter ∧ d'.M0 ≤ d.M0 ∧ d'.C1 ≤ d.C1

theorem qb_comp {N : ℕ} (d : QuantitativeData N) (hd : d.NumericalValid) (M0' : ℝ)
    (h0 : 0 < M0') (hM : M0' ≤ d.M0) :
    0 < thresholds d ∧ thresholds d ≤ p11c_oldThreshold { d with M0 := M0' } := sorry

theorem qb_mono {N : ℕ} (d d' : QuantitativeData N) (hd : d.NumericalValid) (hd' : d'.NumericalValid)
    (h : BudgetOrder d d') : d.gamma ≤ d'.gamma ∧ thresholds d ≤ thresholds d' := sorry

structure BudgetRates where
  vartheta : ℝ
  s : ℝ
  beta : ℝ
  loss : ℝ
  M : ℝ
  M0 : ℝ
  C1 : ℝ
  diam : ℝ

def BudgetRates.Valid (a : BudgetRates) : Prop :=
  0 ≤ a.vartheta ∧ 0 ≤ a.s ∧ 0 ≤ a.beta ∧ 0 ≤ a.loss ∧ 0 ≤ a.M ∧ 0 ≤ a.M0 ∧ 0 ≤ a.C1 ∧ 0 ≤ a.diam

def BudgetRates.exponent (N mu rho : ℕ) (tau : ℝ) (a : BudgetRates) : ℝ :=
  let D := N * a.diam + a.M + a.vartheta + (1 + 1 / (mu : ℝ)) * a.beta
  let G := max (a.beta / rho) ((mu : ℝ) / rho * (a.loss + D))
  let L := if 0 < a.s then a.s + 1 else 0
  let J := max a.vartheta (G + (tau + 1) * L + a.C1)
  let X := max J L
  let H := max (max J (G + (N + 1) * a.s + tau * L + X)) (a.beta + a.M0 + mu * J)
  2 * H + a.C1

def RateBounds {N : ℕ} (a : BudgetRates) (c u : ℝ) (d : QuantitativeData N) : Prop :=
  c * u ^ a.vartheta ≤ d.vartheta ∧ c * u ^ a.s ≤ d.s ∧ c * u ^ a.beta ≤ d.beta ∧
  c * u ^ a.loss ≤ d.epsLoss ∧ d.M ≤ c⁻¹ * u ^ (-a.M) ∧ d.M0 ≤ c⁻¹ * u ^ (-a.M0) ∧
  d.C1 ≤ c⁻¹ * u ^ (-a.C1) ∧ d.diameter ≤ c⁻¹ * u ^ (-a.diam)

/-- c' chosen before all other rates and before the family, with only a_s fixed. -/
theorem qb_poly (N mu rho : ℕ) (tau c asRate : ℝ) (hN : 1 ≤ N) (hmu : 1 ≤ mu)
    (hrho : rho = 1 ∨ rho = 2) (htau : (N : ℝ) * mu / rho - 1 < tau) (htau0 : 0 ≤ tau)
    (hc : 0 < c) (hc1 : c ≤ 1) (has : 0 ≤ asRate) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ a : BudgetRates, a.Valid → a.s = asRate →
      ∀ d : QuantitativeData N, d.NumericalValid → d.mu = mu → d.rho = rho → d.tau = tau →
        ∀ u ∈ Ioc (0 : ℝ) 1, RateBounds a c u d →
          c' * u ^ a.exponent N mu rho tau ≤ thresholds d := sorry

def p11c_G0 {N : ℕ} (d : QuantitativeData N) : ℝ := (d.mu + 1 : ℝ) / d.rho
def p11c_B0 {N : ℕ} (d : QuantitativeData N) : ℝ :=
  2 * max (2 * p11c_G0 d) (1 + d.mu * p11c_G0 d)

theorem qb_beta {N : ℕ} (d : QuantitativeData N) (hd : d.NumericalValid) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ Ioc (0 : ℝ) (min 1 d.M),
      c * b ^ p11c_B0 d ≤ thresholds { d with beta := b } := sorry

theorem budget {N : ℕ} (d : QuantitativeData N) (hd : d.NumericalValid) :
    (∀ M0' : ℝ, 0 < M0' → M0' ≤ d.M0 →
      0 < thresholds d ∧ thresholds d ≤ p11c_oldThreshold { d with M0 := M0' }) ∧
    (∀ d' : QuantitativeData N, d'.NumericalValid → BudgetOrder d d' →
      d.gamma ≤ d'.gamma ∧ thresholds d ≤ thresholds d') ∧
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ Ioc (0 : ℝ) (min 1 d.M),
      c * b ^ p11c_B0 d ≤ thresholds { d with beta := b } := sorry

/- Quantitative/Input and Family. The bound predicates are local input projections of A1--A4;
finite-type upstream names are only referenced in the design reconciliation table. -/
def p11c_scalar {N : ℕ} (rho : ℕ) (w : (Fin N → ℝ) → Fin N → ℝ)
    (c y : Fin N → ℝ) : ℝ := (∑ i, c i * w y i) ^ rho

def p11c_realDomain {N : ℕ} (d : QuantitativeData N) : Set (Phase N) :=
  {z | realInclusion N z.2 ∈ actionNbhd d.K (2 * d.vartheta)}

def QuantitativeInput {N : ℕ} (d : QuantitativeData N) (h : (Fin N → ℂ) → ℂ)
    (f : (Fin N → ℂ) × (Fin N → ℂ) → ℂ) : Prop :=
  let U := actionNbhd d.K (2 * d.vartheta)
  let V := {y : Fin N → ℝ | ∃ x ∈ d.K, KAM.Nekhoroshev.euclid (y - x) ≤ d.vartheta}
  DifferentiableOn ℂ h U ∧ DifferentiableOn ℂ f (complexStrip N d.s ×ˢ U) ∧
  (∀ z ∈ complexStrip N d.s ×ˢ U, ∀ k : Fin N → ℤ,
    f (z.1 + fun i => (k i : ℂ), z.2) = f z) ∧
  (∀ y : Fin N → ℝ, realInclusion N y ∈ U → (h (realInclusion N y)).im = 0) ∧
  (∀ z : Phase N, realInclusion₂ N z ∈ complexStrip N d.s ×ˢ U → (f (realInclusion₂ N z)).im = 0) ∧
  (∀ c : Fin N → ℝ, KAM.Nekhoroshev.euclid c = 1 → ∀ y ∈ d.K,
    ∃ j ≤ d.mu, ∃ v : Fin N → ℝ, KAM.Nekhoroshev.euclid v = 1 ∧
      d.beta ≤ |iteratedFDeriv ℝ j (p11c_scalar d.rho (frequencyMap h) c) y (fun _ => v)|) ∧
  (∀ c : Fin N → ℝ, KAM.Nekhoroshev.euclid c = 1 → ∀ j : ℕ, 1 ≤ j → j ≤ d.mu + 1 →
    ∀ y ∈ V, ∀ v : Fin j → (Fin N → ℝ), (∀ i, KAM.Nekhoroshev.euclid (v i) ≤ 1) →
      |iteratedFDeriv ℝ j (p11c_scalar d.rho (frequencyMap h) c) y v| ≤ d.M) ∧
  (∀ y ∈ U, ‖fderiv ℂ (fun x i => fderiv ℂ h x (Pi.single i 1)) y‖ ≤ d.C1) ∧
  (∀ j ≤ d.mu, ∀ y ∈ V, ∀ v : Fin N → ℝ, KAM.Nekhoroshev.euclid v = 1 →
    KAM.Nekhoroshev.euclid (iteratedFDeriv ℝ j (frequencyMap h) y (fun _ => v)) ≤ d.M0)

/-- Hessian is the max-to-max derivative of the complex gradient, as in A4. -/
def p11c_displacement {N : ℕ} (d : QuantitativeData N) (cDelta eps : ℝ) : ℝ :=
  min ((2 : ℝ) ^ (-18 : ℤ)) (cDelta * Real.sqrt eps / d.gamma)

structure QuantitativeFamily {N : ℕ} (d : QuantitativeData N) (H : Phase N → ℝ)
    (cDelta eps : ℝ) where
  good : Set (Fin N → ℝ)
  torus : (Fin N → ℝ) → (Fin N → ℝ) → Phase N
  freq : (Fin N → ℝ) → Fin N → ℝ
  compact : IsCompact good
  subset : good ⊆ d.K
  measure : volume d.K ≤ volume good + ENNReal.ofReal d.epsLoss
  lattice : ∀ b ∈ good, IsLatticeTorus angleShift H (p11c_realDomain d) (freq b) (torus b)
  dio : ∀ b ∈ good, IsDiophantine d.gamma d.tau (freq b)
  displacement : ∀ b ∈ good, ∀ θ, ‖torus b θ - (θ, b)‖ ≤ p11c_displacement d cDelta eps
  lower : ∀ b ∈ good, ∀ b' ∈ good, ∀ θ θ',
    (1 - (2 : ℝ) ^ (-10 : ℤ)) * ‖(θ, b) - (θ', b')‖ ≤ ‖torus b θ - torus b' θ'‖
  upper : ∀ b ∈ good, ∀ b' ∈ good, ∀ θ θ',
    ‖torus b θ - torus b' θ'‖ ≤ (1 + (2 : ℝ) ^ (-10 : ℤ)) * ‖(θ, b) - (θ', b')‖
  borel : MeasurableSet ((fun z : Phase N => torus z.2 z.1) '' (unitCube N ×ˢ good))
  cell_lower : ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) * volume good ≤
    volume ((fun z : Phase N => torus z.2 z.1) '' (unitCube N ×ˢ good))
  compact_closed : IsCompact ((fun z : Phase N => torus z.2 z.1) ''
    ((Set.pi univ fun _ => Icc (0 : ℝ) 1) ×ˢ good))

def p11c_zeroGood {N : ℕ} (d : QuantitativeData N) (h : (Fin N → ℂ) → ℂ) : Set (Fin N → ℝ) :=
  {b ∈ d.K | IsDiophantine (2 * d.gamma) d.tau (frequencyMap h b)}

theorem zero_case {N : ℕ} (d : QuantitativeData N) (hd : d.Valid)
    (h : (Fin N → ℂ) → ℂ) (hh : QuantitativeInput d h 0) (cDelta : ℝ) :
    ∃ Q : QuantitativeFamily d (realHamiltonian h 0) cDelta 0,
      Q.good = p11c_zeroGood d h ∧ Q.torus = (fun b θ => (θ, b)) ∧ Q.freq = frequencyMap h := sorry

/-- Uniform cDelta depends on precisely N,mu,tau,s,C1, before K,beta,M,M0,h,f. -/
theorem weak_kam_quantitative (N mu : ℕ) (tau s C1 : ℝ) :
    ∃ cDelta : ℝ, 0 < cDelta ∧ ∀ d : QuantitativeData N,
      d.Valid → d.mu = mu → d.tau = tau → d.s = s → d.C1 = C1 →
      ∀ h f, QuantitativeInput d h f → ∀ eps : ℝ, 0 ≤ eps → eps ≤ thresholds d →
      (∀ z ∈ complexStrip N d.s ×ˢ actionNbhd d.K (2 * d.vartheta), ‖f z‖ ≤ eps) →
      Nonempty (QuantitativeFamily d (realHamiltonian h f) cDelta eps) := sorry

/-- K6, with every datum except beta fixed; cDelta is the uniform output of the preceding theorem. -/
theorem displacement_power_flat {N : ℕ} (d : QuantitativeData N) (hd : d.Valid)
    (cDelta : ℝ) (hc : 0 < cDelta) :
    ∃ cD : ℝ, 0 < cD ∧ ∀ b ∈ Ioc (0 : ℝ) (min 1 d.M), ∀ eps : ℝ, 0 ≤ eps →
      p11c_displacement { d with beta := b } cDelta eps ≤
        cD * eps ^ (1 / 2 : ℝ) * b ^ (-p11c_G0 d) := sorry

/-- Explicit solutions and agreement on any connected local time interval; no pre-defined flow. -/
theorem physical_interface {N : ℕ} (d : QuantitativeData N) (hd : d.Valid)
    (H : Phase N → ℝ) (hH : ContDiffOn ℝ 2 H (p11c_realDomain d))
    (cDelta eps : ℝ) (Q : QuantitativeFamily d H cDelta eps) :
    let S := (fun z : Phase N => Q.torus z.2 z.1) '' (unitCube N ×ˢ Q.good)
    let St := ⋃ b ∈ Q.good, range (Q.torus b)
    MeasurableSet S ∧ 0 < volume S ∧ volume S < ⊤ ∧
    0 < ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) * (volume d.K - ENNReal.ofReal d.epsLoss) ∧
    ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) * (volume d.K - ENNReal.ofReal d.epsLoss) ≤ volume S ∧
    volume S ≤ ENNReal.ofReal ((1 + (2 : ℝ) ^ (-10 : ℤ)) ^ (2 * N)) * volume Q.good ∧
    (∀ z ∈ S, ∃ b ∈ Q.good, ∃ θ ∈ unitCube N,
      z = Q.torus b θ ∧ ‖z - (θ, b)‖ ≤ p11c_displacement d cDelta eps) ∧
    (∀ b ∈ Q.good, ∀ θ, ∀ t : ℝ, Q.torus b (θ + t • Q.freq b) ∈ St) ∧
    (∀ b ∈ Q.good, ∀ θ, IsSolutionIn (hamiltonianVectorField H) (p11c_realDomain d) univ
      (fun t : ℝ => Q.torus b (θ + t • Q.freq b))) ∧
    (∀ b ∈ Q.good, ∀ θ, ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J →
      ∀ y : ℝ → Phase N, IsSolutionIn (hamiltonianVectorField H) (p11c_realDomain d) J y →
      y 0 = Q.torus b θ → ∀ t ∈ J, y t = Q.torus b (θ + t • Q.freq b)) ∧
    (∀ b ∈ Q.good, ∀ b' ∈ Q.good, ∀ θ θ', ∀ k : Fin N → ℤ,
      Q.torus b θ = Q.torus b' θ' + angleShift k → b = b') ∧
    (∃ R : Set (Phase N), IsCompact R ∧ R ⊆ St ∧
      ∀ z ∈ St, ∃ y ∈ R, ∃ k : Fin N → ℤ, z = y + angleShift k) ∧
    St = ⋃ k : Fin N → ℤ, (fun z => z + angleShift k) '' S := sorry

/- Planar quartic: use physical functions and frozen coordinates directly. -/
structure PlanarData where
  G : ℝ
  m0 : ℝ
  m : Fin 2 → ℝ

def PlanarData.Valid (p : PlanarData) : Prop := 0 < p.G ∧ 0 < p.m0 ∧ ∀ i, 0 < p.m i
def PlanarData.kappa (p : PlanarData) : ℝ := p.G * p.m0
def p11c_axes : Set (Fin 2 → ℝ) := {a | 0 < a 0 ∧ a 0 < a 1}
def PlanarData.actions (p : PlanarData) (a : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => p.m i * sqrt (p.kappa * a i)
def PlanarData.axes (p : PlanarData) (I : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => I i ^ 2 / (p.m i ^ 2 * p.kappa)

def p11c_hatFix (p : PlanarData) : Phase (2 + 2) → ℝ := fFix p.G p.m ∘ poincareProd p.m p.kappa
def p11c_hatMov (p : PlanarData) : Phase (2 + 2) → ℝ := fMov p.G p.m0 p.m ∘ poincareProd p.m p.kappa

def p11c_secular (P : Phase (2 + 2) → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  secularAverage (fun _ => P) 0 I z.2 z.1

def p11c_slowLength (z : Phase 2) : ℝ := sqrt (∑ i, (z.1 i ^ 2 + z.2 i ^ 2))
def p11c_pairDot (z : Phase 2) : ℝ := z.1 0 * z.1 1 + z.2 0 * z.2 1
def p11c_quartic (c : Fin 6 → ℝ) (z : Phase 2) : ℝ :=
  let A := z.1 0 ^ 2 + z.2 0 ^ 2
  let B := z.1 1 ^ 2 + z.2 1 ^ 2
  let D := p11c_pairDot z
  c 0 * A ^ 2 + c 1 * B ^ 2 + c 2 * A * B + c 3 * D ^ 2 + c 4 * A * D + c 5 * B * D

/-- Unit-axis physical position, from the existing regular Kepler solution. -/
def p11c_orbit (lam : ℝ) (v : Fin 2 → ℝ) : ℂ :=
  let F := keplerLong lam v
  let k := sqrt (1 - planeSq v)
  let q := k • orbitalUnit F - v + (planeDot v (orbitalUnit F) / (1 + k)) • v
  (q 0 : ℂ) + Complex.I * (q 1 : ℂ)

def p11c_orbitJet (lam : ℝ) (v : Fin 2 → ℝ) : ℂ :=
  let X := Complex.exp (Complex.I * lam)
  let z : ℂ := (v 0 : ℂ) + Complex.I * (v 1 : ℂ)
  let b := star z
  X + (X ^ 2 * b / 2 - 3 * z / 2) +
    (3 * X ^ 3 * b ^ 2 / 8 - X * z * b / 2 + X⁻¹ * z ^ 2 / 8) +
    (X ^ 4 * b ^ 3 / 3 - 3 * X ^ 2 * z * b ^ 2 / 8 + X ^ (-2 : ℤ) * z ^ 3 / 24) +
    (125 * X ^ 5 * b ^ 4 / 384 - 3 * X ^ 3 * z * b ^ 3 / 8 - X * z ^ 2 * b ^ 2 / 64 +
      X⁻¹ * z ^ 3 * b / 24 + 3 * X ^ (-3 : ℤ) * z ^ 4 / 128)

def p11c_JetEq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (f g : E → F) : Prop :=
  ∀ j ≤ k, iteratedFDeriv ℝ j f 0 = iteratedFDeriv ℝ j g 0

theorem orbit (lam : ℝ) :
    AnalyticAt ℝ (p11c_orbit lam) 0 ∧ p11c_JetEq 4 (p11c_orbit lam) (p11c_orbitJet lam) := sorry

/-- Purely local integral adapter for Part 8's laplace_def, to be identified by a bridge. -/
def p11c_laplace (s : ℝ) (k : ℤ) (a : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), cos ((k : ℝ) * t) / (1 + a ^ 2 - 2 * a * cos t) ^ s

theorem laplace_red (s a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    p11c_laplace (s - 1) k a = (1 + a ^ 2) * p11c_laplace s k a -
      a * (p11c_laplace s ((k : ℤ) + 1) a + p11c_laplace s ((k : ℤ) - 1) a) ∧
    (k : ℝ) * p11c_laplace (s - 1) k a = (s - 1) * a *
      (p11c_laplace s ((k : ℤ) - 1) a - p11c_laplace s ((k : ℤ) + 1) a) ∧
    (1 ≤ k → (s - 1 - k) * a * p11c_laplace s ((k : ℤ) + 1) a =
      (k + s - 1) * a * p11c_laplace s ((k : ℤ) - 1) a - k * (1 + a ^ 2) * p11c_laplace s k a) := sorry

/-- [A,B,p1,...,p6], exactly the displayed rational formulas. -/
def p11c_pairCoeffs (a : ℝ) : Fin 8 → ℝ :=
  let b0 := p11c_laplace (1 / 2) 0 a
  let b1 := p11c_laplace (1 / 2) 1 a
  let D := 1 - a ^ 2
  ![a * (2 * a * b0 - (1 + a ^ 2) * b1) / (4 * D ^ 2),
    (2 * (1 - a ^ 2 + a ^ 4) * b1 - a * (1 + a ^ 2) * b0) / (2 * D ^ 2),
    a * ((a + 14 * a ^ 3 + 33 * a ^ 5) * b0 - (2 - 6 * a ^ 2 + 46 * a ^ 4 + 6 * a ^ 6) * b1) / (64 * D ^ 4),
    a * ((33 * a + 14 * a ^ 3 + a ^ 5) * b0 - (6 + 46 * a ^ 2 - 6 * a ^ 4 + 2 * a ^ 6) * b1) / (64 * D ^ 4),
    3 * a * ((7 * a + 2 * a ^ 3 + 7 * a ^ 5) * b0 - (2 + 6 * a ^ 2 + 6 * a ^ 4 + 2 * a ^ 6) * b1) / (32 * D ^ 4),
    3 * a * ((-a + 18 * a ^ 3 - a ^ 5) * b0 + (2 - 10 * a ^ 2 - 10 * a ^ 4 + 2 * a ^ 6) * b1) / (16 * D ^ 4),
    ((4 - 15 * a ^ 2 + 50 * a ^ 4 + 9 * a ^ 6) * b1 - (2 * a + 4 * a ^ 3 + 42 * a ^ 5) * b0) / (16 * D ^ 4),
    a ^ 2 * ((9 + 50 * a ^ 2 - 15 * a ^ 4 + 4 * a ^ 6) * b1 - (42 * a + 4 * a ^ 3 + 2 * a ^ 5) * b0) / (16 * D ^ 4)]

def p11c_pairAverage (a : ℝ) (z : Phase 2) : ℝ :=
  (2 * π) ^ (-2 : ℤ) * ∫ l : Fin 2 → ℝ in Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π)),
    ‖(a : ℂ) * p11c_orbit (l 0) ![z.1 0, z.2 0] - p11c_orbit (l 1) ![z.1 1, z.2 1]‖⁻¹

def p11c_pairJet (a : ℝ) (z : Phase 2) : ℝ :=
  p11c_laplace (1 / 2) 0 a + p11c_pairCoeffs a 0 * (p11c_slowLength z) ^ 2 +
    p11c_pairCoeffs a 1 * p11c_pairDot z + p11c_quartic (fun i => p11c_pairCoeffs a (i.castAdd 2 + 2)) z

theorem pair_jet (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) :
    AnalyticAt ℝ (p11c_pairAverage a) 0 ∧ p11c_JetEq 5 (p11c_pairAverage a) (p11c_pairJet a) := sorry

def p11c_coeffs (p : PlanarData) (a : Fin 2 → ℝ) : Fin 6 → ℝ :=
  let I := p.actions a
  let A := p11c_pairCoeffs (a 0 / a 1)
  let pref := -p.G * p.m 0 * p.m 1 / a 1
  ![pref * (A 2 - A 0 / 4) / (I 0 ^ 2), pref * (A 3 - A 0 / 4) / (I 1 ^ 2),
    pref * A 4 / (I 0 * I 1), pref * A 5 / (I 0 * I 1),
    pref * (A 6 - A 1 / 8) / (I 0 ^ (3 / 2 : ℝ) * I 1 ^ (1 / 2 : ℝ)),
    pref * (A 7 - A 1 / 8) / (I 0 ^ (1 / 2 : ℝ) * I 1 ^ (3 / 2 : ℝ))]

def p11c_homogeneousPart (j : ℕ) (f : Phase 2 → ℝ) (z : Phase 2) : ℝ :=
  iteratedFDeriv ℝ j f 0 (fun _ => z) / (j.factorial : ℝ)

theorem quartic_explicit (p : PlanarData) (hp : p.Valid) :
    AnalyticOnNhd ℝ (p11c_coeffs p) p11c_axes ∧ ∀ a ∈ p11c_axes, ∀ z : Phase 2,
      p11c_homogeneousPart 4 (p11c_secular (p11c_hatFix p) (p.actions a)) z = p11c_quartic (p11c_coeffs p a) z ∧
      p11c_homogeneousPart 4 (p11c_secular (p11c_hatMov p) (p.actions a)) z = p11c_quartic (p11c_coeffs p a) z := sorry

/- Quartic families use actual finite polynomial coefficients, not a hypothesis that the
homological solution or a normal form already exists. -/
def p11c_monomial (a : Fin 4 → ℕ) (z : Phase 2) : ℝ :=
  z.1 0 ^ a 0 * z.2 0 ^ a 1 * z.1 1 ^ a 2 * z.2 1 ^ a 3

structure QuarticFamily (O : Set (Fin 2 → ℝ)) where
  coeff : (Fin 4 → ℕ) → (Fin 2 → ℝ) → ℝ
  analytic : ∀ a, AnalyticOnNhd ℝ (coeff a) O

def QuarticFamily.eval {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  ∑ a ∈ (Finset.univ : Finset (Fin 4 → Fin 5)).filter (fun a => ∑ i, (a i).val = 4),
    F.coeff (fun i => (a i).val) I * p11c_monomial (fun i => (a i).val) z

def p11c_rotation (theta : Fin 2 → ℝ) (z : Phase 2) : Phase 2 :=
  (fun j => cos (theta j) * z.1 j + sin (theta j) * z.2 j,
   fun j => -sin (theta j) * z.1 j + cos (theta j) * z.2 j)
def p11c_character (F : (Fin 2 → ℝ) → Phase 2 → ℝ) (k : Fin 2 → ℤ) (I : Fin 2 → ℝ) (z : Phase 2) : ℂ :=
  (2 * π : ℂ) ^ (-2 : ℤ) * ∫ theta : Fin 2 → ℝ in Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π)),
    Complex.exp (-Complex.I * (∑ j, (k j : ℂ) * theta j)) * (F I (p11c_rotation theta z) : ℂ)
def p11c_average (F : (Fin 2 → ℝ) → Phase 2 → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  (p11c_character F 0 I z).re

def p11c_NR4 (O : Set (Fin 2 → ℝ)) (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ I ∈ O, ∀ k : Fin 2 → ℤ, k ≠ 0 → (∑ i, |(k i : ℝ)|) ≤ 4 → ∑ i, (k i : ℝ) * freq I i ≠ 0

def p11c_n0 (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  ∑ j, freq I j * oscillatorAction z.2 z.1 j

def p11c_bracket (F G : Phase 2 → ℝ) (z : Phase 2) : ℝ :=
  fderiv ℝ F z (hamiltonianVectorField G z)

theorem char {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) :
    (∀ I z theta k, p11c_character F.eval k I (p11c_rotation theta z) =
      Complex.exp (Complex.I * (∑ j, (k j : ℂ) * theta j)) * p11c_character F.eval k I z) ∧
    (∀ I z k, 4 < (∑ i, |(k i : ℝ)|) → p11c_character F.eval k I z = 0) ∧
    (∀ I z, HasSum (fun k => p11c_character F.eval k I z) (F.eval I z : ℂ)) ∧
    (∀ I z k, star (p11c_character F.eval k I z) = p11c_character F.eval (-k) I z) := sorry

def p11c_chi {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  (∑' k : Fin 2 → ℤ, if k = 0 then 0 else
    p11c_character F.eval k I z / (Complex.I * (∑ j, (k j : ℂ) * freq I j))).re

theorem homological {O : Set (Fin 2 → ℝ)} (hO : IsOpen O) (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (hf : AnalyticOnNhd ℝ freq O) (hnr : p11c_NR4 O freq) :
    (∃ chi : QuarticFamily O, ∀ I ∈ O, chi.eval I = p11c_chi F freq I) ∧
    ∀ I ∈ O, ∀ z, p11c_bracket (p11c_chi F freq I) (p11c_n0 freq I) z =
      F.eval I z - p11c_average F.eval I z := sorry

/-- New real parametric ODE bridge: local solution/existence, analytic dependence,
variational equation and symplecticity are to be proved, not assumed. -/
theorem real_analytic_hamiltonian_local_flow {d : ℕ} {W : Set (Phase d)} (hW : IsOpen W)
    (H : Phase d → ℝ) (hH : AnalyticOnNhd ℝ H W) (x : Phase d) (hx : x ∈ W) :
    ∃ r T : ℝ, 0 < r ∧ 0 < T ∧ ∃ Phi : ℝ → Phase d → Phase d,
      AnalyticOnNhd ℝ (fun u : ℝ × Phase d => Phi u.1 u.2) (Ioo (-T) T ×ˢ ball x r) ∧
      (∀ y ∈ ball x r, Phi 0 y = y ∧
        IsSolutionIn (hamiltonianVectorField H) W (Ioo (-T) T) (fun t => Phi t y)) ∧
      (∀ t ∈ Ioo (-T) T, IsSymplecticOn 1 (Phi t) (ball x r)) := sorry

open Classical in
/-- Restricted time-one maps chosen by existence only; consumers use flow's specification. -/
def p11c_flow (chi : (Fin 2 → ℝ) → Phase 2 → ℝ) (I : Fin 2 → ℝ) (t : ℝ) (z : Phase 2) : Phase 2 :=
  if h : ∃ g : ℝ → Phase 2, IsSolutionIn (hamiltonianVectorField (chi I)) univ (Icc (-1) 1) g ∧ g 0 = z
  then h.choose t else z

theorem flow {O : Set (Fin 2 → ℝ)} (hO : IsOpen O) (chi : QuarticFamily O)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
      AnalyticOnNhd ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => p11c_flow chi.eval u.1 1 u.2)
        (K ×ˢ {z | p11c_slowLength z < r}) ∧
      ∀ I ∈ K, ∀ z : Phase 2, p11c_slowLength z < r →
        p11c_flow chi.eval I 0 z = z ∧
        IsSolutionIn (hamiltonianVectorField (chi.eval I)) univ (Icc (-1) 1)
          (fun t => p11c_flow chi.eval I t z) ∧
        (∀ t ∈ Icc (-1 : ℝ) 1, (p11c_slowLength (p11c_flow chi.eval I t z)) ^ 2 ≤ 2 * (p11c_slowLength z) ^ 2) ∧
        p11c_slowLength (p11c_flow chi.eval I 1 z - z) ≤ C * (p11c_slowLength z) ^ 3 ∧
        p11c_flow (fun J w => -chi.eval J w) I 1 (p11c_flow chi.eval I 1 z) = z := sorry

/-- Real Taylor bridge: no unverified small-holomorphic-flow hypothesis. -/
theorem real_lie_taylor {U : Set (Phase 2)} (hU : IsOpen U) (K chi : Phase 2 → ℝ)
    (hK : AnalyticOnNhd ℝ K U) (hc : AnalyticOnNhd ℝ chi U)
    (g : ℝ → Phase 2) (hg : IsSolutionIn (hamiltonianVectorField chi) U (Icc (0 : ℝ) 1) g) :
    K (g 1) = K (g 0) + p11c_bracket K chi (g 0) +
      ∫ t in (0 : ℝ)..1, (1 - t) * p11c_bracket (p11c_bracket K chi) chi (g t) := sorry

/-- R has a vanishing 5-jet; no normal-form conclusion is an input. -/
theorem lie {O : Set (Fin 2 → ℝ)} (hO : IsOpen O) (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (hf : AnalyticOnNhd ℝ freq O) (hnr : p11c_NR4 O freq)
    (C : (Fin 2 → ℝ) → ℝ) (R : (Fin 2 → ℝ) × Phase 2 → ℝ)
    (hR : ∀ I ∈ O, AnalyticAt ℝ R (I, 0))
    (hj : ∀ I ∈ O, p11c_JetEq 5 (fun z => R (I, z)) 0)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ A r : ℝ, 0 < A ∧ 0 < r ∧ ∀ I ∈ K, ∀ z : Phase 2, p11c_slowLength z < r →
      |(C I + p11c_n0 freq I (p11c_flow (p11c_chi F freq) I 1 z) +
        F.eval I (p11c_flow (p11c_chi F freq) I 1 z) + R (I, p11c_flow (p11c_chi F freq) I 1 z)) -
        (C I + p11c_n0 freq I z + p11c_average F.eval I z)| ≤ A * (p11c_slowLength z) ^ 6 := sorry

/-- Slow flow lifted in the frozen (phi,q;I,p) coordinate order. -/
def p11c_liftFlow (chi : (Fin 2 → ℝ) → Phase 2 → ℝ) (w : Phase (2 + 2)) : Phase (2 + 2) :=
  let I : Fin 2 → ℝ := fun i => w.2 (Fin.castAdd 2 i)
  let lam : Fin 2 → ℝ := fun i => w.1 (Fin.castAdd 2 i)
  let z : Phase 2 := (fun i => w.1 (Fin.natAdd 2 i), fun i => w.2 (Fin.natAdd 2 i))
  let Y := p11c_flow chi I 1 z
  let g : Fin 2 → ℝ := fun i => ∫ t in (0 : ℝ)..1,
    fderiv ℝ (fun J => chi J (p11c_flow chi I t z)) I (Pi.single i 1)
  assemble I (lam + g) Y.2 Y.1

def p11c_tube (O : Set (Fin 2 → ℝ)) (r : ℝ) : Set (Phase (2 + 2)) :=
  {w | (fun i => w.2 (Fin.castAdd 2 i)) ∈ O ∧
    p11c_slowLength (fun i => w.1 (Fin.natAdd 2 i), fun i => w.2 (Fin.natAdd 2 i)) < r}

theorem lift_map {O O' : Set (Fin 2 → ℝ)} (hO : IsOpen O) (hO' : IsOpen O')
    (hK : IsCompact (closure O')) (hKO : closure O' ⊆ O) (chi : QuarticFamily O) :
    ∃ r : ℝ, 0 < r ∧ IsChart 1 (p11c_liftFlow chi.eval) (p11c_tube O' r) ∧
      InjOn (p11c_liftFlow chi.eval) (p11c_tube O' r) ∧
      ∀ w ∈ p11c_tube O' r, ∀ c : Fin 2 → ℝ,
        p11c_liftFlow chi.eval (w + (Fin.append c 0, 0)) =
          p11c_liftFlow chi.eval w + (Fin.append c 0, 0) := sorry

/- Coefficients and global spectral projector are explicit and independent of a chosen eigenbasis. -/
def p11c_Q (p : PlanarData) (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let I := p.actions a
  let alpha := a 0 / a 1
  let A := p.G * p.m 0 * p.m 1 / (4 * a 1) * alpha * p11c_laplace (3 / 2) 1 alpha
  let B := p.G * p.m 0 * p.m 1 / (4 * a 1) * alpha * p11c_laplace (3 / 2) 2 alpha
  !![-A / I 0, B / sqrt (I 0 * I 1); B / sqrt (I 0 * I 1), -A / I 1]

def p11c_sigma (p : PlanarData) (a : Fin 2 → ℝ) : Fin 2 → ℝ :=
  let Q := p11c_Q p a
  let R := sqrt ((Q 0 0 - Q 1 1) ^ 2 + 4 * Q 0 1 ^ 2)
  ![(Q 0 0 + Q 1 1 - R) / 2, (Q 0 0 + Q 1 1 + R) / 2]

def p11c_projector (p : PlanarData) (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (p11c_sigma p a 0 - p11c_sigma p a 1)⁻¹ • (p11c_Q p a - p11c_sigma p a 1 • (1 : Matrix (Fin 2) (Fin 2) ℝ))

def beta_def (c : Fin 6 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let u := P 0 0; let v := P 1 1; let w := P 0 1; let D := u - v
  let A := c 0 * u ^ 2 + c 1 * v ^ 2 + (c 2 + c 3) * u * v + (c 4 * u + c 5 * v) * w
  let E := c 0 * v ^ 2 + c 1 * u ^ 2 + (c 2 + c 3) * u * v - (c 4 * v + c 5 * u) * w
  let B := 4 * (c 0 + c 1) * u * v + c 2 * D ^ 2 + c 3 * (D ^ 2 / 2 - 2 * u * v) + 2 * (c 5 - c 4) * w * D
  !![8 * A, 4 * B; 4 * B, 8 * E]

def p11c_beta (p : PlanarData) (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  beta_def (p11c_coeffs p a) (p11c_projector p a)

def p11c_rotateSlow (U : Matrix (Fin 2) (Fin 2) ℝ) (z : Phase 2) : Phase 2 :=
  (U.mulVec z.1, U.mulVec z.2)

theorem beta_formula (c : Fin 6 → ℝ) (g s : ℝ) (h : g ^ 2 + s ^ 2 = 1) (z : Phase 2) :
    let U : Matrix (Fin 2) (Fin 2) ℝ := !![g, -s; s, g]
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![g ^ 2, g * s; g * s, s ^ 2]
    p11c_average (fun _ w => p11c_quartic c (p11c_rotateSlow U w)) 0 z =
      (1 / 2 : ℝ) * ∑ i, ∑ j, beta_def c P i j * oscillatorAction z.2 z.1 i * oscillatorAction z.2 z.1 j := sorry

/-- Build the frozen predicate from a sixth-order remainder on the SAME perturbation.
A conditional helper has a distinct name and does not replace birkhoff_form. -/
theorem hasSecularBirkhoffForm_of_sixth_order
    (P : ℝ → Phase (2 + 2) → ℝ) (V : Set (Fin 2 → ℝ)) (r C mu0 : ℝ)
    (hr : 0 < r) (hC : 0 < C) (hmu : 0 < mu0)
    (P0 : ℝ → (Fin 2 → ℝ) → ℝ) (Omega : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ)
    (beta : ℝ → (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hi : ∀ mu ∈ Icc (0 : ℝ) mu0, ∀ I ∈ V, ∀ p q : Fin 2 → ℝ,
      p11c_slowLength (q, p) < r → IntegrableOn (fun phi => P mu (assemble I phi p q))
        (Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π))))
    (he : ∀ mu ∈ Icc (0 : ℝ) mu0, ∀ I ∈ V, ∀ p q : Fin 2 → ℝ,
      p11c_slowLength (q, p) < r →
      |secularAverage P mu I p q - (P0 mu I + (∑ j, Omega mu I j * oscillatorAction p q j) +
        (1 / 2 : ℝ) * ∑ i, ∑ j, beta mu I i j * oscillatorAction p q i * oscillatorAction p q j)| ≤
          C * (p11c_slowLength (q, p)) ^ 6) (r0 : ℝ) (hr0 : 0 < r0) (hrr : r0 ≤ r / sqrt 2) :
    HasSecularBirkhoffForm P V r0 mu0 P0 Omega beta := sorry

/-- Exact explicit global SO(2) eigenframe avoids the unpaid covering-space argument. -/
def p11c_frame (p : PlanarData) (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let Q := p11c_Q p a
  let s := p11c_sigma p a 0
  let v : Fin 2 → ℝ := ![-Q 0 1, Q 0 0 - s]
  let e := (sqrt (∑ i, v i ^ 2))⁻¹ • v
  !![e 0, -e 1; e 1, e 0]

theorem global_planar_frame (p : PlanarData) (hp : p.Valid) :
    (∀ i j, AnalyticOnNhd ℝ (fun a => p11c_frame p a i j) p11c_axes) ∧ ∀ a ∈ p11c_axes,
      (p11c_frame p a).transpose * p11c_frame p a = 1 ∧ (p11c_frame p a).det = 1 ∧
      (p11c_frame p a).transpose * p11c_Q p a * p11c_frame p a = Matrix.diagonal (p11c_sigma p a) := sorry

/-- The inverse rotation lift of Part 9, in the existing frozen assembled coordinates. -/
def p11c_rotationLift (p : PlanarData) (w : Phase (2 + 2)) : Phase (2 + 2) :=
  let I : Fin 2 → ℝ := fun i => w.2 (Fin.castAdd 2 i)
  let lam : Fin 2 → ℝ := fun i => w.1 (Fin.castAdd 2 i)
  let z : Phase 2 := (fun i => w.1 (Fin.natAdd 2 i), fun i => w.2 (Fin.natAdd 2 i))
  let U := p11c_frame p (p.axes I)
  let H : Fin 2 → ℝ := fun l => ∑ i, ∑ j, ∑ k,
    z.2 i * U k i * fderiv ℝ (fun J => p11c_frame p (p.axes J) k j) I (Pi.single l 1) * z.1 j
  let Z := p11c_rotateSlow U z
  assemble I (lam + H) Z.2 Z.1

/-- Simultaneous nonresonance polynomial; Part 9's Phi4 adapter, all modes 0<|k|1<=4. -/
def p11c_phi4 (p : PlanarData) (a : Fin 2 → ℝ) : ℝ :=
  ∏ k ∈ (Finset.univ : Finset (Fin 2 → Fin 9)).filter
    (fun k => 0 < (∑ i, |((k i).val : ℤ) - 4|) ∧ (∑ i, |((k i).val : ℤ) - 4|) ≤ 4),
    ∑ i, (((k i).val : ℝ) - 4) * p11c_sigma p a i

/-- Physical local normalisation, both physical perturbations, SAME coordinate map.
The output includes chart and domain, so neither is smuggled into a standing hypothesis. -/
def PlanarBirkhoffResult (p : PlanarData) (a0 : Fin 2 → ℝ) (rho : ℝ)
    (Oa : Set (Fin 2 → ℝ)) (r C : ℝ) : Prop :=
    ∃ O' : Set (Fin 2 → ℝ), IsOpen O' ∧ p.actions '' closedBall a0 rho ⊆ O' ∧
      IsCompact (closure O') ∧ closure O' ⊆ p.actions '' Oa ∧
      ∃ F chi : QuarticFamily O',
        (∀ I ∈ O', ∀ z, F.eval I z = p11c_quartic (p11c_coeffs p (p.axes I))
          (p11c_rotateSlow (p11c_frame p (p.axes I)) z)) ∧
        (∀ I ∈ O', chi.eval I = p11c_chi F (fun J j => 2 * p11c_sigma p (p.axes J) j) I) ∧
        ∃ T : Phase (2 + 2) → Phase (2 + 2),
        T = p11c_rotationLift p ∘ p11c_liftFlow chi.eval ∧
        (∀ I ∈ O', ∀ j, 2 * p11c_sigma p (p.axes I) j < 0) ∧
        IsChart 1 T (p11c_tube O' r) ∧ InjOn T (p11c_tube O' r) ∧
        (∀ w ∈ p11c_tube O' r, (fun i => (T w).2 (Fin.castAdd 2 i)) =
          (fun i => w.2 (Fin.castAdd 2 i))) ∧
        (∀ w ∈ p11c_tube O' r, ∀ c : Fin 2 → ℝ,
          T (w + (Fin.append c 0, 0)) = T w + (Fin.append c 0, 0)) ∧
        (∀ w ∈ p11c_tube O' r, T w ∈ poincareProdDom 2 ∧
          NoCollision (poincareProd p.m p.kappa (T w)).1) ∧
        ∀ fhat ∈ ({p11c_hatFix p, p11c_hatMov p} : Set (Phase (2 + 2) → ℝ)),
          AnalyticOnNhd ℝ (fhat ∘ T) (p11c_tube O' r) ∧
          ∃ P0 : (Fin 2 → ℝ) → ℝ, (∀ I ∈ p.actions '' closedBall a0 rho,
            P0 I = p11c_secular fhat I 0) ∧
          (∀ I ∈ p.actions '' closedBall a0 rho, ∀ z : Phase 2, p11c_slowLength z < r →
            |p11c_secular (fhat ∘ T) I z - (P0 I +
              (∑ j, 2 * p11c_sigma p (p.axes I) j * oscillatorAction z.2 z.1 j) +
              (1 / 2 : ℝ) * ∑ i, ∑ j, p11c_beta p (p.axes I) i j *
                oscillatorAction z.2 z.1 i * oscillatorAction z.2 z.1 j)| ≤ C * (p11c_slowLength z) ^ 6) ∧
          ∀ mu0 : ℝ, 0 < mu0 → ∀ r0 : ℝ, 0 < r0 → r0 ≤ r / sqrt 2 →
            HasSecularBirkhoffForm (fun _ => fhat ∘ T)
              (interior (p.actions '' closedBall a0 rho)) r0 mu0 (fun _ => P0)
              (fun _ I j => 2 * p11c_sigma p (p.axes I) j) (fun _ I => p11c_beta p (p.axes I))

theorem birkhoff_form (p : PlanarData) (hp : p.Valid)
    (a0 : Fin 2 → ℝ) (rho : ℝ)
    (hgoodK : closedBall a0 rho ⊆ {a ∈ p11c_axes | p11c_phi4 p a ≠ 0}) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ Oa : Set (Fin 2 → ℝ),
      IsOpen Oa → closedBall a0 rho ⊆ Oa →
      Oa ⊆ {a ∈ p11c_axes | p11c_phi4 p a ≠ 0} →
      PlanarBirkhoffResult p a0 rho Oa r C := sorry

/-- Relative error O(alpha²); constants depend only on the mass ratio after normalization. -/
def p11c_relativeError (f g : ℝ → ℝ) : Prop :=
  Asymptotics.IsBigO (nhdsWithin 0 (Ioi (0 : ℝ))) (fun a => f a / g a - 1) (fun a => a ^ 2)

theorem asymptotics (p : PlanarData) (hp : p.Valid) :
    p11c_relativeError (fun a => p11c_beta p ![a, 1] 0 0) (fun a => 3 * p.m 1 / (4 * p.m0 * p.m 0) * a) ∧
    p11c_relativeError (fun a => p11c_beta p ![a, 1] 0 1) (fun a => -9 / (4 * p.m0) * a ^ (3 / 2 : ℝ)) ∧
    p11c_relativeError (fun a => p11c_beta p ![a, 1] 1 1) (fun a => -3 * p.m 0 / (p.m0 * p.m 1) * a ^ 2) ∧
    p11c_relativeError (fun a => (p11c_beta p ![a, 1]).det) (fun a => -117 / (16 * p.m0 ^ 2) * a ^ 3) ∧
    (∀ a ∈ p11c_axes, ∀ s : ℝ, 0 < s → p11c_beta p (s • a) = (s ^ (-2 : ℤ)) • p11c_beta p a) := sorry

theorem torsion (p : PlanarData) (hp : p.Valid) :
    AnalyticOnNhd ℝ (fun a => (p11c_beta p a).det) p11c_axes ∧
    (∃ a ∈ p11c_axes, (p11c_beta p a).det < 0) ∧
    IsOpen {a ∈ p11c_axes | (p11c_beta p a).det ≠ 0} ∧
    p11c_axes ⊆ closure {a ∈ p11c_axes | (p11c_beta p a).det ≠ 0} ∧
    volume {a ∈ p11c_axes | (p11c_beta p a).det = 0} = 0 ∧
    IsOpen {a ∈ p11c_axes | p11c_phi4 p a * (p11c_beta p a).det ≠ 0} ∧
    p11c_axes ⊆ closure {a ∈ p11c_axes | p11c_phi4 p a * (p11c_beta p a).det ≠ 0} ∧
    volume {a ∈ p11c_axes | p11c_phi4 p a * (p11c_beta p a).det = 0} = 0 := sorry

theorem remain (p : PlanarData) (K : Set (Fin 2 → ℝ)) (hK : IsCompact K)
    (hn : ∀ a ∈ K, (p11c_beta p a).det ≠ 0)
    (hc : ContinuousOn (fun a => (p11c_beta p a).det) K) :
    ∃ B : ℝ, 0 < B ∧ ∀ a ∈ K, B ≤ |(p11c_beta p a).det| := sorry

/-- The extra Part-10 frequency certificate is a pending upstream attachment, see table U10.
This geometric projection has a distinct helper name and does not replace the full patch node. -/
theorem torsion_patch_geometry (p : PlanarData) (hp : p.Valid) (aStar : Fin 2 → ℝ)
    (ha : aStar ∈ p11c_axes) (eta : ℝ) (he : 0 < eta) :
    ∃ a0 : Fin 2 → ℝ, ∃ r B : ℝ, 0 < r ∧ 0 < B ∧
      closedBall a0 (2 * r) ⊆ ball aStar eta ∩
        {a ∈ p11c_axes | p11c_phi4 p a ≠ 0 ∧ (p11c_beta p a).det ≠ 0} ∧
      (∀ a ∈ closedBall a0 r, B ≤ |(p11c_beta p a).det| ∧ (p11c_beta p a).IsSymm) := sorry


/- Supplementary contract clauses, kept separate to keep the assembly statements small. -/
theorem orbit_analytic (lam : ℝ) :
    AnalyticOnNhd ℝ (p11c_orbit lam) {v | planeLength v < 1} := sorry

theorem orbit_poincare_bridge (lam L : ℝ) (hL : 0 < L) (u : Fin 2 → ℝ)
    (hu : planeSq u / 2 < L) :
    let w : Phase 2 := (![lam, u 0], ![L, u 1])
    let q := (poincare 1 (L ^ 2) w).1
    (q 0 : ℂ) + Complex.I * (q 1 : ℂ) = p11c_orbit lam (poincareV w) := sorry

theorem laplace_up (s a : ℝ) (hs : 1 / 2 ≤ s) (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (s + 1) 0 a = ((1 + a ^ 2) * p11c_laplace s 0 a +
      2 * a * (1 - 1 / s) * p11c_laplace s 1 a) / (1 - a ^ 2) ^ 2 ∧
    p11c_laplace (s + 1) 1 a = ((1 + a ^ 2) * (1 - 1 / s) * p11c_laplace s 1 a +
      2 * a * p11c_laplace s 0 a) / (1 - a ^ 2) ^ 2 ∧
    ∀ k : ℕ, 1 ≤ k → p11c_laplace (s + 1) ((k : ℤ) + 1) a =
      p11c_laplace (s + 1) ((k : ℤ) - 1) a - k * p11c_laplace s k a / (s * a) := sorry

/-- Polynomial quotients give rational functions with no poles on the admissible interval. -/
theorem laplace_rational_reduction (j k : ℕ) :
    ∃ p0 p1 q : Polynomial ℚ, ∀ a ∈ Ioo (0 : ℝ) 1,
      Polynomial.eval₂ (algebraMap ℚ ℝ) a q ≠ 0 ∧
      p11c_laplace (1 / 2 + (j : ℝ)) k a =
        (Polynomial.eval₂ (algebraMap ℚ ℝ) a p0 * p11c_laplace (1 / 2) 0 a +
         Polynomial.eval₂ (algebraMap ℚ ℝ) a p1 * p11c_laplace (1 / 2) 1 a) /
          Polynomial.eval₂ (algebraMap ℚ ℝ) a q := sorry

def p11c_pairSeriesJet (a : ℝ) : Fin 8 → ℝ :=
  ![3 / 8 * a ^ 2 + 45 / 64 * a ^ 4 + 525 / 512 * a ^ 6,
    -15 / 16 * a ^ 3 - 105 / 64 * a ^ 5 - 4725 / 2048 * a ^ 7,
    135 / 512 * a ^ 4 + 2625 / 2048 * a ^ 6,
    15 / 32 * a ^ 2 + 945 / 512 * a ^ 4 + 4725 / 1024 * a ^ 6,
    9 / 16 * a ^ 2 + 585 / 256 * a ^ 4 + 1575 / 256 * a ^ 6,
    315 / 128 * a ^ 4 + 4725 / 512 * a ^ 6,
    -45 / 64 * a ^ 3 - 525 / 128 * a ^ 5,
    -75 / 32 * a ^ 3 - 2205 / 256 * a ^ 5]

theorem pair_series :
    AnalyticOnNhd ℝ p11c_pairCoeffs (Ioo (-1 : ℝ) 1) ∧
    p11c_JetEq 6 p11c_pairCoeffs p11c_pairSeriesJet ∧
    p11c_JetEq 7 (fun a => p11c_pairCoeffs a 1) (fun a => p11c_pairSeriesJet a 1) := sorry

theorem pair_quadratic_consistency (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_pairCoeffs a 0 = a * p11c_laplace (3 / 2) 1 a / 4 ∧
    p11c_pairCoeffs a 1 = -a * p11c_laplace (3 / 2) 2 a / 2 := sorry

theorem quadratic_physical_bridge (p : PlanarData) (hp : p.Valid) (a : Fin 2 → ℝ)
    (ha : a ∈ p11c_axes) (z : Phase 2) :
    p11c_homogeneousPart 2 (p11c_secular (p11c_hatFix p) (p.actions a)) z =
      (∑ i, ∑ j, z.1 i * p11c_Q p a i j * z.1 j) +
      (∑ i, ∑ j, z.2 i * p11c_Q p a i j * z.2 j) := sorry

theorem character_bracket {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (k : Fin 2 → ℤ) (z : Phase 2) :
    fderiv ℝ (fun w => p11c_character F.eval k I w) z
      (hamiltonianVectorField (p11c_n0 freq I) z) =
        Complex.I * (∑ j, (k j : ℂ) * freq I j) * p11c_character F.eval k I z := sorry

theorem character_polynomial {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    (k : Fin 2 → ℤ) :
    (∀ z, AnalyticOnNhd ℝ (fun I => p11c_character F.eval k I z) O) ∧
    (∀ I, ∃ P : MvPolynomial (Fin 4) ℂ, P.totalDegree ≤ 4 ∧ ∀ z : Phase 2,
      p11c_character F.eval k I z = MvPolynomial.eval
        ![(z.1 0 : ℂ), (z.2 0 : ℂ), (z.1 1 : ℂ), (z.2 1 : ℂ)] P) ∧
    (∀ I z (t : ℝ), p11c_character F.eval k I (t • z) = (t : ℂ) ^ 4 * p11c_character F.eval k I z) ∧
    ∃ A : QuarticFamily O, ∀ I z, A.eval I z = p11c_average F.eval I z := sorry

theorem beta_properties (p : PlanarData) (hp : p.Valid) :
    (∀ i j, AnalyticOnNhd ℝ (fun a => p11c_beta p a i j) p11c_axes) ∧ ∀ a, (p11c_beta p a).IsSymm := sorry

/-- Same domain and physical Hamiltonian, the slow remainder bound cannot be assumed here. -/
theorem full_lift_hamiltonian {O O' : Set (Fin 2 → ℝ)} (hO : IsOpen O) (hO' : IsOpen O')
    (hK : IsCompact (closure O')) (hKO : closure O' ⊆ O) (chi : QuarticFamily O) :
    ∃ r : ℝ, 0 < r ∧ ∀ I ∈ O', ∀ lam : Fin 2 → ℝ, ∀ z : Phase 2,
      p11c_slowLength z < r → ∃ g : ℝ → Phase (2 + 2), g 0 = assemble I lam z.2 z.1 ∧
        g 1 = p11c_liftFlow chi.eval (assemble I lam z.2 z.1) ∧
        IsSolutionIn (hamiltonianVectorField (fun w : Phase (2 + 2) =>
          chi.eval (fun i => w.2 (Fin.castAdd 2 i))
            (fun i => w.1 (Fin.natAdd 2 i), fun i => w.2 (Fin.natAdd 2 i))))
          (p11c_tube O (2 * r)) (Icc (0 : ℝ) 1) g := sorry

/-- Uniformity only in the mass ratio, as claimed by asymptotics; absolute physical scales cancel. -/
theorem asymptotics_uniform_ratio (ratio : ℝ) (hratio : 0 < ratio) :
    ∃ C alpha0 : ℝ, 0 < C ∧ 0 < alpha0 ∧ alpha0 ≤ 1 ∧
      ∀ p : PlanarData, p.Valid → p.m 0 / p.m 1 = ratio → ∀ a ∈ Ioo (0 : ℝ) alpha0,
        |(p11c_beta p ![a, 1]).det / (-117 / (16 * p.m0 ^ 2) * a ^ 3) - 1| ≤ C * a ^ 2 ∧
        |p11c_beta p ![a, 1] 0 0 / (3 * p.m 1 / (4 * p.m0 * p.m 0) * a) - 1| ≤ C * a ^ 2 ∧
        |p11c_beta p ![a, 1] 0 1 / (-9 / (4 * p.m0) * a ^ (3 / 2 : ℝ)) - 1| ≤ C * a ^ 2 ∧
        |p11c_beta p ![a, 1] 1 1 / (-3 * p.m 0 / (p.m0 * p.m 1) * a ^ 2) - 1| ≤ C * a ^ 2 := sorry


/-- The source's combined fast/slow frequency, in frozen actions. -/
def p11c_combinedFrequency (p : PlanarData) (I : Fin 2 → ℝ) : Fin (2 + 2) → ℝ :=
  Fin.append (fun i => p.kappa ^ 2 * p.m i ^ 3 / I i ^ 3)
    (fun i => 2 * p11c_sigma p (p.axes I) i)

/-- Output projection needed from Part 10's interface, not an invented upstream theorem. -/
def PlanarFrequencyPatch (p : PlanarData) (a0 : Fin 2 → ℝ) (r : ℝ) : Prop :=
  let O := p.actions '' ball a0 (2 * r)
  let K := p.actions '' closedBall a0 r
  IsOpen O ∧ IsConnected O ∧ IsCompact K ∧ 0 < volume K ∧
  AnalyticOnNhd ℝ (p11c_combinedFrequency p) O ∧
  (∀ c : Fin (2 + 2) → ℝ, c ≠ 0 → ∃ I ∈ O, ∑ j, c j * p11c_combinedFrequency p I j ≠ 0) ∧
  (∃ alpha : ℝ, 0 < alpha ∧ ∀ a ∈ closedBall a0 r, ∀ k : Fin 2 → ℤ,
    k ≠ 0 → (∑ j, |(k j : ℝ)|) ≤ 4 → alpha ≤ |∑ j, (k j : ℝ) * (2 * p11c_sigma p a j)|) ∧
  ∃ mu0 : ℕ, 1 ≤ mu0 ∧ ∃ beta : ℝ, 0 < beta ∧ ∀ mu : ℕ, mu0 ≤ mu →
    ∀ c : Fin (2 + 2) → ℝ, KAM.Nekhoroshev.euclid c = 1 → ∀ I ∈ K,
      ∃ j ≤ mu, ∃ v : Fin 2 → ℝ, KAM.Nekhoroshev.euclid v = 1 ∧
        beta ≤ |iteratedFDeriv ℝ j (fun J => (∑ k, c k * p11c_combinedFrequency p J k) ^ 2)
          I (fun _ => v)|

/-- Full patch node: includes the retained Part-10 attachment and the Birkhoff map. -/
theorem patch (p : PlanarData) (hp : p.Valid) (aStar : Fin 2 → ℝ)
    (ha : aStar ∈ p11c_axes) (eta : ℝ) (he : 0 < eta) :
    ∃ a0 : Fin 2 → ℝ, ∃ r B : ℝ, 0 < r ∧ 0 < B ∧
      closedBall a0 (2 * r) ⊆ ball aStar eta ∩
        {a ∈ p11c_axes | p11c_phi4 p a ≠ 0 ∧ (p11c_beta p a).det ≠ 0} ∧
      (∀ a ∈ closedBall a0 r, B ≤ |(p11c_beta p a).det| ∧ (p11c_beta p a).IsSymm) ∧
      PlanarFrequencyPatch p a0 r ∧
      ∃ rStar CStar : ℝ, 0 < rStar ∧ 0 < CStar ∧
        PlanarBirkhoffResult p a0 r (ball a0 (2 * r)) rStar CStar := sorry


/-- Explicit pole envelope from laplace-red, with rational constant factors absorbed in p0,p1. -/
theorem laplace_reduction_denominator (j k : ℕ) :
    ∃ p0 p1 : Polynomial ℚ, ∀ a ∈ Ioo (0 : ℝ) 1,
      a ^ k * (1 - a ^ 2) ^ (2 * j) ≠ 0 ∧
      p11c_laplace (1 / 2 + (j : ℝ)) k a =
        (Polynomial.eval₂ (algebraMap ℚ ℝ) a p0 * p11c_laplace (1 / 2) 0 a +
         Polynomial.eval₂ (algebraMap ℚ ℝ) a p1 * p11c_laplace (1 / 2) 1 a) /
          (a ^ k * (1 - a ^ 2) ^ (2 * j)) := sorry

theorem average_action_polynomial {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) :
    ∃ a b c : (Fin 2 → ℝ) → ℝ, AnalyticOnNhd ℝ a O ∧ AnalyticOnNhd ℝ b O ∧ AnalyticOnNhd ℝ c O ∧
      ∀ I ∈ O, ∀ z, p11c_average F.eval I z =
        a I * (oscillatorAction z.2 z.1 0) ^ 2 +
        b I * oscillatorAction z.2 z.1 0 * oscillatorAction z.2 z.1 1 +
        c I * (oscillatorAction z.2 z.1 1) ^ 2 := sorry

theorem asymptotics_general_axes (ratio : ℝ) (hratio : 0 < ratio) :
    ∃ C alpha0 : ℝ, 0 < C ∧ 0 < alpha0 ∧ ∀ p : PlanarData,
      p.Valid → p.m 0 / p.m 1 = ratio → ∀ a ∈ p11c_axes, a 0 / a 1 < alpha0 →
        |(p11c_beta p a).det / (-117 / (16 * p.m0 ^ 2) * a 0 ^ 3 / a 1 ^ 7) - 1| ≤
          C * (a 0 / a 1) ^ 2 := sorry

end KAM.Planetary
```
