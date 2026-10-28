# Lean design: planetary finite preparation, weak measure and the maximal canonical step

Design P11A, Revision 3, 2026-10-28, branch `inp-design-p11a`. Planning evidence only. Scope is the 164 graph
records whose statement source lies in `p11-cp09-preparation.tex`, `p11a1-weak-measure.tex` or
`p11a2-cutoff-step.tex`. No frozen theorem is closed directly. The downstream P-FIXED assembly
belongs to Part 13; this document does not claim any proof closure.

Read with the common design brief and its 2026-10-28 extension, and graph P's `GLOBAL-review.md`,
“Suspected blueprint defects and source limitations”. The worktree has the blueprint but no
`docs/graph/P/DEPGRAPH.md`; coverage is therefore taken from the designated `inp` checkout's
current graph. No graph or blueprint has been edited.


### Input pins

Worktree base: `081967912d5200ad4711d6d16abde6a8cfafea71`. All three blueprint files were compared byte-for-byte with `inp`; they agree.

| Input | SHA-256 |
|---|---|
| `blueprint-P/parts/p11-cp09-preparation.tex` | `4c0e2dfefb50b1e06581e069a55846d25e0e4697a8826514ac699bbb83efb41f` |
| `blueprint-P/parts/p11a1-weak-measure.tex` | `66b5ce26db59b57dbf934938a7bae2fead6b6ff4c7c9d420d33b9582e272bab5` |
| `blueprint-P/parts/p11a2-cutoff-step.tex` | `990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec` |
| `inp:docs/graph/P/DEPGRAPH.md` | `5b1eff327a09a63a553686ba14a4763978e0f589fde8ad42cc67d6545f819f44` |

## 1. Decisions

1. Separate three layers: `WeakMeasure` (parameter dimension N independent of frequency dimension m),
   `MaximalStep` (N angles, N actions, N parameters), and `Preparation` (n fast angles and n secular pairs).
   The squared scalar family is used in preparation; the general measure layer retains both rho=1 and rho=2.
2. Retain existing carriers and operators: frozen `Phase`, `complexStrip`, `actionNbhd`,
   `IsDiophantine`, `IsPhysicalTorus`, `fixedHamiltonian`, `circularTube`; `Weighted.Dom`,
   `Weighted.coeff`, `Weighted.truncate`, `Weighted.WSummable`, `Weighted.wsum`; `Canonical.poissonBracket`,
   `Canonical.flow`, `Canonical.scaledNorm`, `Canonical.symplFormC`; the existing product Poincare chart.
   New aliases are only notation. No global norm or matrix instance is introduced.
3. Explicit Euclidean lengths use `KAM.Nekhoroshev.euclid`. The ambient Pi norm stays the max norm.
   `p11dg` and `p11op` evaluate the SAME `iteratedFDeriv` on Euclidean unit directions. Never identify
   the latter with Lean's default operator norm on a Pi carrier. Conversion factors are explicit.
4. Sup bounds are pointwise `p11Bound`; finite jet bounds are `p11JetBound`. Amounts use a real
   infimum of finite maxima on the compact sphere/patch. Prove boundedness, continuity and attainment
   before using the infimum: no junk infimum is permitted in a proof. The least positive index is
   `p11Index`, meaningful only after `rank_compact` establishes existence.
5. Use the blueprint's actual route: fast averaging (nu1=3), canonical polar normalization, rectangular
   slow averaging with arbitrary fixed nu2, and rescaling. There is no finite Birkhoff step in this route.
6. Keep `K_epsilon=[-1/2,1/2]^(2n)`, vartheta=1/4, eps*=1/2, strip sigma_F/72,
   tau_D=max(n*mu,2n), and the amount `beta_epsilon=(beta_J/2)*epsilon^(mu+2)`.
   All entries except beta_epsilon are fixed before nu2 and epsilon. The exponent
   `Q=5*tau0+2+(tau0+1)*(mu+1)` includes the unscaled J derivative loss.
7. Every stage structure is an OUTPUT. Subsequent constructions select a stage output with classical
   choice from its existence theorem; no result in this design takes such an output specification as
   an extra hypothesis. `P11Physical` and the analytic step/measure hypotheses contain source inputs only.
   Where upstream Part 9/10 interfaces are not yet delivered, the reconciliation table below is binding;
   local data packages do not replace those upstream theorems.
8. Repair the real-flow source gap explicitly: `canonical_step` proves the complex result;
   `canonical_step_real` carries the reality guard on R. This is a reported blueprint correction,
   not a change to any frozen statement. Part 11's actual Hamiltonians are real, so their uses supply it.
9. The unweighted derivative estimate `2*kappa+kappa*s/sigma` is exported as well as the changing
   weighted estimate. Part 11a-3 must sum the former for composition in a fixed norm.
10. Graph proof-step nodes are assigned to named local obligations in the indicated exported theorem's
    proof. They are not independent black-box hypotheses. The node table includes all such steps and
    every standing-data/external record; their exact mathematical obligations and dependencies are
    retained in the contract registry. Splitting a proof into helper lemmas keeps these names and types.

## 2. Carriers and conventions

| Object | Exact carrier / representation |
|---|---|
| parameter / frequency / Fourier mode | `Fin N → ℝ`, `Fin m → ℝ`, `Fin m → ℤ` |
| complex angle, action, parameter | `Fin N → ℂ` each |
| phase / extended family | `(Fin N → ℂ) × (Fin N → ℂ)`, that product paired with `Fin N → ℂ` |
| finite preparation working phase | `(Fin (n+n) → ℂ) × (Fin (n+n) → ℂ)`, positions `(theta,x)`, momenta `(J,y)` |
| physical phase | frozen `Phase (n*2)`; `Kepler.phaseCast (Nat.mul_two n)` handles the dimension equality |
| maximal-step domain | `Weighted.Dom N {0} s r ×ˢ B` (angles width r, action radius s) |
| complex parameter tube | frozen `actionNbhd E t`; the real measure thickening is explicit Euclidean `p11thick` |
| matrix / Jacobian | `Matrix` for algebra; CLMs for induced max operator norms, not the pointwise Pi matrix norm |
| measure | `volume : Measure (Fin N → ℝ)` and `volume : Measure (Phase d)`; inequalities in ENNReal |
| diagonal and full tensors | existing `iteratedFDeriv ℝ j`, evaluated with explicit Euclidean lengths |
| bracket / field | existing `Canonical.poissonBracket` and frozen `hamiltonianVectorFieldℂ` |
| flow | existing `Canonical.flow`, specialized to affine-in-action generators |

Angles have period one. Characters are the existing `KAM.character`; divisors use
`Fourier.modeSize k=|k|_1`. The cohomological equation has POSITIVE sign:
`omega . d_theta phi = P-<P>`, hence `{N,phi}=-(P-<P>)`. All radii/divisors/ratios carry their
positivity assumptions, including mu>=1, N>=1 and m>=1. Zero epsilon and zero A1 remain allowed.
Real exponents use `Real.rpow`; order and lattice exponents which are integers use natural powers.

`p11Good K wt psi` tests one map `wt k` per mode. It is not `IsDiophantine` of a vector.
Only `limit_bridge_diophantine`, after the per-mode tail estimate, produces the frozen predicate.
The measure theorem uses an ENNReal tsum, allowing an infinite right side without treating a
nonsummable real tsum as zero. Finite real series (`loss_sum`, lambda) carry `Summable` explicitly.

The scalar sublevel theorem needs a Euclidean closed ball, rotation with determinant absolute value 1,
and Tonelli on `Fin (N-1) → ℝ × ℝ`; N=1 is treated separately, not discarded. Max-diameter d is
converted to Euclidean diameter by sqrt(N), exactly as in C_sub.

## 3. Reuse map and upstream interfaces to reconcile

These names were read from delivered source or the supplied signatures, not guessed from paper notation.
An absent module is a future import edge, not permission to create an alternative representation.

| Input | Existing declaration / owner | Application and exact compatibility obligation |
|---|---|---|
| norms | `KAM.Nekhoroshev.euclid`, `norm_le_euclid`, `modeSize_euclid_compare` in `Interfaces/Norms` | explicit Euclidean directions and sqrt(m) lattice conversion |
| domains | `Weighted.Dom`, `polyNbhd`, `isOpen_Dom`, `actionNbhd_eq_polyNbhd` | family domains; parameter tube is frozen `actionNbhd` |
| Fourier | `Weighted.coeff`, `truncate`, `modeAverage`; `KAM.torusCoeffW`, `character`, `decay_boundary_radius`, `eq_fourierSumVec_torusCoeffW` | truncation is the delivered operator; finite-support proof converts tsum to finite sum |
| lattice | `KAM.Measure.lattice_count`, `KAM.Measure.lattice_sum`, `KAM.Fourier.modeSize` | polynomial tail and power-law sum; retain lattice l1 norm |
| parameter integral | `Weighted.holomorphic_parametric_integral` | holomorphic Fourier coefficients / averages; integrands continuous over a compact real cube |
| Cauchy | `Weighted.general_cauchy`, `KAM.norm_iteratedFDeriv_le_of_closedBall`, `KAM.cauchy_strip` | first derivative reused; arbitrary mixed parameter derivative constant j^j is a NEW lemma |
| gauge flow | `Canonical.scaleCLE`, `SmallField`, `flow_a`, `flow_b`, `flow_c`, `flow_d`, `flow_e`, `flow_symplFormC` | prove actual polydisc inclusions in gauge interiors before applying; augmented (b,z) field proves joint holomorphy |
| Lie identity | `Canonical.poissonBracket_eq_fderiv_field`, `Canonical.taylor_lie`, `Canonical.taylor_poschel` | use the actual flow; second-order integral remainder keeps the sign and the factor (1-t) |
| ODE | `KAM.ODE.gen_local`, `gen_uniform_exist`, `gen_uniqueness`, `gen_continuation_compact` | supply nonlinear bounded global flow and variational bridge; x-ode alone is insufficient |
| P1 charts | `KAM.Planetary.IsChart`, `chart_field`, `hol_chart`, `torus_transport_phys`, `phys_pipeline` from `PPart1Signatures.lean` | conformal factor epsilon; H_pullback=epsilon^-1 H o chart; primary-to-physical lattice transport |
| P1 measure | `chart_measure_image`, `liouville_lattice_measurableSet`, `measure_chart_image`, `torus_union_saturation` | Borel saturated union and positive measure after chart; do not infer Borel from continuous image alone |
| P6/7 | `poincareProd`, `planetBlock`, `poincareGamma`, `poincareProdDom`, `poincareProdCast`, `Kepler.phaseCast`, `polarMap`, `angleScale` | existing product chart; period-one polar conversion has action divided by 2pi as well as angle multiplied by 2pi |
| physical tube | `tubeRadius`, `axisGap`, `axisMax`, `AxisData`, `axisData_canonical`, `circularTube`, `circularPoint` | exact zeta*=min(eta,gap/6); arbitrary-n forward tube generalizes the Part12 compactness argument |
| N6/7 | `KAM.Nekhoroshev.homological_direct`, `iterative_direct_a`..`iterative_direct_e`, `telescope`, `normal_form` | use exact supplied types; NOT a plug-in for rectangular averaging or the sup-norm maximal step. Prove explicit gauge/domain adapters first. |
| P2 not yet designed | `KAM.Planetary.osc_averaging`, `nfb`, `direct`, `split`, `osc_iter` | need fast-only averaging with oscillator parameters and two-scale normal form on polydiscs, alpha_bar=2pi alpha; physical hypotheses supply positivity, weighted input and finite cutoff nonresonance |
| P8 not yet designed | `perturbation_analytic`, `evenness`, `coeffs` | physical product-chart perturbation analytic, vanishing odd jets, exact secular quadratic coefficients; complex strip needs separate compactness extension |
| P9 not yet designed | `local_analytic`, `lift`, `diagonalize` | analytic real SO(n) rotation and canonical lift with angle correction; supply simple spectrum from P10 and use explicit complexification/identity suppliers below |
| P10 not yet designed | `interface`, `finite_type`, `rnd`, `cp09_lemma1`, `scaling` | physical frequency is the Kepler block plus secular eigenfrequency block on Lambda patch; squared diagonal amount on compact patch; exact varpi_J=(2pi)^-1 varpi_tilde(J/2pi). Appendix A ties its patch to the frozen secular average through the literal secular Hessian, sorted characteristic roots and the explicit fast frequency formula; reconcile this equality with Part10's returned map. |
| P11a-3 not yet designed | `finite_divisor`, `adm_budget`, `adm_budget_beta` | source index/amount, finite retained-set divisors, B0=mu(mu+1)+2; no limiting-frequency premise in finite step |
| P11a-4/5 not yet designed | `weak_kam_quantitative`, `limit_torus`, `displacement`, `evaluation_bilipschitz`, `budget` | primary tori, compact H, measure factor 2^(-2N), lower monotone budget and displacement power, with constants uniform in all admissible H |

The Part11 `kam-input` node is a citation to the last two rows, not a new theorem assumed in
`wrapper`. Its exact supplied shape is (K1)-(K6) at the source locator in the registry. In particular
(K6) is not an output of Part11a-3. Reconciliation must preserve beta-uniform constants, the monotone
minorant's validity for smaller M0, physical time and primary winding. No P11 package can claim root
closure until these upstream interfaces and the equality between the literal secular Hessian and Part10's Q_h is proved.

## 4. Every graph node to Lean responsibility

Paths below are under `KAM/Planetary/`; add `.lean`. Names are in `KAM.Planetary` unless qualified.
`local name in theorem` means a named proof-local `have` (or a private helper split from it), never a
premise. The registry immediately following the table supplies its exact source conclusion and inputs.
Standing-data nodes name output/construction carriers; external nodes name library facts or new local suppliers.

| Graph node | Declaration / local obligation | Module | Statement / proof locator |
|---|---|---|---|
| `bpP:p11:kam-input` | upstream `weak_kam_quantitative` + `budget` + `displacement` | `Preparation/Wrapper` | `p11-cp09-preparation.tex#bpP:p11:kam-input@L24-L38`; `-` |
| `bpP:p11:norm-dict` | `norm_dict` | `Preparation/Working` | `p11-cp09-preparation.tex#bpP:p11:norm-dict@L46-L48`; `p11-cp09-preparation.tex#bpP:p11:norm-dict@L49-L51` |
| `stepP:p11:nd` | `nd` local in `norm_dict` | `Preparation/Working` | `p11-cp09-preparation.tex#stepP:p11:nd@L50-L50`; `p11-cp09-preparation.tex#stepP:p11:nd@L50-L50` |
| `bpP:p11:select` | `select` | `Preparation/BasePoint` | `p11-cp09-preparation.tex#bpP:p11:select@L53-L55`; `p11-cp09-preparation.tex#bpP:p11:select@L56-L60` |
| `stepP:p11:sel-hyp` | `sel_hyp` local in `select` | `Preparation/BasePoint` | `p11-cp09-preparation.tex#stepP:p11:sel-hyp@L57-L57`; `p11-cp09-preparation.tex#stepP:p11:sel-hyp@L57-L57` |
| `stepP:p11:sel-gam` | `sel_gam` local in `select` | `Preparation/BasePoint` | `p11-cp09-preparation.tex#stepP:p11:sel-gam@L58-L58`; `p11-cp09-preparation.tex#stepP:p11:sel-gam@L58-L58` |
| `stepP:p11:sel-int` | `sel_int` local in `select` | `Preparation/BasePoint` | `p11-cp09-preparation.tex#stepP:p11:sel-int@L59-L59`; `p11-cp09-preparation.tex#stepP:p11:sel-int@L59-L59` |
| `bpP:p11:holo-chart` | `holo_chart` | `Preparation/Holomorphic` | `p11-cp09-preparation.tex#bpP:p11:holo-chart@L63-L73`; `p11-cp09-preparation.tex#bpP:p11:holo-chart@L74-L84` |
| `stepP:p11:hc-rot` | `hc_rot` local in `holo_chart` | `Preparation/Holomorphic` | `p11-cp09-preparation.tex#stepP:p11:hc-rot@L75-L75`; `p11-cp09-preparation.tex#stepP:p11:hc-rot@L75-L75` |
| `stepP:p11:hc-lift` | `hc_lift` local in `holo_chart` | `Preparation/Holomorphic` | `p11-cp09-preparation.tex#stepP:p11:hc-lift@L76-L78`; `p11-cp09-preparation.tex#stepP:p11:hc-lift@L76-L78` |
| `stepP:p11:hc-strip` | `hc_strip` local in `holo_chart` | `Preparation/Holomorphic` | `p11-cp09-preparation.tex#stepP:p11:hc-strip@L79-L79`; `p11-cp09-preparation.tex#stepP:p11:hc-strip@L79-L79` |
| `stepP:p11:hc-F` | `hc_F` local in `holo_chart` | `Preparation/Holomorphic` | `p11-cp09-preparation.tex#stepP:p11:hc-F@L80-L80`; `p11-cp09-preparation.tex#stepP:p11:hc-F@L80-L80` |
| `stepP:p11:hc-id` | `hc_id` local in `holo_chart` | `Preparation/Holomorphic` | `p11-cp09-preparation.tex#stepP:p11:hc-id@L81-L81`; `p11-cp09-preparation.tex#stepP:p11:hc-id@L81-L81` |
| `stepP:p11:hc-lat` | `hc_lat` local in `holo_chart` | `Preparation/Holomorphic` | `p11-cp09-preparation.tex#stepP:p11:hc-lat@L82-L82`; `p11-cp09-preparation.tex#stepP:p11:hc-lat@L82-L82` |
| `stepP:p11:hc-mean` | `hc_mean` local in `holo_chart` | `Preparation/Holomorphic` | `p11-cp09-preparation.tex#stepP:p11:hc-mean@L83-L83`; `p11-cp09-preparation.tex#stepP:p11:hc-mean@L83-L83` |
| `bpP:p11:total-chart` | `total_chart` | `Preparation/Polar` | `p11-cp09-preparation.tex#bpP:p11:total-chart@L86-L88`; `p11-cp09-preparation.tex#bpP:p11:total-chart@L89-L92` |
| `stepP:p11:tc-polar` | `tc_polar` local in `total_chart` | `Preparation/Polar` | `p11-cp09-preparation.tex#stepP:p11:tc-polar@L90-L90`; `p11-cp09-preparation.tex#stepP:p11:tc-polar@L90-L90` |
| `stepP:p11:tc-lat` | `tc_lat` local in `total_chart` | `Preparation/Polar` | `p11-cp09-preparation.tex#stepP:p11:tc-lat@L91-L91`; `p11-cp09-preparation.tex#stepP:p11:tc-lat@L91-L91` |
| `bpP:p11:avg-fast` | `avg_fast` | `Preparation/Fast` | `p11-cp09-preparation.tex#bpP:p11:avg-fast@L102-L108`; `p11-cp09-preparation.tex#bpP:p11:avg-fast@L109-L114` |
| `stepP:p11:af-apply` | `af_apply` local in `avg_fast` | `Preparation/Fast` | `p11-cp09-preparation.tex#stepP:p11:af-apply@L110-L110`; `p11-cp09-preparation.tex#stepP:p11:af-apply@L110-L110` |
| `stepP:p11:af-o1` | `af_o1` local in `avg_fast` | `Preparation/Fast` | `p11-cp09-preparation.tex#stepP:p11:af-o1@L111-L111`; `p11-cp09-preparation.tex#stepP:p11:af-o1@L111-L111` |
| `stepP:p11:af-o2` | `af_o2` local in `avg_fast` | `Preparation/Fast` | `p11-cp09-preparation.tex#stepP:p11:af-o2@L112-L112`; `p11-cp09-preparation.tex#stepP:p11:af-o2@L112-L112` |
| `stepP:p11:af-concl` | `af_concl` local in `avg_fast` | `Preparation/Fast` | `p11-cp09-preparation.tex#stepP:p11:af-concl@L113-L113`; `p11-cp09-preparation.tex#stepP:p11:af-concl@L113-L113` |
| `bpP:p11:aniso-bracket` | `aniso_bracket`, `aniso_field` | `Preparation/RectangularBracket` | `p11-cp09-preparation.tex#bpP:p11:aniso-bracket@L120-L124`; `p11-cp09-preparation.tex#bpP:p11:aniso-bracket@L125-L128` |
| `stepP:p11:ab-der` | `ab_der` local in `aniso_bracket` | `Preparation/RectangularBracket` | `p11-cp09-preparation.tex#stepP:p11:ab-der@L126-L126`; `p11-cp09-preparation.tex#stepP:p11:ab-der@L126-L126` |
| `stepP:p11:ab-prod` | `ab_prod` local in `aniso_bracket` | `Preparation/RectangularBracket` | `p11-cp09-preparation.tex#stepP:p11:ab-prod@L127-L127`; `p11-cp09-preparation.tex#stepP:p11:ab-prod@L127-L127` |
| `bpP:p11:aniso-avg` | `aniso_avg` | `Preparation/RectangularAverage` | `p11-cp09-preparation.tex#bpP:p11:aniso-avg@L130-L138`; `p11-cp09-preparation.tex#bpP:p11:aniso-avg@L139-L142` |
| `stepP:p11:aa-same` | `aa_same` local in `aniso_avg` | `Preparation/RectangularAverage` | `p11-cp09-preparation.tex#stepP:p11:aa-same@L140-L140`; `p11-cp09-preparation.tex#stepP:p11:aa-same@L140-L140` |
| `stepP:p11:aa-quad` | `aa_quad` local in `aniso_avg` | `Preparation/RectangularAverage` | `p11-cp09-preparation.tex#stepP:p11:aa-quad@L141-L141`; `p11-cp09-preparation.tex#stepP:p11:aa-quad@L141-L141` |
| `bpP:p11:polar-avg` | `polar_avg`, `polar_average_linear`, `polar_average_normalization`, `polar_extension_unique` | `Preparation/PolarAverage` | `p11-cp09-preparation.tex#bpP:p11:polar-avg@L155-L163`; `p11-cp09-preparation.tex#bpP:p11:polar-avg@L164-L168` |
| `stepP:p11:pa-taylor` | `pa_taylor` local in `polar_avg` | `Preparation/PolarAverage` | `p11-cp09-preparation.tex#stepP:p11:pa-taylor@L165-L165`; `p11-cp09-preparation.tex#stepP:p11:pa-taylor@L165-L165` |
| `stepP:p11:pa-mono` | `pa_mono` local in `polar_avg` | `Preparation/PolarAverage` | `p11-cp09-preparation.tex#stepP:p11:pa-mono@L166-L166`; `p11-cp09-preparation.tex#stepP:p11:pa-mono@L166-L166` |
| `stepP:p11:pa-series` | `pa_series` local in `polar_avg` | `Preparation/PolarAverage` | `p11-cp09-preparation.tex#stepP:p11:pa-series@L167-L167`; `p11-cp09-preparation.tex#stepP:p11:pa-series@L167-L167` |
| `bpP:p11:avg-slow` | `avg_slow` | `Preparation/Slow` | `p11-cp09-preparation.tex#bpP:p11:avg-slow@L170-L179`; `p11-cp09-preparation.tex#bpP:p11:avg-slow@L180-L185` |
| `stepP:p11:as-osc` | `as_osc` local in `avg_slow` | `Preparation/Slow` | `p11-cp09-preparation.tex#stepP:p11:as-osc@L181-L181`; `p11-cp09-preparation.tex#stepP:p11:as-osc@L181-L181` |
| `stepP:p11:as-nr` | `as_nr` local in `avg_slow` | `Preparation/Slow` | `p11-cp09-preparation.tex#stepP:p11:as-nr@L182-L182`; `p11-cp09-preparation.tex#stepP:p11:as-nr@L182-L182` |
| `stepP:p11:as-b2` | `as_b2` local in `avg_slow` | `Preparation/Slow` | `p11-cp09-preparation.tex#stepP:p11:as-b2@L183-L183`; `p11-cp09-preparation.tex#stepP:p11:as-b2@L183-L183` |
| `stepP:p11:as-concl` | `as_concl` local in `avg_slow` | `Preparation/Slow` | `p11-cp09-preparation.tex#stepP:p11:as-concl@L184-L184`; `p11-cp09-preparation.tex#stepP:p11:as-concl@L184-L184` |
| `bpP:p11:prepared` | `prepared` | `Preparation/Prepared` | `p11-cp09-preparation.tex#bpP:p11:prepared@L196-L204`; `p11-cp09-preparation.tex#bpP:p11:prepared@L205-L212` |
| `stepP:p11:pr-basic` | `pr_basic` local in `prepared` | `Preparation/Prepared` | `p11-cp09-preparation.tex#stepP:p11:pr-basic@L206-L206`; `p11-cp09-preparation.tex#stepP:p11:pr-basic@L206-L206` |
| `stepP:p11:pr-a` | `pr_a` local in `prepared` | `Preparation/Prepared` | `p11-cp09-preparation.tex#stepP:p11:pr-a@L207-L207`; `p11-cp09-preparation.tex#stepP:p11:pr-a@L207-L207` |
| `stepP:p11:pr-in` | `pr_in` local in `prepared` | `Preparation/Prepared` | `p11-cp09-preparation.tex#stepP:p11:pr-in@L208-L208`; `p11-cp09-preparation.tex#stepP:p11:pr-in@L208-L208` |
| `stepP:p11:pr-b` | `pr_b` local in `prepared` | `Preparation/Prepared` | `p11-cp09-preparation.tex#stepP:p11:pr-b@L209-L209`; `p11-cp09-preparation.tex#stepP:p11:pr-b@L209-L209` |
| `stepP:p11:pr-c` | `pr_c` local in `prepared` | `Preparation/Prepared` | `p11-cp09-preparation.tex#stepP:p11:pr-c@L210-L210`; `p11-cp09-preparation.tex#stepP:p11:pr-c@L210-L210` |
| `stepP:p11:pr-d` | `pr_d` local in `prepared` | `Preparation/Prepared` | `p11-cp09-preparation.tex#stepP:p11:pr-d@L211-L211`; `p11-cp09-preparation.tex#stepP:p11:pr-d@L211-L211` |
| `bpP:p11:amount` | `amount` | `Preparation/Amount` | `p11-cp09-preparation.tex#bpP:p11:amount@L214-L217`; `p11-cp09-preparation.tex#bpP:p11:amount@L218-L222` |
| `stepP:p11:am-norm` | `am_norm` local in `amount` | `Preparation/Amount` | `p11-cp09-preparation.tex#stepP:p11:am-norm@L219-L219`; `p11-cp09-preparation.tex#stepP:p11:am-norm@L219-L219` |
| `stepP:p11:am-dir` | `am_dir` local in `amount` | `Preparation/Amount` | `p11-cp09-preparation.tex#stepP:p11:am-dir@L220-L220`; `p11-cp09-preparation.tex#stepP:p11:am-dir@L220-L220` |
| `stepP:p11:am-scale` | `am_scale` local in `amount` | `Preparation/Amount` | `p11-cp09-preparation.tex#stepP:p11:am-scale@L221-L221`; `p11-cp09-preparation.tex#stepP:p11:am-scale@L221-L221` |
| `bpP:p11:forward-tube` | `forward_tube` | `Preparation/ForwardTube` | `p11-cp09-preparation.tex#bpP:p11:forward-tube@L230-L232`; `p11-cp09-preparation.tex#bpP:p11:forward-tube@L233-L235` |
| `bpP:p11:wrapper` | `wrapper` | `Preparation/Wrapper` | `p11-cp09-preparation.tex#bpP:p11:wrapper@L237-L241`; `p11-cp09-preparation.tex#bpP:p11:wrapper@L247-L254` |
| `bpP:p11:data-star` | `data_star` | `Preparation/Datum` | `p11-cp09-preparation.tex#bpP:p11:data-star@L243-L245`; `p11-cp09-preparation.tex#bpP:p11:data-star@L243-L245` |
| `stepP:p11:wr-nu` | `wr_nu` local in `wrapper` | `Preparation/Wrapper` | `p11-cp09-preparation.tex#stepP:p11:wr-nu@L248-L248`; `p11-cp09-preparation.tex#stepP:p11:wr-nu@L248-L248` |
| `stepP:p11:wr-kam` | `wr_kam` local in `wrapper` | `Preparation/Wrapper` | `p11-cp09-preparation.tex#stepP:p11:wr-kam@L249-L249`; `p11-cp09-preparation.tex#stepP:p11:wr-kam@L249-L249` |
| `stepP:p11:wr-chain` | `wr_chain` local in `wrapper` | `Preparation/Wrapper` | `p11-cp09-preparation.tex#stepP:p11:wr-chain@L250-L250`; `p11-cp09-preparation.tex#stepP:p11:wr-chain@L250-L250` |
| `stepP:p11:wr-tor` | `wr_tor` local in `wrapper` | `Preparation/Wrapper` | `p11-cp09-preparation.tex#stepP:p11:wr-tor@L251-L251`; `p11-cp09-preparation.tex#stepP:p11:wr-tor@L251-L251` |
| `stepP:p11:wr-meas` | `wr_meas` local in `wrapper` | `Preparation/Wrapper` | `p11-cp09-preparation.tex#stepP:p11:wr-meas@L252-L252`; `p11-cp09-preparation.tex#stepP:p11:wr-meas@L252-L252` |
| `stepP:p11:wr-tube` | `wr_tube` local in `wrapper` | `Preparation/Wrapper` | `p11-cp09-preparation.tex#stepP:p11:wr-tube@L253-L253`; `p11-cp09-preparation.tex#stepP:p11:wr-tube@L253-L253` |
| `bpP:p11:sec-conv#data` | existing `Weighted`/frozen definitions | `Preparation/Basic` | `p11-cp09-preparation.tex#bpP:p11:sec-conv#data@L10-L12`; `-` |
| `bpP:p11:sec-A#data` | `P11Physical`, `P11PatchData`, `p11PatchData`; Part10 port | `Preparation/Working` | `p11-cp09-preparation.tex#bpP:p11:sec-A#data@L42-L44`; `-` |
| `bpP:p11:sec-C#data` | `p11K1`, `p11Alpha1`, `p11s1`, `p11d1`, `p11eta1` | `Preparation/Fast` | `p11-cp09-preparation.tex#bpP:p11:sec-C#data@L96-L100`; `-` |
| `bpP:p11:sec-D#data` | `p11K2`, `p11s2`, `P11SlowData` | `Preparation/Slow` | `p11-cp09-preparation.tex#bpP:p11:sec-D#data@L145-L153`; `-` |
| `bpP:p11:sec-E#data` | `p11Rescale`, `p11PreparedBox`, `P11PreparedData` | `Preparation/Prepared` | `p11-cp09-preparation.tex#bpP:p11:sec-E#data@L189-L194`; `-` |
| `bpP:p11:e4` | `e4` | `Preparation/LogBounds` | `p11-cp09-preparation.tex#bpP:p11:e4@L19-L19`; `-` |
| `bpP:p11:e5` | `e5` | `Preparation/PolarAverage` | `p11-cp09-preparation.tex#bpP:p11:e5@L20-L20`; `-` |
| `bpP:p11a:f-rolle` | `Lagrange.interpolate`, iterated Rolle helper | `WeakMeasure/DividedDifference` | `p11a1-weak-measure.tex#bpP:p11a:f-rolle@L31-L31`; `-` |
| `bpP:p11a:f-meas` | Lebesgue continuity, determinant image, Tonelli helpers | `WeakMeasure/MeasureTools` | `p11a1-weak-measure.tex#bpP:p11a:f-meas@L32-L32`; `-` |
| `bpP:p11a:f-mvt` | Mathlib mean-value inequality and `iteratedFDeriv` line chain rule | `WeakMeasure/Basic` | `p11a1-weak-measure.tex#bpP:p11a:f-mvt@L33-L33`; `-` |
| `bpP:p11a:f-orth` | Householder completion helper on Pi vectors | `WeakMeasure/BallSublevel` | `p11a1-weak-measure.tex#bpP:p11a:f-orth@L34-L34`; `-` |
| `bpP:p11a:f-leib` | Mathlib iterated derivative product formula / finite subset expansion | `WeakMeasure/Stability` | `p11a1-weak-measure.tex#bpP:p11a:f-leib@L36-L36`; `-` |
| `bpP:p11a:conv#data` | `p11euclid`, `p11dg`, `p11op`, `p11thick`, `p11JetBound` | `WeakMeasure/Basic` | `p11a1-weak-measure.tex#bpP:p11a:conv#data@L17-L25`; `-` |
| `bpP:p11a:index-def` | `index_def`, `p11Index`, `p11Amount` | `WeakMeasure/Basic` | `p11a1-weak-measure.tex#bpP:p11a:index-def@L41-L48`; `-` |
| `bpP:p11a:stability` | `stability` | `WeakMeasure/Stability` | `p11a1-weak-measure.tex#bpP:p11a:stability@L58-L65`; `p11a1-weak-measure.tex#bpP:p11a:stability@L66-L71` |
| `stepP:p11a:st-1` | `st_1` local in `stability` | `WeakMeasure/Stability` | `p11a1-weak-measure.tex#stepP:p11a:st-1@L68-L68`; `p11a1-weak-measure.tex#stepP:p11a:st-1@L68-L68` |
| `stepP:p11a:st-2` | `st_2` local in `stability` | `WeakMeasure/Stability` | `p11a1-weak-measure.tex#stepP:p11a:st-2@L69-L69`; `p11a1-weak-measure.tex#stepP:p11a:st-2@L69-L69` |
| `stepP:p11a:st-amount` | `st_amount` local in `stability` | `WeakMeasure/Stability` | `p11a1-weak-measure.tex#stepP:p11a:st-amount@L70-L70`; `p11a1-weak-measure.tex#stepP:p11a:st-amount@L70-L70` |
| `bpP:p11a:M-bound` | `M_bound` | `WeakMeasure/Stability` | `p11a1-weak-measure.tex#bpP:p11a:M-bound@L73-L75`; `p11a1-weak-measure.tex#bpP:p11a:M-bound@L76-L78` |
| `bpP:p11a:divided-difference` | `divided_difference` | `WeakMeasure/DividedDifference` | `p11a1-weak-measure.tex#bpP:p11a:divided-difference@L84-L87`; `p11a1-weak-measure.tex#bpP:p11a:divided-difference@L88-L91` |
| `stepP:p11a:dd-interp` | `dd_interp` local in `divided_difference` | `WeakMeasure/DividedDifference` | `p11a1-weak-measure.tex#stepP:p11a:dd-interp@L89-L89`; `p11a1-weak-measure.tex#stepP:p11a:dd-interp@L89-L89` |
| `stepP:p11a:dd-rolle` | `dd_rolle` local in `divided_difference` | `WeakMeasure/DividedDifference` | `p11a1-weak-measure.tex#stepP:p11a:dd-rolle@L90-L90`; `p11a1-weak-measure.tex#stepP:p11a:dd-rolle@L90-L90` |
| `bpP:p11a:scalar-sublevel` | `scalar_sublevel` | `WeakMeasure/ScalarSublevel` | `p11a1-weak-measure.tex#bpP:p11a:scalar-sublevel@L93-L97`; `p11a1-weak-measure.tex#bpP:p11a:scalar-sublevel@L98-L106` |
| `stepP:p11a:ss-phi` | `ss_phi` local in `scalar_sublevel` | `WeakMeasure/ScalarSublevel` | `p11a1-weak-measure.tex#stepP:p11a:ss-phi@L100-L100`; `p11a1-weak-measure.tex#stepP:p11a:ss-phi@L100-L100` |
| `stepP:p11a:ss-nodes` | `ss_nodes` local in `scalar_sublevel` | `WeakMeasure/ScalarSublevel` | `p11a1-weak-measure.tex#stepP:p11a:ss-nodes@L101-L103`; `p11a1-weak-measure.tex#stepP:p11a:ss-nodes@L101-L103` |
| `stepP:p11a:ss-gaps` | `ss_gaps` local in `scalar_sublevel` | `WeakMeasure/ScalarSublevel` | `p11a1-weak-measure.tex#stepP:p11a:ss-gaps@L104-L104`; `p11a1-weak-measure.tex#stepP:p11a:ss-gaps@L104-L104` |
| `stepP:p11a:ss-dd` | `ss_dd` local in `scalar_sublevel` | `WeakMeasure/ScalarSublevel` | `p11a1-weak-measure.tex#stepP:p11a:ss-dd@L105-L105`; `p11a1-weak-measure.tex#stepP:p11a:ss-dd@L105-L105` |
| `bpP:p11a:ball-sublevel` | `ball_sublevel` | `WeakMeasure/BallSublevel` | `p11a1-weak-measure.tex#bpP:p11a:ball-sublevel@L108-L112`; `p11a1-weak-measure.tex#bpP:p11a:ball-sublevel@L113-L117` |
| `stepP:p11a:bs-rot` | `bs_rot` local in `ball_sublevel` | `WeakMeasure/BallSublevel` | `p11a1-weak-measure.tex#stepP:p11a:bs-rot@L114-L114`; `p11a1-weak-measure.tex#stepP:p11a:bs-rot@L114-L114` |
| `stepP:p11a:bs-sections` | `bs_sections` local in `ball_sublevel` | `WeakMeasure/BallSublevel` | `p11a1-weak-measure.tex#stepP:p11a:bs-sections@L115-L115`; `p11a1-weak-measure.tex#stepP:p11a:bs-sections@L115-L115` |
| `stepP:p11a:bs-tonelli` | `bs_tonelli` local in `ball_sublevel` | `WeakMeasure/BallSublevel` | `p11a1-weak-measure.tex#stepP:p11a:bs-tonelli@L116-L116`; `p11a1-weak-measure.tex#stepP:p11a:bs-tonelli@L116-L116` |
| `bpP:p11a:sublevel` | `sublevel` | `WeakMeasure/Sublevel` | `p11a1-weak-measure.tex#bpP:p11a:sublevel@L119-L130`; `p11a1-weak-measure.tex#bpP:p11a:sublevel@L131-L141` |
| `bpP:p11a:sublevel#kappa` | local `kappa := Nat.ceil ((M/beta)*(4+v⁻¹)*sqrt(N)*d)` | `WeakMeasure/Sublevel` | `p11a1-weak-measure.tex#bpP:p11a:sublevel#kappa@L132-L134`; `p11a1-weak-measure.tex#bpP:p11a:sublevel#kappa@L132-L134` |
| `stepP:p11a:sl-cover` | `sl_cover` local in `sublevel` | `WeakMeasure/Sublevel` | `p11a1-weak-measure.tex#stepP:p11a:sl-cover@L135-L135`; `p11a1-weak-measure.tex#stepP:p11a:sl-cover@L135-L135` |
| `stepP:p11a:sl-lower` | `sl_lower` local in `sublevel` | `WeakMeasure/Sublevel` | `p11a1-weak-measure.tex#stepP:p11a:sl-lower@L136-L138`; `p11a1-weak-measure.tex#stepP:p11a:sl-lower@L136-L138` |
| `stepP:p11a:sl-ball` | `sl_ball` local in `sublevel` | `WeakMeasure/Sublevel` | `p11a1-weak-measure.tex#stepP:p11a:sl-ball@L139-L139`; `p11a1-weak-measure.tex#stepP:p11a:sl-ball@L139-L139` |
| `stepP:p11a:sl-sum` | `sl_sum` local in `sublevel` | `WeakMeasure/Sublevel` | `p11a1-weak-measure.tex#stepP:p11a:sl-sum@L140-L140`; `p11a1-weak-measure.tex#stepP:p11a:sl-sum@L140-L140` |
| `bpP:p11a:diophantine-measure` | `diophantine_measure` | `WeakMeasure/Diophantine` | `p11a1-weak-measure.tex#bpP:p11a:diophantine-measure@L149-L164`; `p11a1-weak-measure.tex#bpP:p11a:diophantine-measure@L165-L170` |
| `stepP:p11a:dm-compact` | `dm_compact` local in `diophantine_measure` | `WeakMeasure/Diophantine` | `p11a1-weak-measure.tex#stepP:p11a:dm-compact@L166-L166`; `p11a1-weak-measure.tex#stepP:p11a:dm-compact@L166-L166` |
| `stepP:p11a:dm-union` | `dm_union` local in `diophantine_measure` | `WeakMeasure/Diophantine` | `p11a1-weak-measure.tex#stepP:p11a:dm-union@L167-L167`; `p11a1-weak-measure.tex#stepP:p11a:dm-union@L167-L167` |
| `stepP:p11a:dm-onek` | `dm_onek` local in `diophantine_measure` | `WeakMeasure/Diophantine` | `p11a1-weak-measure.tex#stepP:p11a:dm-onek@L168-L168`; `p11a1-weak-measure.tex#stepP:p11a:dm-onek@L168-L168` |
| `stepP:p11a:dm-sum` | `dm_sum` local in `diophantine_measure` | `WeakMeasure/Diophantine` | `p11a1-weak-measure.tex#stepP:p11a:dm-sum@L169-L169`; `p11a1-weak-measure.tex#stepP:p11a:dm-sum@L169-L169` |
| `bpP:p11a:power-law` | `power_law` | `WeakMeasure/PowerLaw` | `p11a1-weak-measure.tex#bpP:p11a:power-law@L172-L181`; `p11a1-weak-measure.tex#bpP:p11a:power-law@L182-L186` |
| `stepP:p11a:pl-profile` | `pl_profile` local in `power_law` | `WeakMeasure/PowerLaw` | `p11a1-weak-measure.tex#stepP:p11a:pl-profile@L183-L183`; `p11a1-weak-measure.tex#stepP:p11a:pl-profile@L183-L183` |
| `stepP:p11a:pl-sum` | `pl_sum` local in `power_law` | `WeakMeasure/PowerLaw` | `p11a1-weak-measure.tex#stepP:p11a:pl-sum@L184-L184`; `p11a1-weak-measure.tex#stepP:p11a:pl-sum@L184-L184` |
| `stepP:p11a:pl-conc` | `pl_conc` local in `power_law` | `WeakMeasure/PowerLaw` | `p11a1-weak-measure.tex#stepP:p11a:pl-conc@L185-L185`; `p11a1-weak-measure.tex#stepP:p11a:pl-conc@L185-L185` |
| `bpP:p11a:limit-bridge` | `limit_bridge` | `WeakMeasure/Bridge` | `p11a1-weak-measure.tex#bpP:p11a:limit-bridge@L188-L192`; `p11a1-weak-measure.tex#bpP:p11a:limit-bridge@L193-L195` |
| `bpP:p11a:c2-conv#data` | existing `Phase`, CLM operator norm, `actionNbhd` | `MaximalStep/Basic` | `p11a2-cutoff-step.tex#bpP:p11a:c2-conv#data@L22-L22`; `-` |
| `bpP:p11a:c2-conv#bracket` | existing `Canonical.poissonBracket`, frozen field | `MaximalStep/Basic` | `p11a2-cutoff-step.tex#bpP:p11a:c2-conv#bracket@L28-L28`; `-` |
| `bpP:p11a:domain-def` | `domain_def`, `p11Admissible`, `p11Cut`, `p11Bound` | `MaximalStep/Basic` | `p11a2-cutoff-step.tex#bpP:p11a:domain-def@L23-L27`; `-` |
| `bpP:p11a:x-cauchy` | Cauchy coefficient and mixed-polydisc helper | `MaximalStep/Parameter` | `p11a2-cutoff-step.tex#bpP:p11a:x-cauchy@L32-L32`; `-` |
| `bpP:p11a:x-duality` | `modeSize`, `norm_character_le`, finite Holder helper | `MaximalStep/Divisor` | `p11a2-cutoff-step.tex#bpP:p11a:x-duality@L33-L33`; `-` |
| `bpP:p11a:x-ode` | linear ODE and Gronwall; nonlinear suppliers remain separate | `MaximalStep/RealFlow` | `p11a2-cutoff-step.tex#bpP:p11a:x-ode@L34-L34`; `-` |
| `bpP:p11a:fourier-cutoff` | `fourier_cutoff` | `MaximalStep/FourierCutoff` | `p11a2-cutoff-step.tex#bpP:p11a:fourier-cutoff@L42-L53`; `p11a2-cutoff-step.tex#bpP:p11a:fourier-cutoff@L54-L68` |
| `stepP:p11a:fc-const` | `fc_const` local in `fourier_cutoff` | `MaximalStep/FourierCutoff` | `p11a2-cutoff-step.tex#stepP:p11a:fc-const@L55-L55`; `p11a2-cutoff-step.tex#stepP:p11a:fc-const@L55-L55` |
| `stepP:p11a:fc-decay` | `fc_decay` local in `fourier_cutoff` | `MaximalStep/FourierCutoff` | `p11a2-cutoff-step.tex#stepP:p11a:fc-decay@L57-L57`; `p11a2-cutoff-step.tex#stepP:p11a:fc-decay@L57-L57` |
| `stepP:p11a:fc-tail` | `fc_tail` local in `fourier_cutoff` | `MaximalStep/FourierCutoff` | `p11a2-cutoff-step.tex#stepP:p11a:fc-tail@L59-L60`; `p11a2-cutoff-step.tex#stepP:p11a:fc-tail@L59-L60` |
| `stepP:p11a:fc-count` | `fc_count` local in `fourier_cutoff` | `MaximalStep/FourierCutoff` | `p11a2-cutoff-step.tex#stepP:p11a:fc-count@L62-L63`; `p11a2-cutoff-step.tex#stepP:p11a:fc-count@L62-L63` |
| `stepP:p11a:fc-poly` | `fc_poly` local in `fourier_cutoff` | `MaximalStep/FourierCutoff` | `p11a2-cutoff-step.tex#stepP:p11a:fc-poly@L65-L65`; `p11a2-cutoff-step.tex#stepP:p11a:fc-poly@L65-L65` |
| `stepP:p11a:fc-assemble` | `fc_assemble` local in `fourier_cutoff` | `MaximalStep/FourierCutoff` | `p11a2-cutoff-step.tex#stepP:p11a:fc-assemble@L67-L67`; `p11a2-cutoff-step.tex#stepP:p11a:fc-assemble@L67-L67` |
| `bpP:p11a:loss-choice` | `loss_choice` | `MaximalStep/Loss` | `p11a2-cutoff-step.tex#bpP:p11a:loss-choice@L70-L75`; `p11a2-cutoff-step.tex#bpP:p11a:loss-choice@L76-L82` |
| `stepP:p11a:lc-exponent` | `lc_exponent` local in `loss_choice` | `MaximalStep/Loss` | `p11a2-cutoff-step.tex#stepP:p11a:lc-exponent@L77-L77`; `p11a2-cutoff-step.tex#stepP:p11a:lc-exponent@L77-L77` |
| `stepP:p11a:lc-estimate` | `lc_estimate` local in `loss_choice` | `MaximalStep/Loss` | `p11a2-cutoff-step.tex#stepP:p11a:lc-estimate@L79-L79`; `p11a2-cutoff-step.tex#stepP:p11a:lc-estimate@L79-L79` |
| `stepP:p11a:lc-mono` | `lc_mono` local in `loss_choice` | `MaximalStep/Loss` | `p11a2-cutoff-step.tex#stepP:p11a:lc-mono@L81-L81`; `p11a2-cutoff-step.tex#stepP:p11a:lc-mono@L81-L81` |
| `bpP:p11a:loss-sum` | `loss_sum` | `MaximalStep/Loss` | `p11a2-cutoff-step.tex#bpP:p11a:loss-sum@L84-L89`; `p11a2-cutoff-step.tex#bpP:p11a:loss-sum@L90-L92` |
| `bpP:p11a:taylor-cutoff` | `taylor_cutoff` | `MaximalStep/Taylor` | `p11a2-cutoff-step.tex#bpP:p11a:taylor-cutoff@L97-L104`; `p11a2-cutoff-step.tex#bpP:p11a:taylor-cutoff@L105-L111` |
| `stepP:p11a:tc-line` | `tc_line` local in `taylor_cutoff` | `MaximalStep/Taylor` | `p11a2-cutoff-step.tex#stepP:p11a:tc-line@L106-L106`; `p11a2-cutoff-step.tex#stepP:p11a:tc-line@L106-L106` |
| `stepP:p11a:tc-a` | `tc_a` local in `taylor_cutoff` | `MaximalStep/Taylor` | `p11a2-cutoff-step.tex#stepP:p11a:tc-a@L108-L108`; `p11a2-cutoff-step.tex#stepP:p11a:tc-a@L108-L108` |
| `stepP:p11a:tc-b` | `tc_b` local in `taylor_cutoff` | `MaximalStep/Taylor` | `p11a2-cutoff-step.tex#stepP:p11a:tc-b@L110-L110`; `p11a2-cutoff-step.tex#stepP:p11a:tc-b@L110-L110` |
| `bpP:p11a:cutoff` | `cutoff` | `MaximalStep/Cutoff` | `p11a2-cutoff-step.tex#bpP:p11a:cutoff@L113-L124`; `p11a2-cutoff-step.tex#bpP:p11a:cutoff@L125-L133` |
| `stepP:p11a:cu-coeff` | `cu_coeff` local in `cutoff` | `MaximalStep/Cutoff` | `p11a2-cutoff-step.tex#stepP:p11a:cu-coeff@L126-L126`; `p11a2-cutoff-step.tex#stepP:p11a:cu-coeff@L126-L126` |
| `stepP:p11a:cu-a` | `cu_a` local in `cutoff` | `MaximalStep/Cutoff` | `p11a2-cutoff-step.tex#stepP:p11a:cu-a@L128-L128`; `p11a2-cutoff-step.tex#stepP:p11a:cu-a@L128-L128` |
| `stepP:p11a:cu-b` | `cu_b` local in `cutoff` | `MaximalStep/Cutoff` | `p11a2-cutoff-step.tex#stepP:p11a:cu-b@L130-L130`; `p11a2-cutoff-step.tex#stepP:p11a:cu-b@L130-L130` |
| `stepP:p11a:cu-c` | `cu_c` local in `cutoff` | `MaximalStep/Cutoff` | `p11a2-cutoff-step.tex#stepP:p11a:cu-c@L132-L132`; `p11a2-cutoff-step.tex#stepP:p11a:cu-c@L132-L132` |
| `bpP:p11a:param-cauchy` | `param_cauchy` | `MaximalStep/Parameter` | `p11a2-cutoff-step.tex#bpP:p11a:param-cauchy@L138-L141`; `p11a2-cutoff-step.tex#bpP:p11a:param-cauchy@L142-L146` |
| `stepP:p11a:pc-poly` | `pc_poly` local in `param_cauchy` | `MaximalStep/Parameter` | `p11a2-cutoff-step.tex#stepP:p11a:pc-poly@L143-L143`; `p11a2-cutoff-step.tex#stepP:p11a:pc-poly@L143-L143` |
| `stepP:p11a:pc-iter` | `pc_iter` local in `param_cauchy` | `MaximalStep/Parameter` | `p11a2-cutoff-step.tex#stepP:p11a:pc-iter@L145-L145`; `p11a2-cutoff-step.tex#stepP:p11a:pc-iter@L145-L145` |
| `bpP:p11a:divisor-perturb` | `divisor_perturb` | `MaximalStep/Divisor` | `p11a2-cutoff-step.tex#bpP:p11a:divisor-perturb@L157-L162`; `p11a2-cutoff-step.tex#bpP:p11a:divisor-perturb@L163-L165` |
| `bpP:p11a:sec-hom#lambda` | `p11Lambda`, `p11_lambda_spec` | `MaximalStep/Constants` | `p11a2-cutoff-step.tex#bpP:p11a:sec-hom#lambda@L170-L170`; `-` |
| `bpP:p11a:homological-maximal` | `homological_maximal` | `MaximalStep/Homological` | `p11a2-cutoff-step.tex#bpP:p11a:homological-maximal@L172-L185`; `p11a2-cutoff-step.tex#bpP:p11a:homological-maximal@L186-L198` |
| `stepP:p11a:hm-div` | `hm_div` local in `homological_maximal` | `MaximalStep/Homological` | `p11a2-cutoff-step.tex#stepP:p11a:hm-div@L187-L187`; `p11a2-cutoff-step.tex#stepP:p11a:hm-div@L187-L187` |
| `stepP:p11a:hm-coeff` | `hm_coeff` local in `homological_maximal` | `MaximalStep/Homological` | `p11a2-cutoff-step.tex#stepP:p11a:hm-coeff@L189-L189`; `p11a2-cutoff-step.tex#stepP:p11a:hm-coeff@L189-L189` |
| `stepP:p11a:hm-a` | `hm_a` local in `homological_maximal` | `MaximalStep/Homological` | `p11a2-cutoff-step.tex#stepP:p11a:hm-a@L191-L191`; `p11a2-cutoff-step.tex#stepP:p11a:hm-a@L191-L191` |
| `stepP:p11a:hm-bc` | `hm_bc` local in `homological_maximal` | `MaximalStep/Homological` | `p11a2-cutoff-step.tex#stepP:p11a:hm-bc@L193-L193`; `p11a2-cutoff-step.tex#stepP:p11a:hm-bc@L193-L193` |
| `stepP:p11a:hm-d` | `hm_d` local in `homological_maximal` | `MaximalStep/Homological` | `p11a2-cutoff-step.tex#stepP:p11a:hm-d@L195-L195`; `p11a2-cutoff-step.tex#stepP:p11a:hm-d@L195-L195` |
| `stepP:p11a:hm-bracket` | `hm_bracket` local in `homological_maximal` | `MaximalStep/Homological` | `p11a2-cutoff-step.tex#stepP:p11a:hm-bracket@L197-L197`; `p11a2-cutoff-step.tex#stepP:p11a:hm-bracket@L197-L197` |
| `bpP:p11a:affine-flow` | `affine_flow` | `MaximalStep/AffineFlow` | `p11a2-cutoff-step.tex#bpP:p11a:affine-flow@L203-L216`; `p11a2-cutoff-step.tex#bpP:p11a:affine-flow@L217-L227` |
| `stepP:p11a:af-field` | `af_field` local in `affine_flow` | `MaximalStep/AffineFlow` | `p11a2-cutoff-step.tex#stepP:p11a:af-field@L218-L218`; `p11a2-cutoff-step.tex#stepP:p11a:af-field@L218-L218` |
| `stepP:p11a:af-flow` | `af_flow` local in `affine_flow` | `MaximalStep/AffineFlow` | `p11a2-cutoff-step.tex#stepP:p11a:af-flow@L220-L220`; `p11a2-cutoff-step.tex#stepP:p11a:af-flow@L220-L220` |
| `stepP:p11a:af-simple` | `af_simple` local in `affine_flow` | `MaximalStep/AffineFlow` | `p11a2-cutoff-step.tex#stepP:p11a:af-simple@L222-L222`; `p11a2-cutoff-step.tex#stepP:p11a:af-simple@L222-L222` |
| `stepP:p11a:af-deriv` | `af_deriv` local in `affine_flow` | `MaximalStep/AffineFlow` | `p11a2-cutoff-step.tex#stepP:p11a:af-deriv@L224-L224`; `p11a2-cutoff-step.tex#stepP:p11a:af-deriv@L224-L224` |
| `stepP:p11a:af-rest` | `af_rest` local in `affine_flow` | `MaximalStep/AffineFlow` | `p11a2-cutoff-step.tex#stepP:p11a:af-rest@L226-L226`; `p11a2-cutoff-step.tex#stepP:p11a:af-rest@L226-L226` |
| `bpP:p11a:real-lipschitz` | `real_lipschitz` | `MaximalStep/RealFlow` | `p11a2-cutoff-step.tex#bpP:p11a:real-lipschitz@L229-L235`; `p11a2-cutoff-step.tex#bpP:p11a:real-lipschitz@L236-L242` |
| `stepP:p11a:rl-global` | `rl_global` local in `real_lipschitz` | `MaximalStep/RealFlow` | `p11a2-cutoff-step.tex#stepP:p11a:rl-global@L237-L237`; `p11a2-cutoff-step.tex#stepP:p11a:rl-global@L237-L237` |
| `stepP:p11a:rl-deriv` | `rl_deriv` local in `real_lipschitz` | `MaximalStep/RealFlow` | `p11a2-cutoff-step.tex#stepP:p11a:rl-deriv@L239-L239`; `p11a2-cutoff-step.tex#stepP:p11a:rl-deriv@L239-L239` |
| `stepP:p11a:rl-const` | `rl_const` local in `real_lipschitz` | `MaximalStep/RealFlow` | `p11a2-cutoff-step.tex#stepP:p11a:rl-const@L241-L241`; `p11a2-cutoff-step.tex#stepP:p11a:rl-const@L241-L241` |
| `bpP:p11a:canonical-step` | `canonical_step` | `MaximalStep/Step` | `p11a2-cutoff-step.tex#bpP:p11a:canonical-step@L247-L268`; `p11a2-cutoff-step.tex#bpP:p11a:canonical-step@L269-L290` |
| `stepP:p11a:cs-cutoff` | `cs_cutoff` local in `canonical_step` | `MaximalStep/Step` | `p11a2-cutoff-step.tex#stepP:p11a:cs-cutoff@L270-L270`; `p11a2-cutoff-step.tex#stepP:p11a:cs-cutoff@L270-L270` |
| `stepP:p11a:cs-hom` | `cs_hom` local in `canonical_step` | `MaximalStep/Step` | `p11a2-cutoff-step.tex#stepP:p11a:cs-hom@L272-L272`; `p11a2-cutoff-step.tex#stepP:p11a:cs-hom@L272-L272` |
| `stepP:p11a:cs-flow` | `cs_flow` local in `canonical_step` | `MaximalStep/Step` | `p11a2-cutoff-step.tex#stepP:p11a:cs-flow@L274-L274`; `p11a2-cutoff-step.tex#stepP:p11a:cs-flow@L274-L274` |
| `stepP:p11a:cs-taylor` | `cs_taylor` local in `canonical_step` | `MaximalStep/Step` | `p11a2-cutoff-step.tex#stepP:p11a:cs-taylor@L276-L278`; `p11a2-cutoff-step.tex#stepP:p11a:cs-taylor@L276-L278` |
| `stepP:p11a:cs-u` | `cs_u` local in `canonical_step` | `MaximalStep/Step` | `p11a2-cutoff-step.tex#stepP:p11a:cs-u@L280-L280`; `p11a2-cutoff-step.tex#stepP:p11a:cs-u@L280-L280` |
| `stepP:p11a:cs-bracket` | `cs_bracket` local in `canonical_step` | `MaximalStep/Step` | `p11a2-cutoff-step.tex#stepP:p11a:cs-bracket@L282-L283`; `p11a2-cutoff-step.tex#stepP:p11a:cs-bracket@L282-L283` |
| `stepP:p11a:cs-assemble` | `cs_assemble` local in `canonical_step` | `MaximalStep/Step` | `p11a2-cutoff-step.tex#stepP:p11a:cs-assemble@L285-L285`; `p11a2-cutoff-step.tex#stepP:p11a:cs-assemble@L285-L285` |
| `stepP:p11a:cs-lip` | `cs_lip` local in `canonical_step_real` (guarded) | `MaximalStep/Step` | `p11a2-cutoff-step.tex#stepP:p11a:cs-lip@L287-L287`; `p11a2-cutoff-step.tex#stepP:p11a:cs-lip@L287-L287` |
| `stepP:p11a:cs-param` | `cs_param` local in `canonical_step_param` | `MaximalStep/Step` | `p11a2-cutoff-step.tex#stepP:p11a:cs-param@L289-L289`; `p11a2-cutoff-step.tex#stepP:p11a:cs-param@L289-L289` |

### 4.1 Contract registry (literal graph conclusions and direct inputs)

This is a work list for proof authors. A step must prove this conclusion, not merely build successfully.
Imported results named in DEPS are actual lemma applications. Source hypotheses remain at the statement
locator above; the main signatures bundle only those hypotheses. Where an output specification is factored
in Appendix A, the remaining clauses in this registry are required companion lemmas of the same package.

- **`bpP:p11:kam-input`** — (K1) a compact H in K with meas H >= meas K - eps^*; (K2) for b in H real analytic K_b : R^N -> R^N x R^N with K_b(theta + k) = K_b(theta) + (k, 0), D K_b injective, K_b^*(dr^dtheta) = 0, injective modulo Z^N, and (gamma, tau_D)-Diophantine w_b with s -> K_b(theta + s w_b) a solution of X_H; (K3) sup¦u_b¦ <= Delta = Delta(eps_f; d); (K4) (b, theta) -> K_b(theta) injective on H x [0,1)^N, image B Borel, meas B >= 2^{-2N} meas H; (K5) lower budget: with all entries but beta fixed there is c_* > 0 with eps_adm >= c_* beta^{B_0}, B_0 = mu(mu + 1) + 2 (for 0 < beta <= min{1, M}); (K6) displacement power: c_D > 0, kappa_D > 0, a_D >= 0 with Delta <= c_D eps_f^{kappa_D} beta^{-a_D} whenever eps_f <= eps_adm and beta in (0, min{1,M}]
  Inputs: `bpP:p11a:weak-kam-quantitative, bpP:p11a:limit-torus, bpP:p11a:displacement, bpP:p11a:evaluation-bilipschitz, bpP:p11a:adm-budget-beta, bpP:p11a:adm-budget, bpP:p11a:budget, bpP:p11a:index-def, bpP:p11a:sel-data, bpP:p11:sec-conv#data`.
- **`bpP:p11:norm-dict`** — varpi_J is real analytic and R-nondegenerate on 2 pi B^Lambda, and beta_{2, mu bar}(varpi_J, K_J) >= (2 pi)^{-2-mu bar} beta bar =: beta_J > 0
  Inputs: `stepP:p11:nd, bpP:p11:sec-A#data, bpP:p11a:index-def, bpP:p10:rnd-def`.
- **`stepP:p11:nd`** — varpi_J = (2pi)^{-1} varpi tilde(J/2pi), g_2[varpi_J] = (2pi)^{-2} g_2[varpi tilde], D_J^nu = (2pi)^{-nu} D_Lambda^nu, hence max_nu ¦D^nu g_2[varpi_J]¦ >= (2pi)^{-2-mu bar} beta bar; R-nondegeneracy is invariant under positive diagonal rescaling and affine change of variable
  Inputs: `bpP:p11a:index-def, bpP:p10:interface, bpP:p10:rnd, bpP:p10:scaling, bpP:p11:sec-A#data`.
- **`bpP:p11:select`** — for all k in Z^{2n} \ {0}: ¦k . varpi_J(J_0)¦ >= gamma_0 ¦k¦_1^{-tau_0}; in particular omega(J_0) and Omega tilde(J_0) are (gamma_0, tau_0)-Diophantine in Z^n
  Inputs: `stepP:p11:sel-hyp, stepP:p11:sel-gam, stepP:p11:sel-int, bpP:p0:diophantine#IsDiophantine, bpP:p11:sec-A#data`.
- **`stepP:p11:sel-hyp`** — the hypotheses (D1)-(D3) of Corollary bpP:p11a:power-law hold and the exponent condition tau_0 > n mu bar - 1
  Inputs: `bpP:p11a:power-law, bpP:p11:norm-dict, bpP:p11a:M-bound, bpP:p11:sec-A#data`.
- **`stepP:p11:sel-gam`** — meas(K_J \ H_gamma) <= C_Dio gamma^{2/mu bar}; gamma_0 = min{1, gamma_*(eps_0^*)} gives meas H_{gamma_0} >= meas K_J - eps_0^* > 0, H_gamma0 = {b in K_J : ¦k.varpi_J(b)¦ >= gamma_0 ¦k¦_1^{-tau_0} for all k != 0}
  Inputs: `stepP:p11:sel-hyp, bpP:p11a:power-law, bpP:p11:sec-A#data`.
- **`stepP:p11:sel-int`** — K_J \ int K_J is the boundary of a rectangle (the coordinatewise increasing map a -> 2 pi Lambda(a) maps the cube K_a to a product of intervals), a null set; hence H_gamma0 meets int K_J; take J_0 in it
  Inputs: `stepP:p11:sel-gam, bpP:p11:sec-A#data`.
- **`bpP:p11:holo-chart`** — (a) F holomorphic on T_{2 sigma_F} x J x B_{r_z}, 1-periodic, real, ¦F¦ <= M_F/coth(pi sigma_F)^n, hence wn(F) <= M_F; omega, Omega tilde holomorphic on J with ¦D^j varpi_J¦ <= L (j <= mu bar+1); (b) the extension varrho:D(Lambda_0,r_C/pi)->O(n,C), Lambda_0=J_0/(2pi), is holomorphic, real with values in SO(n) on the real locus, with norm(varrho)<=B_varrho and norm(varrho^T partial_{Lambda_l}varrho)<=B_varrho_prime there for each l; T_1(theta,J,x,y)=(2pi theta,J/(2pi),x,y); O_c is the real domain J in D(J_0,2r_C), norm(z)<r_z; Psi_c = Psi^(n) o Phi_rho^{-1} o T_1 is a symplectic 1-chart on O_c with values in the collision-free domain and H_fix(Psi_c(theta, J, z)) = h tilde(J) + eps F(theta, J, z) for all real eps; symplectic form dJ^dtheta + dy^dx; (c) Psi_c satisfies (Q1)-(Q2) of bpP:p1:torus-transport for iota_k = ((k,0),0), sigma_k = 0; (d) F_0 = theta-average is holomorphic on J x B_{r_z} and F_0 = C(J) + sum Omega_j(J)(x_j^2 + y_j^2)/2 + R_4, ¦R_4¦ <= M_F(¦z¦/r_z)^4, C(J) = C_0(a(J/2pi)), Omega_j = 2 pi Omega tilde_j
  Inputs: `stepP:p11:hc-rot, stepP:p11:hc-lift, stepP:p11:hc-strip, stepP:p11:hc-F, stepP:p11:hc-id, stepP:p11:hc-lat, stepP:p11:hc-mean, bpP:p11:select, bpP:p11:sec-A#data, bpP:p11:sec-conv#data, bpP:p7:product-chart, bpP:p9:lift, bpP:p9:local-analytic, bpP:p6:domain, bpP:p0:hamsymp#symplecticForm, bpP:p0:fixham#fixedHamiltonian, bpP:p1:torus-transport, bpP:p7:product-def, bpP:p8:coeffs`.
- **`stepP:p11:hc-rot`** — sigma_j, rho real analytic on D_R(Lambda_0, t_1), rho extends holomorphically to D(Lambda_0, t_2) with values in O(n, C) (SO(n) at real points); r_C <= min{pi t_2/2, pi rho_*/8}; B_rho = sup ¦rho¦, B_rho prime = max_l sup ¦rho^T d_l rho¦ on D(Lambda_0, r_C/pi), enlarged to >= 1
  Inputs: `bpP:p10:interface, bpP:p9:local-analytic, bpP:p11:select, bpP:p11:sec-A#data`.
- **`stepP:p11:hc-lift`** — Phi_rho^{-1}(lambda tilde, Lambda, xi tilde, eta tilde) = (lambda tilde + H_rho, Lambda, rho xi tilde, rho eta tilde) holds on the complex domain with H_rho holomorphic; ¦rho x¦, ¦rho y¦ <= B_rho r_z, ¦H_rho¦ <= n B_rho prime r_z^2; r_z <= min{1, rho_*/(8 B_rho), (pi sigma prime/(2 n B_rho prime))^{1/2}}
  Inputs: `bpP:p9:lift, stepP:p11:hc-rot, stepP:p11:hc-strip, bpP:p11:sec-A#data`.
- **`stepP:p11:hc-strip`** — exists sigma prime in (0,1/4] with Re s_ij >= (1/4)(a_j - a_i)^2 for ¦Im lambda¦ <= 2 pi sigma prime and w prime in N(rho_*/2); on this set f^_fix = -G sum m_i m_j s_ij^{-1/2} (principal root) is holomorphic and bounded by c(m, G, a)
  Inputs: `bpP:p8:perturbation-analytic, bpP:p7:holomorphic, bpP:p12:f-unif, bpP:p11:sec-A#data, I:bpI:p7:x-hol`.
- **`stepP:p11:hc-F`** — F := f^_fix o Phi_rho^{-1} o T_1 is holomorphic on T_{2 sigma_F} x J x B_{r_z}, 1-periodic in theta, real at real points, sup F = M_infty, M_F = max{1, coth(pi sigma_F)^n M_infty}, wn(F) <= M_F; L bounds varpi_J and its derivatives up to order mu bar + 1 on J
  Inputs: `stepP:p11:hc-lift, stepP:p11:hc-strip, stepP:p11:hc-rot, N:bpN:p4:sup-weighted, N:bpN:p4:general-cauchy, bpP:p11:sec-conv#data, bpP:p11:sec-A#data`.
- **`stepP:p11:hc-id`** — Psi_c maps real points into Psi^(n)(N_R(rho_*) x R^n) in W; H_fix o Psi^(n) = h + eps f^_fix, Phi_rho preserves Lambda, T_1: J -> Lambda = J/2pi, so H_fix(Psi_c) = h tilde(J) + eps F; Psi_c is symplectic and real analytic
  Inputs: `bpP:p8:perturbation-analytic, bpP:p7:product-chart, bpP:p9:lift, bpP:p1:typical, bpP:p1:hol-chart, stepP:p11:hc-F, bpP:p0:fixham#fixedHamiltonian, bpP:p11:sec-A#data, bpP:p7:product-def`.
- **`stepP:p11:hc-lat`** — T_1(theta + k, .) = T_1 + (2 pi k, 0, 0, 0); Phi_rho^{-1} commutes with lambda-shifts; Psi^(n) is invariant under 2 pi Z^n-shifts of lambda with injectivity modulo them; T_1, Phi_rho injective: Psi_c satisfies (Q1)-(Q2) with sigma_k = 0
  Inputs: `bpP:p7:product-chart, bpP:p9:diagonalize, bpP:p9:lift, bpP:p7:product-def`.
- **`stepP:p11:hc-mean`** — F_0 = theta-average of F is holomorphic, equals S_fix(Lambda, rho x, rho y) = C_0 + sum Omega_j R_j + O(¦(x,y)¦^4) and R_4 = F_0 - C - sum Omega_j R_j has vanishing jet to order 3, so ¦R_4¦ <= sup¦R_4¦ (¦z¦/r_z)^4 (Schwarz lemma on lines), enlarging M_F
  Inputs: `N:bpN:p4:coefficients, bpP:p9:diagonalize, bpP:p8:evenness, stepP:p11:hc-F, N:bpN:p4:general-cauchy, stepP:p11:hc-rot, bpP:p11:sec-conv#data, bpP:p8:coeffs`.
- **`bpP:p11:total-chart`** — Theta hat = (theta, J, Theta^(1)) is a symplectic 1-chart for dJ^dtheta + d rho tilde^d zeta, real analytic, Z^n-periodic in zeta with injectivity modulo that; Xi_0 = Psi_c o Theta hat satisfies (Q1)-(Q2) of bpP:p1:torus-transport for d = 2n with sigma_k = 0
  Inputs: `stepP:p11:tc-polar, stepP:p11:tc-lat, bpP:p11:holo-chart, bpP:p1:torus-transport`.
- **`stepP:p11:tc-polar`** — Theta hat is a symplectic 1-chart, real analytic, with the stated periodicity and injectivity modulo Z^n
  Inputs: `bpP:p7:lattice, bpP:p1:typical`.
- **`stepP:p11:tc-lat`** — Xi_0(w + iota_k) = Xi_0(w) (Q1, sigma_k = 0) and Xi_0(w prime) = Xi_0(w) implies w prime = w + iota_m (Q2)
  Inputs: `bpP:p11:holo-chart, stepP:p11:tc-polar, bpP:p1:torus-transport`.
- **`bpP:p11:avg-fast`** — (S1) 2^12 (1+n) K_1 eps M_F sigma_F <= alpha_1 d_1 holds and there is a holomorphic injective real symplectic Phi^1_eps : D_1 prime -> D_1 with H o Phi^1 = h tilde + eps G + f_1, H = h tilde + eps F, G = F_0 + eps g bar holomorphic real, sup¦eps g bar¦ <= eta_1(eps) = 400 (1+n) eps M_F^2/(2 pi alpha_1 d_1), wn(f_1) <= (eps M_F)^{nu_1}, and 2pi alpha_1 sigma_F norm(J-J prime)<=3 eps M_F, 2pi alpha_1 s_1 norm(theta-theta prime)<=9 eps M_F, 2pi alpha_1 r_z norm(z-z prime)<=9 eps M_F; eta_1(eps) <= c eps (log 1/eps)^{2 tau_0+1}
  Inputs: `stepP:p11:af-apply, stepP:p11:af-o1, stepP:p11:af-o2, stepP:p11:af-concl, bpP:p11:sec-C#data, bpP:p11:holo-chart, bpP:p11:sec-conv#data`.
- **`stepP:p11:af-apply`** — Proposition bpP:p2:osc-averaging applies with n -> n, m -> n, D = {J_0}, r = s_1, r_p = r_q = r_z, s-bar = 0, s = sigma_F, K = K_1, alpha = alpha_1, h = h tilde, f = eps F, E = eps M_F, b = 1+n, d = d_1, kappa = kappa_1 >= 6 (the symplectic form is the negative of that of Part 2: preserved equivalently)
  Inputs: `bpP:p2:osc-averaging, bpP:p11:holo-chart, bpP:p11:sec-C#data`.
- **`stepP:p11:af-o1`** — (O1): ¦k.omega(J)¦ >= ¦k.omega(J_0)¦ - ¦k¦_1 ¦omega(J) - omega(J_0)¦ >= gamma_0 K_1^{-tau_0} - K_1 L s_1 >= (3/4) gamma_0 K_1^{-tau_0} >= alpha_1
  Inputs: `bpP:p11:select, K:bp:p1:ext-mvt, bpP:p11:sec-C#data, bpP:p11:holo-chart`.
- **`stepP:p11:af-o2`** — (O2) is (S1): K_1 eps M_F sigma_F/(alpha_1 d_1) -> 0 (by the elementary (e4)), eps_1 the largest value with (S1) and kappa_1 >= 6 for all smaller eps
  Inputs: `bpP:p11:sec-C#data, bpP:p11:holo-chart, bpP:p11:e4`.
- **`stepP:p11:af-concl`** — Phi^1_eps and H o Phi^1 = h tilde + g + f_*, g independent of theta, ¦¦g - f^_0¦¦ <= 400 b E^2/(alpha-bar d); put eps^2 g bar = g - eps F_0, f_1 = f_*, ¦¦f_*¦¦ <= e^{-kappa_1/6} E = (eps M_F)^{nu_1}; displacement bounds; the sup bound for eps g bar is sup-weighted (a)
  Inputs: `bpP:p2:osc-averaging, stepP:p11:af-apply, stepP:p11:af-o1, stepP:p11:af-o2, N:bpN:p4:sup-weighted, bpP:p11:sec-C#data, bpP:p11:sec-conv#data`.
- **`bpP:p11:aniso-bracket`** — the bracket estimate ¦¦{u, w}¦¦_{V-rho, s-sigma} <= (nu_theta + nu_I)/(e rho_* sigma) ¦¦u¦¦ ¦¦w¦¦ with nu_theta = sigma/(s_0 - s + sigma), nu_I = rho_*/min_j(r^0_(j) - r_(j) + rho_(j)) <= 1, and the vector field estimate nu(X_phi) <= ¦¦phi¦¦/(rho_* sigma) for nu(a,b)=max{norm(a)/sigma, max_j norm(b_(j))/rho_(j)}
  Inputs: `stepP:p11:ab-der, stepP:p11:ab-prod, bpP:p11:sec-conv#data`.
- **`stepP:p11:ab-der`** — sum_i ¦¦d_{theta_i} u¦¦_{s-sigma} <= ¦¦u¦¦_{s_0}/(e(s_0 - s + sigma)); max_i ¦d_{I_i} w¦ <= ¦¦w¦¦/rho_*; for u the action Cauchy disc has radius >= r^0_(j) - r_(j) + rho_(j)
  Inputs: `N:bpN:p4:cauchy, bpP:p11:sec-conv#data`.
- **`stepP:p11:ab-prod`** — ¦¦{u, w}¦¦ <= (sum ¦¦d_theta u¦¦) max ¦d_I w¦ + max ¦d_I u¦ (sum ¦¦d_theta w¦¦) <= ¦¦u¦¦¦¦w¦¦/e (1/((s_0 - s + sigma) rho_*) + 1/(min_j(...) sigma)); and the field bound by ¦¦phi¦¦/(rho_* sigma)
  Inputs: `N:bpN:p4:algebra, stepP:p11:ab-der, bpP:p11:sec-conv#data`.
- **`bpP:p11:aniso-avg`** — conclusions (a)-(d) of Proposition bpP:p2:nfb hold with D_r replaced by V, the domain by T_{s/6} x V/2, s-bar = 0, alpha-bar_2 r by alpha-bar_2 r_*, and in addition wn(g - f^_0) <= 130 E^2/(alpha-bar_2 r_* s), g = g(I prime) real, H o Psi = h + g + f_*, wn(f_*) <= e^{-kappa/6} E
  Inputs: `stepP:p11:aa-same, stepP:p11:aa-quad, bpP:p2:nfb, bpP:p11:sec-conv#data`.
- **`stepP:p11:aa-same`** — the proof of Proposition p2:nfb goes through with the replacements (R1) bracket by aniso-bracket, (R2) the N-estimates by the same statements for the scaled norm nu, (R3) alpha-bar rho sigma by alpha-bar rho_* sigma with blockwise losses (step 0: rho_(j),0 = r_(j)/8, sigma_0 = s/6; steps i >= 1: rho_(j) = r_(j)/(8N prime)); the inductive inequalities and displacement bounds are unchanged with r -> r_*
  Inputs: `bpP:p2:nfb, bpP:p2:direct, bpP:p2:split, bpP:p11:aniso-bracket, bpP:p2:osc-iter, stepP:p2:oi-transfer, stepP:p2:nfb-ind, stepP:p2:nfb-disp, N:bpN:p5:flow, N:bpN:p5:composition, N:bpN:p5:transform, N:bpN:p5:canonical-map, N:bpN:p6:homological, N:bpN:p6:iterative, N:bpN:p6:telescope, N:bpN:p6:setting, bpP:p11:sec-conv#data`.
- **`stepP:p11:aa-quad`** — eps_1 = ¦¦f_1¦¦ <= (8/7)(1 + 2/e) y_0 E <= 96 E^2/(alpha-bar_2 r_* s) and ¦¦g - g_0¦¦ <= (4/3) eps_1 <= 128 E^2/(alpha-bar_2 r_* s); in Case B g = f^_0; hence wn(g - f^_0) <= 130 E^2/(alpha-bar_2 r_* s)
  Inputs: `stepP:p2:nfb-first, stepP:p2:nfb-concl, stepP:p11:aa-same, bpP:p11:sec-conv#data`.
- **`bpP:p11:polar-avg`** — exists holomorphic AG on D x D(0, pi r^2/4) with (a) ¦AG¦ <= 2^{2n} S; (b) for real zeta, Re rho tilde_j > 0, ¦rho tilde_j¦ < pi r^2/4: int G(J, Pi(zeta, rho tilde)) dzeta = AG(J, rho tilde); (c) if Taylor coefficients of degree < k vanish then ¦AG¦ <= 2^{2n} S (4¦rho tilde¦/(pi r^2))^{ceil(k/2)}; (d) A linear, A(C) = C, A((x_j^2 + y_j^2)/2) = rho tilde_j/2 pi
  Inputs: `stepP:p11:pa-taylor, stepP:p11:pa-mono, stepP:p11:pa-series, bpP:p11:total-chart`.
- **`stepP:p11:pa-taylor`** — ¦c_ab(J)¦ <= S r^{-¦a¦-¦b¦} and sum ¦c_ab¦ (r/2)^{¦a¦+¦b¦} <= 2^{2n} S
  Inputs: `N:bpN:p4:general-cauchy, K:bp:p1:holomorphic-analytic`.
- **`stepP:p11:pa-mono`** — x^a y^b o Pi = prod (rho tilde_j/pi)^{(a_j+b_j)/2} sin^{a_j} cos^{b_j}(2 pi zeta_j); its zeta-integral is 0 unless all a_j, b_j are even, then prod m_j (rho tilde_j/pi)^{kappa_j}, ¦m_j¦ <= 1, a polynomial in rho tilde
  Inputs: `bpP:p11:e5, bpP:p11:total-chart`.
- **`stepP:p11:pa-series`** — AG := sum_{a,b even} c_ab m_ab pi^{-¦kappa¦} rho tilde^kappa converges normally, is holomorphic with (a); (b) by termwise integration; (c) only ¦a¦+¦b¦ >= k occurs; (d) is immediate
  Inputs: `stepP:p11:pa-taylor, stepP:p11:pa-mono, bpP:p11:e5, I:bpI:p7:x-weier`.
- **`bpP:p11:avg-slow`** — (a) wn(f_2) <= E_2 = c_2 eps^{5/2}(log 1/eps)^{2 tau_0+1} and G hat_0 = C + sum Omega tilde_j rho tilde_j + Z hat with Z hat holomorphic on D(J_0, s_1/2) x D(0, pi r_z^2/16), for every J-multi-index alpha, ¦d_J^alpha d_rho Z hat¦ <= c_2(eps + eta_1) alpha! (4/s_1)^¦alpha¦ on D(J_0,s_1/4) x D_rho tilde; (b) (B1) with alpha_(1), alpha_(2), K_2 and (B2) E_2 <= alpha_(2) pi eps/(128 K_2); (c) Lemma aniso-avg gives Psi_2 with (H o Phi^1 o Theta hat) o Psi_2 = h_0 + g_2 + f_3, ¦g_2¦ <= c_2 eps^3 (log)^{5 tau_0+2}, wn(f_3) <= eps^{nu_2} E_2; (d) norm(rho tilde-rho tilde prime)<=c_2 eps^(3/2) (log(1/eps))^(3 tau_0+1), norm(J-J prime)<=c_2 eps^(5/2) (log(1/eps))^(3 tau_0+1), and norm(theta-theta prime), norm(zeta-zeta prime)<=c_2 eps^(1/2) (log(1/eps))^(3 tau_0+1)
  Inputs: `stepP:p11:as-osc, stepP:p11:as-nr, stepP:p11:as-b2, stepP:p11:as-concl, bpP:p11:aniso-avg, bpP:p11:avg-fast, bpP:p11:sec-D#data, bpP:p11:sec-conv#data, bpP:p11:sec-C#data`.
- **`stepP:p11:as-osc`** — Z hat := A(R_4 + eps g bar) holomorphic, G hat_0 = C + sum Omega tilde_j rho tilde_j + Z hat on D_rho tilde; derivative bounds of Z hat; sup(G hat - G hat_0) <= c(eps^2 + eta_1 sqrt eps); wn(f_2) <= c_2 eps^{5/2}(log 1/eps)^{2 tau_0+1}
  Inputs: `bpP:p11:polar-avg, bpP:p11:holo-chart, bpP:p11:avg-fast, K:bp:p1:ext-mvt, N:bpN:p4:sup-weighted, N:bpN:p4:general-cauchy, bpP:p11:sec-D#data, bpP:p11:sec-C#data, bpP:p11:sec-conv#data, K:bp:p1:holomorphic-analytic`.
- **`stepP:p11:as-nr`** — (B1) on V_2: pure slow case ¦k.d h_0¦ >= eps(delta_0 - delta_0/8 - delta_0/8) >= alpha_(2), case k_1 != 0 ¦k.d h_0¦ >= delta_0/2 >= alpha_(1); alpha_(2) <= alpha_(1), with delta_0 = gamma_0 K_2^{-tau_0}
  Inputs: `stepP:p11:as-osc, bpP:p11:select, N:bpN:p4:general-cauchy, bpP:p11:holo-chart, bpP:p11:sec-D#data, bpP:p11:e4, bpP:p11:sec-C#data`.
- **`stepP:p11:as-b2`** — (B2): E_2 <= alpha_(2) pi eps/(128 K_2): alpha_(2) pi eps/(128 K_2) = (pi gamma_0/512) eps^2 K_2^{-tau_0-1}, and the ratio of E_2 to this quantity is eps^{1/2} times a power of log; kappa = 2 pi K_2 sigma_3 = 6 nu_2 log(1/eps) >= 6
  Inputs: `stepP:p11:as-osc, bpP:p11:sec-D#data, bpP:p11:e4`.
- **`stepP:p11:as-concl`** — g_2 := g, f_3 := f_*, e^{-kappa/6} = eps^{nu_2}; f^_0 = int f_2 = int f_1 o (id, Pi) of size c eps^3; ¦g_2¦ <= ¦f^_0¦ + 130 E_2^2/(alpha-bar_2 r_* sigma_3) <= c_2 eps^3 (log)^{5 tau_0+2}; displacements 3E_2/(alpha-bar_2 sigma_3), 3E_2/(alpha-bar_1 sigma_3), 9E_2/(alpha-bar_2 r_*)
  Inputs: `bpP:p11:aniso-avg, stepP:p11:as-osc, stepP:p11:as-nr, stepP:p11:as-b2, bpP:p11:avg-fast, bpP:p11:sec-D#data`.
- **`bpP:p11:prepared`** — N_eps, P_eps holomorphic on E, 1-periodic in the angles, real, N_eps depends on (r, rho prime) only, H_2 o A_eps = eps H hat_eps; (a) sup¦P_eps¦ <= eps_f(eps) = c_3 eps^{nu_2+3/2} ell^{2 tau_0+1}; (b) ¦omega hat_eps¦ <= C_1 := 2L+1 and ¦D^2 N_eps¦ <= C_1 on K_eps + 3 theta; (c) for real J with norm(J-J_0)<s_2/4 and rho tilde_j in eps(2pi+(-5/4,5/4)), J-derivatives: ¦d_J^alpha(omega hat^(i) - varpi^(i))¦ <= theta_eps for ¦alpha¦ <= mu bar, in the derivative norm of Definition index-def c(n, mu bar) theta_eps; (d) ¦D^k g_2[omega hat_eps](c, y)¦ <= M_* := 2^{mu bar+1}(2L+1)^2 for k <= mu bar + 1 on K_eps + theta, and ¦¦omega hat_eps¦¦^{mu bar}_dg <= M_0^* := c(n, mu bar)(2L+1) >= 1, independent of eps
  Inputs: `stepP:p11:pr-basic, stepP:p11:pr-a, stepP:p11:pr-in, stepP:p11:pr-b, stepP:p11:pr-c, stepP:p11:pr-d, bpP:p11:sec-E#data, bpP:p11a:index-def`.
- **`stepP:p11:pr-basic`** — H_2 o A_eps = H o (Phi^1 o Theta hat o Psi_2 o A_eps), domain chain A_eps(E) in T_{sigma_3/6} x V_2/2, Psi_2 maps into T_{sigma_3} x V_2, Theta hat into T_{sigma_F/6} x D(J_0, s_2) x B_{r_z/4} in D_1 prime; N_eps, P_eps are holomorphic real functions
  Inputs: `bpP:p11:avg-slow, bpP:p11:avg-fast, bpP:p11:total-chart, bpP:p11:sec-E#data, bpP:p11:sec-D#data, bpP:p11:sec-C#data`.
- **`stepP:p11:pr-a`** — sup¦P_eps¦ <= eps^{-1} sup¦f_3¦ <= eps^{nu_2 + 3/2} c_2 ell^{2 tau_0+1} <= eps_f(eps)
  Inputs: `bpP:p11:avg-slow, N:bpN:p4:sup-weighted, bpP:p11:sec-E#data, bpP:p11:sec-conv#data`.
- **`stepP:p11:pr-in`** — (i) ¦d_J^beta G hat_0¦ <= c M_F beta! (4/s_1)^¦beta¦; (ii) ¦d_J^alpha d_rho Z hat¦ <= c eps ell^{2 tau_0+1+(tau_0+1)¦alpha¦}; (iii) ¦d_J^alpha d_rho^gamma g_2¦ <= c alpha! gamma! eps^{3-¦gamma¦} ell^{5 tau_0+2+(tau_0+1)¦alpha¦}
  Inputs: `stepP:p11:as-osc, bpP:p11:avg-slow, N:bpN:p4:general-cauchy, bpP:p11:sec-C#data, bpP:p11:sec-D#data, bpP:p11:sec-E#data, K:bp:p1:holomorphic-analytic`.
- **`stepP:p11:pr-b`** — ¦omega hat_eps¦ <= 2L+1 and the Hessian entries of N_eps are <= c eps^a ell^b with a >= 1, so ¦D^2 N_eps¦ <= 1 <= C_1
  Inputs: `stepP:p11:pr-in, bpP:p11:holo-chart, bpP:p11:sec-E#data, bpP:p11:e4, N:bpN:p4:general-cauchy`.
- **`stepP:p11:pr-c`** — each of the four contributions to d_J^alpha(omega hat^(i) - varpi^(i)) is <= c eps ell^Q (all exponents <= Q, all powers of eps >= 1); sum gives c_3 eps ell^Q = theta_eps
  Inputs: `stepP:p11:pr-in, bpP:p11:sec-E#data`.
- **`stepP:p11:pr-d`** — ¦D^k g_2[omega hat_eps]¦ <= 2^k M_1^2 with M_1 = ¦¦omega hat_eps¦¦^{mu bar+1}_op <= 2L+1; the main terms have norm <= L, other terms <= c eps ell^b <= 1; the diagonal norm is bounded by c(n, mu bar) times the max-norm operator norm: M_*, M_0^*
  Inputs: `bpP:p11a:M-bound, bpP:p11:holo-chart, stepP:p11:pr-in, bpP:p11a:index-def, bpP:p11:sec-E#data, bpP:p11:e4`.
- **`bpP:p11:amount`** — beta_{2, mu bar}(omega hat_eps, K_eps) >= beta_eps := (1/2) eps^{mu bar+2} beta_J > 0
  Inputs: `stepP:p11:am-norm, stepP:p11:am-dir, stepP:p11:am-scale, bpP:p11:holo-chart, bpP:p11:prepared, bpP:p11:norm-dict, bpP:p11a:index-def, bpP:p11:sec-E#data`.
- **`stepP:p11:am-norm`** — g_2[D omega check](c, .) = ¦Dc¦^2 g_2[omega check](c hat, .), eps <= ¦Dc¦ <= 1, so beta_{2, mu}(D omega check, K) >= eps^2 beta_{2, mu}(omega check, K)
  Inputs: `bpP:p11a:index-def, bpP:p11:sec-E#data`.
- **`stepP:p11:am-dir`** — theta := ¦¦psi_eps - psi¦¦^{mu bar}_{dg, A} <= theta_eps, ¦¦psi¦¦ <= L_1 and beta_{2, mu bar}(psi, A) >= beta_J give beta_{2, mu bar}(psi_eps, A) >= beta_J/2 (n-dimensional amount)
  Inputs: `bpP:p11:prepared, bpP:p11a:stability, bpP:p11:norm-dict, bpP:p11:holo-chart, bpP:p11:select, bpP:p11:sec-E#data`.
- **`stepP:p11:am-scale`** — in the variables (r, rho prime) the nu-th derivative of g_2[omega check_eps](c, .) in direction (a, 0) equals eps^nu D_J^nu g_2[psi_eps](c, J)(a^nu); max_nu eps^nu x_nu >= eps^{mu bar} max x_nu, so beta_{2, mu bar}(omega check_eps, K_eps) >= eps^{mu bar} beta_J/2 and with am-norm beta_{2, mu bar}(omega hat_eps, K_eps) >= eps^{mu bar+2} beta_J/2
  Inputs: `bpP:p11a:index-def, stepP:p11:am-norm, stepP:p11:am-dir, bpP:p11:sec-E#data`.
- **`bpP:p11:forward-tube`** — there is delta_zeta in (0, (1/4) min Lambda_i^*], depending only on (G, m0, m, a, zeta), such that every w in R^{4n} with ¦Lambda_i - Lambda_i^*¦ <= delta_zeta and Gamma_i(w) <= delta_zeta lies in O_n and ¦Psi^(n)(w) - circ(lambda/2pi)¦ < zeta; in particular Psi^(n)(w) in U_zeta
  Inputs: `stepP:p12:ft-cpt, stepP:p12:ft-uc, stepP:p12:ft-cmp, bpP:p7:tube, bpP:p7:product-chart, bpP:p12:f-unif, bpP:p0:circular#circularPoint, bpP:p0:circular#circularTube, bpP:p7:product-def`.
- **`bpP:p11:wrapper`** — there is eps_0 > 0 such that for every eps in (0, eps_0) there is a Borel S_eps in Ph(2n) with 0 < meas S_eps < infinity, S_eps in U_zeta_*, and for every z in S_eps there are w in R^2n, K : R^2n -> Ph(2n), theta_0 with z = K(theta_0), K(R^2n) in S_eps and IsPhysTorus(H_fix, w, K), H_fix = fixedHamiltonian G m0 m eps; order of choice data, patch, (mu bar, beta bar), J_0, gamma_0, r_C, sigma_F, r_z, M_F, L, B_rho, B_rho prime, the fixed part d_* of the KAM datum with B_0, c_*, c_D, kappa_D, a_D, nu_2, eps_0, eps
  Inputs: `stepP:p11:wr-nu, stepP:p11:wr-kam, stepP:p11:wr-chain, stepP:p11:wr-tor, stepP:p11:wr-meas, stepP:p11:wr-tube, bpP:p6:tube-constants, bpP:p11:kam-input, bpP:p11:sec-A#data, bpP:p0:phase#Phase, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:fixham#fixedHamiltonian, bpP:p0:circular#circularTube`.
- **`bpP:p11:data-star`** — H hat_eps is d_eps-admissible for d_eps = (mu bar, beta_eps, K_eps, 1/4, s_*, M_*, M_0^*, C_1, tau_D, 1/2): holomorphy, periodicity, reality (Prop prepared), (A1) Lemma amount, (A2) Prop prepared (d), (A3) (b) with C_1 = 2L+1 >= 3, (A4) (d) with M_0^*; 0 < beta_eps <= min{1, M_*}; all entries except beta_eps = beta_J eps^{mu bar+2}/2 form the eps-independent part d_*; (K5) and (K6) apply with the constants of d_*, and eps_adm(d_eps) >= c_* beta_eps^{B_0}, B_0 = mu bar(mu bar + 1) + 2
  Inputs: `bpP:p11:prepared, bpP:p11:amount, bpP:p11:kam-input, bpP:p11:sec-E#data`.
- **`stepP:p11:wr-nu`** — nu_2 := max{(mu bar + 2) B_0 + 2, ((mu bar + 2) a_D + 1)/kappa_D + 2}; eps_f(eps) <= eps_adm(d_eps) (eps_adm >= c_* (beta_J/2)^{B_0} eps^{(mu bar+2)B_0} >= c prime eps^{nu_2-2}) and Delta <= c_D eps_f^{kappa_D} beta_eps^{-a_D} <= c double prime eps^{1+2 kappa_D} ell^c <= 1/2, hence there is eps_0 <= eps_3 (depending on the data, nu_2 and these constants) with eps_f <= eps_adm, Delta <= 1/2 and the tube inequalities of step wr-tube for all eps in (0, eps_0)
  Inputs: `bpP:p11:kam-input, bpP:p11:prepared, bpP:p11:data-star, bpP:p11:e4`.
- **`stepP:p11:wr-kam`** — Definition kam-input applied to H hat_eps with eps_f = eps_f(eps) gives a compact H_eps in K_eps with meas >= 1/2 and for b in H_eps maps K_b = (theta + u^theta_b, zeta + u^zeta_b; b_r + u^r_b, b_rho prime + u^{rho prime}_b) with ¦u_b¦ <= Delta <= 1/2; hence the actions of every real point of every torus satisfy ¦r¦ <= 1, ¦rho prime¦ <= 1 < pi/2
  Inputs: `bpP:p11:kam-input, bpP:p11:data-star, stepP:p11:wr-nu, bpP:p11:prepared, bpP:p11:sec-E#data`.
- **`stepP:p11:wr-chain`** — Xi_eps = Psi_c o Phi^1_eps o Theta hat o Psi_2 o A_eps is defined and real analytic on R_eps, an eps-chart in the sense of Definition bpP:p1:chart with lattice properties (Q1)-(Q2) (sigma_k = 0, iota_k = ((k,0),0)) factor by factor, H_fix o Xi_eps = H_2 o A_eps = eps H hat_eps, i.e. H hat_eps = H_fix^{Xi_eps}; physical time preserved
  Inputs: `stepP:p11:pr-basic, bpP:p11:total-chart, bpP:p1:chart, bpP:p11:aniso-avg, bpP:p11:holo-chart, bpP:p11:avg-fast, bpP:p11:avg-slow, bpP:p1:chart-field, bpP:p11:sec-E#data, bpP:p0:fixham#fixedHamiltonian`.
- **`stepP:p11:wr-tor`** — K_b satisfies (L1)-(L6) of bpP:p1:lattice-torus with G = H hat_eps, O = R_eps, w = w_b (tau_D >= 2n); by bpP:p1:torus-transport (b) IsPhysTorus(H_fix, w_b, Xi_eps o K_b); for z = Xi_eps(K_b(theta_0)): w := w_b, K := Xi_eps o K_b gives z = K(theta_0), K(R^2n) in S_eps = Xi_eps(A), A = K(H_eps x R^2n)
  Inputs: `stepP:p11:wr-kam, stepP:p11:wr-chain, bpP:p1:lattice-torus, bpP:p1:torus-transport, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:diophantine#IsDiophantine`.
- **`stepP:p11:wr-meas`** — A = union_k (B + iota_k) is Borel, invariant, in R_eps; some translate of the ambient cell has meas(B cap (Q + iota_k)) > 0, so meas(A cap Q) > 0; by bpP:p6:measure-positive (b) S_eps = Xi_eps(A) is Borel with meas S_eps = eps^{2n} meas(A cap Q) > 0; finiteness from the tube inclusion
  Inputs: `stepP:p11:wr-kam, stepP:p11:wr-tor, stepP:p11:wr-chain, bpP:p6:measure-positive, bpP:p1:liouville-lattice, stepP:p11:wr-tube`.
- **`stepP:p11:wr-tube`** — after Psi_2: rho tilde_j in eps[2 pi - 2, 2 pi + 2], ¦J - J_0¦ <= 2 eps; x_j^2 + y_j^2 < 3 eps; Phi^1 moves J by <= c eps ell^{tau_0} and z by <= c eps ell^{tau_0} = o(sqrt eps); (xi, eta) = rho(x, y) with rho in SO(n) real orthogonal, sum(xi^2 + eta^2) <= 4 n eps, Gamma_i <= 2 n eps, ¦Lambda - Lambda^*¦ <= delta_*/8 + c eps ell^{tau_0} <= delta_*; Lemma forward-tube applies: Xi_eps(...) in U_zeta_* in U_eta
  Inputs: `stepP:p11:wr-kam, stepP:p11:wr-nu, stepP:p11:wr-chain, bpP:p11:avg-slow, bpP:p11:avg-fast, bpP:p9:lift, bpP:p11:forward-tube, bpP:p6:tube-geometry, bpP:p11:sec-A#data, bpP:p11:sec-D#data, bpP:p11:e4, bpP:p11:sec-C#data`.
- **`bpP:p11:sec-conv#data`** — defines: angles of period one, characters chi_k = e^{2 pi i k.theta}, max norms on R^m, C^m with induced operator norms, D(c, r) = {v in C^m : ¦v - c¦_inf < r}, T_sigma = {theta in C^m : ¦Im theta¦_inf < sigma}; for V open and u on T_sigma x V 1-periodic in the angles the weighted norm wn(u, V, sigma) = sup_{x in V} sum_k ¦u^_k(x)¦ e^{2 pi ¦k¦_1 sigma} (Fourier expansion in the angles only; other variables play the role of parameters); sup ¦u¦ <= wn(u) <= coth(pi sigma prime)^m sup over T_{sigma+sigma prime} x V ¦u¦; the period conversion chart (1-chart) with frozen frequency w = omega_CP/2pi
  Inputs: `N:bpN:p4:norm, N:bpN:p4:sup-weighted, bpP:p1:period-convert`.
- **`bpP:p11:sec-A#data`** — defines: Lambda_i^* = m_i sqrt(kappa a_i); the patch a_0, r_0, K_a, K_Lambda = Lambda(K_a); mu bar and beta bar (squared convention); h tilde(J) = h(J/2pi), omega(J) = grad h tilde = nu(J/2pi)/2pi, Omega tilde(J) = Omega(J/2pi)/2pi with Omega_j = 2 sigma_j and Omega tilde_j < 0, varpi_J = (omega, Omega tilde) on 2 pi B^Lambda, K_J = 2 pi K_Lambda
  Inputs: `bpP:p6:conv#data, bpP:p6:tube-constants, bpP:p8:perturbation-analytic, bpP:p11:forward-tube, bpP:p10:interface, bpP:p9:dict`.
- **`bpP:p11:sec-C#data`** — defines nu_1 = 3, K_1 = 3(nu_1 - 1)/(pi sigma_F) log(1/(eps M_F)), alpha_1 = (1/2) gamma_0 K_1^{-tau_0}, s_1 = min{r_C, gamma_0/(4 L K_1^{tau_0+1})}, d_1 = min{s_1 sigma_F, r_z^2}; D_1 = T_{sigma_F} x D(J_0, s_1) x B_{r_z}, D_1 prime = T_{sigma_F/6} x D(J_0, s_1/2) x B_{r_z/2}
  Inputs: `bpP:p11:holo-chart`.
- **`bpP:p11:sec-D#data`** — defines: Pi = Theta^(1) on the polar shell P_eps = {¦Im zeta¦ < sigma_F/6, ¦rho tilde_j - 2 pi eps¦ < pi eps} (holomorphic, ¦Pi¦ <= sqrt(3 eps) e^{pi sigma_F/3}); sigma_3 = sigma_F/12; G hat(J, zeta, rho tilde) = G(J, Pi), G hat_0 = zeta-average, h_0(J, rho tilde) = h tilde(J) + eps G hat_0, f_2 = eps(G hat - G hat_0) + f_1 o (id, Pi), K_2 = 3 nu_2/(pi sigma_3) log(1/eps), alpha_(1) = gamma_0 K_2^{-tau_0}/4, alpha_(2) = eps gamma_0 K_2^{-tau_0}/4, s_2 = min{s_1/4, gamma_0/(8 L K_2^{tau_0+1})}, r_* = pi eps; e^{-2 pi K_2 sigma_3/6} = eps^{nu_2}; the slow frequency is the second block d_{rho tilde} h_0 = eps(Omega tilde(J) + ...)
  Inputs: `bpP:p11:total-chart, bpP:p11:avg-fast, bpP:p11:sec-C#data, bpP:p11:holo-chart`.
- **`bpP:p11:sec-E#data`** — defines: rho tilde_0 = (2 pi eps, ..., 2 pi eps), the eps-chart A_eps(theta, r, zeta, rho prime) = (theta, J_0 + eps r, zeta, eps(2 pi 1 + rho prime)) with A_eps^*(dJ^dtheta + d rho tilde^dzeta) = eps(dr^dtheta + d rho prime^dzeta), mapping {¦r¦ < 2, ¦rho prime¦ < pi/2} into V_2/2 iff 2 eps <= s_2/2; E = {¦Im(theta, zeta)¦ < sigma_3/6, ¦r¦ < 2, ¦rho prime¦ < pi/2}; N_eps = (h_0 + g_2) o A_eps/eps, P_eps = f_3 o A_eps/eps, H hat_eps = H_2 o A_eps/eps = N_eps + P_eps with H_2 = H o Phi^1_eps o Theta hat o Psi_2; the KAM datum entries K_eps = [-1/2, 1/2]^{2n}, theta = 1/4, eps^* = 1/2, s = s_* = sigma_3/6 = sigma_F/72, N = 2n, mu = mu bar, tau_D = max{n mu bar, 2n}; the domain table; hat omega_eps = (omega hat^(1), eps omega hat^(2)) with omega hat^(1) = omega + eps d_J G hat_0 + d_J g_2, omega hat^(2) = Omega tilde + d_rho Z hat + eps^{-1} d_rho g_2
  Inputs: `bpP:p11:avg-slow, bpP:p11:avg-fast, bpP:p11:total-chart, bpP:p11:sec-D#data, bpP:p11:kam-input, bpP:p11:sec-A#data, bpP:p11:select`.
- **`bpP:p11:e4`** — log(1/epsilon)>=1; epsilon^a (log(1/epsilon))^b tends to 0 as epsilon tends to 0 through positive values
  Inputs: `-`.
- **`bpP:p11:e5`** — the integral of the uniformly convergent series is the sum of its termwise integrals; int_0^1 sin(2pi t)^a cos(2pi t)^b dt=0 unless a and b are both even, and its absolute value is at most 1
  Inputs: `-`.
- **`bpP:p11a:f-rolle`** — u^(q) has a zero in (a,b) (Rolle q times); the Lagrange interpolation polynomial P = sum_i y_i prod_{j!=i}(t-t_j)/(t_i-t_j) is the unique polynomial of degree <= q with P(t_i)=y_i, its t^q coefficient is sum_i y_i/prod_{j!=i}(t_i-t_j), and P^(q) = q! times it
  Inputs: `-`.
- **`bpP:p11a:f-meas`** — countable subadditivity and monotonicity; t -> meas(E ∩ [a,t]) is continuous and nondecreasing; meas(Q(E)) = meas E; Tonelli on R^(N-1) x R
  Inputs: `-`.
- **`bpP:p11a:f-mvt`** — mean value inequality (K:bp:p1:ext-mvt) and the chain rule d^q/dt^q g(x+ta) = D^q g(x+ta)(a^q)
  Inputs: `-`.
- **`bpP:p11a:f-orth`** — a is the last column of an orthogonal matrix Q (Q=I if a=e_N, else the Householder matrix Q = I - 2vv^T/(v^T v), v = e_N - a; ¦det Q¦=1, Q e_N = a)
  Inputs: `-`.
- **`bpP:p11a:f-leib`** — D^k(fh)(y)(a_1..a_k) = sum over subsets S of {1..k} of D^¦S¦f(y)(a_S) D^(k-¦S¦)h(y)(a_(S^c)); for equal arguments sum_j binom(k,j) D^j f(a^j) D^(k-j) h(a^(k-j))
  Inputs: `-`.
- **`bpP:p11a:conv#data`** — defines: ¦.¦_2, ¦.¦_inf on R^N and R^m with comparison; d = d_inf(K) = sup ¦y-y'¦_inf; K_theta = {y: dist_2(y,K)<=theta}; the diagonal and operator tensor norms dgn(D^nu g(y)), opn(D^nu g(y)) with dgn <= opn; the seminorms norm(g)^mu_dg,A and norm(g)^mu_op,A
  Inputs: `-`.
- **`bpP:p11a:index-def`** — defines g_rho[omega](c,y) = <c,omega(y)>^rho, beta_{rho,mu}(omega,K) = min over c in S^(m-1), y in K of max_{0<=nu<=mu} dgn(D^nu g_rho(c,y)) (a minimum of a continuous function on a compact set), and, when some beta_{rho,mu}>0 with 1<=mu<=L, the index mu_0 (least positive integer with beta_{rho,mu_0}>0) and the amount beta_rho(omega,K) = beta_{rho,mu_0}
  Inputs: `bpP:p11a:conv#data`.
- **`bpP:p11a:stability`** — for 0<=nu<=mu, y in A: dgn(D^nu e_c(y)) <= theta (rho=1), <= 2^nu theta (2M_0+theta) (rho=2); with eta_1(theta)=theta, eta_2(theta)=2^mu theta (2M_0+theta): for compact K subset A, beta_{rho,mu}(omega~,K) >= beta_{rho,mu}(omega,K) - eta_rho(theta); if beta_{rho,mu}(omega,K)>=beta>0 and eta_rho(theta)<=beta/2 then beta_{rho,mu}(omega~,K)>=beta/2 and dgn(D^nu e_c(y))<=beta/2 on A for all c, nu<=mu; no analyticity or nondegeneracy of omega~ assumed
  Inputs: `stepP:p11a:st-1, stepP:p11a:st-2, stepP:p11a:st-amount, bpP:p11a:index-def, bpP:p11a:conv#data`.
- **`stepP:p11a:st-1`** — dgn(D^nu e_c(y)) <= theta
  Inputs: `bpP:p11a:conv#data, bpP:p11a:index-def`.
- **`stepP:p11a:st-2`** — dgn(D^nu e_c(y)) <= 2^nu theta (2M_0+theta)
  Inputs: `bpP:p11a:f-leib, bpP:p11a:conv#data, bpP:p11a:index-def`.
- **`stepP:p11a:st-amount`** — beta_{rho,mu}(omega~,K) >= beta_{rho,mu}(omega,K) - eta_rho(theta) (triangle inequality for the seminorm dgn, then max over nu and min over (c,y))
  Inputs: `stepP:p11a:st-1, stepP:p11a:st-2, bpP:p11a:index-def, bpP:p11a:conv#data`.
- **`bpP:p11a:M-bound`** — opn(D^k g_1[omega](c,y)) <= M_1 and opn(D^k g_2[omega](c,y)) <= 2^k M_1^2 <= 2^(mu+1) M_1^2
  Inputs: `bpP:p11a:index-def, bpP:p11a:conv#data, bpP:p11a:f-leib`.
- **`bpP:p11a:divided-difference`** — there is xi in (t_0,t_q) with sum_{i=0}^q f(t_i)/prod_{j!=i}(t_i-t_j) = f^(q)(xi)/q!
  Inputs: `stepP:p11a:dd-interp, stepP:p11a:dd-rolle`.
- **`stepP:p11a:dd-interp`** — the t^q-coefficient of P is c = sum_i f(t_i)/prod_{j!=i}(t_i-t_j), so P^(q) = q! c
  Inputs: `bpP:p11a:f-rolle`.
- **`stepP:p11a:dd-rolle`** — there is xi in (t_0,t_q) with u^(q)(xi)=0, i.e. f^(q)(xi) = q! c
  Inputs: `bpP:p11a:f-rolle, stepP:p11a:dd-interp`.
- **`bpP:p11a:scalar-sublevel`** — for every eps>0: meas{t in [a,b]: ¦f(t)¦<=eps} <= 2q (eps/beta)^(1/q)
  Inputs: `stepP:p11a:ss-phi, stepP:p11a:ss-nodes, stepP:p11a:ss-gaps, stepP:p11a:ss-dd, bpP:p11a:f-meas`.
- **`stepP:p11a:ss-phi`** — phi(t) = meas(E ∩ [a,t]) is continuous and nondecreasing from phi(a)=0 to phi(b)=L
  Inputs: `bpP:p11a:f-meas`.
- **`stepP:p11a:ss-nodes`** — nodes t_0 = min E, t_i = min{t: phi(t) >= iL/q} lie in E, satisfy phi(t_i)=iL/q, t_0<...<t_q and t_j - t_i >= (j-i)L/q
  Inputs: `stepP:p11a:ss-phi, bpP:p11a:f-meas`.
- **`stepP:p11a:ss-gaps`** — prod_{j!=i} ¦t_i-t_j¦ >= i! (q-i)! (L/q)^q
  Inputs: `stepP:p11a:ss-nodes`.
- **`stepP:p11a:ss-dd`** — beta/q! <= ¦sum f(t_i)/prod(t_i-t_j)¦ <= eps 2^q (q/L)^q / q!, hence L^q <= (2q)^q eps/beta
  Inputs: `bpP:p11a:divided-difference, stepP:p11a:ss-nodes, stepP:p11a:ss-gaps`.
- **`bpP:p11a:ball-sublevel`** — for every eps>0: meas{y in U: ¦g(y)¦<=eps} <= 2q (2r)^(N-1) (eps/beta)^(1/q)
  Inputs: `stepP:p11a:bs-rot, stepP:p11a:bs-sections, stepP:p11a:bs-tonelli, bpP:p11a:conv#data`.
- **`stepP:p11a:bs-rot`** — y = y_0 + Q(x',t) preserves Lebesgue measure and maps {¦x'¦_2^2+t^2<=r^2} onto U
  Inputs: `bpP:p11a:f-orth, bpP:p11a:f-meas, bpP:p11a:conv#data`.
- **`stepP:p11a:bs-sections`** — section measure <= 2q (eps/beta)^(1/q) (zero if I_x' is a point)
  Inputs: `bpP:p11a:f-mvt, bpP:p11a:scalar-sublevel, stepP:p11a:bs-rot, bpP:p11a:conv#data`.
- **`stepP:p11a:bs-tonelli`** — meas{y in U: ¦g(y)¦<=eps} <= 2q (2r)^(N-1) (eps/beta)^(1/q)
  Inputs: `bpP:p11a:f-meas, stepP:p11a:bs-sections, stepP:p11a:bs-rot, bpP:p11a:conv#data`.
- **`bpP:p11a:sublevel`** — for every 0<eps<beta/4: meas{y in K: ¦g~(y)¦<=eps} <= C_sub (eps/beta)^(1/mu), C_sub = 2^(N+2) mu (sqrt(N) d)^(N-1) (M/beta) (1 + (4+1/theta) sqrt(N) d)
  Inputs: `stepP:p11a:sl-cover, stepP:p11a:sl-lower, stepP:p11a:sl-ball, stepP:p11a:sl-sum, bpP:p11a:conv#data, bpP:p11a:sublevel#kappa`.
- **`bpP:p11a:sublevel#kappa`** — kappa = ceil((M/beta)(4+1/theta) sqrt(N) d) >= 1, r = sqrt(N) d/kappa satisfy kappa >= 4M sqrt(N) d/beta, kappa >= sqrt(N) d/theta, kappa <= (M/beta)(1+(4+1/theta) sqrt(N) d); hence M r <= beta/4 and r <= theta
  Inputs: `bpP:p11a:conv#data`.
- **`stepP:p11a:sl-cover`** — K subset union of balls U_j = {¦y-b_j¦_2<=r} around points b_j in Q_j ∩ K (at most kappa^N of them), each U_j convex and contained in K_theta subset V
  Inputs: `bpP:p11a:sublevel#kappa, bpP:p11a:conv#data`.
- **`stepP:p11a:sl-lower`** — ¦D^nu g~(y)(a^nu)¦ >= beta - M r - beta/2 >= beta/4 on U_j for nu(j)>=1, and ¦g~(y)¦ >= beta/4 > eps on U_j for nu(j)=0
  Inputs: `bpP:p11a:f-mvt, stepP:p11a:sl-cover, bpP:p11a:sublevel#kappa, bpP:p11a:conv#data`.
- **`stepP:p11a:sl-ball`** — meas{y in U_j: ¦g~(y)¦<=eps} <= 8 mu (2r)^(N-1) (eps/beta)^(1/mu) (empty if nu(j)=0)
  Inputs: `bpP:p11a:ball-sublevel, stepP:p11a:sl-lower, stepP:p11a:sl-cover, bpP:p11a:conv#data`.
- **`stepP:p11a:sl-sum`** — meas{y in K: ¦g~(y)¦<=eps} <= 2^(N+2) mu (sqrt(N) d)^(N-1) kappa (eps/beta)^(1/mu) <= C_sub (eps/beta)^(1/mu)
  Inputs: `bpP:p11a:f-meas, stepP:p11a:sl-ball, stepP:p11a:sl-cover, bpP:p11a:sublevel#kappa, bpP:p11a:conv#data`.
- **`bpP:p11a:diophantine-measure`** — with H = {b in K: ¦k.omega~_k(b)¦>=Psi(k) for all k!=0}: H is compact and meas(K\H) <= C_sub beta^(-1/mu) sum_{k!=0} (Psi(k)/¦k¦_2)^(rho/mu), C_sub = C_sub(N,mu,d,theta,M/beta) of Theorem bpP:p11a:sublevel (right side may be +inf)
  Inputs: `stepP:p11a:dm-compact, stepP:p11a:dm-union, stepP:p11a:dm-onek, stepP:p11a:dm-sum, bpP:p11a:index-def, bpP:p11a:conv#data, bpP:p11a:sublevel`.
- **`stepP:p11a:dm-compact`** — H is an intersection of closed subsets of K, hence compact
  Inputs: `-`.
- **`stepP:p11a:dm-union`** — K\H is contained in the union over k!=0 of {b in K: ¦g_rho[omega~_k](c_k,b)¦<=eps_k}
  Inputs: `bpP:p11a:index-def, bpP:p11a:conv#data`.
- **`stepP:p11a:dm-onek`** — meas{b in K: ¦g~(b)¦<=eps_k} <= C_sub beta^(-1/mu) (Psi(k)/¦k¦_2)^(rho/mu)
  Inputs: `bpP:p11a:sublevel, stepP:p11a:dm-union, bpP:p11a:index-def, bpP:p11a:conv#data`.
- **`stepP:p11a:dm-sum`** — meas(K\H) <= sum_k meas{¦g~_k¦<=eps_k} (countable subadditivity)
  Inputs: `bpP:p11a:f-meas, stepP:p11a:dm-union, stepP:p11a:dm-onek`.
- **`bpP:p11a:power-law`** — H_gamma compact and meas(K\H_gamma) <= C_Dio gamma^(rho/mu), C_Dio = C_sub beta^(-1/mu) m^(rho/(2mu)) 2 3^(m-1) (1+1/s); for every eps* in (0,meas K) and 0<gamma<=gamma_*(eps*) = min{(1/2) m^(-1/2) (beta/4)^(1/rho), (eps*/C_Dio)^(mu/rho)}: meas H_gamma >= meas K - eps*
  Inputs: `stepP:p11a:pl-profile, stepP:p11a:pl-sum, stepP:p11a:pl-conc, bpP:p11a:diophantine-measure, bpP:p11a:conv#data, bpP:p11a:index-def`.
- **`stepP:p11a:pl-profile`** — For every k!=0, Psi(k)/¦k¦_2 <= sqrt(m) gamma ¦k¦_1^(-tau-1) <= sqrt(m) gamma, so (D4) of the theorem holds.
  Inputs: `bpP:p11a:conv#data`.
- **`stepP:p11a:pl-sum`** — sum_{k!=0} (Psi(k)/¦k¦_2)^(rho/mu) <= (sqrt(m) gamma)^(rho/mu) S(m,tau') = (sqrt(m) gamma)^(rho/mu) 2 3^(m-1) (s+1)/s
  Inputs: `K:bp:p4:lattice-sum, stepP:p11a:pl-profile, bpP:p11a:conv#data`.
- **`stepP:p11a:pl-conc`** — meas(K\H_gamma) <= C_Dio gamma^(rho/mu); for gamma <= gamma_*, (sqrt(m) gamma)^rho <= 2^(-rho) beta/4 < beta/4 and C_Dio gamma^(rho/mu) <= eps*
  Inputs: `bpP:p11a:diophantine-measure, stepP:p11a:pl-sum, stepP:p11a:pl-profile, bpP:p11a:conv#data`.
- **`bpP:p11a:limit-bridge`** — ¦k.v¦ >= gamma ¦k¦_1^(-tau); consequently omega_*(b) is (gamma,tau)-Diophantine in the frozen sense (Definition bpP:p0:diophantine)
  Inputs: `bpP:p11a:power-law, bpP:p0:diophantine#IsDiophantine, bpP:p11a:conv#data`.
- **`bpP:p11a:c2-conv#data`** — defines: max norms ¦.¦_inf, ¦k¦_1, induced matrix norm, norm of D^j u = sup over ¦a_i¦_inf<=1; the thickening E+t = {b in C^N: exists b' in E, ¦b-b'¦_inf<t} (open) and polydiscs P(b',t) subset E+t
  Inputs: `-`.
- **`bpP:p11a:c2-conv#bracket`** — defines X_phi = (d_eta phi, -d_theta phi), {u,v} = Du.X_v = d_theta u . d_eta v - d_eta u . d_theta v, and the generating function phi acts by the time-one flow Phi = X_phi^1; same convention as Rus01 up to row/column conversion and the factor 2 pi; the sign was fixed to match N:bpN:p5:taylor
  Inputs: `N:bpN:p5:setting, bpP:p11a:c2-conv#data`.
- **`bpP:p11a:domain-def`** — defines T_r = {theta in C^N: ¦Im theta¦_inf<r}, D(r,s;B) = {(theta,eta,b): theta in T_r, ¦eta¦_inf<s, b in B}, the sup norm of F, admissible functions (holomorphic in all variables, B open, 1-periodic in each theta_j), the truncation cut_T F = sum_{¦k¦_1<=T} F^_k chi_k with F^_k = integral of F chi_(-k), chi_k = exp(2 pi i k.theta), the average <F> = F^_0, trigonometric polynomials of degree <= T
  Inputs: `K:bp:p0:domains#complexStrip, bpP:p11a:c2-conv#data`.
- **`bpP:p11a:x-cauchy`** — g(zeta) = sum_j g_j zeta^j on ¦zeta¦<R with ¦g_j¦<=M R^(-j); and ¦d_(zeta_1)...d_(zeta_j) G(0)¦ <= M prod R_i^(-1)
  Inputs: `-`.
- **`bpP:p11a:x-duality`** — ¦k.x¦ <= ¦k¦_1 ¦x¦_inf and ¦chi_k(theta)¦ <= exp(2 pi ¦k¦_1 ¦Im theta¦_inf)
  Inputs: `-`.
- **`bpP:p11a:x-ode`** — unique global solution, affine in y(0); and ¦y(t)¦ <= e^(Lambda t) ¦y(0)¦
  Inputs: `-`.
- **`bpP:p11a:fourier-cutoff`** — c_N>=1; cut_T F is a trigonometric polynomial of degree <=T, entire in theta; (a) norm(F-cut_T F)_(r-d) <= eps_N(T,d) norm(F)_r; (b) norm(cut_T F)_(r-d) <= (1+eps_N(T,d)) norm(F)_r; (c) cut_T F is real if F is real on R^N
  Inputs: `stepP:p11a:fc-const, stepP:p11a:fc-decay, stepP:p11a:fc-tail, stepP:p11a:fc-count, stepP:p11a:fc-poly, stepP:p11a:fc-assemble, bpP:p11a:domain-def, bpP:p11a:c2-conv#data`.
- **`stepP:p11a:fc-const`** — c_N >= 1
  Inputs: `-`.
- **`stepP:p11a:fc-decay`** — ¦F^_k¦ <= e^(-2 pi ¦k¦_1 r) norm(F)_r; F = sum F^_k chi_k on T_rho for rho<r; F - cut_T F = sum_{¦k¦_1>T} F^_k chi_k on T_(r-d); (c) cut_T F real if F real
  Inputs: `K:bp:p1:decay, K:bp:p1:summation, bpP:p11a:domain-def, bpP:p11a:c2-conv#data`.
- **`stepP:p11a:fc-tail`** — ¦F - cut_T F¦ <= norm(F)_r sum_{¦k¦_1>T} e^(-2 pi ¦k¦_1 d)
  Inputs: `bpP:p11a:x-duality, stepP:p11a:fc-decay, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`stepP:p11a:fc-count`** — sum_{¦k¦_1>T} e^(-2 pi ¦k¦_1 d) <= 2 3^(N-1) sum_{j>T} j^(N-1) e^(-pi j d) e^(-pi j d)
  Inputs: `K:bp:p4:lattice-count, stepP:p11a:fc-tail, bpP:p11a:c2-conv#data`.
- **`stepP:p11a:fc-poly`** — j^(N-1) e^(-pi j d) <= ((N-1)/(e pi d))^(N-1) and sum_{j>T} e^(-pi j d) <= e^(-pi T d)(1+1/(pi d))
  Inputs: `K:bp:p1:exp-sums, stepP:p11a:fc-count`.
- **`stepP:p11a:fc-assemble`** — tail sum <= 2 3^(N-1) ((N-1)/(e pi))^(N-1) (d^(-(N-1)) + d^(-N)/pi) e^(-pi T d) <= eps_N(T,d); this is (a), and (b) follows with the triangle inequality
  Inputs: `stepP:p11a:fc-count, stepP:p11a:fc-poly, stepP:p11a:fc-tail, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`bpP:p11a:loss-choice`** — if d_T<=1 then eps_N(T,d_T) <= alpha; T -> d_T(alpha) is decreasing on [1,inf) and alpha -> d_T(alpha) is decreasing
  Inputs: `stepP:p11a:lc-exponent, stepP:p11a:lc-estimate, stepP:p11a:lc-mono, bpP:p11a:fourier-cutoff`.
- **`stepP:p11a:lc-exponent`** — A = log(2c_N/alpha) + N log(pi T) >= log 2 + N log pi > 1
  Inputs: `bpP:p11a:fourier-cutoff`.
- **`stepP:p11a:lc-estimate`** — eps_N(T,d_T) <= c_N 2 (pi T)^N (alpha/(2 c_N)) (pi T)^(-N) = alpha
  Inputs: `stepP:p11a:lc-exponent, bpP:p11a:fourier-cutoff`.
- **`stepP:p11a:lc-mono`** — d/dT of (a+N log(pi T))/(pi T) is negative; the alpha-monotonicity is clear
  Inputs: `bpP:p11a:fourier-cutoff`.
- **`bpP:p11a:loss-sum`** — d_nu <= (a + b nu + N log(pi T_0) + N nu log Theta)/(pi T_0 Theta^nu) and sum_{nu>=0} d_nu <= (1/(pi T_0)) [ (a+N log(pi T_0)) Theta/(Theta-1) + (b+N log Theta) Theta/(Theta-1)^2 ]; for alpha_nu = alpha_0 delta^(kappa nu): a = log(2c_N/alpha_0), b = kappa log(1/delta)
  Inputs: `bpP:p11a:loss-choice, bpP:p11a:fourier-cutoff`.
- **`bpP:p11a:taylor-cutoff`** — F^(<=1) is admissible (entire in eta); (a) ¦d_(eta_j) F(theta,0,b)¦_inf <= M/s, ¦F^(<=1)¦ <= M(1+¦eta¦_inf/s), norm(F^(<=1))_(r,s;B) <= 2M; (b) for 0<q<1: norm(F - F^(<=1))_(r,qs;B) <= M q^2/(1-q)
  Inputs: `stepP:p11a:tc-line, stepP:p11a:tc-a, stepP:p11a:tc-b, bpP:p11a:domain-def, bpP:p11a:c2-conv#data`.
- **`stepP:p11a:tc-line`** — g(zeta) = sum g_j zeta^j with ¦g_j¦ <= M s^(-j), g_0 = F(theta,0,b), g_1 = d_eta F(theta,0,b) eta/a
  Inputs: `bpP:p11a:x-cauchy, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`stepP:p11a:tc-a`** — ¦F^(<=1)¦ <= M + M a/s and ¦d_(eta_j) F(theta,0,b)¦ <= M/s
  Inputs: `K:bp:p1:ext-cauchy, stepP:p11a:tc-line, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`stepP:p11a:tc-b`** — ¦F - F^(<=1)¦ = ¦sum_{j>=2} g_j a^j¦ <= M (a/s)^2/(1-a/s) <= M q^2/(1-q)
  Inputs: `stepP:p11a:tc-line, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`bpP:p11a:cutoff`** — R_*0, R_*1,j are trigonometric polynomials of degree <=T, admissible on C^N x B; (a) norm(R_*0)_(r-d;B) <= (1+E_T) eps, norm(R_*1,j)_(r-d;B) <= (1+E_T) eps/s, norm(R_*)_(r-d,s;B) <= 2(1+E_T) eps; (b) norm(R-R_*)_(r-d,qs;B) <= eps (q^2/(1-q) + 2E_T); (c) R_* real if R real; with T=T_nu, d=d_nu, alpha=alpha_nu of Lemma bpP:p11a:loss-choice: E_T<=alpha and (b) reads <= eps(q^2/(1-q)+2 alpha)
  Inputs: `stepP:p11a:cu-coeff, stepP:p11a:cu-a, stepP:p11a:cu-b, stepP:p11a:cu-c, bpP:p11a:fourier-cutoff, bpP:p11a:taylor-cutoff, bpP:p11a:domain-def, bpP:p11a:loss-choice, bpP:p11a:c2-conv#data`.
- **`stepP:p11a:cu-coeff`** — b -> integral R(x,0,b) chi_(-k) dx is holomorphic; R_*0, R_*1,j are finite sums of these times characters, hence admissible
  Inputs: `N:bpN:p4:ext-param, bpP:p11a:domain-def, bpP:p11a:c2-conv#data`.
- **`stepP:p11a:cu-a`** — norm(R_*)_(r-d,s;B) <= 2(1+E_T) eps, norm(R_*0)_(r-d;B) <= (1+E_T) eps, norm(R_*1,j)_(r-d;B) <= (1+E_T) eps/s
  Inputs: `bpP:p11a:fourier-cutoff, bpP:p11a:taylor-cutoff, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`stepP:p11a:cu-b`** — norm(R-R_*) <= eps q^2/(1-q) + 2 E_T eps
  Inputs: `bpP:p11a:taylor-cutoff, bpP:p11a:fourier-cutoff, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`stepP:p11a:cu-c`** — R^(<=1) is real at real points and so is R_*
  Inputs: `bpP:p11a:fourier-cutoff, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`bpP:p11a:param-cauchy`** — for every b in E+t' and j>=1: norm(D^j u(b)) <= j^j M (t-t')^(-j); likewise for the b-derivatives of a function of (theta,eta,b) at every (theta,eta)
  Inputs: `stepP:p11a:pc-poly, stepP:p11a:pc-iter, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`stepP:p11a:pc-poly`** — G(zeta) = u(b + sum zeta_i a_i) is holomorphic and bounded by M on the polydisc, which lies in P(b',t) subset E+t
  Inputs: `bpP:p11a:c2-conv#data`.
- **`stepP:p11a:pc-iter`** — D^j u(b)(a_1..a_j) = d_(zeta_1)..d_(zeta_j) G(0) is bounded by M (j/rho)^j; vector valued: componentwise with max norm
  Inputs: `bpP:p11a:x-cauchy, stepP:p11a:pc-poly, bpP:p11a:c2-conv#data`.
- **`bpP:p11a:divisor-perturb`** — ¦k.omega(b)¦ >= D/2 for all b in E+t and 0<¦k¦_1<=T
  Inputs: `bpP:p11a:c2-conv#data, bpP:p11a:x-duality, K:bp:p1:ext-mvt`.
- **`bpP:p11a:sec-hom#lambda`** — defines Lambda_delta = coth(pi delta)^N - 1 = sum_{k!=0} e^(-2 pi delta ¦k¦_1) (K:bp:p1:exp-sums (b) with x = 2 pi delta), with Lambda_delta <= (1+1/(pi delta))^N - 1 and Lambda_delta <= (4N/(pi delta))^N
  Inputs: `K:bp:p1:exp-sums, bpP:p11a:c2-conv#data`.
- **`bpP:p11a:homological-maximal`** — there are unique admissible trigonometric polynomials phi_0, phi_1,j of degree <=T with zero average, holomorphic on C^N x B, such that omega(b).d_theta phi_0 = P_0 - <P_0>, omega(b).d_theta phi_1,j = P_1,j - <P_1,j>; (a) norm(phi_0)_(r_*-delta;B) <= Lambda_delta M_0/(pi D), likewise phi_1,j with M_1; (b) averages holomorphic on B bounded by M_0, M_1; (c) for 0<t'<t, j>=1, b in E+t', theta in T_(r_*-delta): norm(D_b^j phi_0) <= j^j Lambda_delta M_0 (pi D)^(-1) (t-t')^(-j), likewise phi_1,j, averages; (d) if P_0,P_1 are real on real points, reality for real (theta,b); (e) ¦phi^_1,j,k(b)¦ <= M_1 e^(-2 pi ¦k¦_1 r_*)/(pi D) for 0<¦k¦_1<=T; and {N_b,phi} = -(P - <P>) for phi = phi_0 + phi_1.eta, N_b = h + omega.eta, P = P_0 + P_1.eta
  Inputs: `stepP:p11a:hm-div, stepP:p11a:hm-coeff, stepP:p11a:hm-a, stepP:p11a:hm-bc, stepP:p11a:hm-d, stepP:p11a:hm-bracket, bpP:p11a:divisor-perturb, bpP:p11a:sec-hom#lambda, bpP:p11a:c2-conv#bracket, bpP:p11a:domain-def, bpP:p11a:c2-conv#data`.
- **`stepP:p11a:hm-div`** — ¦k.omega(b)¦ >= D/2 for all b in B
  Inputs: `bpP:p11a:divisor-perturb, bpP:p11a:c2-conv#data`.
- **`stepP:p11a:hm-coeff`** — the equation holds iff phi^_0,k = p_k/(2 pi i k.omega(b)) for 0<¦k¦_1<=T and phi^_0,0 = 0; this defines phi_0 uniquely and holomorphically on B; likewise phi_1,j
  Inputs: `stepP:p11a:hm-div, stepP:p11a:cu-coeff, K:bp:p1:fourier-basic, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`stepP:p11a:hm-a`** — ¦phi^_0,k¦ <= M_0 e^(-2 pi ¦k¦_1 r_*)/(pi D); ¦phi_0¦ <= Lambda_delta M_0/(pi D); same for phi_1,j; (e) is the coefficient bound
  Inputs: `K:bp:p1:decay, stepP:p11a:hm-coeff, bpP:p11a:sec-hom#lambda, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, stepP:p11a:hm-div`.
- **`stepP:p11a:hm-bc`** — (b) ¦p_0¦ <= M_0 and p_0 holomorphic; (c) parameter Cauchy estimates for b -> phi_0(theta,b) on B = E+t with M = Lambda_delta M_0/(pi D)
  Inputs: `bpP:p11a:param-cauchy, K:bp:p1:decay, stepP:p11a:hm-a, stepP:p11a:hm-coeff, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`stepP:p11a:hm-d`** — conj(phi^_0,k) = phi^_0,-k, so phi_0 (likewise phi_1, averages) is real for real (theta,b)
  Inputs: `stepP:p11a:hm-coeff, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`stepP:p11a:hm-bracket`** — {N_b,phi} = -omega.d_theta phi = -(P - <P>)
  Inputs: `stepP:p11a:hm-coeff, bpP:p11a:c2-conv#bracket, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`bpP:p11a:affine-flow`** — (a) on Omega: ¦d_eta phi¦<=A_1, ¦d_theta phi¦<=A_eta, nu(X_phi)<=kappa<=1/2; (b) Phi = X_phi^1 defined and holomorphic on Omega_h, trajectories for ¦t¦<=1 stay in Omega, ¦Phi_theta-theta¦<=A_1, ¦Phi_eta-eta¦<=A_eta; (c) Phi(theta,eta) = (Theta(theta), M(theta) eta + m(theta)), Theta the time-one map of d_t theta = phi_1(theta), M = (D Theta)^(-T); (d) on Omega_f: ¦D Phi - 1¦_nu <= 2 kappa, ¦D Theta - 1¦, ¦M - 1¦ <= 2 kappa, ¦d_theta(M eta + m)¦ <= kappa s/sigma; (e) (D Phi)^T J D Phi = J, Phi(theta+k,eta) = Phi(theta,eta)+(k,0), reality if phi_0,phi_1 are real on R^N, Psi = X_phi^(-1) with Psi o Phi = id = Phi o Psi on Omega_f; (f) if B is open and (theta,b)->phi_i(theta,b) are jointly holomorphic with the same bounds for every b, then Phi_b is jointly holomorphic on B x Omega_h with the same bounds
  Inputs: `stepP:p11a:af-field, stepP:p11a:af-flow, stepP:p11a:af-simple, stepP:p11a:af-deriv, stepP:p11a:af-rest, N:bpN:p5:setting, N:bpN:p5:flow, bpP:p11a:domain-def, bpP:p11a:c2-conv#bracket, bpP:p11a:c2-conv#data`.
- **`stepP:p11a:af-field`** — ¦d_(theta_i) phi_0¦<=s A_1/sigma, ¦d_(theta_i) phi_1,j¦<=A_1/sigma, ¦d_theta phi¦<=A_eta, ¦d_eta phi¦<=A_1, nu(X_phi)<=kappa<=1/2; A_eta<=s/4 is 4(N+1)A_1<=sigma
  Inputs: `K:bp:p1:cauchy-strip, N:bpN:p5:setting, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, bpP:p11a:c2-conv#bracket`.
- **`stepP:p11a:af-flow`** — Phi = X_phi^1 defined and holomorphic on Omega_h subset Omega^(1/2), trajectories in Omega, Omega_f subset Omega^1, ¦Phi_theta - theta¦ <= A_1, ¦Phi_eta - eta¦ <= A_eta
  Inputs: `N:bpN:p5:flow, N:bpN:p5:setting, K:bp:p1:ext-mvt, stepP:p11a:af-field, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, bpP:p11a:c2-conv#bracket`.
- **`stepP:p11a:af-simple`** — Phi_theta(theta_0,eta_0) = Theta(theta_0), Phi_eta = M(theta_0) eta_0 + m(theta_0) and M = (D Theta)^(-T)
  Inputs: `N:bpN:p5:flow, bpP:p11a:x-ode, N:bpN:p5:symplectic, stepP:p11a:af-flow, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, bpP:p11a:c2-conv#bracket`.
- **`stepP:p11a:af-deriv`** — ¦D Theta - 1¦, ¦M - 1¦ <= 2 kappa and ¦d_theta(M eta + m)¦ <= kappa s/sigma
  Inputs: `N:bpN:p5:flow, stepP:p11a:af-simple, stepP:p11a:af-flow, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`stepP:p11a:af-rest`** — canonical, periodic, real if phi_0,phi_1 are real on R^N, invertible with Psi = X_(-phi)^1; if B is open and (theta,b)->phi_i(theta,b) are jointly holomorphic with the same bounds for every b, then Phi_b is holomorphic jointly on B x Omega_h with the same bounds
  Inputs: `N:bpN:p5:symplectic, N:bpN:p5:flow, stepP:p11a:af-flow, stepP:p11a:af-field, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, bpP:p11a:c2-conv#bracket`.
- **`bpP:p11a:real-lipschitz`** — ¦D Theta^t(theta) - 1¦ <= e^Lambda - 1, Theta^t(theta+k) = Theta^t(theta)+k, ¦Theta^t(theta) - theta¦ <= sup ¦phi_1¦, Lambda <= 2 pi T max_i sum_{0<¦k¦_1<=T} ¦phi^_1,i,k¦; under the coefficient bound of Proposition bpP:p11a:homological-maximal(e): Lambda <= Lambda_R = 2 T M_1 Lambda_(r_*)/D
  Inputs: `stepP:p11a:rl-global, stepP:p11a:rl-deriv, stepP:p11a:rl-const, bpP:p11a:homological-maximal, bpP:p11a:sec-hom#lambda, bpP:p11a:c2-conv#data`.
- **`stepP:p11a:rl-global`** — global solutions; Theta^t(theta+k) = Theta^t(theta)+k (uniqueness); ¦Theta^t - theta¦ <= ¦t¦ sup ¦phi_1¦
  Inputs: `bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`stepP:p11a:rl-deriv`** — ¦Y(t)¦ <= e^(Lambda ¦t¦) and ¦Y(t)-1¦ <= e^(Lambda ¦t¦) - 1
  Inputs: `bpP:p11a:x-ode, stepP:p11a:rl-global, bpP:p11a:c2-conv#data, K:bp:p1:ext-integral`.
- **`stepP:p11a:rl-const`** — Lambda <= 2 pi T max_i sum_{0<¦k¦_1<=T} ¦phi^_1,i,k¦ <= 2 T M_1 Lambda_(r_*)/D
  Inputs: `bpP:p11a:homological-maximal, bpP:p11a:sec-hom#lambda, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.
- **`bpP:p11a:canonical-step`** — with R_* = R_*0 + R_*1.eta the cutoff of Proposition bpP:p11a:cutoff, Delta h = <R_*0>, Delta omega = <R_*1>, N_+ = h + Delta h + (omega + Delta omega).eta, D_+ = D(r_+,qs;B), phi = phi_0 + phi_1.eta the solution of Proposition bpP:p11a:homological-maximal with P = R_*, r_* = r-d, M_0 = (1+E_T) eps, M_1 = M_0/s: (i) Delta h, Delta omega holomorphic on B with ¦Delta h¦<=(1+E_T) eps<=2 eps, ¦Delta omega¦_inf<=(1+E_T) eps/s, N_+ of the form of N; (ii) Phi_b = X_(phi_b)^1 defined and holomorphic on D_+ with values in D(r_++sigma,s;B), ¦Phi_theta-theta¦<=A_1<=sigma/(4(N+1)), ¦Phi_eta-eta¦<=A_eta<=s/4, Phi simple, canonical, periodic, real if the data are real, ¦D Phi - 1¦_nu<=2 kappa, invertible with inverse X_phi^(-1); (iii) H_b o Phi_b = N_+ + R_+ on D_+, where R_+ is holomorphic, 1-periodic in theta and real at real points if the data are real, with norm(R_+)_(D_+) <= eps (q^2/(1-q) + 2E_T) + N(4N+5)(5+4E_T)(1+E_T) Lambda_delta eps^2/(pi D s sigma) <= eps(2q^2+2E_T) + 18 N(4N+5) Lambda_delta eps^2/(pi D s sigma); (iv) for real b in E, real theta: ¦D Theta_b - 1¦_inf <= e^(Lambda_R) - 1, Lambda_R = 2T(1+E_T) eps Lambda_(r-d)/(D s), Theta_b(theta+k) = Theta_b(theta)+k; (v) parameter derivatives for 0<t'<t, j>=1 on E+t' at every (theta,eta) in D_+: bounds j^j(1+E_T) eps (t-t')^(-j), (…)/s, j^j A_1 (t-t')^(-j), j^j A_eta (t-t')^(-j), j^j norm(R_+) (t-t')^(-j)
  Inputs: `stepP:p11a:cs-cutoff, stepP:p11a:cs-hom, stepP:p11a:cs-flow, stepP:p11a:cs-taylor, stepP:p11a:cs-u, stepP:p11a:cs-bracket, stepP:p11a:cs-assemble, stepP:p11a:cs-lip, stepP:p11a:cs-param, bpP:p11a:fourier-cutoff, bpP:p11a:cutoff, bpP:p11a:homological-maximal, bpP:p11a:affine-flow, bpP:p11a:sec-hom#lambda, bpP:p11a:domain-def, bpP:p11a:c2-conv#data, bpP:p11a:c2-conv#bracket`.
- **`stepP:p11a:cs-cutoff`** — R_* is a trigonometric polynomial with norm(R_*0)_(r-d;B)<=M_0, norm(R_*1,j)_(r-d;B)<=M_1, norm(R_*)_(r-d,s;B)<=2 M_0, norm(R-R_*)_(r-d,qs;B) <= eps(q^2/(1-q)+2E_T)
  Inputs: `bpP:p11a:c2-conv#data, bpP:p11a:domain-def, bpP:p11a:cutoff`.
- **`stepP:p11a:cs-hom`** — phi on T_(r_1), r_1 = r-d-delta, with norm(phi_1,j)_(r_1;B) <= Lambda_delta M_1/(pi D) = A_1, norm(phi_0)_(r_1;B) <= s A_1, (i) from part (b) (Delta h = <R_*0>, ¦Delta h¦<=M_0) and {N_b,phi} = -(R_* - <R_*>) =: w
  Inputs: `stepP:p11a:cs-cutoff, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, bpP:p11a:c2-conv#bracket, bpP:p11a:sec-hom#lambda, bpP:p11a:homological-maximal`.
- **`stepP:p11a:cs-flow`** — (ii): Phi_b holomorphic on D_+ jointly, with displacements A_1, A_eta, simple form, canonical, periodic, real if the data are real, inverse
  Inputs: `stepP:p11a:cs-hom, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, bpP:p11a:affine-flow`.
- **`stepP:p11a:cs-taylor`** — H o Phi(z) = N_b(z) + {N_b,phi}(z) + R(z) + calR(z), calR = integral_0^1 {u_t,phi}(X_phi^t z) dt, u_t = (1-t) w + R; hence H o Phi = N_+ + R_+ with R_+ = (R - R_*) + calR, holomorphic in (theta,eta,b), periodic, real if the data are
  Inputs: `bpP:p11a:affine-flow, N:bpN:p5:taylor, stepP:p11a:cs-hom, stepP:p11a:cs-cutoff, stepP:p11a:cs-flow, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, bpP:p11a:c2-conv#bracket`.
- **`stepP:p11a:cs-u`** — ¦w¦ <= 4(1+E_T) eps and ¦u_t¦ <= U := eps(5+4E_T) (<= 9 eps)
  Inputs: `stepP:p11a:cs-cutoff, stepP:p11a:cs-taylor, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, K:bp:p1:ext-integral`.
- **`stepP:p11a:cs-bracket`** — ¦d_(theta_i) u_t(z_t)¦ <= U/sigma, ¦d_(eta_i) u_t(z_t)¦ <= 4U/s, and ¦{u_t,phi}(z_t)¦ <= N(4N+5) U A_1/sigma
  Inputs: `bpP:p11a:affine-flow, K:bp:p1:ext-cauchy, stepP:p11a:cs-u, stepP:p11a:cs-flow, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, bpP:p11a:c2-conv#bracket`.
- **`stepP:p11a:cs-assemble`** — ¦calR¦ <= N(4N+5) U A_1/sigma; hence (iii) both forms of the bound for norm(R_+)_(D_+) (using q^2/(1-q)<=2q^2, (5+4E_T)(1+E_T)<=18)
  Inputs: `stepP:p11a:cs-bracket, stepP:p11a:cs-u, stepP:p11a:cs-hom, stepP:p11a:cs-taylor, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, bpP:p11a:sec-hom#lambda, stepP:p11a:cs-cutoff, K:bp:p1:ext-integral`.
- **`stepP:p11a:cs-lip`** — ¦D Theta_b - 1¦_inf <= e^(Lambda_R) - 1 with Lambda_R = 2T(1+E_T) eps Lambda_(r-d)/(D s), Theta_b(theta+k) = Theta_b(theta)+k
  Inputs: `bpP:p11a:real-lipschitz, bpP:p11a:homological-maximal, stepP:p11a:cs-hom, stepP:p11a:cs-flow, bpP:p11a:c2-conv#data, bpP:p11a:domain-def, bpP:p11a:sec-hom#lambda`.
- **`stepP:p11a:cs-param`** — parameter Cauchy estimates (v) on E+t'
  Inputs: `bpP:p11a:param-cauchy, stepP:p11a:cs-assemble, stepP:p11a:cs-flow, stepP:p11a:cs-hom, bpP:p11a:c2-conv#data, bpP:p11a:domain-def`.

## 5. Departures, source gaps and blueprint issues

| ID | Exact location and quoted text | Why / design action |
|---|---|---|
| SG1 | p11 L75, “By (e1) varrho extends holomorphically” and “identities ... hence on D” | The imported holomorphic-to-real restriction theorem is in the opposite direction. Prove `p11_complexification` from the real analytic power series by complexifying each finite-dimensional real coefficient, shrinking the radius for absolute convergence; prove `p11_real_slice_identity` by successive one-variable identity theorems. Apply entrywise to the finite matrix identities. This is new proof work, not a new source axiom. |
| SG2 | p11 L83, “hence |R4| <= sup|R4| (|z|/rz)^4” | First-derivative Cauchy is insufficient. `p11_radial_schwarz` is supplied separately, using Taylor vanishing to obtain the order-k little-o premise of Mathlib `Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO`, with the closed target ball provided by the sup bound; handle k=0 separately. |
| SG3 | p11a2 L237, “smooth, bounded and Lipschitz, so solutions are global” | `x-ode` is only linear. `p11_bounded_global_flow` uses `ODE.gen_local`, bounded displacement, a compact ball on every finite time interval and `gen_continuation_compact`. Uniqueness is `gen_uniqueness`. No complex strip loss is paid on the real global orbit. |
| SG4 | p11a2 L239, “Y(t)=D Theta^t(theta) solves Y'=...” | Linear ODE existence does not identify this derivative. Prove `p11_global_variational` on short flow charts by differentiating the integral equation (initial-data Picard differentiability), extend over finitely many charts on a compact time interval and use the chain rule; then Gronwall. |
| SG5 | p11a2 L248, “real ... if reality is wanted”; L267/L287, “for real b ... real theta” / “real-lipschitz” | Optional reality does not imply a real angle flow. Separate `canonical_step_real` with an explicit `p11Real ... R` guard. Counter-mechanism: a complex Fourier mode gives a complex homological generator on real angles. Do not assert a global real-flow estimate for that generator. `wrapper` supplies reality from the physical Hamiltonian. No frozen statement is weakened or given a new premise. |

All five actual SOURCE_GAP notes in this scope have an explicit design action. The aniso-avg note says
“no SOURCE_GAP node”; it still needs an original rectangular proof, not an unverified application of
N's isotropic theorem. The graph review itself remains FAIL for its own graph-input reasons; this document
does not change that verdict.

Other recorded conventions/departures:

- The divided-difference/one-dimensional proof replaces the Bakhtin citation and keeps the blueprint's
  `2q*(eps/beta)^(1/q)`, not Rus01's Chebyshev constant. With `ContDiffOn` on a closed interval, the
  derivative lower bound is needed only on the open interval: dropping endpoints gives a stronger true lemma.
- The circumscribed cube gives `(2r)^(N-1)`; two tensor gauges avoid silently paying a polarization constant.
- The sup-norm Fourier cutoff uses the blueprint's c_N, not Rus05 multipliers. Loss is exactly d_T,
  including `N*log(pi*T)`; choosing d only from log(1/alpha) would omit the growing polynomial tail.
- Frozen objects are referenced literally. `P11Phase` is an abbreviation; `domain_def` is an abbreviation
  through existing `Weighted.Dom`. `p11PolarC` is a new complex extension; prove its real restriction is
  the existing `polarMap` conjugated by slow-angle multiplication by 2pi and slow-action division by 2pi.
  `p11PolarR` is only its real restriction; never assume a new chart equals the established one.
- Finite scalar cutoffs are factored componentwise for vector inputs. Companion vector lemmas must bound
  the max norm without multiplying the Fourier sup constant by the number of components.
- Larger output specifications are factored into companion results (e.g. `cutoff_coefficients`,
  `canonical_step_simple_inverse`, `canonical_step_real`, `canonical_step_param`). The registry retains
  every original clause, including homological uniqueness, reality, entire theta extension, average bounds,
  simple-flow block derivatives, parameter holomorphy and rectangular action-block displacements.
- **Amendment D29 (2026-10-28, found by the P11A-C8 prover, ruled by the main orchestrator).** The last
  clause of `cutoff_coefficients` (Appendix) was false as first signed: `∀ z, p11Cutoff T R z = p11R0 T R
  (z.1.1,z.2) + ∑ i, p11R1 T R (z.1.1,z.2) i * z.1.2 i` lacks `z.2 ∈ B`. Off `B`, `R` is unconstrained by
  `p11Admissible`, and the truncation integrates over the torus. Counterexample: `R((x,η),b) = f(x) + η₁ g(x)`
  with `f` non-integrable and `g = 1 - f` gives cutoff `1` at `η₁ = 1` but `R0 = R1 = 0`. The clause now reads
  `∀ z, z.2 ∈ B → …`; the name is unchanged, and `cs-cutoff` uses it only on `B`. The signature file
  `.drafts/design/P11ASignatures.lean` carries the same amendment. Package C8 is split: C8 proves
  `canonical_step`, `canonical_step_param`, `canonical_step_real` and the helper `p11_cutoff_coeff`; round C8b
  (same branch) adds the amended `cutoff_coefficients` and `canonical_step_simple_inverse`.
- Do not replace the finite-stage divisor by two comparisons to the limit. Use the finite retained-set
  telescoping sum with shell UPPER endpoint T_m, including m=0, from `finite_divisor`.
- Constants for `p11Order` are chosen before nu2, which is chosen before epsilon. K5 is a LOWER bound
  on the admissible threshold, K6 a displacement power with beta-uniform constants. An upper threshold
  or merely C0 closeness of the normalized frequency cannot pay these obligations.

Pinned-paper issues below are inherited reports in the blueprint, not newly independently checked PDF errata:

| Source location / quote | Existing report and relevance |
|---|---|
| CP09 (17),(28), Prop2, “1/2” on the secular linear term | E-P-CP09-1: inconsistent with half(x²+y²)=rho; use Omega/(2pi) once. |
| CP09 p21 after (47), “epsilon0 <= c epsilon^nu0” | E-P-CP09-2: upper budget does not imply the required lower budget. |
| CP09 (27), polydisc radius “|rho0|/2” | E-P-CP09-3: may reach a zero square-root component for unequal multi-component centers; equal-component shell here avoids it. |
| CP09 Lemma3, “K intersect D” | E-P-CP09-4: use parameter preimage of the frequency good set, not intersection of unrelated carriers. |
| CP09 Lemma7, fast variables unchanged / repeated secular term | E-P-CP09-5: not used by this averaging route. |
| CP09 p17, “Psi_epsilon=Psi_0+O(epsilon)” | E-P-CP09-6: C0 does not control a finite-order amount; unscaled J jets are required. |
| Rus05 p30 (46), “E(T rho)” after dimension rescaling | R05-2: review reports E(T rho/n); bypassed by l1 cutoff. |

The earlier CP09-7 domain complaint is withdrawn in the blueprint: restricting a valid pulled-back domain
is legitimate. Keep only the explicit conformal normalization/time bookkeeping. No new pinned-paper erratum
or frozen-declaration defect is asserted here.

## 6. Modules, import DAG and packages

All paths in the table are under `KAM/Planetary/`, all include `.lean`. Each package is 150-800 proof lines;
no single implementation module is planned above 800 lines. Split before the 1500-line hard cap. A facade
may re-export the submodules but must not import a provider or a draft theorem anchor.

| Package | Wave | Module(s) | Lines | Exact inputs / prior packages |
|---|---:|---|---:|---|
| P11A-W0 | 1 | `WeakMeasure/Basic` | 400 | `Interfaces.Norms`, Mathlib iterated derivatives, compact maxima |
| P11A-W1 | 2 | `WeakMeasure/Stability` | 450 | W0; iterated Leibniz, Cauchy-Schwarz; stability and M_bound |
| P11A-W2 | 2 | `WeakMeasure/FiniteType` | 250 | W0; Part10 `finite_type`, `cp09_lemma1`, `rnd` exact port |
| P11A-W3 | 1 | `WeakMeasure/DividedDifference` | 450 | `Lagrange.interpolate`, Rolle; interpolation coefficient helper |
| P11A-W4 | 2 | `WeakMeasure/ScalarSublevel` | 450 | W3; distribution-function continuity, quantile nodes and gaps |
| P11A-W5 | 3 | `WeakMeasure/MeasureTools`, `WeakMeasure/BallSublevel` | 650 | W0,W4; Householder completion, determinant image measure, Tonelli |
| P11A-W6 | 4 | `WeakMeasure/Sublevel` | 550 | W1,W5; finite cube cover and explicit ceiling/radius inequalities |
| P11A-W7 | 5 | `WeakMeasure/Diophantine` | 400 | W6; countable subadditivity, compact intersection |
| P11A-W8 | 6 | `WeakMeasure/PowerLaw`, `WeakMeasure/Bridge`, `WeakMeasure/ChartScaling` | 700 | W7; `KAM.Measure.lattice_sum`, `modeSize_euclid_compare`; limit_bridge |
| P11A-C0 | 1 | `MaximalStep/Basic`, `MaximalStep/Constants` | 400 | existing Weighted/frozen objects; lambda lattice identity |
| P11A-C1 | 2 | `MaximalStep/FourierCutoff` | 500 | C0; `decay_boundary_radius`, vector Fourier reconstruction, `lattice_count` |
| P11A-C2 | 3 | `MaximalStep/Loss` | 350 | C1; geometric and arithmetico-geometric sums; monotonic loss |
| P11A-C3 | 2 | `MaximalStep/Taylor`, `MaximalStep/Parameter` | 600 | C0; one-variable power series, mixed-polydisc Cauchy j^j |
| P11A-C4 | 7 | `MaximalStep/Cutoff`, `MaximalStep/Divisor` | 500 | C1,C3; W8 for divisor_wide; mean value on each polydisc |
| P11A-C5 | 8 | `MaximalStep/Homological` | 550 | C4; finite coefficients, averages and parameter derivatives |
| P11A-C6 | 2 | `MaximalStep/AffineFlow`, `MaximalStep/ParameterFlow` | 750 | C0; `Canonical.flow_a/b/c/d/e`, `flow_symplFormC`; no W/measure dependency |
| P11A-C7 | 3 | `MaximalStep/GlobalRealFlow`, `MaximalStep/RealFlow` | 750 | C6; nonlinear continuation and variational bridges, Gronwall |
| P11A-C8 | 9 | `MaximalStep/Step`, `MaximalStep/StepParameter` | 700 | C5,C6,C7; integral Lie identity, explicit U/bracket estimate; `cutoff_coefficients` amended (D29, guard `z.2 ∈ B`), delivered in round C8b |
| P11A-P0 | 3 | `Preparation/AnalyticExtension`, `Preparation/Schwarz` | 600 | C3; real analytic coefficient complexification, identity theorem, radial Schwarz |
| P11A-P1 | 7 | `Preparation/Basic`, `Preparation/Working`, `Preparation/BasePoint` | 550 | W1,W2,W8,P9; P10 exact physical-frequency interface; norm_dict/select |
| P11A-P2 | 8 | `Preparation/Holomorphic`, `Preparation/Polar` | 750 | P0,P1; P8/9 and existing P6/7; P1 hol_chart and exact period-one lattice |
| P11A-P3 | 3 | `Preparation/RectangularBracket` | 450 | C0; `Weighted` coefficient Cauchy and algebra |
| P11A-P4 | 4 | `Preparation/RectangularAverage` | 750 | P3,C6; P2 direct/split/nfb adaptation and N6/7 exact gauge adapters |
| P11A-P5 | 9 | `Preparation/Fast`, `Preparation/LogBounds` | 500 | P2; P2 osc_averaging, weighted spectator conversion, e4 |
| P11A-P6 | 4 | `Preparation/PolarAverage` | 650 | C3,P0; Taylor coefficients and termwise integration; e5 |
| P11A-P7 | 10 | `Preparation/Slow` | 650 | P4,P5,P6; pure-slow and mixed-divisor estimates separately |
| P11A-P8 | 11 | `Preparation/Prepared`, `Preparation/Amount` | 750 | P7,W1; full unscaled J jets, vector and scalar jets including zero; split modules 500/250 |
| P11A-P8D | 11 | `Preparation/Datum` | 300 | P8; same chosen Q, fixed geometry, A1-A4 and amount smallness; exact 11a5 bridge after reconciliation |
| P11A-P9 | 2 | `Preparation/ForwardTube` | 350 | existing product Poincare chart, circularPoint, compactness |
| P11A-P10 | 12 | `Preparation/Wrapper` | 500 | P8D,P9; neighbouring Part11a3-5 K1-K6; P1 physical transport and measure |

Wave numbers impose the complete dependencies; an actual launch waits for named external owners too.
C4's cutoff portion can land before W8; its divisor_wide companion waits for W8. Similarly C8 can
land the complex statement before C7's global real-flow estimate. The rectangular branch does not import
the maximal step or the weak-measure layer; it is a separate weighted-norm argument.

The import DAG consists exactly of each row's prior-package edges plus the named existing inputs.
Within a row, import only from earlier rows or earlier listed modules when explicitly needed; in particular
`WeakMeasure` imports no `Preparation`, `MaximalStep` imports no `Preparation`, and `Preparation/Wrapper`
imports no provider or frozen theorem anchor. P11a3 consumes C8/W8; P11a4/5 consumes that iteration;
`Preparation/Wrapper` consumes P11a4/5. There is no edge from their iteration back to preparation.

## 7. Provider boundary and validation

No provider is created. Part13 consumes `KAM.Planetary.wrapper` with the literal physical input fields
(n>=2, G,m0,m positive, ordered positive axes, eta>0), casts `n+n=n*2` using the existing phase equivalence,
and invokes its `fixkol_assembly` to obtain the frozen P-FIXED conclusion. This scope supplies no
binder to a frozen provider and does not seal P-FIXED. All frozen files and manifest entries are read-only.

Appendix A is a standalone design module: definitions are explicit; every theorem body is `sorry`.
It prints axioms for sublevel/canonical_step/wrapper and, in Revision 2, prepared/data_star; these include `sorryAx`.
Successful elaboration verifies signatures, not proofs. The common design brief authorizes sorry in this
untracked scratch/design artifact only; implementation code still obeys AGENTS.md rule 4.

Revision 1 validation receipt (historical; superseded by Revision 2 below):

- `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p11a .drafts/scratch/P11ASignatures.lean`: exit 0; 58 warnings, all exactly `declaration uses sorry`; zero errors or other warnings. The final 1316-line source has SHA-256 `40f6b495348ae7b10bf06bf8837bba7433b1bb648f98d17602eb780904690983`.
- Revision 1 signatures were copied byte-for-byte to `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`; its then-current Appendix A matched the checked copy.
- `#print axioms` for `sublevel`, `canonical_step`, `wrapper`: `[propext, sorryAx, Classical.choice, Quot.sound]`, as expected for design signatures.
- Static contract checks: PASS, all 164 scoped nodes occur exactly once in the mapping table, 58 Revision 1 theorem bodies are all `sorry`, no resource overrides or forbidden declarations, no trailing whitespace, file below 1500 lines.
- `PATH=.drafts/scratch/sig-lint-bin:$PATH sh scripts/lint_sources.sh`: exit 0 (the actual run also supplied the completed signature gate PID to serialize the ABI subcheck). Output: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`.
- `git diff --check`: PASS (rerun on staged design before commit).

The shared build snapshot has no `Canonical.CompositionIntegral.olean` or `Planetary.Newtonian.Tube.olean`.
The signature file therefore imports neither module: its `p11Zeta` helper unfolds
`min eta (axisGap a/6)` literally instead of redefining either helper. Implementation uses the delivered
`tubeRadius`/`axisGap` names after that module is built. The maximal step uses the arbitrary-gauge `Canonical.taylor_lie`/`taylor_poschel` from `Canonical/Lie`,
not `composition_integral` (which requires weighted ComposeData). That weighted package is a separate
rectangular-averaging proof dependency and is not needed to elaborate these theorem signatures. The lint ABI subcheck also invokes Lean: its `lake env lean` subprocess is routed through the same
gate by a scratch PATH wrapper, which removes itself before calling the gate. This runs the unmodified
`scripts/lint_sources.sh` without an unauthorized direct elaboration.
The patch is selected inside one eighth of the independently proved forward-tube action margin
`p11PhysicalDelta`. `p11ChartInput` is the literal inverse rotation lift after T1, built with
frozen `assemble` and the existing product Poincare chart; its real SO(n), spectral, lattice and
collision-free properties remain explicit output obligations.
The signatures artifact and scratch log
remain untracked. The design commit contains only this Markdown file.

## 8. Risks and instructions to provers

- Step nodes must be discharged against their full registry contract. An aggregate stage signature is not
  permission to omit a companion result; the source clause remains binding even when factored out.
- Upstream Part2/8/9/10 and Part11a3-5 are reconciliation points. Do not invent numerical hypotheses or
  assume a secular nondegeneracy, a Diophantine point, a lower KAM budget, or a small torus displacement.
  The patch helper already specifies the physical spectral map; prove its bridge to the returned Part10 eigenvalue labelling at that port.
- The real polar chart is a bridge to existing `polarMap`, not an independent chart proof. The complex
  extension may use principal roots only on the componentwise positive-real shell.
- Euclidean multilinear gauges need a bounded/attained supremum proof. Avoid installing a Euclidean norm
  instance on the Pi type. At order zero verify evaluation conventions explicitly.
- Borel saturation and chart image measure require the P1 hypotheses, including lattice injectivity and
  local analytic inverse. Compactness alone of parameter space does not prove the whole union compact.
- Joint parameter holomorphy of the flow must be proved using the augmented field on small local parameter
  discs. The full parameter tube need not have any positive uniform interior margin.
- Keep arithmetic lemmas separate from analytic proofs. Default-heartbeat failure calls for splitting a
  proof or interface, never a resource override. No conclusion-shaped field may be added while implementing.

## 9. Hard rules for every Lean proof brief (verbatim)

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


## Revision 2

This revision addresses all five findings and three notes of
[`DESIGN-P11A-design-audit-1.md`](DESIGN-P11A-design-audit-1.md). These are corrections to design contracts;
the independent audit remains a historical FAIL, and no theorem proof or frozen anchor is closed.

| Finding | Resolution in the exact signatures | Implementation owner / consumer |
|---|---|---|
| F1 (major), source-local premises | `homological_maximal`, `homological_maximal_real`, `homological_maximal_param` restrict input and uniqueness-competitor truncation to `univ ×ˢ B` or the parameter tube. `aniso_bracket`, `aniso_avg` restrict periodicity to their own strip/action domains. The finite-sum solution remains explicit; its entire-angle extension follows from that construction. | C5; P3/P4. Values outside the source domains are unconstrained. |
| F2 (major), prepared datum | The base `P11PreparedSpec` now states the unscaled J estimate for every `‖rho‖ < 5/4`, `‖J-J0‖ < s2/4`. `P11PreparedFullSpec` also identifies `checkW` there with `p11SlowNormalizedFreq`, the actual derivatives of `h0+g2`. It exports vector diagonal jets through mu including order zero, and scalar order-zero bounds alongside the original positive-order full-tensor bounds. `prepared`, `p11PreparedData`, `amount` and `data_star` all use the full spec and the same selected Q. `data_star` exports A1-A4, fixed geometry and `0 < beta ≤ min 1 M`. | P2 chooses the enlarged L; P8 proves the full preparation/amount; P8D assembles it; Part11a5 consumes it. |
| F3 (major), polar clause (d) | `polar_average_linear`, `polar_average_normalization`, `polar_extension_unique` accompany `polar_avg`. They give linearity on analytic input domains, both normalizations including `rho/(2*pi)`, and uniqueness of the extension. | P6; `as_osc` uses these exports. |
| F4 (major), rectangular field | `aniso_field` exports the frozen `hamiltonianVectorFieldℂ` estimate in the scaled norm with separate action weights rho1/rho2. It supplements `aniso_bracket` under local periodicity. | P3; P4's R2 flow estimate. |
| F5 (moderate), complete chart lemma | `chart_scaling` retains amount clause (a). `chart_scaling_geometry`, `chart_scaling_jets`, `chart_scaling_good` export diameter/thickening/volume, both tensor identities, and good-set/excluded-measure transport. `chart_scaling_upper` and `chart_scaling_closeness` explicitly package (b),(c), including the rechecked threshold `max 1 (lambda^mu)*theta ≤ beta'/2`. | W8, new `WeakMeasure/ChartScaling.lean`; preparation rescalings and Part11a5. |

For F2, `P11SecularFullSpec` strengthens the freely selected initial L to bound the Euclidean size
of `Fin.append omega ((2*pi)^-1 • Omega)` on its original complex ball. This is obtained by enlarging L
before any averaging constant, nu or epsilon is chosen. The source only asks for a sufficiently large L;
this is a declared stronger output, with no extra physical premise. Set
`M0* = p11M0 n mu L = (2*n+1)^(mu+1)*(2*L+1)` before nu and epsilon. The proof pays the
Euclidean/max comparison in each tensor direction; it must never identify those gauges. Finite-order
Cauchy estimates and further shrinking the epsilon threshold give the vector jet bound. The scalar
constant remains `M* = 2^(mu+1)*(2*L+1)^2`, and `C1 = 2*L+1`. Neither constant depends on nu.

The datum exported by `data_star` is a conjunction of the actual analytic and quantitative outputs,
with `Q := p11PreparedData D nu eps c`; the amount, Hamiltonian and jet bounds refer to this same Q.
It does not posit an admissibility conclusion as a premise. Once Part11a5 delivers its exact admissibility
predicate, P8D must prove a typed bridge from these conjuncts into it. The K5 lower budget and K6
constants then come from that reconciled API, with their original quantifier order. They remain upstream
proof obligations, and are not claimed proved by the existence of a sorry-bodied package.

For F3, linear combinations of arbitrary totalized nonintegrable inputs are not used. Prove integrability
of the analytic integrands on the compact angle cube, then the raw identities. Fix each J and apply
`polar_extension_unique` on the connected action polydisc to transport the identities to the extensions.
This yields the source's linear analytic averaging operator without assuming connectedness of D.

For F5, apply `chart_scaling_jets` to `p11scalar rho w direction` for both rho=1 and rho=2, and to
`p11scalar rho (wt k) direction - p11scalar rho w direction` for closeness. Polynomial composition
supplies their `ContDiffOn` premises from D1-D3. Use `chart_scaling_upper` with k=mu+1 and
`chart_scaling_closeness` with mu and the diagonal bound `p11JetBound true` supplied by D3;
geometry transfers the thickened set. Use the diagonal identity from `chart_scaling_jets` directly,
with no full-tensor premise or polarization factor. The numerical recheck is mandatory.
D2's `M' ≥ beta'` follows from `M ≥ beta`, `max 1 (lambda^(mu+1)) ≥ 1` and
`min 1 (lambda^mu) ≤ 1`. No chart-invariance assertion replaces this calculation.

N1 is retained: `canonical_step_real` requires reality on R, supplied by the physical construction.
The recorded blueprint defect is still p11a2 L248/L287 (SG5 above); it is not a frozen-statement change.
N2 is retained as an explicit launch gate: all upstream ports in Section 3 must reconcile by exact name
and type. In particular the secular Hessian identity, sorted spectrum/SO(n) lift, fixed-norm derivative
estimate, finite retained-set divisors, lower monotone budget and displacement power remain required.
N3 is retained as a proof gate: W0 must establish boundedness/attainment for each supremum/infimum on
positive-dimensional unit spheres and nonempty compact patches, and choice specifications must be
proved at the positive-small-epsilon thresholds before using selected stage data. The strengthened
`holo_chart` selects from `P11SecularFullSpec`; `prepared`, `amount`, `data_star` select from
`P11PreparedFullSpec`. Default branches on arbitrary total inputs prove no source claim.

The source registry in Section 4.1 remains literal. These explicit companions, rather than prose-only
obligations, now cover its omitted clauses. The only additional package is P8D; the revised schedule has
30 packages and the same 12 waves. W8's ChartScaling imports only W0 and Mathlib affine calculus/measure
facts; the other W8 modules keep their prior dependencies. P8D follows P8 within wave 11. P6's new
identities use its existing analytic/identity inputs; P3's field estimate uses its coefficient Cauchy input.
All implementation modules remain below 1500 lines, and each package stays in the 150-800 line range.
No new pinned-paper erratum is asserted. F1-F5 were design omissions or departures; F2's former
narrowing is removed, and the enlarged initial L is the only new declared output strengthening.

Revision 2 validation receipt (historical snapshot, 2026-10-28; file hashes and equality refer to R2):

- Final targeted check: `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p11a .drafts/scratch/P11ASignaturesR2.lean`, exit 0. Exactly 67 warnings, all `declaration uses sorry`; zero errors or other warnings. Log: `.drafts/scratch/P11A-r2-check.log`.
- Exact final signatures: 1319 lines, 171 named declarations, 67 theorem bodies all `sorry`; SHA-256 `1a4b339d7d9008ff8d1aa5f2a85addc1b0f3476c40ab8fbf7e922cf3f9be8493`. Appendix A, the scratch copy and `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` are byte-identical. Blank separators were compressed to keep the required single-file scratch comfortably below 1500 lines.
- `#print axioms` for `sublevel`, `canonical_step`, `wrapper`, `prepared`, `data_star`: each reports `[propext, sorryAx, Classical.choice, Quot.sound]`. This is signature elaboration, not proof closure.
- `PATH="$PWD/.drafts/scratch/sig-lint-bin:$PATH" sh scripts/lint_sources.sh`: exit 0; `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. Log: `.drafts/scratch/P11A-r2-lint.log`. The existing wrapper routes the lint ABI elaboration through `inp_sig_check.sh`; it ran after the first revision elaboration and before the final signature check.
- Static checks: all 164 unique graph rows preserved, 30 packages, exact-copy equality, 67 sorry-only theorem bodies, no forbidden declarations or resource overrides, no trailing whitespace, signature length below 1500. `git diff --check` and `git diff --cached --check`: exit 0.
- No implementation module changed, so the signatures check is the applicable targeted Lean check under the common design brief; no library build or rebuild was run. Only this document is committed; the independent audit remains untouched and untracked.

## Revision 3

This revision responds to [`DESIGN-P11A-design-audit-2.md`](DESIGN-P11A-design-audit-2.md).
Audit 2's sole remaining finding is F5-R2 (moderate); its resolutions of F1-F4 and the other F5
clauses are preserved. Both audit reports remain historical FAIL reports, unchanged. This revision
requests a new independent review and claims signature elaboration only, with no proof closure.

| Finding / note | Revision 3 resolution |
|---|---|
| F5-R2 (moderate), source D3 gauge mismatch | Both the input `hb` and output of `chart_scaling_closeness` now use `p11JetBound true`. Its domain, regularity and numerical recheck remain unchanged. This is the exact diagonal companion proposed in audit 2; `chart_scaling_upper` retains the full-tensor D2 bound under its distinct name. The Revision 2 application explanation above is corrected accordingly. |
| F1, source-local premises (resolved in audit 2) | Preserve all domain-restricted polynomial, uniqueness and periodicity premises; arbitrary extensions remain unconstrained. |
| F2, full preparation/datum (resolved in audit 2) | Preserve the full unscaled domain, actual slow-stage derivative identification, zero/vector jets and the same selected Q in prepared/amount/data_star. No stronger input premise is introduced. |
| F3, polar clause (d) (resolved in audit 2) | Preserve analytic-domain linearity, constant/quadratic normalization and fibrewise holomorphic extension uniqueness. |
| F4, rectangular field (resolved in audit 2) | Preserve the frozen Hamiltonian-field estimate and separate action-block weights. |
| F5, remaining chart clauses (accepted in audit 2) | Preserve geometry, both jet identities, amount, D2 upper size, good-set and excluded-measure transport. |
| N1, reality guard | Retain `canonical_step_real`'s explicit guard and the p11a2 L248/L287 source-gap report; physical uses must supply reality. |
| N2, upstream gates | Retain every exact-interface/proof obligation in Section 3, including the future admissibility bridge. Sorry packages certify none of them. |
| N3, totality and choice | Retain boundedness/attainment and positive-small-epsilon choice gates. No theorem uses a default selector branch as evidence. |
| Audit validation limitation | The corrected companion is included in the complete R3 gated signature check below; audit 2's exit-143 optional probe remains a historical unsuccessful check. No new Mathlib dependency or name-check claim is needed. |

For the concrete D3 application fix a mode k and Euclidean unit direction c, and set
`f := p11scalar rho (wt k) c - p11scalar rho w c`, `E := p11thick K v`, and
`A y := y0 + lambda • y`. The existing D3 closeness field supplies `p11JetBound true mu E f theta`
(with theta equal to its supplied bound). Polynomial composition gives `ContDiffOn` on V.
The diagonal half of `chart_scaling_jets` gives, for every j <= mu and A y in E,
`p11dg (f ∘ A) j y = lambda^j * p11dg f j (A y)`.
Since lambda > 0 and theta >= 0, this is at most `max 1 (lambda^mu)*theta`; the explicit
`hrecheck` then gives beta'/2. The output is precisely diagonal D3 on the preimage thickening,
identified by `chart_scaling_geometry`. There is no conversion between the two tensor gauges and
no change to D3, beta', the blueprint, or a frozen declaration.

The package/module schedule remains 30 packages in 12 waves. W8 owns this corrected companion;
its inputs already include W0 and affine calculus. All earlier source issues and upstream gates
remain recorded. F5-R2 is a design adapter mismatch, not a pinned-paper erratum.

Revision 3 validation receipt (2026-10-28):

- `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p11a .drafts/scratch/P11ASignaturesR3.lean`: exit 0; 67 warnings, all `declaration uses sorry`; no errors or other warnings. Log: `.drafts/scratch/P11A-r3-check.log`.
- Final signatures: 1320 lines, 171 named declarations, 67 theorem bodies all `sorry`; SHA-256 `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092`. Appendix A, delivered signatures and R3 scratch copy are byte-identical. The only theorem-type delta from R2 is the two diagonal gauge selectors in `chart_scaling_closeness`.
- `#print axioms` for `sublevel`, `canonical_step`, `wrapper`, `prepared`, `data_star`, and the corrected `chart_scaling_closeness`: each returned `[propext, sorryAx, Classical.choice, Quot.sound]`. This validates types only.
- `LEAN_NUM_THREADS=1 PATH="$PWD/.drafts/scratch/sig-lint-bin:$PATH" nice -n 5 sh scripts/lint_sources.sh`: exit 0; `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. Log: `.drafts/scratch/P11A-r3-lint.log`. The existing PATH wrapper routed ABI elaboration through the required gate after the signature check completed; the runs were sequential.
- Static checks: all 164 unique graph mapping rows unchanged; 30 packages / 12 waves, each 150-800 lines; signature length below 1500; sorry-only theorem bodies; no forbidden declarations, resource overrides or trailing whitespace; Appendix/scratch/delivery equality. `git diff --check` and `git diff --cached --check`: exit 0 before commit.
- No implementation module was changed; the complete signature elaboration is the applicable targeted Lean check. No library build/rebuild was run. Blueprint input hashes still match Section 1; both audit reports are untouched. Commit scope is this design document only.

## Appendix A. Exact signatures

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module
public import Mathlib
public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.Weighted.Projections
public import KAM.Weighted.Parametric
public import KAM.Canonical.FlowInverse
public import KAM.Canonical.Symplectic
public import KAM.Planetary.Poincare.Product
public import KAM.Frozen.Planetary.Defs.CircularTube
public import KAM.Frozen.Planetary.Defs.SecularAverage
public import KAM.Frozen.Planetary.Defs.IsPhysicalTorus
/-!
# P11A design signatures
Draft only. All proof bodies are sorry. No provider or theorem anchor is imported.
The scratch copy is elaborated only by inp_sig_check.sh.
-/
@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary
abbrev P11Vec (n : ℕ) := Fin n → ℝ
abbrev P11CVec (n : ℕ) := Fin n → ℂ
abbrev P11Phase (n : ℕ) := P11CVec n × P11CVec n
abbrev P11Family (n : ℕ) := P11Phase n × P11CVec n
/-- Explicit Euclidean lengths; retain the existing max norm instances. -/
abbrev p11euclid {n : ℕ} (x : P11Vec n) := KAM.Nekhoroshev.euclid x
def p11dot {m : ℕ} (c w : P11Vec m) : ℝ := ∑ i, c i * w i
def p11dotZ {m : ℕ} (k : Fin m → ℤ) (w : P11Vec m) : ℝ :=
  ∑ i, (k i : ℝ) * w i
def p11dotC {m : ℕ} (k : Fin m → ℤ) (w : P11CVec m) : ℂ :=
  ∑ i, (k i : ℂ) * w i
/-- Closed Euclidean thickening, not max-norm Metric.cthickening. -/
def p11thick {n : ℕ} (K : Set (P11Vec n)) (v : ℝ) : Set (P11Vec n) :=
  {y | ∃ x ∈ K, p11euclid (y - x) ≤ v}
/-- Order zero is evaluated on the unique empty tuple. -/
def p11dg {n m : ℕ} (f : P11Vec n → P11Vec m) (j : ℕ) (y : P11Vec n) : ℝ :=
  sSup {v | ∃ a : P11Vec n, p11euclid a = 1 ∧
    v = p11euclid (iteratedFDeriv ℝ j f y (fun _ => a))}
def p11op {n m : ℕ} (f : P11Vec n → P11Vec m) (j : ℕ) (y : P11Vec n) : ℝ :=
  sSup {v | ∃ a : Fin j → P11Vec n, (∀ i, p11euclid (a i) ≤ 1) ∧
    v = p11euclid (iteratedFDeriv ℝ j f y a)}
def p11scalar {n m : ℕ} (rho : ℕ) (w : P11Vec n → P11Vec m)
    (c : P11Vec m) (y : P11Vec n) : P11Vec 1 :=
  fun _ => (p11dot c (w y)) ^ rho
def p11maxJet {n m : ℕ} (mu : ℕ) (f : P11Vec n → P11Vec m) (y : P11Vec n) : ℝ :=
  sSup {v | ∃ j ≤ mu, v = p11dg f j y}
/-- index-def: precisely the scalar-family amount, rho=1 or rho=2. -/
def index_def {n m : ℕ} (rho mu : ℕ) (w : P11Vec n → P11Vec m)
    (K : Set (P11Vec n)) : ℝ :=
  sInf {v | ∃ c : P11Vec m, p11euclid c = 1 ∧
    ∃ y ∈ K, v = p11maxJet mu (p11scalar rho w c) y}
def p11JetBound {n m : ℕ} (diag : Bool) (mu : ℕ) (A : Set (P11Vec n))
    (f : P11Vec n → P11Vec m) (M : ℝ) : Prop :=
  ∀ j ≤ mu, ∀ y ∈ A, (if diag then p11dg f j y else p11op f j y) ≤ M
def p11eta (rho mu : ℕ) (M theta : ℝ) : ℝ :=
  if rho = 1 then theta else (2 : ℝ)^mu * theta * (2*M + theta)
/-- Common source geometry of S1-S3 and D1-D4. -/
structure P11Patch (n : ℕ) where
  K : Set (P11Vec n)
  V : Set (P11Vec n)
  v : ℝ
  n_pos : 1 ≤ n
  nonempty : K.Nonempty
  compact : IsCompact K
  openV : IsOpen V
  diameter_pos : 0 < Metric.diam K
  v_pos : 0 < v
  thick_sub : p11thick K v ⊆ V
/-- All fields are S1-S3, with regularity on the open V. -/
structure P11SublevelHyp {n : ℕ} (P : P11Patch n) (mu : ℕ)
    (g gt : P11Vec n → ℝ) (beta M : ℝ) : Prop where
  mu_pos : 1 ≤ mu
  beta_pos : 0 < beta
  size_ge : beta ≤ M
  g_smooth : ContDiffOn ℝ (mu+1) g P.V
  gt_smooth : ContDiffOn ℝ mu gt P.V
  finite_type : ∀ y ∈ P.K, beta ≤ p11maxJet mu (fun (x : P11Vec n) (_ : Fin 1) => g x) y
  size : ∀ j, 1 ≤ j → j ≤ mu+1 → ∀ y ∈ p11thick P.K P.v,
    p11op (fun (x : P11Vec n) (_ : Fin 1) => g x) j y ≤ M
  close : p11JetBound true mu (p11thick P.K P.v)
    (fun (x : P11Vec n) (_ : Fin 1) => gt x - g x) (beta/2)
def p11Csub (n mu : ℕ) (d v ratio : ℝ) : ℝ :=
  (2 : ℝ)^(n+2) * mu * (Real.sqrt n * d)^(n-1) * ratio *
    (1+(4+v⁻¹)*Real.sqrt n*d)
/-- The source's R-nondegeneracy; this is an interface to Part 10, not a new frozen object. -/
def p11RNondegenerate {n m : ℕ} (V : Set (P11Vec n)) (w : P11Vec n → P11Vec m) : Prop :=
  ∀ c : P11Vec m, c ≠ 0 → ∃ y ∈ V, p11dot c (w y) ≠ 0
theorem rank_compact {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {V K : Set (P11Vec n)} (hV : IsOpen V) (hconn : IsPreconnected V)
    (hK : IsCompact K) (hne : K.Nonempty) (hsub : K ⊆ V)
    {w : P11Vec n → P11Vec m} (hw : AnalyticOnNhd ℝ w V)
    (hr : p11RNondegenerate V w) {rho : ℕ} (hp : rho=1 ∨ rho=2) :
    ∃ mu : ℕ, 1 ≤ mu ∧ 0 < index_def rho mu w K := sorry
theorem stability {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {V A K : Set (P11Vec n)} (hV : IsOpen V) (hAV : A ⊆ V)
    (hKA : K ⊆ A) (hK : IsCompact K) (hne : K.Nonempty)
    {rho mu : ℕ} (hp : rho=1 ∨ rho=2) {w wt : P11Vec n → P11Vec m}
    (hw : ContDiffOn ℝ mu w V) (hwt : ContDiffOn ℝ mu wt V)
    {M theta : ℝ} (hM : 0 ≤ M) (ht : 0 ≤ theta)
    (hb : p11JetBound true mu A w M) (he : p11JetBound true mu A (wt-w) theta) :
    (∀ c, p11euclid c=1 → p11JetBound true mu A
      (p11scalar rho wt c-p11scalar rho w c) (p11eta rho mu M theta)) ∧
    index_def rho mu w K - p11eta rho mu M theta ≤ index_def rho mu wt K := sorry
theorem M_bound {n m : ℕ} (hn : 1 ≤ n) {V A : Set (P11Vec n)}
    (hV : IsOpen V) (hAV : A ⊆ V) {mu : ℕ} {w : P11Vec n → P11Vec m}
    (hw : ContDiffOn ℝ (mu+1) w V) {M : ℝ} (hM : 0 ≤ M)
    (hb : p11JetBound false (mu+1) A w M) :
    ∀ c, p11euclid c=1 → ∀ j, 1 ≤ j → j ≤ mu+1 → ∀ y ∈ A,
      p11op (p11scalar 1 w c) j y ≤ M ∧
      p11op (p11scalar 2 w c) j y ≤ (2 : ℝ)^j*M^2 := sorry
theorem divided_difference {q : ℕ} (hq : 1 ≤ q) {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ q f (Icc a b)) (t : Fin (q+1) → ℝ)
    (ht : StrictMono t) (ha : ∀ i, a ≤ t i) (hb : ∀ i, t i ≤ b) :
    ∃ xi ∈ Ioo (t 0) (t (Fin.last q)),
      (∑ i, f (t i) / ∏ j ∈ Finset.univ.erase i, (t i-t j)) =
        iteratedDeriv q f xi / q.factorial := sorry
theorem scalar_sublevel {q : ℕ} (hq : 1 ≤ q) {a b beta eps : ℝ}
    (hab : a < b) (hbeta : 0 < beta) (heps : 0 < eps) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ q f (Icc a b))
    (hlow : ∀ t ∈ Ioo a b, beta ≤ |iteratedDeriv q f t|) :
    volume {t ∈ Icc a b | |f t| ≤ eps} ≤
      ENNReal.ofReal (2*q*(eps/beta)^((q : ℝ)⁻¹)) := sorry
theorem ball_sublevel {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q)
    {V : Set (P11Vec n)} (hV : IsOpen V) {y0 a : P11Vec n} {r beta eps : ℝ}
    (hr : 0 < r) (ha : p11euclid a=1) (hb : 0 < beta) (he : 0 < eps)
    (hsub : {y | p11euclid (y-y0) ≤ r} ⊆ V) {g : P11Vec n → ℝ}
    (hg : ContDiffOn ℝ q g V)
    (hlow : ∀ y, p11euclid (y-y0) ≤ r →
      beta ≤ |iteratedFDeriv ℝ q g y (fun _ => a)|) :
    volume {y | p11euclid (y-y0) ≤ r ∧ |g y| ≤ eps} ≤
      ENNReal.ofReal (2*q*(2*r)^(n-1)*(eps/beta)^((q : ℝ)⁻¹)) := sorry
theorem sublevel {n mu : ℕ} {P : P11Patch n} {g gt : P11Vec n → ℝ}
    {beta M eps : ℝ} (H : P11SublevelHyp P mu g gt beta M)
    (he : 0 < eps) (he' : eps < beta/4) :
    volume {y ∈ P.K | |gt y| ≤ eps} ≤
      ENNReal.ofReal (p11Csub n mu (Metric.diam P.K) P.v (M/beta) *
        (eps/beta)^((mu : ℝ)⁻¹)) := sorry
/-- The mode-dependent maps live over the original patch, even when retained sets shrink. -/
def p11Good {n m : ℕ} (K : Set (P11Vec n))
    (wt : (Fin m → ℤ) → P11Vec n → P11Vec m) (psi : (Fin m → ℤ) → ℝ) :=
  {y ∈ K | ∀ k, k ≠ 0 → psi k ≤ |p11dotZ k (wt k y)|}
structure P11DioHyp {n m : ℕ} (P : P11Patch n) (rho mu : ℕ)
    (w : P11Vec n → P11Vec m) (wt : (Fin m → ℤ) → P11Vec n → P11Vec m)
    (beta M : ℝ) : Prop where
  m_pos : 1 ≤ m
  mu_pos : 1 ≤ mu
  convention : rho=1 ∨ rho=2
  beta_pos : 0 < beta
  size_ge : beta ≤ M
  regular : ContDiffOn ℝ (mu+1) w P.V
  perturbed_regular : ∀ k, k ≠ 0 → ContDiffOn ℝ mu (wt k) P.V
  amount : beta ≤ index_def rho mu w P.K
  size : ∀ c, p11euclid c=1 → ∀ j, 1 ≤ j → j ≤ mu+1 →
    ∀ y ∈ p11thick P.K P.v, p11op (p11scalar rho w c) j y ≤ M
  close : ∀ k, k ≠ 0 → ∀ c, p11euclid c=1 →
    p11JetBound true mu (p11thick P.K P.v)
      (p11scalar rho (wt k) c-p11scalar rho w c) (beta/2)
theorem diophantine_measure {n m rho mu : ℕ} {P : P11Patch n}
    {w : P11Vec n → P11Vec m} {wt : (Fin m → ℤ) → P11Vec n → P11Vec m}
    {beta M : ℝ} (H : P11DioHyp P rho mu w wt beta M)
    (psi : (Fin m → ℤ) → ℝ) (hp : ∀ k, k ≠ 0 → 0 < psi k)
    (hsmall : ∀ k, k ≠ 0 → (psi k / p11euclid (fun i => (k i : ℝ)))^rho < beta/4) :
    IsCompact (p11Good P.K wt psi) ∧
    volume (P.K \ p11Good P.K wt psi) ≤
      ENNReal.ofReal (p11Csub n mu (Metric.diam P.K) P.v (M/beta) * beta^(-((mu : ℝ)⁻¹))) *
        ∑' k : {k : Fin m → ℤ // k ≠ 0},
          ENNReal.ofReal ((psi k / p11euclid (fun i => ((k.val i) : ℝ)))^
            ((rho : ℝ)/mu)) := sorry
def p11CDio (n m rho mu : ℕ) (d v beta M tau : ℝ) : ℝ :=
  p11Csub n mu d v (M/beta) * beta^(-((mu : ℝ)⁻¹)) *
    (m : ℝ)^((rho : ℝ)/(2*mu)) * 2*3^(m-1) *
      (1+(((rho : ℝ)*(tau+1)/mu-m)⁻¹))
def p11GammaStar (m rho mu : ℕ) (beta C eps : ℝ) : ℝ :=
  min ((1/2 : ℝ)*(m : ℝ)^(-(1/2 : ℝ))*(beta/4)^((rho : ℝ)⁻¹))
    ((eps/C)^((mu : ℝ)/rho))
theorem power_law {n m rho mu : ℕ} {P : P11Patch n}
    {w : P11Vec n → P11Vec m} {wt : (Fin m → ℤ) → P11Vec n → P11Vec m}
    {beta M tau gamma : ℝ} (H : P11DioHyp P rho mu w wt beta M)
    (ht : (m : ℝ)*mu/rho-1 < tau) (hg : 0 < gamma)
    (hsmall : (Real.sqrt m*gamma)^rho < beta/4) :
    let G := p11Good P.K wt (fun k => gamma * KAM.Fourier.modeSize k ^ (-tau))
    let C := p11CDio n m rho mu (Metric.diam P.K) P.v beta M tau
    IsCompact G ∧ volume (P.K \ G) ≤ ENNReal.ofReal (C*gamma^((rho : ℝ)/mu)) ∧
    ∀ eps, 0 < eps → ENNReal.ofReal eps < volume P.K →
      gamma ≤ p11GammaStar m rho mu beta C eps →
      volume P.K - ENNReal.ofReal eps ≤ volume G := sorry
theorem limit_bridge {m : ℕ} {gamma tau : ℝ} (hg : 0 < gamma)
    {k : Fin m → ℤ} (hk : k ≠ 0) {u v : P11Vec m}
    (hu : 2*gamma*KAM.Fourier.modeSize k^(-tau) ≤ |p11dotZ k u|)
    (ht : ‖u-v‖ ≤ gamma*KAM.Fourier.modeSize k^(-tau-1)) :
    gamma*KAM.Fourier.modeSize k^(-tau) ≤ |p11dotZ k v| := sorry
theorem limit_bridge_diophantine {n m : ℕ} {K : Set (P11Vec n)}
    {wt : (Fin m → ℤ) → P11Vec n → P11Vec m} {gamma tau : ℝ}
    (hg : 0 < gamma) {b : P11Vec n}
    (hb : b ∈ p11Good K wt (fun k => 2*gamma*KAM.Fourier.modeSize k^(-tau)))
    (v : P11Vec m)
    (ht : ∀ k, k ≠ 0 → ‖wt k b-v‖ ≤ gamma*KAM.Fourier.modeSize k^(-tau-1)) :
    KAM.IsDiophantine gamma tau v := sorry
/-! ## Cutoff/step objects: existing domains, coefficients, truncation, bracket and flow. -/
def domain_def (n : ℕ) (r s : ℝ) (B : Set (P11CVec n)) : Set (P11Family n) :=
  KAM.Weighted.Dom n {0} s r ×ˢ B
def p11Admissible {n : ℕ} (r s : ℝ) (B : Set (P11CVec n)) (F : P11Family n → ℂ) : Prop :=
  DifferentiableOn ℂ F (domain_def n r s B) ∧
    ∀ j : Fin n, ∀ z ∈ domain_def n r s B,
      F ((z.1.1+Pi.single j 1,z.1.2),z.2)=F z
def p11Bound {E F : Type*} [NormedAddCommGroup F] (U : Set E) (f : E → F) (M : ℝ) : Prop :=
  ∀ z ∈ U, ‖f z‖ ≤ M
def p11Real {n : ℕ} (U : Set (P11Family n)) (F : P11Family n → ℂ) : Prop :=
  ∀ x : Phase n, ∀ b : P11Vec n,
    (KAM.realInclusion₂ n x,KAM.realInclusion n b) ∈ U →
      (F (KAM.realInclusion₂ n x,KAM.realInclusion n b)).im=0
def p11Cut {n : ℕ} (T : ℝ) (F : P11Family n → ℂ) (z : P11Family n) : ℂ :=
  KAM.Weighted.truncate T (fun u : P11CVec n × P11CVec n => F ((u.1,z.1.2),u.2))
    (z.1.1,z.2)
def p11Taylor {n : ℕ} (F : P11Family n → ℂ) (z : P11Family n) : ℂ :=
  F ((z.1.1,0),z.2)+fderiv ℂ (fun eta => F ((z.1.1,eta),z.2)) 0 z.1.2
def p11Cutoff {n : ℕ} (T : ℝ) (F : P11Family n → ℂ) := p11Cut T (p11Taylor F)
def p11C (n : ℕ) : ℝ :=
  2*(1+1/Real.pi)*(3*n/(Real.exp 1*Real.pi))^(n-1)
def p11Error (n : ℕ) (T d : ℝ) : ℝ := p11C n*(1+(d^n)⁻¹)*Real.exp (-Real.pi*T*d)
def p11Loss (n : ℕ) (T alpha : ℝ) : ℝ :=
  (Real.log (2*p11C n/alpha)+n*Real.log (Real.pi*T))/(Real.pi*T)
def p11Lambda (n : ℕ) (delta : ℝ) : ℝ := KAM.Weighted.coth (Real.pi*delta)^n-1
theorem fourier_cutoff {n : ℕ} (hn : 1 ≤ n) {r s T d M : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : 0 ≤ T) (hd : 0 < d) (hdr : d < r)
    {B : Set (P11CVec n)} (hB : IsOpen B) {F : P11Family n → ℂ}
    (hF : p11Admissible r s B F) (hM : 0 ≤ M) (hb : p11Bound (domain_def n r s B) F M) :
    1 ≤ p11C n ∧ p11Admissible (r-d) s B (p11Cut T F) ∧
    p11Bound (domain_def n (r-d) s B) (F-p11Cut T F) (p11Error n T d*M) ∧
    p11Bound (domain_def n (r-d) s B) (p11Cut T F) ((1+p11Error n T d)*M) ∧
    (p11Real (domain_def n r s B) F → p11Real (domain_def n (r-d) s B) (p11Cut T F)) ∧
    ∀ eta b, b ∈ B → ‖eta‖ < s →
      Differentiable ℂ (fun theta => p11Cut T F ((theta,eta),b)) := sorry
theorem loss_choice {n : ℕ} (hn : 1 ≤ n) {alpha T : ℝ}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hT : 1 ≤ T) :
    0 < p11Loss n T alpha ∧
    (p11Loss n T alpha ≤ 1 → p11Error n T (p11Loss n T alpha) ≤ alpha) ∧
    AntitoneOn (fun t => p11Loss n t alpha) (Ici 1) ∧
    AntitoneOn (fun a => p11Loss n T a) (Ioc 0 1) := sorry
theorem loss_sum {n : ℕ} (hn : 1 ≤ n) {theta T0 a b : ℝ}
    (ht : 1 < theta) (hT : 1 ≤ T0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (alpha : ℕ → ℝ) (hap : ∀ j, 0 < alpha j ∧ alpha j ≤ 1)
    (hlog : ∀ j, Real.log (2*p11C n/alpha j) ≤ a+b*j) :
    Summable (fun j => p11Loss n (T0*theta^j) (alpha j)) ∧
    (∀ j, p11Loss n (T0*theta^j) (alpha j) ≤
      (a+b*j+n*Real.log (Real.pi*T0)+n*j*Real.log theta)/(Real.pi*T0*theta^j)) ∧
    (∑' j, p11Loss n (T0*theta^j) (alpha j)) ≤
      ((a+n*Real.log (Real.pi*T0))*theta/(theta-1)+
        (b+n*Real.log theta)*theta/(theta-1)^2)/(Real.pi*T0) := sorry
theorem taylor_cutoff {n : ℕ} {r s M q : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hM : 0 ≤ M) (hq : 0 < q) (hq1 : q < 1)
    {B : Set (P11CVec n)} (hB : IsOpen B) {F : P11Family n → ℂ}
    (hF : p11Admissible r s B F) (hb : p11Bound (domain_def n r s B) F M) :
    p11Admissible r s B (p11Taylor F) ∧
    p11Bound (domain_def n r s B) (p11Taylor F) (2*M) ∧
    p11Bound (domain_def n r (q*s) B) (F-p11Taylor F) (M*q^2/(1-q)) ∧
    ∀ theta ∈ KAM.complexStrip n r, ∀ b ∈ B,
      ‖fderiv ℂ (fun eta => F ((theta,eta),b)) 0‖ ≤ M/s := sorry
theorem cutoff {n : ℕ} (hn : 1 ≤ n) {r s T d eps q : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : 0 ≤ T) (hd : 0 < d) (hdr : d < r)
    (he : 0 ≤ eps) (hq : 0 < q) (hq1 : q < 1)
    {B : Set (P11CVec n)} (hB : IsOpen B) {R : P11Family n → ℂ}
    (hR : p11Admissible r s B R) (hb : p11Bound (domain_def n r s B) R eps) :
    p11Admissible (r-d) s B (p11Cutoff T R) ∧
    p11Bound (domain_def n (r-d) s B) (p11Cutoff T R) (2*(1+p11Error n T d)*eps) ∧
    p11Bound (domain_def n (r-d) (q*s) B) (R-p11Cutoff T R)
      (eps*(q^2/(1-q)+2*p11Error n T d)) ∧
    (p11Real (domain_def n r s B) R → p11Real (domain_def n (r-d) s B) (p11Cutoff T R)) := sorry
theorem param_cauchy {n q : ℕ} {E : Set (P11Vec n)} {t tp M : ℝ}
    (htp : 0 < tp) (ht : tp < t) (hM : 0 ≤ M)
    {u : P11CVec n → P11CVec q} (hu : DifferentiableOn ℂ u (KAM.actionNbhd E t))
    (hb : p11Bound (KAM.actionNbhd E t) u M) {j : ℕ} (hj : 1 ≤ j) :
    ∀ b ∈ KAM.actionNbhd E tp, ‖iteratedFDeriv ℂ j u b‖ ≤
      (j : ℝ)^j*M/(t-tp)^j := sorry
theorem divisor_wide {n : ℕ} {gamma tau T : ℝ}
    (hg : 0 < gamma) (ht : 0 ≤ tau) (hT : 0 < T)
    (v : P11Vec n) (u : (Fin n → ℤ) → P11Vec n)
    (hu : ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      2*gamma*KAM.Fourier.modeSize k^(-tau) ≤ |p11dotZ k (u k)|)
    (hc : ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      ‖u k-v‖ ≤ gamma*KAM.Fourier.modeSize k^(-tau-1)) :
    ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      gamma*T^(-tau) ≤ |p11dotZ k v| := sorry
theorem divisor_perturb {n : ℕ} {E : Set (P11Vec n)} {t T D L : ℝ}
    (ht : 0 < t) (hT : 0 < T) (hD : 0 < D) (hL : 0 ≤ L)
    (w : P11CVec n → P11CVec n) (hw : DifferentiableOn ℂ w (KAM.actionNbhd E t))
    (hb : ∀ b ∈ KAM.actionNbhd E t, ‖fderiv ℂ w b‖ ≤ L)
    (hsmall : t*T*L ≤ D/2)
    (hdiv : ∀ b ∈ E, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      D ≤ ‖p11dotC k (w (KAM.realInclusion n b))‖) :
    ∀ b ∈ KAM.actionNbhd E t, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      D/2 ≤ ‖p11dotC k (w b)‖ := sorry
/-- The generator is defined from existing scalar truncation; no Diophantine premise. -/
def p11Solve {n : ℕ} (T : ℝ) (w : P11CVec n → P11CVec n)
    (P : P11CVec n × P11CVec n → ℂ) (theta b : P11CVec n) : ℂ :=
  ∑' k : Fin n → ℤ, if k=0 ∨ T < KAM.Fourier.modeSize k then 0 else
    KAM.Weighted.coeff P b k / (2*Real.pi*Complex.I*p11dotC k (w b)) * KAM.character k theta
def p11AngleClass {n : ℕ} (r : ℝ) (B : Set (P11CVec n))
    (P : P11CVec n × P11CVec n → ℂ) : Prop :=
  DifferentiableOn ℂ P (KAM.complexStrip n r ×ˢ B) ∧
    ∀ j : Fin n, ∀ z ∈ KAM.complexStrip n r ×ˢ B, P (z.1+Pi.single j 1,z.2)=P z
def p11AngleAverage {n : ℕ} (P : P11CVec n × P11CVec n → ℂ) (b : P11CVec n) : ℂ :=
  KAM.Weighted.coeff P b 0
theorem homological_maximal {n : ℕ} (hn : 1 ≤ n) {r delta T D M : ℝ}
    (hr : 0 < r) (hd : 0 < delta) (hdr : delta < r) (hT : 0 < T)
    (hD : 0 < D) (hM : 0 ≤ M) {B : Set (P11CVec n)} (hB : IsOpen B)
    (w : P11CVec n → P11CVec n) (hw : DifferentiableOn ℂ w B)
    (hdiv : ∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    (P : P11CVec n × P11CVec n → ℂ) (hP : p11AngleClass r B P)
    (hpoly : ∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T P z=P z)
    (hb : p11Bound (KAM.complexStrip n r ×ˢ B) P M) :
    let phi := fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2
    p11AngleClass (r-delta) B phi ∧
    DifferentiableOn ℂ phi (Set.univ ×ˢ B) ∧
    (∀ z, KAM.Weighted.truncate T phi z=phi z) ∧
    DifferentiableOn ℂ (p11AngleAverage P) B ∧
    (∀ b ∈ B, p11AngleAverage phi b=0) ∧
    (∀ theta ∈ KAM.complexStrip n (r-delta), ∀ b ∈ B,
      fderiv ℂ (fun x => phi (x,b)) theta (w b)=P (theta,b)-p11AngleAverage P b) ∧
    p11Bound (KAM.complexStrip n (r-delta) ×ˢ B) phi (p11Lambda n delta*M/(Real.pi*D)) ∧
    (∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      ‖KAM.Weighted.coeff phi b k‖ ≤ M*Real.exp (-2*Real.pi*KAM.Fourier.modeSize k*r)/(Real.pi*D)) ∧
    (∀ b ∈ B, ‖p11AngleAverage P b‖ ≤ M) ∧
    ∀ u, p11AngleClass (r-delta) B u →
      (∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T u z=u z) →
      (∀ b ∈ B, p11AngleAverage u b=0) →
      (∀ theta ∈ KAM.complexStrip n (r-delta), ∀ b ∈ B,
        fderiv ℂ (fun x => u (x,b)) theta (w b)=P (theta,b)-p11AngleAverage P b) →
      EqOn u phi (KAM.complexStrip n (r-delta) ×ˢ B) := sorry
/-- Affine generating function in the existing Hamiltonian carrier. -/
def p11Affine {n : ℕ} (p0 : P11CVec n → ℂ) (p1 : P11CVec n → P11CVec n)
    (z : P11Phase n) : ℂ := p0 z.1+∑ i, p1 z.1 i*z.2 i
def p11Flow {n : ℕ} (phi : P11Phase n → ℂ) (r s sigma : ℝ) (t : ℝ) :=
  KAM.Canonical.flow (KAM.hamiltonianVectorFieldℂ phi)
    (KAM.Weighted.Dom n {0} s (r-sigma)) t
def p11GaugeBound {n : ℕ} (rho sigma : ℝ) (L : P11Phase n →L[ℂ] P11Phase n) (M : ℝ) : Prop :=
  ∀ z, KAM.Canonical.scaledNorm rho sigma (L z) ≤ M*KAM.Canonical.scaledNorm rho sigma z
structure P11AffineHyp {n : ℕ} (p0 : P11CVec n → ℂ) (p1 : P11CVec n → P11CVec n)
    (r s sigma A : ℝ) : Prop where
  n_pos : 1 ≤ n
  sigma_pos : 0 < sigma
  radius : 2*sigma < r
  s_pos : 0 < s
  A_nonneg : 0 ≤ A
  small : 4*(n+1)*A ≤ sigma
  hol0 : DifferentiableOn ℂ p0 (KAM.complexStrip n r)
  hol1 : DifferentiableOn ℂ p1 (KAM.complexStrip n r)
  per0 : ∀ j : Fin n, ∀ x ∈ KAM.complexStrip n r, p0 (x+Pi.single j 1)=p0 x
  per1 : ∀ j : Fin n, ∀ x ∈ KAM.complexStrip n r, p1 (x+Pi.single j 1)=p1 x
  bound0 : p11Bound (KAM.complexStrip n r) p0 (s*A)
  bound1 : p11Bound (KAM.complexStrip n r) p1 A
theorem affine_flow {n : ℕ} {p0 : P11CVec n → ℂ} {p1 : P11CVec n → P11CVec n}
    {r s sigma A : ℝ} (H : P11AffineHyp p0 p1 r s sigma A) :
    let phi := p11Affine p0 p1
    let F := p11Flow phi r s sigma 1
    let U := KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)
    let V := KAM.Weighted.Dom n {0} (s/2) (r-2*sigma)
    let kappa := 2*(n+1)*A/sigma
    DifferentiableOn ℂ F U ∧
    (∀ z ∈ U, ‖(F z).1-z.1‖ ≤ A ∧ ‖(F z).2-z.2‖ ≤ (n+1)*s*A/sigma) ∧
    (∀ z ∈ U, ∀ t ∈ Icc (-1 : ℝ) 1,
      p11Flow phi r s sigma t z ∈ KAM.Weighted.Dom n {0} s (r-sigma)) ∧
    (∃ Theta : P11CVec n → P11CVec n, ∃ M : P11CVec n → P11CVec n →L[ℂ] P11CVec n,
      ∃ v : P11CVec n → P11CVec n, ∀ z ∈ U,
        F z=(Theta z.1,M z.1 z.2+v z.1) ∧
        ∀ a b, (∑ i, (fderiv ℂ Theta z.1 a) i*(M z.1 b) i)=∑ i, a i*b i) ∧
    (∀ z ∈ V, p11GaugeBound (s/2) sigma (fderiv ℂ F z-ContinuousLinearMap.id ℂ _) (2*kappa)) ∧
    (∀ z ∈ V, ‖fderiv ℂ F z-ContinuousLinearMap.id ℂ _‖ ≤ 2*kappa+kappa*s/sigma) ∧
    (∀ z ∈ U, ∀ u v, KAM.Canonical.symplFormC (fderiv ℂ F z u) (fderiv ℂ F z v)=
      KAM.Canonical.symplFormC u v) ∧
    (∀ z ∈ U, ∀ k : Fin n → ℤ,
      F (z.1+(fun i => (k i : ℂ)),z.2)=F z+((fun i => (k i : ℂ)),0)) ∧
    (∀ z ∈ V, p11Flow phi r s sigma (-1) (F z)=z ∧
      F (p11Flow phi r s sigma (-1) z)=z) ∧
    (KAM.Canonical.RealOn (KAM.Weighted.Dom n {0} s r) phi →
      ∀ x : Phase n, KAM.realInclusion₂ n x ∈ U →
        ∀ i, ((F (KAM.realInclusion₂ n x)).1 i).im=0 ∧
          ((F (KAM.realInclusion₂ n x)).2 i).im=0) := sorry
/-! ## Explicit local suppliers for graph SOURCE_GAPs. -/
/-- hc-rot: complexification is a new proof obligation, not supplied by holomorphic-to-real restriction. -/
theorem p11_complexification {a b : ℕ} {f : P11Vec a → P11Vec b} {x : P11Vec a}
    (hf : AnalyticAt ℝ f x) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : P11CVec a → P11CVec b,
      DifferentiableOn ℂ F (Metric.ball (KAM.realInclusion a x) r) ∧
      ∀ y, ‖y-x‖ < r → F (KAM.realInclusion a y)=KAM.realInclusion b (f y) := sorry
/-- hc-rot: persistence of polynomial identities; applied entrywise to rho^T rho-1 and det rho-1. -/
theorem p11_real_slice_identity {n : ℕ} {x : P11Vec n} {r : ℝ} (hr : 0 < r)
    {F : P11CVec n → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball (KAM.realInclusion n x) r))
    (hzero : ∀ y, ‖y-x‖ < r → F (KAM.realInclusion n y)=0) :
    ∀ z ∈ Metric.ball (KAM.realInclusion n x) r, F z=0 := sorry
/-- hc-mean: higher order Schwarz on complex radial lines. -/
theorem p11_radial_schwarz {n k : ℕ} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    {F : P11CVec n → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 r))
    (hb : p11Bound (Metric.ball 0 r) F M)
    (hj : ∀ j < k, iteratedFDeriv ℂ j F 0=0) :
    ∀ z ∈ Metric.ball 0 r, ‖F z‖ ≤ M*(‖z‖/r)^k := sorry
/-- rl-global supplier: complete nonlinear flow of a bounded C1 field. -/
theorem p11_bounded_global_flow {n : ℕ} {v : P11Vec n → P11Vec n}
    (hv : ContDiff ℝ 1 v) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖v x‖ ≤ M)
    (x : P11Vec n) :
    ∃ u : ℝ → P11Vec n, u 0=x ∧ ∀ t, HasDerivAt u (v (u t)) t := sorry
open Classical in
def p11RealFlow {n : ℕ} (v : P11Vec n → P11Vec n) (t : ℝ) (x : P11Vec n) : P11Vec n :=
  if h : ∃ u : ℝ → P11Vec n, u 0=x ∧ ∀ t, HasDerivAt u (v (u t)) t
    then h.choose t else x
/-- rl-deriv supplier: differentiability in initial data and its actual variational equation. -/
theorem p11_global_variational {n : ℕ} {v : P11Vec n → P11Vec n}
    (hv : ContDiff ℝ 2 v) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ x, ‖v x‖ ≤ M) (hD : ∀ x, ‖fderiv ℝ v x‖ ≤ L) :
    (∀ t, Differentiable ℝ (p11RealFlow v t)) ∧
    (∀ x t, HasDerivAt (fun s => fderiv ℝ (p11RealFlow v s) x)
      ((fderiv ℝ v (p11RealFlow v t x)).comp (fderiv ℝ (p11RealFlow v t) x)) t) ∧
    ∀ x, fderiv ℝ (p11RealFlow v 0) x=ContinuousLinearMap.id ℝ _ := sorry
/-- The analytic real-flow estimate is proved with a real field from the start. -/
theorem real_lipschitz {n : ℕ} {v : P11Vec n → P11Vec n}
    (hv : ContDiff ℝ 2 v) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ x, ‖v x‖ ≤ M) (hD : ∀ x, ‖fderiv ℝ v x‖ ≤ L)
    (hp : ∀ x, ∀ k : Fin n → ℤ, v (x+fun i => (k i : ℝ))=v x) :
    ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x,
      ‖fderiv ℝ (p11RealFlow v t) x-ContinuousLinearMap.id ℝ _‖ ≤ Real.exp L-1 ∧
      ‖p11RealFlow v t x-x‖ ≤ M ∧
      ∀ k : Fin n → ℤ, p11RealFlow v t (x+fun i => (k i : ℝ))=
        p11RealFlow v t x+fun i => (k i : ℝ) := sorry
/-- Canonical-step source parameters; no conclusions are fields. -/
structure P11Step (n : ℕ) where
  E : Set (P11Vec n)
  t : ℝ
  r : ℝ
  s : ℝ
  T : ℝ
  d : ℝ
  delta : ℝ
  sigma : ℝ
  q : ℝ
  D : ℝ
  L : ℝ
  eps : ℝ
  n_pos : 1 ≤ n
  t_pos : 0 < t
  s_pos : 0 < s
  T_pos : 0 < T
  d_pos : 0 < d
  delta_pos : 0 < delta
  sigma_pos : 0 < sigma
  radius : 0 < r-d-delta-2*sigma
  q_pos : 0 < q
  q_le : q ≤ 1/2
  D_pos : 0 < D
  L_nonneg : 0 ≤ L
  eps_nonneg : 0 ≤ eps
  cutoff_error : p11Error n T d ≤ 1
  divisor_small : t*T*L ≤ D/2
  flow_small : 4*(n+1)*p11Lambda n delta*(1+p11Error n T d)*eps ≤ Real.pi*D*s*sigma
def p11StepA {n : ℕ} (S : P11Step n) : ℝ :=
  p11Lambda n S.delta*(1+p11Error n S.T S.d)*S.eps/(Real.pi*S.D*S.s)
def p11StepKappa {n : ℕ} (S : P11Step n) : ℝ := 2*(n+1)*p11StepA S/S.sigma
def p11StepRem {n : ℕ} (S : P11Step n) : ℝ :=
  S.eps*(S.q^2/(1-S.q)+2*p11Error n S.T S.d)+
    n*(4*n+5)*(5+4*p11Error n S.T S.d)*(1+p11Error n S.T S.d)*
      p11Lambda n S.delta*S.eps^2/(Real.pi*S.D*S.s*S.sigma)
def p11R0 {n : ℕ} (T : ℝ) (R : P11Family n → ℂ) (z : P11CVec n × P11CVec n) : ℂ :=
  p11Cutoff T R ((z.1,0),z.2)
def p11R1 {n : ℕ} (T : ℝ) (R : P11Family n → ℂ) (z : P11CVec n × P11CVec n) : P11CVec n :=
  fun i => fderiv ℂ (fun eta => p11Cutoff T R ((z.1,eta),z.2)) 0 (Pi.single i 1)
def p11DeltaH {n : ℕ} (T : ℝ) (R : P11Family n → ℂ) := p11AngleAverage (p11R0 T R)
def p11DeltaW {n : ℕ} (T : ℝ) (R : P11Family n → ℂ) (b : P11CVec n) : P11CVec n :=
  fun i => p11AngleAverage (fun z => p11R1 T R z i) b
def p11StepPhi {n : ℕ} (S : P11Step n) (w : P11CVec n → P11CVec n)
    (R : P11Family n → ℂ) (b : P11CVec n) : P11Phase n → ℂ :=
  p11Affine (fun theta => p11Solve S.T w (p11R0 S.T R) theta b)
    (fun theta i => p11Solve S.T w (fun z => p11R1 S.T R z i) theta b)
def p11StepMap {n : ℕ} (S : P11Step n) (w : P11CVec n → P11CVec n)
    (R : P11Family n → ℂ) (z : P11Family n) : P11Phase n :=
  p11Flow (p11StepPhi S w R z.2) (S.r-S.d-S.delta) S.s S.sigma 1 z.1
def p11Normal {n : ℕ} (h : P11CVec n → ℂ) (w : P11CVec n → P11CVec n)
    (z : P11Family n) : ℂ := h z.2+∑ i, w z.2 i*z.1.2 i
def p11StepRemainder {n : ℕ} (S : P11Step n) (h : P11CVec n → ℂ)
    (w : P11CVec n → P11CVec n) (R : P11Family n → ℂ) (z : P11Family n) : ℂ :=
  (p11Normal h w+R) (p11StepMap S w R z,z.2)-
    p11Normal (h+p11DeltaH S.T R) (w+p11DeltaW S.T R) z
structure P11StepHyp {n : ℕ} (S : P11Step n) (h : P11CVec n → ℂ)
    (w : P11CVec n → P11CVec n) (R : P11Family n → ℂ) : Prop where
  holh : DifferentiableOn ℂ h (KAM.actionNbhd S.E S.t)
  holw : DifferentiableOn ℂ w (KAM.actionNbhd S.E S.t)
  realh : ∀ b : P11Vec n, KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t →
    (h (KAM.realInclusion n b)).im=0
  realw : ∀ b : P11Vec n, KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t →
    ∀ i, (w (KAM.realInclusion n b) i).im=0
  admissible : p11Admissible S.r S.s (KAM.actionNbhd S.E S.t) R
  bound : p11Bound (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R S.eps
  derivative : ∀ b ∈ KAM.actionNbhd S.E S.t, ‖fderiv ℂ w b‖ ≤ S.L
  divisor : ∀ b ∈ S.E, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ S.T →
    S.D ≤ ‖p11dotC k (w (KAM.realInclusion n b))‖
/-- canonical-step i-iii, complex form. The output functions are explicit, never assumed. -/
theorem canonical_step {n : ℕ} {S : P11Step n} {h : P11CVec n → ℂ}
    {w : P11CVec n → P11CVec n} {R : P11Family n → ℂ} (H : P11StepHyp S h w R) :
    let B := KAM.actionNbhd S.E S.t
    let rp := S.r-S.d-S.delta-2*S.sigma
    let U := domain_def n rp (S.q*S.s) B
    let F := p11StepMap S w R
    let Rp := p11StepRemainder S h w R
    DifferentiableOn ℂ (p11DeltaH S.T R) B ∧
    DifferentiableOn ℂ (p11DeltaW S.T R) B ∧
    p11Bound B (p11DeltaH S.T R) ((1+p11Error n S.T S.d)*S.eps) ∧
    p11Bound B (p11DeltaW S.T R) ((1+p11Error n S.T S.d)*S.eps/S.s) ∧
    DifferentiableOn ℂ F U ∧
    (∀ z ∈ U, (F z,z.2) ∈ domain_def n (rp+S.sigma) S.s B) ∧
    (∀ z ∈ U, ‖(F z).1-z.1.1‖ ≤ p11StepA S ∧
      ‖(F z).2-z.1.2‖ ≤ (n+1)*S.s*p11StepA S/S.sigma) ∧
    (∀ z ∈ U, p11GaugeBound (S.s/2) S.sigma
      (fderiv ℂ (fun x => F (x,z.2)) z.1-ContinuousLinearMap.id ℂ _) (2*p11StepKappa S)) ∧
    (∀ z ∈ U, ‖fderiv ℂ (fun x => F (x,z.2)) z.1-ContinuousLinearMap.id ℂ _‖ ≤
      2*p11StepKappa S+p11StepKappa S*S.s/S.sigma) ∧
    (∀ z ∈ U, ∀ u v, KAM.Canonical.symplFormC
      (fderiv ℂ (fun x => F (x,z.2)) z.1 u) (fderiv ℂ (fun x => F (x,z.2)) z.1 v)=
        KAM.Canonical.symplFormC u v) ∧
    (∀ z ∈ U, ∀ k : Fin n → ℤ, F ((z.1.1+(fun i => (k i : ℂ)),z.1.2),z.2)=
      F z+((fun i => (k i : ℂ)),0)) ∧
    p11Admissible rp (S.q*S.s) B Rp ∧ p11Bound U Rp (p11StepRem S) ∧
    p11StepRem S ≤ S.eps*(2*S.q^2+2*p11Error n S.T S.d)+
      18*n*(4*n+5)*p11Lambda n S.delta*S.eps^2/(Real.pi*S.D*S.s*S.sigma) ∧
    (∀ z ∈ U, (p11Normal h w+R) (F z,z.2)=
      p11Normal (h+p11DeltaH S.T R) (w+p11DeltaW S.T R) z+Rp z) := sorry
/-- cs-lip: EXPLICIT reality guard repairs p11a2 L248/L287; no frozen type changes. -/
theorem canonical_step_real {n : ℕ} {S : P11Step n} {h : P11CVec n → ℂ}
    {w : P11CVec n → P11CVec n} {R : P11Family n → ℂ} (H : P11StepHyp S h w R)
    (hreal : p11Real (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R) :
    let rp := S.r-S.d-S.delta-2*S.sigma
    (∀ x : Phase n, ∀ b : P11Vec n,
      (KAM.realInclusion₂ n x,KAM.realInclusion n b) ∈ domain_def n rp (S.q*S.s) (KAM.actionNbhd S.E S.t) →
        ∀ i, ((p11StepMap S w R (KAM.realInclusion₂ n x,KAM.realInclusion n b)).1 i).im=0 ∧
          ((p11StepMap S w R (KAM.realInclusion₂ n x,KAM.realInclusion n b)).2 i).im=0) ∧
    p11Real (domain_def n rp (S.q*S.s) (KAM.actionNbhd S.E S.t)) (p11StepRemainder S h w R) ∧
    ∀ b ∈ S.E, ∀ theta : P11Vec n,
      ‖fderiv ℝ (fun x : P11Vec n => fun i =>
        ((p11StepMap S w R ((KAM.realInclusion n x,0),KAM.realInclusion n b)).1 i).re) theta-
        ContinuousLinearMap.id ℝ _‖ ≤
        Real.exp (2*S.T*(1+p11Error n S.T S.d)*S.eps*p11Lambda n (S.r-S.d)/(S.D*S.s))-1 := sorry
/-- v: use the existing full complex domain; derivatives cost only t-tp. -/
theorem canonical_step_param {n : ℕ} {S : P11Step n} {h : P11CVec n → ℂ}
    {w : P11CVec n → P11CVec n} {R : P11Family n → ℂ} (H : P11StepHyp S h w R)
    {tp : ℝ} (htp : 0 < tp) (ht : tp < S.t) {j : ℕ} (hj : 1 ≤ j) :
    ∀ b ∈ KAM.actionNbhd S.E tp,
      ‖iteratedFDeriv ℂ j (p11DeltaH S.T R) b‖ ≤
        (j : ℝ)^j*(1+p11Error n S.T S.d)*S.eps/(S.t-tp)^j ∧
      ‖iteratedFDeriv ℂ j (p11DeltaW S.T R) b‖ ≤
        (j : ℝ)^j*(1+p11Error n S.T S.d)*S.eps/(S.s*(S.t-tp)^j) ∧
      ∀ z ∈ KAM.Weighted.Dom n {0} (S.q*S.s) (S.r-S.d-S.delta-2*S.sigma),
        ‖iteratedFDeriv ℂ j (fun b => (p11StepMap S w R (z,b)).1-z.1) b‖ ≤
          (j : ℝ)^j*p11StepA S/(S.t-tp)^j ∧
        ‖iteratedFDeriv ℂ j (fun b => (p11StepMap S w R (z,b)).2-z.2) b‖ ≤
          (j : ℝ)^j*(n+1)*S.s*p11StepA S/(S.sigma*(S.t-tp)^j) ∧
        (∀ Mr : ℝ, p11Bound
          (domain_def n (S.r-S.d-S.delta-2*S.sigma) (S.q*S.s) (KAM.actionNbhd S.E S.t))
          (p11StepRemainder S h w R) Mr →
          ‖iteratedFDeriv ℂ j (fun b => p11StepRemainder S h w R (z,b)) b‖ ≤
            (j : ℝ)^j*Mr/(S.t-tp)^j) := sorry
/-! ## Finite preparation. Data structures below are outputs, never theorem premises. -/
structure P11Physical (n : ℕ) where
  G : ℝ
  m0 : ℝ
  m : P11Vec n
  a : P11Vec n
  eta : ℝ
  n_ge : 2 ≤ n
  G_pos : 0 < G
  m0_pos : 0 < m0
  m_pos : ∀ i, 0 < m i
  a_pos : ∀ i, 0 < a i
  ordered : StrictMono a
  eta_pos : 0 < eta
def p11Zeta {n : ℕ} (D : P11Physical n) : ℝ :=
  min D.eta ((sInf ({x | ∃ i, x=D.a i} ∪ {x | ∃ i j, i ≠ j ∧ x=|D.a i-D.a j|}))/6)
theorem p11_zeta_pos {n : ℕ} (D : P11Physical n) : 0 < p11Zeta D := sorry
/-- Forward tube uses existing product chart and one-planet Gamma, for arbitrary n. -/
theorem forward_tube {n : ℕ} (D : P11Physical n) {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ delta : ℝ, 0 < delta ∧
      (∀ i, delta ≤ D.m i*Real.sqrt (D.G*D.m0*D.a i)/4) ∧
      ∀ w : Phase (n+n),
        (∀ i : Fin n, |w.2 (Fin.castAdd n i)-D.m i*Real.sqrt (D.G*D.m0*D.a i)| ≤ delta) →
        (∀ i, poincareGamma (planetBlock w i) ≤ delta) →
        w ∈ poincareProdDom n ∧
        ‖poincareProd D.m (D.G*D.m0) w-
          circularPoint D.G D.m0 D.m D.a (fun i => w.1 (Fin.castAdd n i)/(2*Real.pi))‖ < zeta := sorry
def p11PhysicalDelta {n : ℕ} (D : P11Physical n) : ℝ :=
  (forward_tube D (p11_zeta_pos D)).choose
/-- Literal secular Hessian, connected to Part 8 Q_h by an equality proved at its port. -/
def p11SecularMatrix {n : ℕ} (D : P11Physical n) (L : P11Vec n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (1/2 : ℝ) * iteratedFDeriv ℝ 2
    (fun xi : P11Vec n => secularAverage
      (fun (_ : ℝ) z => fFix D.G D.m (poincareProd D.m (D.G*D.m0) z)) 0 L 0 xi)
    0 ![Pi.single i 1,Pi.single j 1]
/-- Part 10 patch output, tied to the actual frozen secular average and physical frequencies. -/
structure P11PatchData (n : ℕ) where
  K : Set (P11Vec n)
  V : Set (P11Vec n)
  varpi : P11Vec n → P11Vec (n+n)
  sigma : P11Vec n → P11Vec n
  mu : ℕ
  beta : ℝ
def P11PatchSpec {n : ℕ} (D : P11Physical n) (A : P11PatchData n) : Prop :=
  (∀ J ∈ A.V, StrictMono (A.sigma J) ∧
    (p11SecularMatrix D ((2*Real.pi)⁻¹ • J)).charpoly=
      ∏ i, (Polynomial.X-Polynomial.C (A.sigma J i))) ∧
  (∀ J ∈ A.V, A.varpi J=Fin.append
    (fun i : Fin n => (D.G*D.m0)^2*D.m i^3/((J i/(2*Real.pi))^3*(2*Real.pi)))
    (fun i : Fin n => 2*A.sigma J i/(2*Real.pi))) ∧
  IsOpen A.V ∧ IsPreconnected A.V ∧ IsCompact A.K ∧ A.K.Nonempty ∧ A.K ⊆ A.V ∧
    0 < volume A.K ∧ volume (A.K \ interior A.K)=0 ∧
    1 ≤ A.mu ∧ 0 < A.beta ∧ AnalyticOnNhd ℝ A.varpi A.V ∧
    p11RNondegenerate A.V A.varpi ∧ A.beta ≤ index_def 2 A.mu A.varpi A.K ∧
    ∀ J ∈ A.K, ∀ i : Fin n,
      |J i/(2*Real.pi)-D.m i*Real.sqrt (D.G*D.m0*D.a i)| < p11PhysicalDelta D/8
/-- Implementation uses Part 10 interface and shrinks the physical patch to the requested tube. -/
theorem p11_patch {n : ℕ} (D : P11Physical n) : ∃ A, P11PatchSpec D A := sorry
def p11PatchData {n : ℕ} (D : P11Physical n) : P11PatchData n := (p11_patch D).choose
/-- norm-dict retains the exact scalar and input dilation factor. -/
theorem norm_dict {n m mu : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {V K : Set (P11Vec n)} (hV : IsOpen V) (hK : IsCompact K)
    (hne : K.Nonempty) (hsub : K ⊆ V) {w : P11Vec n → P11Vec m}
    (hw : AnalyticOnNhd ℝ w V) {beta : ℝ} (hb : 0 < beta)
    (ham : beta ≤ index_def 2 mu w K) :
    let wJ := fun J : P11Vec n => (2*Real.pi)⁻¹ • w ((2*Real.pi)⁻¹ • J)
    AnalyticOnNhd ℝ wJ ((fun J => (2*Real.pi) • J) '' V) ∧
    p11RNondegenerate ((fun J => (2*Real.pi) • J) '' V) wJ ∧
    (2*Real.pi)^(-(2+(mu : ℝ)))*beta ≤
      index_def 2 mu wJ ((fun J => (2*Real.pi) • J) '' K) := sorry
/-- Base point theorem, no Diophantine point is assumed. -/
theorem select {n : ℕ} (D : P11Physical n) :
    let A := p11PatchData D
    ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ 1 ∧ ∃ J0 ∈ interior A.K,
      KAM.IsDiophantine gamma (max ((n : ℝ)*A.mu) (2*n)) (A.varpi J0) ∧
      KAM.IsDiophantine gamma (max ((n : ℝ)*A.mu) (2*n)) (fast (a := n) (b := n) (A.varpi J0)) ∧
      KAM.IsDiophantine gamma (max ((n : ℝ)*A.mu) (2*n)) (slow (a := n) (b := n) (A.varpi J0)) := sorry
/-- Working chart carrier: ((theta,x),(J,y)), exactly the existing phase carrier. -/
def p11WorkingDom (n : ℕ) (J0 : P11Vec n) (s r rz : ℝ) : Set (P11Phase (n+n)) :=
  {z | (fun i : Fin n => z.1 (Fin.castAdd n i)) ∈ KAM.complexStrip n s ∧
    ‖(fun i : Fin n => z.2 (Fin.castAdd n i))-KAM.realInclusion n J0‖ < r ∧
    ‖(fun i : Fin n => z.1 (Fin.natAdd n i))‖ < rz ∧
    ‖(fun i : Fin n => z.2 (Fin.natAdd n i))‖ < rz}
/-- Only data, with all properties in P11SecularSpec. -/
structure P11SecularData (n : ℕ) where
  J0 : P11Vec n
  gamma : ℝ
  tau : ℝ
  rC : ℝ
  sigma : ℝ
  rz : ℝ
  MF : ℝ
  L : ℝ
  Brho : ℝ
  Bdrho : ℝ
  h : P11CVec n → ℂ
  C : P11CVec n → ℂ
  omega : P11CVec n → P11CVec n
  Omega : P11CVec n → P11CVec n
  F : P11Phase (n+n) → ℂ
  rho : P11CVec n → Matrix (Fin n) (Fin n) ℂ
  chart : Phase (n+n) → Phase (n*2)
/-- Literal P9 inverse lift after the canonical period conversion T1; positions and momenta keep frozen order. -/
def p11ChartInput {n : ℕ} (C : P11SecularData n) (z : Phase (n+n)) : Phase (n+n) :=
  let L : P11Vec n := fun i => fast z.2 i/(2*Real.pi)
  let x := KAM.realInclusion n (slow z.1)
  let y := KAM.realInclusion n (slow z.2)
  let R := C.rho (KAM.realInclusion n L)
  assemble L
    (fun l => 2*Real.pi*fast z.1 l+
      (∑ i, ∑ j, y i*(R.transpose*fderiv ℂ C.rho (KAM.realInclusion n L) (Pi.single l 1)) i j*x j).re)
    (fun i => (R.mulVec y i).re) (fun i => (R.mulVec x i).re)
def p11WorkingH {n : ℕ} (C : P11SecularData n) (eps : ℝ) (z : P11Phase (n+n)) : ℂ :=
  C.h (fun i : Fin n => z.2 (Fin.castAdd n i))+eps*C.F z
def p11FastMean {n : ℕ} (F : P11Phase (n+n) → ℂ) (J : P11CVec n) (z : P11Phase n) : ℂ :=
  KAM.torusAverage (fun theta : P11Vec n =>
    F (Fin.append (KAM.realInclusion n theta) z.1,Fin.append J z.2))
def P11SecularSpec {n : ℕ} (D : P11Physical n) (C : P11SecularData n) : Prop :=
  (∀ J : P11Vec n, KAM.realInclusion n J ∈ Metric.ball (KAM.realInclusion n C.J0) (2*C.rC) →
    J ∈ (p11PatchData D).V ∧
    (∀ i : Fin n, (C.omega (KAM.realInclusion n J) i).re=(p11PatchData D).varpi J (Fin.castAdd n i)) ∧
    (∀ i : Fin n, (C.Omega (KAM.realInclusion n J) i).re=
      2*Real.pi*(p11PatchData D).varpi J (Fin.natAdd n i))) ∧
  (∀ J : P11Vec n, ‖J-C.J0‖ < 2*C.rC →
    (C.h (KAM.realInclusion n J)).re= -∑ i, (D.G*D.m0)^2*D.m i^3/(2*(J i/(2*Real.pi))^2)) ∧
  (DifferentiableOn ℂ C.omega (Metric.ball (KAM.realInclusion n C.J0) (2*C.rC)) ∧
   DifferentiableOn ℂ C.Omega (Metric.ball (KAM.realInclusion n C.J0) (2*C.rC))) ∧
  C.tau=max ((n : ℝ)*(p11PatchData D).mu) (2*n) ∧
  DifferentiableOn ℂ C.h (Metric.ball (KAM.realInclusion n C.J0) (2*C.rC)) ∧
  (∀ J ∈ Metric.ball (KAM.realInclusion n C.J0) (2*C.rC),
    C.omega J=fun i => fderiv ℂ C.h J (Pi.single i 1)) ∧
  (∀ J ∈ Metric.ball (KAM.realInclusion n C.J0) (2*C.rC), ∀ j ≤ (p11PatchData D).mu+1,
    ‖iteratedFDeriv ℂ j (fun J => Fin.append (C.omega J) ((2*Real.pi : ℂ)⁻¹ • C.Omega J)) J‖ ≤ C.L) ∧
  C.J0 ∈ interior (p11PatchData D).K ∧ 0 < C.gamma ∧ C.gamma ≤ 1 ∧
  KAM.IsDiophantine C.gamma C.tau ((p11PatchData D).varpi C.J0) ∧
  0 < C.rC ∧ C.rC ≤ 1 ∧ C.rC ≤ Real.pi*p11PhysicalDelta D/8 ∧ 0 < C.sigma ∧ C.sigma ≤ 1/4 ∧
  0 < C.rz ∧ C.rz ≤ 1 ∧ 1 ≤ C.MF ∧ 1 ≤ C.L ∧ 1 ≤ C.Brho ∧ 1 ≤ C.Bdrho ∧
  DifferentiableOn ℂ C.F (p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz) ∧
  p11Bound (p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz) C.F
    (C.MF/KAM.Weighted.coth (Real.pi*C.sigma)^n) ∧
  (∀ z ∈ p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz, ∀ j : Fin n,
    C.F (z.1+Pi.single (Fin.castAdd n j) 1,z.2)=C.F z) ∧
  (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz →
    (C.F (KAM.realInclusion₂ (n+n) z)).im=0) ∧
  (∀ J ∈ Metric.ball (KAM.realInclusion n C.J0) (2*C.rC),
    ∀ z : P11Phase n, ‖z‖ < C.rz →
      ‖p11FastMean C.F J z-C.C J-∑ i, C.Omega J i*(z.1 i^2+z.2 i^2)/2‖ ≤
        C.MF*(‖z‖/C.rz)^4) ∧
  (∀ L : P11Vec n, ‖L-(2*Real.pi)⁻¹ • C.J0‖ < C.rC/Real.pi →
    (∀ i j, (C.rho (KAM.realInclusion n L) i j).im=0) ∧
    (C.rho (KAM.realInclusion n L)).det=1 ∧
    (let R : Matrix (Fin n) (Fin n) ℝ := fun i j => (C.rho (KAM.realInclusion n L) i j).re
     R.transpose*p11SecularMatrix D L*R=Matrix.diagonal ((p11PatchData D).sigma ((2*Real.pi) • L)))) ∧
  (DifferentiableOn ℂ C.rho (Metric.ball ((2*Real.pi)⁻¹ • KAM.realInclusion n C.J0) (C.rC/Real.pi)) ∧
   ∀ J ∈ Metric.ball ((2*Real.pi)⁻¹ • KAM.realInclusion n C.J0) (C.rC/Real.pi),
     (C.rho J).transpose*C.rho J=1 ∧
     (∀ i, (∑ j, ‖C.rho J i j‖) ≤ C.Brho) ∧
     (∀ l : Fin n, ∀ i, (∑ j, ‖((C.rho J).transpose*fderiv ℂ C.rho J (Pi.single l 1)) i j‖) ≤ C.Bdrho)) ∧
  (let O := KAM.realInclusion₂ (n+n) ⁻¹' p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz
   AnalyticOnNhd ℝ C.chart O ∧ KAM.Kepler.IsSymplecticOn 1 C.chart O ∧
   (∀ z ∈ O, p11ChartInput C z ∈ poincareProdDom n ∧
     C.chart z=poincareProd D.m (D.G*D.m0) (p11ChartInput C z) ∧ C.chart z ∈ collisionFreeDomain n) ∧
   (∀ z ∈ O, ∀ k : Fin n → ℤ,
     C.chart (z.1+Fin.append (fun i => (k i : ℝ)) 0,z.2)=C.chart z) ∧
   (∀ z ∈ O, ∀ z' ∈ O, C.chart z=C.chart z' →
     ∃ k : Fin n → ℤ, z'=(z.1+Fin.append (fun i => (k i : ℝ)) 0,z.2)) ∧
   (∀ eps : ℝ, ∀ z ∈ O, fixedHamiltonian D.G D.m0 D.m eps (C.chart z)=
      (p11WorkingH C eps (KAM.realInclusion₂ (n+n) z)).re))
/-- Part 11 A: this is constructed from physical data, not a standing chart hypothesis. -/
def P11SecularFullSpec {n : ℕ} (D : P11Physical n)
    (C : P11SecularData n) : Prop :=
  P11SecularSpec D C ∧
  ∀ J ∈ Metric.ball (KAM.realInclusion n C.J0) (2*C.rC),
    KAM.Nekhoroshev.euclid
      (Fin.append (C.omega J) ((2*Real.pi : ℂ)⁻¹ • C.Omega J)) ≤ C.L
theorem holo_chart {n : ℕ} (D : P11Physical n) :
    ∃ C, P11SecularFullSpec D C := sorry
def p11SecularData {n : ℕ} (D : P11Physical n) : P11SecularData n := (holo_chart D).choose
/-- Canonical polar chart in period one; no new real polar representation. -/
def p11PolarC {n : ℕ} (z : P11Phase (n+n)) : P11Phase (n+n) :=
  (Fin.append (fun i : Fin n => z.1 (Fin.castAdd n i))
    (fun i : Fin n => Complex.sqrt (z.2 (Fin.natAdd n i)/Real.pi)*
      Complex.sin (2*Real.pi*z.1 (Fin.natAdd n i))),
   Fin.append (fun i : Fin n => z.2 (Fin.castAdd n i))
    (fun i : Fin n => Complex.sqrt (z.2 (Fin.natAdd n i)/Real.pi)*
      Complex.cos (2*Real.pi*z.1 (Fin.natAdd n i))))
def p11PolarR {n : ℕ} (z : Phase (n+n)) : Phase (n+n) :=
  ((fun i => (p11PolarC (KAM.realInclusion₂ (n+n) z)).1 i |>.re),
   (fun i => (p11PolarC (KAM.realInclusion₂ (n+n) z)).2 i |>.re))
theorem total_chart {n : ℕ} :
    let O : Set (Phase (n+n)) := {z | ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i)}
    AnalyticOnNhd ℝ p11PolarR O ∧ KAM.Kepler.IsSymplecticOn 1 p11PolarR O ∧
    (∀ z ∈ O, ∀ k : Fin n → ℤ,
      p11PolarR (z.1+Fin.append 0 (fun i => (k i : ℝ)),z.2)=p11PolarR z) ∧
    ∀ z ∈ O, ∀ z' ∈ O, p11PolarR z=p11PolarR z' →
      ∃ k : Fin n → ℤ, z'=(z.1+Fin.append 0 (fun i => (k i : ℝ)),z.2) := sorry
/-- Total-chart companion: compatibility of BOTH integer angle lattices with the physical chart. -/
theorem total_chart_transport {n : ℕ} (D : P11Physical n)
    {O : Set (Phase (n+n))} (hO : IsOpen O)
    (hpos : ∀ z ∈ O, ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i))
    (hmap : MapsTo p11PolarR O
      (KAM.realInclusion₂ (n+n) ⁻¹' p11WorkingDom n (p11SecularData D).J0
        (2*(p11SecularData D).sigma) (2*(p11SecularData D).rC) (p11SecularData D).rz))
    (hshift : ∀ z ∈ O, ∀ k : Fin (n+n) → ℤ, (z.1+(fun i => (k i : ℝ)),z.2) ∈ O) :
    let Xi := (p11SecularData D).chart ∘ p11PolarR
    AnalyticOnNhd ℝ Xi O ∧ KAM.Kepler.IsSymplecticOn 1 Xi O ∧
    (∀ z ∈ O, ∀ k : Fin (n+n) → ℤ, Xi (z.1+(fun i => (k i : ℝ)),z.2)=Xi z) ∧
    ∀ z ∈ O, ∀ z' ∈ O, Xi z=Xi z' →
      ∃ k : Fin (n+n) → ℤ, z'=(z.1+(fun i => (k i : ℝ)),z.2) := sorry
/-- Exact CP09 preparation parameters; nu1 is fixed at 3. -/
def p11K1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) : ℝ :=
  6/(Real.pi*C.sigma)*Real.log (1/(eps*C.MF))
def p11Alpha1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) := C.gamma/2*p11K1 C eps^(-C.tau)
def p11s1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) :=
  min C.rC (C.gamma/(4*C.L*p11K1 C eps^(C.tau+1)))
def p11d1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) := min (p11s1 C eps*C.sigma) C.rz^2
def p11eta1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) :=
  400*(1+n)*eps*C.MF^2/(2*Real.pi*p11Alpha1 C eps*p11d1 C eps)
structure P11FastData (n : ℕ) where
  map : P11Phase (n+n) → P11Phase (n+n)
  G : P11CVec n × P11Phase n → ℂ
  f1 : P11Phase (n+n) → ℂ
  deriving Inhabited
def P11FastSpec {n : ℕ} (C : P11SecularData n) (eps : ℝ) (A : P11FastData n) : Prop :=
  let U := p11WorkingDom n C.J0 (C.sigma/6) (p11s1 C eps/2) (C.rz/2)
  DifferentiableOn ℂ A.map U ∧ InjOn A.map U ∧
  DifferentiableOn ℂ A.f1 U ∧ KAM.Canonical.RealOn U A.f1 ∧
  DifferentiableOn ℂ A.G
    (Metric.ball (KAM.realInclusion n C.J0) (p11s1 C eps/2) ×ˢ Metric.ball 0 (C.rz/2)) ∧
  (∀ J : P11Vec n, ‖J-C.J0‖ < p11s1 C eps/2 → ∀ z : Phase n, ‖z‖ < C.rz/2 →
    (A.G (KAM.realInclusion n J,KAM.realInclusion₂ n z)).im=0) ∧
  (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ U → ∀ i,
    ((A.map (KAM.realInclusion₂ (n+n) z)).1 i).im=0 ∧
    ((A.map (KAM.realInclusion₂ (n+n) z)).2 i).im=0) ∧
  (∀ z ∈ U, ∀ u v, KAM.Canonical.symplFormC (fderiv ℂ A.map z u) (fderiv ℂ A.map z v)=
    KAM.Canonical.symplFormC u v) ∧
  (∀ z ∈ U, ∀ k : Fin n → ℤ, A.map (z.1+Fin.append (fun i => (k i : ℂ)) 0,z.2)=
    A.map z+(Fin.append (fun i => (k i : ℂ)) 0,0)) ∧
  MapsTo A.map U (p11WorkingDom n C.J0 C.sigma (p11s1 C eps) C.rz) ∧
  (∀ z ∈ U, p11WorkingH C eps (A.map z)=
    C.h (fun i : Fin n => z.2 (Fin.castAdd n i))+
    eps*A.G ((fun i : Fin n => z.2 (Fin.castAdd n i)),
      ((fun i : Fin n => z.1 (Fin.natAdd n i)),fun i : Fin n => z.2 (Fin.natAdd n i)))+A.f1 z) ∧
  p11Bound U A.f1 ((eps*C.MF)^3) ∧
  (∀ z : P11Phase n, ‖z‖ < C.rz/2 → ∀ J, ‖J-KAM.realInclusion n C.J0‖ < p11s1 C eps/2 →
    let f := fun u : P11CVec n × P11CVec n => A.f1 (Fin.append u.1 z.1,Fin.append u.2 z.2)
    KAM.Weighted.WSummable f (C.sigma/6) J ∧ KAM.Weighted.wsum f (C.sigma/6) J ≤ (eps*C.MF)^3) ∧
  (∀ J, ‖J-KAM.realInclusion n C.J0‖ < p11s1 C eps/2 → ∀ z : P11Phase n, ‖z‖ < C.rz/2 →
    ‖A.G (J,z)-p11FastMean C.F J z‖ ≤ p11eta1 C eps) ∧
  ∀ z ∈ U,
    2*Real.pi*p11Alpha1 C eps*C.sigma*
      ‖(fun i : Fin n => (A.map z).2 (Fin.castAdd n i)-z.2 (Fin.castAdd n i))‖ ≤ 3*eps*C.MF ∧
    2*Real.pi*p11Alpha1 C eps*p11s1 C eps*
      ‖(fun i : Fin n => (A.map z).1 (Fin.castAdd n i)-z.1 (Fin.castAdd n i))‖ ≤ 9*eps*C.MF ∧
    2*Real.pi*p11Alpha1 C eps*C.rz*
      max (‖(fun i : Fin n => (A.map z).1 (Fin.natAdd n i)-z.1 (Fin.natAdd n i))‖)
        (‖(fun i : Fin n => (A.map z).2 (Fin.natAdd n i)-z.2 (Fin.natAdd n i))‖) ≤ 9*eps*C.MF
theorem avg_fast {n : ℕ} (D : P11Physical n) :
    let C := p11SecularData D
    ∃ eps1 : ℝ, 0 < eps1 ∧ eps1 < 1 ∧ ∀ eps, 0 < eps → eps ≤ eps1 →
      2^12*(1+n)*p11K1 C eps*eps*C.MF*C.sigma ≤ p11Alpha1 C eps*p11d1 C eps ∧
      ∃ A, P11FastSpec C eps A := sorry
open Classical in
def p11FastData {n : ℕ} (D : P11Physical n) (eps : ℝ) : P11FastData n :=
  if h : ∃ A, P11FastSpec (p11SecularData D) eps A then h.choose else default
/-- Polar average as a linear operator on holomorphic germs; its value at zero has no square-root singularity. -/
def p11PolarAverage {n : ℕ} (G : P11CVec n × P11Phase n → ℂ)
    (z : P11CVec n × P11CVec n) : ℂ :=
  KAM.torusAverage (fun theta : P11Vec n =>
    G (z.1,((fun i => Complex.sqrt (z.2 i/Real.pi)*Complex.sin (2*Real.pi*(theta i))),
      fun i => Complex.sqrt (z.2 i/Real.pi)*Complex.cos (2*Real.pi*(theta i)))))
/-- Entire action extension is specified existentially; the raw principal-root integral is only compared on Re rho>0. -/
theorem polar_avg {n : ℕ} {D : Set (P11CVec n)} (hD : IsOpen D) {r S : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hS : 0 < S)
    {G : P11CVec n × P11Phase n → ℂ}
    (hG : DifferentiableOn ℂ G (D ×ˢ Metric.ball 0 r))
    (hb : p11Bound (D ×ˢ Metric.ball 0 r) G S) :
    ∃ AG : P11CVec n × P11CVec n → ℂ,
      DifferentiableOn ℂ AG (D ×ˢ Metric.ball 0 (Real.pi*r^2/4)) ∧
      p11Bound (D ×ˢ Metric.ball 0 (Real.pi*r^2/4)) AG (2^(2*n)*S) ∧
      (∀ z ∈ D ×ˢ Metric.ball 0 (Real.pi*r^2/4), (∀ i, 0 < (z.2 i).re) →
        AG z=p11PolarAverage G z) ∧
      ∀ k : ℕ, (∀ J ∈ D, ∀ j < k, iteratedFDeriv ℂ j (fun z => G (J,z)) 0=0) →
        ∀ z ∈ D ×ˢ Metric.ball 0 (Real.pi*r^2/4),
          ‖AG z‖ ≤ 2^(2*n)*S*(4*‖z.2‖/(Real.pi*r^2))^((k+1)/2) := sorry
/-- Blockwise radii on the existing action carrier; arbitrary center is complex. -/
def p11Box {a b : ℕ} (c : P11CVec (a+b)) (r1 r2 : ℝ) : Set (P11CVec (a+b)) :=
  {I | (∀ i : Fin a, ‖I (Fin.castAdd b i)-c (Fin.castAdd b i)‖ < r1) ∧
    ∀ i : Fin b, ‖I (Fin.natAdd a i)-c (Fin.natAdd a i)‖ < r2}
/-- Weighted bound over an arbitrary open action set, using existing wsum and WSummable. -/
def p11WBound {n m : ℕ} (V : Set (P11CVec m)) (s : ℝ)
    (f : P11CVec n × P11CVec m → ℂ) (M : ℝ) : Prop :=
  ∀ I ∈ V, KAM.Weighted.WSummable f s I ∧ KAM.Weighted.wsum f s I ≤ M
theorem aniso_field {a b : ℕ} {c : P11CVec (a+b)}
    {r1 r2 rho1 rho2 s sigma M : ℝ}
    (h1 : 0 < rho1) (h2 : 0 < rho2)
    (hr1 : rho1 < r1) (hr2 : rho2 < r2)
    (hs : 0 < sigma) (hs' : sigma < s)
    {phi : P11Phase (a+b) → ℂ}
    (hphi : DifferentiableOn ℂ phi
      (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2))
    (hp : ∀ z ∈ KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2,
      ∀ i : Fin (a+b), phi (z.1+Pi.single i 1,z.2)=phi z)
    (hM : p11WBound (p11Box c r1 r2) s phi M) :
    ∀ z ∈ KAM.complexStrip (a+b) (s-sigma) ×ˢ
      p11Box c (r1-rho1) (r2-rho2),
      let X := KAM.hamiltonianVectorFieldℂ phi z
      max (‖X.1‖/sigma)
        (max (‖(fun i : Fin a => X.2 (Fin.castAdd b i))‖/rho1)
          (‖(fun i : Fin b => X.2 (Fin.natAdd a i))‖/rho2)) ≤
        M/(min rho1 rho2*sigma) := sorry
theorem polar_average_linear {n : ℕ} {D : Set (P11CVec n)}
    (hD : IsOpen D) {r : ℝ} (hr : 0 < r)
    {G H : P11CVec n × P11Phase n → ℂ}
    (hG : DifferentiableOn ℂ G (D ×ˢ Metric.ball 0 r))
    (hH : DifferentiableOn ℂ H (D ×ˢ Metric.ball 0 r))
    (a b : ℂ) :
    ∀ z ∈ D ×ˢ Metric.ball 0 (Real.pi*r^2/4),
      (∀ i, 0 < (z.2 i).re) →
      p11PolarAverage (a • G+b • H) z =
        a*p11PolarAverage G z+b*p11PolarAverage H z := sorry
theorem polar_average_normalization {n : ℕ}
    (C : P11CVec n → ℂ) (z : P11CVec n × P11CVec n) :
    p11PolarAverage (fun y => C y.1) z = C z.1 ∧
    ∀ i : Fin n,
      p11PolarAverage (fun y => (y.2.1 i^2+y.2.2 i^2)/2) z =
        z.2 i/(2*Real.pi) := sorry
theorem polar_extension_unique {n : ℕ} {D : Set (P11CVec n)}
    (hD : IsOpen D) {R : ℝ} (hR : 0 < R)
    {A B : P11CVec n × P11CVec n → ℂ}
    (hA : DifferentiableOn ℂ A (D ×ˢ Metric.ball 0 R))
    (hB : DifferentiableOn ℂ B (D ×ˢ Metric.ball 0 R))
    (heq : ∀ z ∈ D ×ˢ Metric.ball 0 R, (∀ i, 0 < (z.2 i).re) → A z=B z) :
    EqOn A B (D ×ˢ Metric.ball 0 R) := sorry
theorem aniso_bracket {a b : ℕ} {c : P11CVec (a+b)} {r01 r02 r1 r2 rho1 rho2 s0 s sigma U W : ℝ}
    (h01 : r1 ≤ r01) (h02 : r2 ≤ r02) (h1 : 0 < rho1) (h2 : 0 < rho2)
    (hr1 : rho1 < r1) (hr2 : rho2 < r2) (hs : 0 < sigma) (hs' : sigma < s) (hs0 : s ≤ s0)
    {u w : P11Phase (a+b) → ℂ}
    (hu : DifferentiableOn ℂ u (KAM.complexStrip (a+b) s0 ×ˢ p11Box c r01 r02))
    (hw : DifferentiableOn ℂ w (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2))
    (hup : ∀ z ∈ KAM.complexStrip (a+b) s0 ×ˢ p11Box c r01 r02,
      ∀ i : Fin (a+b), u (z.1+Pi.single i 1,z.2)=u z)
    (hwp : ∀ z ∈ KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2,
      ∀ i : Fin (a+b), w (z.1+Pi.single i 1,z.2)=w z)
    (hU : p11WBound (p11Box c r01 r02) s0 u U) (hW : p11WBound (p11Box c r1 r2) s w W) :
    p11WBound (p11Box c (r1-rho1) (r2-rho2)) (s-sigma) (KAM.Canonical.poissonBracket u w)
      ((sigma/(s0-s+sigma)+min rho1 rho2/min (r01-r1+rho1) (r02-r2+rho2)) /
        (Real.exp 1*min rho1 rho2*sigma)*U*W) := sorry
/-- Rectangular averaging statement; divisor hypotheses are the literal B1, not an assumed output. -/
theorem aniso_avg {a b : ℕ} {c : P11CVec (a+b)} {r1 r2 s T alpha1 alpha2 E : ℝ}
    (hr1 : 0 < r1) (hr2 : 0 < r2) (hs : 0 < s) (hT : 0 < T)
    (hk : 6 ≤ 2*Real.pi*T*s) (ha : 0 < alpha2) (ha' : alpha2 ≤ alpha1)
    {h : P11CVec (a+b) → ℂ} {f : P11Phase (a+b) → ℂ}
    (hh : DifferentiableOn ℂ h (p11Box c r1 r2))
    (hf : DifferentiableOn ℂ f (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2))
    (hp : ∀ z ∈ KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2,
      ∀ i : Fin (a+b), f (z.1+Pi.single i 1,z.2)=f z)
    (hrealh : ∀ x : P11Vec (a+b), KAM.realInclusion (a+b) x ∈ p11Box c r1 r2 →
      (h (KAM.realInclusion (a+b) x)).im=0)
    (hrealf : KAM.Canonical.RealOn (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2) f)
    (hE : 0 ≤ E) (hb : p11WBound (p11Box c r1 r2) s f E)
    (hsmall : E ≤ alpha2*min r1 r2/(128*T))
    (hdiv : ∀ I ∈ p11Box c r1 r2, ∀ k : Fin (a+b) → ℤ, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      (if (fun i : Fin a => k (Fin.castAdd b i))=0 then alpha2 else alpha1) ≤
        ‖p11dotC k (fun i => fderiv ℂ h I (Pi.single i 1))‖) :
    ∃ Psi : P11Phase (a+b) → P11Phase (a+b), ∃ g : P11CVec (a+b) → ℂ,
      ∃ fs : P11Phase (a+b) → ℂ,
      let U := KAM.complexStrip (a+b) (s/6) ×ˢ p11Box c (r1/2) (r2/2)
      DifferentiableOn ℂ Psi U ∧ InjOn Psi U ∧
      DifferentiableOn ℂ g (p11Box c (r1/2) (r2/2)) ∧ DifferentiableOn ℂ fs U ∧
      KAM.Canonical.RealOn U fs ∧
      (∀ I : P11Vec (a+b), KAM.realInclusion (a+b) I ∈ p11Box c (r1/2) (r2/2) →
        (g (KAM.realInclusion (a+b) I)).im=0) ∧
      (∀ z ∈ U, ∀ k : Fin (a+b) → ℤ, Psi (z.1+(fun i => (k i : ℂ)),z.2)=Psi z+((fun i => (k i : ℂ)),0)) ∧
      (∀ z ∈ U, ∀ i : Fin (a+b), fs (z.1+Pi.single i 1,z.2)=fs z) ∧
      (∀ z : Phase (a+b), KAM.realInclusion₂ (a+b) z ∈ U → ∀ i,
        ((Psi (KAM.realInclusion₂ (a+b) z)).1 i).im=0 ∧
        ((Psi (KAM.realInclusion₂ (a+b) z)).2 i).im=0) ∧
      MapsTo Psi U (KAM.complexStrip (a+b) s ×ˢ p11Box c r1 r2) ∧
      (∀ z ∈ U, h (Psi z).2+f (Psi z)=h z.2+g z.2+fs z) ∧
      p11WBound (p11Box c (r1/2) (r2/2)) (s/6) fs (Real.exp (-2*Real.pi*T*s/6)*E) ∧
      p11WBound (p11Box c (r1/2) (r2/2)) (s/6)
        (fun z : P11Phase (a+b) => g z.2-KAM.Weighted.coeff f z.2 0) (130*E^2/(2*Real.pi*alpha2*min r1 r2*s)) ∧
      p11WBound (p11Box c (r1/2) (r2/2)) (s/6)
        (fun z : P11Phase (a+b) => g z.2-KAM.Weighted.coeff f z.2 0) (E/(2*Real.pi*T*s)) ∧
      (∀ z ∈ U,
        2*Real.pi*alpha1*s*‖(fun i : Fin a => (Psi z).2 (Fin.castAdd b i)-z.2 (Fin.castAdd b i))‖ ≤ 3*E ∧
        2*Real.pi*alpha2*s*‖(fun i : Fin b => (Psi z).2 (Fin.natAdd a i)-z.2 (Fin.natAdd a i))‖ ≤ 3*E) ∧
      (∀ z ∈ U, ‖(Psi z).1-z.1‖ ≤ 9*E/(2*Real.pi*alpha2*min r1 r2)) ∧
      (∀ z ∈ U, ∀ u v, KAM.Canonical.symplFormC (fderiv ℂ Psi z u) (fderiv ℂ Psi z v)=
        KAM.Canonical.symplFormC u v) := sorry
/-- Prepared chart rescaling, positions unchanged, both action blocks scaled by eps. -/
def p11Rescale {n : ℕ} (J0 : P11Vec n) (eps : ℝ) (z : P11Phase (n+n)) : P11Phase (n+n) :=
  (z.1, Fin.append (fun i : Fin n => (J0 i : ℂ)+eps*z.2 (Fin.castAdd n i))
    (fun i : Fin n => eps*(2*Real.pi+z.2 (Fin.natAdd n i))))
def p11PreparedBox (n : ℕ) : Set (P11Vec (n+n)) :=
  Set.pi univ (fun _ => Icc (-1/2 : ℝ) (1/2))
def p11K2 {n : ℕ} (C : P11SecularData n) (nu eps : ℝ) : ℝ :=
  3*nu/(Real.pi*(C.sigma/12))*Real.log (1/eps)
def p11s2 {n : ℕ} (C : P11SecularData n) (nu eps : ℝ) : ℝ :=
  min (p11s1 C eps/4) (C.gamma/(8*C.L*p11K2 C nu eps^(C.tau+1)))
structure P11SlowData (n : ℕ) where
  Psi : P11Phase (n+n) → P11Phase (n+n)
  h0 : P11CVec (n+n) → ℂ
  g2 : P11CVec (n+n) → ℂ
  Z : P11CVec (n+n) → ℂ
  f2 : P11Phase (n+n) → ℂ
  f3 : P11Phase (n+n) → ℂ
  deriving Inhabited
/-- Coordinate multi-index derivative on the existing Pi carrier, in fixed coordinate order. -/
def p11PartialVec {n m : ℕ} (alpha : Fin n → ℕ) (f : P11CVec n → P11CVec m) : P11CVec n → P11CVec m :=
  ((List.ofFn (fun i : Fin n => List.replicate (alpha i) i)).flatten).foldl
    (fun g i => fun x => fderiv ℂ g x (Pi.single i 1)) f
def P11SlowSpec {n : ℕ} (D : P11Physical n) (nu eps c : ℝ) (A : P11SlowData n) : Prop :=
  let C := p11SecularData D
  let Fast := p11FastData D eps
  let center : P11CVec (n+n) := Fin.append (KAM.realInclusion n C.J0) (fun _ => 2*Real.pi*eps)
  let V := p11Box center (p11s2 C nu eps) (Real.pi*eps)
  let Vh := p11Box center (p11s2 C nu eps/2) (Real.pi*eps/2)
  let s := C.sigma/12
  let E := c*eps^(5/2 : ℝ)*Real.log (1/eps)^(2*C.tau+1)
  (∀ z ∈ KAM.complexStrip (n+n) s ×ˢ V,
    A.h0 z.2+A.f2 z=p11WorkingH C eps (Fast.map (p11PolarC z))) ∧
  (∀ I ∈ V, A.h0 I=C.h (fun i : Fin n => I (Fin.castAdd n i))+
    eps*p11PolarAverage Fast.G ((fun i : Fin n => I (Fin.castAdd n i)),fun i : Fin n => I (Fin.natAdd n i))) ∧
  (∀ I ∈ V, A.h0 I=C.h (fun i : Fin n => I (Fin.castAdd n i))+
    eps*(C.C (fun i : Fin n => I (Fin.castAdd n i))+
      (∑ i : Fin n, C.Omega (fun j : Fin n => I (Fin.castAdd n j)) i/(2*Real.pi)*I (Fin.natAdd n i))+A.Z I)) ∧
  DifferentiableOn ℂ A.Z
    {I : P11CVec (n+n) | ‖(fun i : Fin n => I (Fin.castAdd n i))-KAM.realInclusion n C.J0‖ < p11s1 C eps/2 ∧
      ‖(fun i : Fin n => I (Fin.natAdd n i))‖ < Real.pi*C.rz^2/16} ∧
  (∀ alpha : Fin n → ℕ, ∀ J, ‖J-KAM.realInclusion n C.J0‖ < p11s1 C eps/4 →
    ∀ rho : P11CVec n, ‖rho-(fun _ => (2*Real.pi*eps : ℂ))‖ < Real.pi*eps →
      ‖p11PartialVec alpha
        (fun J => fun i : Fin n => fderiv ℂ (fun rho : P11CVec n => A.Z (Fin.append J rho)) rho (Pi.single i 1)) J‖ ≤
        c*(eps+p11eta1 C eps)*(∏ i, ((alpha i).factorial : ℝ))*(4/p11s1 C eps)^(∑ i, alpha i)) ∧
  (∀ I ∈ V, ∀ k : Fin (n+n) → ℤ, k ≠ 0 → KAM.Fourier.modeSize k ≤ p11K2 C nu eps →
    (if (fun i : Fin n => k (Fin.castAdd n i))=0 then eps else 1)*
      C.gamma/4*p11K2 C nu eps^(-C.tau) ≤
        ‖p11dotC k (fun i => fderiv ℂ A.h0 I (Pi.single i 1))‖) ∧
  DifferentiableOn ℂ A.h0 V ∧ DifferentiableOn ℂ A.g2 Vh ∧
  DifferentiableOn ℂ A.f2 (KAM.complexStrip (n+n) s ×ˢ V) ∧
  DifferentiableOn ℂ A.f3 (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) ∧
  KAM.Canonical.RealOn (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) A.f3 ∧
  KAM.Canonical.RealOn (KAM.complexStrip (n+n) s ×ˢ V) A.f2 ∧
  (∀ I : P11Vec (n+n), KAM.realInclusion (n+n) I ∈ Vh →
    (A.g2 (KAM.realInclusion (n+n) I)).im=0 ∧ (A.h0 (KAM.realInclusion (n+n) I)).im=0) ∧
  (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh →
    ∀ i, ((A.Psi (KAM.realInclusion₂ (n+n) z)).1 i).im=0 ∧
      ((A.Psi (KAM.realInclusion₂ (n+n) z)).2 i).im=0) ∧
  (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh, ∀ i : Fin (n+n),
    A.f3 (z.1+Pi.single i 1,z.2)=A.f3 z) ∧
  DifferentiableOn ℂ A.Psi (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) ∧
  (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh, ∀ u v,
    KAM.Canonical.symplFormC (fderiv ℂ A.Psi z u) (fderiv ℂ A.Psi z v)=KAM.Canonical.symplFormC u v) ∧
  (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh, ∀ k : Fin (n+n) → ℤ,
    A.Psi (z.1+(fun i => (k i : ℂ)),z.2)=A.Psi z+((fun i => (k i : ℂ)),0)) ∧
  InjOn A.Psi (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) ∧
  MapsTo A.Psi (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) (KAM.complexStrip (n+n) s ×ˢ V) ∧
  p11WBound V s A.f2 E ∧
  E ≤ (eps*C.gamma/4*p11K2 C nu eps^(-C.tau))*Real.pi*eps/(128*p11K2 C nu eps) ∧
  p11WBound Vh (s/6) A.f3 (eps^nu*E) ∧
  p11Bound Vh A.g2 (c*eps^3*Real.log (1/eps)^(5*C.tau+2)) ∧
  (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh,
    A.h0 (A.Psi z).2+A.f2 (A.Psi z)=A.h0 z.2+A.g2 z.2+A.f3 z) ∧
  (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh,
    ‖(fun i : Fin n => (A.Psi z).2 (Fin.natAdd n i)-z.2 (Fin.natAdd n i))‖ ≤
      c*eps^(3/2 : ℝ)*Real.log (1/eps)^(3*C.tau+1) ∧
    ‖(fun i : Fin n => (A.Psi z).2 (Fin.castAdd n i)-z.2 (Fin.castAdd n i))‖ ≤
      c*eps^(5/2 : ℝ)*Real.log (1/eps)^(3*C.tau+1) ∧
    ‖(A.Psi z).1-z.1‖ ≤ c*eps^(1/2 : ℝ)*Real.log (1/eps)^(3*C.tau+1))
theorem avg_slow {n : ℕ} (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ eps2 c2 : ℝ, 0 < eps2 ∧ eps2 < 1 ∧ 1 ≤ c2 ∧
      ∀ eps, 0 < eps → eps ≤ eps2 → ∃ A, P11SlowSpec D nu eps c2 A := sorry
open Classical in
def p11SlowConstant {n : ℕ} (D : P11Physical n) (nu : ℝ) : ℝ :=
  if h : 1 ≤ nu then ((avg_slow D h).choose_spec).choose else 1
open Classical in
def p11SlowData {n : ℕ} (D : P11Physical n) (nu eps : ℝ) : P11SlowData n :=
  if h : ∃ A, P11SlowSpec D nu eps (p11SlowConstant D nu) A then h.choose else default
structure P11PreparedData (n : ℕ) where
  N : P11CVec (n+n) → ℂ
  P : P11Phase (n+n) → ℂ
  chain : Phase (n+n) → Phase (n*2)
  checkW : P11Vec (n+n) → P11Vec (n+n)
  deriving Inhabited
def p11PreparedFreq {n : ℕ} (Q : P11PreparedData n) (I : P11CVec (n+n)) : P11CVec (n+n) :=
  fun i => fderiv ℂ Q.N I (Pi.single i 1)
def p11PreparedFreqR {n : ℕ} (Q : P11PreparedData n) (I : P11Vec (n+n)) : P11Vec (n+n) :=
  fun i => (p11PreparedFreq Q (KAM.realInclusion (n+n) I) i).re
def P11PreparedSpec {n : ℕ} (D : P11Physical n) (nu eps c : ℝ) (Q : P11PreparedData n) : Prop :=
  let C := p11SecularData D
  let A := p11PatchData D
  let U := KAM.actionNbhd (p11PreparedBox n) 1
  let V := KAM.complexStrip (n+n) (C.sigma/72) ×ˢ U
  let smallV := KAM.actionNbhd (p11PreparedBox n) (3/4)
  let W := p11PreparedFreq Q
  let ell := Real.log (1/eps)
  let exponent := 5*C.tau+2+(C.tau+1)*(A.mu+1)
  (let A := p11SlowData D nu eps
   (∀ z ∈ V, let y := p11Rescale C.J0 eps z
     Q.N z.2=(A.h0 y.2+A.g2 y.2)/eps ∧ Q.P z=A.f3 y/eps) ∧
   ∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ V →
     let w := (p11FastData D eps).map (p11PolarC (A.Psi (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z))))
     Q.chain z=C.chart ((fun i => (w.1 i).re),fun i => (w.2 i).re)) ∧
  DifferentiableOn ℂ Q.N U ∧ DifferentiableOn ℂ Q.P V ∧
  (∀ z ∈ V, ∀ i : Fin (n+n), Q.P (z.1+Pi.single i 1,z.2)=Q.P z) ∧
  KAM.Canonical.RealOn V (fun z => Q.N z.2+Q.P z) ∧
  KAM.Canonical.RealOn V Q.P ∧
  (∀ I : P11Vec (n+n), KAM.realInclusion (n+n) I ∈ U → (Q.N (KAM.realInclusion (n+n) I)).im=0) ∧
  p11Bound V Q.P (c*eps^(nu+3/2)*ell^(2*C.tau+1)) ∧
  p11Bound smallV W (2*C.L+1) ∧
  (∀ I ∈ smallV, ‖fderiv ℂ W I‖ ≤ 2*C.L+1) ∧
  (∀ y : P11Vec (n+n), ‖y‖ ≤ 5/4 →
    p11PreparedFreqR Q y=Fin.append
      (fun i : Fin n => Q.checkW y (Fin.castAdd n i))
      (fun i : Fin n => eps*Q.checkW y (Fin.natAdd n i))) ∧
  (∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    let psi := fun J : P11Vec n => Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho)
    p11JetBound true A.mu {J | ‖J-C.J0‖ < p11s2 C nu eps/4} (psi-A.varpi) (c*eps*ell^exponent)) ∧
  (∀ direction, p11euclid direction=1 → ∀ j, 1 ≤ j → j ≤ A.mu+1 →
    ∀ y ∈ p11thick (p11PreparedBox n) (1/4),
      p11op (p11scalar 2 (p11PreparedFreqR Q) direction) j y ≤ (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2) ∧
  (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ V →
    fixedHamiltonian D.G D.m0 D.m eps (Q.chain z)=eps*(Q.N (KAM.realInclusion (n+n) z.2)+
      Q.P (KAM.realInclusion₂ (n+n) z)).re)
def p11M0 (n mu : ℕ) (L : ℝ) : ℝ :=
  (2*n+1 : ℝ)^(mu+1)*(2*L+1)
def p11SlowNormalizedFreq {n : ℕ} (D : P11Physical n)
    (nu eps : ℝ) (J rho : P11Vec n) : P11Vec (n+n) :=
  let A := p11SlowData D nu eps
  let I := Fin.append (KAM.realInclusion n J)
    (fun i : Fin n => (eps*(2*Real.pi+rho i) : ℂ))
  let W : P11CVec (n+n) :=
    fun i => fderiv ℂ (A.h0+A.g2) I (Pi.single i 1)
  Fin.append (fun i : Fin n => (W (Fin.castAdd n i)).re)
    (fun i : Fin n => (W (Fin.natAdd n i)).re/eps)
def P11PreparedFullSpec {n : ℕ} (D : P11Physical n)
    (nu eps c : ℝ) (Q : P11PreparedData n) : Prop :=
  let C := p11SecularData D
  let A := p11PatchData D
  let ell := Real.log (1/eps)
  let exponent := 5*C.tau+2+(C.tau+1)*(A.mu+1)
  P11PreparedSpec D nu eps c Q ∧
  (∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    ∀ J : P11Vec n, ‖J-C.J0‖ < p11s2 C nu eps/4 →
      Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho) =
        p11SlowNormalizedFreq D nu eps J rho) ∧
  (∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    p11JetBound true A.mu {J | ‖J-C.J0‖ < p11s2 C nu eps/4}
      ((fun J => Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho))-A.varpi)
      (c*eps*ell^exponent)) ∧
  p11JetBound true A.mu (p11thick (p11PreparedBox n) (1/4))
    (p11PreparedFreqR Q) (p11M0 n A.mu C.L) ∧
  (∀ direction, p11euclid direction=1 →
    ∀ y ∈ p11thick (p11PreparedBox n) (1/4),
      p11op (p11scalar 2 (p11PreparedFreqR Q) direction) 0 y ≤
        (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2)
theorem prepared {n : ℕ} (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ eps3 c3 : ℝ, 0 < eps3 ∧ eps3 < 1 ∧ 1 ≤ c3 ∧
    ∀ eps, 0 < eps → eps ≤ eps3 →
      5*eps ≤ p11s2 (p11SecularData D) nu eps ∧
      c3*eps*Real.log (1/eps)^(5*(p11SecularData D).tau+2+
        ((p11SecularData D).tau+1)*((p11PatchData D).mu+1)) ≤ 1 ∧
      ∃ Q, P11PreparedFullSpec D nu eps c3 Q := sorry
open Classical in
def p11PreparedData {n : ℕ} (D : P11Physical n) (nu eps c : ℝ) : P11PreparedData n :=
  if h : ∃ Q, P11PreparedFullSpec D nu eps c Q then h.choose else default
/-- The directional argument pays epsilon^mu before the target block pays epsilon^2. -/
theorem amount {n : ℕ} (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ epsA c3 : ℝ, 0 < epsA ∧ epsA < 1 ∧ 1 ≤ c3 ∧
    ∀ eps, 0 < eps → eps ≤ epsA →
      let Q := p11PreparedData D nu eps c3
      P11PreparedFullSpec D nu eps c3 Q ∧
      (1/2 : ℝ)*eps^((p11PatchData D).mu+2)*(p11PatchData D).beta ≤
        index_def 2 (p11PatchData D).mu (p11PreparedFreqR Q) (p11PreparedBox n) := sorry
/-- General affine chart-scaling helper for the scalar amount (no identification of rho=1 and rho=2). -/
theorem chart_scaling {n m rho mu : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {K V : Set (P11Vec n)} (hK : IsCompact K) (hne : K.Nonempty) (hV : IsOpen V) (hKV : K ⊆ V)
    {w : P11Vec n → P11Vec m} (hw : ContDiffOn ℝ mu w V)
    (y0 : P11Vec n) {lambda : ℝ} (hl : 0 < lambda) :
    min 1 (lambda^mu)*index_def rho mu w K ≤
      index_def rho mu (fun y => w (y0+lambda • y)) ((fun y => y0+lambda • y) ⁻¹' K) := sorry
/-- Source chart-scaling geometry and Lebesgue measure transport. -/
theorem chart_scaling_geometry {n : ℕ} (y0 : P11Vec n)
    {lambda : ℝ} (hl : 0 < lambda) (K : Set (P11Vec n))
    (hK : IsCompact K) (v : ℝ) :
    let A := fun y : P11Vec n => y0+lambda • y
    Metric.diam (A ⁻¹' K) = Metric.diam K/lambda ∧
    p11thick (A ⁻¹' K) (v/lambda) = A ⁻¹' p11thick K v ∧
    ∀ E : Set (P11Vec n),
      volume (A ⁻¹' E) = ENNReal.ofReal (lambda^n)⁻¹*volume E := sorry
theorem chart_scaling_jets {n m k : ℕ} (hn : 1 ≤ n)
    {V : Set (P11Vec n)} (hV : IsOpen V)
    {f : P11Vec n → P11Vec m} (hf : ContDiffOn ℝ k f V)
    (y0 : P11Vec n) {lambda : ℝ} (hl : 0 < lambda) :
    ∀ j ≤ k, ∀ y, y0+lambda • y ∈ V →
      p11dg (fun x => f (y0+lambda • x)) j y =
        lambda^j*p11dg f j (y0+lambda • y) ∧
      p11op (fun x => f (y0+lambda • x)) j y =
        lambda^j*p11op f j (y0+lambda • y) := sorry
theorem chart_scaling_good {n m : ℕ} (y0 : P11Vec n)
    {lambda : ℝ} (hl : 0 < lambda) (K : Set (P11Vec n))
    (wt : (Fin m → ℤ) → P11Vec n → P11Vec m)
    (psi : (Fin m → ℤ) → ℝ) :
    let A := fun y : P11Vec n => y0+lambda • y
    p11Good (A ⁻¹' K) (fun k y => wt k (A y)) psi =
      A ⁻¹' p11Good K wt psi ∧
    volume (K \ p11Good K wt psi) =
      ENNReal.ofReal (lambda^n)*
        volume ((A ⁻¹' K) \ p11Good (A ⁻¹' K) (fun k y => wt k (A y)) psi) := sorry
/-- Source chart-scaling (b): transfer the upper full-tensor derivative bound. -/
theorem chart_scaling_upper {n m k : ℕ} (hn : 1 ≤ n)
    {V : Set (P11Vec n)} (hV : IsOpen V) {f : P11Vec n → P11Vec m}
    (hf : ContDiffOn ℝ k f V) {E : Set (P11Vec n)} (hEV : E ⊆ V)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ j, 1 ≤ j → j ≤ k → ∀ y ∈ E, p11op f j y ≤ M)
    (y0 : P11Vec n) {lambda : ℝ} (hl : 0 < lambda) :
    ∀ j, 1 ≤ j → j ≤ k → ∀ y, y0+lambda • y ∈ E →
      p11op (fun x => f (y0+lambda • x)) j y ≤ max 1 (lambda^k)*M := sorry
/-- Source chart-scaling (c): diagonal closeness is rechecked after scaling. -/
theorem chart_scaling_closeness {n m mu : ℕ} (hn : 1 ≤ n)
    {V : Set (P11Vec n)} (hV : IsOpen V) {f : P11Vec n → P11Vec m}
    (hf : ContDiffOn ℝ mu f V) {E : Set (P11Vec n)} (hEV : E ⊆ V)
    {theta beta' : ℝ} (ht : 0 ≤ theta) (hb : p11JetBound true mu E f theta)
    (y0 : P11Vec n) {lambda : ℝ} (hl : 0 < lambda)
    (hrecheck : max 1 (lambda^mu)*theta ≤ beta'/2) :
    p11JetBound true mu ((fun y => y0+lambda • y) ⁻¹' E)
      (fun y => f (y0+lambda • y)) (beta'/2) := sorry
/-- Unconditional physical output: Part 13 owns FixKol assembly and the frozen provider. -/
theorem wrapper {n : ℕ} (D : P11Physical n) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps, 0 < eps → eps < eps0 →
      ∃ S : Set (Phase (n*2)), MeasurableSet S ∧ 0 < volume S ∧ volume S < ⊤ ∧
        S ⊆ circularTube D.G D.m0 D.m D.a (p11Zeta D) ∧
        ∀ z ∈ S, ∃ w : P11Vec (n*2), ∃ K : P11Vec (n*2) → Phase (n*2),
          ∃ theta0, z=K theta0 ∧ Set.range K ⊆ S ∧
            IsPhysicalTorus (fixedHamiltonian D.G D.m0 D.m eps) w K := sorry
/-- wr-nu keeps the order independent of epsilon and every intermediate averaging constant. -/
def p11Order (mu : ℕ) (kappa a : ℝ) : ℝ :=
  max ((mu+2)*(mu*(mu+1)+2)+2) (((mu+2)*a+1)/kappa+2)
/-- Generic logarithmic domination needed in both finite averaging stages and wr-nu. -/
theorem e4 {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    Tendsto (fun eps : ℝ => eps^a*Real.log (1/eps)^b) (nhdsWithin 0 (Ioi 0)) (nhds 0) := sorry
theorem e5 (a b : ℕ) (h : Odd a ∨ Odd b) :
    (∫ t in (0 : ℝ)..1, Real.sin (2*Real.pi*t)^a*Real.cos (2*Real.pi*t)^b)=0 := sorry
/-- Reality of the maximal homological solution; this supplies the guard used by cs-lip. -/
theorem homological_maximal_real {n : ℕ} {r T D : ℝ} (hr : 0 < r) (hT : 0 < T) (hD : 0 < D)
    {B : Set (P11CVec n)} (hB : IsOpen B) (w : P11CVec n → P11CVec n)
    (hw : DifferentiableOn ℂ w B)
    (hdiv : ∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    (P : P11CVec n × P11CVec n → ℂ) (hP : p11AngleClass r B P)
    (hpoly : ∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T P z=P z)
    (hwr : ∀ b : P11Vec n, KAM.realInclusion n b ∈ B → ∀ i, (w (KAM.realInclusion n b) i).im=0)
    (hpr : ∀ x b : P11Vec n, KAM.realInclusion n b ∈ B →
      (P (KAM.realInclusion n x,KAM.realInclusion n b)).im=0) :
    ∀ x b : P11Vec n, KAM.realInclusion n b ∈ B →
      (p11Solve T w P (KAM.realInclusion n x) (KAM.realInclusion n b)).im=0 := sorry
/-- Every-order parameter clause of homological-maximal(c), scalar and average. -/
theorem homological_maximal_param {n : ℕ} {r delta T D M t tp : ℝ}
    (hr : 0 < r) (hd : 0 < delta) (hdr : delta < r) (hT : 0 < T)
    (hD : 0 < D) (hM : 0 ≤ M) {E : Set (P11Vec n)} (htp : 0 < tp) (htt : tp < t)
    (w : P11CVec n → P11CVec n) (hw : DifferentiableOn ℂ w (KAM.actionNbhd E t))
    (hdiv : ∀ b ∈ KAM.actionNbhd E t, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    (P : P11CVec n × P11CVec n → ℂ) (hP : p11AngleClass r (KAM.actionNbhd E t) P)
    (hpoly : ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t,
      KAM.Weighted.truncate T P z=P z)
    (hb : p11Bound (KAM.complexStrip n r ×ˢ KAM.actionNbhd E t) P M)
    {j : ℕ} (hj : 1 ≤ j) :
    ∀ theta ∈ KAM.complexStrip n (r-delta), ∀ b ∈ KAM.actionNbhd E tp,
      ‖iteratedFDeriv ℂ j (p11Solve T w P theta) b‖ ≤
        (j : ℝ)^j*p11Lambda n delta*M/(Real.pi*D*(t-tp)^j) ∧
      ‖iteratedFDeriv ℂ j (p11AngleAverage P) b‖ ≤ (j : ℝ)^j*M/(t-tp)^j := sorry
/-- Sign bridge for the existing frozen field and Poisson bracket, independent of any solving equation. -/
theorem p11_normal_affine_bracket {n : ℕ} (h : ℂ) (w : P11CVec n)
    {p0 : P11CVec n → ℂ} {p1 : P11CVec n → P11CVec n} {z : P11Phase n}
    (h0 : DifferentiableAt ℂ p0 z.1) (h1 : DifferentiableAt ℂ p1 z.1) :
    KAM.Canonical.poissonBracket (fun z : P11Phase n => h+∑ i, w i*z.2 i) (p11Affine p0 p1) z=
      -(fderiv ℂ p0 z.1 w+∑ i, fderiv ℂ p1 z.1 w i*z.2 i) := sorry
/-- Coefficient bounds of cutoff(a), needed separately by cs-cutoff. -/
theorem cutoff_coefficients {n : ℕ} (hn : 1 ≤ n) {r s T d eps : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : 0 ≤ T) (hd : 0 < d) (hdr : d < r)
    (he : 0 ≤ eps) {B : Set (P11CVec n)} (hB : IsOpen B) {R : P11Family n → ℂ}
    (hR : p11Admissible r s B R) (hb : p11Bound (domain_def n r s B) R eps) :
    p11Bound (KAM.complexStrip n (r-d) ×ˢ B) (p11R0 T R) ((1+p11Error n T d)*eps) ∧
    p11Bound (KAM.complexStrip n (r-d) ×ˢ B) (p11R1 T R) ((1+p11Error n T d)*eps/s) ∧
    -- D29 (2026-10-28): `z.2 ∈ B →` added; the unguarded clause was false (see the companion-results note).
    ∀ z, z.2 ∈ B → p11Cutoff T R z=p11R0 T R (z.1.1,z.2)+∑ i, p11R1 T R (z.1.1,z.2) i*z.1.2 i := sorry
/-- Additional clauses of canonical-step(ii), with the same unmodified source premises. -/
theorem canonical_step_simple_inverse {n : ℕ} {S : P11Step n} {h : P11CVec n → ℂ}
    {w : P11CVec n → P11CVec n} {R : P11Family n → ℂ} (H : P11StepHyp S h w R) :
    let U := domain_def n (S.r-S.d-S.delta-2*S.sigma) (S.q*S.s) (KAM.actionNbhd S.E S.t)
    (∃ Theta : P11CVec n × P11CVec n → P11CVec n,
      ∃ M : P11CVec n × P11CVec n → P11CVec n →L[ℂ] P11CVec n,
        ∃ v : P11CVec n × P11CVec n → P11CVec n,
          ∀ z ∈ U, p11StepMap S w R z=(Theta (z.1.1,z.2),M (z.1.1,z.2) z.1.2+v (z.1.1,z.2)) ∧
            ∀ a b, (∑ i, fderiv ℂ (fun theta => Theta (theta,z.2)) z.1.1 a i *
              M (z.1.1,z.2) b i)=∑ i, a i*b i) ∧
    ∀ z ∈ U,
      p11Flow (p11StepPhi S w R z.2) (S.r-S.d-S.delta) S.s S.sigma (-1) (p11StepMap S w R z)=z.1 ∧
      p11StepMap S w R
        (p11Flow (p11StepPhi S w R z.2) (S.r-S.d-S.delta) S.s S.sigma (-1) z.1,z.2)=z.1 := sorry
/-- lambda definition, its lattice identity and both bounds are separate from the cohomological theorem. -/
theorem p11_lambda_spec {n : ℕ} (hn : 1 ≤ n) {delta : ℝ} (hd : 0 < delta) :
    Summable (fun k : {k : Fin n → ℤ // k ≠ 0} =>
      Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k.val)) ∧
    (∑' k : {k : Fin n → ℤ // k ≠ 0}, Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k.val))=
      p11Lambda n delta ∧
    p11Lambda n delta ≤ (1+1/(Real.pi*delta))^n-1 ∧
    p11Lambda n delta ≤ (4*n/(Real.pi*delta))^n := sorry
/-- The least positive index is meaningful only after rank_compact gives nonempty candidates. -/
def p11Index {n m : ℕ} (rho : ℕ) (w : P11Vec n → P11Vec m) (K : Set (P11Vec n)) : ℕ :=
  sInf {mu | 1 ≤ mu ∧ 0 < index_def rho mu w K}
def p11Amount {n m : ℕ} (rho : ℕ) (w : P11Vec n → P11Vec m) (K : Set (P11Vec n)) : ℝ :=
  index_def rho (p11Index rho w K) w K
/-- data-star: all the parameter geometry is fixed before epsilon; output bounds are uniform. -/
theorem data_star {n : ℕ} (D : P11Physical n) :
    IsCompact (p11PreparedBox n) ∧ volume (p11PreparedBox n)=1 ∧
    Metric.diam (p11PreparedBox n)=1 ∧
    0 < (1/4 : ℝ) ∧ 0 < (1/2 : ℝ) ∧
    max ((n : ℝ)*(p11PatchData D).mu) (2*n) >
      max (((n+n : ℕ) : ℝ)*(p11PatchData D).mu/2-1)
        (((n+n : ℕ) : ℝ)-1) ∧
    ∀ nu : ℝ, 1 ≤ nu →
      ∃ epsA c : ℝ, 0 < epsA ∧ epsA < 1 ∧ 1 ≤ c ∧
      ∀ eps, 0 < eps → eps ≤ epsA →
        let C := p11SecularData D
        let A := p11PatchData D
        let beta := (1/2 : ℝ)*eps^(A.mu+2)*A.beta
        let M := (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2
        0 < beta ∧ beta ≤ min 1 M ∧
        1 ≤ p11M0 n A.mu C.L ∧
        let Q := p11PreparedData D nu eps c
        P11PreparedFullSpec D nu eps c Q ∧
          beta ≤ index_def 2 A.mu (p11PreparedFreqR Q) (p11PreparedBox n) := sorry
/-- af-rest(f): joint parameter holomorphy is a proved augmented-field bridge. -/
theorem affine_flow_param {n : ℕ} {B : Set (P11CVec n)} (hB : IsOpen B)
    (p0 : P11CVec n × P11CVec n → ℂ) (p1 : P11CVec n × P11CVec n → P11CVec n)
    {r s sigma A : ℝ}
    (h0 : DifferentiableOn ℂ p0 (KAM.complexStrip n r ×ˢ B))
    (h1 : DifferentiableOn ℂ p1 (KAM.complexStrip n r ×ˢ B))
    (H : ∀ b ∈ B, P11AffineHyp (fun theta => p0 (theta,b)) (fun theta => p1 (theta,b)) r s sigma A) :
    DifferentiableOn ℂ (fun z : P11CVec n × P11Phase n =>
      p11Flow (p11Affine (fun theta => p0 (theta,z.1)) (fun theta => p1 (theta,z.1))) r s sigma 1 z.2)
      (B ×ˢ KAM.Weighted.Dom n {0} (3*s/4) (r-3*sigma/2)) := sorry
/-- rl-const: induced max operator bound, from an actual finite trigonometric polynomial. -/
theorem p11_trig_derivative_bound {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T)
    (S : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → P11CVec n)
    (hdeg : ∀ k ∈ S, KAM.Fourier.modeSize k ≤ T) (x : P11Vec n) :
    ‖fderiv ℂ (fun theta : P11CVec n => ∑ k ∈ S, KAM.character k theta • a k)
      (KAM.realInclusion n x)‖ ≤
      2*Real.pi*T*sSup (Set.range (fun i : Fin n => ∑ k ∈ S.erase 0, ‖a k i‖)) := sorry
#print axioms KAM.Planetary.sublevel
#print axioms KAM.Planetary.canonical_step
#print axioms KAM.Planetary.wrapper
#print axioms KAM.Planetary.prepared
#print axioms KAM.Planetary.data_star
#print axioms KAM.Planetary.chart_scaling_closeness
end KAM.Planetary
end
```
