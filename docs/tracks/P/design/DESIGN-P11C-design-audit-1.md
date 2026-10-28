# P11C independent design audit 1

**Overall verdict: PASS WITH NOTES.** No material signature-fidelity, frozen-object, carrier, norm, or constant-dependence defect survived the refutation pass. This is approval of a design surface, not proof completion or permission to skip its explicit upstream reconciliation gates. Notes N1–N2 concern provenance and the package dependency table.

## Scope, authority and frozen inputs

Audit date: 2026-10-28. Tier 2, refute-first source/signature correspondence audit. Authority: the user's instructions, AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-design.md`, and the designer's handoff. Only this report is a lasting edit. The requested signature copy and disposable name probe are the expressly permitted scratch exceptions. No git mutation, source repair, frozen/manifest edit, production build or external communication was performed.

Frozen-v1 worktree HEAD: `cd78f327760a4827e26d1346c0e805b70f1fa456`; comparison `inp` at inspection: `cd23a4d1097be186cd5c5703bf8687af6373121d`. `git diff inp...HEAD` contains only the 1,132-line design document.

| Input | SHA-256 |
|---|---|
| `docs/tracks/P/design/P11C-LEAN-DESIGN.md` | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |
| `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` | `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079` |
| `blueprint-P/parts/p11a5-quantitative-theorem.tex` | `f4ea938ec9baf0a280fded708fc7b2bbac4584a6347ad9d49da1291c73ad9b1d` |
| `blueprint-P/parts/p11b-planar-torsion.tex` | `f8ce70a3460c855e1e04ea1a8d39c7a32a550f38b8097ca993a6a17efe012bf1` |
| Integration `docs/graph/P/DEPGRAPH.md` | `5b1eff327a09a63a553686ba14a4763978e0f589fde8ad42cc67d6545f819f44` |
| Integration `docs/graph/P/packets/P-p11a45.nodes.md` | `555a803096ee7c19d46afb01bfdf660d35bac0abe7320c6609bc95fa55ae0aed` |
| Integration `docs/graph/P/packets/P-p11b.nodes.md` | `e271dc184301b0027ad1ad06190dba86cdd069e7553510d7fbbf1f560aa2a87b` |
| `.drafts/handoff-DESIGN-P11C.md` | `185b318fdb71d40fab06ddd3622abe229f1c745e7be141bd6ca1f9f4caace2ee` |

Appendix A is byte-identical to the supplied signature file. Both blueprint files are byte-identical to integration. Mechanical extraction found **83 scoped graph records and 83 distinct design rows**, with no missing/extra IDs; the source-only physical-interface addition is also designed. The signatures contain **44 theorem declarations, 80 definitions and 5 structures**, 815 lines. Every declaration has a row below; generated structure projections are covered with their owning structure.

## Findings and adversarial disposition

**N1 — Low; provenance.** Design section 4 calls the integration graph SHA-256 `14e720a80bc40bfec284dd0acbb83f93ac5bd9b3750f21a34bd592af852e9f64` its scope authority. The currently read graph has the hash above. **Proposed fix:** refresh the recorded graph snapshot/hash and preserve the scoped 83-ID inventory. Refutation check: recomputing the current inventory yields exactly the same 83 design rows, and both statement-source files are byte-identical; this is not evidence of a missing scoped node or altered signature.

**N2 — Low; package execution detail.** Section 7's advertised “exact module/import DAG” omits helper dependencies. The node table assigns `p11c_homogeneousPart` to T6 (section 4, quartic-explicit row), but T12's `quadratic_physical_bridge` already uses it (signature L716–720) while T12 is wave 3 and T6 wave 4. T15's frozen bridge uses `p11c_slowLength` owned by T1, although T15 lists “frozen definitions only” and is also wave 1. Q4 owns `displacement_power_flat`, which uses `p11c_displacement` from the quantitative interface, but the DAG omits Interface→Budget. **Proposed fix:** put the generic jet/homogeneous-part helpers in Setting (T1), add Setting→FrozenBridge and Interface→Budget, and schedule FrozenBridge after Setting (wave 2 suffices). Alternatively name a small earlier common helper module. Refutation check: these are actual identifier references in the signatures, not speculative proof dependencies; moving only generic definitions avoids any substantive cycle or statement change. The existing line budget has ample room. This is a dispatch-table correction, not a false theorem.

No F-numbered mathematical finding was confirmed; therefore no corrected theorem signature is required. No additional source premise or weakened target is proposed.

## Theorem signatures

All names in this and the next table are in `KAM.Planetary`. Source abbreviations below expand as `bpP:<label>`; line numbers refer to the frozen-v1 standalone signature file, not the longer appendix.

| Lean name and line | Blueprint label | Verdict | Reason |
|---|---|---|---|
| `qb_comp` L129 | `p11a:bu-minor` | PASS | Positive minorant; M0 comparison retains a positive upper bound. |
| `qb_mono` L133 | `p11a:bu-mono` | PASS | Product order has exactly the required monotonic directions. |
| `qb_poly` L164 | `p11a:bu-poly` | PASS | c′ precedes other rates and all data; exact D,G,L,J,X,H,B. |
| `qb_beta` L176 | `p11a:bu-beta` | PASS | All varying beta values are inside one existential constant. |
| `budget` L180 | `p11a:budget` | PASS | Comparison, order and beta power; general-rate clause supplied separately by qb_poly. |
| `zero_case` L243 | `p11a:zero-case` | PASS | Explicit 2-gamma good set, unperturbed torus and frozen frequencyMap. |
| `weak_kam_quantitative` L249 | `p11a:weak-kam-quantitative` | PASS | A1–A4 inputs; K1–K4 output, K5–K6 separate data lemmas; correct cDelta dependence. |
| `displacement_power_flat` L257 | `p11a:weak-kam-quantitative` | PASS | K6: exponent 1/2 and loss (mu+1)/rho, uniformly in replacement beta. |
| `physical_interface` L264 | `p11a:physical-interface` | PASS | Borel positive finite measure, displacement, global curves, local uniqueness and lattice saturation. |
| `orbit` L334 | `p11b:orbit` | PASS | Exact degree-four Laurent jet; full open-disc analyticity supplied by orbit_analytic. |
| `laplace_red` L341 | `p11b:laplace-red` | PASS | All three recurrences; arbitrary real s, guarded recurrence use. |
| `pair_jet` L371 | `p11b:pair-jet` | PASS | Actual pair integral has the displayed jet through order five. |
| `quartic_explicit` L386 | `p11b:quartic-explicit` | PASS | Actual frozen moving/fixed secular averages, factorial-normalized fourth derivative. |
| `char` L422 | `p11b:char` | PASS | Positive character covariance, finite mode support, reconstruction and reality. |
| `homological` L434 | `p11b:homological` | PASS | Analytic real quartic witness and correct bracket sign; NR4 is a source premise. |
| `real_analytic_hamiltonian_local_flow` L442 | `p11b:e-ode` | PASS | New real local existence, joint time/initial-data analyticity and symplecticity; no SmallField assumption. |
| `flow` L456 | `p11b:flow` | PASS | Compact-uniform radius, analytic time-one map, cubic displacement, inverse; [-1,1] strengthens [0,1]. |
| `real_lie_taylor` L470 | `p11b:lie` | PASS | New real chain-rule/integral Taylor bridge along an actual solution. |
| `lie` L477 | `p11b:lie` | PASS | Vanishing 5-jet, compact-uniform sixth-order bound; slow-independent C cancels. |
| `lift_map` L502 | `p11b:lift-map` | PASS | Analytic symplectic injective flow lift with all angle translations; composition supplied by BirkhoffResult. |
| `beta_formula` L539 | `p11b:beta-formula` | PASS | SO(2) rotation, spectral projector and frozen R=(x²+y²)/2; factors 8/4. |
| `hasSecularBirkhoffForm_of_sixth_order` L547 | `p11b:birkhoff-form` | PASS | Separately named conditional helper; integrability and sixth-order estimate imply exact frozen predicate. |
| `global_planar_frame` L570 | `p11b:birkhoff-form` | PASS | Explicit global oriented eigenframe; discharges the reason for simply-connectedness. |
| `birkhoff_form` L626 | `p11b:birkhoff-form` | PASS | Actual same T for both perturbations; r,C precede Oa; exact frozen averaged predicate. |
| `asymptotics` L638 | `p11b:asymptotics` | PASS | All three entry limits, determinant -117/16, relative O(alpha²), homogeneity -2. |
| `torsion` L645 | `p11b:torsion` | PASS | Analytic nonzero determinant, open dense full-measure sets, including simultaneous Phi4 locus. |
| `remain` L655 | `p11b:remain` | PASS | Compact positivity helper; nonvanishing and continuity are precisely the premises needed here. |
| `torsion_patch_geometry` L662 | `p11b:patch` | PASS | Distinct geometric helper; full patch theorem additionally supplies frequency and Birkhoff outputs. |
| `orbit_analytic` L671 | `p11b:orbit` | PASS | Full intended eccentricity disc, not merely the germ at zero. |
| `orbit_poincare_bridge` L674 | `p11b:orbit` | PASS | Actual delivered poincare/poincareV; positive action and Gamma<L ensure k=sqrt(1-|v|²). |
| `laplace_up` L680 | `p11b:laplace-red` | PASS | s>=1/2 guards 1/s; exact two upward identities and recurrence. |
| `laplace_rational_reduction` L689 | `p11b:laplace-red` | PASS | Rational polynomial numerator/denominator with no poles on (0,1). |
| `pair_series` L707 | `p11b:pair-jet` | PASS | Analytic on (-1,1), exact listed coefficients through order six (B through seven). |
| `pair_quadratic_consistency` L712 | `p11b:pair-jet` | PASS | A=alpha b(1)/4 and B=-alpha b(2)/2, correct normalized Laplace convention. |
| `quadratic_physical_bridge` L716 | `p11b:sec-beta#data` | PASS | Actual physical second homogeneous jet equals both Q quadratic blocks. |
| `character_bracket` L722 | `p11b:char` | PASS | Frozen Hamiltonian sign agrees with positive i(k·Omega) character derivative. |
| `character_polynomial` L728 | `p11b:char` | PASS | Polynomial degree<=4 plus exact degree-four homogeneity and analytic coefficients. |
| `beta_properties` L737 | `p11b:beta-def` | PASS | Entrywise analyticity and symmetric matrix; no bare-matrix instance. |
| `full_lift_hamiltonian` L741 | `p11b:lift-map` | PASS | Actual full Hamilton equations, including angle derivative, on the same action/slow tube. |
| `asymptotics_uniform_ratio` L752 | `p11b:asymptotics` | PASS | Common C,alpha0 before every physical scale except the fixed mass ratio. |
| `patch` L782 | `p11b:patch` | PASS | Near every axis vector: doubled cube, uniform torsion, same-patch full frequency and Birkhoff data. |
| `laplace_reduction_denominator` L794 | `p11b:laplace-red` | PASS | Explicit alpha^k(1-alpha²)^(2j) envelope; positive interval excludes poles. |
| `average_action_polynomial` L802 | `p11b:lie` | PASS | Analytic coefficients and all three action monomials of the quartic average. |
| `asymptotics_general_axes` L809 | `p11b:asymptotics` | PASS | Correct a1³/a2⁷ determinant scale and mass-ratio-only relative error. |

## Definitions and structures

These verdicts concern intended meaning on the specified analytic domains and safe use of total extensions. They do not claim analyticity of singular physical formulas outside those domains.

| Lean name and line | Blueprint label | Verdict | Reason |
|---|---|---|---|
| `IsChart` L30 | `p1:chart / p1:lattice-torus / p1:torus-union` | PASS | Exact upstream Part-1 definition excerpt; production must import its owner. |
| `IsLatticeTorus` L33 | `p1:chart / p1:lattice-torus / p1:torus-union` | PASS | Exact upstream Part-1 definition excerpt; production must import its owner. |
| `unitCube` L43 | `p1:chart / p1:lattice-torus / p1:torus-union` | PASS | Exact upstream Part-1 definition excerpt; production must import its owner. |
| `QuantitativeData` L47 | `p11a:weak-kam-quantitative` | PASS | Numerical data only; separate budget and KAM validity guards. |
| `QuantitativeData.NumericalValid` L60 | `p11a:weak-kam-quantitative` | PASS | Numerical data only; separate budget and KAM validity guards. |
| `QuantitativeData.Valid` L67 | `p11a:weak-kam-quantitative` | PASS | Numerical data only; separate budget and KAM validity guards. |
| `p11c_bump` L70 | `p11a:smooth-cutoff` | PASS | Literal normalized polynomial bump and finite derivative-index maxima. |
| `p11c_mollifier` L71 | `p11a:smooth-cutoff` | PASS | Literal normalized polynomial bump and finite derivative-index maxima. |
| `p11c_mollifierMass` L74 | `p11a:smooth-cutoff` | PASS | Literal normalized polynomial bump and finite derivative-index maxima. |
| `p11c_cutoffDerivative` L75 | `p11a:smooth-cutoff` | PASS | Literal normalized polynomial bump and finite derivative-index maxima. |
| `p11c_cutoffConstant` L78 | `p11a:smooth-cutoff` | PASS | Literal normalized polynomial bump and finite derivative-index maxima. |
| `QuantitativeData.diameter` L83 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `QuantitativeData.varpi` L84 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `QuantitativeData.cN` L86 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `QuantitativeData.A0` L88 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `QuantitativeData.cDio` L89 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `QuantitativeData.gamma` L94 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `QuantitativeData.tbar` L98 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `QuantitativeData.tflat` L100 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `QuantitativeData.xibar` L102 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `QuantitativeData.thetaMax` L104 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `QuantitativeData.lambdaFlat` L106 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `thresholds` L111 | `p11a:thresholds` | PASS | Literal explicit numerical formula; max diameter and positive-data guards. |
| `p11c_oldThreshold` L114 | `p11a:budget` | PASS | Old threshold/order adapter; not a replacement iteration. |
| `BudgetOrder` L124 | `p11a:budget` | PASS | Old threshold/order adapter; not a replacement iteration. |
| `BudgetRates` L136 | `p11a:bu-poly` | PASS | Eight independent nonnegative rates; exact source exponent/bounds. |
| `BudgetRates.Valid` L146 | `p11a:bu-poly` | PASS | Eight independent nonnegative rates; exact source exponent/bounds. |
| `BudgetRates.exponent` L149 | `p11a:bu-poly` | PASS | Eight independent nonnegative rates; exact source exponent/bounds. |
| `RateBounds` L158 | `p11a:bu-poly` | PASS | Eight independent nonnegative rates; exact source exponent/bounds. |
| `p11c_G0` L172 | `p11a:bu-beta` | PASS | Explicit G0 and B0, no Hamiltonian dependence. |
| `p11c_B0` L173 | `p11a:bu-beta` | PASS | Explicit G0 and B0, no Hamiltonian dependence. |
| `p11c_scalar` L190 | `p11a:weak-kam-quantitative` | PASS | Source input, frozen-domain adapter, or output-only KAM family; no conclusion assumed. |
| `p11c_realDomain` L193 | `p11a:weak-kam-quantitative` | PASS | Source input, frozen-domain adapter, or output-only KAM family; no conclusion assumed. |
| `QuantitativeInput` L196 | `p11a:weak-kam-quantitative` | PASS | Source input, frozen-domain adapter, or output-only KAM family; no conclusion assumed. |
| `p11c_displacement` L216 | `p11a:weak-kam-quantitative` | PASS | Source input, frozen-domain adapter, or output-only KAM family; no conclusion assumed. |
| `QuantitativeFamily` L219 | `p11a:weak-kam-quantitative` | PASS | Source input, frozen-domain adapter, or output-only KAM family; no conclusion assumed. |
| `p11c_zeroGood` L240 | `p11a:zero-case` | PASS | Explicit subset of K with the stronger 2-gamma divisors. |
| `PlanarData` L288 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `PlanarData.Valid` L293 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `PlanarData.kappa` L294 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `p11c_axes` L295 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `PlanarData.actions` L296 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `PlanarData.axes` L297 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `p11c_hatFix` L299 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `p11c_hatMov` L300 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `p11c_secular` L302 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `p11c_slowLength` L305 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `p11c_pairDot` L306 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `p11c_quartic` L307 | `p11b:sec-set#data` | PASS | Physical data or coordinate/polynomial adapter; frozen objects used directly. |
| `p11c_orbit` L314 | `p11b:orbit` | PASS | Actual Kepler orbit, finite displayed jet, or genuine equality of derivatives. |
| `p11c_orbitJet` L320 | `p11b:orbit` | PASS | Actual Kepler orbit, finite displayed jet, or genuine equality of derivatives. |
| `p11c_JetEq` L330 | `p11b:orbit` | PASS | Actual Kepler orbit, finite displayed jet, or genuine equality of derivatives. |
| `p11c_laplace` L338 | `p11b:laplace-red` | PASS | Normalized radian Laplace integral. |
| `p11c_pairCoeffs` L350 | `p11b:pair-jet` | PASS | Displayed rational coefficients, actual pair integral and finite invariant jet. |
| `p11c_pairAverage` L363 | `p11b:pair-jet` | PASS | Displayed rational coefficients, actual pair integral and finite invariant jet. |
| `p11c_pairJet` L367 | `p11b:pair-jet` | PASS | Displayed rational coefficients, actual pair integral and finite invariant jet. |
| `p11c_coeffs` L374 | `p11b:quartic-explicit` | PASS | Physical coefficient formula or factorial-normalized homogeneous derivative. |
| `p11c_homogeneousPart` L383 | `p11b:quartic-explicit` | PASS | Physical coefficient formula or factorial-normalized homogeneous derivative. |
| `p11c_monomial` L393 | `p11b:char` | PASS | Finite quartic coefficients and genuine rotations/character integrals; no new norm instance. |
| `QuarticFamily` L396 | `p11b:char` | PASS | Finite quartic coefficients and genuine rotations/character integrals; no new norm instance. |
| `QuarticFamily.eval` L400 | `p11b:char` | PASS | Finite quartic coefficients and genuine rotations/character integrals; no new norm instance. |
| `p11c_rotation` L404 | `p11b:char` | PASS | Finite quartic coefficients and genuine rotations/character integrals; no new norm instance. |
| `p11c_character` L407 | `p11b:char` | PASS | Finite quartic coefficients and genuine rotations/character integrals; no new norm instance. |
| `p11c_average` L410 | `p11b:char` | PASS | Finite quartic coefficients and genuine rotations/character integrals; no new norm instance. |
| `p11c_NR4` L413 | `p11b:char` | PASS | Finite quartic coefficients and genuine rotations/character integrals; no new norm instance. |
| `p11c_n0` L416 | `p11b:char` | PASS | Finite quartic coefficients and genuine rotations/character integrals; no new norm instance. |
| `p11c_bracket` L419 | `p11b:char` | PASS | Finite quartic coefficients and genuine rotations/character integrals; no new norm instance. |
| `p11c_chi` L429 | `p11b:homological` | PASS | Finite-support character sum with guarded nonzero divisors on O. |
| `p11c_flow` L452 | `p11b:flow` | PASS | Choice of an actual solution; fallback is not used in flow conclusions. |
| `p11c_liftFlow` L489 | `p11b:lift-map` | PASS | Frozen assembled coordinates and partial-action derivative with trajectory held fixed. |
| `p11c_tube` L498 | `p11b:lift-map` | PASS | Frozen assembled coordinates and partial-action derivative with trajectory held fixed. |
| `p11c_Q` L511 | `p11b:sec-beta#data` | PASS | Explicit physical Q, sorted eigenvalues and spectral projector. |
| `p11c_sigma` L518 | `p11b:sec-beta#data` | PASS | Explicit physical Q, sorted eigenvalues and spectral projector. |
| `p11c_projector` L523 | `p11b:sec-beta#data` | PASS | Explicit physical Q, sorted eigenvalues and spectral projector. |
| `beta_def` L526 | `p11b:beta-def / p11b:beta-formula` | PASS | Explicit projector-only torsion formula or concrete linear rotation. |
| `p11c_beta` L533 | `p11b:beta-def / p11b:beta-formula` | PASS | Explicit projector-only torsion formula or concrete linear rotation. |
| `p11c_rotateSlow` L536 | `p11b:beta-def / p11b:beta-formula` | PASS | Explicit projector-only torsion formula or concrete linear rotation. |
| `p11c_frame` L563 | `p11b:birkhoff-form / p11b:lift-map` | PASS | Global eigenvector normalization and the full inverse-rotation lift. |
| `p11c_rotationLift` L576 | `p11b:birkhoff-form / p11b:lift-map` | PASS | Global eigenvector normalization and the full inverse-rotation lift. |
| `p11c_phi4` L587 | `p9:good` | PASS | Finite all-mode NR4 product; only its nonzero-locus identification is required. |
| `PlanarBirkhoffResult` L594 | `p11b:birkhoff-form` | PASS | Output-only actual F, chi, same T, physical domain and exact frozen predicate. |
| `p11c_relativeError` L635 | `p11b:asymptotics` | PASS | Relative-error Big-O along positive alpha tending to zero. |
| `p11c_pairSeriesJet` L697 | `p11b:pair-jet` | PASS | Finite exact list of displayed series coefficients. |
| `p11c_combinedFrequency` L762 | `p11b:patch / p10:interface` | PASS | Frozen-action combined frequency and output-only same-patch certificate. |
| `PlanarFrequencyPatch` L767 | `p11b:patch / p10:interface` | PASS | Frozen-action combined frequency and output-only same-patch certificate. |

## Consumers, frozen objects and dropped premises

**Consumer verdict: PASS at the design/interface level.** Direct uses checked in P Part 11 (`kam-input`, wrapper and beta-power/displacement use), Part 12 (`d-patch`, `d-bnf`, chart and P-G assembly), and Part 13 (`fixed-ham`, `d-bnf`, wrapper and physical transport). The requested cross-track N Part-3 search in I/P and N Parts 7/11/12 concerns the common real ODE interface: this design consumes that interface; it does not redefine or weaken its consumers. There is no new export intended to replace an I/N theorem. Remaining upstream interface reconciliations are explicitly gated in design section 3; approval here does not certify undelivered upstream proofs.

- The KAM parameter/carrier is `Fin N → ℝ`, its phase is the product in (angle,action) order, and the periodic lattice is period one. The product swap mentioned in U1 is an isometry; it loses no dimension or measure factor. Lower and upper Lipschitz bounds, positive cell measure and compact representatives give disjoint embedded compact quotient tori; an additional quotient-manifold definition is unnecessary.
- `QuantitativeInput` uses frozen `frequencyMap`, max-to-max complex Hessian operator norm, Euclidean diagonal lower/M0 bounds and independent Euclidean input directions for the M bound. Holomorphy on the open neighborhood supplies the omitted explicit C-infinity clause. Pointwise bounds are equivalent to the source suprema on the compact derivative domains. Attainment of the unit-direction maximum uses continuity and a nonempty compact sphere, with N>=1 already guarded.
- K5 is supplied by `budget` plus `qb_poly`, and K6 by `displacement_power_flat`, rather than being copied as assumptions into the family. Their quantifier order is sufficient for the Part-11 beta-varying family. `cDelta` is chosen before rho,K,beta,M,M0,thickness,h,f; the finite rho choices do not force wider dependence. The zero branch uses the literal unperturbed family, with displacement zero for every cDelta.
- P12/P13 receive the same full T for `p11c_hatFix` and `p11c_hatMov`. The formula, action preservation, angle-translation covariance and upstream physical periodicity give the Hamiltonian split and hperiod. Those elementary consumer deductions do not require a new physical premise. The P0 value is the actual zero-slow secular average; U8's identification supplies the source C0 / C0+delta names.
- `patch` retains the positive-volume frozen-action patch, analytic combined R-nondegenerate frequency, uniform NR4 and positive finite type for every mu>=mu0, as well as Birkhoff and torsion data. The geometric-only helper is not substituted for it. Part-10 stability applies with the positive finite-type amount; no stability assumption is smuggled in.

**Frozen-object verdict: PASS.** Read the actual definitions of `Phase`, `assemble`, `oscillatorAction`, `secularAverage`, `HasSecularBirkhoffForm`, `frequencyMap`, `realHamiltonian`, `actionNbhd`, and `hamiltonianVectorField`, together with `IsDiophantine` and the actual real `IsSolutionIn` interface. The design uses these objects directly. Poincare/fFix/fMov are the delivered physical functions. The standalone IsChart/IsLatticeTorus/unitCube bodies match the Part-1 signatures, rather than inventing a parallel frozen object. The physical Newton/IsSolutionOn predicates are downstream transport work; no claim here identifies them by assumption with a replacement predicate.

The frozen Birkhoff bridge is valid with the stated non-strict radius condition: open oscillator discs imply slowLength²<2 r0²<=r². For the remainder, slowLength<=2 times the max norm yields the factor 64, and delta²<=eps/(64C) gives the exact frozen fourth-power bound, including zero. Integrability is an explicit helper premise and an output obligation for the actual pullback. P12 should retain its stricter r0=r/2 for the closed-cylinder margin.

**Definition verdict: PASS.** Input structures contain typing, numerical or source analytic data. Conclusion-shaped fields occur only in the returned `QuantitativeFamily`, `PlanarBirkhoffResult` and `PlanarFrequencyPatch`; none replaces a main theorem hypothesis. QuarticFamily is an actual finite degree-four polynomial, although its coefficient accessor has an infinite carrier. The unused coefficients can be zero. The character and chi sums have finite support. The flow's fallback is harmless only because `flow` proves existence/specification on its used neighborhood; no conclusion relies on that fallback. Off-domain physical functions need no analyticity claim. No global instance on bare functions or matrices is introduced.

Dropped premises checked independently: simply-connectedness is unnecessary after the explicit global nonzero eigenvector `(-Q12,Q11-sigma1)` is normalized (Q12>0 throughout the cone); its positive quarter-turn gives the second oriented column. Analyticity of the slow-independent C in `lie` is unnecessary because it cancels identically from the estimate. Neither drop weakens the physical Birkhoff target.

## Packages and source gaps

**Package verdict: PASS WITH NOTES (N2).** All 32 packages are bounded at 150–750 estimated lines, summing to 16,400. There is no quantitative/planar branch cycle or provider dependency. Correct the omitted helper edges before issuing the relevant briefs. The estimates are planning estimates; R2/R3 analytic flow and T5 exact averaged jet extraction may require further file splits, under the existing 1,500-line cap and default heartbeats.

The four scoped SOURCE_GAP responses were checked against the global review and the actual real/complex interfaces: local/maximal existence before continuation; a new real Lie-Taylor bridge; a real full variational/symplectic flow bridge including the angle component; and an explicit global eigenframe replacing the unpaid angle lift. These are named future proof obligations, not already closed gaps. No complex N theorem is applied without its SmallField/gauge/holomorphy inputs. Multivariable analytic zero-set nullity remains an explicit U9/U10 obligation; empty interior alone would not justify `torsion`'s null-set conclusions.

No new pinned-paper erratum was found or asserted. The existing CP11 B.6 candidate and the stale Part-11 minorant citation remain reported in design section 6. Primary PDFs were not re-audited; this review checks the supplied blueprints, graph contracts, frozen definitions and Lean design. No claim of source-completeness of the older direct Rus01/Rus05 route is made.

## Verification and limits

- `git diff inp...HEAD`: only the design file, 1,132 inserted lines; no implementation change.
- Appendix extraction, source hashes and the 83-node inventory: PASS as recorded above.
- Gated command `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p11c .drafts/scratch/P11CAudit1.lean`: **exit 0; exactly 44 declaration-uses-sorry warnings, no errors or other warnings**. This ran once against the byte-identical copy, using `LEAN_NUM_THREADS=1`, `nice -n 5`, default heartbeats and the integration build snapshot. No simultaneous Lean job was launched by this auditor.
- Mathlib/upstream-name probe `.lake/abi-scratch/P11CAuditNames.lean`, through the same gate: **exit 0, no warnings/errors**. All eight MK names checked: `Matrix.det_fin_two`, `AnalyticOnNhd`, `iteratedFDeriv`, `MvPolynomial.eval`, `MvPolynomial.totalDegree`, `intervalIntegral.integral_deriv_eq_sub`, `HasFDerivAt.comp_hasDerivAt`, `IsCompact.exists_isMinOn`. Also checked the four real ODE names and four analytic-limit/restriction/parametric-integral names in U3/U5. The printed types retain the required openness, differentiability, integrability, derivative convergence, reality and compactness premises; the design names those proof obligations explicitly.
- `P11C_BASE_PATH="$PATH" PATH="$PWD/.drafts/scratch/gated-bin:$PATH" LEAN_NUM_THREADS=1 nice -n 5 scripts/lint_sources.sh`: **exit 0**. Output: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. The pre-existing designer shim routes the ABI subprocess through the same gate; no library build was run.
- Final input rehash: unchanged design, original signatures and graph. Both auditor scratch files deleted. Report validation: 129 declaration rows; numbered N1/N2 with severity and proposed fixes; no control characters or trailing whitespace. `git diff --check` and `git diff --no-index --check /dev/null <report>` passed. Final git status contains only this new report; no tracked-file changes.

The designer's `#print axioms` receipt for `weak_kam_quantitative`, `birkhoff_form`, `patch` is `[propext, sorryAx, Classical.choice, Quot.sound]` for each. That query receipt was read, not independently rerun; the fresh 44 sorry warnings independently confirm that no theorem proof has been supplied. This report does not approve any frozen theorem seal or root closure.
