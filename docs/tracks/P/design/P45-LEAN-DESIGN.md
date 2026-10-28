# Lean design for P-G measure and assembly (blueprint-P Parts 4–5)

Design Revision 3, 2026-10-28. Branch `inp-design-p45`, base `081967912d5200ad4711d6d16abde6a8cfafea71`.
Planning evidence only: signatures with `sorry` certify types, not mathematical proofs or frozen closure.
The provider target is exactly `KAM.Planetary.properlyDegenerateKAM`, still `DRAFT_SORRY`.

The deliverable is this document plus `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`.
Appendix A is the complete, byte-identical signatures file. The scratch copy and all elaboration logs
stay under this worktree's `.drafts/scratch/`. Only this design document is committed.

## 1. Decisions

1. Keep the frozen predicates, Hamiltonian, oscillator actions, phase ordering and theorem telescope.
   `PGData` bundles precisely the frozen inputs, including `hVc`, the boundary collar, the joint analytic
   family, torsion and symmetry. It contains neither a prepared complex Hamiltonian nor a KAM conclusion.
   `main` repeats the frozen type literally with only its declaration name changed.
2. Distinguish source data from produced witnesses. `PGExtension`, `PGAnalytic`, `PGAveraging` and
   `PGFamily` are outputs of named existence lemmas. The chosen objects are definitions using those
   lemmas. Neither the provider nor `main` accepts their specifications as hypotheses.
3. Use direct resonance slicing for the actual frequency `(omega0+mu*G, mu*Theta)`.
   CP10's covering-number uniformity and the rescaled-map resonance argument are not inputs.
   The three cases are slow, fast-dominant and slow-dominant large lattice modes. Preserve the factor
   `mu^(tau-n)/lambda`, the real normal and offset, and `tau>n`.
4. Choose analytic bounds, then `C1`, then `k0,k1,G`, before either small parameter. Set
   `tau=n+1`, `c=2n+4`; `K0` is data-only. `params` contains the literal radius, shell and scale formulas.
   The loss constant is the exact printed sum `(A+Cdio*Cgamma)/volume(V)+6*b*k1+cn*Cb`. The final radius is a further data-only shrinking of the preliminary analytic radius, after the
   measure-loss constant is available. This breaks a bookkeeping cycle without changing quantifiers.
5. The measured torus representative is `outputRepresentative`, an intersection with the **output**
   angle cell. It is not the image of the input parameter cell. `cell_transfer` proves equality of
   cell measures by lattice saturation, disjoint translates and Liouville, not by cell preservation.
6. Strict upper measure is proved by deleting a small positive-measure subfamily of whole tori.
   The deletion is an action-coordinate half-space; null coordinate slices give a continuous cumulative
   finite measure. The surviving family stays sigma compact and contains every torus through its points.
7. Reuse N's actual `KAM.Weighted.{InClass,WBound}` and `KAM.Measure` lattice/Lipschitz infrastructure.
   Use P1's exact chart, period and torus interfaces. The P2/P3 writers own their full interfaces:
   Section 5 and Appendix A use the delivered exact records and typed upstream applications.
8. The global graph review's twelve SOURCE_GAPs in this scope are explicit proof obligations in Section 6.
   No source-gap note is discharged merely by including a `sorry` signature or by finding a library name.

## 2. Carriers, standing objects and conventions

| Object | Carrier / declaration | Convention |
|---|---|---|
| physical/cylindrical phase | frozen `Phase (a+b)` | positions `(phi,q)` before momenta `(I,p)` |
| actions/frequencies | `Fin (a+b) → ℝ` or `ℂ` | first `a` fast, last `b` slow |
| block projections | frozen `fast`, `slow` on real vectors; `blockFast`, `blockSlow` on complex/integer vectors | scalar-generic extensions, with explicit `blockFast_real`, `blockSlow_real` bridge obligations |
| complex phase | `PGComplexPhase n` | abbreviation for existing product carrier; no norm instances |
| source data | `PGData a b` | all frozen binders, no extra assumption |
| compact core | `innerCore V t` | `I∈V` and distance to every frontier point at least `t`; avoids empty-set `infDist` artifacts |
| neighbourhood | `realNbhd X s`, frozen `KAM.actionNbhd X s` | witness form; real version identified with thickening in the geometry package |
| two-scale set | P1 `twoScaleDiophantine a b` | exact existing definition; `resonanceBad_eq` is its complement bridge |
| S4 | `MeasureData a b` | compact positive-volume core, original frequency coefficients, N1–N3, frozen inverse and its bounds |
| holomorphic extension | `PGExtension d`, selected by `pgExtension d` | thin complex tube, selected before the oscillator radius |
| Birkhoff coefficients | `jetP0`, `jetOmega`, `jetBeta` | derivatives of `complexAverage`; original frozen functions only on `V` |
| remainder | `pgRemainder` | average minus the constructed degree-four polynomial |
| analytic constants | `PGAnalytic`, `PGAnalyticSpec` | produced by `freq_data`; inverse bounds and norms are conclusions |
| geometric preparation | `PGParameters`, `params` | numbers are explicit; no hidden dependence on a torus family |
| action domain | `pgActionDomain = checkedCore × actionShell` via `joinedActions` | flattened `Fin (a+b)` carrier; not a new product space |
| tori | `PGFamily.raw`, `physicalTorus`, frozen `IsCylinderTorus` | family indexed by original actions `J0`, frequency is `freq J0/(2*pi)` |
| measured union | `kset`, `rawUnion`, `outputRepresentative` | unions are of whole ranges; output angle cutoff only for measurement |
| measures | Lebesgue `volume`, `ENNReal.ofReal` | positivity/finite-volume gates precede every `toReal` and every division |

`a,b>0` are source assumptions, not local typeclass instances. The fast domain is nonempty because
`IsConnected V` includes nonemptiness. Positive finite `volume V` follows from openness, boundedness
and `a>0`; it is proved, never requested from the provider. S4's core is compact and contained in a
bounded set, so its positive volume is also finite. `MeasureData` is local standing source data for
Part 4, **not** a replacement input to the frozen theorem.

The generic block functions are necessary because the frozen projections accept only real vectors.
Their real bridges must be used when applying frozen predicates. `joinedActions` is the same set as
`Fin.append '' (X ×ˢ Y)`; the coordinate linear equivalence is measure preserving. No global Pi or
matrix norm instance is installed.

Angles in physical charts have period `2*pi`. P3's angles have period one; physical time is preserved
by using `H3(theta,J) = Htilde(2*pi*theta,J)/(2*pi)`. The final frozen frequency is the **period-one**
frequency `w=omegaCP/(2*pi)`, with no second division. Thresholds satisfy `alpha_i=2*pi*gamma_i`.
P1's `cyl_pipeline` already performs the conformal Hamiltonian and angle scaling; its input is the
unscaled period-one torus, in angle/action order.

The coefficient radius of a CP strip is its radian geometric width. N's `WBound` uses geometric
period-one widths and weight `exp(2*pi*s*|k|_1)`. Thus `sigma_tot=pgWidth/12` corresponds to
`WBound` width `pgWidth/(24*pi)`. `kam_hyp` records that conversion explicitly. Sums use the l1
mode size; ambient coordinate norms are max norms. Each oscillator disc is `xi_j < r^2/2`.

## 3. Node-to-declaration table

The worktree does not contain `docs/graph/P/DEPGRAPH.md`. This table reads the authoritative current
`/root/code/KAM-inp/docs/graph/P/DEPGRAPH.md` without changing it. Node IDs are stable under the global
review. All 124 records whose `STATEMENT_SOURCE` is in the two assigned source files are listed below,
including proof steps and data/constant subnodes. The blueprint texts used for locators are the local
`blueprint-P/parts/p4-pg-measure.tex` and `p5-pg-assembly.tex`.

`p4:Lx–y` means `blueprint-P/parts/p4-pg-measure.tex:Lx–y`, and similarly for p5. The full stable label
is the node ID in the first column. A proof-step row names the containing declaration and its proof
obligation; it does not invent an exported lemma for a contradiction step. External nodes map to
library inputs or an explicitly new supplying lemma. This is a design ownership table, not a claim
that all 124 nodes already have proved declarations.

| Graph node | Declaration / local proof owner | Module | Statement; proof | Contract / exact input |
|---|---|---|---|---|
| `bpP:p4:ext-tonelli` | `ext_tonelli` | `PGMeasure/Tonelli` | p4:L11; — | Tonelli after coordinate permutation |
| `bpP:p4:ext-deriv` | `ext_deriv` | `PGMeasure/CompactLipschitz` | p4:L13; — | analytic derivative and local C1 regularity |
| `bpP:p4:ext-conn` | `ext_conn` | `PGMeasure/Collar` | p4:L14; — | frontier crossing for a connected segment |
| `bpP:p4:collar` | `collar` | `PGMeasure/Collar` | p4:L22–29; p4:L30–37 | compact core for every t>0; exact difference; conditional loss; enlargement |
| `stepP:p4:co-compact` | `local to collar` | `PGMeasure/Collar` | p4:L31–32; p4:L31–32 | compact core for every t>0; exact difference; conditional loss; enlargement |
| `stepP:p4:co-meas` | `local to collar` | `PGMeasure/Collar` | p4:L33–34; p4:L33–34 | compact core for every t>0; exact difference; conditional loss; enlargement |
| `stepP:p4:co-nbhd` | `local to collar` | `PGMeasure/Collar` | p4:L35–36; p4:L35–36 | compact core for every t>0; exact difference; conditional loss; enlargement |
| `bpP:p4:lip-compact` | `lip_compact` | `PGMeasure/CompactLipschitz` | p4:L41–43; p4:L44–49 | partial-C1 compact-pair estimate |
| `stepP:p4:lc-contra` | `local to lip_compact` | `PGMeasure/CompactLipschitz` | p4:L45–46; p4:L45–46 | partial-C1 compact-pair estimate |
| `stepP:p4:lc-local` | `local to lip_compact` | `PGMeasure/CompactLipschitz` | p4:L47–48; p4:L47–48 | partial-C1 compact-pair estimate |
| `bpP:p4:lip-inverse` | `lip_inverse` | `PGMeasure/CompactLipschitz` | p4:L51–54; p4:L55–60 | frozen inverse, image bounds, compact Lipschitz |
| `stepP:p4:li-cont` | `local to lip_inverse` | `PGMeasure/CompactLipschitz` | p4:L56–57; p4:L56–57 | frozen inverse, image bounds, compact Lipschitz |
| `stepP:p4:li-lip` | `local to lip_inverse` | `PGMeasure/CompactLipschitz` | p4:L58–59; p4:L58–59 | frozen inverse, image bounds, compact Lipschitz |
| `bpP:p4:freq` | `secularPolynomial; slowFrequency; freq; resonanceBad_eq` | `PGMeasure/Setting` | p4:L72–76; — | actual CP frequency; exact P1 complement bridge |
| `bpP:p4:data` | `MeasureData` | `PGMeasure/Setting` | p4:L78–86; — | literal S4 standing hypotheses |
| `bpP:p4:affine-slab` | `affine_slab` | `PGMeasure/AffineSlab` | p4:L88–90; p4:L91–93 | real normal and offset |
| `bpP:p4:lattice-tail` | `lattice_tail` | `PGMeasure/LatticeTail` | p4:L95–98; p4:L99–102 | full sum and real-cutoff tail |
| `stepP:p4:lt-a` | `local to lattice_tail` | `PGMeasure/LatticeTail` | p4:L100; p4:L100 | full sum and real-cutoff tail |
| `stepP:p4:lt-b` | `local to lattice_tail` | `PGMeasure/LatticeTail` | p4:L101; p4:L101 | full sum and real-cutoff tail |
| `bpP:p4:two-scale-diophantine-measure` | `two_scale_diophantine_measure` | `PGMeasure/TwoScale` | p4:L104–112; p4:L113–141 | three resonance cases; explicit measure_c1, measure_c2 |
| `stepP:p4:dm-slow` | `local to two_scale_diophantine_measure` | `PGMeasure/TwoScale` | p4:L118–119; p4:L118–119 | three resonance cases; explicit measure_c1, measure_c2 |
| `stepP:p4:dm-y` | `local to two_scale_diophantine_measure` | `PGMeasure/TwoScale` | p4:L121–123; p4:L121–123 | three resonance cases; explicit measure_c1, measure_c2 |
| `stepP:p4:dm-A` | `local to two_scale_diophantine_measure` | `PGMeasure/TwoScale` | p4:L125–128; p4:L125–128 | three resonance cases; explicit measure_c1, measure_c2 |
| `stepP:p4:dm-Bstruct` | `local to two_scale_diophantine_measure` | `PGMeasure/TwoScale` | p4:L130–131; p4:L130–131 | three resonance cases; explicit measure_c1, measure_c2 |
| `stepP:p4:dm-B` | `local to two_scale_diophantine_measure` | `PGMeasure/TwoScale` | p4:L133–138; p4:L133–138 | three resonance cases; explicit measure_c1, measure_c2 |
| `stepP:p4:dm-sum` | `local to two_scale_diophantine_measure` | `PGMeasure/TwoScale` | p4:L139–140; p4:L139–140 | three resonance cases; explicit measure_c1, measure_c2 |
| `stepP:p4:dc-prod` | `local to realNbhd_joinedActions; domain_collar_helper` | `PGMeasure/Collar` | p4:L161–162; p4:L161–162 | product neighbourhood in max norm; unnormalised loss |
| `bpP:p4:disc-measure` | `disc_measure; disc_measure_chart; disc_measure_image; disc_measure_shell` | `PGMeasure/Polar` | p4:L173–178; p4:L179–186 | chart, Jacobian, volume, null centres, shell |
| `stepP:p4:dm-jac` | `local to disc_measure; disc_measure_chart; disc_measure_image; disc_measure_shell` | `PGMeasure/Polar` | p4:L180–181; p4:L180–181 | chart, Jacobian, volume, null centres, shell |
| `stepP:p4:dm-cell` | `local to disc_measure; disc_measure_chart; disc_measure_image; disc_measure_shell` | `PGMeasure/Polar` | p4:L182–183; p4:L182–183 | chart, Jacobian, volume, null centres, shell |
| `stepP:p4:dm-shell` | `local to disc_measure; disc_measure_chart; disc_measure_image; disc_measure_shell` | `PGMeasure/Polar` | p4:L184–185; p4:L184–185 | chart, Jacobian, volume, null centres, shell |
| `bpP:p4:conv#data` | `PGData; innerCore; realNbhd` | `PG/Setting` | p4:L19–20; — | source context and coordinate conventions |
| `bpP:p4:conv#shell` | `actionShell; joinedActions` | `PGMeasure/Setting` | p4:L153–154; — | plain shell and flattened product |
| `bpP:p4:s-disc#chart` | `oscillatorPolar; polarCellMap` | `PGMeasure/Polar` | p4:L169–171; — | general a,b; exact P7 specialization bridge |
| `bpP:p5:order` | `PGData; pgExtension; pgAnalytic; pgScales; pgRstar; finalRadius` | `PGAssembly/Main` | p5:L13–23; p5:L13–23 | dependency order encoded by arguments; no new theorem |
| `bpP:p5:ext` | `ext; PGExtension; pgExtension` | `PGAssembly/Extension` | p5:L29–31; p5:L32–37 | thin periodic complex extension with uniform bounds |
| `stepP:p5:ext-loc` | `local to ext; PGExtension; pgExtension` | `PGAssembly/Extension` | p5:L33; p5:L33 | thin periodic complex extension with uniform bounds |
| `stepP:p5:ext-glue` | `local to ext; PGExtension; pgExtension` | `PGAssembly/Extension` | p5:L34; p5:L34 | thin periodic complex extension with uniform bounds |
| `stepP:p5:ext-per` | `local to ext; PGExtension; pgExtension` | `PGAssembly/Extension` | p5:L35; p5:L35 | thin periodic complex extension with uniform bounds |
| `stepP:p5:ext-H0` | `local to ext; PGExtension; pgExtension` | `PGAssembly/Extension` | p5:L36; p5:L36 | thin periodic complex extension with uniform bounds |
| `bpP:p5:consts` | `pgWidth; pgOscRadius; complexAverage; consts` | `PGAssembly/Extension` | p5:L39–44; p5:L45–47 | complex radius selected after tube; fixed weighted bound |
| `bpP:p5:birkhoff-ext` | `jetP0; jetOmega; jetBeta; jetPolynomial; birkhoff_ext` | `PGAssembly/Jets` | p5:L49–56; p5:L57–62 | on-V identification; holomorphy; joint continuity; complex symmetry; vanishing jet; closure torsion |
| `stepP:p5:be-coef` | `local to jetP0; jetOmega; jetBeta; jetPolynomial; birkhoff_ext; birkhoff_ext_parameter_regularity` | `PGAssembly/Jets` | p5:L58; p5:L58 | on-V identification; holomorphy; joint continuity; complex symmetry; vanishing jet; closure torsion |
| `stepP:p5:be-an` | `local to jetP0; jetOmega; jetBeta; jetPolynomial; birkhoff_ext; birkhoff_ext_parameter_regularity` | `PGAssembly/Jets` | p5:L59; p5:L59 | on-V identification; holomorphy; joint continuity; complex symmetry; vanishing jet; closure torsion |
| `stepP:p5:be-jet` | `local to jetP0; jetOmega; jetBeta; jetPolynomial; birkhoff_ext; birkhoff_ext_parameter_regularity` | `PGAssembly/Jets` | p5:L60; p5:L60 | on-V identification; holomorphy; joint continuity; complex symmetry; vanishing jet; closure torsion |
| `stepP:p5:be-det` | `local to jetP0; jetOmega; jetBeta; jetPolynomial; birkhoff_ext; birkhoff_ext_parameter_regularity` | `PGAssembly/Jets` | p5:L61; p5:L61 | on-V identification; holomorphy; joint continuity; complex symmetry; vanishing jet; closure torsion |
| `bpP:p5:uniform-remainder` | `uniform_remainder` | `PGAssembly/Remainder` | p5:L64–70; p5:L71–74 | uniform fifth-order complex remainder |
| `stepP:p5:ur-bound` | `local to uniform_remainder` | `PGAssembly/Remainder` | p5:L72; p5:L72 | uniform fifth-order complex remainder |
| `stepP:p5:ur-schwarz` | `local to uniform_remainder` | `PGAssembly/Remainder` | p5:L73; p5:L73 | uniform fifth-order complex remainder |
| `bpP:p5:lip-complex` | `lip_complex` | `PGAssembly/FastComplex` | p5:L80–82; p5:L83–86 | close-pair Cauchy; far-pair sup bound |
| `bpP:p5:bilip` | `complexFast; bilip` | `PGAssembly/FastComplex` | p5:L88–90; p5:L91–94 | complex lower Lipschitz and bounded derivative |
| `stepP:p5:bl-real` | `local to complexFast; bilip` | `PGAssembly/FastComplex` | p5:L92; p5:L92 | complex lower Lipschitz and bounded derivative |
| `stepP:p5:bl-comp` | `local to complexFast; bilip` | `PGAssembly/FastComplex` | p5:L93; p5:L93 | complex lower Lipschitz and bounded derivative |
| `bpP:p5:dio-one` | `dio_one` | `PGMeasure/OneScale` | p5:L96–98; p5:L99–102 | single-scale fast exclusion |
| `bpP:p5:freq-data` | `PGAnalyticSpec; freq_data; pgAnalytic` | `PGAssembly/FrequencyBounds` | p5:L104–108; p5:L109–113 | radius-2 polynomial bounds; muStar<=mu0; Lipschitz bounds and complex beta inverse |
| `stepP:p5:fd-bd` | `local to PGAnalyticSpec; freq_data; pgAnalytic` | `PGAssembly/FrequencyBounds` | p5:L110; p5:L110 | radius-2 polynomial bounds; muStar<=mu0; Lipschitz bounds and complex beta inverse |
| `stepP:p5:fd-lip` | `local to PGAnalyticSpec; freq_data; pgAnalytic` | `PGAssembly/FrequencyBounds` | p5:L111; p5:L111 | radius-2 polynomial bounds; muStar<=mu0; Lipschitz bounds and complex beta inverse |
| `stepP:p5:fd-beta` | `local to PGAnalyticSpec; freq_data; pgAnalytic` | `PGAssembly/FrequencyBounds` | p5:L112; p5:L112 | radius-2 polynomial bounds; muStar<=mu0; Lipschitz bounds and complex beta inverse |
| `bpP:p5:freq-inj` | `complexIntegrable; complexFrequency; freq_inj` | `PGAssembly/FrequencyInverse` | p5:L115–125; p5:L126–130 | complex injectivity and row-wise inverse bounds |
| `stepP:p5:fi-inj` | `local to complexIntegrable; complexFrequency; freq_inj` | `PGAssembly/FrequencyInverse` | p5:L127; p5:L127 | complex injectivity and row-wise inverse bounds |
| `stepP:p5:fi-blk` | `local to complexIntegrable; complexFrequency; freq_inj` | `PGAssembly/FrequencyInverse` | p5:L128; p5:L128 | complex injectivity and row-wise inverse bounds |
| `stepP:p5:fi-inv` | `local to complexIntegrable; complexFrequency; freq_inj` | `PGAssembly/FrequencyInverse` | p5:L129; p5:L129 | complex injectivity and row-wise inverse bounds |
| `bpP:p5:params` | `PGParameters; params; checkedCore; pgActionDomain` | `PGAssembly/Parameters` | p5:L137–145; — | all formulas explicit functions of r,mu |
| `bpP:p5:rstar` | `rstar; pgRstar; finalRadius` | `PGAssembly/Threshold` | p5:L147–156; — | preliminary radius, then data-only measure shrink |
| `bpP:p5:param-facts` | `param_facts` | `PGAssembly/Threshold` | p5:L158–163; p5:L164–166 | log powers; gammaBar; positive finite action volume |
| `bpP:p5:avg` | `PGAveraging; AveragingSpec; avg; pgAvg` | `PGAssembly/Averaging` | p5:L170–174; p5:L175–180 | P2 application; Fourier remainder and displacements |
| `stepP:p5:av-dict` | `local to PGAveraging; AveragingSpec; avg; pgAvg` | `PGAssembly/Averaging` | p5:L176; p5:L176 | P2 application; Fourier remainder and displacements |
| `stepP:p5:av-R1` | `local to PGAveraging; AveragingSpec; avg; pgAvg` | `PGAssembly/Averaging` | p5:L177; p5:L177 | P2 application; Fourier remainder and displacements |
| `stepP:p5:av-R2` | `local to PGAveraging; AveragingSpec; avg; pgAvg` | `PGAssembly/Averaging` | p5:L178; p5:L178 | P2 application; Fourier remainder and displacements |
| `stepP:p5:av-id` | `local to PGAveraging; AveragingSpec; avg; pgAvg` | `PGAssembly/Averaging` | p5:L179; p5:L179 | P2 application; Fourier remainder and displacements |
| `bpP:p5:phi` | `phi; phiDomain; oscillatorPolarComplex` | `PGAssembly/Chart` | p5:L184–186; — | compose real averaging with polar chart |
| `bpP:p5:phi-chart` | `phi_chart` | `PGAssembly/Chart` | p5:L188–191; p5:L192–196 | IsChart; Q1; Q2; compose the AveragingSpec identity |
| `stepP:p5:pc-img` | `local to phi_chart` | `PGAssembly/Chart` | p5:L193; p5:L193 | IsChart; Q1; Q2; compose the AveragingSpec identity |
| `stepP:p5:pc-lat` | `local to phi_chart` | `PGAssembly/Chart` | p5:L194; p5:L194 | IsChart; Q1; Q2; compose the AveragingSpec identity |
| `stepP:p5:pc-ham` | `local to phi_chart` | `PGAssembly/Chart` | p5:L195; p5:L195 | IsChart; Q1; Q2; compose the AveragingSpec identity |
| `bpP:p5:kam-hyp` | `kamH; kamF; kam_hyp` | `PGAssembly/KAMInputs` | p5:L198–202; p5:L203–208 | exact N norm, frequency and Hessian inverse obligations |
| `stepP:p5:kh-dom` | `local to kamH; kamF; kam_hyp` | `PGAssembly/KAMInputs` | p5:L204; p5:L204 | exact N norm, frequency and Hessian inverse obligations |
| `stepP:p5:kh-h` | `local to kamH; kamF; kam_hyp` | `PGAssembly/KAMInputs` | p5:L205; p5:L205 | exact N norm, frequency and Hessian inverse obligations |
| `stepP:p5:kh-f` | `local to kamH; kamF; kam_hyp` | `PGAssembly/KAMInputs` | p5:L206; p5:L206 | exact N norm, frequency and Hessian inverse obligations |
| `stepP:p5:kh-norm` | `local to kamH; kamF; kam_hyp` | `PGAssembly/KAMInputs` | p5:L207; p5:L207 | exact N norm, frequency and Hessian inverse obligations |
| `bpP:p5:kam-cond` | `kam_cond; PGScaleSpec; pgScales; params` | `PGAssembly/Scales` | p5:L212–222; p5:L223–226 | choose scales then evaluate rhoHat,Ehat; rstar gives KAM inequality |
| `stepP:p5:kc-eval` | `local to kam_cond; PGScaleSpec; pgScales; params` | `PGAssembly/Scales` | p5:L224; p5:L224 | choose scales then evaluate rhoHat,Ehat; rstar gives KAM inequality |
| `stepP:p5:kc-small` | `local to kam_cond; PGScaleSpec; pgScales; params` | `PGAssembly/Scales` | p5:L225; p5:L225 | choose scales then evaluate rhoHat,Ehat; rstar gives KAM inequality |
| `bpP:p5:rK` | `r_k` | `PGAssembly/Threshold` | p5:L228–231; p5:L232–234 | strict enlargement and shell width bounds |
| `stepP:p5:rk-dir` | `local to r_k` | `PGAssembly/Threshold` | p5:L233; p5:L233 | strict enlargement and shell width bounds |
| `bpP:p5:location` | `location` | `PGAssembly/Chart` | p5:L241–243; p5:L244–248 | action collar and strict oscillator radial margin |
| `stepP:p5:lo-range` | `local to location` | `PGAssembly/Chart` | p5:L245; p5:L245 | action collar and strict oscillator radial margin |
| `stepP:p5:lo-act` | `local to location` | `PGAssembly/Chart` | p5:L246; p5:L246 | action collar and strict oscillator radial margin |
| `stepP:p5:lo-disc` | `local to location` | `PGAssembly/Chart` | p5:L247; p5:L247 | action collar and strict oscillator radial margin |
| `bpP:p5:kset` | `pgD0; physicalTorus; kset; rawUnion` | `PGAssembly/Parameters` (pgD0); `PGAssembly/Family` (consumers) | p5:L250–254; — | early parameter set; unions of entire torus ranges |
| `bpP:p5:torus-conv` | `PGFamilySpec; torus_conv; frequency_bounds` | `PGAssembly/Family` | p5:L256–258; p5:L259–264 | P3 output plus P1 pipeline; retains quantitative family data |
| `stepP:p5:tc-chart` | `local to PGFamilySpec; torus_conv; frequency_bounds` | `PGAssembly/Family` | p5:L260; p5:L260 | P3 output plus P1 pipeline; retains quantitative family data |
| `stepP:p5:tc-LT` | `local to PGFamilySpec; torus_conv; frequency_bounds` | `PGAssembly/Family` | p5:L261; p5:L261 | P3 output plus P1 pipeline; retains quantitative family data |
| `stepP:p5:tc-pipe` | `local to PGFamilySpec; torus_conv; frequency_bounds` | `PGAssembly/Family` | p5:L262; p5:L262 | P3 output plus P1 pipeline; retains quantitative family data |
| `stepP:p5:tc-freq` | `local to PGFamilySpec; torus_conv; frequency_bounds` | `PGAssembly/Family` | p5:L263; p5:L263 | P3 output plus P1 pipeline; retains quantitative family data |
| `bpP:p5:cell-transfer` | `outputRepresentative; cell_transfer` | `PGAssembly/CellTransfer` | p5:L266–268; p5:L269–275 | output-angle representative; whole unions; exact measure factor |
| `stepP:p5:ct-cell` | `local to outputRepresentative; cell_transfer` | `PGAssembly/CellTransfer` | p5:L270; p5:L270 | output-angle representative; whole unions; exact measure factor |
| `stepP:p5:ct-dec` | `local to outputRepresentative; cell_transfer` | `PGAssembly/CellTransfer` | p5:L271; p5:L271 | output-angle representative; whole unions; exact measure factor |
| `stepP:p5:ct-disj` | `local to outputRepresentative; cell_transfer` | `PGAssembly/CellTransfer` | p5:L272; p5:L272 | output-angle representative; whole unions; exact measure factor |
| `stepP:p5:ct-count` | `local to outputRepresentative; cell_transfer` | `PGAssembly/CellTransfer` | p5:L273; p5:L273 | output-angle representative; whole unions; exact measure factor |
| `stepP:p5:ct-liou` | `local to outputRepresentative; cell_transfer` | `PGAssembly/CellTransfer` | p5:L274; p5:L274 | output-angle representative; whole unions; exact measure factor |
| `bpP:p5:budget` | `budget` | `PGAssembly/ActionBudget` | p5:L280–283; p5:L284–288 | P3 (3.1), direct resonance loss, Cantor collar |
| `stepP:p5:bu-read` | `local to budget` | `PGAssembly/ActionBudget` | p5:L285; p5:L285 | P3 (3.1), direct resonance loss, Cantor collar |
| `stepP:p5:bu-dio` | `local to budget` | `PGAssembly/ActionBudget` | p5:L286; p5:L286 | P3 (3.1), direct resonance loss, Cantor collar |
| `stepP:p5:bu-collar` | `local to budget` | `PGAssembly/ActionBudget` | p5:L287; p5:L287 | P3 (3.1), direct resonance loss, Cantor collar |
| `bpP:p5:lower` | `lower; pgLoss` | `PGAssembly/Lower` | p5:L290–293; p5:L294–298 | bad actions, two shell ends, lost tori |
| `stepP:p5:lo-setup` | `local to lower; pgLoss` | `PGAssembly/Lower` | p5:L295; p5:L295 | bad actions, two shell ends, lost tori |
| `stepP:p5:lo-bad` | `local to lower; pgLoss` | `PGAssembly/Lower` | p5:L296; p5:L296 | bad actions, two shell ends, lost tori |
| `stepP:p5:lo-lost` | `local to lower; pgLoss` | `PGAssembly/Lower` | p5:L297; p5:L297 | bad actions, two shell ends, lost tori |
| `bpP:p5:strictness` | `finite_measure_coordinate_cut; strictness` | `PGAssembly/Strictness` | p5:L302–307; p5:L308–313 | atomless parameter measure; half-space deletion |
| `stepP:p5:st-add` | `local to finite_measure_coordinate_cut; strictness` | `PGAssembly/Strictness` | p5:L309; p5:L309 | atomless parameter measure; half-space deletion |
| `stepP:p5:st-null` | `local to finite_measure_coordinate_cut; strictness` | `PGAssembly/Strictness` | p5:L310; p5:L310 | atomless parameter measure; half-space deletion |
| `stepP:p5:st-ivt` | `local to finite_measure_coordinate_cut; strictness` | `PGAssembly/Strictness` | p5:L311; p5:L311 | atomless parameter measure; half-space deletion |
| `stepP:p5:st-conc` | `local to finite_measure_coordinate_cut; strictness` | `PGAssembly/Strictness` | p5:L312; p5:L312 | atomless parameter measure; half-space deletion |
| `bpP:p5:main` | `main` | `PGAssembly/Main` | p5:L317–320; p5:L321–326 | exact frozen telescope; provider wrapper below anchor |
| `stepP:p5:mn-const` | `local to main` | `PGAssembly/Main` | p5:L322; p5:L322 | exact frozen telescope; provider wrapper below anchor |
| `stepP:p5:mn-given` | `local to main` | `PGAssembly/Main` | p5:L323; p5:L323 | exact frozen telescope; provider wrapper below anchor |
| `stepP:p5:mn-set` | `local to main` | `PGAssembly/Main` | p5:L324; p5:L324 | exact frozen telescope; provider wrapper below anchor |
| `stepP:p5:mn-meas` | `local to main` | `PGAssembly/Main` | p5:L325; p5:L325 | exact frozen telescope; provider wrapper below anchor |
| `bpP:p5:kam-hyp#C1` | `kam_c1` | `PGAssembly/Scales` | p5:L200–201; — | explicit data-only bound |
| `bpP:p5:kam-cond#scales` | `PGScales; PGScaleSpec; kam_cond; log_power_dominated` | `PGAssembly/Scales` | p5:L213–217; — | ordered data-only witnesses |
| `bpP:p5:rstar#Cgamma` | `pgCgamma; param_facts` | `PGAssembly/Threshold` | p5:L152; — | exact formula G*(30/pgWidth)^(tau+1) |
| `bpP:p5:budget#constant` | `pgBudget; pgMeasureUpper1; pgMeasureUpper2; budget` | `PGAssembly/ActionBudget` | p5:L286–287; — | explicit data-only Cb sum before r,mu |
| `bpP:p5:lower#constant` | `pgBudget; pgLoss; lower` | `PGAssembly/Lower` | p5:L291; — | exact Closs sum before finalRadius |

Part 4's graph excludes `beta-inverse`, the relative collar lemma and the standalone Part-4 budgets
from the live root route (the global review explains why). Their useful unnormalised content is still
specified by `beta_inverse` and `domain_collar_helper`; the P5 Cantor budget is the one actually consumed.
`disc_measure_image` and `disc_measure_shell` expose the other clauses of `disc-measure` separately.

## 4. Reuse map and precise proof plans

| Need | Existing declaration | Applicability / new work |
|---|---|---|
| lattice spheres and full sum | `KAM.Measure.lattice_count`, `KAM.Measure.lattice_sum` | instantiate with `(n,tau-1)` and `(b,tau)`; `lattice_tail` adds a real-cutoff integral comparison |
| scalar affine interval | `KAM.Measure.volume_abs_affine_lt_le` | real slope and offset already supported; combine sections to prove `affine_slab` |
| null/Lipschitz images | `KAM.lip_image`, `KAM.lip_image_prod` | preserve domain dimension; use McShane if a theorem requires a global map |
| extension | `KAM.mcshane_components`, `KAM.mcshane_prod` | source-subset Lipschitz maps, max norm; never replace an inverse by an uncontrolled extension |
| holomorphic parameter integration | `KAM.Weighted.holomorphic_parametric_integral` | exact existing finite-dimensional signature; flatten action/oscillator variables into `Fin (a+b+b)` |
| sup-to-weighted | `KAM.Weighted.wbound_of_sup_bound`, `sup_le_wbound`, `InClass`, `WBound` | exact names, positive widths, coefficient/geometric conversion in Section 2 |
| scalar strip coefficients | `KAM.summableWeighted_torusCoeff`, `KAM.Fourier.SummableWeighted`, `weightedNorm` | fast Fourier slices of the complex oscillator Hamiltonian, not a new norm |
| regularity/restriction | `KAM.holomorphic_regularity_of_finiteDimensional`, `KAM.realInclusion`, `realInclusion₂` | joint derivative continuity and restriction to the real slice |
| symplectic form | frozen `KAM.symplecticForm`; `KAM.Kepler.IsSymplecticOn` | use existing form, including its sign; P1 `IsChart` is its analytic wrapper |
| P1 chart transport | `IsChart.comp`, `hol_chart`, `chart_field`, `cyl_pipeline` | exact P1 draft signatures; no DRAFT_SORRY theorem import |
| measure conversion | `chart_measure_image`, `volume_angleScale_image` | P1 exact names; do not require averaging to preserve a fundamental cell |
| parametrised unions | `torus_union`, `torus_union_measurableSet_of_sigmaCompact`, `torus_union_saturation` | P1 exact names; apply to the *input*-cell image for nullity, output cutoff for measure equality |
| frequency dictionary | `isDiophantine_min_of_mem_twoScale`, `smul_mem_twoScale`, `cp10_isDiophantine` | P1 exact names; frozen single-scale predicate, no independent Diophantine definition |
| polar formula | P7 draft `polarMap`, `polarMap_symplectic`, `analyticOnNhd_polarMap` | existing `a=b` specialization; `oscillatorPolar_eq_polarMap` identifies the general `a,b` chart with it |
| Schur algebra | `Matrix.fromBlocks₁₁Invertible`, `Matrix.invOf_fromBlocks₁₁_eq` | convert nonsingular inverses to the required block identity; row norm bounds remain new |
| growth | `isLittleO_log_rpow_rpow_atTop` | proves data-only scale selection; positivity of the logarithm is a separate gate |
| finite-measure continuity | `MeasureTheory.tendsto_measure_iUnion_atTop`, `tendsto_measure_iInter_atTop`, `intermediate_value_Icc` | coordinate cumulative measure, then IVT on a finite enclosing interval |

**Collar and compact Lipschitz.** Use the universal distance-to-frontier definition, closedness inside
`closure V`, and the connected line segment to a point outside `V` to get the frontier crossing.
The collar bound is monotonicity against the frozen `hboundary` set. For a compact nonconvex domain,
use local derivative bounds for close pairs and the bounded image for separated pairs; do not assume
the compact core is convex. `lip_compact` keeps the printed partial-C1 premises. The joint-C1 variant
is separately named `lip_compact_c1`, not a substitute with stronger hypotheses.

**Resonances.** Set `F_k=k·freq`. For `k_f=0`, apply `affine_slab` with normal `beta^T*k_s`
and offset `k_s·Omega`; N3 supplies the lower norm bound and the factor `mu` cancels against the slow
threshold. For the fast-dominant modes, change only the fast actions to `y=fastFrequency H0 I` and
pull back with `(g(y),xi)`. Two points in the same `y_j` section give a difference lower bound from
N1, even when the core is disconnected. For the remaining modes prove both
`|k|_1>(2*mu*LN*Lg)^-1` and slow-block dominance. Slice along a large coordinate of `beta^T*k_s`,
control the `G` increment by N2, sum over `j`, then use the tail in `lattice_tail`. Borelness comes
from the N1/N2 Lipschitz premises and the frozen inverse; it is not an extra S4 assumption.
The constants `measure_c1`, `measure_c2` retain the displayed formulas. Their core-volume denominator
is uniformly bounded in P5 by `volume core >= volume V/2`.

**Analytic preparation.** Complexify local real power series on a compact real parameter/angle box,
prove a real-slice identity theorem, glue overlaps, and extend periodically. First choose the tube,
then `pgOscRadius=min(r0/2,delta/4)`. The average attaches to the frozen normalized integral through `complexAverage_real`. `complexFrequency_real` identifies the derived complex frequency with the original real frequency on V. `oscillatorPolarComplex_real` fixes the principal-root real restriction.
The degree-four jet follows from the frozen little-o condition and symmetry. In particular the diagonal
coefficient is `D_pj^4/3`, the off-diagonal coefficient is `D_pi^2 D_pj^2`; dropping symmetry would identify
only the symmetric part of beta. Continue the vanishing jet across the connected complex tube, then use
`schwarz_order_five` on complex lines. On the real boundary the constructed coefficients extend by
continuity; the supplied total functions `P0,Omega,beta` remain unconstrained there.

**Complex fast frequency and full inverse.** Differentiate the frozen inverse identities on the open
`W` to obtain a real left inverse, use equal finite dimensions, and complexify the derivative. A
compactness contradiction splits pairs with different and identical limiting real points. Local
linearisation gives the complex lower Lipschitz bound in the latter case. Bounds on the polynomial,
its derivatives and beta follow by Cauchy and Cramer after shrinking the tube uniformly in `mu`.
`freq_inj` uses the fast lower Lipschitz bound and the slow affine formula for injectivity, then Neumann
inversion of the fast block and its Schur complement for the derivative inverse. Track the first inverse
row as O(1) and the second as O(1/mu); a uniform O(1/mu) bound on the whole inverse alone is insufficient.

**Averaging and KAM.** Supply P2 with the normalized perturbation `Ptilde/LP`, small parameter `LP*mu`,
nonresonance on `checkedCore_rhoBar`, and `exp(-Kbar*pgWidth/6)=r^5`. `AveragingSpec` includes both the
Fourier remainder estimate and physical-coordinate displacements. Compose with the general oscillator
polar chart and use the exact P1 chart API. `kam_hyp` supplies the period-one weighted perturbation
reality on the real slice and complex frequency-map conditions; `freq_inj` supplies the inverse block bounds. These and the
arithmetic `kam_cond`, `rstar`, `r_k` supply the exact P3 adapter, not an assumed KAM result.

**Location and budget.** Use the *upper-trimmed* shell `l2top=l2-2*l1`, with width `ell=l2-3*l1`.
For the fast coordinates use `rK+DeltaI<t` and `collar`. For oscillator discs, the polar point has a
strict radial margin and `sqrt(2)*DeltaMax <= k1*r^(3/2)` preserves it. The raw family specification
must retain P3's enlarged-domain loss estimate (3.1), its output-action range and its Lipschitz
parametrisation. Those are needed after existence. The Cantor collar loss is bounded using
`N_s(checkedCore)\checkedCore ⊆ (N_s(innerCore)\innerCore) ∪ (innerCore\checkedCore)`;
Part 4's plain-core normalized budget cannot simply be substituted. Divide only after the positive
core-volume estimates are established. The two cut ends of the shell cost `6*b*k1*sqrt r`.

**Cell transfer and strictness.** Obtain sigma compactness from the Lipschitz input-cell image,
countable lattice saturation and the F-sigma output-angle cell. Apply P1 Liouville to its injective
chart image and count physical fast-angle translates; their intersections partition the physical cell.
Construct a finite Borel measure on original action parameters by the measurable inverse of this
injective representative. Prove coordinate hyperplanes null via the Lipschitz raw parametrisation,
not by projecting a physical torus set. Apply `finite_measure_coordinate_cut`; the cut mass is
`min(total/2, sqrt(r)*volume(cell)/2)`. The complement of the cut is sigma compact, so its union
is Borel, remains a union of whole frozen cylinder tori, and has strict positive and strict upper measure.

## 5. Delivered upstream interfaces and concrete adapters

Appendix A contains verbatim declaration fixtures extracted from the delivered
`/root/code/KAM-inp/.drafts/design/P23Signatures.lean`, including `OscHyp`,
`averaged_remainder`, `ScaleData`, `KamHyp` and the complete joint `two_scale_kam`.
These are elaboration fixtures only: implementation modules import the owners' modules.
The two `#check fun ...` expressions apply the upstream theorems to P45's produced
hypothesis records and check their entire instantiated output types. All new adapter
lemmas have `sorry` bodies, like every other design theorem; this is an interface
receipt, not a proof receipt. No extra frozen premise is introduced.

| Upstream declaration | Exact supplying adapter / dictionary | Consumed output |
|---|---|---|
| P2 `OscHyp` | `pg_osc_hyp`, `pg_osc_bound`, `pg_osc_positive` | exact hypotheses for `averaged_remainder` |
| P2 `averaged_remainder` | first typed application in Appendix A | joint `Psi,g,fs,R`, holomorphy, injectivity, symplecticity, reality, periodicity, remainder and four displacement bounds |
| P2 `oscPack`, `oscFunction`, Weighted `coeff` | `pg_osc_zero` | zero coefficient equals the actual `complexAverage/LP`, at scaled oscillator coordinates |
| P3 `ScaleData`, `KamHyp` | `pgKamScale`, `pg_kam_hyp`, `pg_kam_dictionary` | exact KAM hypothesis record; L, rhoHat, Ehat and dioBase identities |
| P3 `two_scale_kam` | second typed application in Appendix A | one joint witness `(i,Phi,K,I0,KC)`; no separate `limit_actions`/`limit_phi` assumption |
| P1 `cyl_pipeline` | `phi_chart`, `location`, P3 lattice torus, `kamH+kamF` identity | `IsCylinderTorus` with unchanged period-one frequency |
| P1 `chart_measure_image`, `torus_union*` | `cell_transfer`; raw parametrization on original actions × input unit cell | Borel/null images and physical factor `(2*pi)^n`; no cell preservation premise |
| N `holomorphic_parametric_integral`, `wbound_of_sup_bound` | Jets and KAMInputs | analytic averages and weighted bounds |
| P7 `polarMap`, `polarMap_symplectic`, `analyticOnNhd_polarMap` | `oscillatorPolar_eq_polarMap` at a=b | exact existing polar chart; general a,b bridge |

For P2 put `c=2*pi`, `e=pgOscRadius`, `w=pgWidth`, `L=LP`, and
`T(theta,q,I,p)=(c*theta,sqrt(c)*q,I,sqrt(c)*p)` in frozen phase order.
`pgOscNormalize` is T and `pgOscUnnormalize` is its inverse. The proved output
`pg_osc_normalization` includes `T*omega=c*omega`; scaling just the fast angles
would fail this identity. Supply `h=H0/c`, `P'=P∘T/L`, `mu'=L*mu/c`,
`epsilon0=e/sqrt(c)`, `s0=w/c`, `alpha=pgOscAlpha=gammaBar/(2*c*Kbar^tau)`,
`r=rhoBar` and
`K=15/(pi*s0)*log(1/r)=Kbar` to `averaged_remainder`. `pg_osc_zero`
identifies its zero mode with the constructed secular average, not arbitrary frozen
boundary values. `pg_osc_domain` identifies the image of the exact transformed
half-domain with `averagingDomain`. The input-domain image lies in the extension
domain by the collar, positive tube widths and the chosen oscillator radius.

For the returned joint witnesses define the physical map `A.Psi=T∘Psi∘T⁻¹`
and physical remainder `A.remainder=c*(R∘T⁻¹)`. Multiplying the transformed
identity by c gives exactly `AveragingSpec`. The quadratic remainder term becomes
`800*(1+b)*L^2*mu^2*Kbar^tau/(gammaBar*min(rhoBar*w,e^2))`; the exponential
term becomes `L*mu*r^5`. The divisor at a core point is at least
`gammaBar/Kbar^tau`; extension to its rhoBar-neighbourhood loses at most half,
then dividing H0 by c divides its derivative by c. Thus the supplied constant
is exactly `gammaBar/(4*pi*Kbar^tau)`, not a core-only bound.

Write `K=Kbar`, `gamma=gammaBar`, `rho=rhoBar`. Since `rho*w<=e^2` and
`rho=gamma/(2*M0*K^(tau+1))`, the quadratic term is
`1600*(1+b)*M0*L^2*mu^2*K^(2*tau+1)/(gamma^2*w)`.
The first branch `gamma>=G*sqrt(L*mu)*K^(tau+1/2)*r^(-5/2)` bounds it by
`1600*(1+b)*M0*L*mu*r^5/(G^2*w)<=L*mu*r^5`, using the existing
`G^2>=1600*(1+b)*M0/w`. Together with the exponential term this gives
`2*L*mu*r^5`. The transformed `OscHyp.small` reduces to the sufficient bound
`G^2>=2^14*(1+b)*M0*K*r^5`, supplied by the existing G condition and
`K*r^5<=1`. These are proof obligations for P5-AV using P5-TH's radius bounds;
they require no stronger frozen premise or new threshold quantifier.

Physical displacements are at most `6*L*mu*K^tau/(gamma*w)` in fast actions
and `18*L*mu*K^tau/(gamma*e)` in each oscillator block. They imply the unchanged
exported constants `12*L*mu*Kbar^tau/(w*gammaBar)` and
`18*L*mu*Kbar^tau/(e*gammaBar)`.
Conjugation cancels the common conformal factor and yields a 1-chart; real
restriction uses P1 hol_chart. Weighted bounds retain the same fast Fourier modes
and coefficient width w/6 under this conjugation.

For P3 use `D=pgActionDomain`, `sbar=w/15`, `s=w/60`, `rho=lambda1/2`,
`M=C1`, `Mhat=C1*mu`, `Mbar=Mbar2=C1/mu`, `Mbar1=C1`, `E=C1*mu*r^5`.
`pgKamScale.L` is definitionally `initialL`, so the additional `hL` argument
is `Eq.refl`; `pg_kam_dictionary` also proves its value is C1/mu.
`geometricWidth(sbar+s)=w/(24*pi)`. Scalar-generic block projections agree
by unfolding; pointwise equalities of derivative maps in `kam_hyp` become CLM
equalities by extensionality. `pg_kam_dictionary` identifies the exact D0,
rhoHat and Ehat with P45's values, so P3's radius and complement constant match.

Destructure the single `two_scale_kam` output once. Define
`F.raw J theta = K (realFreq (kamH d mu) J) theta` on D0. Its inverse-frequency
clause proves `I0(realFreq h J)=J`; thus the joint factorization is
`F.raw J theta=Phi(theta,i J)`. The i-defect and Phi-defect estimates give the
ordinary Pi/Prod Lipschitz bound after comparison with their positive scaled norms.
P3's modulo-lattice conclusion and complex extension give injectivity and analytic
tori; `location` and P1 `cyl_pipeline` give exactly `physicalTorus` in the cylinder.
The measure output is already on the input unit cell in frozen phase order.
For null slices, swap action/angle factors in the raw Lipschitz parametrization
before applying P1; no assumption on the averaging map preserving a cell is used.
`PGFamilySpec` is the resulting P45 contract, with no separately invented upstream
family predicate. P5-AV and P5-FAM still require proof implementation and independent
review before dispatch; the former missing-interface gate is replaced by these exact
adapter signatures and applications.

The delivered P2 `ob_der` uses the target-width denominator; P3 `rem_norm`
uses the corrected monotonicity and the larger-domain displacement belongs to Psi,
not its restriction. These remain recorded blueprint departures, not frozen premises.

## 6. All source gaps in scope and their supplying work

The graph review reports unregistered classical inputs, rather than permission to assume them.
These twelve records remain graph SOURCE_GAPs until actual proofs and supplying graph edges land.
Source/proof locators below are in `p5-pg-assembly.tex`.

| Gap node and locator | Quoted invocation / issue | Design response and package |
|---|---|---|
| `stepP:p5:ext-loc`, L33 | “a Lebesgue number gives delta1”; real power series made holomorphic, uniformly bounded | new `compact_real_complexification`, implemented by local complexification then compact selection; P5-CL/P5-CG; no real-analytic-to-holomorphic bridge assumed |
| `stepP:p5:ext-glue`, L34 | “identity theorem” on a real open part of a several-variable overlap | new `real_slice_identity`, by coordinatewise identity on a real polydisc followed by analytic continuation; P5-ID |
| `stepP:p5:be-coef`, L58 | analytic averaging and “Taylor polynomial ... equals” from little-o | existing `KAM.Weighted.holomorphic_parametric_integral` plus new `fourth_jet_unique`; P5-JET; fourth-order vanishing, not merely a value identity |
| `stepP:p5:be-an`, L59 | parameter integral, joint continuity, mixed derivatives | existing N parametric integral; compact dominated continuity; `ContDiffAt.iteratedFDeriv_comp_perm` after holomorphic regularity; P5-JET |
| `stepP:p5:be-jet`, L60 | connected tube, real-slice identity | new `connected_complex_tube` plus `real_slice_identity`; P5-ID/P5-JET; uses frozen connected V |
| `stepP:p5:ur-schwarz`, L73 | “maximum principle” for g(t)/t^5 | new `schwarz_order_five`, derived on circles of radius R'<R then R' ↑ R; P5-REM |
| `stepP:p5:bl-real`, L92 | “Dg Domega0=1”, square left inverse invertible | `HasFDerivAt.comp`, finite-dimensional `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`; P5-BL; complexification of the real inverse derivative is explicit |
| `stepP:p5:bl-comp`, L93 | convergent subsequences and local linearisation | finite-dimensional compact closures and `IsCompact.tendsto_subseq`; P5-BL; no compactness of an open complex tube claimed |
| `stepP:p5:fi-blk`, L128 | “Schur complement” | matrix block factorization and Neumann input, `Matrix.fromBlocks₁₁Invertible`; P5-FI |
| `stepP:p5:fi-inv`, L129 | “Block inversion” | new `schur_inverse_blocks`, from `Matrix.invOf_fromBlocks₁₁_eq`; P5-FI; row-sum estimates separate |
| `stepP:p5:st-ivt`, L311 | finite-measure monotone continuity, intermediate value | new `finite_measure_coordinate_cut`; exact Mathlib monotone measure limits plus `intermediate_value_Icc`; P5-CUT |
| `bpP:p5:kam-cond#scales`, L213–217 | “kappa0^2/(log kappa0)^(2tau+2) → infinity” | `isLittleO_log_rpow_rpow_atTop` and `kam_cond`; P5-SCALE; choice of k0 first, k1 second, G third |

## 7. Departures, blueprint issues and suspected errata

| Item | Treatment and reason |
|---|---|
| all constants bundled in records | source premises and output witnesses are separated; projections preserve order, and final theorem has the original telescope |
| complex tube notation | use witness neighbourhood of a real skeleton in the existing max complex norm; shrink by a fixed factor to fit the blueprint's separate real/imaginary bounds; no claim of radius r0/2 in complex oscillators |
| `oscillatorPolar` for arbitrary a,b | extend the existing P7 a=b formula, with a specialization equality; do not duplicate a Poincare chart or change its action domain |
| real/integer/complex blocks | scalar-generic projection extensions with explicit frozen-real bridges, because frozen `fast`/`slow` are real-only |
| two thresholds | preliminary `pgRstar` handles analytic/KAM conditions; `finalRadius` shrinks it after the data-only measure-loss constant; both precede r and mu |
| step nodes | remain local proof obligations inside their result, with exact locators; no exported theorem for an impossible intermediate contradiction assertion |
| source and graph exclusions | standalone plain-core relative budget is not used for the Cantor core; no graph repair or undocumented reassignment is made |

P1 `liouville_lattice` requires target-lattice invariance and is not directly applicable to Phi, whose target shifts only fast angles. Use `chart_measure_image` plus the separate mixed-lattice counting argument. Also, `beta_inverse` drops symmetry: the adjugate bound holds for every invertible matrix, so this is strictly stronger, with no new conclusion-shaped input. P5 helper statements specialize the analytic sublemmas to the full frozen standing context in `PGData`; no extra condition beyond that context is introduced.

**Blueprint issues requiring an explicit proof detail.** P5 L246 uses `rK+DeltaI<t` although the printed
(r5) only explicitly names the oscillator displacement. The radius-selection lemma here includes the
fast-action inequality as an additional *proved numerical consequence* (DeltaI=O(r^(11/2)), not a
hypothesis on P-G. P5 L73's boundary-circle argument is read as R'<R followed by a limit; the maximum
principle does not require an extension to the boundary of the open radius. P5's closure extension is
only for the constructed jet coefficients; it supplies no boundary identities for the arbitrary total
frozen `P0,Omega,beta`. All three points are made literal in the signatures/proof plan.

The radius signature also records every application guard: the S4 upper bound on `R^6` using the
selected frozen inverse Lipschitz constant; `Kbar*r^5<=1`; `rhoBar*pgWidth<=eps_an^2`; and a logarithmic
branch guard `R<exp(-(tau+1))`. The last makes `r^2*log(1/r)^(tau+1)` monotone on the whole interval
of use, so an endpoint bound really implies the required all-smaller-r bound. These are explicit
consequences arranged by the preliminary shrinking, not added frozen assumptions. `PGAnalyticSpec`
includes N2 in the slow actions as well as N1 in the fast actions; a bound on the scalar polynomial
alone is not substituted for either Lipschitz premise.

**Inherited paper allegations, not independently reverified against the pinned PDFs in this design.**
P4's E1: CP10 p563 first line “c_i independent of epsilon and mu” is unsupported by the covering number
p in (58); P4 gives the shrinking-domain resonance counterexample. E2: CP10 p562 (59) treats the
rescaled slow frequency as if it had the same resonances as the actual map, although the mixed slow
term acquires mu. E3: p561 below (55), footnote 25/(57), the asserted boundary-collar estimate for
arbitrary open V requires the explicit frozen collar assumption. E4 (not verified): p561 (56), the
shell loss “C epsilon^(n2/2)” conflicts with the direct O(sqrt epsilon) calculation for n2>=2.
P5 also flags p563 (60)'s uniform O(epsilon^5) inference and CP11's unproved strict upper measure:
this design supplies the jet/compactness/Schwarz and torus-deletion arguments. None is silently treated
as a proved paper theorem. No errata ledger or blueprint is edited.

## 8. Modules, DAG and prover packages

All paths below are `.lean` files under `KAM/Planetary/`; every estimated file has 150–800 lines.
The provider alone is `KAM/Provider/Planetary/ProperlyDegenerateKAM.lean`. Facades, if desired, only
public-import their children and remain below the 1500-line limit. Exact proof packages are below;
repeat the hard rules of Section 11 in each dispatched Lean brief.

| Package | Exact module path | Lines | Wave | Named inputs | Output |
|---|---|---:|---:|---|---|
| P45-S | `KAM/Planetary/PG/Setting.lean` | 300 | 1 | frozen definitions | PGData, block extensions and bridges, source carriers |
| P4-S | `KAM/Planetary/PGMeasure/Setting.lean` | 320 | 2 | P45-S | freq, MeasureData, resonanceBad, joinedActions |
| P4-CO | `KAM/Planetary/PGMeasure/Collar.lean` | 450 | 3 | P45-S,P4-S; hboundary | ext_conn (first), collar, realNbhd_joinedActions, domain_collar_helper |
| P4-LI | `KAM/Planetary/PGMeasure/CompactLipschitz.lean` | 500 | 2 | P45-S; frozen hfreq | ext_deriv, lip_compact, lip_compact_c1, lip_inverse |
| P4-TO | `KAM/Planetary/PGMeasure/Tonelli.lean` | 220 | 1 | Mathlib product measure | ext_tonelli, section_measure_le_of_pairwise_dist |
| P4-AF | `KAM/Planetary/PGMeasure/AffineSlab.lean` | 250 | 2 | P4-TO; KAM.Measure.volume_abs_affine_lt_le | affine_slab |
| P4-LT | `KAM/Planetary/PGMeasure/LatticeTail.lean` | 300 | 1 | KAM.Measure.lattice_count, lattice_sum | lattice_tail, latticeS |
| P5-CL | `KAM/Planetary/PGAssembly/ComplexLocal.lean` | 700 | 1 | real convergent power series, finite-dimensional coordinates | local_real_complexification |
| P5-ID | `KAM/Planetary/PGAssembly/RealSlice.lean` | 700 | 1 | one-variable identity; complex analytic regularity | real_slice_identity, connected_complex_tube |
| P5-CG | `KAM/Planetary/PGAssembly/ComplexGlue.lean` | 650 | 2 | P5-CL, P5-ID; compact cover | compact_real_complexification with uniform radius and bound |
| P5-EX | `KAM/Planetary/PGAssembly/Extension.lean` | 600 | 3 | P45-S, P5-CG; hP,hperiod,hfreq; strip coefficients | ext, PGExtension, consts, pgExtension, complexAverage |
| P4-R0 | `KAM/Planetary/PGMeasure/ResonanceSlow.lean` | 350 | 3 | P4-S,P4-AF,P4-LT; N3 | beta_inverse (first), slow resonance sections and lattice sum |
| P4-RA | `KAM/Planetary/PGMeasure/ResonanceFast.lean` | 550 | 3 | P4-S,P4-LI,P4-TO,P4-LT; N1 | frequency-coordinate pullback and fast sections |
| P4-RB | `KAM/Planetary/PGMeasure/ResonanceLarge.lean` | 650 | 3 | P4-S,P4-TO,P4-LT; N1,N2,N3 | large-mode structure, slow sections, tail |
| P4-M | `KAM/Planetary/PGMeasure/TwoScale.lean` | 250 | 4 | P4-R0,P4-RA,P4-RB; exact P1 predicate | measure_c1, measure_c2, resonanceBad_eq, two_scale_diophantine_measure |
| P4-POL | `KAM/Planetary/PGMeasure/Polar.lean` | 700 | 2 | P45-S; exact P1 IsChart and P7 polarMap; area formula | oscillatorPolar_eq_polarMap, disc_measure_chart, disc_measure_image, disc_measure, disc_measure_shell |
| P4-ONE | `KAM/Planetary/PGMeasure/OneScale.lean` | 250 | 3 | P4-LI,P4-AF,P4-LT; frozen IsDiophantine | dio_one |
| P5-JET | `KAM/Planetary/PGAssembly/Jets.lean` | 750 | 4 | P5-EX,P5-ID; N holomorphic_parametric_integral; hBNF,hsymm | fourth_jet_unique, jetP0/Omega/Beta/Polynomial, birkhoff_ext, birkhoff_ext_parameter_regularity |
| P5-REM | `KAM/Planetary/PGAssembly/Remainder.lean` | 500 | 5 | P5-JET; one-variable maximum principle | schwarz_order_five, uniform_remainder |
| P5-BL | `KAM/Planetary/PGAssembly/FastComplex.lean` | 550 | 4 | P5-EX,P4-LI; HasFDerivAt.comp, compact subsequences | lip_complex, complexFast, bilip |
| P5-FD | `KAM/Planetary/PGAssembly/FrequencyBounds.lean` | 650 | 6 | P5-REM,P5-BL,P4-ONE; Cauchy,Cramer | PGAnalyticSpec, freq_data, pgAnalytic, pgCU |
| P5-FI | `KAM/Planetary/PGAssembly/FrequencyInverse.lean` | 650 | 7 | P5-FD; Matrix.fromBlocks₁₁Invertible; Neumann | schur_inverse_blocks, freq_inj |
| P5-SCALE | `KAM/Planetary/PGAssembly/Scales.lean` | 350 | 7 | P5-FD; isLittleO_log_rpow_rpow_atTop | kam_c1, log_power_dominated, PGScaleSpec, kam_cond, pgScales |
| P5-PAR | `KAM/Planetary/PGAssembly/Parameters.lean` | 300 | 8 | P5-SCALE,P4-CO,P4-S; P1 twoScaleDiophantine | params, checkedCore, pgActionDomain, pgD0, admissible |
| P5-TH | `KAM/Planetary/PGAssembly/Threshold.lean` | 650 | 9 | P5-PAR,P4-ONE,P4-CO,P5-FI | rstar, pgRstar, param_facts, r_k |
| P5-AV | `KAM/Planetary/PGAssembly/Averaging.lean` | 550 | 10 | P5-TH,P5-EX,P5-JET; P2 OscHyp,averaged_remainder; Section 5 adapters | pgOscAlpha, pg_osc_*, avg, PGAveraging, AveragingSpec, pgAvg |
| P5-CH | `KAM/Planetary/PGAssembly/Chart.lean` | 550 | 11 | P5-AV,P4-POL; P1 IsChart.comp,hol_chart | phi_chart, location, phi, phiDomain |
| P5-KH | `KAM/Planetary/PGAssembly/KAMInputs.lean` | 550 | 11 | P5-AV,P5-FI,P5-REM,P5-PAR; N WBound API | kamH, kamF, kam_hyp, pgKamScale, pg_kam_hyp, pg_kam_dictionary |
| P5-FAM | `KAM/Planetary/PGAssembly/Family.lean` | 650 | 12 | P5-CH,P5-KH,P5-TH; P3 KamHyp,two_scale_kam joint output; P1 cyl_pipeline | PGFamilySpec, torus_conv, pgFamily, kset, rawUnion, frequency_bounds |
| P5-CT | `KAM/Planetary/PGAssembly/CellTransfer.lean` | 750 | 13 | P5-FAM; P1 chart_measure_image,volume_angleScale_image,torus_union* | cell_transfer, outputRepresentative |
| P5-BU | `KAM/Planetary/PGAssembly/ActionBudget.lean` | 550 | 13 | P5-FAM,P4-M,P4-CO,P5-TH | pgMeasureUpper1/2, explicit pgBudget, budget on Cantor core, positive denominators |
| P5-LO | `KAM/Planetary/PGAssembly/Lower.lean` | 350 | 14 | P5-CT,P5-BU,P4-POL | lower, pgLoss, finalRadius |
| P5-CUT | `KAM/Planetary/PGAssembly/CutMeasure.lean` | 550 | 2 | finite-measure limits; intermediate_value_Icc | finite_measure_coordinate_cut only (abstract finite measure) |
| P5-ST | `KAM/Planetary/PGAssembly/Strictness.lean` | 500 | 15 | P5-LO,P5-CUT,P5-FAM; P1 null-image bounds | parameter-measure construction, strictness, whole-torus deletion |
| P5-MAIN | `KAM/Planetary/PGAssembly/Main.lean` | 250 | 16 | P5-ST,P5-FAM,P5-CT; frozen Kolmogorov definition | main, literal telescope and ENNReal strict lower slack |
| P5-PROV | `KAM/Provider/Planetary/ProperlyDegenerateKAM.lean` | 150 | 17 | P5-MAIN; no theorem anchor import | provider wrapper to the exact frozen type |

36 packages, 17,540 estimated proof lines. Waves describe dependency readiness, not permission to run concurrent Lean processes. Each package is 150–800 lines.

DAG: `PG/Setting` is below both measure and assembly modules. `PGMeasure/{Collar,CompactLipschitz,
AffineSlab,LatticeTail}` feed `ResonanceSlow`, `ResonanceFast`, `ResonanceLarge`, then `TwoScale`.
`PGAssembly/{ComplexLocal,RealSlice}` feed `ComplexGlue`, then `Extension`, then `Jets`, then `Remainder`.
`FastComplex` and `Jets` feed `FrequencyBounds`/`FrequencyInverse`. These and `Weighted` feed
`Scales`/`Parameters`/`Threshold`. `Parameters` imports the P1 two-scale predicate and
P4 frequency formula; it owns `pgD0` immediately after `pgActionDomain`.
`Parameters` feeds both `KAMInputs` and `Family`, with no reverse import from either.
`Averaging` imports the delivered P2 interface; `Chart` imports
Averaging, Polar and P1. `KAMInputs` and the delivered P3 interface feed `Family`; `CellTransfer` and
`ActionBudget` feed `Lower`; `CutMeasure` supplies only abstract measure continuity; the actual parameter measure is built
in `Strictness`, downstream of Family. `CutMeasure` and `Lower` feed `Strictness`; `Main` imports those and
`FrequencyBounds`. The provider imports `Main`, never the frozen P-G theorem. No implementation
module imports a provider or DRAFT_SORRY anchor. Imports are directed; in particular `PG/Setting`
contains only source/coordinate data, not chosen witnesses that depend on downstream existence lemmas.

Chosen-witness definitions live with their supplying theorem: `pgExtension` in Extension, `pgAnalytic`
in FrequencyBounds, `pgScales` in Scales, `pgRstar` in Threshold, `pgAvg` in Averaging, `pgFamily` in
Family, the explicit `pgBudget` in ActionBudget and `pgLoss` in Lower. This avoids the subtle cycle of putting all definitions in Setting.

## 9. Binder-by-binder provider assembly

The provider declaration is `KAM.Provider.Planetary.properlyDegenerateKAM`, with the same explicit and
implicit binders as Appendix A's `main`. Its conclusion is byte-for-byte the frozen conclusion.
Do not import `KAM.Frozen.Planetary.Theorems.ProperlyDegenerateKAM` to obtain its type or proof.

| Frozen binders, in order | Construction/use |
|---|---|
| `{a b}`, `ha`, `hb` | `PGData a b` and positive dimensions for coordinates, lattice sums and a chosen first coordinate |
| `V,hV,hVc,hVb` | open connected bounded source action domain; compact closure, positive finite volume, connected complex tube |
| `W,hW,hVW` | analytic fast Hamiltonian and inverse near closure V; real and complex lower Lipschitz bounds |
| `hboundary` | choose A,d once; collar and all core-volume/radius bounds use these witnesses |
| `r0,mu0,B`, `hr0,hmu0,hB` | analytic real oscillator domain, compact coupling interval, uniform torsion gap |
| `H0,P,P0,Omega,beta` | retain these exact total functions in source data and in the frozen degenerateHamiltonian |
| `hP,hperiod` | uniform extension and periodic averaging; includes mu=0 and mu=mu0 |
| `hfreq` | use the frozen inverse witness and its two identities; do not assume a second inverse |
| `hBNF` | derivative-jet identification and uniform fifth-order remainder, from the actual normalized secularAverage |
| `htorsion,hsymm` | determinant lower bound; recover beta itself from the symmetric fourth jet |
| existential `rStar,C,c` | `rStar=finalRadius d`; `C=max(pgLoss d+1,Cw)`; `c=2*pgTau a b+2` |
| positivity and `rStar<r0`, `<1` | radius selection and positive loss constant; `C>0`, `c>0` from bounds and a,b>0 |
| arbitrary `r,mu` and five inequalities | build `admissible d (pgRstar d) r mu` by `r<finalRadius<=pgRstar`; no constants chosen using r or mu |
| existential S | `kset d r mu h (pgD0 d r mu \ B)` for the deletion B supplied by `strictness` |
| frozen `IsCylinderKolmogorovSet` | measurable union from `cell_transfer`; inclusion/location; each member is a physicalTorus with its entire range in S; `torus_conv`, two-scale-to-single-scale, and `frequency_bounds` |
| `0 < volume(S∩cell)` | `strictness` |
| strict relative lower bound | `strictness` gives coefficient `1-(Closs+1/2)*sqrt r`; C>=Closs+1 and positive finite cell give strict slack; split on sign of `1-C*sqrt r` for `ENNReal.ofReal` |
| strict upper bound | surviving mass is original mass minus positive deleted mass; finite cell measure and disjoint whole-torus families |

`Cw` is selected from `frequency_bounds` before r,mu. The same final C is used in both the fast and
slow frequency bounds and the measure inequality. The frequency exponent witnesses in each torus are
`gamma=min(gamma1,gamma2)>0`, `tau=n+1>n`. `PGData` is constructed by assigning every listed field to
the identically named binder; no field needs a new lemma or premise. The provider then applies
`KAM.Planetary.main` with the original binder list. Sealing the frozen anchor is a separate audited task.

## 10. Risks and validation

The costliest new analytic foundations are real-to-complex power-series extension and identity from a
real open slice in several variables. They are separate packages, not labelled “standard” to conceal
missing APIs. Default-heartbeat failures split estimates/modules; no budget override is permitted.
The raw P3 family must provide its quantitative measure estimate as well as tori. Its rescaled Lipschitz
bounds must be converted to the ordinary Pi/Prod norm using fixed positive scales before null-image
arguments; uniformity in r is not needed for nullity. The P2/P3 adapter proofs remain dispatch gates; Section 5 now instantiates the delivered
records and joint outputs. This design does not assert that their providers are implemented.

The signatures include a small exact P1/P7 definition snapshot (`IsChart`, `fullShift`, `angleScale`,
`twoScaleDiophantine`, `unitCube`, `polarMap`) because those draft modules are not importable built
modules in this checkout. Implementations import the owners' modules instead of redeclaring them.
Their names/types and definitionally equal bodies are preserved, and the two new scalar/general-dimension bridges are
explicit. All other imports are actual built modules or frozen definitions. Every theorem body in
Appendix A is `sorry`; there are no proof bodies disguised as definitions.

Final signature command (run serially through the required gate):

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p45 .drafts/scratch/P45Signatures.lean
```

Revision 3 signature gate: exit 0, **69 warnings, all declaration uses `sorry`**;
no errors or other warnings. Both typed upstream applications elaborate. The final
file has **1286 lines**. `#print axioms KAM.Planetary.main` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`. The literal frozen telescope and
conclusion comparison passes. All theorem bodies are sorry, and Appendix A, shared
file and checked scratch file are byte-identical. Logs:
`.drafts/scratch/P45-r3-signatures.log` and `.drafts/scratch/P45-r3-lint.log`.
`PATH=/root/code/KAM-inp-design-p45/.drafts/scratch/gated-bin:$PATH scripts/lint_sources.sh`
exits 0: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`;
`FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`.
Owned document `git diff --check` also exits 0. Static validation in
`.drafts/scratch/P45-r3-static.log` confirms Appendix/shared/scratch identity, the
literal frozen telescope/conclusion, 124 node-table rows, and all 36 named local
package dependencies in strictly earlier waves (including Parameters before KAMInputs/Family).

The signature and fixture theorems are all `sorry`; the printed main axioms include
`sorryAx`, so successful elaboration does not close P-G. The lint ABI subprocess is
routed through the required gate by the existing scratch wrapper. There is no
production Lean module change and no separate production build target in this task.

Read-only interface snapshots (SHA256):

| Input | SHA256 |
|---|---|
| `docs/graph/P/DEPGRAPH.md` (inp) | `5b1eff327a09a63a553686ba14a4763978e0f589fde8ad42cc67d6545f819f44` |
| `docs/graph/P/reviews/GLOBAL-review.md` (inp) | `39f5a84a7d261187fa474fa94ecc839a1fac463810fdd8ce674fe5766d539e65` |
| `.drafts/design/P23Signatures.lean` (inp, Revision 2) | `7d7dae4308ea9ec0ca763a2a21ce4b83280bdbb4b91d2c4f5e7567b71085e834` |
| `.drafts/design/PPart1Signatures.lean` (inp) | `78f21690c9e2623e9d9a9b6087bf32d1477434618c3089d98d0d0b99d5d098f7` |
| `.drafts/design/KeplerSignaturesP.lean` (inp) | `d9903304231afac0841cf0456d90c3dec04b2eb9e1a9752a9d4f9f9b7164d9c8` |


## Revision 2 — audit finding resolutions

| Finding | Resolution and owning package |
|---|---|
| F1 (medium) | `collar` separates all-positive-radius compactness, inclusion and set difference from t<d measure bounds; adds lower volume and neighbourhood difference inclusion. P4-CO. |
| F2 (major) | `birkhoff_ext_parameter_regularity` exports joint continuity of P0, each Omega/beta entry and complex beta symmetry on the half tube; appended output, no new hypothesis. P5-JET. |
| F3 (medium) | `analyticBoundDomain` has slow radius 2 and is used only for polynomial/C1/C2 bounds. `analyticDomain` retains slow radius 1 for inversion. P5-FD. |
| F4 (major) | `PGAnalyticSpec` now proves muStar<=mu0 by selecting a smaller positive threshold. The existing freq_inj range is unchanged and fully supported. P5-FD. |
| F5 (medium) | `dioConstant` is the explicit one-scale formula; `dio_one` exports that bound. `pgMeasureUpper1/2` and the explicit pgBudget sum replace arbitrary existential budget witnesses. P4-ONE/P5-BU. |
| F6 (medium) | `disc_measure` includes the null-centre coverage of cylinderCell by the polar image, as well as its numeric volume. P4-POL. |
| N1 (medium dispatch gate) | Section 5 and Appendix A use the delivered exact P23 fixtures, typed OscHyp/KamHyp adapters and actual elaborated theorem applications; replace separate limit_actions/limit_phi expectations by the joint two_scale_kam witnesses. Include oscillator normalization, zero mode, transformed domain and displacement dictionary. No interface approval or proof closure is inferred from elaboration. |
| N2 (low) | P4-CO supplies ext_conn before collar; P4-R0 supplies beta_inverse before its resonance work; P4-TO exports section_measure_le_of_pairwise_dist. Radius-2 bounds remain separate from the inverse domain. |

**Additional blueprint defect (F4).** `p5-pg-assembly.tex` L104–125 bounds
coefficients only for mu in [0,mu0] but the printed inverse lemma uses (0,muStar]
without saying muStar<=mu0. Outside that interval the extension is unconstrained.
The repair is an output of freq_data: shrink muStar to min(muStar,mu0), retaining
all preceding smallness bounds. This is a blueprint issue, not a pinned-paper erratum.

**Declared numeric enlargement (F5).** `pgInverseR` is a strictly positive enclosing
radius for the fast-frequency image, rather than its exact maximum. The explicit
formulas use this same witness throughout; increasing a box radius only enlarges
these positive-dimensional slab estimates. The inverse Lipschitz witness also stays
the one selected by lip_inverse. Constants and thresholds still precede r and mu.

The existing 124-node table and all twelve scoped SOURCE_GAP assignments remain.
No frozen, manifest, graph, blueprint, generated root or README edit is authorized
or performed. The source gaps remain proof obligations after these contract repairs.

## Revision 3 — audit 2 finding resolutions

| Finding | Resolution and owning package |
|---|---|
| F7 (major; completes N1) | New `pgOscAlpha=gammaBar/(4*pi*Kbar^tau)` is the constant supplied to `pg_osc_hyp`. Section 5 derives the cutoff and neighbourhood losses, corrected quadratic remainder and physical displacements, and checks the existing G bounds suffice for both remainder and `OscHyp.small`. P5-AV owns this definition and the unchanged upstream application. No source Diophantine hypothesis is strengthened. |
| F8 (medium) | Move the unchanged `pgD0` definition immediately after `pgActionDomain`, with an explicit Parameters ownership comment in Appendix A. P5-PAR imports the P1 predicate and P4 frequency formula; the package table and DAG now place it before KAMInputs and Family. Remove it from P5-FAM outputs. |
| Prior F1–F6, N2 (audit 2 PASS) | Preserve all prior collar, coefficient-regularity, radius-2, muStar, numerical-budget, polar-coverage and helper-ownership repairs. The N1 application now consumes the corrected divisor constant. |
| Validation note | Audit 2's independent lint run lacked an ABI receipt; it is not treated as a pass. Section 10 records a fresh Revision 3 lint result, separate from signature elaboration. |

F7 is a design transcription/normalization defect relative to
`p5-pg-assembly.tex` L176–178 (`stepP:p5:av-R1`), whose printed bound is
`gammaBar/(2*Kbar^tau)` before Hamiltonian scaling. F8 is a design module-ownership
defect. Neither is a new pinned-source erratum or an authorized frozen change.
The two upstream applications still check types only; all analytic proofs and the
twelve scoped SOURCE_GAP obligations remain unpaid.

## 11. Hard rules for every Lean package brief (verbatim)

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


## Appendix A. Exact signatures

`P45Signatures.lean`: 1286 lines; SHA256 `f4c7752bf23b8b149e4e5c0f1fac5288b4c32c10d19c4a17d3afe79af1c13ca2`. One file, below the 1500-line cap.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Basic
public import KAM.Canonical.Setting
public import KAM.Canonical.Flow
public import KAM.Weighted.Bracket
public import KAM.Weighted.Cauchy
public import KAM.Weighted.Projections
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm
public import KAM.Frozen.Planetary.Defs.HasFastDiffeomorphism
public import KAM.Frozen.Planetary.Defs.IsCylinderKolmogorovSet
public import KAM.Frozen.Planetary.Defs.CylinderCell
public import KAM.Frozen.Planetary.Defs.DegenerateHamiltonian
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Frozen.Planetary.Defs.FastFrequency
public import KAM.Strip.RealRestriction
public import KAM.Kepler.Basic
public import KAM.Weighted.SupWeighted
public import KAM.Measure.Lattice
public import KAM.Measure.Slab
public import KAM.Measure.Lipschitz

/-! # P45 design signatures
Design evidence only. All theorem bodies are sorry. No frozen theorem/provider imports.
P2/P3 exact upstream fixtures and typed applications appear below; proofs remain obligations.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators
namespace KAM.NormalForm
def zBall (n : ℕ) (K : ℝ) : Set (Fin n → ℤ) := {k | KAM.Fourier.modeSize k ≤ K}
def freq {n : ℕ} (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℂ) : Fin n → ℂ := fun i => fderiv ℂ h I (Pi.single i 1)
def dotC {n : ℕ} (k : Fin n → ℤ) (v : Fin n → ℂ) : ℂ := ∑ i, (k i : ℂ) * v i
def DivisorBound {n : ℕ} (V : Set (Fin n → ℂ)) (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (c : ℝ) : Prop :=
  ∀ I ∈ V, ∀ k ∈ zBall n K \ Λ, c ≤ ‖dotC k (freq h I)‖
end KAM.NormalForm

namespace KAM.Planetary

variable {a b n : ℕ}

def twoScaleDiophantine (n₁ n₂ : ℕ) (γ₁ γ₂ τ : ℝ) : Set (Fin (n₁+n₂) → ℝ) :=
  {ω | (∀ k : Fin (n₁+n₂) → ℤ, (fun i : Fin n₁ => k (Fin.castAdd n₂ i)) ≠ 0 →
    γ₁/(∑ i, |(k i:ℝ)|)^τ ≤ |∑ i, (k i:ℝ)*ω i|) ∧
    (∀ k : Fin (n₁+n₂) → ℤ, k ≠ 0 → (fun i : Fin n₁ => k (Fin.castAdd n₂ i)) = 0 →
      γ₂/(∑ i, |(k i:ℝ)|)^τ ≤ |∑ i, (k i:ℝ)*ω i|)}


/-! Exact P23 fixtures: import owning modules after landing; never reimplement these APIs. -/
open KAM.Weighted KAM.Canonical KAM.NormalForm Real
def IsLatticeTorus {d : ℕ} (L : (Fin d → ℤ) → Phase d) (G : Phase d → ℝ) (O : Set (Phase d))
    (w : Fin d → ℝ) (K : (Fin d → ℝ) → Phase d) : Prop :=
  (AnalyticOnNhd ℝ K univ ∧ ∀ θ, K θ ∈ O ∧ DifferentiableAt ℝ G (K θ)) ∧
  (∀ θ (k : Fin d → ℤ), K (θ + fun i => (k i : ℝ)) = K θ + L k) ∧
  (∀ θ θ', K θ = K θ' → ∃ k : Fin d → ℤ, θ' = θ + fun i => (k i : ℝ)) ∧
  (∀ θ, Function.Injective (fderiv ℝ K θ)) ∧
  (∀ θ u v, KAM.symplecticForm (fderiv ℝ K θ u) (fderiv ℝ K θ v) = 0) ∧
  (∀ θ t, HasDerivAt (fun s : ℝ => K (θ + s • w))
    (KAM.hamiltonianVectorField G (K (θ + t • w))) t)
abbrev CPhase (n : ℕ) := (Fin n → ℂ) × (Fin n → ℂ)
abbrev CHam (n : ℕ) := CPhase n → ℂ
def geometricWidth (σ : ℝ) : ℝ := σ / (2 * π)
def realBase {n : ℕ} (D : Set (Fin n → ℝ)) : Set (Fin n → ℂ) := KAM.realInclusion n '' D
def coefficientDom {n : ℕ} (D : Set (Fin n → ℝ)) (r σ : ℝ) : Set (CPhase n) :=
  Dom n (realBase D) r (geometricWidth σ)
def realTube {n : ℕ} (D : Set (Fin n → ℝ)) (r : ℝ) : Set (Fin n → ℝ) :=
  (KAM.realInclusion n) ⁻¹' KAM.actionNbhd D r
def firstBlock {a b : ℕ} {𝕜 : Type*} (x : Fin (a + b) → 𝕜) : Fin a → 𝕜 :=
  fun i => x (Fin.castAdd b i)
def lastBlock {a b : ℕ} {𝕜 : Type*} (x : Fin (a + b) → 𝕜) : Fin b → 𝕜 :=
  fun i => x (Fin.natAdd a i)
def oscPack {n m : ℕ} (z : CPhase (n + m)) : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ) :=
  (firstBlock (b := m) z.1, Fin.append (firstBlock (b := m) z.2)
    (Fin.append (lastBlock (a := n) z.2) (lastBlock (a := n) z.1)))
def oscUnpack {n m : ℕ} (z : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)) : CPhase (n + m) :=
  (Fin.append z.1 (lastBlock (a := m) (lastBlock (a := n) z.2)),
    Fin.append (firstBlock (b := m + m) z.2) (firstBlock (b := m) (lastBlock (a := n) z.2)))
def oscFunction {n m : ℕ} (f : CHam (n + m)) : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ) → ℂ := f ∘ oscUnpack
def oscParams {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq : ℝ) : Set (Fin (n + (m + m)) → ℂ) :=
  {x | firstBlock (b := m + m) x ∈ KAM.actionNbhd D r ∧
    ‖firstBlock (b := m) (lastBlock (a := n) x)‖ < rp ∧
    ‖lastBlock (a := m) (lastBlock (a := n) x)‖ < rq}
def oscDom {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S : ℝ) : Set (CPhase (n + m)) :=
  oscPack ⁻¹' (KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq)
def oscBound {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S : ℝ) (f : CHam (n + m)) (E : ℝ) : Prop :=
  ∀ x ∈ oscParams (m := m) D r rp rq,
    WSummable (oscFunction f) S x ∧ wsum (oscFunction f) S x ≤ E
def oscClass {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S : ℝ) (f : CHam (n + m)) : Prop :=
  DifferentiableOn ℂ f (oscDom D r rp rq S) ∧
    ∀ j : Fin n, ∀ z ∈ oscDom D r rp rq S,
      f (z.1 + Pi.single (Fin.castAdd m j) 1, z.2) = f z
structure OscHyp {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq sbar s K α E : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m)) : Prop where
  n_pos : 1 ≤ n
  m_pos : 1 ≤ m
  positive : 0 < r ∧ 0 < rp ∧ 0 < rq ∧ 0 < s ∧ 0 < K ∧ 0 < α
  sbar_nonneg : 0 ≤ sbar
  E_nonneg : 0 ≤ E
  budget : 6 ≤ 2 * π * K * s
  holo : DifferentiableOn ℂ h (KAM.actionNbhd D r)
  real_h : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd D r → (h (KAM.realInclusion n I)).im = 0
  cls : oscClass D r rp rq (sbar + s) f
  bound : oscBound D r rp rq (sbar + s) f E
  real_f : RealOn (oscDom D r rp rq (sbar + s)) f
  divisor : DivisorBound (KAM.actionNbhd D r) K {0} h α
  small : 2 ^ 12 * (1 + (m : ℝ)) * K * E * s ≤ α * min (r * s) (rp * rq)
theorem averaged_remainder {n m : ℕ} {D : Set (Fin n → ℝ)} {r ε₀ s₀ ε μ α : ℝ}
    {h : (Fin n → ℂ) → ℂ} {P : CHam (n + m)}
    (hε : 0 < ε ∧ ε < exp (-1 / 5)) (hμ : 0 < μ)
    (H : OscHyp D r ε₀ ε₀ 0 s₀ (15 / (π * s₀) * log (1 / ε)) α μ h (μ • P))
    (hP : oscBound D r ε₀ ε₀ s₀ P 1) :
    ∃ (Ψ : CPhase (n + m) → CPhase (n + m)) (g fs R : CHam (n + m)),
      let V := oscDom D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6)
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧ MapsTo Ψ V (oscDom D r ε₀ ε₀ s₀) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin n → ℤ,
        Ψ (z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) = Ψ z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) ∧
      (∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈ V →
        Ψ (KAM.realInclusion₂ (n + m) x) ∈ range (KAM.realInclusion₂ (n + m))) ∧
      oscClass D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) g ∧ RealOn V g ∧
      (∀ x ∈ oscParams (m := m) D (r / 2) (ε₀ / 2) (ε₀ / 2), ∀ θ θ',
        oscUnpack (θ, x) ∈ V → oscUnpack (θ', x) ∈ V → g (oscUnpack (θ, x)) = g (oscUnpack (θ', x))) ∧
      oscClass D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) fs ∧ RealOn V fs ∧ RealOn V R ∧
      (∀ z ∈ V, h (firstBlock (b := m) (Ψ z).2) + μ * P (Ψ z) =
        h (firstBlock (b := m) z.2) + μ * coeff (oscFunction P) (oscPack z).2 0 + R z) ∧
      (∀ z ∈ V, R z = g z - μ * coeff (oscFunction P) (oscPack z).2 0 + fs z) ∧
      oscClass D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) R ∧
      oscBound D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) R
        (400 * (1 + (m : ℝ)) * μ ^ 2 / (2 * π * α * min (r * s₀) (ε₀ ^ 2)) + μ * ε ^ 5) ∧
      oscBound D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) fs (μ * ε ^ 5) ∧
      ∀ z ∈ V,
        2 * π * α * s₀ * ‖firstBlock (b := m) ((Ψ z).2 - z.2)‖ ≤ 3 * μ ∧
        2 * π * α * r * ‖firstBlock (b := m) ((Ψ z).1 - z.1)‖ ≤ 9 * μ ∧
        2 * π * α * ε₀ * ‖lastBlock (a := n) ((Ψ z).2 - z.2)‖ ≤ 9 * μ ∧
        2 * π * α * ε₀ * ‖lastBlock (a := n) ((Ψ z).1 - z.1)‖ ≤ 9 * μ := sorry
structure ScaleData where
  τ : ℝ
  γ₁ : ℝ
  γ₂ : ℝ
  s : ℝ
  ρ : ℝ
  E : ℝ
  M : ℝ
  Mhat : ℝ
  Mbar : ℝ
  Mbar₁ : ℝ
  Mbar₂ : ℝ
  L : ℝ
def constants (p : ScaleData) : ℝ × ℝ × ℝ :=
  let x := p.E * p.M ^ 2 * p.L / p.γ₁ ^ 2
  let K := 6 / p.s * max 1 (log (1 / x))
  let R := min (min (p.γ₁ / (3 * p.M * K ^ (p.τ + 1)))
    (p.γ₂ / (3 * p.Mhat * K ^ (p.τ + 1)))) p.ρ
  (K, R, p.E * p.L / R ^ 2)
def cutoff (p : ScaleData) : ℝ := (constants p).1
def rhoHat (p : ScaleData) : ℝ := (constants p).2.1
def eHat (p : ScaleData) : ℝ := (constants p).2.2
def kamConstant (n : ℕ) (τ : ℝ) : ℝ := max (2 ^ 13 * (n : ℝ)) ((24 : ℝ) ^ (τ + 1) / 3)
def complementConstant (n : ℕ) : ℝ := 1 + (1 + 2 ^ n) * (1 + (4 / 3 : ℝ) ^ n)
def initialL (M Mhat Mbar : ℝ) : ℝ := max Mbar (max M⁻¹ Mhat⁻¹)
def realFreq {n : ℕ} (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (freq h (KAM.realInclusion n I) i).re
def dioBase {a b : ℕ} (D : Set (Fin (a + b) → ℝ)) (h : (Fin (a + b) → ℂ) → ℂ)
    (p : ScaleData) : Set (Fin (a + b) → ℝ) :=
  D ∩ realFreq h ⁻¹' twoScaleDiophantine a b p.γ₁ p.γ₂ p.τ
def omegaSet {a b : ℕ} (D : Set (Fin (a + b) → ℝ)) (h : (Fin (a + b) → ℂ) → ℂ)
    (p : ScaleData) : Set (Fin (a + b) → ℝ) :=
  realFreq h '' D ∩ twoScaleDiophantine a b p.γ₁ p.γ₂ p.τ
structure KamHyp {a b : ℕ} (D : Set (Fin (a + b) → ℝ)) (sbar : ℝ) (p : ScaleData)
    (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) : Prop where
  a_pos : 1 ≤ a
  b_pos : 1 ≤ b
  τ_gt : ((a + b : ℕ) : ℝ) < p.τ
  positive : 0 < p.γ₂ ∧ 0 < p.s ∧ 0 < p.ρ ∧ 0 < p.E ∧
    0 < p.M ∧ 0 < p.Mhat ∧ 0 < p.Mbar ∧ 0 < p.Mbar₁ ∧ 0 < p.Mbar₂
  gamma_order : p.γ₂ ≤ p.γ₁
  widths : 4 * p.s ≤ sbar ∧ sbar < 1
  normalized : p.Mhat ≤ p.M ∧ p.Mbar₁ ≤ p.Mbar ∧ p.Mbar₂ ≤ p.Mbar
  L_bound : initialL p.M p.Mhat p.Mbar ≤ p.L
  holo : DifferentiableOn ℂ h (KAM.actionNbhd D p.ρ)
  real_h : RealOn (coefficientDom D p.ρ (sbar + p.s)) (fun z => h z.2)
  real_f : RealOn (coefficientDom D p.ρ (sbar + p.s)) f
  f_class : InClass (realBase D) p.ρ (geometricWidth (sbar + p.s)) f
  f_bound : WBound (realBase D) p.ρ (geometricWidth (sbar + p.s)) f p.E
  injective : Set.InjOn (freq h) (KAM.actionNbhd D p.ρ)
  hessian : ∀ I ∈ KAM.actionNbhd D p.ρ,
    ‖fderiv ℂ (freq h) I‖ ≤ p.M ∧
    (∀ v, ‖lastBlock (a := a) (fderiv ℂ (freq h) I v)‖ ≤ p.Mhat * ‖v‖) ∧
    ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
      (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) = fderiv ℂ (freq h) I ∧
      ‖(A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ))‖ ≤ p.Mbar ∧
      (∀ v, ‖firstBlock (b := b) (A.symm v)‖ ≤ p.Mbar₁ * ‖v‖) ∧
      (∀ v, ‖lastBlock (a := a) (A.symm v)‖ ≤ p.Mbar₂ * ‖v‖)
  small : kamConstant (a + b) p.τ * eHat p < 1
def limitmap_data {n : ℕ} (R s : ℝ) (z : Phase n) : ℝ := max (‖z.1‖ * (2 * π / s)) (‖z.2‖ / R)
theorem two_scale_kam {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f)
    (hL : p.L = initialL p.M p.Mhat p.Mbar) :
    ∃ (i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ))
      (Φ : Phase (a + b) → Phase (a + b))
      (K : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ) → Phase (a + b))
      (I₀ : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ))
      (KC : (Fin (a + b) → ℝ) → (Fin (a + b) → ℂ) → CPhase (a + b)),
      let D₀ := dioBase D h p
      let Ω := omegaSet D h p
      let Dstar := i '' D₀
      let r := 32 * eHat p * rhoHat p
      let Hr := fun z : Phase (a + b) => (h (KAM.realInclusion (a + b) z.2) + f (KAM.realInclusion₂ (a + b) z)).re
      let KO := ⋃ ω ∈ Ω, range (K ω)
      (∀ ω ∈ Ω, I₀ ω ∈ D₀ ∧ realFreq h (I₀ ω) = ω ∧ ∀ I ∈ D₀, realFreq h I = ω → I = I₀ ω) ∧
      (∀ I ∈ D₀,
        ‖firstBlock (b := b) (i I - I)‖ ≤ 20 * (p.Mbar₁ / p.Mbar) * eHat p * rhoHat p ∧
        ‖lastBlock (a := a) (i I - I)‖ ≤ 20 * (p.Mbar₂ / p.Mbar) * eHat p * rhoHat p) ∧
      (∀ I ∈ D₀, ∀ J ∈ D₀, ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat p * ‖I - J‖) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ y ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
        limitmap_data (rhoHat p) p.s ((Φ x - x) - (Φ y - y)) ≤
          768 * (a + b) * eHat p * limitmap_data (rhoHat p) p.s (x - y)) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ k : Fin (a + b) → ℤ,
        Φ (x + KAM.ODE.angleShift k) = Φ x + KAM.ODE.angleShift k) ∧
      (∀ ω ∈ Ω, ∀ θ, K ω θ = Φ (θ, i (I₀ ω))) ∧
      (∀ ω ∈ Ω,
        IsLatticeTorus KAM.ODE.angleShift Hr (univ ×ˢ realTube D r) ω (K ω) ∧
        DifferentiableOn ℂ (KC ω) (KAM.complexStrip (a + b) (geometricWidth sbar)) ∧
        (∀ θ, KC ω (KAM.realInclusion (a + b) θ) = KAM.realInclusion₂ (a + b) (K ω θ)) ∧
        (∀ θ ∈ KAM.complexStrip (a + b) (geometricWidth sbar),
          ‖(KC ω θ).1 - θ‖ ≤ 3 / (4 * π) * eHat p * p.s) ∧
        (∀ θ,
          ‖firstBlock (b := b) ((K ω θ).2 - I₀ ω)‖ ≤ 20 * (p.Mbar₁ / p.Mbar + p.Mhat / p.M) * eHat p * rhoHat p ∧
          ‖lastBlock (a := a) ((K ω θ).2 - I₀ ω)‖ ≤ 20 * (p.Mbar₂ / p.Mbar + 1) * eHat p * rhoHat p ∧
          ‖fderiv ℝ (fun θ => (K ω θ).1 - θ) θ‖ ≤ 3 / 4 * (a + b) * eHat p)) ∧
      (∀ ω ∈ Ω, ∀ ω' ∈ Ω, ∀ θ θ', ∀ k : Fin (a + b) → ℤ,
        K ω θ = K ω' θ' + KAM.ODE.angleShift k → ω = ω' ∧ θ = θ' + fun j => (k j : ℝ)) ∧
      (∀ ω ∈ Ω, ∀ ω' ∈ Ω, ‖ω - ω'‖ < p.ρ / p.Mbar → ‖I₀ ω - I₀ ω'‖ ≤ p.Mbar * ‖ω - ω'‖) ∧
      (Bornology.IsBounded D → ∀ ω ∈ Ω, ∀ ω' ∈ Ω,
        ‖I₀ ω - I₀ ω'‖ ≤ p.Mbar * max 1 (Metric.diam D / p.ρ) * ‖ω - ω'‖) ∧
      volume (((univ ×ˢ realTube D r) \ KO) ∩ {z : Phase (a + b) | ∀ j, z.1 j ∈ Ico 0 1}) ≤
        ENNReal.ofReal (complementConstant (a + b)) *
          (volume (D \ D₀) + volume (realTube D r \ D)) := sorry


/-- Scalar-generic extension; real specializations are identified with the frozen projections. -/
def blockFast {a b : ℕ} {F : Type*} (v : Fin (a+b) → F) : Fin a → F := fun i => v (Fin.castAdd b i)
def blockSlow {a b : ℕ} {F : Type*} (v : Fin (a+b) → F) : Fin b → F := fun i => v (Fin.natAdd a i)
theorem blockFast_real (v : Fin (a+b) → ℝ) : blockFast v = fast v := sorry
theorem blockSlow_real (v : Fin (a+b) → ℝ) : blockSlow v = slow v := sorry

/-- Source data only: the frozen P-G binders, without extra hypotheses. -/
structure PGData (a b : ℕ) where
  ha : 0 < a
  hb : 0 < b
  V : Set (Fin a → ℝ)
  hV : IsOpen V
  hVc : IsConnected V
  hVb : Bornology.IsBounded V
  W : Set (Fin a → ℝ)
  hW : IsOpen W
  hVW : closure V ⊆ W
  hboundary : ∃ A d : ℝ, 0 < A ∧ 0 < d ∧ ∀ t : ℝ, 0 < t → t < d →
    volume {I : Fin a → ℝ | ∃ J ∈ frontier V, dist I J < t} ≤ ENNReal.ofReal (A * t)
  r0 : ℝ
  mu0 : ℝ
  B : ℝ
  hr0 : 0 < r0
  hmu0 : 0 < mu0
  hB : 0 < B
  H0 : (Fin a → ℝ) → ℝ
  P : ℝ → Phase (a + b) → ℝ
  P0 : ℝ → (Fin a → ℝ) → ℝ
  Omega : ℝ → (Fin a → ℝ) → (Fin b → ℝ)
  beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ
  hP : AnalyticOnNhd ℝ (fun z : ℝ × Phase (a + b) => P z.1 z.2)
    (Icc 0 mu0 ×ˢ closure (cylinder V r0))
  hperiod : ∀ mu ∈ Icc 0 mu0, ∀ z ∈ cylinder V r0, ∀ k : Fin a → ℤ,
    P mu (z + fastShift k) = P mu z
  hfreq : HasFastDiffeomorphism H0 W
  hBNF : HasSecularBirkhoffForm P V r0 mu0 P0 Omega beta
  htorsion : ∀ mu ∈ Icc 0 mu0, ∀ I ∈ V, B ≤ |(beta mu I).det|
  hsymm : ∀ mu ∈ Icc 0 mu0, ∀ I ∈ V, (beta mu I).IsSymm

def pgBoundaryA (d : PGData a b) : ℝ := d.hboundary.choose

def pgBoundaryD (d : PGData a b) : ℝ := d.hboundary.choose_spec.choose

/-- Real neighbourhood, expressed by witnesses to avoid empty-set infDist totality. -/
def realNbhd (X : Set (Fin n → ℝ)) (s : ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ y ∈ X, dist x y < s}

def innerCore (V : Set (Fin a → ℝ)) (t : ℝ) : Set (Fin a → ℝ) :=
  {I ∈ V | ∀ J ∈ frontier V, t ≤ dist I J}

def actionShell (b : ℕ) (l u : ℝ) : Set (Fin b → ℝ) := pi univ fun _ => Ioo l u

def joinedActions (X : Set (Fin a → ℝ)) (Y : Set (Fin b → ℝ)) : Set (Fin (a+b) → ℝ) :=
  {J | blockFast J ∈ X ∧ blockSlow J ∈ Y}

def unitCube (n : ℕ) : Set (Fin n → ℝ) := pi univ fun _ => Ico (0 : ℝ) 1

/-- `bpP:p4:collar`, all clauses, with an unnormalised bound. -/
theorem collar {V : Set (Fin a → ℝ)}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {A d : ℝ}
    (hc : ∀ s : ℝ, 0 < s → s < d →
      volume {I : Fin a → ℝ | ∃ J ∈ frontier V, dist I J < s} ≤
        ENNReal.ofReal (A*s)) :
    (∀ t : ℝ, 0 < t →
      IsCompact (innerCore V t) ∧ innerCore V t ⊆ V ∧
      V \ innerCore V t =
        {I ∈ V | ∃ J ∈ frontier V, dist I J < t}) ∧
    (∀ t : ℝ, 0 < t → t < d →
      volume (V \ innerCore V t) ≤ ENNReal.ofReal (A*t) ∧
      volume V - ENNReal.ofReal (A*t) ≤ volume (innerCore V t)) ∧
    (∀ t s : ℝ, 0 < s → s < t →
      realNbhd (innerCore V t) s ⊆ V ∧
      realNbhd (innerCore V t) s \ innerCore V t ⊆ V \ innerCore V t) ∧
    (∀ t s : ℝ, 0 < s → s < t → t < d →
      volume (realNbhd (innerCore V t) s \ innerCore V t) ≤
        ENNReal.ofReal (A*t)) := by sorry

/-- Classical derivative regularity used by P4. -/
theorem ext_deriv {p q : ℕ} {U : Set (Fin p → ℝ)} {f : (Fin p → ℝ) → Fin q → ℝ}
    (hf : AnalyticOnNhd ℝ f U) :
    AnalyticOnNhd ℝ (fderiv ℝ f) U ∧ ContDiffOn ℝ 1 f U := sorry

theorem ext_conn {C V : Set (Fin a → ℝ)} (hC : IsPreconnected C)
    (hCV : (C ∩ V).Nonempty) (hCc : (C \ V).Nonempty) : (C ∩ frontier V).Nonempty := sorry

theorem realNbhd_joinedActions (X : Set (Fin a → ℝ)) (Y : Set (Fin b → ℝ)) (s : ℝ) :
    realNbhd (joinedActions X Y) s = joinedActions (realNbhd X s) (realNbhd Y s) := sorry

/-- Joint C1 is stronger input than the printed partial-C1 premise; conditional helper only. -/
theorem lip_compact_c1 {p m q : ℕ} {T : Set (Fin p → ℝ)} {X : Set (Fin m → ℝ)}
    {O : Set ((Fin p → ℝ) × (Fin m → ℝ))} {f : (Fin p → ℝ) × (Fin m → ℝ) → Fin q → ℝ}
    (hT : IsCompact T) (hX : IsCompact X) (hO : IsOpen O) (hsub : T ×ˢ X ⊆ O)
    (hf : ContDiffOn ℝ 1 f O) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ T, ∀ x ∈ X, ∀ y ∈ X, ‖f (t,x)-f (t,y)‖ ≤ L*‖x-y‖ := sorry

/-- Exact partial-C1 source version. -/
theorem lip_compact {p m q : ℕ} {T : Set (Fin p → ℝ)} {X : Set (Fin m → ℝ)}
    {O : Set ((Fin p → ℝ) × (Fin m → ℝ))} {f : (Fin p → ℝ) × (Fin m → ℝ) → Fin q → ℝ}
    (hT : IsCompact T) (hX : IsCompact X) (hO : IsOpen O) (hsub : T ×ˢ X ⊆ O)
    (hf : ContinuousOn f O)
    (hd : ∀ z ∈ O, DifferentiableAt ℝ (fun x => f (z.1,x)) z.2)
    (hdf : ContinuousOn (fun z => fderiv ℝ (fun x => f (z.1,x)) z.2) O) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ T, ∀ x ∈ X, ∀ y ∈ X, ‖f (t,x)-f (t,y)‖ ≤ L*‖x-y‖ := sorry

theorem lip_inverse {H0 : (Fin a → ℝ) → ℝ} {V W : Set (Fin a → ℝ)}
    (hW : IsOpen W) (hVb : Bornology.IsBounded V) (hVW : closure V ⊆ W)
    (hf : HasFastDiffeomorphism H0 W) :
    ∃ (g : (Fin a → ℝ) → Fin a → ℝ) (L R : ℝ), 1 ≤ L ∧ 0 < R ∧
      ContinuousOn (fastFrequency H0) W ∧ IsCompact (fastFrequency H0 '' closure V) ∧
      (∀ I ∈ W, g (fastFrequency H0 I) = I) ∧
      (∀ y ∈ fastFrequency H0 '' closure V, ‖y‖ ≤ R) ∧
      ∀ y ∈ fastFrequency H0 '' closure V, ∀ y' ∈ fastFrequency H0 '' closure V,
        ‖g y-g y'‖ ≤ L*‖y-y'‖ := sorry

/-- Chosen inverse and its constants come from the same frozen-inverse specification. -/
def pgInverse (d : PGData a b) : (Fin a → ℝ) → Fin a → ℝ :=
  (lip_inverse d.hW d.hVb d.hVW d.hfreq).choose

def pgInverseL (d : PGData a b) : ℝ :=
  (lip_inverse d.hW d.hVb d.hVW d.hfreq).choose_spec.choose

def pgInverseR (d : PGData a b) : ℝ :=
  (lip_inverse d.hW d.hVb d.hVW d.hfreq).choose_spec.choose_spec.choose

theorem beta_inverse (hb : 0 < b) {T : Matrix (Fin b) (Fin b) ℝ} {B M : ℝ}
    (hB : 0 < B) (hM : 0 ≤ M) (hdet : B ≤ |T.det|) (hentries : ∀ i j, |T i j| ≤ M) :
    ∀ v : Fin b → ℝ, ‖v‖ ≤ ((Nat.factorial b : ℝ)*M^(b-1)/B)*‖T.transpose.mulVec v‖ := sorry

/-- Polynomial uses the frozen coefficients themselves on V. -/
def secularPolynomial (P0 : ℝ → (Fin a → ℝ) → ℝ)
    (Omega : ℝ → (Fin a → ℝ) → Fin b → ℝ)
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ)
    (mu : ℝ) (I : Fin a → ℝ) (xi : Fin b → ℝ) : ℝ :=
  P0 mu I + ∑ j, Omega mu I j * xi j + (1/2:ℝ)*∑ i, ∑ j, beta mu I i j*xi i*xi j

def slowFrequency (Omega : ℝ → (Fin a → ℝ) → Fin b → ℝ)
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ)
    (mu : ℝ) (I : Fin a → ℝ) (xi : Fin b → ℝ) : Fin b → ℝ :=
  Omega mu I + (beta mu I).mulVec xi

def freq (H0 : (Fin a → ℝ) → ℝ) (P0 : ℝ → (Fin a → ℝ) → ℝ)
    (Omega : ℝ → (Fin a → ℝ) → Fin b → ℝ)
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ)
    (mu : ℝ) (J : Fin (a+b) → ℝ) : Fin (a+b) → ℝ :=
  Fin.append (fastFrequency H0 (blockFast J) + mu •
    fun i => fderiv ℝ (fun I => secularPolynomial P0 Omega beta mu I (blockSlow J)) (blockFast J) (Pi.single i 1))
    (mu • slowFrequency Omega beta mu (blockFast J) (blockSlow J))

/-- S4 source premises. The two-scale set is owned by P1 and is not redeclared here. -/
structure MeasureData (a b : ℕ) where
  H0 : (Fin a → ℝ) → ℝ
  W : Set (Fin a → ℝ)
  V : Set (Fin a → ℝ)
  core : Set (Fin a → ℝ)
  hW : IsOpen W
  hVb : Bornology.IsBounded V
  hVW : closure V ⊆ W
  hfreq : HasFastDiffeomorphism H0 W
  hcore : IsCompact core
  hcoreV : core ⊆ V
  hvol : 0 < volume core
  P0 : ℝ → (Fin a → ℝ) → ℝ
  Omega : ℝ → (Fin a → ℝ) → Fin b → ℝ
  beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ
  tau : ℝ
  lambda0 : ℝ
  mu1 : ℝ
  LN : ℝ
  LB : ℝ
  Lg : ℝ
  Ry : ℝ
  hRy : 0 < Ry
  hRybound : ∀ y ∈ fastFrequency H0 '' closure V, ‖y‖ ≤ Ry
  ha : 0 < a
  hb : 0 < b
  htau : (a+b:ℕ) < tau
  hlambda0 : 0 < lambda0
  hmu1 : 0 < mu1
  hLN : 1 ≤ LN
  hLB : 1 ≤ LB
  hLg : 1 ≤ Lg
  g : (Fin a → ℝ) → Fin a → ℝ
  hinv : ∀ I ∈ W, g (fastFrequency H0 I) = I
  hglip : ∀ y ∈ fastFrequency H0 '' closure V, ∀ y' ∈ fastFrequency H0 '' closure V,
    ‖g y-g y'‖ ≤ Lg*‖y-y'‖
  small : mu1 ≤ (2*(1+2*b*LN*LB)*a*LN*Lg)⁻¹
  N1 : ∀ mu ∈ Ioc 0 mu1, ∀ I ∈ core, ∀ I' ∈ core, ∀ xi : Fin b → ℝ, ‖xi‖ ≤ lambda0 →
    ‖blockFast (freq H0 P0 Omega beta mu (Fin.append I xi)) - fastFrequency H0 I -
      (blockFast (freq H0 P0 Omega beta mu (Fin.append I' xi)) - fastFrequency H0 I')‖ ≤ mu*LN*‖I-I'‖ ∧
    ‖slowFrequency Omega beta mu I xi - slowFrequency Omega beta mu I' xi‖ ≤ LN*‖I-I'‖
  N2 : ∀ mu ∈ Ioc 0 mu1, ∀ I ∈ core, ∀ xi xi' : Fin b → ℝ,
    ‖xi‖ ≤ lambda0 → ‖xi'‖ ≤ lambda0 →
    ‖blockFast (freq H0 P0 Omega beta mu (Fin.append I xi)) -
      blockFast (freq H0 P0 Omega beta mu (Fin.append I xi'))‖ ≤ mu*LN*‖xi-xi'‖
  N3 : ∀ mu ∈ Ioc 0 mu1, ∀ I ∈ core, ∀ v : Fin b → ℝ, ‖v‖ ≤ LB*‖(beta mu I).transpose.mulVec v‖

/-- Real normals and arbitrary offset: the integer-normal K slab theorem alone is insufficient. -/
theorem affine_slab (hn : 0 < n) (ell : Fin n → ℝ) (hell : ell ≠ 0)
    (c lambda eps : ℝ) (hl : 0 < lambda) (he : 0 < eps) :
    volume {x : Fin n → ℝ | (∀ i, x i ∈ Icc (-lambda) lambda) ∧ |∑ i, ell i*x i+c| < eps} ≤
      ENNReal.ofReal (2*eps*(2*lambda)^(n-1)/‖ell‖) := sorry

def latticeWeight (tau : ℝ) (k : Fin n → ℤ) : ℝ := (∑ i, |(k i : ℝ)|) ^ (-tau)

theorem lattice_tail (hn : 0 < n) {tau : ℝ} (ht : (n:ℝ) < tau) :
    Summable (fun k : {k : Fin n → ℤ // k ≠ 0} => latticeWeight tau k.val) ∧
    (∑' k : {k : Fin n → ℤ // k ≠ 0}, latticeWeight tau k.val) ≤
      2*3^(n-1)*(tau+1-n)/(tau-n) ∧
    ∀ m : ℝ, 1 ≤ m →
      (∑' k : {k : Fin n → ℤ // m < ∑ i, |(k i : ℝ)|}, latticeWeight (tau+1) k.val) ≤
      (2*3^(n-1)/(tau+1-n))*(2/m)^(tau+1-n) := sorry

/-- Resonance union helper; `resonanceBad_eq` identifies it with the exact P1 predicate. -/
def resonanceBad (F : (Fin (a+b) → ℝ) → Fin (a+b) → ℝ)
    (D : Set (Fin (a+b) → ℝ)) (alpha1 alpha2 tau : ℝ) : Set (Fin (a+b) → ℝ) :=
  {J ∈ D | ∃ k : Fin (a+b) → ℤ, k ≠ 0 ∧
    |∑ i, (k i : ℝ)*F J i| <
      (if (blockFast k : Fin a → ℤ) = 0 then alpha2 else alpha1)/(∑ i, |(k i : ℝ)|)^tau}

def latticeS (n : ℕ) (tau : ℝ) : ℝ := 2*3^(n-1)*(tau+1-n)/(tau-n)

def measure_c1 (d : MeasureData a b) : ℝ :=
  d.Lg^(a+b)/(volume d.core).toReal * max (4*(2*d.Ry)^(a-1)*latticeS (a+b) d.tau)
    (4*b^2*d.LB*(2*d.Ry)^a * (2*3^(a+b-1)/(d.tau+1-(a+b:ℕ))) *
      (4*d.LN*d.Lg)^(d.tau+1-(a+b:ℕ)))

def measure_c2 (d : MeasureData a b) : ℝ := b*d.LB*latticeS b (d.tau+1)

theorem two_scale_diophantine_measure (d : MeasureData a b)
    (lambda mu alpha1 alpha2 : ℝ) (hl : 0 < lambda) (hl0 : lambda ≤ d.lambda0)
    (hmu : mu ∈ Ioc 0 d.mu1) (ha1 : 0 < alpha1) (ha2 : 0 < alpha2)
    (Q : Set (Fin b → ℝ)) (hQ : MeasurableSet Q) (hQsub : Q ⊆ actionShell b (-lambda) lambda) :
    volume (resonanceBad (freq d.H0 d.P0 d.Omega d.beta mu)
      (joinedActions d.core Q) alpha1 alpha2 d.tau) ≤
      ENNReal.ofReal (measure_c1 d*alpha1*(1+mu^(d.tau-(a+b:ℕ))/lambda)+measure_c2 d*(alpha2/mu)/lambda) *
        volume d.core * ENNReal.ofReal ((2*lambda)^b) := sorry

/-- P4 enclosure estimate also valid for the Cantor core X used by P5. -/
theorem domain_collar_helper {X : Set (Fin a → ℝ)} (hX : MeasurableSet X)
    {l u s E : ℝ} (hl : 0 < l) (hlu : l < u) (hs : 0 < s) (hsl : s < l)
    (hXfinite : volume X < ⊤) (hE : volume (realNbhd X s \ X) ≤ ENNReal.ofReal E) :
    volume (realNbhd (joinedActions X (actionShell b l u)) s \ joinedActions X (actionShell b l u)) ≤
      ENNReal.ofReal (E*(u-l+2*s)^b) + volume X *
        ENNReal.ofReal ((u-l+2*s)^b-(u-l)^b) := sorry

/-- General a,b extension of the existing Kepler `polarMap`; same formula at a=b. -/
def oscillatorPolar (z : Phase (a+b)) : Phase (a+b) :=
  assemble (blockFast z.2) (blockFast z.1)
    (fun j => Real.sqrt (2*blockSlow z.2 j)*Real.cos (blockSlow z.1 j))
    (fun j => Real.sqrt (2*blockSlow z.2 j)*Real.sin (blockSlow z.1 j))

/-- Existing Kepler/P7 draft definition, reproduced only in this elaboration snapshot. -/
def polarMap (z : Phase (n+n)) : Phase (n+n) :=
  assemble (fast z.2) (fast z.1) (fun i => Real.sqrt (2*slow z.2 i)*Real.cos (slow z.1 i))
    (fun i => Real.sqrt (2*slow z.2 i)*Real.sin (slow z.1 i))

theorem oscillatorPolar_eq_polarMap (z : Phase (n+n)) :
    oscillatorPolar (a:=n) (b:=n) z = polarMap z := sorry

def polarCellMap (z : Phase (a+b)) : Phase (a+b) :=
  oscillatorPolar ((2*Real.pi) • z.1,z.2)

theorem disc_measure {V : Set (Fin a → ℝ)} (hV : MeasurableSet V)
    {r : ℝ} (hr : 0 < r) :
    volume (cylinderCell (b:=b) V r) =
      ENNReal.ofReal ((2*Real.pi)^(a+b)*(r^2/2)^b)*volume V ∧
    volume (cylinderCell (b:=b) V r \ polarCellMap ''
      {z : Phase (a+b) | blockFast z.2 ∈ V ∧
        blockSlow z.2 ∈ actionShell b 0 (r^2/2) ∧
        z.1 ∈ unitCube (a+b)}) = 0 := by sorry

theorem disc_measure_image {X : Set (Phase (a+b))} (hX : MeasurableSet X)
    (hpos : ∀ z ∈ X, ∀ j : Fin b, 0 < blockSlow z.2 j)
    (hcell : ∀ z ∈ X, z.1 ∈ unitCube (a+b)) :
    MeasurableSet (polarCellMap '' X) ∧
    volume (polarCellMap '' X) = ENNReal.ofReal ((2*Real.pi)^(a+b))*volume X := sorry

theorem disc_measure_shell {V : Set (Fin a → ℝ)} (hV : MeasurableSet V)
    {r l : ℝ} (hr : 0 < r) (hl : 0 < l) (hlr : l < r^2/2) :
    volume {z ∈ cylinderCell (b:=b) V r | ∃ j : Fin b,
      oscillatorAction (blockSlow z.2) (blockSlow z.1) j ≤ l} ≤
      ENNReal.ofReal (b*l/(r^2/2))*volume (cylinderCell (b:=b) V r) := sorry

abbrev PGComplexPhase (n : ℕ) := (Fin n → ℂ) × (Fin n → ℂ)

def assembleComplex (I phi : Fin a → ℂ) (p q : Fin b → ℂ) : PGComplexPhase (a+b) :=
  (Fin.append phi q,Fin.append I p)

def extensionDomain (d : PGData a b) (delta : ℝ) : Set (PGComplexPhase (a+b)) :=
  {z | ∃ w : Phase (a+b), blockFast w.2 ∈ closure d.V ∧
    ‖(blockSlow w.2,blockSlow w.1)‖ ≤ d.r0/2 ∧ ‖z-KAM.realInclusion₂ (a+b) w‖ < delta}

/-- Produced witness, never an extra hypothesis of P-G. -/
structure PGExtension (d : PGData a b) where
  delta : ℝ
  MP : ℝ
  M0 : ℝ
  P : ℝ → PGComplexPhase (a+b) → ℂ
  H0 : (Fin a → ℂ) → ℂ
  delta_pos : 0 < delta
  delta_lt : delta < 1
  MP_pos : 0 < MP
  M0_pos : 0 < M0
  holo : ∀ mu ∈ Icc 0 d.mu0, DifferentiableOn ℂ (P mu) (extensionDomain d delta)
  continuous : ContinuousOn (fun z : ℝ × PGComplexPhase (a+b) => P z.1 z.2)
    (Icc 0 d.mu0 ×ˢ extensionDomain d delta)
  agrees : ∀ mu ∈ Icc 0 d.mu0, ∀ w : Phase (a+b), w ∈ closure (cylinder d.V d.r0) →
    KAM.realInclusion₂ (a+b) w ∈ extensionDomain d delta →
      P mu (KAM.realInclusion₂ (a+b) w) = (d.P mu w : ℂ)
  periodic : ∀ mu ∈ Icc 0 d.mu0, ∀ z ∈ extensionDomain d delta, ∀ k : Fin a → ℤ,
    P mu (z+KAM.realInclusion₂ (a+b) (fastShift k)) = P mu z
  bound : ∀ mu ∈ Icc 0 d.mu0, ∀ z ∈ extensionDomain d delta, ‖P mu z‖ ≤ MP
  h0holo : DifferentiableOn ℂ H0 (KAM.actionNbhd (closure d.V) delta)
  h0real : ∀ I : Fin a → ℝ, KAM.realInclusion a I ∈ KAM.actionNbhd (closure d.V) delta →
    H0 (KAM.realInclusion a I) = (d.H0 I : ℂ)
  h0bounds : ∀ I ∈ KAM.actionNbhd (closure d.V) delta,
    ‖H0 I‖ ≤ M0 ∧ ‖fderiv ℂ H0 I‖ ≤ M0 ∧ ‖fderiv ℂ (fderiv ℂ H0) I‖ ≤ M0

theorem ext (d : PGData a b) : Nonempty (PGExtension d) := sorry

def pgExtension (d : PGData a b) : PGExtension d := Classical.choice (ext d)

def pgWidth (d : PGData a b) : ℝ := (pgExtension d).delta/2

def pgOscRadius (d : PGData a b) : ℝ := min (d.r0/2) ((pgExtension d).delta/4)

def complexAverage (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ)
    (x : PGComplexPhase b) : ℂ :=
  ((2*Real.pi : ℂ)^a)⁻¹ * ∫ phi in (pi univ fun _ : Fin a => Icc (0:ℝ) (2*Real.pi)),
    (pgExtension d).P mu (assembleComplex I (KAM.realInclusion a phi) x.2 x.1)

/-- Attachment to the actual frozen normalized secular average, only on its constrained domain. -/
theorem complexAverage_real (d : PGData a b) (mu : ℝ) (hmu : mu ∈ Icc 0 d.mu0)
    (I : Fin a → ℝ) (hI : I ∈ d.V) (p q : Fin b → ℝ) (hx : ‖(p,q)‖ < pgOscRadius d) :
    complexAverage d mu (KAM.realInclusion a I) (KAM.realInclusion b q,KAM.realInclusion b p) =
      (secularAverage d.P mu I p q : ℂ) := sorry

/-- Jets are constructed from the average, not from arbitrary total boundary values. -/
def jetP0 (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ) : ℂ := complexAverage d mu I 0

def jetOmega (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ) (j : Fin b) : ℂ :=
  iteratedFDeriv ℂ 2 (complexAverage d mu I) 0 (fun _ => (0,Pi.single j 1))

def jetBeta (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ) : Matrix (Fin b) (Fin b) ℂ :=
  fun i j => if i=j then (1/3:ℂ)*iteratedFDeriv ℂ 4 (complexAverage d mu I) 0 (fun _ => (0,Pi.single i 1))
  else iteratedFDeriv ℂ 4 (complexAverage d mu I) 0
    (fun k : Fin 4 => if k.val < 2 then (0,Pi.single i 1) else (0,Pi.single j 1))

def jetPolynomial (d : PGData a b) (mu : ℝ) (J : Fin (a+b) → ℂ) : ℂ :=
  jetP0 d mu (blockFast J) + ∑ j, jetOmega d mu (blockFast J) j * blockSlow J j +
    (1/2:ℂ)*∑ i, ∑ j, jetBeta d mu (blockFast J) i j*blockSlow J i*blockSlow J j

def pgRemainder (d : PGData a b) (mu : ℝ) (I : Fin a → ℂ) (x : PGComplexPhase b) : ℂ :=
  complexAverage d mu I x - jetPolynomial d mu
    (Fin.append I (fun j => (x.1 j^2+x.2 j^2)/2))

theorem consts (d : PGData a b) : ∃ LP : ℝ, 1 ≤ LP ∧
    ∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2),
    ∀ x : PGComplexPhase b, ‖x‖ < pgOscRadius d →
      KAM.Fourier.SummableWeighted (pgWidth d)
        (KAM.torusCoeff (fun phi => (pgExtension d).P mu
          (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a phi) x.2 x.1))) ∧
      KAM.Fourier.weightedNorm (pgWidth d)
        (KAM.torusCoeff (fun phi => (pgExtension d).P mu
          (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a phi) x.2 x.1))) ≤ LP := sorry

theorem birkhoff_ext (d : PGData a b) :
    (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ d.V,
      jetP0 d mu (KAM.realInclusion a I) = (d.P0 mu I : ℂ) ∧
      (∀ j, jetOmega d mu (KAM.realInclusion a I) j = (d.Omega mu I j : ℂ)) ∧
      (∀ i j, jetBeta d mu (KAM.realInclusion a I) i j = (d.beta mu I i j : ℂ))) ∧
    (∀ mu ∈ Icc 0 d.mu0,
      DifferentiableOn ℂ (jetP0 d mu) (KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2)) ∧
      (∀ j, DifferentiableOn ℂ (fun I => jetOmega d mu I j)
        (KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2))) ∧
      (∀ i j, DifferentiableOn ℂ (fun I => jetBeta d mu I i j)
        (KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2)))) ∧
    (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2),
      ∀ k : ℕ, k ≤ 4 → iteratedFDeriv ℂ k (pgRemainder d mu I) 0 = 0) ∧
    (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ closure d.V,
      d.B ≤ ‖(jetBeta d mu (KAM.realInclusion a I)).det‖) := sorry

theorem birkhoff_ext_parameter_regularity (d : PGData a b) :
    ContinuousOn
      (fun z : ℝ × (Fin a → ℂ) => jetP0 d z.1 z.2)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V)
        ((pgExtension d).delta/2)) ∧
    (∀ j, ContinuousOn
      (fun z : ℝ × (Fin a → ℂ) => jetOmega d z.1 z.2 j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V)
        ((pgExtension d).delta/2))) ∧
    (∀ i j, ContinuousOn
      (fun z : ℝ × (Fin a → ℂ) => jetBeta d z.1 z.2 i j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V)
        ((pgExtension d).delta/2))) ∧
    (∀ mu ∈ Icc 0 d.mu0,
      ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2),
        (jetBeta d mu I).IsSymm) := by sorry

theorem uniform_remainder (d : PGData a b) : ∃ r1 CQ : ℝ,
    0 < r1 ∧ r1 ≤ pgOscRadius d ∧ 0 < CQ ∧
    ∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/4),
      ∀ x : PGComplexPhase b, ‖x‖ ≤ r1 → ‖pgRemainder d mu I x‖ ≤ CQ*‖x‖^5 := sorry

theorem lip_complex {m N : ℕ} (hN : 0 < N) {X : Set (Fin N → ℝ)} {rho A : ℝ}
    (hrho : 0 < rho) {f : (Fin N → ℂ) → Fin m → ℂ}
    (hf : DifferentiableOn ℂ f (KAM.actionNbhd X (2*rho)))
    (hb : ∀ z ∈ KAM.actionNbhd X (2*rho), ‖f z‖ ≤ A) :
    ∀ z ∈ KAM.actionNbhd X rho, ∀ z' ∈ KAM.actionNbhd X rho,
      ‖f z-f z'‖ ≤ (2*N*A/rho)*‖z-z'‖ := sorry

def complexFast (d : PGData a b) (I : Fin a → ℂ) (i : Fin a) : ℂ :=
  fderiv ℂ (pgExtension d).H0 I (Pi.single i 1)

theorem bilip (d : PGData a b) : ∃ rho c0 M0 : ℝ,
    0 < rho ∧ rho < (pgExtension d).delta/16 ∧ 0 < c0 ∧ 1 ≤ M0 ∧
    (∀ z ∈ KAM.actionNbhd (closure d.V) rho, ∀ z' ∈ KAM.actionNbhd (closure d.V) rho,
      c0*‖z-z'‖ ≤ ‖complexFast d z-complexFast d z'‖) ∧
    (∀ z ∈ KAM.actionNbhd (closure d.V) (2*rho), ‖fderiv ℂ (complexFast d) z‖ ≤ M0) := sorry

def dioConstant (d : PGData a b) (tau : ℝ) : ℝ :=
  2*(pgInverseL d)^a*latticeS (a+b) tau*(2*pgInverseR d)^(a-1)

theorem dio_one (d : PGData a b) {tau : ℝ} (ht : (a+b:ℕ) < tau) :
    0 < dioConstant d tau ∧ ∀ gamma : ℝ, 0 < gamma →
      volume {I ∈ d.V | ¬ KAM.IsDiophantine gamma tau
        (fastFrequency d.H0 I)} ≤
          ENNReal.ofReal (dioConstant d tau*gamma) := by sorry

/-- Numeric carriers selected before r and mu. The specification is produced below. -/
structure PGAnalytic where
  rho : ℝ
  c0 : ℝ
  M0 : ℝ
  AN : ℝ
  LN : ℝ
  LB : ℝ
  muStar : ℝ
  LP : ℝ
  CQ : ℝ
  r1 : ℝ
  Cdio : ℝ

def analyticDomain (d : PGData a b) (p : PGAnalytic) : Set (Fin (a+b) → ℂ) :=
  {J | blockFast J ∈ KAM.actionNbhd (closure d.V) p.rho ∧ ‖blockSlow J‖ < 1}

def analyticBoundDomain (d : PGData a b) (p : PGAnalytic) :
    Set (Fin (a+b) → ℂ) :=
  {J | blockFast J ∈ KAM.actionNbhd (closure d.V) p.rho ∧
    ‖blockSlow J‖ < 2}


def complexIntegrable (d : PGData a b) (mu : ℝ) (J : Fin (a+b) → ℂ) : ℂ :=
  (pgExtension d).H0 (blockFast J)+mu*jetPolynomial d mu J

def complexFrequency (d : PGData a b) (mu : ℝ) (J : Fin (a+b) → ℂ) (i : Fin (a+b)) : ℂ :=
  fderiv ℂ (complexIntegrable d mu) J (Pi.single i 1)

/-- All clauses are proved from d. None is an assumed inverse or assumed KAM family. -/
def PGAnalyticSpec (d : PGData a b) (p : PGAnalytic) : Prop :=
  0 < p.rho ∧ p.rho < (pgExtension d).delta/16 ∧ 0 < p.c0 ∧
  1 ≤ p.M0 ∧ 1 ≤ p.AN ∧ 1 ≤ p.LN ∧ 1 ≤ p.LB ∧ 0 < p.muStar ∧ p.muStar ≤ 1 ∧ p.muStar ≤ d.mu0 ∧
  1 ≤ p.LP ∧ (pgExtension d).MP * KAM.Weighted.coth ((pgExtension d).delta/4)^a ≤ p.LP ∧ 0 < p.CQ ∧ 0 < p.r1 ∧ p.r1 ≤ pgOscRadius d ∧ 0 < p.Cdio ∧
  p.muStar*p.AN ≤ p.c0/2 ∧ 4*p.muStar*p.AN^2*p.LB ≤ p.c0 ∧
  2*p.muStar*p.LN^2*p.LB < p.c0 ∧ p.LN ≤ p.AN ∧
  (∀ gamma : ℝ, 0 < gamma →
    volume {I ∈ d.V | ¬ KAM.IsDiophantine gamma ((a+b:ℕ)+1) (fastFrequency d.H0 I)} ≤
      ENNReal.ofReal (p.Cdio*gamma)) ∧
  (∀ z ∈ KAM.actionNbhd (closure d.V) p.rho, ∀ z' ∈ KAM.actionNbhd (closure d.V) p.rho,
    p.c0*‖z-z'‖ ≤ ‖complexFast d z-complexFast d z'‖) ∧
  (∀ z ∈ KAM.actionNbhd (closure d.V) (2*p.rho), ‖fderiv ℂ (complexFast d) z‖ ≤ p.M0) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) p.rho,
    ∀ I' ∈ KAM.actionNbhd (closure d.V) p.rho, ∀ xi : Fin b → ℂ, ‖xi‖ ≤ 1 →
      ‖(fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I (Pi.single i 1)) -
        (fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I' (Pi.single i 1))‖ ≤ p.LN*‖I-I'‖ ∧
      ‖(jetOmega d mu I+(jetBeta d mu I).mulVec xi) -
        (jetOmega d mu I'+(jetBeta d mu I').mulVec xi)‖ ≤ p.LN*‖I-I'‖) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) p.rho,
    ∀ xi xi' : Fin b → ℂ, ‖xi‖ ≤ 1 → ‖xi'‖ ≤ 1 →
      ‖(fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I (Pi.single i 1)) -
        (fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi')) I (Pi.single i 1))‖ ≤ p.LN*‖xi-xi'‖) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ J ∈ analyticBoundDomain d p,
    ‖jetPolynomial d mu J‖ ≤ p.AN ∧ ‖fderiv ℂ (jetPolynomial d mu) J‖ ≤ p.AN ∧
      ‖fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J‖ ≤ p.AN) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) p.rho, ∀ v : Fin b → ℂ,
    ‖v‖ ≤ p.LB*‖(jetBeta d mu I).mulVec v‖) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/4),
    ∀ x : PGComplexPhase b, ‖x‖ ≤ p.r1 → ‖pgRemainder d mu I x‖ ≤ p.CQ*‖x‖^5)

theorem freq_data (d : PGData a b) : ∃ p : PGAnalytic, PGAnalyticSpec d p := sorry

def pgAnalytic (d : PGData a b) : PGAnalytic := (freq_data d).choose

def pgCU (p : PGAnalytic) : ℝ :=
  max (p.M0+p.AN+1) (max (4*(p.AN+1)^2*p.LB/p.c0+4) (8*p.LB+4))

theorem complexFrequency_real (d : PGData a b) (mu : ℝ) (hmu : mu ∈ Icc 0 d.mu0)
    (J : Fin (a+b) → ℝ) (hJ : (blockFast J : Fin a → ℝ) ∈ d.V) :
    complexFrequency d mu (KAM.realInclusion (a+b) J) =
      KAM.realInclusion (a+b) (freq d.H0 d.P0 d.Omega d.beta mu J) := sorry

theorem freq_inj (d : PGData a b) : ∀ mu ∈ Ioc 0 (pgAnalytic d).muStar,
    InjOn (complexFrequency d mu) (analyticDomain d (pgAnalytic d)) ∧
    ∀ J ∈ analyticDomain d (pgAnalytic d),
      ∃ T : (Fin (a+b) → ℂ) ≃L[ℂ] (Fin (a+b) → ℂ),
        (∀ v, T v = fderiv ℂ (complexFrequency d mu) J v) ∧
        ‖T.toContinuousLinearMap‖ ≤ pgCU (pgAnalytic d) ∧
        ‖T.symm.toContinuousLinearMap‖ ≤ pgCU (pgAnalytic d)/mu ∧
        (∀ v, ‖blockFast (T.symm v)‖ ≤ pgCU (pgAnalytic d)*‖v‖) ∧
        (∀ v, ‖blockSlow (T v)‖ ≤ pgCU (pgAnalytic d)*mu*‖v‖) := sorry

/-! Exact P1 definitions copied solely for a self-contained untracked elaboration probe.
Implementation imports Hamiltonian/Chart, Hamiltonian/Diophantine, Hamiltonian/TorusUnion. -/
def IsChart (c : ℝ) (Ψ : Phase n → Phase n) (O : Set (Phase n)) : Prop :=
  AnalyticOnNhd ℝ Ψ O ∧ KAM.Kepler.IsSymplecticOn c Ψ O

def fullShift (k : Fin n → ℤ) : Phase n := (fun i => 2*Real.pi*(k i:ℝ),0)

def angleScale (c : ℝ) (z : Phase n) : Phase n := (c • z.1,z.2)

theorem disc_measure_chart :
    IsChart 1 (oscillatorPolar (a:=a) (b:=b)) {z : Phase (a+b) | ∀ j : Fin b, 0 < blockSlow z.2 j} ∧
    InjOn (polarCellMap (a:=a) (b:=b))
      {z : Phase (a+b) | (∀ j : Fin b, 0 < blockSlow z.2 j) ∧ z.1 ∈ unitCube (a+b)} ∧
    (∀ z : Phase (a+b), (∀ j : Fin b, 0 < blockSlow z.2 j) →
      |(fderiv ℝ (oscillatorPolar (a:=a) (b:=b)) z).det| = 1) ∧
    (∀ z z' : Phase (a+b), (∀ j : Fin b, 0 < blockSlow z.2 j) →
      (∀ j : Fin b, 0 < blockSlow z'.2 j) → ∀ k : Fin a → ℤ,
      oscillatorPolar z' = oscillatorPolar z + fastShift k →
        ∃ m : Fin (a+b) → ℤ, z'=z+fullShift m) := sorry

theorem resonanceBad_eq (F : (Fin (a+b) → ℝ) → Fin (a+b) → ℝ)
    (D : Set (Fin (a+b) → ℝ)) (alpha1 alpha2 tau : ℝ) :
    resonanceBad F D alpha1 alpha2 tau = {J ∈ D | F J ∉ twoScaleDiophantine a b alpha1 alpha2 tau} := sorry

theorem local_real_complexification {N : ℕ} {f : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hf : AnalyticAt ℝ f x) : ∃ (rho M : ℝ) (F : (Fin N → ℂ) → ℂ),
      0 < rho ∧ 0 < M ∧ DifferentiableOn ℂ F (ball (KAM.realInclusion N x) rho) ∧
      (∀ y ∈ ball x rho, F (KAM.realInclusion N y) = (f y : ℂ)) ∧
      (∀ z ∈ ball (KAM.realInclusion N x) rho, ‖F z‖ ≤ M) := sorry

/-- Explicit classical input for ext-loc, including the uniform bound. -/
theorem compact_real_complexification {N : ℕ} {X : Set (Fin N → ℝ)}
    (hX : IsCompact X) {f : (Fin N → ℝ) → ℝ} (hf : AnalyticOnNhd ℝ f X) :
    ∃ (rho M : ℝ) (F : (Fin N → ℂ) → ℂ), 0 < rho ∧ 0 < M ∧
      DifferentiableOn ℂ F (KAM.actionNbhd X rho) ∧
      (∀ x : Fin N → ℝ, KAM.realInclusion N x ∈ KAM.actionNbhd X rho →
        F (KAM.realInclusion N x) = (f x:ℂ)) ∧
      (∀ z ∈ KAM.actionNbhd X rho, ‖F z‖ ≤ M) := sorry

/-- Real-slice identity in several variables: not the one-variable theorem with a renamed domain. -/
theorem real_slice_identity {N : ℕ} {U : Set (Fin N → ℂ)} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f g : (Fin N → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {V : Set (Fin N → ℝ)} (hV : IsOpen V) (hVne : V.Nonempty)
    (hVU : KAM.realInclusion N '' V ⊆ U)
    (heq : ∀ x ∈ V, f (KAM.realInclusion N x) = g (KAM.realInclusion N x)) : EqOn f g U := sorry

theorem connected_complex_tube {N : ℕ} {X : Set (Fin N → ℝ)}
    (hX : IsConnected X) {rho : ℝ} (hrho : 0 < rho) :
    IsConnected (KAM.actionNbhd X rho) := sorry

/-- o(norm x^4) fixes all analytic Taylor coefficients through degree four. -/
theorem fourth_jet_unique {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (ho : ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ x, ‖x‖ < delta → |f x| ≤ eps*‖x‖^4) :
    ∀ k : ℕ, k ≤ 4 → iteratedFDeriv ℝ k f 0 = 0 := sorry

/-- Higher-order Schwarz, used after restricting to a complex line. -/
theorem schwarz_order_five {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hbound : ∀ z ∈ ball (0:ℂ) R, ‖g z‖ ≤ M)
    (hjet : ∀ k : ℕ, k ≤ 4 → iteratedDeriv k g 0 = 0) :
    ∀ z ∈ ball (0:ℂ) R, ‖g z‖ ≤ M/R^5*‖z‖^5 := sorry

/-- Identifies the missing row-wise operator bounds after Schur complement inversion. -/
theorem schur_inverse_blocks {A : Matrix (Fin a) (Fin a) ℂ}
    {B : Matrix (Fin a) (Fin b) ℂ} {C : Matrix (Fin b) (Fin a) ℂ}
    {D : Matrix (Fin b) (Fin b) ℂ} (hA : IsUnit A.det) (hS : IsUnit (D-C*A⁻¹*B).det) :
    (Matrix.fromBlocks A B C D)⁻¹ =
      Matrix.fromBlocks (A⁻¹+A⁻¹*B*(D-C*A⁻¹*B)⁻¹*C*A⁻¹)
        (-A⁻¹*B*(D-C*A⁻¹*B)⁻¹) (-(D-C*A⁻¹*B)⁻¹*C*A⁻¹) ((D-C*A⁻¹*B)⁻¹) := sorry

/-- Real target dimension and finite measure; continuity uses atomless coordinate slices. -/
theorem finite_measure_coordinate_cut {N : ℕ} (j : Fin N) (nu : Measure (Fin N → ℝ))
    [IsFiniteMeasure nu] (hnull : ∀ s : ℝ, nu {x | x j=s} = 0) :
    Continuous (fun s : ℝ => (nu {x | x j ≤ s}).toReal) := sorry

/-- Tonelli in a product-coordinate form; any coordinate permutation reduces to this. -/
theorem section_measure_le_of_pairwise_dist {E : Set ℝ} {delta : ℝ}
    (hd : 0 ≤ delta)
    (hE : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ delta) :
    volume E ≤ ENNReal.ofReal delta := by sorry

theorem ext_tonelli {m : ℕ} {R : Set ((Fin m → ℝ) × ℝ)} (hR : MeasurableSet R)
    {P : Set (Fin m → ℝ)} (hP : MeasurableSet P) (hsub : R ⊆ P ×ˢ univ)
    {delta : ℝ} (hd : 0 ≤ delta)
    (hsections : ∀ x : Fin m → ℝ, volume {t : ℝ | (x,t) ∈ R} ≤ ENNReal.ofReal delta) :
    volume R ≤ ENNReal.ofReal delta * volume P := sorry

theorem log_power_dominated {p A : ℝ} (hp : 0 < p) (hA : 0 < A) :
    ∃ K : ℝ, 1 < K ∧ A*(Real.log K)^p < K^2 := sorry

/-- Stable numeric constant C1, before r and mu; period factors included. -/
def kam_c1 (d : PGData a b) : ℝ :=
  max 1 (max (2*Real.pi*pgCU (pgAnalytic d))
    ((2^5*(pgAnalytic d).CQ+2*(pgAnalytic d).LP)*
      KAM.Weighted.coth (pgWidth d/24)^(a+b)/(2*Real.pi)))

structure PGScales where
  k0 : ℝ
  k1 : ℝ
  G : ℝ

def pgTau (a b : ℕ) : ℝ := (a+b:ℕ)+1

def pgK0 (d : PGData a b) (s : PGScales) : ℝ :=
  6/(pgWidth d/60)*max 1 (Real.log (s.k0^2/(kam_c1 d)^4))

def pgChat (a b : ℕ) : ℝ := max (2^13*(a+b:ℕ)) (24^(pgTau a b+1)/3)

def PGScaleSpec (d : PGData a b) (s : PGScales) : Prop :=
  (kam_c1 d)^2 ≤ s.k0 ∧ 0 < s.k1 ∧
  9*pgChat a b*(kam_c1 d)^4*(pgK0 d s)^(2*pgTau a b+2) < s.k0^2 ∧
  4*pgChat a b*(kam_c1 d)^2 < s.k1^2 ∧
  max (2*(pgAnalytic d).M0*s.k1)
    (max (Real.sqrt (2^14*(1+b)*(pgAnalytic d).M0))
      (Real.sqrt (1600*(1+b)*(pgAnalytic d).M0/pgWidth d))) ≤ s.G

theorem kam_cond (d : PGData a b) : ∃ s : PGScales, PGScaleSpec d s := sorry

def pgScales (d : PGData a b) : PGScales := (kam_cond d).choose

/-- All entries are explicit functions of r,mu and data-only chosen constants. -/
structure PGParameters where
  Kbar : ℝ
  t : ℝ
  l1 : ℝ
  l2 : ℝ
  l2top : ℝ
  ell : ℝ
  rho : ℝ
  gammaBar : ℝ
  rhoBar : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  rhoHat : ℝ
  Ehat : ℝ
  rK : ℝ

def params (d : PGData a b) (r mu : ℝ) : PGParameters :=
  let s := pgScales d
  let p := pgAnalytic d
  let Kbar := 30/pgWidth d*Real.log (1/r)
  let l1 := s.k1*r^(5/2:ℝ)
  let gammaBar := s.G*max (Real.sqrt (p.LP*mu)*Kbar^(pgTau a b+1/2)*r^(-5/2:ℝ))
    (r^(5/2:ℝ)*Kbar^(pgTau a b+1))
  let rhoHat := min (s.k0*r^(5/2:ℝ)/(3*kam_c1 d*(pgK0 d s)^(pgTau a b+1))) (l1/2)
  let Ehat := (kam_c1 d)^2*r^5/rhoHat^2
  ⟨Kbar,Real.sqrt r,l1,r^2/2,r^2/2-2*l1,r^2/2-3*l1,l1/2,gammaBar,
    gammaBar/(2*p.M0*Kbar^(pgTau a b+1)),s.k0*r^(5/2:ℝ),mu*s.k0*r^(5/2:ℝ),rhoHat,Ehat,32*Ehat*rhoHat⟩

def checkedCore (d : PGData a b) (r mu : ℝ) : Set (Fin a → ℝ) :=
  innerCore d.V (Real.sqrt r) ∩ {I | KAM.IsDiophantine (params d r mu).gammaBar (pgTau a b) (fastFrequency d.H0 I)}

def pgActionDomain (d : PGData a b) (r mu : ℝ) : Set (Fin (a+b) → ℝ) :=
  joinedActions (checkedCore d r mu) (actionShell b (params d r mu).l1 (params d r mu).l2top)

/- Owner: KAM/Planetary/PGAssembly/Parameters.lean; after pgActionDomain. -/
def pgD0 (d : PGData a b) (r mu : ℝ) : Set (Fin (a+b) → ℝ) :=
  {J ∈ pgActionDomain d r mu | ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) ∈
    twoScaleDiophantine a b (params d r mu).gamma1 (params d r mu).gamma2 (pgTau a b)}

def admissible (d : PGData a b) (R r mu : ℝ) : Prop :=
  0 < r ∧ r < R ∧ 0 < mu ∧ mu < d.mu0 ∧ mu < r^6/(Real.log (1/r))^(2*pgTau a b+2)

/-- Data-only threshold, selected before r,mu; output includes all numerical KAM conditions. -/
def pgCgamma (d : PGData a b) : ℝ :=
  (pgScales d).G*(30/pgWidth d)^(pgTau a b+1)

theorem rstar (d : PGData a b) : ∃ R : ℝ, 0 < R ∧ R < d.r0 ∧ R < Real.exp (-(pgTau a b+1)) ∧ R < Real.exp (-1) ∧ R < 1 ∧
    R^6 ≤ (2*(1+2*b*(pgAnalytic d).LN*(pgAnalytic d).LB)*a*(pgAnalytic d).LN*pgInverseL d)⁻¹ ∧
    (pgAnalytic d).LP ≤ Real.log (1/R) ∧ R^2*(Real.log (1/R))^(pgTau a b+1) ≤ 1 ∧
    Real.sqrt R < pgBoundaryD d ∧
    pgBoundaryA d*Real.sqrt R ≤ (volume d.V).toReal/2 ∧
    (pgAnalytic d).Cdio*pgCgamma d*Real.sqrt R ≤ (volume d.V).toReal/4 ∧
    ∀ r mu : ℝ, admissible d R r mu →
      r < (pgAnalytic d).r1/2 ∧ r < pgOscRadius d/4 ∧
      (params d r mu).Kbar*r^5 ≤ 1 ∧
      (params d r mu).rhoBar*pgWidth d ≤ (pgOscRadius d)^2 ∧
      (params d r mu).rK + 12*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
        (pgWidth d*(params d r mu).gammaBar) < Real.sqrt r ∧
      Real.sqrt 2 * (18*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
        (pgOscRadius d*(params d r mu).gammaBar)) ≤ (pgScales d).k1*r^(3/2:ℝ) ∧
      0 < (params d r mu).l1 ∧ (params d r mu).ell ≥ r^2/4 ∧
      (params d r mu).rhoBar ≤ (pgAnalytic d).rho ∧
      (params d r mu).l1 ≤ (params d r mu).rhoBar ∧
      mu < (pgAnalytic d).muStar ∧ pgChat a b*(params d r mu).Ehat < 1 ∧
      (params d r mu).rK < min (Real.sqrt r) ((params d r mu).l1) ∧
      (params d r mu).rK < (params d r mu).rhoBar/2 ∧
      ENNReal.ofReal (1/2)*volume d.V ≤ volume (innerCore d.V (Real.sqrt r)) ∧
      ENNReal.ofReal (1/4)*volume d.V ≤ volume (checkedCore d r mu) := sorry

def pgRstar (d : PGData a b) : ℝ := (rstar d).choose

theorem param_facts (d : PGData a b) : 0 < pgCgamma d ∧
    ∀ r mu : ℝ, admissible d (pgRstar d) r mu →
      (pgAnalytic d).LP*mu ≤ r^6*(Real.log (1/r))^(-(2*pgTau a b+1)) ∧
      6 ≤ (params d r mu).Kbar*pgWidth d ∧
      (params d r mu).gammaBar ≤ pgCgamma d*Real.sqrt r ∧
      0 < volume (pgActionDomain d r mu) ∧ volume (pgActionDomain d r mu) < ⊤ := sorry

theorem r_k (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    (params d r mu).rK < (params d r mu).rhoHat/(256*(a+b:ℕ)) ∧
    2*(params d r mu).rK/(params d r mu).ell ≤ (pgScales d).k1/(64*(a+b:ℕ))*Real.sqrt r ∧
    (1+2*(params d r mu).rK/(params d r mu).ell)^b < 2 := sorry

structure PGAveraging (n : ℕ) where
  Psi : PGComplexPhase n → PGComplexPhase n
  remainder : PGComplexPhase n → ℂ

def averagingDomain (d : PGData a b) (r mu : ℝ) : Set (PGComplexPhase (a+b)) :=
  {z | blockFast z.2 ∈ KAM.actionNbhd (checkedCore d r mu) ((params d r mu).rhoBar/2) ∧
    blockFast z.1 ∈ KAM.complexStrip a (pgWidth d/6) ∧ ‖(blockSlow z.2,blockSlow z.1)‖ < pgOscRadius d/2}

def realAverageMap (A : PGAveraging n) (z : Phase n) : Phase n :=
  ((fun i => (A.Psi (KAM.realInclusion₂ n z)).1 i |>.re),
    (fun i => (A.Psi (KAM.realInclusion₂ n z)).2 i |>.re))

def AveragingSpec (d : PGData a b) (r mu : ℝ) (A : PGAveraging (a+b)) : Prop :=
  DifferentiableOn ℂ A.Psi (averagingDomain d r mu) ∧
  InjOn A.Psi (averagingDomain d r mu) ∧
  MapsTo A.Psi (averagingDomain d r mu) (extensionDomain d (pgExtension d).delta) ∧
  (∀ z ∈ averagingDomain d r mu,
    (pgExtension d).H0 (blockFast (A.Psi z).2)+mu*(pgExtension d).P mu (A.Psi z) =
      complexIntegrable d mu (Fin.append (blockFast z.2)
        (fun j => ((blockSlow z.1 j)^2+(blockSlow z.2 j)^2)/2)) +
      mu*pgRemainder d mu (blockFast z.2) (blockSlow z.1,blockSlow z.2)+A.remainder z) ∧
  DifferentiableOn ℂ A.remainder (averagingDomain d r mu) ∧
  (∀ z ∈ averagingDomain d r mu, ‖A.remainder z‖ ≤ 2*(pgAnalytic d).LP*mu*r^5) ∧
  (∀ I ∈ KAM.actionNbhd (checkedCore d r mu) ((params d r mu).rhoBar/2),
    ∀ x : PGComplexPhase b, ‖x‖ < pgOscRadius d/2 →
      KAM.Fourier.SummableWeighted (pgWidth d/6)
        (KAM.torusCoeff (fun theta => A.remainder
          (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a theta) x.2 x.1))) ∧
      KAM.Fourier.weightedNorm (pgWidth d/6)
        (KAM.torusCoeff (fun theta => A.remainder
          (assembleComplex I ((2*Real.pi:ℂ) • KAM.realInclusion a theta) x.2 x.1))) ≤
        2*(pgAnalytic d).LP*mu*r^5) ∧
  (∀ z ∈ averagingDomain d r mu, ∀ k : Fin a → ℤ,
    A.Psi (z+KAM.realInclusion₂ (a+b) (fastShift k)) =
      A.Psi z+KAM.realInclusion₂ (a+b) (fastShift k)) ∧
  (∀ z : Phase (a+b), KAM.realInclusion₂ (a+b) z ∈ averagingDomain d r mu →
    A.Psi (KAM.realInclusion₂ (a+b) z) = KAM.realInclusion₂ (a+b) (realAverageMap A z)) ∧
  IsChart 1 (realAverageMap A) ((KAM.realInclusion₂ (a+b)) ⁻¹' averagingDomain d r mu) ∧
  (∀ z : Phase (a+b), KAM.realInclusion₂ (a+b) z ∈ averagingDomain d r mu →
    ‖blockFast (realAverageMap A z).2-blockFast z.2‖ ≤
      12*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/(pgWidth d*(params d r mu).gammaBar) ∧
    ‖(blockSlow (realAverageMap A z).2-blockSlow z.2,blockSlow (realAverageMap A z).1-blockSlow z.1)‖ ≤
      18*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/(pgOscRadius d*(params d r mu).gammaBar))

/-- Mixed fast-angle/oscillator normalization, conformally symplectic with factor 2*pi. -/
def pgOscNormalize (z : CPhase (a+b)) : CPhase (a+b) :=
  (Fin.append ((2*Real.pi:ℂ) • blockFast z.1)
    ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.1),
   Fin.append (blockFast z.2) ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.2))
def pgOscUnnormalize (z : CPhase (a+b)) : CPhase (a+b) :=
  (Fin.append ((2*Real.pi:ℂ)⁻¹ • blockFast z.1)
    ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • blockSlow z.1),
   Fin.append (blockFast z.2) ((Real.sqrt (2*Real.pi):ℂ)⁻¹ • blockSlow z.2))
def pgOscP (d : PGData a b) (mu : ℝ) (z : CPhase (a+b)) : ℂ :=
  (pgExtension d).P mu (pgOscNormalize z)/(pgAnalytic d).LP
def pgOscH (d : PGData a b) (I : Fin a → ℂ) : ℂ := (pgExtension d).H0 I/(2*Real.pi)
def pgOscE (d : PGData a b) (mu : ℝ) : ℝ := (pgAnalytic d).LP*mu/(2*Real.pi)
def pgOscEpsilon (d : PGData a b) : ℝ := pgOscRadius d/Real.sqrt (2*Real.pi)
def pgOscWidth (d : PGData a b) : ℝ := pgWidth d/(2*Real.pi)
/-- Cutoff divisor after neighbourhood loss and conformal Hamiltonian scaling. -/
def pgOscAlpha (d : PGData a b) (r mu : ℝ) : ℝ :=
  (params d r mu).gammaBar / (4*Real.pi*(params d r mu).Kbar^(pgTau a b))
theorem pg_osc_hyp (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    OscHyp (checkedCore d r mu) (params d r mu).rhoBar (pgOscEpsilon d) (pgOscEpsilon d)
      0 (pgOscWidth d) (15/(Real.pi*pgOscWidth d)*Real.log (1/r))
      (pgOscAlpha d r mu) (pgOscE d mu)
      (pgOscH d) (pgOscE d mu • pgOscP d mu) := sorry
theorem pg_osc_bound (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    oscBound (checkedCore d r mu) (params d r mu).rhoBar (pgOscEpsilon d) (pgOscEpsilon d)
      (pgOscWidth d) (pgOscP d mu) 1 := sorry
theorem pg_osc_positive (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    (0 < r ∧ r < Real.exp (-1/5)) ∧ 0 < pgOscE d mu := sorry
theorem pg_osc_zero (d : PGData a b) (mu : ℝ) (hmu : mu ∈ Icc 0 d.mu0)
    (z : CPhase (a+b))
    (hz : z ∈ oscDom (closure d.V) ((pgExtension d).delta/2)
      (pgOscEpsilon d) (pgOscEpsilon d) (pgOscWidth d)) :
    KAM.Weighted.coeff (oscFunction (pgOscP d mu)) (oscPack z).2 0 =
      complexAverage d mu (blockFast z.2)
        ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.1,
         (Real.sqrt (2*Real.pi):ℂ) • blockSlow z.2)/(pgAnalytic d).LP := sorry
theorem pg_osc_normalization :
    (∀ z : CPhase (a+b), pgOscUnnormalize (pgOscNormalize z) = z ∧
      pgOscNormalize (pgOscUnnormalize z) = z) ∧
    (∀ z u v : CPhase (a+b),
      KAM.Canonical.symplFormC (fderiv ℂ pgOscNormalize z u) (fderiv ℂ pgOscNormalize z v) =
        (2*Real.pi:ℂ)*KAM.Canonical.symplFormC u v) := sorry
theorem pg_osc_domain (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    pgOscNormalize '' oscDom (checkedCore d r mu) ((params d r mu).rhoBar/2)
      (pgOscEpsilon d/2) (pgOscEpsilon d/2) (pgOscWidth d/6) = averagingDomain d r mu := sorry

/- Exact upstream application checked without introducing a proof body. -/
#check fun (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) =>
  averaged_remainder (pg_osc_positive d r mu h).1 (pg_osc_positive d r mu h).2
    (pg_osc_hyp d r mu h) (pg_osc_bound d r mu h)

theorem avg (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    ∃ A : PGAveraging (a+b), AveragingSpec d r mu A := sorry

def pgAvg (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) : PGAveraging (a+b) :=
  (avg d r mu h).choose

def phi (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) : Phase (a+b) → Phase (a+b) :=
  realAverageMap (pgAvg d r mu h) ∘ oscillatorPolar

def phiDomain (d : PGData a b) (r mu : ℝ) : Set (Phase (a+b)) :=
  {z | KAM.realInclusion a (blockFast z.2) ∈ KAM.actionNbhd (checkedCore d r mu) ((params d r mu).rhoBar/2) ∧
    blockSlow z.2 ∈ actionShell b ((params d r mu).l1/2) (2*(params d r mu).l2)}

theorem phi_chart (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    IsOpen (phiDomain d r mu) ∧ IsChart 1 (phi d r mu h) (phiDomain d r mu) ∧
    (∀ z ∈ phiDomain d r mu, ∀ k : Fin (a+b) → ℤ, z+fullShift k ∈ phiDomain d r mu ∧
      phi d r mu h (z+fullShift k) = phi d r mu h z+fastShift (blockFast k)) ∧
    (∀ z ∈ phiDomain d r mu, ∀ z' ∈ phiDomain d r mu, ∀ k : Fin a → ℤ,
      phi d r mu h z' = phi d r mu h z+fastShift k → ∃ m : Fin (a+b) → ℤ, z'=z+fullShift m) := sorry

def oscillatorPolarComplex (z : PGComplexPhase (a+b)) : PGComplexPhase (a+b) :=
  assembleComplex (blockFast z.2) (blockFast z.1)
    (fun j => (2*blockSlow z.2 j)^(1/2:ℂ)*Complex.cos (blockSlow z.1 j))
    (fun j => (2*blockSlow z.2 j)^(1/2:ℂ)*Complex.sin (blockSlow z.1 j))

theorem oscillatorPolarComplex_real (z : Phase (a+b))
    (hz : ∀ j : Fin b, 0 < blockSlow z.2 j) :
    oscillatorPolarComplex (KAM.realInclusion₂ (a+b) z) =
      KAM.realInclusion₂ (a+b) (oscillatorPolar z) := sorry

def kamH (d : PGData a b) (mu : ℝ) (J : Fin (a+b) → ℂ) : ℂ :=
  complexIntegrable d mu J/(2*Real.pi)

def kamF (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (z : PGComplexPhase (a+b)) : ℂ :=
  let w := (pgAvg d r mu h).Psi (oscillatorPolarComplex ((2*Real.pi:ℂ) • z.1,z.2))
  ((pgExtension d).H0 (blockFast w.2)+mu*(pgExtension d).P mu w)/(2*Real.pi)-kamH d mu z.2

/-- Local estimates used to prove pg_kam_hyp for the exact delivered P3 record. -/
theorem kam_hyp (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    KAM.Weighted.InClass (KAM.realInclusion (a+b) '' pgActionDomain d r mu)
      (params d r mu).rho (pgWidth d/(24*Real.pi)) (kamF d r mu h) ∧
    KAM.Weighted.WBound (KAM.realInclusion (a+b) '' pgActionDomain d r mu)
      (params d r mu).rho (pgWidth d/(24*Real.pi)) (kamF d r mu h) (kam_c1 d*mu*r^5) ∧
    DifferentiableOn ℂ (kamH d mu) (KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) ∧
    InjOn (fun J i => fderiv ℂ (kamH d mu) J (Pi.single i 1))
      (KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) ∧
    (∀ z : Phase (a+b), z.2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rho →
      (kamH d mu (KAM.realInclusion (a+b) z.2)).im = 0 ∧
        (kamF d r mu h (KAM.realInclusion₂ (a+b) z)).im = 0) ∧
    ∀ J ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho,
      ∃ T : (Fin (a+b) → ℂ) ≃L[ℂ] (Fin (a+b) → ℂ),
        (∀ v i, T v i = fderiv ℂ (fun J i => fderiv ℂ (kamH d mu) J (Pi.single i 1)) J v i) ∧
        ‖T.toContinuousLinearMap‖ ≤ kam_c1 d ∧
        ‖T.symm.toContinuousLinearMap‖ ≤ kam_c1 d/mu ∧
        (∀ v, ‖blockSlow (T v)‖ ≤ kam_c1 d*mu*‖v‖) ∧
        (∀ v, ‖blockFast (T.symm v)‖ ≤ kam_c1 d*‖v‖) := sorry

theorem location (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (z : Phase (a+b)) (hz : z.2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rK) :
    angleScale (2*Real.pi) z ∈ phiDomain d r mu ∧
    phi d r mu h (angleScale (2*Real.pi) z) ∈ cylinder d.V r := sorry

/-- Exact P3 data; L is initialL, with a separate equality to C1/mu. -/
def pgKamScale (d : PGData a b) (r mu : ℝ) : ScaleData :=
  let C := kam_c1 d
  ⟨pgTau a b,(params d r mu).gamma1,(params d r mu).gamma2,
    pgWidth d/60,(params d r mu).rho,C*mu*r^5,C,C*mu,C/mu,C,C/mu,
    initialL C (C*mu) (C/mu)⟩
theorem pg_kam_hyp (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    KamHyp (pgActionDomain d r mu) (pgWidth d/15) (pgKamScale d r mu)
      (kamH d mu) (kamF d r mu h) := sorry
theorem pg_kam_dictionary (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    (pgKamScale d r mu).L = kam_c1 d/mu ∧
    rhoHat (pgKamScale d r mu) = (params d r mu).rhoHat ∧
    eHat (pgKamScale d r mu) = (params d r mu).Ehat ∧
    dioBase (pgActionDomain d r mu) (kamH d mu) (pgKamScale d r mu) = pgD0 d r mu := sorry
#check fun (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) =>
  two_scale_kam (pg_kam_hyp d r mu h) (Eq.refl (pgKamScale d r mu).L)

/-- Parameter actions J0; raw output is in frozen angle/action order. -/
structure PGFamily (n : ℕ) where
  raw : (Fin n → ℝ) → (Fin n → ℝ) → Phase n

def physicalTorus (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (F : PGFamily (a+b)) (J : Fin (a+b) → ℝ) : (Fin (a+b) → ℝ) → Phase (a+b) :=
  phi d r mu h ∘ angleScale (2*Real.pi) ∘ F.raw J

def PGFamilySpec (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (F : PGFamily (a+b)) : Prop :=
  IsSigmaCompact (pgD0 d r mu) ∧
  (∃ L : ℝ, 0 < L ∧ ∀ z ∈ pgD0 d r mu ×ˢ unitCube (a+b),
    ∀ z' ∈ pgD0 d r mu ×ˢ unitCube (a+b),
      ‖F.raw z.1 z.2-F.raw z'.1 z'.2‖ ≤ L*‖z-z'‖) ∧
  (∀ J ∈ pgD0 d r mu, ∀ theta, ∀ k : Fin (a+b) → ℤ,
    F.raw J (theta+fun i => (k i:ℝ)) = F.raw J theta+((fun i => (k i:ℝ)),0)) ∧
  (∀ J ∈ pgD0 d r mu, ∀ J' ∈ pgD0 d r mu, ∀ theta theta',
    physicalTorus d r mu h F J theta = physicalTorus d r mu h F J' theta' → J=J') ∧
  (∀ J ∈ pgD0 d r mu, ∀ theta,
    (F.raw J theta).2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rK) ∧
  (volume (({z : Phase (a+b) | z.2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rK ∧
      z.1 ∈ unitCube (a+b)}) \ (⋃ J ∈ pgD0 d r mu, range (F.raw J))) ≤
    ENNReal.ofReal (1+(1+2^(a+b))*(1+(4/3:ℝ)^(a+b))) *
      (volume (pgActionDomain d r mu \ pgD0 d r mu) +
        volume (realNbhd (pgActionDomain d r mu) (params d r mu).rK \ pgActionDomain d r mu))) ∧
  (∀ J ∈ pgD0 d r mu,
    IsCylinderTorus (degenerateHamiltonian d.H0 d.P mu) (cylinder d.V r)
      ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) (physicalTorus d r mu h F J))

/-- Assembly from the single joint two_scale_kam output, via P1 cyl_pipeline. -/
theorem torus_conv (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    ∃ F : PGFamily (a+b), PGFamilySpec d r mu h F := sorry

def pgFamily (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) : PGFamily (a+b) :=
  (torus_conv d r mu h).choose

def kset (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (B : Set (Fin (a+b) → ℝ)) : Set (Phase (a+b)) :=
  ⋃ J ∈ B, range (physicalTorus d r mu h (pgFamily d r mu h) J)

def rawUnion (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (B : Set (Fin (a+b) → ℝ)) : Set (Phase (a+b)) :=
  ⋃ J ∈ B, range ((pgFamily d r mu h).raw J)

def outputRepresentative (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (B : Set (Fin (a+b) → ℝ)) : Set (Phase (a+b)) :=
  rawUnion d r mu h B ∩ {z | z.1 ∈ unitCube (a+b)}

theorem cell_transfer (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    {B : Set (Fin (a+b) → ℝ)} (hB : IsSigmaCompact B) (hsub : B ⊆ pgD0 d r mu) :
    IsSigmaCompact (outputRepresentative d r mu h B) ∧ MeasurableSet (kset d r mu h B) ∧
    kset d r mu h B ⊆ cylinder d.V r ∧
    volume (kset d r mu h B ∩ cylinderCell d.V r) =
      ENNReal.ofReal ((2*Real.pi)^(a+b))*volume (outputRepresentative d r mu h B) := sorry

def kamMeasureConstant (n : ℕ) : ℝ := 1+(1+2^n)*(1+(4/3:ℝ)^n)

def pgMeasureUpper1 (d : PGData a b) : ℝ :=
  let p := pgAnalytic d
  let t := pgTau a b
  (pgInverseL d)^(a+b)/((volume d.V).toReal/2) *
    max (4*(2*pgInverseR d)^(a-1)*latticeS (a+b) t)
      (4*b^2*p.LB*(2*pgInverseR d)^a *
        (2*3^(a+b-1)/(t+1-(a+b:ℕ))) *
        (4*p.LN*pgInverseL d)^(t+1-(a+b:ℕ)))

def pgMeasureUpper2 (d : PGData a b) : ℝ :=
  b*(pgAnalytic d).LB*latticeS b (pgTau a b+1)

def pgBudget (d : PGData a b) : ℝ :=
  4^(b+1)*2*Real.pi*(pgScales d).k0 *
    (5*pgMeasureUpper1 d+4*pgMeasureUpper2 d) +
    8*(pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)/
      (volume d.V).toReal + b*(pgScales d).k1/16

theorem budget (d : PGData a b) : 0 < pgBudget d ∧
    ∀ r mu : ℝ, ∀ h : admissible d (pgRstar d) r mu,
      volume (({z : Phase (a+b) | z.2 ∈ pgActionDomain d r mu ∧
        z.1 ∈ unitCube (a+b)}) \ rawUnion d r mu h (pgD0 d r mu)) ≤
        ENNReal.ofReal (kamMeasureConstant (a+b)*pgBudget d*Real.sqrt r)*
          volume (pgActionDomain d r mu) := by sorry

/-- Exact Closs formula of the blueprint, with data-only selected component bounds. -/
def pgLoss (d : PGData a b) : ℝ :=
  (pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)/(volume d.V).toReal +
    6*b*(pgScales d).k1 + kamMeasureConstant (a+b)*pgBudget d

theorem lower (d : PGData a b) : 0 < pgLoss d ∧ ∀ r mu : ℝ,
    ∀ h : admissible d (pgRstar d) r mu,
      ENNReal.ofReal (1-pgLoss d*Real.sqrt r)*volume (cylinderCell (b:=b) d.V r) ≤
        volume (kset d r mu h (pgD0 d r mu) ∩ cylinderCell d.V r) := sorry

def finalRadius (d : PGData a b) : ℝ := min (pgRstar d) (((2*(pgLoss d+1))⁻¹)^2)

/-- Deletes whole tori via an action-coordinate half-space; both sides remain sigma compact. -/
theorem strictness (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (hr : r < finalRadius d) : ∃ B : Set (Fin (a+b) → ℝ),
      B ⊆ pgD0 d r mu ∧ IsSigmaCompact B ∧ IsSigmaCompact (pgD0 d r mu \ B) ∧
      0 < volume (kset d r mu h (pgD0 d r mu \ B) ∩ cylinderCell d.V r) ∧
      ENNReal.ofReal (1-(pgLoss d+1/2)*Real.sqrt r)*volume (cylinderCell (b:=b) d.V r) ≤
        volume (kset d r mu h (pgD0 d r mu \ B) ∩ cylinderCell d.V r) ∧
      volume (kset d r mu h (pgD0 d r mu \ B) ∩ cylinderCell d.V r) < volume (cylinderCell (b:=b) d.V r) := sorry

theorem frequency_bounds (d : PGData a b) : ∃ Cw : ℝ, 0 < Cw ∧ ∀ r mu : ℝ,
    admissible d (pgRstar d) r mu → ∀ J ∈ pgD0 d r mu,
      ‖(blockFast ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) : Fin a → ℝ)‖ ≤ Cw ∧
      ‖(blockSlow ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) : Fin b → ℝ)‖ ≤ Cw*mu := sorry

/-- Exact frozen telescope and conclusion, with only the declaration name changed. -/
theorem main {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (V : Set (Fin a → ℝ)) (hV : IsOpen V) (hVc : IsConnected V)
    (hVb : Bornology.IsBounded V)
    (W : Set (Fin a → ℝ)) (hW : IsOpen W) (hVW : closure V ⊆ W)
    (hboundary : ∃ A d : ℝ, 0 < A ∧ 0 < d ∧
      ∀ t : ℝ, 0 < t → t < d →
        volume {I : Fin a → ℝ | ∃ J ∈ frontier V, dist I J < t} ≤
          ENNReal.ofReal (A * t))
    (r0 mu0 B : ℝ)
    (hr0 : 0 < r0) (hmu0 : 0 < mu0) (hB : 0 < B)
    (H0 : (Fin a → ℝ) → ℝ) (P : ℝ → Phase (a + b) → ℝ)
    (P0 : ℝ → (Fin a → ℝ) → ℝ)
    (Omega : ℝ → (Fin a → ℝ) → (Fin b → ℝ))
    (beta : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ)
    (hP : AnalyticOnNhd ℝ (fun z : ℝ × Phase (a + b) => P z.1 z.2)
      (Set.Icc 0 mu0 ×ˢ closure (cylinder V r0)))
    (hperiod : ∀ mu ∈ Set.Icc 0 mu0, ∀ z ∈ cylinder V r0,
      ∀ k : Fin a → ℤ, P mu (z + fastShift k) = P mu z)
    (hfreq : HasFastDiffeomorphism H0 W)
    (hBNF : HasSecularBirkhoffForm P V r0 mu0 P0 Omega beta)
    (htorsion : ∀ mu ∈ Set.Icc 0 mu0, ∀ I ∈ V, B ≤ |(beta mu I).det|)
    (hsymm : ∀ mu ∈ Set.Icc 0 mu0, ∀ I ∈ V, (beta mu I).IsSymm) :
    ∃ rStar C c : ℝ, 0 < rStar ∧ rStar < r0 ∧ rStar < 1 ∧ 0 < C ∧ 0 < c ∧
      ∀ r mu : ℝ, 0 < r → r < rStar → 0 < mu → mu < mu0 →
        mu < r ^ 6 / (Real.log (1 / r)) ^ c →
        ∃ S : Set (Phase (a + b)),
          IsCylinderKolmogorovSet (degenerateHamiltonian H0 P mu) V r mu C S ∧
          0 < volume (S ∩ cylinderCell V r) ∧
          ENNReal.ofReal (1 - C * Real.sqrt r) * volume (cylinderCell (b := b) V r) <
            volume (S ∩ cylinderCell V r) ∧
          volume (S ∩ cylinderCell V r) < volume (cylinderCell (b := b) V r) :=
  by sorry

#print axioms KAM.Planetary.main

end KAM.Planetary
```

## Revision 4 (2026-10-28, main orchestrator; prover finding P5-EX)
**Defect.** In revision 3, `PGExtension.agrees` required `P mu (realInclusion₂ w) = d.P mu w` for EVERY real `w` with
`realInclusion₂ w ∈ extensionDomain d delta`. That set contains real points within `delta` of the box whose fast action
lies outside `closure d.V`, i.e. outside `closure (cylinder d.V d.r0)`. There `PGData` constrains nothing: `hP` is
`AnalyticOnNhd` only at points of `Icc 0 mu0 ×ˢ closure (cylinder V r0)` (with no uniformity in the unbounded fast
angle) and `hperiod` holds only on `cylinder V r0`, while `d.P` is a total function. Combined with `periodic`, the old
`agrees` forced `d.P` to be `2π`-periodic on a whole real `delta`-neighbourhood, and the prover's counterexample (add a
bump to `d.P` outside an angle-dependent neighbourhood `W0 = {dist(w, closure cyl) < 1/(1+|fast angle|)}` of the closed
cylinder) satisfies every `PGData` field while making `ext` false for every `delta > 0`.
**Amendment (minimal).** `agrees` now also assumes `w ∈ closure (cylinder d.V d.r0)` (see the structure above and
`P45Signatures.lean`). Nothing else changes. `h0real` is unaffected: `H0` is controlled on the open set of `hfreq`,
which contains `closure V` with a positive margin, and `delta` is chosen below that margin.
**Consumers checked.** `complexAverage_real` evaluates at `w = (phi, q; I, p)` with `I ∈ V` and
`‖(p, q)‖ < pgOscRadius ≤ r0/2`, a point of the cylinder; the `birkhoff_ext` identifications are on `V`. Both still
follow from the amended `agrees`.
**Source note.** blueprint-P p5-pg-assembly, Lemma `bpP:p5:ext` ("`P~ = P` at real points" of `X_delta`) and step
`ext-per` gloss the same point; record as a candidate source imprecision (not an erratum of the frozen statements).
