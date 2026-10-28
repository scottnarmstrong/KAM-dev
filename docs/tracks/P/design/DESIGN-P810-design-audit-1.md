# Independent design audit P810, audit 1

Overall verdict: **FAIL**.

Audited branch `inp-design-p810`, HEAD `38f40fd`, against `git diff inp...HEAD`. The branch diff contains only the 1417-line design document. The original signature file has SHA-256 `aa8e13ad5e4e62b40d0f12effde76ce4e643abbcb545cb7a933f666bf6241931`; its 885 lines and 78 theorem stubs are byte-identical to Appendix A. This is a design audit, not a proof audit or approval to seal an anchor.

Read the assigned brief, AGENTS.md, PLAN.md, DECISIONS.md, handoff, the three blueprint parts and graph packets, relevant downstream blueprint uses, frozen definitions and delivered chart interfaces. All three blueprint hashes match the design and the files in `/root/code/KAM-inp`. The graph inventory is exactly 55 + 42 + 61 = 158 records. A table entry allocating a proof cut does not by itself export that cut's conclusion.

The verdict follows the brief's explicit instruction to fail additional premises and weakened conclusions. No counterexample to the literal halved matrix, the lift formulas, the nondegeneracy assertion or the stability constant was found. The failures below concern the declared contracts and package imports; successful elaboration does not repair them.

## Findings and exact proposed fixes

### F1 — Major: `e_diff` assumes analytic regularity instead of finite regularity

Signature lines 564–569; blueprint `bpP:p8:e-diff`, p8 line 27; graph `P-p8.nodes.md`, record of the same name. The blueprint assumes C^k parameter dependence and jointly continuous derivatives through that finite order. The signature requires all orders of joint continuity and `ContDiffOn ℝ ⊤`. In this pinned Mathlib, `⊤ : WithTop ℕ∞` is the analytic level ω, not the smooth level ∞: see `Mathlib/Analysis/Calculus/ContDiff/Defs.lean:90,118–132` and the independently checked `ContDiffAt.analyticAt`. This is an unlisted extra premise. Holomorphic applications can supply it, but that does not preserve the advertised general external contract. Replace the theorem by:

```lean
theorem e_diff {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec n → Vec d → ℝ} (k : ℕ)
    (hCont : ∀ j : ℕ, j ≤ k → ContinuousOn
      (fun z : Vec n × Vec d => iteratedFDeriv ℝ j (f z.1) z.2)
      (cell n ×ˢ U))
    (hSmooth : ∀ t ∈ cell n, ContDiffOn ℝ k (f t) U)
    {x : Vec d} (hx : x ∈ U) :
    iteratedFDeriv ℝ k (fun y => ∫ t in cell n, f t y) x =
      ∫ t in cell n, iteratedFDeriv ℝ k (f t) x := by
  sorry
```

The corrected finite-order theorem can be instantiated at each j ≤ k to obtain the entire source derivative statement.

### F2 — Major: `definite` drops the asserted estimates for the unscaled matrix

Signature lines 286–289; blueprint `bpP:p9:definite`, p9 lines 91–103; graph record `bpP:p9:definite`, especially `SOURCE_CONCLUSION` and `stepP:p9:p73-had`. The returned estimate concerns only `coeffs = Q_h`. Neither of the two inequalities for `qhat` is returned. `l75` and `l75_bound` are generic ingredients, not the promised specialization to the literal planetary coefficients. The design table maps those cuts into `definite`, so proving exactly the advertised signature does not discharge their whole contract. Preserve the current result and add the missing specialization:

```lean
theorem definite (D : Data n) (hn : 2 ≤ n)
    {a : Vec n} (ha : a ∈ axes n) :
    let cHat : ℝ := ⨅ j, ∑ k ∈ Finset.univ.erase j,
      (pairA D a j k - pairB D a j k)
    0 < cHat ∧
    (∀ x : Vec n,
      quad (qhat D a) x ≤
        -(∑ j, (∑ k ∈ Finset.univ.erase j,
          (pairA D a j k - pairB D a j k)) * x j^2) ∧
      -(∑ j, (∑ k ∈ Finset.univ.erase j,
          (pairA D a j k - pairB D a j k)) * x j^2) ≤
        -cHat * length2 x^2) ∧
    0 < coercivity D a ∧
    (∀ x, quad (coeffs D a) x ≤ -coercivity D a * length2 x^2) ∧
    (∀ j, sigma D a j ≤ -coercivity D a) ∧
    ContinuousOn (coercivity D) (axes n) := by
  sorry
```

These added estimates are not new assumptions. The existing source argument proves them before the congruence step.

### F3 — Major: `diagonalize` omits the locally uniform rotated expansion

Signature lines 351–363; blueprint `bpP:p9:diagonalize`, p9 lines 134–153, especially (b),(c); graph `P-p9.nodes.md:744` and its `SOURCE_CONCLUSION`. The signature exports the exact quadratic identity and, for each fixed action, an average/composition identity. It exports no bound for the rotated remainder, no local uniformity in the actions and no explicit negative Ω. Its radius lies *after* `I ∈ W`. The source's locally uniform fourth-order expansion is precisely the quantitative assertion needed when Part 11 preparation chooses one neighbourhood. The original `quadratic_form` is an ingredient for proving this, not a rotated expansion with the required witnesses. The split transport declarations do correctly address (d); that part is not the objection.

Replace `diagonalize` by the following strengthening (same source premises, current conclusions retained). This adds a convenient max-norm formulation of the source's local uniform O(u^4), equivalent in finite dimension:

```lean
theorem diagonalize (D : Data n) (hn : 2 ≤ n) {W : Set (Vec n)} (hW : IsOpen W)
    (hWI : W ⊆ actionDomain D) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I))
    (hDiag : ∀ I ∈ W, coeffs D (axis D I) =
      R I * Matrix.diagonal (sigma D (axis D I)) * (R I).transpose) :
    (∀ I ∈ W, ∀ ξ η : Vec n,
      quad (coeffs D (axis D I)) ξ + quad (coeffs D (axis D I)) η =
      ∑ j, (2*sigma D (axis D I) j) *
        oscillatorAction ((R I).transpose.mulVec η) ((R I).transpose.mulVec ξ) j) ∧
    (∀ b : Bool, ∀ I ∈ W, ∃ r : ℝ, 0 < r ∧ ∀ ξ η : Vec n,
      ‖(ξ,η)‖ < r →
      avg (fun t => perturbation D b (liftInv R (assemble I t η ξ))) =
        secular D b ((R I).mulVec ξ,I,(R I).mulVec η)) ∧
    (∀ I ∈ W, ∀ j, 2*sigma D (axis D I) j < 0) ∧
    (∀ I0 ∈ W, ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      Metric.ball I0 r ⊆ W ∧
      ∀ b : Bool, ∀ I ∈ Metric.ball I0 r, ∀ ξ η : Vec n,
        ‖(ξ,η)‖ < r →
        |avg (fun t => perturbation D b (liftInv R (assemble I t η ξ))) -
          (constantTerm D (axis D I) + (if b then modelDelta D I else 0) +
            ∑ j, (2*sigma D (axis D I) j) * oscillatorAction η ξ j)| ≤
          C * ‖(ξ,η)‖^4) := by
  sorry
```

The source's full Hamiltonian split is already separately owned by `pc_share` and action preservation by `lift`; the correction above targets the missing quantitative secular export. The simple-spectrum premise is not needed for this algebraic/average result once an analytic SO diagonalizer is supplied. Its omission is a valid strengthening, though the departures section should say so.

### F4 — Major: the claimed exact import DAG cannot implement the declarations as allocated

Design lines 395–433 claim every non-upstream input is listed and lies in a strictly earlier wave. Two counterexamples:

1. `S9-D` (Definiteness, wave 4) exports `definite`, whose type uses `sigma`. The table assigns `sorted` and `sigma` to `S9-S` (LocalAnalytic, also wave 4), and does not list S9-S as an input. A type dependency is required even before a proof is written.
2. `S9-G` (GoodPolynomial, wave 5) exports `good_set_dichotomy`. Its null-set conclusion needs the explicitly owned `analytic_zero_null`/`generic` layer in S10-Z. Its sole listed package input is S9-S. The selected analytic-zero route cannot obtain this result from the spectral/IFT package.

Proposed concrete ownership repair:

```text
S9-N / SecularSpectrum/Norms / wave 2: also own sorted and isSO.
S8-C / SecularForm/Coefficients / wave 3: also own SecularSpectrum.sigma;
  add S9-N as an input, after coeffs_hermitian has been declared.
S9-S / SecularSpectrum/LocalAnalytic / wave 4: import those definitions;
  retain ownership of local_analytic and local_analytic_unique only.
S9-G / SecularSpectrum/GoodPolynomial / wave 5: add S10-Z as an input.
```

All newly listed edges then point strictly backwards. Alternatively move a module to a later wave and update every affected consumer; do not merely assert the existing table is already a complete DAG. Forecast lengths remain below 1500; the repair does not require a large module.

### N1 — Note: graph coverage is narrower than full blueprint coverage

The published p9 packet and the 158-row design inventory omit `bpP:p9:lemma70`, `lemma71`, `cor72`, `top-simple` and their proof steps even though those statements occur in the byte-matching blueprint (p9 lines 29–68,185–191). They are not signatures in this assignment's declared published-graph scope. Accordingly this audit does not fail their absence or invent an implementation for them. Preserve this boundary in completion claims: “158/158 published records” does not mean “every theorem appearing in Parts 8–10”. The unused roots-continuity alternative is also explicitly unpaid, correctly.

### N2 — Note: keep the proof boundary and upstream status explicit

The copied Part 1 interfaces match the current `PPart1Signatures.lean` after whitespace normalization, including all definition bodies and both theorem types. They are draft interfaces, not delivered proofs. The five missing P7 obligations are owned, not assumed. O(2) invariant theory, multivariable analytic zero-null, min-max, polarization and the two inductions remain substantive proof work. No theorem here seals a frozen anchor or proves torsion. No new pinned-paper erratum is alleged by this audit.

## Signature inventory

One row per theorem signature follows. Names are relative to `KAM.Planetary`; the final definitions table inventories the remaining 92 declarations separately. PASS means no material defect found in that signature, read together with the explicitly allocated cooperating exports. It does not assert proof existence or completion. Proposed replacements above are review text, not a modified/re-elaborated input signature file.

| Lean theorem | Blueprint label / role | Verdict | Reason |
|---|---|---|---|
| `SecularForm.perturbation_analytic` | `bpP:p8:perturbation-analytic` | PASS | Common radius, bilinear complex square, both models and real restriction retained. |
| `SecularForm.symmetries` | `bpP:p8:symmetries` | PASS | Three literal chart identities on invariant chart domain. |
| `SecularForm.evenness` | `bpP:p8:evenness` | PASS | Exact reflection and simultaneous rotation, including total averages. |
| `SecularForm.lemma64` | `bpP:p8:lemma64` | PASS | Correct mass power, virial term and cross averages. |
| `SecularForm.laplace` | `bpP:p8:laplace` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.identities` | `bpP:p8:identities` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.coeffs_hermitian` | `bpP:p8:coeffs` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.coeffs_analytic` | `bpP:p8:coeffs` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.quadratic_form` | `bpP:p8:quadratic-form` | PASS | Literal half matrix; uniform action-neighbourhood fourth-order bound. |
| `SecularForm.identification` | `bpP:p8:identification` | PASS | Integrability equivalence guards subtraction of total integrals. |
| `SecularForm.same_jets` | `bpP:p8:same-jets` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.birkhoff_transfer` | `bpP:p8:same-jets#transfer (conditional helper)` | PASS | Distinct conditional helper; frozen integrability and remainder clauses. |
| `SecularForm.same_jets_transfer` | `bpP:p8:same-jets#transfer` | PASS | Source-specific discharge on whole chart disc; Ω and β unchanged. |
| `SecularForm.quartic` | `bpP:p8:quartic` | PASS | Six invariant coefficients, action dependence, exact diagonal values. |
| `SecularSpectrum.norm_compare` | `bpP:p9:conv#data / norm-compare` | PASS | Explicit Euclidean lengths; ambient Pi norm stays max. |
| `SecularSpectrum.l75` | `bpP:p9:l75` | PASS | Sign-free identity is true; inequality guard remains in l75_bound. |
| `SecularSpectrum.l74` | `bpP:p9:l74` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularSpectrum.definite` | `bpP:p9:definite` | FAIL | F2: qhat estimate chain omitted. |
| `SecularSpectrum.local_analytic` | `bpP:p9:local-analytic` | PASS | Simple eigenvalue enumeration yields analytic ordered SO frame. |
| `SecularSpectrum.lift` | `bpP:p9:lift` | PASS | Full action derivative and inverse correction; frozen symplectic form. |
| `SecularSpectrum.k4_finite` | `bpP:p9:good` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularSpectrum.good_set` | `bpP:p9:good-set(a,b)` | PASS | Symmetric polynomial and NR4 equivalence retained. |
| `SecularSpectrum.diagonalize` | `bpP:p9:diagonalize(a–c)` | FAIL | F3: locally uniform rotated expansion omitted. |
| `SecularSpectrum.n2` | `bpP:p9:n2` | PASS | Explicit two-body identities in increasing spectrum convention. |
| `SecularSpectrum.n2_global_frame` | `bpP:p9:n2` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.generic` | `bpP:p10:generic` | PASS | Finite common nonzero locus; openness, relative density and null bad set. |
| `Nondegeneracy.weyl` | `bpP:p10:weyl` | PASS | Sorted multiplicities and explicit Euclidean operator norm. |
| `Nondegeneracy.sorted_analytic` | `bpP:p10:sorted-analytic` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.laplace_bounds` | `bpP:p10:laplace-bounds` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.formula69` | `bpP:p10:formula69` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.peel` | `bpP:p10:peel` | PASS | Uniform C precedes inner axis; powers 3/2, 2, 11/4 retained. |
| `Nondegeneracy.n2` | `bpP:p10:n2` | PASS | Explicit two-body identities in increasing spectrum convention. |
| `Nondegeneracy.good_point` | `bpP:p10:good-point` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.good_set` | `bpP:p10:good-set` | PASS | Symmetric polynomial and NR4 equivalence retained. |
| `Nondegeneracy.fc_analytic` | `bpP:p10:Fc-analytic` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.f_nonzero` | `bpP:p10:F-nonzero` | PASS | Every nonzero real relation vector and all positive mass data. |
| `Nondegeneracy.rnd` | `bpP:p10:rnd` | PASS | Actual action map, joint and separate frequency components. |
| `Nondegeneracy.scaling` | `bpP:p10:scaling / rnd(c)` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.finite_type` | `bpP:p10:finite-type` | PASS | Compact nonempty parameter and patch guards; least order handled separately. |
| `Nondegeneracy.index_amount` | `bpP:p10:index-def` | PASS | Least positive index, monotonic amount and positivity equivalence. |
| `Nondegeneracy.cp09_lemma1` | `bpP:p10:cp09-lemma1` | PASS | Squared scalar family; positive output dimension and compact nonempty K. |
| `Nondegeneracy.stability` | `bpP:p10:stability` | PASS | Correct diagonal tensor norms, 2^ν constant and positive-old-amount guard. |
| `Nondegeneracy.interface` | `bpP:p10:interface` | PASS | Simultaneous patch, positive NR4 minimum, action image and least positive order. |
| `SecularForm.e_param` | `bpP:p8:e-param` | PASS | Compact-cell holomorphic parameter integral on open domain. |
| `SecularForm.e_diff` | `bpP:p8:e-diff` | FAIL | F1: extra analytic/all-orders premises. |
| `SecularForm.average_translate` | `bpP:p8:e-diff` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.e_taylor` | `bpP:p8:e-taylor` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.e_weyl` | `bpP:p8:e-weyl` | PASS | Owns polynomial invariant theorem, no assumed representation. |
| `SecularForm.e_poch` | `bpP:p8:e-poch` | PASS | Literal coefficients, binomial series and asymptotic bound. |
| `SecularForm.compact_uniform` | `bpP:p12:f-unif / p8 pa-unif adapter` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.periodic_derivative_integral` | `K:bp:p1:ext-integral` / `bpP:p8:lemma64` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.quartic_scaling` | `bpP:p8:quartic(a)` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.f_pol` | `bpP:p10:f-pol` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.f_leib` | `bpP:p10:f-leib` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.scaling_amount` | `bpP:p10:scaling` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `isLatticeTorus_periodOne_iff` | `bpP:p1:period-convert / phys-pipeline` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `phys_pipeline` | `bpP:p1:phys-pipeline` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.lemma64_coordinates` | `bpP:p8:lemma64` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.evenness_taylor` | `bpP:p8:evenness` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.same_jets_on` | `bpP:p8:same-jets#jets` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.analytic_zero_null` | `bpP:p9:e-id / p10:generic` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.action_diffeomorphism` | `bpP:p10:conv#data` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.product_chart` | `bpP:p7:product-chart(b)` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.pc_prod` | `bpP:p7:pc-prod` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.pc_share` | `bpP:p7:pc-share` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.pc_dec` | `bpP:p7:pc-dec` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularSpectrum.lattice` | `bpP:p7:lattice` | PASS | Literal positive-action polar chart; radian quotient and conformal factor. |
| `SecularSpectrum.diagonalize_transport` | `bpP:p9:diagonalize(d), owned gap repair` | PASS | Polar/lift/cast composition and full Q1/Q2 obligations. |
| `SecularSpectrum.diagonalize_period_one` | `bpP:p9:diagonalize(d) / p1:phys-pipeline` | PASS | Frozen physical torus, ω/(2π), unchanged physical time. |
| `SecularForm.quartic_pair_scaling` | `bpP:p8:quartic(a)` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularSpectrum.norm_compare_operator` | `bpP:p9:norm-compare` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularSpectrum.good_characteristic` | `bpP:p9:good-set(a)` | PASS | Symmetric polynomial in literal charpoly coefficients. |
| `SecularSpectrum.good_set_dichotomy` | `bpP:p9:good-set(c)` | PASS | Exact analytic-zero dichotomy; package dependency missing (F4). |
| `SecularSpectrum.local_analytic_unique` | `bpP:p9:local-analytic` | PASS | Connected patch fixes column signs with determinant one. |
| `SecularSpectrum.l75_bound` | `bpP:p9:l75` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `SecularForm.laplace_fourier` | `bpP:p8:laplace-def` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.cp09_unsquared` | `bpP:p10:cp09-lemma1` | PASS | Source statement retained by this helper and its named cooperating exports. |
| `Nondegeneracy.cp09_product` | `bpP:p10:cp09-lemma1` | PASS | Independent coefficient spheres; r=0 correctly gives constant product one. |

## Definitions and structures

Verdict: **PASS for mathematical objects and guards**, with the module-ownership defect F4. Every carrier is a Pi type or a product of Pi types. There is no new global instance. `Data` contains only positive physical data and dimension. `secular` uses the frozen average itself; the frozen oscillator half is preserved. Literal inverse powers, integrals and derivatives are only consumed with their local validity guards. For n=0, empty unit spheres in the generic norm definitions give the zero operator value; positive-output sphere families explicitly require m>0. `index_def` has an existence witness and never returns a fabricated default order.

The auxiliary `pairA/pairB` diagonal values and arbitrary off-domain total values are not used as analytic or physical values. Remainders use the ambient max norm only where equivalence of finite-dimensional norms permits it; CP09's amount and stability use the explicit Euclidean diagonal tensor norm. No hidden conversion of that amount to a full mixed multilinear norm was found.

The following rows cover every non-theorem declaration. Labels for auxiliary notation identify its owning blueprint object, not a claim that the blueprint spells out that helper's Lean name.

| Declaration | Blueprint owner | Verdict |
|---|---|---|
| `SecularForm.Vec` | `bpP:p8:conv#data` | PASS |
| `SecularForm.CVec` | `bpP:p8:conv#data` | PASS |
| `SecularForm.Mat` | `bpP:p8:conv#data` | PASS |
| `SecularForm.Slow` | `bpP:p8:conv#data` | PASS |
| `SecularForm.CSlow` | `bpP:p8:conv#data` | PASS |
| `SecularForm.Data` | `bpP:p8:conv#data` | PASS |
| `SecularForm.axes` | `bpP:p8:conv#data` | PASS |
| `SecularForm.action` | `bpP:p8:conv#data` | PASS |
| `SecularForm.axis` | `bpP:p8:conv#data` | PASS |
| `SecularForm.actionDomain` | `bpP:p8:conv#data` | PASS |
| `SecularForm.nu` | `bpP:p8:conv#data` | PASS |
| `SecularForm.perturbation` | `bpP:p8:conv#data` | PASS |
| `SecularForm.secular` | `bpP:p8:conv#data` | PASS |
| `SecularForm.slowSecular` | `bpP:p8:conv#data` | PASS |
| `SecularForm.slowDom` | `bpP:p8:conv#data` | PASS |
| `SecularForm.cell` | `bpP:p8:conv#data` | PASS |
| `SecularForm.avg` | `bpP:p8:conv#data` | PASS |
| `SecularForm.rho` | `bpP:p8:rho / conv#data` | PASS |
| `SecularForm.polydisc` | `bpP:p8:rho / conv#data` | PASS |
| `SecularForm.inclusion` | `bpP:p8:rho / conv#data` | PASS |
| `SecularForm.realDisc` | `bpP:p8:rho / conv#data` | PASS |
| `SecularForm.planetC` | `bpP:p8:conv#data` | PASS |
| `SecularForm.separationC` | `bpP:p8:conv#data` | PASS |
| `SecularForm.perturbationC` | `bpP:p8:conv#data` | PASS |
| `SecularForm.secularC` | `bpP:p8:conv#data` | PASS |
| `SecularForm.rotateSlow` | `bpP:p8:conv#data` | PASS |
| `SecularForm.rotatePhysical` | `bpP:p8:conv#data` | PASS |
| `SecularForm.momentum` | `bpP:p8:conv#data` | PASS |
| `SecularForm.position` | `bpP:p8:conv#data` | PASS |
| `SecularForm.laplace_def` | `bpP:p8:laplace-def / e-poch` | PASS |
| `SecularForm.poch` | `bpP:p8:laplace-def / e-poch` | PASS |
| `SecularForm.laplaceTerm` | `bpP:p8:laplace-def / e-poch` | PASS |
| `SecularForm.laplaceC` | `bpP:p8:laplace-def / e-poch` | PASS |
| `SecularForm.pairA` | `bpP:p8:coeffs` | PASS |
| `SecularForm.pairB` | `bpP:p8:coeffs` | PASS |
| `SecularForm.constantTerm` | `bpP:p8:coeffs` | PASS |
| `SecularForm.qhat` | `bpP:p8:coeffs` | PASS |
| `SecularForm.coeffs` | `bpP:p8:coeffs` | PASS |
| `SecularForm.quad` | `bpP:p8:coeffs` | PASS |
| `SecularForm.modelDelta` | `bpP:p8:identification` | PASS |
| `SecularForm.pairSlowSecular` | `bpP:p8:quartic` | PASS |
| `SecularForm.quarticMonomials` | `bpP:p8:quartic` | PASS |
| `SecularForm.radialPhi` | `bpP:p8:quartic` | PASS |
| `SecularForm.radialH` | `bpP:p8:quartic` | PASS |
| `SecularForm.radialR1` | `bpP:p8:quartic` | PASS |
| `SecularSpectrum.length2` | `bpP:p9:conv#data` | PASS |
| `SecularSpectrum.op2` | `bpP:p9:conv#data` | PASS |
| `SecularSpectrum.frobenius` | `bpP:p9:conv#data` | PASS |
| `SecularSpectrum.sorted` | `bpP:p9:conv#data` | PASS |
| `SecularSpectrum.sigma` | `bpP:p9:conv#data` | PASS |
| `SecularSpectrum.isSO` | `bpP:p9:conv#data` | PASS |
| `SecularSpectrum.dominance` | `bpP:p9:l75 / definite` | PASS |
| `SecularSpectrum.coercivity` | `bpP:p9:l75 / definite` | PASS |
| `SecularSpectrum.liftMap` | `bpP:p9:lift` | PASS |
| `SecularSpectrum.liftInv` | `bpP:p9:lift` | PASS |
| `SecularSpectrum.liftDomain` | `bpP:p9:lift` | PASS |
| `SecularSpectrum.k4` | `bpP:p9:good` | PASS |
| `SecularSpectrum.nr4` | `bpP:p9:good` | PASS |
| `SecularSpectrum.discriminant` | `bpP:p9:good` | PASS |
| `SecularSpectrum.good` | `bpP:p9:good` | PASS |
| `SecularSpectrum.goodAxes` | `bpP:p9:good` | PASS |
| `SecularSpectrum.simpleAxes` | `bpP:p9:good` | PASS |
| `Nondegeneracy.outerData` | `bpP:p10:peel` | PASS |
| `Nondegeneracy.peelError` | `bpP:p10:peel` | PASS |
| `Nondegeneracy.rnd_def` | `bpP:p10:rnd-def / Fc-def` | PASS |
| `Nondegeneracy.relation` | `bpP:p10:rnd-def / Fc-def` | PASS |
| `Nondegeneracy.fc_def` | `bpP:p10:rnd-def / Fc-def` | PASS |
| `Nondegeneracy.frequency` | `bpP:p10:rnd / interface` | PASS |
| `Nondegeneracy.frequencyAxes` | `bpP:p10:rnd / interface` | PASS |
| `Nondegeneracy.jetNorm` | `bpP:p10:index-def / stability` | PASS |
| `Nondegeneracy.scalarJet` | `bpP:p10:index-def / stability` | PASS |
| `Nondegeneracy.jetMax` | `bpP:p10:index-def / stability` | PASS |
| `Nondegeneracy.betaFamily` | `bpP:p10:index-def / stability` | PASS |
| `Nondegeneracy.sphere` | `bpP:p10:index-def / stability` | PASS |
| `Nondegeneracy.squaredForm` | `bpP:p10:index-def / stability` | PASS |
| `Nondegeneracy.betaMu` | `bpP:p10:index-def / stability` | PASS |
| `Nondegeneracy.index_def` | `bpP:p10:index-def / stability` | PASS |
| `SecularForm.unitPosition` | `bpP:p8:quartic` | PASS |
| `SecularForm.separatedDomain` | `bpP:p8:quartic` | PASS |
| `SecularForm.dimensionlessPair` | `bpP:p8:quartic` | PASS |
| `IsChart` | `bpP:p1:chart / phys-pipeline` | PASS |
| `fullShift` | `bpP:p1:chart / phys-pipeline` | PASS |
| `IsLatticeTorus` | `bpP:p1:chart / phys-pipeline` | PASS |
| `periodOne` | `bpP:p1:chart / phys-pipeline` | PASS |
| `IsTwoPiLatticeTorus` | `bpP:p1:chart / phys-pipeline` | PASS |
| `SecularForm.keplerActionHam` | `bpP:p7:product-chart` | PASS |
| `polarDom` | `bpP:p7:lattice` | PASS |
| `polarMap` | `bpP:p7:lattice` | PASS |
| `angleScale` | `bpP:p7:lattice` | PASS |
| `SecularSpectrum.rotatedPhysicalChart` | `bpP:p9:diagonalize(d) / p7:lattice` | PASS |
| `SecularSpectrum.rotatedDomain` | `bpP:p9:diagonalize(d) / p7:lattice` | PASS |
| `SecularSpectrum.opMax` | `bpP:p9:conv#data` | PASS |

## Consumer and frozen-object verdicts

Frozen-object verdict: **PASS**. Read `Phase`, `Assemble`, `SecularAverage`, `OscillatorAction`, `HasSecularBirkhoffForm`, `IsPhysicalTorus`, `HamiltonianVectorField`, and `SymplecticForm`. The signatures use these exact declarations. In particular the physical output is `Phase (n*2)`, the canonical source is `Phase (n+n)`, and `phaseCast (Nat.mul_two n)` bridges them. No parallel solution predicate replaces a frozen one. No frozen source or manifest was edited.

Consumer verdict: **FAIL pending F3**, otherwise no incompatible carrier found. The relevant uses checked are:

| Consumer | Required output | Audit |
|---|---|---|
| P Part 9 | Laplace positivity, symmetric literal half matrix and O(u^4) | Preserved by p8 exports; F2 concerns the full p9 definiteness contract. |
| P Part 10 | Sorted multiplicities, negative spectrum, finite analytic symmetric product | Correct Euclidean operator norm; no universal cover or global analytic root assumption. |
| P Part 11 preparation, including p11 `stepP:p11:wr-tube` | Analytic rotation/lift, norm preservation, common local rotated expansion | Lift and norm preservation present; quantitative expansion must be exported as in F3. |
| P Part 11a, rank-compact and stability | Positive finite order in action coordinates; squared and unsquared scalar amounts | `interface`, `cp09_lemma1`, `cp09_unsquared`, `cp09_product`, `stability` fit. Part 11a separately owns its C^μ and unsquared stability generalization. |
| P Part 11b torsion | Six quartic invariants, diagonal formulas and common model jets | Present; mixed coefficients and torsion determinant remain Part 11b proof work. |
| P Parts 12/13 | Good patch in any neighbourhood, additional nonzero determinant condition, moving/fixed transfer | `interface` includes the finite extra family before patch witnesses; exact frozen transfer preserves Ω and β. |
| P Part 1 physical transport | Chart Q1/Q2 and radian torus, Diophantine ω | Literal copied API and named period-one wrapper are compatible. |

The brief's requested N-p3 consumer search was also inspected in I/P and N Parts 7,11,12. Those references concern the separate ODE layer (uniqueness, continuation and frozen solution predicates); they do not create an additional P810 signature or justify importing a parallel solution notion here.

Package verdict: **FAIL (F4)**. There are 33 forecast modules, 10 waves, each under 1500 lines; no provider import or planned frozen edit. The line forecasts pass, but the exact declared imports do not. The generic parameter integral adapter also needs the routine finite-product reindexing from CSlow to CVec; no assertion of an automatic carrier equality should replace that adapter.

## Validation and limitations

1. Direct requested worktree invocation, `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .drafts/scratch/P810Signatures.lean`: exit **1**, before source elaboration, `unknown module prefix 'KAM'`. This worktree has shared packages but no `.lake/build`. This is an environment failure, not a signature defect. No library rebuild was attempted.
2. One effective signature elaboration through the designer's prescribed shared-build gate:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
     /root/code/KAM-inp-design-p810 .drafts/scratch/P810Signatures.lean
   exit 0; exactly 78 warnings: declaration uses `sorry`; no errors or other Lean diagnostics.
   ```

   The wrapper runs `LEAN_NUM_THREADS=1 nice -n 5 ... lake env lean` in `/root/code/KAM-inp`. Only one Lean/lake process was started at a time by this auditor; the shared gate has other slots for independently managed sessions.
3. Independent name/type probe `.lake/abi-scratch/P810Names.lean`, through the same wrapper: exit **0**. Checked the following names and inspected their displayed types:

   ```text
   Matrix.IsHermitian.spectral_theorem
   Matrix.IsHermitian.charpoly_eq
   Matrix.IsHermitian.eigenvalues₀_antitone
   Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀
   MvPolynomial.esymmAlgEquiv
   AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
   ContDiffAt.contDiffAt_implicitFunction
   AnalyticAt.contDiffAt
   ContDiffAt.analyticAt
   AnalyticAt.analyticAt_localInverse
   IsCompact.uniformContinuousOn_of_continuous
   intervalIntegral.integral_eq_sub_of_hasDerivAt
   intervalIntegral.integral_mul_deriv_eq_deriv_mul
   intervalIntegral.integral_pos_iff_support_of_nonneg_ae
   ```

   Applicability: the spectral theorem is a matrix conjugation identity; `eigenvalues₀` is antitone, so reversing is required. The symmetric-polynomial equivalence accepts an arbitrary commutative coefficient ring, including Polynomial ℝ. The identity theorem propagates zero on a preconnected set; it does not prove nullity. The analytic IFT requires an invertible partial derivative and nonzero differentiability order; its analytic specialization is the top order. FTC requires derivative integrability, supplied by the C¹ periodic map. No missing Mathlib-name failure was found.
4. Independent `#print axioms` on delivered inputs:

   ```text
   KAM.Planetary.poincareProd_symplectic:
     [propext, Classical.choice, Quot.sound]
   KAM.Planetary.poincare_holomorphic:
     [propext, Classical.choice, Quot.sound]
   ```

   The draft's 78 main results all have literal `sorry` bodies and therefore depend on `sorryAx`; they are not proofs. The handoff's six draft axiom lists were not independently reprinted here (doing so would require a further elaboration of the same draft); the independently verified fact is their unchanged literal bodies and successful signature elaboration. No claim of an axiom-free main theorem is made.
5. `LEAN_PATH=/root/code/KAM-inp/.lake/build/lib/lean LEAN_NUM_THREADS=1 nice -n 5 scripts/lint_sources.sh`: exit **0**, exact output:

   ```text
   check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   This supplies the shared built modules to the unchanged lint/ABI checks. No production-module build applies to this report-only assignment; the signature elaboration is the targeted check.
6. `git diff --check inp...HEAD`: exit **0**. Appendix equality, all three blueprint hashes, 158 unique covered graph nodes and 78 theorem rows independently checked. The report has one row for each of the 92 remaining definitions/abbreviations/structure declarations as well. Temporary probes and the audit's scratch signature copy are removed after checking. Final repository change: this report only; no state-changing git command, source edit, frozen edit or manifest edit.

Uncertainties: proof-size forecasts and the feasibility of the difficult owned proof packages remain design estimates. The proposed corrected signatures above were not substituted into or elaborated with the original signatures; they are proposed fixes for a designer revision and subsequent check. No new paper-PDF audit was performed. Inherited errata E-P-Fej04r-2,-3,-7,-8, E-P8-Fej50 and E-P-CP11-1,-2 remain inherited allegations with the design's quotations and blueprint locators, not new confirmations by this report. No mathematical deviation was introduced in repository Lean code.
