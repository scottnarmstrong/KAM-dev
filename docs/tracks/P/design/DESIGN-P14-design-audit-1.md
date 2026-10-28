# P14 independent design audit 1

**Overall verdict: FAIL.** Signature/source fidelity needs correction before these contracts are given to provers. The supplied file elaborates, the four frozen target types are preserved, and no counterexample to those four targets was found. These facts do not repair the helper-contract findings below.

Audit date: 2026-10-28. Scope: the design and all 47 theorem signatures, 19 definitions and one structure; both P14 blueprint parts; their 182 packet records; relevant frozen objects and supplier interfaces. This is a tier-2 refute-first design audit, not proof verification or a new pinned-PDF audit.

## Frozen inputs and permissions

- Worktree `/root/code/KAM-inp-design-p14`, branch `inp-design-p14`, HEAD `19d394844f5b9ce0c87aa12832413e9ddc6e893a`; comparison ref `inp` = `cd23a4d1097be186cd5c5703bf8687af6373121d` at inspection.
- `git diff inp...HEAD` contains only the 1198-line `docs/tracks/P/design/P14-LEAN-DESIGN.md` addition; SHA-256 `392d3d8624114bfa4d3265bddcef636ab9f812ce04204ba8e13d0309c007fc2b`.
- Original `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`: 712 lines; SHA-256 `6ddae2d1ecb4a64662c872b1d7c387e64fb7d2d78d456e0275b1fcb4585db435`. Appendix A is byte-identical. The original was never edited; the requested scratch copy was used.
- Handoff `.drafts/handoff-DESIGN-P14.md`: SHA-256 `50047d2b6e09b258f92752c7e7c4955c56fefd2321686db55b1c1545b1fc4987`.
- `blueprint-P/parts/p14a-amd-expsafe.tex` (a): SHA-256 `a2735bd6fbc36dc765bafccac43af4e3742b101a7e0f2d97725e70ac37ff8452`.
- `blueprint-P/parts/p14b-secular-box.tex` (b): SHA-256 `f14536c948f27bc9ccb330b5df0b482846696aa7ea10283d42ee2569be2d0ae7`.
- Packet files `P-p14a1.nodes.md`, `P-p14a2.nodes.md`, `P-p14b.nodes.md`: 45, 56, 81 records respectively. SHA-256 respectively `38cb7e1a7018dd0d050010a4686617ad153771338921e2c8c27968ab49bb143e`, `752a183229761111a610be1a9d64bf483b77c5b162361ec969d20b188141fe5e`, `58f7a3d123c1d67a08b925aa61e1bfd0f39b5cdb9b744e509a088104f0e5dcd2`.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the exact audit brief and designer handoff. The manuscript-audit skill supplied the evidence/refutation procedure; the user's report-only authorization supplied the permission envelope. No git mutations, production edits, frozen edits or build-cache repairs were authorized or performed. Temporary ABI probes are removed after use.

All locators below refer to this snapshot. S means the original signatures file; D means the design. PASS in the ledger means an acceptable design contract, sometimes composed with explicitly assigned companion obligations; it never means a proved theorem. Findings were rechecked against the source, graph packet, companion signatures and downstream uses before classification.

## Numbered findings and proposed fixes

### F1 — Major: h_data does not preserve the source constants or their dependence

**Evidence.** S243–255 / D728–740 says `∃ g v M : ℝ` after `kappa e A rho` and their hypotheses. There is no equation tying those witnesses to the formulas in D267–271. Source a195–200 fixes
`g_h = min_i m_i^3/(u_i+3κ)^3`, `varsigma_h = min_i 3m_i^3/(u_i+3κ)^4`, and `M_C = sum_i 3m_i^3/(5ℓ_i/8)^4`.
The packet `P-p14a2.nodes.md`, node `bpP:p14:h-data`, explicitly says `CONSTANT_SCOPE: g_h, varsigma_h, M_C depend on m, l, u, kappa only`. It also exports the real-coordinate lower margin, absent from S.

**Refutation attempt.** D271 acknowledges existential packaging, and E11 can fix a particular rho before applying N. That is enough for the eventual frozen expsafe quantifier order, so this finding does not allege a false frozen theorem. But the contract permits witnesses varying with rho,e,A and has no formula constraint; choosing smaller g,v and larger M preserves its conclusion. It therefore does not establish the source's specific constants or the claimed dependence. Prose formulas cannot constrain a Lean existential. The finding survives the audit brief's explicit constant-dependence criterion.

**Fix.** Fix the three scalar definitions before rho, or constrain witnesses to the exact finite minima/sum. The following replacement uses minimum characterizations to avoid an auxiliary instance or a choice of default index. The positive planet count guarantees the minima exist. Negated holomorphy/C2/reality/Hessian-bound clauses follow from the displayed clauses by negation; keep those bridges in E4.

```lean
theorem h_data (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible)
    {kappa e A rho : ℝ} (hd : EnlargedData B kappa e A)
    (hrho : 0 < rho) (hrk : rho ≤ kappa) :
    (∀ I ∈ fastBox B kappa, Metric.closedBall I rho ⊆ fastBox B (2*kappa)) ∧
    ∃ g v M : ℝ,
      (∀ i, g ≤ B.mass i^3 / (B.upper i + 3*kappa)^3) ∧
      (∃ i, g = B.mass i^3 / (B.upper i + 3*kappa)^3) ∧
      (∀ i, v ≤ 3 * B.mass i^3 / (B.upper i + 3*kappa)^4) ∧
      (∃ i, v = 3 * B.mass i^3 / (B.upper i + 3*kappa)^4) ∧
      M = ∑ i, 3 * B.mass i^3 / (5 * B.lower i / 8)^4 ∧
      0 < g ∧ 0 < v ∧ 0 < M ∧
      DifferentiableOn ℂ (planetaryKeplerC B.mass) (KAM.actionNbhd (fastBox B (2*kappa)) rho) ∧
      ContDiffOn ℂ 2 (planetaryKeplerC B.mass) (KAM.actionNbhd (fastBox B (2*kappa)) rho) ∧
      (∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ KAM.actionNbhd (fastBox B (2*kappa)) rho →
        (planetaryKeplerC B.mass (fun i => (I i : ℂ))).im = 0) ∧
      (∀ z ∈ KAM.actionNbhd (fastBox B (2*kappa)) rho,
        ‖fderiv ℂ (fderiv ℂ (planetaryKeplerC B.mass)) z‖ ≤ M) ∧
      KAM.Nekhoroshev.HasDefiniteFastPart (fastBox B (2*kappa)) rho g v (planetaryKeplerC B.mass) ∧
      KAM.Nekhoroshev.HasDefiniteFastPart (fastBox B (2*kappa)) rho g v (-planetaryKeplerC B.mass) ∧
      ∀ z ∈ KAM.actionNbhd (fastBox B (2*kappa)) rho, ∀ i,
        0 < 5 * B.lower i / 8 ∧
        5 * B.lower i / 8 ≤ B.lower i - 3*kappa ∧
        B.lower i - 3*kappa ≤ (z i).re
```

### F2 — Medium: the one-planet element contracts acquire unrelated planet premises

**Evidence.** Source a42–53 (`bpP:p14:elements`) assumes only one planet's `m>0`, `r>0`, `E<0`, `C>0`. S111–134 requires `ProgradeElliptic m z`, whose frozen body is `∀ i, ...` over every planet, before selecting i. D284–285 explicitly calls this a departure. The deficit helper inherits the same strengthening of the premises.

**Refutation attempt.** Every present AMD consumer does have all-planet ellipticity, and a one-planet result could be recovered by repackaging a new singleton system. Those observations avoid a current consumer blockage. They do not make the additional premises true for the existing carrier: the selected planet can be elliptic while another planet has zero position or negative angular momentum. No singleton transport bridge is part of this local contract. The brief requires failure for extra premises even if current consumers can supply them. This is a fidelity issue, not a counterexample to the stated conditional lemmas.

**Fix.** Require only the selected planet's four frozen scalar conditions. Global consumers pass `hz i`. Export the elementary clauses of (b), (c), (f) as well, rather than leaving their reconstruction implicit. These are complete replacement statement blocks; proof bodies are intentionally not supplied by this audit.

```lean
theorem elements {m : Fin n → ℝ} {z : Phase (n * 2)} (i : Fin n)
    (hz : 0 < m i ∧ 0 < planeLength (bodyVector z.1 i) ∧
      keplerEnergy m z i < 0 ∧
      0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i)) :
    0 < keplerAxis m z i ∧ 0 < keplerAction m z i ∧
    keplerAction m z i ^ 2 = m i ^ 2 * keplerAxis m z i ∧
    keplerEnergy m z i = -(m i)^3 / (2 * keplerAction m z i ^ 2) ∧
    planeLength (keplerEccVector m z i)^2 = 1 -
      planeCross (bodyVector z.1 i) (bodyVector z.2 i)^2 / keplerAction m z i ^ 2 ∧
    planeLength (keplerEccVector m z i) < 1 ∧
    planeCross (bodyVector z.1 i) (bodyVector z.2 i) =
      keplerAction m z i * Real.sqrt (1 - planeLength (keplerEccVector m z i)^2) ∧
    planeDot (bodyVector z.1 i) (keplerEccVector m z i) =
      keplerAxis m z i * (1 - planeLength (keplerEccVector m z i)^2) -
        planeLength (bodyVector z.1 i) ∧
    keplerAxis m z i * (1 - planeLength (keplerEccVector m z i)) ≤
      planeLength (bodyVector z.1 i) ∧
    planeLength (bodyVector z.1 i) ≤
      keplerAxis m z i * (1 + planeLength (keplerEccVector m z i)) ∧
    planeSq (bodyVector z.2 i) < 2 * m i ^ 2 / planeLength (bodyVector z.1 i) ∧
    (0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i) ∧
      planeCross (bodyVector z.1 i) (bodyVector z.2 i) ≤ keplerAction m z i) ∧
    0 ≤ planeLength (keplerEccVector m z i) ∧
    planeDot (bodyVector z.1 i) (keplerEccVector m z i) =
      planeCross (bodyVector z.1 i) (bodyVector z.2 i)^2 / m i^2 -
        planeLength (bodyVector z.1 i) ∧
    keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i) =
      keplerAction m z i * (1 - Real.sqrt (1 - planeLength (keplerEccVector m z i)^2)) ∧
    0 ≤ keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i)
```

```lean
theorem eccentricity_deficit {m : Fin n → ℝ} {z : Phase (n * 2)}
    (i : Fin n)
    (hz : 0 < m i ∧ 0 < planeLength (bodyVector z.1 i) ∧
      keplerEnergy m z i < 0 ∧
      0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i)) {e : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hle : e ≤ planeLength (keplerEccVector m z i)) :
    keplerAction m z i * (1 - Real.sqrt (1 - e ^ 2)) ≤
      keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i)
```

### F3 — Medium: real_domain loses quantitative pair separation

**Evidence.** Source a184–187 (`bpP:p14:real-domain`) says both `|q_i| ≥ d/2` and `|q_i-q_j| ≥ d/2` for `i ≠ j`. The corresponding packet repeats both. S228–233 / D713–718 exports chartSafe membership, eccentricity and radial lower bounds, but no pair lower bound. The row `stepP:p14:rd-sep` is assigned as an internal obligation of this parent, not as a separately exported replacement theorem.

**Refutation attempt.** Membership in chartSafe gives `NoCollision`, hence strictly positive pair distances. It gives no numerical `d/2` margin. E3 can prove the stronger margin from the enlarged annuli, but a proof step hidden inside a weaker parent theorem cannot subsequently be projected from its type. No other supplied signature exports this enlarged-domain quantitative conclusion. This survives as a weakened source conclusion, even though qualitative collision freedom suffices for several present consumers.

**Fix.** Retain the explicit pair margin. The last inclusion remains correctly split into `original_cylinder_subset`.

```lean
theorem real_domain (B : AMDBox n) (hB : B.Admissible) {kappa e A : ℝ}
    (hd : EnlargedData B kappa e A) :
    enlargedCylinder B kappa A ⊆ chartSafe B.mass ∧
    ∀ w ∈ enlargedCylinder B kappa A,
      (∀ i,
        planeLength (keplerEccVector B.mass (poincareProd B.mass 1 w) i) < e ∧
        B.distance / 2 ≤ planeLength (bodyVector (poincareProd B.mass 1 w).1 i)) ∧
      ∀ i j, i ≠ j → B.distance / 2 ≤
        planeLength (bodyVector (poincareProd B.mass 1 w).1 i -
          bodyVector (poincareProd B.mass 1 w).1 j)
```

### F4 — Low: uniform_data omits its stated delta upper bound

**Evidence.** Source a239–241 and the packet `bpP:p14:uniform-data` require `δ ∈ (0,π]`. D309 promises `choose delta≤pi`. S290–298 / D775–783 only returns `UniformData ... delta M L`; the existing structure has `delta_pos` but no upper bound.

**Refutation attempt.** One can shrink any returned delta to `min delta π`, preserving its closed-ball bounds and Lipschitz data. Thus this is an easy repair and does not invalidate continuation. The current type nevertheless lacks the source's upper-bound clause; the brief explicitly rejects weakened conclusions. Add the clause or an explicit shrinking wrapper in the same package.

```lean
theorem uniform_data {W Q : Set (Phase (n+n))} (hW : IsOpen W)
    {F : Phase (n+n) → Phase (n+n)} (hF : ContDiffOn ℝ 1 F W)
    (hWp : ∀ k : Fin n → ℤ, ∀ w, w ∈ W ↔ w + fastShift k ∈ W)
    (hFp : ∀ k : Fin n → ℤ, ∀ w ∈ W, F (w + fastShift k) = F w)
    (hQ : IsCompact Q) (hQ0 : ∀ w ∈ Q, fast w.1 = 0)
    (hQW : ∀ w : Phase (n+n),
      assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ Q → w ∈ W) :
    ∃ (delta M : ℝ) (L : ℝ≥0), KAM.ODE.UniformData F W
      {w | assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ Q} delta M L ∧ delta ≤ Real.pi
```

### F5 — Medium: the stated Mathlib reuse interface is not executable as written

**Evidence.** D265 names `intervalIntegral.integral_hasDerivAt`. An independent `#check` produces:

```text
error(lean.unknownIdentifier): Unknown constant `intervalIntegral.integral_hasDerivAt`
```

The existing replacement is `intervalIntegral.integral_hasDerivAt_right`, whose type requires interval integrability, strong measurability at the endpoint filter, and endpoint continuity. D65 names global `is_const_of_deriv_eq_zero` for interval constancy, but its checked type requires `Differentiable ... f` and zero derivative on the entire scalar field. It cannot directly consume angular-momentum conservation known only on J. D67 names `DifferentiableOn.div` for holomorphic calculus in arbitrary finite dimension; the checked declaration is the scalar-domain derivative version (`s : Set 𝕜`), so it does not directly instantiate at the product complex phase carrier.

**Refutation attempt.** Importing all Mathlib in the probe did not reveal the missing FTC name. The alternative `_right` theorem has exactly the needed endpoint shape. Interval constancy is available through convex-set mean-value results, and multivariable division can use inverse composition and multiplication. These are library-interface repairs, not new mathematical obstructions. `Convex.is_const_of_deriv_eq_zero` was tested only as a possible replacement and is also absent; it is not a name claimed by the design.

**Fix.** Correct the FTC name and document its three premises. For conservation on intervals use a convex-set derivative theorem (e.g. `Convex.is_const_of_fderivWithin_eq_zero` with derivative-within bridges), rather than asserting global differentiability. For complex division use the generic Frechet inverse/composition API. If a local wrapper is preferable, the concrete signatures needed by the consumers are:

```lean
theorem angle_quadrature {omega : ℝ → (Fin 2 → ℝ)}
    (h : Continuous omega) (t : ℝ) :
    HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, omega s) (omega t) t

theorem interval_constancy {J : Set ℝ} (hJ : J.OrdConnected)
    {f : ℝ → ℝ} (hf : ∀ t ∈ J, HasDerivAt f 0 t) :
    ∀ s ∈ J, ∀ t ∈ J, f t = f s

theorem complex_division {d : ℕ}
    {U : Set ((Fin d → ℂ) × (Fin d → ℂ))}
    {f g : ((Fin d → ℂ) × (Fin d → ℂ)) → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hg0 : ∀ z ∈ U, g z ≠ 0) :
    DifferentiableOn ℂ (fun z => f z / g z) U
```

These replacement statements are proposals, not proved additions. F5 concerns the supplier table; it does not turn the independently elaborated downstream theorem signatures into syntax failures.

## Signature ledger

Names are in `KAM.Planetary` unless prefixed `Provider.Planetary`, which means `KAM.Provider.Planetary`. Labels beginning `p14:` mean `bpP:p14:`; step suffixes name the source proof obligations. The two p7 labels are `bpP:p7:*`.

| Lean name | Blueprint label / obligation | Verdict | Reason |
|---|---|---|---|
| `local_complex_restriction` | `p7:ho-hol; p14:x-hol` | PASS | Local derivative restriction, no strip hypothesis. |
| `local_analytic_complexification` | `p14:x-cx` | PASS | Local real-to-complex extension; radius is existential. |
| `real_trace_identity` | `p14:x-id; tb-glue, tb-per` | PASS | Intersections of real-centred max balls; empty intersections harmless. |
| `secular_parametric_integral` | `p14:sb-sm-3; p8:e-diff` | PASS | Finite-order compact-parameter integral; C∞ obtained for every finite order. |
| `elements` | `p14:elements` | FAIL | F2: global ellipticity replaces the local planet premises. |
| `eccentricity_deficit` | `p14:elements(f)` | FAIL | F2: same unnecessary all-planet premise. |
| `ecc_bound` | `p14:ecc-bound` | PASS | All-planet ellipticity is needed here to control every deficit summand. |
| `geometry` | `p14:geometry` | PASS | Geometry plus amdCompact membership; elementary radial clauses also available from elements. |
| `amd_compact` | `p14:geometry, geo-k` | PASS | Exact compact collision-free set, split from geometry. |
| `closure` | `p14:closure` | PASS | Sequential collar closure and outer openness; continuity split below. |
| `element_continuity` | `p14:closure(a)` | PASS | Exact negative-energy domain; arbitrary fixed masses cause no continuity problem. |
| `moving_ode` | `p14:moving-ode` | PASS | Literal frozen predicate bridge and C1 field; negative field follows by negation. |
| `ang_mom` | `p14:ang-mom` | PASS | OrdConnected real time set; actual scalar angular momentum. |
| `enlarge` | `p14:enlarge` | PASS | All E1–E3 fields are source geometric inequalities. |
| `sec_domain_chart_facts` | `p14:ch-elements; sec-domain#chart-facts` | PASS | General n; remaining energy/eccentricity formulas derive using elements and the displayed dictionary. |
| `real_domain` | `p14:real-domain` | FAIL | F3: drops the d/2 pair-separation conclusion. |
| `original_cylinder_subset` | `p14:real-domain(last)` | PASS | Separate exact inclusion. |
| `h_data` | `p14:h-data` | FAIL | F1: unspecified constants chosen after rho, and no explicit constants or real-coordinate margin. |
| `chart_perturbation_analytic` | `p14:ch-split; p7:pc-share` | PASS | Explicit real-analytic obligation on chartSafe. |
| `tube` | `p14:tube` | PASS | Periodic complex tube, real agreement and membership; empty compact set allowed. |
| `perturbation` | `p14:perturbation` | PASS | Both P and -P; fixed B0 before mu; normalized frozen perturbation. |
| `uniform_data` | `p14:uniform-data` | FAIL | F4: omits delta ≤ pi. |
| `lift` | `p14:lift` | PASS | ChartSafe, physical projection and two-sided derivative on the closed segment; action/AMD bounds follow from hout and dictionary. |
| `hnu` | `p14:hnu` | PASS | Pointwise equality on open workingCylinder; field/differentiability bridges explicitly assigned to E10. |
| `stopped` | `p14:stopped` | PASS | B0 and nu0 before all mu,T,delta,z0; actual frozen stopped predicate. |
| `sb_numerics` | `p14:sb-numerics` | PASS | Every N1–N7 rational and the unused source chain are present. |
| `sb_chart` | `p14:sb-chart` | PASS | Actual frozen formulas; positive radius follows from positive mass/action and e<1. |
| `sb_cov` | `p14:sb-cov` | PASS | All-point strengthening survives total divisions/sqrt; omitted scalar equalities unfold from invariant Gamma and unchanged actions. |
| `sb_s` | `p14:sb-S, sb-Sdef` | PASS | Open S and required safe geometry; quantitative intermediate radii/radicand are internal Region obligations. |
| `sb_smooth_prop` | `p14:sb-smooth-prop` | PASS | Integral identity/smooth integrand split into next two helpers; literal SecularRegular. |
| `secular_integrand_identity` | `p14:sb-sm-1` | PASS | Exact frozen integrand after assemble; no assumed alternative average. |
| `secular_integrand_smooth` | `p14:sb-smooth-prop(b)` | PASS | Joint C∞ and global F periodicity. |
| `sb_rot` | `p14:sb-rot` | PASS | S membership and exact averaged-Hamiltonian invariance. |
| `sb_pred` | `p14:sb-pred` | PASS | Frozen Iso predicate; C2/C1 supplied by Smooth and ODE/Hamiltonian. |
| `sb_field` | `p14:sb-field` | PASS | Zero fast-action velocity and AMD derivative cancellation; other components in next helper. |
| `secular_field_components` | `p14:sb-fd-1` | PASS | Fast angle derivative and reduced slow field in correct coordinate order. |
| `sb_slow` | `p14:sb-slow` | PASS | Actual reduced flow in open slice and conserved AMD; no unbounded-angle compactness claim. |
| `sb_global` | `p14:sb-global` | PASS | Global frozen solution predicate, S membership, exact constants of motion. |
| `sb_unique` | `p14:sb-unique` | PASS | Agreement-set proof supports dropping competitor regularity. |
| `amd` | `p14:amd; p0:amd` | PASS | Frozen telescope, formatting normalized. |
| `expsafe` | `p14:expsafe; p0:expsafe` | PASS | Frozen telescope; constants before mu,z0. |
| `sb_safety` | `p14:sb-safety` | PASS | Frozen telescope including competitor regularity and every F. |
| `sb_cited` | `p14:sb-cited` | PASS | Exact rational specialization. |
| `Provider.Planetary.amdConfinement` | `p14:amd; p0:amd` | PASS | Exact frozen provider telescope. |
| `Provider.Planetary.planetaryExponentialSafety` | `p14:expsafe; p0:expsafe` | PASS | Exact frozen provider telescope. |
| `Provider.Planetary.secularBoxSafety` | `p14:sb-safety` | PASS | Exact frozen provider telescope. |
| `Provider.Planetary.secularBoxAtCitedMasses` | `p14:sb-cited` | PASS | Exact frozen provider telescope. |

## Definition and structure verdict

**PASS.** All 20 new definition/structure declarations were inspected on their full carriers:

| Objects | Verdict and reason |
|---|---|
| `amdOuter`, `amdInner`, `amdCollar`, `amdCompact` | Literal LowAMD wrappers and geometric inequalities; compact set imposes no unbounded angle coordinates. |
| `negativeEnergyDomain` | Exactly positive radii and negative Kepler energies; no unnecessary positivity premise needed for its continuity statement. |
| `chartAMD`, `chartSafe`, `fastBox`, `slowBall`, `enlargedCylinder`, `workingCylinder` | Correct fast/slow order and quadratic sum; general-n physical bridge is explicitly assigned to E1. |
| `EnlargedData` | Only the geometric E1–E3 conditions plus positivity/enlargement inequalities. No analytic extension, stopped bound or confinement conclusion is a field. |
| `planetaryKeplerC` | Exact sum with factor 1/2; zero-coordinate total values are excluded from derivative use by the positive action tube. |
| `periodicOrbitSet`, `complexTube` | Actual fast-shift orbit and open max-norm tube; meaningful for empty K. |
| `sb_sdef`, `secularRotation`, `sb_omega`, `reducedSecularH` | Exact region inequalities; slow rotation with the correct xi/eta order; fast-action derivative; affine lambda-zero reduction. |
| `explicitSecularIntegrand` | Actual full moving Hamiltonian and Jacobian product; `secular_integrand_identity` supplies equality to the frozen integrand. |

No global instance on bare function or matrix types was introduced. All-point covariance and lambda independence are algebraic statements, so no junk-value argument is needed outside the elliptic domain. Smoothness and integral use remain guarded by S and SecularRegular.

## Frozen objects and exact targets

**PASS.** Read the actual frozen bodies used by these contracts: Phase, fast/slow/assemble/fastShift; Hamiltonian vector field; Iso and Nekhoroshev solution predicates; moving/Newton solution and uniqueness predicates; Kepler/AMD/box objects; barycentric maps; all explicit secular chart/integrand/average/regularity objects; actionNbhd, complexifyPhase, innerCore, HasDefiniteFastPart, IsPartialPerturbation and the two N exponents.

No parallel solution or secular-Hamiltonian definition is assumed equal. The new auxiliary chartAMD has an explicit bridge; the new explicit integrand has an explicit bridge. Read-only text comparison with declaration-name boundaries confirms all eight library/provider telescopes are byte-identical to the four frozen theorem types, as claimed in the handoff.

N's exact frozen root was read at `KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean`. Its HasDefiniteFastPart and curried Hessian norm agree with the intended application. No frozen-definition defect or new pinned-source erratum was found. No frozen file or manifest was edited.

## Consumer verdict

**PASS for application shape, subject to F1–F5 contract repairs and future proofs.** No claimed proof availability is inferred from this verdict.

- AMD: `ecc_bound` needs every nonnegative deficit, so its global ProgradeElliptic premise is appropriate. The stopped bound is tested only on already-safe segments. Closure and compact continuation must give a solution strictly beyond ±T to supply the frozen two-sided endpoint derivatives. The proposed route does that; it never assumes whole-window safety.
- N application in E11: n is the planet count, k=n, G=`fastBox B kappa`, G'=`fastBox B (2*kappa)`, D=`slowBall n A`. Open/convex boxes, open slow ball, h-data, both perturbation signs, queried-time slow erosion, initial fast erosion, arbitrary positive segment duration and time reversal match the literal frozen N telescope. The max-norm slow perturbation costs sqrt(2n); the formula for epsD accounts for it. Exponents use n, not 2n. F1 blocks source-fidelity approval, but does not by itself prevent the N call at a fixed rho.
- Chart/physical boundary: `Phase (n+n)` and `Phase (n*2)` require the existing phaseCast/poincareProdCast bridge. The design names it explicitly and does not pretend definitional equality. General-n dictionary work is assigned componentwise; no Fin 2 supplier is instantiated at arbitrary n.
- Secular consumers: S gives open-domain regularity; slow trajectories stay on the compact AMD sphere at fixed fast actions. Quadrature supplies the unbounded angles. The actual frozen Iso predicate is used. The stronger uniqueness helper is valid via the relatively open/closed agreement set and does not need competing-curve regularity. Positive mu may be dropped in these helper results because it changes only coefficients/speeds; the final frozen premise is retained.
- Required cross-track search: direct N-Part-3 references were inspected in I Parts 5/7/8 and P Parts 1/6/11b/14a/14b. The prescribed N Parts 7/11a/11b/11c/12 have no direct `\Nref{bpN:p3:` occurrences in this snapshot. None of those external consumers directly cites a P14 label; P14 is a consumer of the shared ODE layer, not its replacement. Its new uniform-data result addresses the radian fast sub-block that the existing full-block period-one helper cannot directly cover.

## Packages and remaining notes

**Package verdict: PASS.** The A0–A6, E0–E12, S0–S12 DAG is acyclic. Planned ordinary modules have 150–750 lines; wrapper packages remain tiny and do not import one another. The 712-line scratch file and every planned module are below 1500 lines. No heartbeat, recursion-depth or synthesis override is used. No implementation module is assigned an import of a quarantined provider or draft frozen theorem.

**N1 — Medium, implementation risk.** Real-analytic complexification, real-trace uniqueness on intersections and Ck parameter-integral induction are substantial new obligations. Their signatures appear mathematically valid, including the zero-dimensional/empty-compact cases. A sorry-bearing file imported through Mathlib does not establish their feasibility at the default resource limits. Proposed action: prove E5/E6 and S4 before committing dependent prover waves; split files if needed, preserving the stated caps.

**N2 — Medium, upstream availability.** The N root was still sorry-bearing in the inspected frozen source, and remains a proof-release prerequisite for E11. The design correctly treats it as a dependency, with no extra premise on expsafe. Wait for its ordinary proof export or sealed anchor; do not use a provider import to bypass quarantine.

## Verification and closeout

The signatures were elaborated exactly once with `LEAN_NUM_THREADS=1`, `nice -n 5`, default resources, via the existing shared signature gate. The gate runs `lake env lean` from `/root/code/KAM-inp` against shared compiled imports because this design worktree has no private build overlay. No lake build, clean, update or cache download was run. This is the design-only targeted elaboration check; there are no new production modules to build.

```text
inp_sig_check.sh /root/code/KAM-inp-design-p14 .drafts/scratch/P14Signatures.lean
exit 0
47 warnings: declaration uses sorry
0 other diagnostics
```

A separate ABI-scratch probe copied the existing four-root axiom probe and checked every explicitly named Mathlib supplier in the graph/reuse tables: compact thickening, compactness, chain rule, global constancy, division, multiplication, dominated parameter differentiation, scalar restriction, periodic interval integral and FTC. The only unknown name claimed by the design was the FTC name in F5; division and constancy have the type limitations recorded there. A speculative `Convex.is_const_of_deriv_eq_zero` check also failed, as reported, and is not attributed to the designer.

```text
#print axioms KAM.Planetary.amd
#print axioms KAM.Planetary.expsafe
#print axioms KAM.Planetary.sb_safety
#print axioms KAM.Planetary.sb_cited
all four: [propext, sorryAx, Classical.choice, Quot.sound]
```

These are independently rerun admitted-design receipts, not proof closure. The ABI probe exited 1 because of the deliberate missing-name checks. A second ABI-scratch probe elaborated all eight proposed replacement statements, together with the 20 original auxiliary definitions/structure: exit 0, eight sorry warnings, no errors. It also confirmed `Convex.is_const_of_fderivWithin_eq_zero` with the required convex-set type. This check validates the replacement statement syntax and carriers only; their proofs were not attempted.

Lint was independently rerun, sequentially after the name probe, with the existing gate adapter:

```text
PATH="$PWD/.drafts/gated-bin:$PATH" LEAN_NUM_THREADS=1 scripts/lint_sources.sh
exit 0
check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The only persistent repository change is this report. `git diff --check` exited 0; original signatures and design hashes were rechecked unchanged.

Mechanical checks: Appendix A equals the original signatures; 47/47 theorem rows and 20/20 definition/structure declarations accounted for; 182/182 graph IDs present with no missing/extra scoped IDs; all eight frozen-target types match after whitespace normalization. No source erratum is asserted; F1–F5 are design/interface findings. No source claim was repaired or frozen premise changed. Approval is withheld until the findings are reconciled and the revised signatures are independently rechecked.
