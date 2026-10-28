# Lean design for blueprint-N Part 2: quasi-convexity and zero perturbation

Design N2, 2026-10-28. Planning evidence only; no new proofs, freezes or provider changes.
Scope: every graph node whose statement or proof is sourced from `blueprint-N/parts/p2-qc-zero.tex`.
Checkout baseline: `081967912d5200ad4711d6d16abde6a8cfafea71`, branch `inp-design-n2`.
Part 2 SHA-256: `ed9954f4a8313436ba58be47d1f061022b49cdf3ad04ba72b0c9467412dce73d`.
Format model read: `PART145-LEAN-DESIGN.md` and both `PART145-design-audit-{1,2}.md`.

## Decisions

1. Reuse the implemented `KAM/Nekhoroshev/QuasiConvex.lean` and `ZeroPerturbation.lean`.
   Their `isoenergetic_bijective_of_qc` and `zero_perturbation_core` already prove the exact frozen conclusions.
   The graph marks the corresponding anchors PROVED, and their current source bodies call their providers.
   The brief classifies this assignment as infrastructure with **no frozen theorem closure**. Respect that:
   the new work exposes missing infrastructure and source-step receipts, without resealing either theorem.
2. The general `qc_kernel` is genuinely weaker in hypotheses than the existing analytic theorem:
   arbitrary real matrix, no symmetry, no norm bound, nonvanishing quadratic form on the perpendicular
   hyperplane, `freq ≠ 0`, and `lam ≠ 0` of either sign. Do not replace it by
   `isoenergetic_injective`, whose hypotheses require an actual C² Hessian and positivity.
3. Use a continuous linear map `bordered_map`, built from existing CLM projections, finite sums and products.
   This gives a typed kernel and a direct `HasFDerivAt` target. The coordinate helper
   `real_hessian_matrix` is the matrix of the frozen real Hessian, not a second Hessian predicate.
4. Preserve all dimensions for the analytic results. The matrix lemma drops the redundant premise `1 ≤ n`:
   `freq ≠ 0` already implies it. `n0` states `U = ∅` from frozen quasi-convexity at dimension zero.
   Never add a dimension premise to N-QC or N-ZERO.
5. Prove the zero-field formula on **all** `Wdom n R s`, not merely `actionBall n R`.
   Existing `perturbation_zero_real` and `realHamiltonian_eq_realPart` only cover the smaller action ball;
   they do not by themselves supply the full graph contract. Use Part 1's exact `holo_real_e`
   with `Data n R s 0 h f`, plus its domain bridge, then differentiate a local equality.
6. Every new theorem below has a `sorry` body only in the untracked design draft, as expressly required
   by DESIGN-COMMON. Production implementations must be complete, and the ordinary ban on nonfrozen
   production `sorry` remains binding. No new production Lean file is written in this assignment.

## Carriers and standing structures

| Object | Exact existing object or explicit coordinate helper |
|---|---|
| Real and complex actions | `Fin n → ℝ`, `Fin n → ℂ`, with their existing max norms |
| Real phase points | `(Fin n → ℝ) × (Fin n → ℝ)`, angles first |
| Integrable real function | frozen `realPart h` |
| Frequency | frozen `KAM.frequencyMap h I`, real derivatives on coordinate vectors |
| Quasi-convexity | frozen `IsStrictlyQuasiConvex U h m`, including `m > 0`, open U, C², nonzero frequency and max-norm coercivity |
| Hessian coordinates | `real_hessian_matrix h I i j = fderiv ℝ (fderiv ℝ (realPart h)) I (Pi.single i 1) (Pi.single j 1)` |
| Kernel operator | `bordered_map freq A lam : ((Fin n → ℝ) × ℝ) →L[ℝ] (ℝ × (Fin n → ℝ))` |
| Enlarged real domain | existing `Wdom n R s = Set.univ ×ˢ Metric.ball 0 (R+s)` |
| Analytic premises | existing `Data n R s 0 h f`, assembled by its four fields `hR`, `hs`, `hh`, `hf` |
| Real dynamics | frozen `KAM.realHamiltonian`, `KAM.hamiltonianVectorField`, `IsSolutionOn`, `integrableOrbit` |

No standing axiom, new class, global norm instance, alternate solution predicate or frequency representation.
The two helper definitions have real bodies, exposed for unfolding. Matrix entries are simply coordinates of
an existing derivative; `qd_sym` proves the reconstruction and symmetry used by all consumers.

## Every node mapped to a declaration

All unqualified Lean names are in `KAM.Nekhoroshev`. New module names in the last column mean
`KAM/Nekhoroshev/QcZero/<name>.lean`. Statement and proof columns retain the graph's exact locators;
these are authoritative even where two graph nodes map to one declaration or one conjunct.
The two Part-0 rows are included because their proof source is Part 2. All Part-2 graph records are included.

| Node | Lean declaration | Statement locator | Proof locator | Module; exact inputs / reuse |
|---|---|---|---|---|
| `bpN:p0:zero` | `zero_perturbation_core` | `p0-conventions.tex#bpN:p0:zero` @ L239-L246 | `p2-qc-zero.tex#bpN:p2:zero` @ L87-L97 | existing ZeroPerturbation; Existing SEALED anchor zero_perturbation; no provider work |
| `bpN:p0:qcthm` | `isoenergetic_bijective_of_qc` | `p0-conventions.tex#bpN:p0:qcthm` @ L248-L257 | `p2-qc-zero.tex#bpN:p2:qc-bij` @ L53-L61 | existing QuasiConvex; Existing SEALED anchor quasiConvex_isoenergetic_derivative; no provider work |
| `bpN:p2:qc-kernel` | `qc_kernel` | `p2-qc-zero.tex#bpN:p2:qc-kernel` @ L11-L18 | `p2-qc-zero.tex#bpN:p2:qc-kernel` @ L19-L27 | Kernel; qk_pair, qk_scalar; finite-dimensional linear algebra |
| `stepN:p2:qk-eqs` | `qk_eqs` | `p2-qc-zero.tex#stepN:p2:qk-eqs` @ L20-L20 | `p2-qc-zero.tex#stepN:p2:qk-eqs` @ L20-L20 | Kernel; bordered_map_apply; Prod.mk_eq_zero |
| `stepN:p2:qk-pair` | `qk_pair` | `p2-qc-zero.tex#stepN:p2:qk-pair` @ L22-L22 | `p2-qc-zero.tex#stepN:p2:qk-pair` @ L22-L22 | Kernel; qk_eqs; finite sums and lam ≠ 0 |
| `stepN:p2:qk-scalar` | `qk_scalar` | `p2-qc-zero.tex#stepN:p2:qk-scalar` @ L24-L24 | `p2-qc-zero.tex#stepN:p2:qk-scalar` @ L24-L24 | Kernel; qk_pair, qk_eqs; nonzero coordinate of freq |
| `stepN:p2:qk-bij` | `qc_kernel (second conjunct)` | `p2-qc-zero.tex#stepN:p2:qk-bij` @ L26-L26 | `p2-qc-zero.tex#stepN:p2:qk-bij` @ L26-L26 | Kernel; qk_pair, qk_scalar; LinearMap.injective_iff_surjective_of_finrank_eq_finrank |
| `bpN:p2:n0` | `n0` | `p2-qc-zero.tex#bpN:p2:n0` @ L29-L31 | `p2-qc-zero.tex#bpN:p2:n0` @ L29-L31 | QCResults; IsStrictlyQuasiConvex; Subsingleton.elim on Fin 0 → ℝ |
| `bpN:p2:qc-deriv` | `qc_deriv` + `qd_sym` | `p2-qc-zero.tex#bpN:p2:qc-deriv` @ L33-L37 | `p2-qc-zero.tex#bpN:p2:qc-deriv` @ L38-L46 | Derivative; hasFDerivAt_isoenergetic, qd_sym, bordered_map_apply |
| `stepN:p2:qd-first` | `qd_first` | `p2-qc-zero.tex#stepN:p2:qd-first` @ L39-L39 | `p2-qc-zero.tex#stepN:p2:qd-first` @ L39-L39 | Derivative; clm_apply_eq_sum; hasFDerivAt_isoenergetic first component |
| `stepN:p2:qd-freq` | `qd_freq` | `p2-qc-zero.tex#stepN:p2:qd-freq` @ L41-L41 | `p2-qc-zero.tex#stepN:p2:qd-freq` @ L41-L41 | Derivative; ContDiffOn.fderiv_of_isOpen; ContinuousLinearMap.apply; hasFDerivAt_pi |
| `stepN:p2:qd-sym` | `qd_sym` | `p2-qc-zero.tex#stepN:p2:qd-sym` @ L43-L43 | `p2-qc-zero.tex#stepN:p2:qd-sym` @ L43-L43 | Derivative; qd_freq; ContDiffAt.isSymmSndFDerivAt; clm_apply_eq_sum twice |
| `stepN:p2:qd-prod` | `qd_prod` | `p2-qc-zero.tex#stepN:p2:qd-prod` @ L45-L45 | `p2-qc-zero.tex#stepN:p2:qd-prod` @ L45-L45 | Derivative; HasFDerivAt.smul; qd_freq, qd_sym |
| `bpN:p2:qc-bij` | `qc_bij` | `p2-qc-zero.tex#bpN:p2:qc-bij` @ L48-L52 | `p2-qc-zero.tex#bpN:p2:qc-bij` @ L53-L61 | QCResults; isoenergetic_bijective_of_qc (existing exact result) |
| `stepN:p2:qb-unpack` | `qb_unpack` | `p2-qc-zero.tex#stepN:p2:qb-unpack` @ L54-L54 | `p2-qc-zero.tex#stepN:p2:qb-unpack` @ L54-L54 | QCResults; IsStrictlyQuasiConvex; n0 |
| `stepN:p2:qb-deriv` | `qb_deriv` | `p2-qc-zero.tex#stepN:p2:qb-deriv` @ L56-L56 | `p2-qc-zero.tex#stepN:p2:qb-deriv` @ L56-L56 | QCResults; qc_deriv, qb_unpack; HasFDerivAt.fderiv |
| `stepN:p2:qb-pos` | `qb_pos` | `p2-qc-zero.tex#stepN:p2:qb-pos` @ L58-L58 | `p2-qc-zero.tex#stepN:p2:qb-pos` @ L58-L58 | QCResults; qb_unpack; qd_sym quadratic identity; norm_pos_iff |
| `stepN:p2:qb-concl` | `qc_bij` | `p2-qc-zero.tex#stepN:p2:qb-concl` @ L60-L60 | `p2-qc-zero.tex#stepN:p2:qb-concl` @ L60-L60 | QCResults; isoenergetic_bijective_of_qc; alternate source route qc_kernel, qb_deriv, qb_pos |
| `bpN:p2:zero-deriv` | `zero_deriv` | `p2-qc-zero.tex#bpN:p2:zero-deriv` @ L69-L73 | `p2-qc-zero.tex#bpN:p2:zero-deriv` @ L74-L80 | ZeroField; zd_zero, zd_diff, zd_field |
| `stepN:p2:zd-zero` | `zd_zero` | `p2-qc-zero.tex#stepN:p2:zd-zero` @ L75-L75 | `p2-qc-zero.tex#stepN:p2:zd-zero` @ L75-L75 | ZeroField; holo_real_e; realInclusion₂_preimage_complexDomain |
| `stepN:p2:zd-diff` | `zd_diff` | `p2-qc-zero.tex#stepN:p2:zd-diff` @ L77-L77 | `p2-qc-zero.tex#stepN:p2:zd-diff` @ L77-L77 | ZeroField; zd_zero; realActionDomain_eq; isOpen_Wdom; HasFDerivAt.comp; Filter.EventuallyEq.fderiv_eq |
| `stepN:p2:zd-field` | `zd_field` | `p2-qc-zero.tex#stepN:p2:zd-field` @ L79-L79 | `p2-qc-zero.tex#stepN:p2:zd-field` @ L79-L79 | ZeroField; zd_diff; frozen hamiltonianVectorField, frequencyMap |
| `bpN:p2:zero` | `zero` | `p2-qc-zero.tex#bpN:p2:zero` @ L82-L86 | `p2-qc-zero.tex#bpN:p2:zero` @ L87-L97 | ZeroOrbit; zero_perturbation_core (existing exact result) |
| `stepN:p2:z-init` | `z_init` | `p2-qc-zero.tex#stepN:p2:z-init` @ L88-L88 | `p2-qc-zero.tex#stepN:p2:z-init` @ L88-L88 | ZeroOrbit; frozen integrableOrbit; zero_smul, zero_add |
| `stepN:p2:z-ball` | `z_ball` | `p2-qc-zero.tex#stepN:p2:z-ball` @ L90-L90 | `p2-qc-zero.tex#stepN:p2:z-ball` @ L90-L90 | ZeroOrbit; frozen actionBall; R/2 < R |
| `stepN:p2:z-H` | `z_h` | `p2-qc-zero.tex#stepN:p2:z-H` @ L92-L92 | `p2-qc-zero.tex#stepN:p2:z-H` @ L92-L92 | ZeroOrbit; z_ball, z_init, zero_deriv; ball_subset_realActionDomain |
| `stepN:p2:z-curve` | `z_curve` | `p2-qc-zero.tex#stepN:p2:z-curve` @ L94-L94 | `p2-qc-zero.tex#stepN:p2:z-curve` @ L94-L94 | ZeroOrbit; hasDerivAt_id'; HasDerivAt.smul_const, const_add, prodMk; hasDerivAt_const |
| `stepN:p2:z-eq` | `z_eq` | `p2-qc-zero.tex#stepN:p2:z-eq` @ L96-L96 | `p2-qc-zero.tex#stepN:p2:z-eq` @ L96-L96 | ZeroOrbit; z_h, z_curve, zd_field; frozen IsSolutionOn |

The `qk-bij` row is the second conjunct of `qc_kernel`; no separate wrapper is needed.
`qb-concl` and `qc-bij` share `qc_bij`. Already proved step `qd-first` stays mapped to
`clm_apply_eq_sum` / `hasFDerivAt_isoenergetic` as well as the named coordinate receipt `qd_first`.
No graph-status changes are made by this design. New `sorry` statements are not proof receipts.

## Conventions and exact reuse

- Dot products are finite sums `∑ i, freq i * v i`; ambient norms stay max norms.
  `∑ i, ∑ j, v i * A i j * v j` is the literal nonsymmetric quadratic form.
- Hessian orientation matters: differentiating the i-th frequency gives `D²h[I][v,e_i]`.
  Our matrix is `Q i j = D²h[I][e_i,e_j]`. Use Schwarz before identifying this with `Qv`.
  `qd_sym` includes the quadratic identity explicitly, so no unproved matrix/Hessian equality is assumed.
- `qc_deriv` concludes `HasFDerivAt`; its `.differentiableAt` and `.fderiv` give both clauses of the
  blueprint. It holds at arbitrary real `lam`, including zero. Only `qc_kernel` needs `lam ≠ 0`.
- `hasFDerivAt_isoenergetic (realPart h) lam` takes a `ContDiffAt ℝ 2` proof.
  Supply `hh.contDiffAt (hU.mem_nhds hI)` from the stated source premises.
  Its derivative uses the evaluation orientation above; `qd_sym` is the bridge to the matrix form.
- `isoenergetic_bijective_of_qc hqc hI hlam` directly supplies `qc_bij` with exactly the same
  variables; use it as the implemented analytic route. The source route through `qc_kernel` remains
  available to future users. Reusing that theorem does not establish the newly generalized matrix lemma.
- `zero_perturbation_core hR hs hh hf theta0 I0 hI` directly supplies `zero`.
  `z_eq` is its solution conjunct. Reuse these rather than duplicating the completed proof.
- `IsSolutionOn` requires action membership, differentiability of H, and two-sided `HasDerivAt` at
  each visited point. `z_h` and `z_curve` retain those guards; `z_eq` includes all three.
- `z_init` and `z_curve` are algebraic/affine statements for arbitrary h. The latter needs no
  differentiability of h, because the fixed vector `frequencyMap h I0` is constant in time.
- Binder safety: section hypotheses are included explicitly in the signatures. In particular the
  C²/open-set assumptions of `qc_deriv` and all analytic assumptions of `zero_deriv` survive elaboration.
  `omit` removes unrelated analytic premises only for the algebraic orbit receipts.
- Period is 1 throughout, but no Fourier character or period conversion enters this part.

## Upstream interface (to reconcile)

No pending neighboring-part interface is invented. All needed Part-1 interfaces have exact existing
names and implementations in this checkout and in the shared `inp` build used by the signature gate.
Parts 3–7 supply no prerequisite for these results.

| Owning part / module | Exact declaration and shape consumed | Inputs supplied here |
|---|---|---|
| N1 `Interfaces/Setting` | `Data n R s 0 h f`; `Wdom n R s` | `Data.mk hR hs hh hf` |
| N1 `Interfaces/Domains` | `realActionDomain_eq hR hs : realActionDomain n R s = Metric.ball 0 (R+s)` | R,s positive |
| N1 `Interfaces/Domains` | `realInclusion₂_preimage_complexDomain hR hs : KAM.realInclusion₂ n ⁻¹' complexDomain n R s = Wdom n R s` | R,s positive; membership in Wdom |
| N1 `Interfaces/Domains` | `isOpen_Wdom (R s : ℝ)`; `ball_subset_realActionDomain hR hs` | R,s; positive widths for inclusion |
| N1 `Interfaces/HoloReal` | `holo_real_e hd : (∀ w ∈ complexDomain n R s, f w = 0) ∧ ∀ z ∈ Wdom n R s, KAM.realHamiltonian h f z = realPart h z.2` | exact Data record above |
| Existing N2 `QuasiConvex` | `clm_apply_eq_sum φ v`; `hasFDerivAt_isoenergetic g lam hg` | realPart h, local C² |
| Existing N2 `QuasiConvex` | `isoenergetic_bijective_of_qc hqc hI hlam` | frozen QC premise, I membership, positive lam |
| Existing N2 `ZeroPerturbation` | `zero_perturbation_core hR hs hh hf theta0 I0 hI` | exact frozen zero-theorem inputs |
| Mathlib `FDeriv/Symmetric` | `ContDiffAt.isSymmSndFDerivAt` | local C²; source point in open U |
| Mathlib finite dimension | `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` | dimensions n+1 = 1+n; trivial kernel |

`Data` and `Wdom` belong to `KAM.Nekhoroshev`, not an `ODE` subnamespace. Do not recreate them.
For I reuse, export `qc_kernel` in this namespace, but require no change to I's delivered signatures.
The current I Part 3 explicitly says it does not need this kernel argument; the N2 introduction's
claim that I cites it is stale (see issues below).

## Modules and import DAG

All paths below are exact planned production files. Each has the standard copyright, `module`,
`public import`, module docstring and `public section`; expose definitions that must unfold.
Existing public paths remain intact; no refactoring of a sealed provider's dependencies is necessary.

| Module | Imports beyond Mathlib / frozen definitions | Estimated final lines |
|---|---|---:|
| `KAM/Nekhoroshev/QcZero/Kernel.lean` | no existing N implementation; CLM finite-dimensional APIs | 250–400 |
| `KAM/Nekhoroshev/QcZero/Derivative.lean` | `KAM.Nekhoroshev.QuasiConvex`, `KAM.Nekhoroshev.QcZero.Kernel` | 250–450 |
| `KAM/Nekhoroshev/QcZero/QCResults.lean` | `KAM.Nekhoroshev.QcZero.Derivative` | 150–250 |
| `KAM/Nekhoroshev/QcZero/ZeroField.lean` | `KAM.Nekhoroshev.Interfaces.HoloReal` | 200–350 |
| `KAM/Nekhoroshev/QcZero/ZeroOrbit.lean` | `KAM.Nekhoroshev.QcZero.ZeroField`, `KAM.Nekhoroshev.ZeroPerturbation` | 150–250 |

`real_hessian_matrix` lives in Derivative, `bordered_map` in Kernel. Kernel does not import Derivative.
`QCResults` never feeds back into existing QuasiConvex; ZeroField never imports ZeroOrbit.
No file imports a provider or a DRAFT_SORRY theorem anchor. Existing implementation modules imported
by the signatures follow the same quarantine. No generated root or README edit is planned here.
The single draft is under 1500 lines; production estimates are well below the cap.

## Packages and waves

Each package is one prover session, 150–800 estimated lines, and owns exactly its module above.
All estimates include documentation and small supporting lemmas; do not pad to meet an estimate.

| Package | Wave | Inputs named | Work / output |
|---|---:|---|---|
| N2-KERNEL | 1 | frozen coordinate carrier; CLM projections; finite-dimensional injective/surjective theorem | `bordered_map`, application formula, qk equations/pair/scalar, `qc_kernel`; 250–400 lines |
| N2-ZFIELD | 1 | N1 `Data`, `Wdom`, `holo_real_e`, domain identities; frozen C³ clause of `IsAnalyticIntegrable` | zd receipts and `zero_deriv`; 200–350 lines |
| N2-DERIV | 2 | N2-KERNEL; `hasFDerivAt_isoenergetic`, `clm_apply_eq_sum`; C² Schwarz | matrix helper, qd receipts, `qc_deriv`; 250–450 lines |
| N2-ZORBIT | 2 | N2-ZFIELD; existing `zero_perturbation_core`; frozen orbit / solution predicates | z receipts, `z_eq`, `zero`; 150–250 lines |
| N2-QC | 3 | N2-DERIV; existing `isoenergetic_bijective_of_qc`; frozen QC predicate | `n0`, qb receipts, `qc_bij`; 150–250 lines |

Proof plans:

- **N2-KERNEL:** expose the finite-sum application formula; project a zero output into the two
  kernel equations. Multiply each coordinate of the second equation by v_i and sum to get
  `lam * (∑ i, ∑ j, v i * A i j * v j) = 0`. Use `lam ≠ 0`, then the quadratic nonvanishing
  premise to force v=0. A nonzero coordinate of freq forces u=0. Prove trivial kernel, then
  use finrank equality (product dimensions n+1 and 1+n) for surjectivity. Do not use matrix symmetry.
- **N2-DERIV:** localize C² with open U, use existing derivative calculation and basis expansion.
  Prove frequency C¹ using derivative regularity and continuous linear evaluation. Schwarz switches
  `[v,e_i]` to `[e_i,v]`, then expand v. Expand both variables for the quadratic form identity.
  Prove first/product receipts independently from their rules, and identify the full CLM by extensionality.
- **N2-QC:** unpack the literal frozen predicate; nonzero frequency rules out n=0. Use the quadratic
  identity with `m * ‖v‖² > 0` for `qb_pos`. Existing exact analytic theorem supplies `qc_bij`;
  the stronger matrix lemma is not asserted proved by this reuse.
- **N2-ZFIELD:** build Data from exactly the four source premises. `holo_real_e` and the preimage
  domain identity give vanishing and equality on Wdom. For z in Wdom obtain an eventual equality in
  `𝓝 z` from its openness. The frozen C³ clause, `realActionDomain_eq` and projection composition
  give a genuine derivative; transfer it by eventual equality, then evaluate it on coordinate vectors
  in the frozen field. Package all statements in `zero_deriv`.
- **N2-ZORBIT:** use affine `HasDerivAt` rules; no ODE theorem needed. Radius R/2 gives membership
  in radius R, hence Wdom. Apply the field receipt along the orbit and retain differentiability.
  For the full frozen-shaped result reuse `zero_perturbation_core`, and take its solution conjunct
  for `z_eq`; the smaller receipts document the source route and support enlarged-domain consumers.

## Provider assembly

None is assigned or modified. The sealed results already have exact implementations. As a consistency
check only, their current types are matched binder by binder by the two existing calls:

| Frozen result | Existing implementation call | Binder / conclusion correspondence |
|---|---|---|
| `quasiConvex_isoenergetic_derivative` | `isoenergetic_bijective_of_qc hqc hI hlam` | implicit n,U,h,m,I,lam unchanged; QC premise, membership, positivity; same fderiv of `(realPart h, lam • frequencyMap h)` |
| `zero_perturbation` | `zero_perturbation_core hR hs hh hf theta0 I0 hI` | implicit n,R,s,h,f unchanged; R,s positive, integrable, size-zero perturbation, both initial coordinates and radius-R/2 membership; identical initial/solution/constant-action conjunction |

The scratch imports the implementation modules only, not the anchors or providers. New `qc_bij` and
`zero` are convenience names with these exact conclusions; they never substitute for a frozen anchor.
A design elaboration or design commit is not a new seal or proof of the matrix generalization.

## Departures

| ID | Location | Departure and reason |
|---|---|---|
| D-N2-1 | qc-kernel | Drop redundant `n ≥ 1`: a nonzero `Fin n → ℝ` forces this, so the theorem is strictly stronger and still true (vacuous at n=0). No positive-lam or symmetry assumption is added. |
| D-N2-2 | qk-pair | Drop unused freq-nonzero premise locally: the pairing argument only needs lam≠0 and quadratic nonvanishing. It is strictly stronger and the scalar step still requires freq≠0. |
| D-N2-3 | derivative / field lemmas | `HasFDerivAt` instead of a separate differentiability assertion plus fderiv identity; supplies both and avoids total-derivative ambiguity. |
| D-N2-4 | z-init, z-curve | Drop all analytic and radius premises: evaluation and time differentiation of the affine orbit are true for every total h. `z_ball` retains only hR and hI, its exact graph inputs. |
| D-N2-5 | qc-bij, zero | Use existing implementation routes; do not duplicate proof or provider assembly. Node table separately records the finer source receipts, including the general matrix gap and enlarged domain. |
| D-N2-6 | proof-step names | `stepN:p2:z-H` becomes snake-case `z_h`. `qk-bij` and `qb-concl` use a conjunct / shared theorem, not duplicated declarations. |

## Blueprint issues and suspected errata

1. **Scope wording:** p2 L4, “This part proves two frozen theorems completely”, is a blueprint description,
   whereas DESIGN-N2 assigns no new frozen closure. Both are already sealed in this snapshot; the design
   preserves that distinction. No frozen statement is defective and no edit is proposed.
2. **Stale I consumer claim:** p2 L5–6, “cited by track I as the isoenergetic gate”, conflicts with
   `blueprint-I/parts/p3-iso-local-charts.tex` L415: “the nonsingular-derivative argument of track N ... is not needed.”
   No delivered I signature references `qc_kernel`. Treat the N lemma as reusable infrastructure, without
   claiming an active I proof dependency. This is blueprint coordination, not a pinned-paper erratum.
3. **Coverage of existing code:** the blueprint `zero-deriv` L70–72 ranges over W_s. Existing smaller-ball
   equality lemmas cannot discharge it. The enlarged-domain result is an explicit new proof obligation.
4. **No pinned-paper defect identified.** BM11 is cited by the blueprint at Lemma 3.3 pp.9–10, but this
   assignment inspects the supplied blueprint and existing implementations, not a fresh pinned-PDF audit.
   Do not interpret absence of a reported paper erratum as independent paper verification.
5. Graph `qb-deriv` lists `qc-kernel` as a dependency, although it uses only its explicit operator form;
   the DAG depends on Kernel definitions rather than its nonvanishing theorem. Keep the graph unchanged
   and explain this dependency granularity at integration. No circular proof is introduced.

## Risks and validation

- Highest statement risk: transposing the Hessian silently. `qd_sym` makes both symmetry and quadratic
  reconstruction explicit. Matrix nonvanishing is a source premise; no injectivity or inverse conclusion
  is smuggled into a hypothesis.
- Highest domain risk: differentiating equality at only a point. `zd_diff` uses equality on the open Wdom
  and C³ from the frozen definition, with `realActionDomain_eq` to establish the required neighborhood.
- No quantitative inverse radius is provided, uniform or otherwise. No uniqueness conclusion is added to
  N-ZERO, and no frequency lower bound or normal-form/ODE assumption is added anywhere.
- Elaborated signatures alone do not prove any new theorem. The probe reports `sorryAx` on `qc_kernel`,
  `qc_deriv`, `zero_deriv`; existing `isoenergetic_bijective_of_qc` and `zero_perturbation_core` report only
  `propext`, `Classical.choice`, `Quot.sound`.
- Serial validation uses only `inp_sig_check.sh`; no direct build or lean invocation. The required lint's
  ABI helper normally invokes Lean directly, so a task-local PATH adapter routes just that invocation
  through the same signature gate and restores PATH within the gate to avoid recursion. No lint script
  is edited. No production Lean module was authored, so a new-module targeted build is inapplicable;
  the required targeted signature elaboration is the compile check for this design.

Validation completed in this checkout:

- `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-n2 .drafts/scratch/N2Signatures.lean`:
  exit 0; exactly 25 `declaration uses 'sorry'` warnings, no other diagnostics.
- The same gate on `.drafts/scratch/N2InterfaceProbe.lean`: exit 0; actual binder checks and
  `#print axioms` outputs recorded in `.drafts/scratch/N2-interface-probe.log`.
- `scripts/lint_sources.sh` with the gate adapter: exit 0; `check_lean_modules: PASS
  (412 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (144 frozen declarations)`.
- Appendix A is byte-identical to the scratch and delivered signature files; all 28 graph rows are
  accounted for. The handoff records the final commit and artifact hashes.

## Hard rules for every implementation brief (verbatim)

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

Untracked deliverable: `/root/code/KAM-inp/.drafts/design/N2Signatures.lean`.
Checked copy: `.drafts/scratch/N2Signatures.lean`.
SHA-256 `6f0af532d88555f0dd089b07298270823eecafd6d46efa540eeda7f8ef87a57a`; 195 lines, 25 new theorem signatures, two explicit definitions.
All new proof bodies are `sorry`; imported implementations are reused under their original names.
The final check exits 0 with 25 `declaration uses 'sorry'` warnings and no other Lean diagnostics.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.QuasiConvex
public import KAM.Nekhoroshev.ZeroPerturbation
public import KAM.Nekhoroshev.Interfaces.HoloReal
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Part 2 signatures: bordered kernel, derivative identification and zero field
Design evidence only. Existing results are imported, never redeclared.
Every new theorem body is `sorry`; definitions have explicit bodies.
-/

@[expose] public noncomputable section

namespace KAM.Nekhoroshev

variable {n : ℕ}

/-- Coordinate matrix of the real Hessian; not the complex Hessian of Part 1. -/
def real_hessian_matrix (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ (realPart h)) I (Pi.single i 1) (Pi.single j 1)

/-- The linear map `(v,u) ↦ (freq·v, u freq + lam A v)`. -/
def bordered_map (freq : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) :
    ((Fin n → ℝ) × ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
  ((∑ i, (ContinuousLinearMap.proj i).smulRight (freq i)).comp
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ)).prod
    ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).smulRight freq +
      lam • (ContinuousLinearMap.pi fun i =>
        ∑ j, (ContinuousLinearMap.proj j).smulRight (A i j)).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ))

theorem bordered_map_apply (freq : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) (v : Fin n → ℝ) (u : ℝ) :
    bordered_map freq A lam (v, u) =
      (∑ i, freq i * v i, u • freq + lam • (fun i => ∑ j, A i j * v j)) := sorry

theorem qk_eqs (freq : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) (v : Fin n → ℝ) (u : ℝ)
    (hz : bordered_map freq A lam (v, u) = 0) :
    (∑ i, freq i * v i) = 0 ∧
      u • freq + lam • (fun i => ∑ j, A i j * v j) = 0 := sorry

theorem qk_pair (freq : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    {lam : ℝ} (hlam : lam ≠ 0)
    (hA : ∀ v : Fin n → ℝ, (∑ i, freq i * v i) = 0 → v ≠ 0 →
      (∑ i, ∑ j, v i * A i j * v j) ≠ 0)
    (v : Fin n → ℝ) (u : ℝ) (hz : bordered_map freq A lam (v, u) = 0) :
    v = 0 := sorry

theorem qk_scalar (freq : Fin n → ℝ) (hfreq : freq ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (hA : ∀ v : Fin n → ℝ, (∑ i, freq i * v i) = 0 → v ≠ 0 →
      (∑ i, ∑ j, v i * A i j * v j) ≠ 0)
    (v : Fin n → ℝ) (u : ℝ) (hz : bordered_map freq A lam (v, u) = 0) :
    u = 0 := sorry

theorem qc_kernel (freq : Fin n → ℝ) (hfreq : freq ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (hA : ∀ v : Fin n → ℝ, (∑ i, freq i * v i) = 0 → v ≠ 0 →
      (∑ i, ∑ j, v i * A i j * v j) ≠ 0) :
    LinearMap.ker (bordered_map freq A lam).toLinearMap = ⊥ ∧
      Function.Bijective (bordered_map freq A lam) := sorry

theorem n0 {U : Set (Fin 0 → ℝ)} {h : (Fin 0 → ℂ) → ℂ} {m : ℝ}
    (hqc : IsStrictlyQuasiConvex U h m) : U = ∅ := sorry

section Derivative
variable {U : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
variable (hU : IsOpen U) (hh : ContDiffOn ℝ 2 (realPart h) U)
variable {I : Fin n → ℝ} (hI : I ∈ U)
include hU hh hI

theorem qd_first (lam : ℝ) :
    DifferentiableAt ℝ (fun p : (Fin n → ℝ) × ℝ => realPart h p.1) (I, lam) ∧
    ∀ v u, fderiv ℝ (fun p : (Fin n → ℝ) × ℝ => realPart h p.1) (I, lam) (v, u) =
      ∑ i, KAM.frequencyMap h I i * v i := sorry

theorem qd_freq : ContDiffOn ℝ 1 (KAM.frequencyMap h) U ∧
    DifferentiableAt ℝ (KAM.frequencyMap h) I ∧
    ∀ v i, fderiv ℝ (KAM.frequencyMap h) I v i =
      fderiv ℝ (fderiv ℝ (realPart h)) I v (Pi.single i 1) := sorry

theorem qd_sym :
    (∀ i j, real_hessian_matrix h I i j = real_hessian_matrix h I j i) ∧
    (∀ v, fderiv ℝ (KAM.frequencyMap h) I v =
      fun i => ∑ j, real_hessian_matrix h I i j * v j) ∧
    ∀ v, (∑ i, ∑ j, v i * real_hessian_matrix h I i j * v j) =
      fderiv ℝ (fderiv ℝ (realPart h)) I v v := sorry

theorem qd_prod (lam : ℝ) :
    DifferentiableAt ℝ (fun p : (Fin n → ℝ) × ℝ => p.2 • KAM.frequencyMap h p.1)
      (I, lam) ∧
    ∀ v u, fderiv ℝ (fun p : (Fin n → ℝ) × ℝ => p.2 • KAM.frequencyMap h p.1)
      (I, lam) (v, u) = u • KAM.frequencyMap h I +
        lam • (fun i => ∑ j, real_hessian_matrix h I i j * v j) := sorry

theorem qc_deriv (lam : ℝ) :
    HasFDerivAt (fun p : (Fin n → ℝ) × ℝ =>
      (realPart h p.1, p.2 • KAM.frequencyMap h p.1))
      (bordered_map (KAM.frequencyMap h I) (real_hessian_matrix h I) lam) (I, lam) := sorry
end Derivative

section QuasiConvex
variable {U : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ} {m : ℝ}
variable (hqc : IsStrictlyQuasiConvex U h m) {I : Fin n → ℝ} (hI : I ∈ U)
include hqc hI

theorem qb_unpack : 0 < m ∧ IsOpen U ∧ ContDiffOn ℝ 2 (realPart h) U ∧
    KAM.frequencyMap h I ≠ 0 ∧ (1 ≤ n) ∧
    ∀ v : Fin n → ℝ, (∑ i, KAM.frequencyMap h I i * v i) = 0 →
      m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I v v := sorry

theorem qb_deriv (lam : ℝ) :
    fderiv ℝ (fun p : (Fin n → ℝ) × ℝ =>
      (realPart h p.1, p.2 • KAM.frequencyMap h p.1)) (I, lam) =
      bordered_map (KAM.frequencyMap h I) (real_hessian_matrix h I) lam := sorry

theorem qb_pos (v : Fin n → ℝ)
    (hv : (∑ i, KAM.frequencyMap h I i * v i) = 0) (hv0 : v ≠ 0) :
    0 < ∑ i, ∑ j, v i * real_hessian_matrix h I i j * v j := sorry

/-- Existing implementation `isoenergetic_bijective_of_qc` proves this exact conclusion. -/
theorem qc_bij {lam : ℝ} (hlam : 0 < lam) :
    Function.Bijective (fderiv ℝ (fun p : (Fin n → ℝ) × ℝ =>
      (realPart h p.1, p.2 • KAM.frequencyMap h p.1)) (I, lam)) := sorry
end QuasiConvex

section ZeroField
variable {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
variable {h : (Fin n → ℂ) → ℂ} (hh : IsAnalyticIntegrable R s h)
variable {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
variable (hf : IsAnalyticPerturbation R s 0 f)
include hR hs hh hf

/-- `Wdom`, from Part 1, is the enlarged domain, not just `actionBall n R`. -/
theorem zd_zero : (∀ w ∈ complexDomain n R s, f w = 0) ∧
    (∀ z ∈ Wdom n R s, KAM.realInclusion₂ n z ∈ complexDomain n R s) ∧
    ∀ z ∈ Wdom n R s, KAM.realHamiltonian h f z = realPart h z.2 := sorry

theorem zd_diff (z : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ Wdom n R s) :
    HasFDerivAt (KAM.realHamiltonian h f)
      ((fderiv ℝ (realPart h) z.2).comp
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))) z := sorry

theorem zd_field (z : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ Wdom n R s) :
    KAM.hamiltonianVectorField (KAM.realHamiltonian h f) z =
      (KAM.frequencyMap h z.2, 0) := sorry

theorem zero_deriv (z : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ Wdom n R s) :
    KAM.realHamiltonian h f z = realPart h z.2 ∧
    DifferentiableAt ℝ (KAM.realHamiltonian h f) z ∧
    (∀ a b, fderiv ℝ (KAM.realHamiltonian h f) z (a, b) =
      fderiv ℝ (realPart h) z.2 b) ∧
    KAM.hamiltonianVectorField (KAM.realHamiltonian h f) z =
      (KAM.frequencyMap h z.2, 0) := sorry

variable (theta0 I0 : Fin n → ℝ)

omit hR hs hh hf in
theorem z_init : integrableOrbit h theta0 I0 0 = (theta0, I0) ∧
    ∀ t : ℝ, (integrableOrbit h theta0 I0 t).2 = I0 := sorry

omit hs hh hf in
theorem z_ball (hI : I0 ∈ actionBall n (R / 2)) : I0 ∈ actionBall n R := sorry

theorem z_h (hI : I0 ∈ actionBall n (R / 2)) (t : ℝ) :
    (integrableOrbit h theta0 I0 t).2 ∈ actionBall n R ∧
    integrableOrbit h theta0 I0 t ∈ Wdom n R s ∧
    DifferentiableAt ℝ (KAM.realHamiltonian h f) (integrableOrbit h theta0 I0 t) := sorry

omit hR hs hh hf in
theorem z_curve (t : ℝ) : HasDerivAt (integrableOrbit h theta0 I0)
    (KAM.frequencyMap h I0, 0) t := sorry

theorem z_eq (hI : I0 ∈ actionBall n (R / 2)) :
    IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R) Set.univ
      (integrableOrbit h theta0 I0) := sorry

/-- Exact conclusion already proved by `zero_perturbation_core`. -/
theorem zero (hI : I0 ∈ actionBall n (R / 2)) :
    integrableOrbit h theta0 I0 0 = (theta0, I0) ∧
    IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R) Set.univ
      (integrableOrbit h theta0 I0) ∧
    ∀ t : ℝ, (integrableOrbit h theta0 I0 t).2 = I0 := sorry
end ZeroField

end KAM.Nekhoroshev
```
