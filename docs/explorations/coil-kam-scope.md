# Coil-produced magnetic fields: KAM scope and certificate plan

Date: 2026-11-10. Research and numerical feasibility report; no new Lean theorem.
Branch: `coil-kam-scope`; controlling brief: `.drafts/BRIEF-COIL-KAM-SCOPE.md`.
Local input: `a345c744aaadc9b67fc2a7abea3f45b5d105a94e`.
Upstream input: PlasmaLean `79b6152e779a62287da76fb4a49918e38575b3d6`.

## 1. Decision and claim labels

**Estimate / recommendation:** proceed with a bounded numerical and analytic-bounds stage.
Do not launch production kernel certificates yet.
The recoverable polygonal coil field has a credible numerical invariant torus.
Its existing formal certificate has an enormous tail, rather than a demonstrated absence of tori.
Our current Hamiltonian checker does not accept that field directly.
Its good magnetic-model threshold cannot be transferred to coils without a formulation bridge.

The preferred route **to this repository's existing KAM theorem** is a certified canonical annular chart.
It requires a vector potential, a periodic gauge, and a validated implicit radial inversion.
That is a new trusted analytic interface, not merely another `HamExpr` formula.
A precise conditional transfer theorem and its construction obligations appear in §6.
The alternative is an analytic flow-form KAM theorem of our own (route (c), §5).
It can reuse our certificate engineering but is a different mathematical checker.

Claims in this report carry the following meanings:

| Label | Meaning |
|---|---|
| **Proved (source)** | A theorem with the cited source path and body; inspected here, not rebuilt. |
| **Literature** | A statement attributed to the cited authors and year. |
| **Measured** | A computation performed for this report, without interval validation. |
| **Estimate** | A forecast, mathematical derivation not formalized here, or proposed implementation. |

“Proved (source)” never means a fresh kernel replay in this task.
Reported historical timings are explicitly source-reported measurements.
All current Python computations are untrusted candidate generation and diagnostics.
The proposed trusted chain uses kernel-checked proof terms and standard axioms only.
D77's compiler-assisted tier is excluded from every proposed certificate and headline theorem.

**Measured:** the pilot uses the actual upstream 196-segment field, not an idealized replacement.
The main numerical question has a partial positive answer: a well-resolved approximate torus exists.
The requested `~1e-20` residual is **not achieved or certified in this report**.
Fourier support for that target is an extrapolation, with explicit precision and tail gates.
No physical plasma or charged-particle confinement follows from this study.

## 2. Sources, chronology and exact target

PlasmaLean was cloned under `.drafts/coil/PlasmaLean/`; its checked-out HEAD is the pin above.
The following four historical commits were inspected, including their evolving status notes:

| Commit | Date | Source change and interpretation |
|---|---|---|
| [`44b378b`](https://github.com/siddhartha-gadgil/PlasmaLean/commit/44b378bef8fb894137999e4e0a0822a607bd7092) | 2026-10-21 | Stage 1: complex segments, analytic composition, Paley–Wiener and aliasing tools. |
| [`3f7b0ed`](https://github.com/siddhartha-gadgil/PlasmaLean/commit/3f7b0ed589cc6c50ddf3845ff01d1e971f6d3bf5) | 2026-10-21 | Stage 1b: joint holomorphy, two-variable Cauchy theory, coil field and distance bound. |
| [`40170ba`](https://github.com/siddhartha-gadgil/PlasmaLean/commit/40170ba09656b6e250cdce6d398ddc2a7ff87118) | 2026-10-21 | Stage 2: sound sampled pipeline, numerically useless coarse certificate. |
| [`3d6f65d`](https://github.com/siddhartha-gadgil/PlasmaLean/commit/3d6f65d36499607527bd8ff41c430250b2252b18) | 2026-10-21 | Public status explicitly records coil KAM as blocked. |

The final integration paragraph of the pinned
[coil status note](https://github.com/siddhartha-gadgil/PlasmaLean/blob/79b6152e779a62287da76fb4a49918e38575b3d6/notes/theory/coil-kam-status.md)
supersedes its earlier “not started” and “not imported” paragraphs.
Reusable stage-2 tools are imported; the vacuous demonstration certificate remains opt-in.
Those historical paragraphs are not evidence that stage 1 remains incomplete.

**Proved (source):** all-time confinement and field-line existence are already obtained for the distinct
exact rational vacuum field `RationalStellarator.field (1/4)`.
See upstream `PlasmaLean/Design/RationalStellaratorConfinedForever.lean`,
`RationalStellaratorFieldLines.lean`, and `KamTorusAExact.lean`.
The declarations include `torusA_exact`, `rationalStellarator_confined_forever`, and
`rationalStellarator_confined_forever_exists`.
The last gives a unique global field line from every point in the stated trapped region.
Neither that exact field nor its all-time theorem is identified with the polygonal coil field.

**Proved (source):** upstream `DommaschkKamNested.lean`, theorem `dommaschk_nested`,
provides two nested invariant tori of its exact Dommaschk field.
It also proves geometric nesting and the specified two-surface C1 contract.
This source inspection does not supply an all-time confinement/continuation theorem for that field.
It does not certify a coil realization of the Dommaschk field.

The coil target is exactly `tfField + polyCoilFieldC`:

* `PolygonCoilCubicData.lean`: `repKC`, `repVC`, and `filsC`.
* Two representative closed polygons, 24 vertices each, with dyadic coordinates and currents.
* Their signed orbit under identity, a half turn, and the stated reflection produces eight filaments.
* There are 192 polygon segments, plus four sides of the TF rectangle.
* `RationalStellaratorCoilsTF.lean`: TF closure distance `Λ = 10^6`, current factor `κ = 1/2`.
* `PolygonCoilSegment.lean`: theorem `segField_eq_closed` identifies the segment field formula.

The remotely closed TF loop is a mathematical thin-filament model.
It is not a practical coil layout at machine scale.
The exact return legs are retained in every pilot evaluation.
They break the otherwise useful twofold and stellarator symmetries at order `10^-6`.
In particular, full toroidal angle and odd toroidal Fourier modes must be retained.

**Proved (source):** the earlier coil result is finite confinement for 52 transits,
with field-line existence assumed, as the pinned `notes/design/vacuum-demonstrator.md` states.
It is not a substitute for the missing all-time coil theorem.
The planned name `PolygonCoilKam.coilStellarator_confined_forever` has no producer theorem.

## 3. Why the coil route is blocked

### 3.1 Analyticity exists, but the useful quantitative domain is missing

**Proved (source):** `Theory/Fields/BiotSavartComplex.lean` defines the holomorphic segment field
on `segDomain`, where the real part of the bilinear squared distance stays positive.
For a segment `p → q`, complex observation point `y`, and `t ∈ [0,1]`, this is

`Re ((p + t(q-p) - y) · (p + t(q-p) - y)) > 0`.

The dot product is complex bilinear, not the Hermitian norm.
Real coil separation alone does not certify this inequality on a complex strip.
The sufficient bound compares imaginary displacement with real distance to the segment.

**Proved (source):** `Design/CoilFieldComplexDist.lean` proves `filsC_far` using a rational
bisection certificate: each coil point has `|z| ≥ 7/20` or `|r-1| ≥ 7/20`.
`CoilFieldComplex.lean` proves holomorphy on the resulting tube neighbourhood.
Its concrete Cartesian field sup bound is `17400`.
The later coarse certificate uses a different tube and obtains `Mcoil ≤ 45000`.
These two numbers are not conflicting estimates for the same domain.

The cylinder map itself produces imaginary displacement `R sinh(Im φ)`.
The fixed tube proof therefore limits the common angular strip to about `0.13–0.15` radians.
The originally planned strip pair `(0.8, 0.5)` is unavailable by that proof.
This is a limit of the certified neighbourhood, not a proof of a singularity at `0.13`.
Torus-adapted domains and unequal poloidal/toroidal strips may improve it.

### 3.2 Samples are sound; their tail bound is unusable

**Proved (source):** `CoilKamPoint.pointAP_sound` bounds the pointwise residual of the original field.
`CoilKamResidual.lean` identifies its complex extension and holomorphy under explicit mapping bounds.
`Theory/KAM/StripPaleyWiener.lean` proves aliasing and Fourier-tail estimates.
`Theory/KAM/SampledBound.lean`, `Bd_of_sample_sum`, weakens a DFT to sample-modulus sums.
There is no discovered unsoundness in these implications in this source reading.

The coarse torus has 281 trigonometric records at scale `2^100` and support `8 × 16`.
Its sample grid is `16 × 32`, retained frequency box `(7,15)`.
The analyticity strip is `ρ = 1/25`, and the target coefficient radius is `r = 1/50`.
The majorized ratio in its tail is `q = 50/51`.
With `geoZ(q) = (1+q)/(1-q)` and `tailZ(q,K) = 2q^(K+1)/(1-q)`, the tail includes

`2 M geoZ(q) (tailZ(q,7) + tailZ(q,15))`.

The sampled contribution is only about `2.1e-4` and `2.5e-4`.
The aliasing contribution is about `4.5e9` and `2.7e9`.
**Proved (source):** `Design/CoilKamCert.lean`, `coilTorus_resR_Bd` and `coilTorus_resZ_Bd`,
give `Bd (1/50) ... (4.5e9)` and `Bd (1/50) ... (2.71e9)`.
“Vacuous” means useless for smallness, not logically false or a bound on the true residual's size.

Increasing arithmetic precision does not remove this analytic tail.
Nor does checking the same coarse samples on a faster workstation.
At large support the sample-modulus shortcut also loses a factor of order `exp(r K)`.
A useful certificate must retain cancellation in the DFT and prove its rounding and alias bounds.

### 3.3 The toroidal denominator cannot be paid segment by segment

The residual is kept in flow form to avoid division:

`E_R = B_φ(K) (∂φ + ι ∂θ)R - R B_R(K)`,
`E_z = B_φ(K) (∂φ + ι ∂θ)z - R B_z(K)`.

The iteration still needs an inverse bound for `B_φ(K)` on a complex neighbourhood.
The source reports real `R B_φ` around `[0.981,1.006]`, and complex sampled minimum about `0.976`.
Those samples are not a nonvanishing certificate.
The sum of separate filament bounds exceeds `5.3` even at real points.
That bound cannot show a perturbation smaller than a TF contribution of order one.
One needs grouping, Fourier/Taylor enclosure, or local complex boxes that preserve cancellation.
The exact long-axis contribution should be isolated symbolically before bounding the returns.

The status note's proposed coarse derivative bound `2e6` makes a naive real cover prohibitive.
Its estimate of roughly `10^20` cells is a warning about that route, not a lower bound on all methods.

### 3.4 Newton smallness and the theorem interface are separate blockers

**Proved (source):** `Design/KamFlowIteration.lean` gives
`FlowField.KamH.kam_flow_torus` with scalar condition

`32 κ e0 / δ0^4 ≤ 1`, and limiting strip `ρ∞ = ρ0 - 6 δ0 > 0`.

It also requires admissibility throughout the correction neighbourhood and displacement bounds.
`Design/KamFlowField.lean` represents its field and primitive identities by polynomials.
The coil field is not an instance of that polynomial interface.
The analytic `AnaFieldAt` infrastructure does not by itself extend the iteration theorem.
The full-period convention also changes the transport and Diophantine constants.
The source's `γ_eff = γ/4` is an input to its own scaled formulas, not our checker parameter.

**Estimate (upstream oracle):** requirement.py predicts `e0` around `4e-36` with crude bounds,
`1e-29` with sharper sup bounds, and `5e-28` with an adapted neighbourhood as well.
These predictions inherit torus-A frame/twist bounds; they are not certified coil thresholds.
The shorthand “needs about `1e-30`” describes this range, not one frozen literal test.

### 3.5 Cost follows the analytic problem

**Measured (upstream report):** 512 point checks took about 830 CPU-seconds at 100 bits,
approximately 1.6 seconds per point, with up to 4.3 GB per process.
That old peak exceeds this brief's 4 GB numerical-job ceiling; no such Lean job was run here.
**Estimate (upstream):** isotropic narrow strips force `K ≈ 1500` and about nine million points.
Improved strips `(0.8,0.25)` and `M ≈ 10` suggest a `256 × 1024` grid.
Separable torus evaluation reduces the forecast from about 200 CPU-days to about four CPU-days.
Those improvements are prerequisites to the forecast, not already available proofs.

## 4. Weighted area and normalization

**Estimate / derivation:** write `B_R,B_φ,B_z` for physical cylindrical components.
For `R > 0` and `B_φ ≠ 0`, the equations with toroidal angle in radians are

`F_R = dR/dφ = R B_R/B_φ`, `F_z = dz/dφ = R B_z/B_φ`.

Cylindrical divergence-free means

`∂R(R B_R) + ∂φ B_φ + ∂z(R B_z) = 0`.

Consequently, with `w = B_φ`,

`∂φ w + ∂R(w F_R) + ∂z(w F_z) = 0`.

If `Pφ0,φ1` is the cross-section flow, its preservation statement is

`Pφ0,φ1* (w(·,φ1) dR∧dz) = w(·,φ0) dR∧dz`.

The area density changes with phase; it is not generally a fixed symplectic form.
For contravariant cylindrical component `B^φ = B_φ/R`, the same density is `R B^φ`.
This distinction avoids a spurious extra factor of `R`.
Upstream's polynomial clearing convention has weight `D/R^3` in its own interface.
One cannot insert the raw coil residual denominator as that polynomial `D` without rescaling identities.

The three-dimensional magnetic flux form is

`β = i_B(R dR∧dφ∧dz)`
`  = R B_R dφ∧dz - B_φ dR∧dz + R B_z dR∧dφ`.

It is closed by divergence-free, and its kernel is the field direction.
Equivalently, it is `-w(dR-F_R dφ)∧(dz-F_z dφ)`.
For a vector potential, `β = d(A_R dR + R A_φ dφ + A_z dz)`.
Keeping this sign convention makes the canonical transfer below directly checkable.

Our angles have period one; upstream's pilot angles have period `2π`.
Set `θturn = θrad/(2π)` and `t = φrad/(2π)`.
The transport frequency remains `(ι,1)` for `d/dt` on the torus,
but the spatial field-line vector field acquires a factor `2π`.
An upstream radian strip `a` corresponds to geometric turn strip `a/(2π)` here.
Its Fourier weight `exp(a |k|)` is the same weight in the coefficient convention of `docs/PLAN.md`.
All residual and threshold comparisons below retain these conversions explicitly.

**Literature:** Viana, Mugnaine and Caldas (2023), §§II–III,
derive the variational/gauge route to a canonical magnetic field-line Hamiltonian.
[Tutorial and equations](https://arxiv.org/html/2308.00821v1#S3).
The global annular chart, complex inverse bounds and checker attachment here remain proposed work.

## 5. Three formulation routes

| Route | What can be reused | New mathematical obligation | Recommendation |
|---|---|---|---|
| (a) Canonical annular chart | Existing isoenergetic route A/B and much of the checker | Exact chart, gauge, implicit inverse, holomorphic quantitative evaluation | Preferred for a result using our existing theorem. |
| (b) Weighted-form a-posteriori theorem | Cohomology, Newton estimates and proof architecture | Variable symplectic geometry, exactness, new frame/torsion checker | Longer-term generic extension. |
| (c) Analytic flow-form iteration | Upstream geometric method and our kernel data machinery | Replace polynomial interface, prove analytic step/admissibility and coil identities | Best fallback for a joint coil result. |

### (a) Explicit canonical coordinates

A local Cartesian choice `q=z`, `p=A_z` after a gauge can simplify formulas.
It is not a global annular angle around a closed meridional curve.
A coil torus needs a periodic poloidal coordinate with degree one.
Use polar coordinates about a prescribed periodic centre curve on an annulus away from its centre.
Pull back the vector potential and gauge away the radial coefficient.
The remaining one-form is `P(q,r,t) dq - H0(q,r,t) dt`.
Its radial derivative `P_r` is a signed nonzero multiple of `r B_φ`.
In turns, the fixed-centre factor is `-2π r B_φ`; a moving centre changes other coefficients.
The equation `P(q,r,t)=p` then defines the radial inverse `r=G(q,p,t)`.
The canonical Hamiltonian is `h(q,p,t)=H0(q,G(q,p,t),t)`.

This construction needs uniform complex injectivity/contraction bounds, not just real monotonicity.
The gauge may introduce a radial integral without an elementary antiderivative.
Adding a logarithm constructor alone therefore does not finish route (a).
One option is a certified analytic-function interface with validated quadrature and implicit evaluation.
An alternative finite polynomial surrogate must carry a uniform original-field remainder and its derivatives.
Proving a torus of the surrogate alone does not prove a torus of the coil field.

### (b) A theorem for a varying weighted form

Passing the physical flow directly to track K is not a type-level specialization.
The current theorem assumes a canonical Hamiltonian vector field.
A spatially varying density and its phase derivative change normal-frame and torsion identities.
One can extend the closed magnetic two-form to a four-dimensional symplectic system by adding a clock action,
or formulate a direct nonautonomous weighted-form theorem with a flux primitive.
Either route must prove exactness/zero-average solvability; divergence-free alone does not give it.
It must also quantify the inverse form and derivatives on the same complex domains as the residual.
The literature's covariant formulations do not constitute a local Lean implementation.
**Literature:** Haro and Luque (2019) develop covariant a-posteriori Hamiltonian results,
including isoenergetic variants; [paper](https://arxiv.org/abs/1711.05515).
That is supporting methodology, not a claim that their theorem directly accepts this three-dimensional flow.

### (c) Upstream flow form with larger certificates

The existing polynomial `FlowField` includes divergence, flux-primitive, and torsion identities.
These are meaningful source premises, not removable implementation details.
Replace polynomial evaluation with analytic functions, coefficient-space composition and derivative bounds.
Prove the corresponding chain rules and Taylor remainder, then refactor step and admissibility stability.
Use full-period `∂φ+ι∂θ` rather than silently retaining the rational-field doubled-angle operator.
Supply the coil vector potential/flux identities and complex inverse-denominator bound separately.
The `AnaFieldAt` work closes part of this job, but its scalar Cartesian instances do not close all of it.

The exact identity `X = n/D` must remain attached to the original segment sum.
Certificate shards can prove the finite norm inequalities for this new flow checker.
They do not make `checkTorusCertificateV2` a flow checker by renaming its input.
**Estimate:** this route may deliver a theorem earlier if the canonical inverse is badly conditioned.
Its current smallness constants can demand substantially smaller errors than the magnetic example.

## 6. Precise bridge theorem for route (a)

**Estimate / proposed theorem**, provisionally `coil_barrier_of_canonical_V2`.
This is a mathematical contract, not approved Lean text or a proved declaration.
All carriers can use `Fin n → ℝ`, `Fin n → ℂ` and `Fin n → ℤ` as required.

Fix an open coil-free physical region `U ⊂ ℝ³` and an analytic real field `B` on it.
Fix a complex annulus chart with two period-one angles `(q,t)` and action interval `I`.
Its real map is

`χ(q,p,t) = (R(q,p,t) cos(2πt), R(q,p,t) sin(2πt), Z(q,p,t))`.

Assume the following source/typing data and checkable analytic bounds:

1. A holomorphic complex extension of the exact finite-segment field on a specified neighbourhood.
   On real points it agrees with `B`; on that neighbourhood every branch/denominator is valid.
2. A holomorphic periodic chart and inverse on explicit open domains, real on real points.
   On the real annulus, `R ≥ Rmin > 0` and `B_φ∘χ ≥ bmin > 0`.
   The chart is an embedding of each closed meridional annulus and has degree-one angle.
3. A real-on-real periodic analytic function `h(q,p,t)` and the exact identity
   `χ*β = dp∧dq - dh∧dt`, with `β = i_B vol` as in §4.
   A producer proves this identity from the actual potential, gauge and inverse construction.
4. An exact attachment of `H(q,t,p,J) = J+h(q,p,t)` to the checker Hamiltonian.
   The unchanged checker requires an actual exact `HamExpr` representation.
   For an implicitly defined `h`, a new analytic certificate/base interface and its soundness
   must be proved first; it can reuse the KAM theorem, but is not the unchanged Boolean checker.
5. A finite torus certificate `c`, witness `w`, and algebraic frequency `ω*` in its checked box,
   with a proved Diophantine bound in the repository's convention.
   `checkTorusCertificateV2 routeAV2 c w = true`, or the corresponding audited extended-base test.
   All embedding, energy, Gram, torsion, domain and displacement checks refer to this same `H`.
6. A graph/degree certificate on the exact torus, derived from candidate bounds plus displacement,
   placing its projection in a compact subannulus of the chart domain.
   The projection bounds also put it in a compact coil-free subset of `U`.

Then there is an analytic invariant embedded physical torus `S ⊂ U`.
After clock-phase normalization its parametrization `κ` satisfies

`Dκ(θ) (ι,1) = (2π R(κ(θ))/B_φ(κ(θ))) B(κ(θ))`.

Here `ι` is the ratio of the two components of `ω*`.
The clock component and primary periodicity fix the time normalization;
an isoenergetic ray scale must be resolved in that step, not assumed equal to one at input.
All field lines on `S` are reparametrized quasiperiodic lines with that rotation ratio.
The positive prefactor is bounded above and below on `S`, so both time parameters are complete there.

If the degree/embedding certificate additionally makes `S` the boundary of a compact solid torus `V`,
with `V ⊂ U`, then every point in `V` has a unique global solution of `x'=B(x)`.
The solution stays in `V` for all real time, and points in its interior remain in its interior.
This last conclusion needs compactness and coil clearance of the whole trapped solid torus,
not merely clearance of its boundary or an invariant parameterization.

The hypotheses are conditional analytic data, not a claim that a coil instance pays them today.
In particular item 5 is not replaced by the premise “an exact torus exists”.
The proposed bridge has a distinct name and never stands in for an unconditional source result.

### Proof outline and size

* Apply the existing checker soundness, obtaining its exact canonical torus and closeness bounds.
* Use `H_J=1`, primary periodicity and a phase shift to normalize the clock.
* Contract the exact flux identity with the projected Hamiltonian vector field.
  Its kernel is the original field direction; the toroidal component fixes the factor `2πR/B_φ`.
* Compose the torus with `χ`; transfer holomorphy, reality, degree and embedding.
* Prove the solid-torus boundary claim from radial graph/degree and quantitative separation bounds.
* Use local ODE uniqueness to forbid a crossing; compact continuation gives global existence.
* Check the exact literal application statement, then perform the usual independent seal process.

**Estimate:** transfer after a supplied chart: 1,500–3,000 new Lean lines.
Chart, gauge, implicit inverse, domains and exact original-field attachment: 5,000–12,000 lines.
Potential/log/quadrature evaluation and sound derivative interface: another 3,000–8,000 lines.
Total route-(a) range: approximately 10,000–23,000 handwritten lines, before instance data.
These estimates overlap in possible implementations; they are not measured development costs.
Use focused modules under 1,500 lines, with no resource-budget overrides.

## 7. Expression language and ball arithmetic

**Proved (source):** `KAM/Certificate/Expr/Basic.lean` already provides rational constants, π,
actions, Fourier sine/cosine modes, arithmetic, division, powers, exp, sine, cosine and square root.
`Expr/BallSqrt.lean` proves an outward-rounded square-root ball under a right-half-plane guard.
`Expr/Slp.lean` has inverse and square-root slots.
`Model/SqrtWitness.lean`, `sqrtWitness_sound`, validates a polynomial root witness by its defect.
The lunar lock already consumes square roots; adding another `sqrt` constructor is unnecessary.

For straight segments let `a=p-y`, `b=q-y`, `α=√(a·a)`, `β=√(b·b)`.
The field contribution is exactly

`κ (α+β)/(αβ(αβ+a·b)) (a×b)`.

Therefore the finite polygonal **field** needs only existing arithmetic, inverse and square root,
once its Cartesian observation coordinates have an exact expression/evaluation interface.
No logarithm or `atanh` is needed just to evaluate that field.
For long nearly opposite endpoint vectors, rationalize the small denominator:

`(α+β)(αβ-a·b)/(αβ ((a×b)·(a×b)))`.

Choose a stable representation per verified domain; both need nonzero-denominator proofs.
The cross-product denominator can vanish on a line extension even where the physical field is regular.
Use a different representation there rather than asserting one global stable formula.
Algebraic equivalence is exact only on the explicitly guarded branch domains.

For the vector potential of one segment, with length `L`, a convenient real expression is

`Aseg(y) = κ (q-p)/L · log((α+β+L)/(α+β-L))`.

Its curl agrees with the segment field off the filament, with orientation fixed by `p → q`.
Complex branch and logarithm identities must be proved on the chosen neighbourhood.
The equivalent `2 atanh(L/(α+β))` can be useful when its argument is bounded away from one.
This potential formula is a derived proposal here; no imported potential theorem is claimed.
The sign of alternative endpoint-log expressions must be checked against the defining line integral.

| Item | Existing support | Additional trusted work |
|---|---|---|
| `1/|x-y|`, powers of distance | `div`, `sqrt` | Domain guards; no Hermitian complex norm substitution. |
| Finite segment field | Arithmetic and roots | Exact geometry interpretation, curl/divergence and stable-form identity. |
| Segment potential | No logarithm constructor | Branch-aware log ball/model/jet soundness, or validated primitive integration. |
| Canonical radial inverse | None as a primitive | Uniform contraction/inverse theorem and derivative enclosures through order needed. |
| Fourier-filament integral | No integration constructor | Certified quadrature with complex/tube remainder and derivative bounds. |
| Tail of an infinite filament expansion | Not finite-expression semantics | Explicit analytic tail, original-field attachment, and current/geometry error budget. |

A finite Fourier description of the coil curve does not make its Biot–Savart integral a finite `HamExpr`.
Sampling it into a polygon changes the field and requires a model-error theorem.
For an exact polygonal target, no smooth-coil approximation remainder is owed.
For a physical smooth-coil target that remainder becomes a compulsory new invoice.

**Estimate:** one point evaluation of 196 segments uses 392 endpoint square roots before sharing,
roughly `10^4` scalar arithmetic operations and hundreds of divisions.
Common endpoints can share roots; reuse and a separate long-TF expression matter.
Third-order jets in three spatial variables have 20 scalar slots before sparsity.
The route-A refined claims need bounds through `D²X_H`, hence third Hamiltonian derivatives.
An implicit chart must furnish these derivatives, not merely a certified point value.

Plain enclosing balls over a whole torus can lose all cancellation between segments.
Use Fourier/Taylor models or small local balls whose signed centres are summed first.
Carry outward dyadic rounding, root defects, inverses and all derivative tails explicitly.
For a log ball, range-reduce to `log c + 2∑ z^(2j+1)/(2j+1)` with `|z|<1` and a proved tail.
Alternatively supply a witness for the derivative and anchor, with a proved integral remainder.
Neither approach has been implemented or benchmarked in this task.

## 8. Numerical pilot on the literal coil field

### 8.1 Reproduction and resource contract

Committed driver: `scripts/coil/pilot.py`; reproduction: `bash scripts/coil/reproduce.sh`.
Only NumPy, mpmath and Python's standard library are used.
The driver imports the pinned upstream untrusted `coil.py` and `refit.py`.
It checks the upstream revision and parses the committed `CoilKamData.ckRecs` seed.
Thus it does not rely on the upstream oracle's unavailable `/tmp/k2work/double_A.npz`.
The 281 seed records are converted from their exact integer scale `2^100`.
No downloaded Python code is used as proof evidence.

Every numerical command ran sequentially with this prefix:

```sh
systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 \
  python3 -B scripts/coil/pilot.py ...
```

Each job imposes `RLIMIT_CPU=3500` seconds, below 60 CPU-minutes.
The cgroup supplies the actual memory cap; RSS is recorded as a diagnostic.
No Lean, Lake or compilation subprocess was launched by these scripts.
Scratch arrays, logs and JSON receipts live only in `.drafts/coil/`.
The reproduction commands select a bounded list of jobs, below three CPU-hours in aggregate.

**Measured:** retained numerical receipts report:

| Job | Timed CPU seconds | Peak RSS KiB |
|---|---:|---:|
| Fits through `16×40` | 57.248 | 1,434,916 |
| Fit `20×56` | 201.109 | 3,052,496 |
| RK4 trace/refinement | 15.295 | 38,948 |
| Spectra and complex diagnostics | 1.789 | 187,064 |
| 65-digit residual samples | .367 | 43,568 |

Total timed computation: 275.808 CPU-seconds, about 4.60 CPU-minutes.
Imports precede the loop timers; allowing another minute still puts the numerical total below six CPU-minutes.
The longest job is about 201 seconds; maximum RSS is approximately 2.91 GiB.
The first fit receipt predates the CLI addition for resuming a larger truncation;
the final driver preserves that fit and includes the larger job explicitly in reproduction.
Python is 3.12.3, NumPy 2.5.0, and mpmath 1.3.0.

### 8.2 Parametrization/Newton result

The frequency is the upstream noble number `ι=(75+√5)/562`, approximately `0.13743`.
The ansatz uses all cosine and sine records in the full-period half plane
`{(0,m):0≤m≤M} ∪ {(k,m):1≤k≤N,-M≤m≤M}`.
The phase condition fixes the sine coefficient of `(1,0)` in `R` to zero.
The Galerkin Newton update uses an analytic Jacobian via complex-step spatial derivatives,
and NumPy least squares; one redundant equation is retained.
This is floating-point Newton, not a validated contraction proof.

**Measured:** shifted oversampled validation gives:

| Support `N × M` | Unknowns | Validation grid | Max `|E_R|` | Max `|E_z|` | Sample FFT weighted ℓ¹ at `r=.063`, R |
|---|---:|---|---:|---:|---:|
| `8 × 16` | 1,121 | `33 × 59` | `1.31e-6` | `1.70e-6` | `1.41e-5` |
| `12 × 24` | 2,449 | `45 × 83` | `2.93e-7` | `1.50e-7` | `2.39e-6` |
| `16 × 40` | 5,345 | `57 × 131` | `3.86e-10` | `2.38e-10` | `1.04e-8` |
| `20 × 56` | 9,265 | `69 × 179` | `6.43e-13` | `4.49e-13` | `5.50e-11` |

The validation grids are shifted by `.071` and `.137` radians relative to collocation.
All field evaluations retain the exact TF return geometry and odd modes.
The weighted quantities are FFT diagnostics, without alias or roundoff certificates.
The collocation residual can fall to `~1e-16` while the independent residual is `~1e-10`.
The latter is the relevant observed truncation defect.
The largest truncation uses a compact collocation grid to stay under the 4 GB memory cap.
Its validation grid remains larger and shifted, and no collocation residual is promoted to a norm bound.

The approximate torus spans roughly `R∈[.831,1.188]`, `z∈[-.180,.180]`.
Its sampled clearance and field diagnostics are recorded below.
These are sampled extrema rather than rigorous geometric enclosures.

### 8.3 Field-line tracing and precision cross-check

**Measured:** maximum one-turn discrepancy over four initial angles:
`2.5664e-7` at 64 RK4 steps, `1.5661e-8` at 128, and `9.6889e-10` at 256.
The successive improvement factors are about 16.4 and 16.2, consistent with fourth-order integration error.

Tracing starts at four separated angles on the candidate torus and covers one full toroidal turn.
Classical RK4 at successively doubled resolutions is compared to the parametrized target
`K(θ+2πι,2π)` using the same fixed frequency.
This is a consistency test of the field and parametrization, not long-time stability evidence.
No field-line tracing tolerance is used as a KAM residual certificate.

**Measured:** at `(θ,φ)=(.271,.193)`, `(1.7,2.3)`, `(4.1,5.2)`, the 65-digit
`(E_R,E_z)` values are respectively approximately
`(-1.58e-14,-1.48e-14)`, `(-1.33e-14,9.76e-14)`, `(6.37e-14,5.02e-14)`.

The mpmath check evaluates three non-grid points at 65 decimal digits.
It reconstructs the dyadic coil data exactly and evaluates the stored double torus coefficients as exact binaries.
It does not perform a high-precision refit or provide an interval supremum.
These nonzero values show that evaluating the same candidate more accurately does not pay its residual.

### 8.4 Fourier support and analyticity

**Measured:** shell regression gives decay rates `1.0741` in θ and `.43543` in φ, in radians.
The fit uses θ modes 4–18 and even φ modes 4–46 above amplitude `1e-13`.
The poloidal shells are visibly nonmonotone; the fit is a forecast, not a uniform tail envelope.
Ignoring prefactors, `log(1e20)/rate` gives cutoffs 43 and 106.
At coefficient radius `.063` these illustrative cutoffs become about 46 and 124,
before allowing for derivative, composition, shell-count and enclosure losses.

Fit an exponential to coefficient shell maxima above the double-noise floor.
For the toroidal fit use the dominant even modes; the small odd modes remain in every field/residual evaluation.
Fitted decay is evidence of resolution and a planning scale, not a proof of a holomorphic strip.
The upstream larger scan reported roughly `exp(-1.3|k|)` and `exp(-.42|m|)`.
At a nonzero target strip, subtract its coefficient radius from those exponents before estimating tails.
Nonlinear composition and differentiation also cost polynomial factors in the mode indices.

**Estimate:** plan `N≈40–60`, `M≈120–200` for a real residual near `1e-20`,
and use the upper end, more precision and explicit tail bounds for a weighted norm.
This corresponds to roughly ten to twenty-five thousand half-plane records.
It is not a measured support requirement or proof that these cutoffs suffice.
At upstream flow thresholds closer to `1e-28`, the source's `N≈56`, `M≈205` is the relevant planning point.
The associated signed rectangular box has about 47,000 modes before sparsity.

**Measured:** on a `24 × 48` real angle grid, the minimum distance to the 192 polygon segments
is `.299685`; sampled `R B_φ` lies in `[.980767,1.005548]`.
The four TF segments are retained in the field and branch diagnostics.
For toroidal shifts `Im φ=β` with real θ, the diagnostic is:

| β (radians) | Min `|R B_φ|` | Max Cartesian component modulus | Min `Re segQ` over all segments and segment parameter |
|---:|---:|---:|---:|
| .03 | .980737 | 1.15264 | .08937 |
| .07 | .980604 | 1.15475 | .08743 |
| .12 | .980283 | 1.15976 | .08280 |
| .18 | .979656 | 1.16926 | .07395 |
| .24 | .978692 | 1.18303 | .06147 |

Each row samples the two torus angles on that grid at the indicated imaginary shift.
For each sampled complex point, the real quadratic in the segment parameter is minimized analytically.
This tests every segment parameter at those points, but not intervening angle values or imaginary shifts.
There is no poloidal complex displacement or normal tube in this particular diagnostic.

A sampled positive `Re segQ` is a sufficient-branch diagnostic only at those sampled points.
It neither proves the whole strip nor identifies a true complex singularity when the sufficient test fails.
The rigorous inherited tube strip remains around `0.13–0.15` radians under its original mapping conditions.
For a new candidate those conditions must be rechecked, not inherited from the coarse torus.
Use proposed radian widths such as `(ρ_θ,ρ_φ)=(.4,.08)` only as initial validation targets.
Their turn widths are approximately `(.0637,.0127)`.
No such anisotropic strip is certified here.

### 8.5 Comparison with the refined checker

**Proved (source record):** the magnetic example has a kernel certificate with error `7.3e-22`
against threshold `10^-19.19`, about 1.94 decades of margin, per `mag-status.json`.
Its public torus strip is `3e-6` turns; its Hamiltonian is a small exact trigonometric expression.
The Moon's band record has different errors, around `1.6e-16` and `1.83e-16`.
Thus `7e-22` versus `10^-19.2` is the magnetic comparison point, not a universal Moon/coil threshold.

For coils the measured `E=D LK-n` is a flow-form residual in physical R/z components.
To obtain a Hamiltonian invariance error one must divide by `D`, change coordinates with bounded derivatives,
convert radians to turns, attach the dummy action/energy, and pay all approximation and derivative tails.
Symbolically a chart-dependent budget has the form

`e_H ≤ Cchart · (2π/bmin) · e_flow + e_chart + e_jet + e_tail + e_round`.

This is a budgeting schematic, not a proved inequality with a computed `Cchart`.
The true refined threshold must be recomputed from the coil's frame, torsion, derivative and domain bounds.
Even a certified raw residual `1e-20` can fail after those costs.
The present pilot therefore does not clear the production-certificate numerical gate.

## 9. Certificate size, kernel cost and new proof effort

The checker is reusable, but a coil instance is much more expensive than one short polynomial Hamiltonian.
Each field/model evaluation contains hundreds of roots and cancellation-sensitive sums.
The principal unknown is the sharp complex bound and chart conditioning, not the number of CPU cores.

**Proved (source records):** the magnetic chain has 5,807 generated modules.
The lunar band has about 1,650; the lock has 13,668 and about 242 MB of source.
These counts come from `docs/results/{Magnetic,SO-2,SO-3}.md`.
`docs/campaign/side/mag-status.json` reports a remaining 2,058-module package at about 26 CPU-hours,
with 3–5 hours projected elapsed time on the 64-core workstation.
That is not a measured total time for every magnetic module.

**Estimate:** a sharp `256×1024` sampling route has 262,144 points and about 51 million segment visits.
At the historical 1.6 seconds per point, raw evaluation alone is about 116 CPU-hours.
The upstream optimized forecast of four CPU-days is consistent in scale but assumes separability.
This excludes exact DFT, frame/twist, analytic domain, potential and implicit-chart work.
A canonical potential and third-order jets can multiply the arithmetic burden severalfold.
Do not quote a four-day total for the canonical route from a field-only benchmark.

| Scenario | Source size estimate | Generated module estimate | Kernel CPU estimate |
|---|---|---|---|
| Sharp flow-form proof, efficient grid/DFT | 0.2–1 GB | 5,000–20,000 | 100–400 CPU-h |
| Canonical chart, local analytic evaluations and jets | 0.5–3 GB | 10,000–50,000 | 300–1,500 CPU-h |
| Existing crude isotropic tail route | No useful budget | Potentially hundreds of thousands | No-go before sharpening |

Every number in this table is an estimate, not a kernel benchmark performed here.
Bytes depend on precision, shared data, encoding and per-declaration splitting.
Generated lines are not counted as new mathematical proof lines.
Budget the exact DFT separately; a direct quadratic DFT can dominate the field checks.
Validated FFT or separable block transforms need their own soundness and rounding budgets.

On this shared server, one 4 GB lane at comparable throughput means roughly those CPU-hours in elapsed time.
That throughput is not established by this task's Python timings.
At 16–32 useful workstation lanes, the flow scenario suggests about 4–30 hours elapsed,
and the canonical scenario about 12–100 hours including serial dependency tails.
Sixty-four nominal cores do not guarantee 64-fold speedup under memory and import constraints.
The production scheduler and allowed memory tier require a separate approved campaign brief.

Use balanced products, shared input literals, explicit per-point or per-block facts,
and bounded per-declaration work rather than a single enormous reduction.
`docs/explorations/lean-kernel-nat-literal-hash.md` records dramatic low-limb collision slowdowns.
Whiten serialized data and avoid repeated large mantissas with identical low limbs where applicable.
Whitening is exact encoding with a checked decoder, not perturbation of coefficients.
Do not extrapolate the old stage-2 kernel cost without remeasuring representative new shards.

**Estimate:** alternative (b) needs about 15,000–35,000 handwritten Lean lines plus a new base checker.
Alternative (c) needs about 6,000–15,000 lines for the analytic interface/iteration and coil identities,
plus 2,000–6,000 lines for sharpened bounds, checking and application geometry.
Existing upstream proofs might reduce these ranges, but no port compatibility is established.
All three alternatives need independent mathematical and package audits.
None is a one-file bridge from the current coil data to the existing checker.

## 10. Staged plan and explicit stop gates

1. **Model pin and independent numerical candidate.**
   Preserve the full 196-segment model, currents, endpoints, frequency and period conventions.
   This report recovers the model and obtains a numerical candidate.
   Gate: a multiprecision refit with independent oversampling, high-mode shells and residual below `1e-24`.
   That gate leaves reserve for a putative `1e-20` analytic budget; it is not a universal threshold.
2. **Cancellation-aware complex enclosures.**
   Prove coil clearance, positive-real radicands and a lower bound for `B_φ` on an adapted domain.
   Group filaments and isolate the long TF contribution.
   Gate: a useful bound, for example `|R B_φ-1|<1/2`, proved on the entire selected complex tube.
   If only segmentwise sup bounds remain available, stop before large emission.
3. **Canonical chart prototype, with route decision.**
   Build a periodic annular gauge and validate the radial implicit inverse with derivative bounds.
   Compare its predicted KAM budget and cost with the analytic flow-form extension.
   Gate: explicit source attachment, quantitative domains and no unpaid inversion/primitive term.
   If chart conditioning dominates, choose route (c) explicitly; do not describe it as the existing checker.
4. **Freeze the mathematical contract only after exact text approval.**
   Ordinary analytic/checker theorems remain unfrozen until the normal owner workflow says otherwise.
   No frozen statement is edited by this study.
   Gate: independent statement review rejects conclusion-shaped premises and surrogate-only claims.
5. **Small complete certificate prototype.**
   Measure one representative field, derivative, inverse/root/log and DFT shard on the target kernel.
   Establish bit-exact producer/checker agreement and rejection of a mutated coefficient or branch guard.
   Gate: per-module default-budget elaboration, memory cap and credible total extrapolation.
6. **Production and application.**
   Emit the full data package in an opt-in application, with an authenticated dependency manifest.
   Run complete kernel checking/replay, exact source/model equality, fresh axiom inventory and independent audit.
   Prove the separating-surface and compact-continuation theorem for the same field and region.
   Only then propose sealing a literal all-time coil-field confinement statement.

**Estimate / decision:** stages 1–3 are worthwhile research; stage 6 is currently no-go.
The first literal unpaid analytic gate is a cancellation-aware complex enclosure with nonvanishing `B_φ`.
In parallel the candidate still needs a high-precision solve and a true residual-tail bound.
Neither outstanding gate is paid by the successful low-resolution Newton solve.

## 11. Target theorem

If the stages succeed, the result would state: **for the specified exact rational polygonal closed-current model,
there is an analytic embedded invariant torus of specified rotation ratio; every initial point
in a specified compact solid torus has a unique field line for all real time and stays inside.**
Its conclusion would name the coil field, currents, endpoints, region and time parameter literally.
It would be a field-line theorem, without claims about finite-radius conductors, MHD equilibrium,
guiding-centre drifts, collisions, charged particles or experimental confinement.
Those are new models and new hypotheses, not consequences of an invariant field-line surface.

## 12. Checks, uncertainties, source defects and handoff

The only committed edits are this report and the two small scripts under `scripts/coil/`.
All downloaded source, numerical candidates and receipts remain under `.drafts/coil/`.
The completion marker is `.drafts/READY-COIL-SCOPE`, as requested by the brief.
No KAM source, frozen file, manifest, root, README or generated build file was edited.
No push was performed.

The brief's explicit research-only restriction supersedes the general build/lint handoff rule.
`scripts/lint_sources.sh` was read and not executed: its final ABI step invokes `lake env lean`.
No targeted build, `#print axioms`, kernel replay, new theorem audit or full-lint PASS is claimed.
Historical standard-axiom statements above are source records, not fresh measurements.
There are no new main Lean results whose axioms could be printed in this report.

| Check performed | Exact result |
|---|---|
| `python3 -B scripts/gen_root_imports.py --check` | Exit 0, no output. |
| `python3 -B scripts/render_errata.py --check` | Exit 0, no output. |
| `ast.parse` on `scripts/coil/pilot.py` | `pilot.py: syntax OK`. |
| `bash -n scripts/coil/reproduce.sh` | Exit 0, no output. |
| Report line-count constraint and local Markdown links | PASS, within 400–900 lines; every local link resolves. |
| Five sequential scoped numerical jobs | Exit 0; receipts `fit`, `fit20`, `trace`, `diagnostics`, `precision`. |
| Upstream `git status --porcelain` | Exit 0, no output; source pin remains unchanged. |
| Protected-path `git diff --exit-code` and final tracked-file scope | PASS; only owned report/scripts enter the commit. |
| `git diff --cached --check` | Exit 0, no output. |

The commit suppresses the post-commit HQ generator with its documented `HQ_UPDATING=1` switch.
The hook would otherwise invoke generated-HQ work prohibited by this brief, including README updates.
This does not stand in for a build or any mathematical validation.

Uncertainties: sufficient complex tube versus actual singularity, sharp cancellation bounds,
periodic gauge and implicit inverse conditioning, coil twist stability, high-precision tail,
proof-port compatibility, kernel shard size and workstation parallel efficiency.
The pilot's success does not resolve these uncertainties.

Suspected source/document defects and deviations, reported without editing the ledger:

* `docs/results/Magnetic.md`, final source paragraph: “No kernel-checked certificate chain for it is on `main` yet.”
  This is stale against its own sealed status and the landed provider/body at this snapshot.
* The same page says the planning `3/1000` was not attempted; the existing pitch report records earlier
  multiprecision attempts. Distinguish those attempts from the fallback certificate and seal.
* Upstream `coil-kam-status.md` preserves historical “not started” / “not imported” paragraphs.
  Read its final integration note for current import scope; no mathematical defect is inferred.
* Its early `(0.8,0.5)` complex-strip assumption is explicitly withdrawn later in the same note.
  This report retains that withdrawal rather than recycling the optimistic early threshold.
* No mathematical defect in a frozen declaration or in an upstream theorem was established by this reading.
* The intended deviation from upstream's dense high-resolution oracle is the bounded compact-grid pilot
  and recovery from the committed coarse torus; its shifted validation errors are reported literally.
* No physical normalization, toroidal symmetry or original-law remainder has been silently discarded.

## 13. Primary references and source locators

* PlasmaLean (2026), pinned status note and four commits linked in §2.
  All upstream relative paths in this report refer to that pin, not a moving branch.
  Source inspection only, without independent elaboration or kernel replay.
* PlasmaLean `PlasmaLean/Design/CoilKam{Data,Torus,Point,Lip,Residual,Cert}.lean`:
  literal coarse candidate, exact field residual, sample transfer and certified coarse bounds.
* PlasmaLean `PlasmaLean/Theory/Fields/BiotSavartComplex.lean`,
  `Design/PolygonCoilSegment.lean`, `Design/CoilFieldComplex{,Dist}.lean`:
  field identity, branch domains, complex bounds and certified coil separation.
* PlasmaLean `PlasmaLean/Design/KamFlow{Field,Step,Iteration}.lean`:
  polynomial interface, single-step estimates, iteration and admissibility contract.
* [Local checker result](../results/SO-1.md), [magnetic result](../results/Magnetic.md),
  [lunar band](../results/SO-2.md), [lunar lock](../results/SO-3.md).
* [Magnetic seal plan](mag/SEAL-PLAN.md), [existing comparison](mag/SIGNIFICANCE-AND-PITCH.md),
  [kernel literal-hash measurements](lean-kernel-nat-literal-hash.md).
* Viana, Mugnaine and Caldas (2023), *Hamiltonian description for magnetic field lines: a tutorial*,
  [arXiv:2308.00821](https://arxiv.org/abs/2308.00821), §§II–III, variational and gauge formulation.
* Haro and Luque (2019), *A-posteriori KAM theory with optimal estimates for partially integrable systems*,
  [arXiv:1711.05515](https://arxiv.org/abs/1711.05515), covariant Hamiltonian and isoenergetic theory.
* Figueras, Haro and Luque (2017), *Rigorous computer assisted application of KAM theory: a modern approach*,
  [arXiv:1601.00084](https://arxiv.org/abs/1601.00084), Fourier-based validation methodology for maps.
  It supports the validation strategy, not a direct field-line theorem for the present coil instance.
