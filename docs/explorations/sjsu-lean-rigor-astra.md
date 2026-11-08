# SJSU and SJS: what kernel-checked statements would require

Independent research report, 6 November 2026. Reviewed checkout:
`9ddda9b7cf1003e14b2b7cd91f58d395e67b8984` (PR #8 merge; SJS-X1 material is also present).
This is a proposal, not a certificate, statement approval, or proof audit. No Lean build or
kernel experiment was run. No coordination with the independent `kam-b1` scoping effort.

**Recommendation:** first certify five-billion-year confinement for the **literal SJSU18-O2
polynomial**, using the pruned Fourier–Taylor approximate integrals and the landed first-exit
theorem. Separately advance the planar SJS torus through a certified-frequency, complex-domain,
and packed-arithmetic pilot. Neither floating gate currently supplies the finite inequalities
needed for a Lean application. Transferring SJSU18-O2 to the full Newtonian four-body system is
a third, substantially larger project.

The most consequential findings are:

* SJSU has a useful *measured* factor 860 at the proposed action width, but its grid Fourier
  sums, sampled base minima, floating tails, and model conversion are not enclosures.
* SJS-X1's approximately `6e-32` is an **in-band** residual. Its production out-of-band mass is
  `2.3e-26`; the proposed route-B threshold is approximately `1e-38`, itself still a model.
* The printed SJS frequency is rational and exactly resonant. The proposed cubic replacement
  must be used to regenerate the torus, and its arithmetic must be proved in Lean.
* Program B has the analytic confinement theorems. Its current Boolean torus-chain checker
  accepts a finite Fourier–Taylor Hamiltonian, not the infinite polar expansion of the exact
  degree-18 Cartesian polynomial. There is a real adapter/checker task.
* The B5 certified-torus adapter currently requires `G1Hyps`, including old smallness bounds;
  a v2 certificate alone does not supply that structure. This is a source-visible interface
  issue to remove in an ordinary successor theorem, not a new premise for an application.

## 1. Evidence and the existing interfaces

The controlling scope is [.drafts/ASTRA-SJSU-RIGOR.md](../../.drafts/ASTRA-SJSU-RIGOR.md),
[AGENTS.md](../../AGENTS.md), [PLAN](../PLAN.md), and [DECISIONS](../DECISIONS.md).
The November 3 B readiness documents are historical designs; current code supersedes their
statements that freezing, the coefficient layer, or B3 are still pending.

| Read in this checkout | What it actually provides | What it does not provide |
|---|---|---|
| [Frozen B1-T](../../KAM/Frozen/EffectiveStability/TorusConfinement.lean) | `torus_confinement`: unique physical solution past ±T, normalized action drift ≤ηⱼ\|t\|, from a C² symplectic chart, left inverse, `H ∘ Ψ = N + R`, and angle-derivative bounds on R | A chart or remainder estimate for SJSU |
| [Frozen B1-E](../../KAM/Frozen/EffectiveStability/OscillatorConfinement.lean) | `oscillator_confinement`, with actions `(pⱼ²+qⱼ²)/2` and bounds on their brackets with R | A successful origin-centered normalization at the nominal SJSU point |
| [Oscillator checker](../../KAM/EffectiveStability/OscillatorChainCheck.lean) and [coefficient layer](../../KAM/EffectiveStability/Poly/Coeff.lean) | `checkOscChain_sound`, finite Lie identities, analytic flow tails; `CertCoeff` supports ℚ and ℚ(√2) | General transcendental Laplace coefficients or polar square roots as finite polynomials |
| [Torus checker](../../KAM/EffectiveStability/TorusChainCheck.lean), [FT representation](../../KAM/EffectiveStability/FT/Basic.lean) | `checkTorusChain_sound`; rational cosine/sine coefficients with nonnegative `(2π)^e` tags, finite Taylor powers, exact finite Lie sums and domain budgets | A generic finite polynomial plus analytic remainder input, arbitrary anisotropic polar tubes, or an implicit Kepler node |
| [ApproxIntegral](../../KAM/Application/Confinement/ApproxIntegral.lean) | `hamiltonian_approxIntegrals_confinement` on an open W; compact `closure D`; strict boundary separation; maximal solution, uniqueness and observable drift | A finite certificate checker proving those analytic premises for literal SJSU observables |
| [v2 engine](../../KAM/CertificateSharp/V2/Engine.lean), [route B](../../KAM/CertificateSharp/V2/RouteBEngine.lean) | `checkV2With_sound` / `checkTorusCertificateV2_sound`: passing checks + an exact enclosed Diophantine vector ⇒ `CertifiedTorus` | Infinite Diophantine arithmetic from a finite divisor scan, or Hamiltonian identity from an external solver |
| [CertifiedTorus definition](../../KAM/Certificate/Defs.lean) | Holomorphic, primary, real invariant parametrization, exact energy, interior margin, derivative/displacement bounds, frequency on a ray | Fixed frequency equality; explicit injectivity and Lagrangian clauses are not fields of this definition |
| [B5 adapter](../../KAM/EffectiveStability/CertifiedTorusRoute.lean) | `CertifiedTorusAt` + `G1Hyps` + `RouteChecks` ⇒ confinement through a cotangent chart; explicit quadratic drift constant | Automatic long-time confinement from any v2 output |
| [Λ observable bridge](../../KAM/Application/LambdaDrift/ObservableBridge.lean) and [LP1](../../KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean) | Geometric safety from genuinely bounded fast-action drift; asymptotic Newtonian safety below an existential mass threshold | An explicit admissible μ₀ at the cited masses, or an error estimate for SJSU secular averaging |

The [HH proposal/receipt](../tracks/B/PROPOSAL-MERGED-MAJORANT.md) reports 34 kernel
shards, approximately 27 CPU-min, peak 3.4 GB. Its [frozen application](../../KAM/Frozen/EffectiveStability/HenonHeilesConfinement.lean)
is sealed. The proposed merged-Lie optimization remains a proposal in that document; the
current oscillator checker still calls `cartLieSum` and bounds the existing chain remainder.
Do not price SJSU as if the proposed speedup had already been measured.

Background read: [SJSU effective stability](sjsu-effective-stability.md),
[model recovery](sjsu-model-recovery.md), [gate 2](sjsu-near-torus-gate.md),
[SJS feasibility](sjs-feasibility.md), [SJS plan](sjs-plan.md),
[X1](sjs-x1-support.md), [LG00 scout](sjs-lg00-scout.md), and [ambition](ambition.md).
The older estimate “hybrid + packed: 6–19 CPU-h” is explicitly withdrawn by SJS-PLAN:
Hamiltonian composition still needs the final accuracy. The LG00 scout's missing `sqrt`
node is now present in [HamExpr](../../KAM/Certificate/Expr/Basic.lean); a Kepler implicit
node is still absent from its constructors. Existing packed infrastructure is substantial,
but the inspected packed sharp-route wrapper is route A; route-B integration must be
accounted for explicitly rather than inferred from the directory's existence.

## 2. Candidate SJSU statements

### 2.1 Fix one exact model before certifying it

Let `H18` be the real Hamiltonian obtained from the **complex-form decimal strings**, read
as exact rationals, in `applications/sjsu/data/sjsu18-o2.json`, with

`sha256 = 702b0b3a3c7c713d48cc3044f90bd13795b79f255550275cc7937c5d8a067772`.

Use real phase coordinates `(q,p)=(η,ξ)`, each `Fin 3 → ℝ`, and
`zⱼ=(ξⱼ−iηⱼ)/√2`. The file's `{zⱼ,z̄ⱼ}=−i` then agrees with canonical
`{ηⱼ,ξⱼ}=1`. Pair conjugate terms to define a manifestly real polynomial. All total
degrees are even, so converting the whole conjugate-symmetric polynomial to real variables
has rational coefficients: the √2 denominator contributes `2^(degree/2)`.

This chooses a model; it does **not** claim these rational numbers equal exact Laplace
integrals. The independently rounded `real_form` is not an exact duplicate: the check in
§5 found 47 discrepancies among its 78 quadratic/quartic coefficients, at most `2e-27`.
Derive the real polynomial from the chosen complex form, or explicitly charge that difference.
Do not silently treat both as exact definitions of the same H.

Fix `z_nom` by reading the six printed `xi_eta_secular` coordinates as exact decimals from
`validation/table2_map_poincare_order1.json`. This is a specified point of the secular model,
not a proved image of an observed or Newtonian initial state. Its numerical preprocessing
is provenance, not a theorem premise.

### 2.2 Recommended literal finite-time target

Choose, then pin, a finite exact matrix V, positive base actions, a real trigonometric shift
`B₀(φ)`, and three real rational Fourier–Taylor expressions `Fⱼ(u,φ)`. Define
`w=Vᵀ((ξ−iη)/√2)`, `Iⱼ=|wⱼ|²`, `φ=(arg w₁−arg w₃,arg w₂−arg w₃)`, and
`u=I−B₀(φ)`. In Lean evaluate the periodic factors through `wⱼ/|wⱼ|`, avoiding an
`arg` branch cut. Require an invertible V for these coordinates; if using canonical chart
identities, prove V orthogonal exactly (§3). Define the observable `Aⱼ(z)=Fⱼ(u,φ)`.
The letters A here denote approximate integrals, not the SJS integer matrix below.

The numerical graph `τ̃` is not needed in the final definition. A fixed finite center
`B₀` suffices if the boundary certificate passes on its tube; alternatively pin a finite
approximation to `B₀+τ̃` and charge its error. Avoid defining the tube by an uncertified
Newton root.

Proposed acceptance literals are

* `δ=1/10^6`, `T₀=5·10^9` years in the dataset clock;
* `ηⱼ=1/(2·10^16)=5e-17` for each of the three observables;
* rational centers `cⱼ`, chosen from the numerical `F(z_nom)` and enclosed rigorously.

Set `U={z: |uⱼ(z)|<2δ for all j}`, `D=U ∩ {z: |Aⱼ(z)−cⱼ|<δ for all j}`, and
`Q=closure U ∩ {z: |Aⱼ(z)−cⱼ|≤δ/2 for all j}`. Restrict these definitions to the
open polar domain W; prove `closure D ⊆ W`, compactness and `Q ⊆ D` from positive
modal actions, an upper action bound and strict separation at the tube faces. In Cartesian
coordinates the angles are compact circles; an infinite lifted angle cylinder would not
satisfy the compact-closure premise of ApproxIntegral.

**Candidate theorem, with all constants and functions fixed before the initial point:**
`z_nom ∈ Q`, Q contains a nonempty open neighborhood of `z_nom`, and **for every** `z₀ ∈ Q`
there are maximal endpoints `Tm,Tp` and a solution z of `ż=X_H18(z)` in W with
`z(0)=z₀`, `Tm<−T₀<T₀<Tp`, agreeing with every other solution through z₀ on its
order-connected interval in W. **For every** real t with `|t|≤T₀` and every `j∈Fin 3`,

`z(t)∈D`, `|Aⱼ(z(t))−Aⱼ(z₀)|≤5e-17 |t|≤1/(4·10^6)`,

and hence `|Aⱼ(z(t))−cⱼ|≤3/(4·10^6)` and `|Iⱼ(z(t))−B₀,ⱼ(φ(t))|<2/10^6`.

The certificate must **prove**, not assume in this application theorem:

1. Smoothness of the literal observables on W, compact containment, and nominal containment.
2. On every tube face, `|Aⱼ−cⱼ|>δ` for the corresponding j, with a positive rational margin.
3. On `closure D`, `|dAⱼ(X_H18)|≤ηⱼ`.

For the F-faces the strict first-exit inequality is
`δ/2 + T₀ηⱼ = 3δ/4 < δ`. This is why the proposal uses a conservative five-billion-year
literal rather than `T=min δ/(2η)`: equality at that numerical supremum does not meet the
landed theorem's strict boundary-separation premise or yield existence *past* ±T.

This is a direct instance of the **ordinary** theorem
`KAM.Application.Confinement.hamiltonian_approxIntegrals_confinement` (namespace verified in its file),
not literally an instance of either frozen B1 anchor. A new literal application anchor is
needed if the owner wants this result frozen. The alternate canonical-chain version below
would instantiate frozen `torus_confinement`. Do not relabel the direct observable proof as
an oscillator-confinement proof.

**Which actions drift?** Aⱼ are corrected actions. Raw modal Iⱼ have genuine oscillations
of order `10^-5`, so the `2.5e-7` drift conclusion cannot be transferred to them unchanged.
For any physical observable Oᵢ, certify
`|Oᵢ−dᵢ−ΣⱼBᵢⱼAⱼ|≤eᵢ` on D; the landed observable-transfer lemma yields
`|Oᵢ(z(t))−Oᵢ(z₀)|≤2eᵢ+|t|Σⱼ|Bᵢⱼ|ηⱼ`.
For raw modal actions another immediate bound is
`|Iⱼ(t)−Iⱼ(0)|≤osc(B₀,ⱼ)+4δ`, with a certified oscillation bound.
The sampled eccentricity intervals in gate 2 are candidate targets for a separate range
certificate, not consequences of the displayed small corrected-action drift alone.

### 2.3 Alternate B1-T statement and extensions

With a certified canonical chart Ψ and inverse, the frozen B1-T target is: for every
`w₀=(θ₀,J₀)` with `|J₀ⱼ|≤aⱼ`, a unique physical solution exists past ±T₀ from Ψ(w₀),
with `|(Ψ⁻¹z(t))ᴵⱼ−J₀ⱼ|≤ηⱼ|t|` and `|(Ψ⁻¹z(t))ᴵⱼ|≤aⱼ+T₀ηⱼ<bⱼ`.
For normalized actions in the source units choose `a=δ/2,b=δ,η=5e-17`, subject to
converting period, symplectic and time units consistently. This requires the exact chart,
not just pruned observables, and is more work than §2.2 for the current data.

For a fuller Hamiltonian `H*=H18+ΔH` in a justified common coordinate/clock system, prove
`sup_D |dAⱼ(X_ΔH)|≤εⱼ`. Then reuse the same first-exit theorem with rates
`ηⱼ+εⱼ` and strict `δ/2+T₀(ηⱼ+εⱼ)<δ`. This is an honest **conditional helper**, with a
distinct name. An unconditional Newtonian application must discharge the ΔH estimate,
coordinate reconstruction, fast-action control and initial-set identification.

## 3. From floating SJSU objects to certificates

### 3.1 Exact polynomial versus an enclosed analytic model

There are three materially different levels:

| Model policy | Rounding/truncation obligation | Scope of conclusion |
|---|---|---|
| Exact decimal polynomial H18 | Parse decimal strings into ℚ; certify all subsequent computation; no omitted degree-20 term in this definition | Literal reconstructed polynomial only |
| Exact Laplace-based truncated normal form | Enclose π, mass/axis factors, roots, Laplace coefficients, finite divisors and all finite algebra, including rounding to H18 | A specified truncation with genuinely analytic coefficients |
| Exact planar Newtonian Hamiltonian | Additionally bound eccentricity degree >18, fast Fourier order >16, omitted fast-action powers, all omitted Lie orders/mass terms, averaging error and inverse coordinate/clock maps | Full planar four-body dynamics, if the same rate budget closes |

The file was generated with mpmath, not exact rational Laplace integrals. Its masses use
`m₀=4π²` and exact printed mass ratios; the reference axes were selected by a floating
long-time average. Pinning those axes as parameters is legitimate; asserting that they
are exact averages is a different theorem.

A rigorous Laplace evaluator can use the positive series already written in
[laplace.py](../../applications/sjsu/scripts/laplace.py):

`tₘ = 2 (1/2)ₘ (1/2)ₖ₊ₘ/(m!(k+m)!) · α^(k+2m)`.

For the n-th Euler derivative, multiply by `(k+2m)^n`. At rational or enclosed α with
`0<α≤α₊<1`, bound the ratio of consecutive derivative terms for every m≥M by

`q = α₊² · sup_{m≥M} ((m+1/2)(k+m+1/2)/((m+1)(k+m+1)))
                 · ((k+2m+2)/(k+2m))^n < 1`.

Handle the zero exponent separately. Prove this uniform ratio bound; then the omitted
sum is at most the first omitted term divided by `1−q`. Use outward dyadic arithmetic
for the finite computation and all derivative orders actually consumed. A rational
partial sum is not the full Laplace coefficient. The present code stops after three
small terms; despite its docstring, it does not return or implement that geometric-tail
certificate. Arbitrary precision agreement is useful regression evidence only.

For coefficient intervals `h_e∈[h̄_e±r_e]`, retain their correlations where possible and
bound the error bracket directly, e.g.
`Σ_e r_e sup_D |{Aⱼ,M_e}|`. A scalar H-error without a derivative/analytic-radius bound
is insufficient. For analytic omitted terms use derivative majorants or Cauchy estimates
with explicit positive radius losses. Account for the entire omitted expansion, not just
its first homogeneous term.

### 3.2 Charts and normalization

The numerical stages are a good **untrusted producer**: constant modal actions, free-frequency
Kolmogorov steps, Birkhoff steps, recentering, a Lagrangian graph projection, then repeat
around `B₀`. Their floating convergence is not a proof obligation if the final Aⱼ are checked
directly. Pruning is valid because any smooth literal Aⱼ with small actual brackets works;
no exact identification with a Lie pullback is required.

If instead retaining Lie-chain provenance:

* `checkOscChain` fits polynomial Hamiltonians and Cartesian generators around the origin.
  It covers HH and a smaller SJSU box in principle. The measured nominal origin route fails;
  importing the checker cannot repair that analytic failure.
* `checkTorusChain` fits the finite trigonometric generators of both Kolmogorov and Birkhoff
  normalization. It checks finite Lie identities, not how the generator was found; no
  infinite Diophantine premise is required for finite-time confinement. Near resonant
  terms may be retained in the remainder. Its current `Nact` must be action-only; a
  general resonant normal form belongs under a separate observable-based contract.
* The actual polar H is `Σ c ∏(B₀,ⱼ(φ)+uⱼ)^((aⱼ+bⱼ)/2) exp(i k·q)`. Half-integral
  powers and nonconstant B₀ make this an **infinite** Taylor/Fourier expression. The current
  Boolean checker would prove a theorem only for its finite `ftEvalR c.H`. Extend its input
  with a proved analytic remainder and derivative budgets through every flow, or use the
  direct observable checker. Finite Lie Taylor sums themselves are not exact flow maps;
  Program B's domain and Lie-tail proofs are essential.
* The floating Jacobi V is neither exactly orthogonal nor exactly diagonalizing. One option
  is an exactly orthogonal rational approximation via rational rotations/Cayley parameters;
  retain the off-diagonal quadratic terms. Another is an enclosed algebraic diagonalizer.
  For direct observables a merely invertible rational V is sufficient **if all derivatives
  are taken in the original canonical variables**; do not then use canonical modal-bracket
  identities without the resulting matrix correction.
* An exact finite scalar S makes `I=B₀+u` canonical when `B₀=I*+c₀+∇S` with the chosen
  sign convention. A small measured nongradient component does not prove this identity;
  define the projected shift exactly and recompute the literal brackets.
* The producer stores two relative angles and three actions. This is symmetry-compressed
  data, not a two-pair canonical chart: lift keys to `(k₁,k₂,−k₁−k₂)` in `Fin 3 → ℤ`, or
  prove an actual AMD reduction with the third action as a parameter.
* Source q has period 2π and `{q,I}=−1`; the repository FT layer has period-one angles and
  canonical sign. For example θ=−q/(2π), J=2πI is canonical. This introduces π factors in
  action scalings; current FT tags have nonnegative powers only. Alternatively retain I and
  prove the accompanying Hamiltonian/time scaling. Charge this adapter explicitly, including
  the conversion back to years. Merely relabeling q as θ changes the equations.

Multiplying the polar observables by denominators is not a free polynomial solution:
`{D A,H}=D{A,H}+A{D,H}`. The second term and the changed boundary ranges must be bounded;
odd powers of `|w|` may still leave square roots. The direct analytic tube checker preserves
the useful cancellations most transparently.

### 3.3 Recommended checker contract

Build an ordinary `checkSjsuApproxIntegrals` (proposed name, **not present**) with soundness
ending at ApproxIntegral. It consumes exact H18, exact coordinate/observable literals,
positive tube domains, rational centers and radii, and independently checkable intermediate
models. Its proof obligations are:

1. A sparse finite real Fourier–Taylor algebra with derivative-aware remainder bounds,
   outward coefficient rounding and a proved Cartesian/polar evaluation bridge.
2. Positive modal-action bounds on the **whole** tube; sound sqrt/inverse models on that
   domain; composition with B₀ and all omitted action and Fourier tails.
3. Exact cancellation in each retained `{Aⱼ,H18}` block before taking absolute values.
   Majorizing the two Poisson-product halves separately would lose the small residual.
4. Boundary-face separation, initial containment, and optional eccentricity ranges, using
   analytic norms or a certified subdivision cover. Vertex sampling is insufficient.
5. A final finite rational conjunction giving strict separation and rate bounds; split
   kernel checks reassemble that conjunction. The application theorem has only `z₀∈Q`
   as its initial-data hypothesis, not a supplied bracket inequality or a supplied `check=true`.

Retain all three approximate integrals even if pruning breaks the exact sum identity.
Prove exact AMD conservation separately from H18's charge balance; it is useful but not
needed to justify an otherwise valid three-observable first-exit certificate.

## 4. Candidate planar SJS theorem and pipeline

### 4.1 Fix the Hamiltonian, frequency, energy and units

Use the exact reduced planar Hamiltonian implemented mathematically in
[hsyn.py](../../scripts/sjs/x1/hsyn.py): masses `m₁=9546/10000`, `m₂=2856/10000`,
`μ=1/1000`, total angular momentum `C=3.05839852910896096675` interpreted as an exact rational,
with the regular synodic canonical coordinates and `Λ₂=C+I₅+I₆−Λ₁`. The formula is

`H = −m₁³/(2Λ₁²) − m₂³/(2Λ₂²)
     + μ (|V₁+V₂|²/2 − m₁m₂/|X₁−X₂|)`.

Positions and momenta are obtained from the regular Kepler variables, including the exact
solution F of `λ=F−k sin F+h cos F`. These equations and the canonical reduction must be
proved equivalent to the intended planar Hamiltonian, not defined by executing Python's
finite Newton loop. The masses here are FH's scaled constants, not the SJSU dataset's
AU/year mass convention.

A concrete arithmetic candidate from the committed
[frequency receipt](../../scripts/sjs/plan/results/sjs_dioph.json) is

`r³−r−1=0`, `1<r<3/2`, `Dω=56234133`,

```
A = [[ 835682, 1466520, 1107043],
     [ 336682,  590836,  446009],
     [   -184,    -323,    -244]],
Ω = A · (1,r,r²) / Dω.
```

Our exact integer determinant calculation gives `det A=−6340`, so the three polynomial
coordinates are independent over ℚ. Irreducibility of `x³−x−1` and an algebraic-norm
argument give the all-integer-vector lower bound after enclosing its other conjugates.
The numerical norm constant is `2.771548805031541…e-7`, **less than** the rounded `2.8e-7`
in the plan. A safe proposed raw-unit lower bound is `γraw=27/10^8`; prove it with rational
root/conjugate bounds. The existing [CubicDiophantine](../../KAM/Certificate/CubicDiophantine.lean)
proves a different `x³−2` example, so this instance/generalization is still needed.

The X1 embedding is wound: `K(p)=(A_w p+q(p),act(p))`, with `A_w=F_s Gᵀ` in its
notation, unrelated to the integer matrix A above. Prove the unimodular angle change and
its dual action transformation, then convert to the repository's period-one **primary**
embedding. For `θ=Gᵀp`, the parameter frequency is `G⁻ᵀΩ`. Transform both the analytic
strip and the Diophantine lower bound. If `k·G⁻ᵀΩ=(G⁻¹k)·Ω` and
`|G⁻¹k|₁≤C_G|k|₁`, a safe bound is `γraw/C_G²`, before period/time scaling.
Frequency-specific conjugate bounds can give a better constant directly in this frame.
The X1 strip weight is measured in the original lattice; an adapted-frame box does not
preserve that strip automatically.

For a concrete isoenergetic target propose the exact energy
`E*=−0.10643795635888591243808637078709`, from the X1 energy receipt, and an initial ray
scale `s₀=1001/1000`, upper scale `σω=501/500`. In the final normalized chart/clock define
`ω*=Ωnormal/s₀`. Certify the ray margins and take a conservative rational lower bound
for `γraw` after **all** frame, period, s₀ and clock factors. E* also transforms if the
Hamiltonian is rescaled. These are proposed literal choices: the producer must solve at
this energy and direction; its current fixed-frequency torus does not already do so.

### 4.2 Exact shape of the theorem

Once a literal certificate c is fixed, its rational `ρ∞>0`, `μcert>0`, `σK`, `disp`,
frequency box and derivative bounds are fixed constants, not existential substitutes for
failed checks. **There exist** `K∞ : (Fin 3 → ℂ) → (Fin 3 → ℂ) × (Fin 3 → ℂ)` and
`s∞∈(1,σω)` such that:

* K∞ is holomorphic on the specified smaller strip, primary under integer shifts, and real
  on real arguments;
* for every θ in that strip, `DK∞(θ)(s∞ω*)=X_H(K∞(θ))`, `H(K∞(θ))=E*`, and the ball of
  radius `μcert/2` about K∞(θ) lies in the certified collision-free domain;
* for every such θ, `‖K∞(θ)−Kc(θ)‖≤disp` and `‖DK∞(θ)‖≤σK−μcert/2`;
* `‖s∞ω*−s₀ω*‖≤disp` in the certificate's clock and norm.

This is the **literal `CertifiedTorus c ω*` conclusion**, with no unproved Diophantine or
residual premise left in the final application. For every real phase θ₀, the curve
`t↦K∞(θ₀+t s∞ω*)` is an all-time reduced Hamiltonian solution. To call its image an
embedded Lagrangian torus in the full geometric sense, also derive Lagrangianity from
exact invariance and prove a projection bound `‖D(K∞^θ−id)‖<1` on a smaller strip (or an
alternative injectivity argument); the definition itself does not explicitly assert those
extra clauses. The positive modal actions and collision exclusion are uniform domain facts.

**Unfixed constants remain visible:** no current certificate specifies a verified positive
ρ∞ or a verified displacement number for this new frequency/energy. They must be computed
and written into the application before freeze. The expected source strip is `0.02` in
radian-angle units, i.e. `0.02/(2π)` geometrically in period-one coordinates before the
frame change; a rational inner strip must be chosen. Claiming a particular closeness now
would invent a numerical receipt.

The implementation route is `checkV2With_sound` (packed base checker plus a proved route-B
engine), or `checkTorusCertificateV2_sound` with the landed base. The relevant sealed
source interface is [I-G1 `KAM.Iso.isoenergetic_kam`](../../KAM/Frozen/Iso/Theorems/IsoenergeticKam.lean).
For effective constants the implementation uses the ordinary sharpened v2 branch
`KAM.Iso.Sharp2.RouteB.iso_g1_branch_B` / `iso_g1_v2B_frozen`; “frozen” in the latter name
means the frozen *form* of the hypotheses, not a new manifest anchor. Thus it supplies
an instance of the I-G1 **conclusion**, using stronger effective machinery, rather than
computing the existential constants of the original anchor. A literal SJS application
would need its own approved anchor. There is no existing frozen SJS-X1 theorem to seal.

This is an invariant torus in the **reduced three-degree-of-freedom** system. Full planar
Newtonian reconstruction must restore the removed rotation and prove the time/coordinate
identification. An extra cyclic phase cannot simply be declared a fourth independent
quasiperiodic frequency. Also, one 3-torus does not separate a 5-dimensional energy surface;
the lunar barrier argument cannot give confinement of its neighborhood here.

### 4.3 What must pass before this theorem exists

1. Regenerate a high-precision candidate at the exact algebraic frequency direction and
   selected energy, keeping the resonance and satellites. Enclose all discarded modes.
   The X1 coefficients beyond L≈22 are not established input accuracy at L=45.
2. Prove the regular Kepler solver as a complex analytic implicit function on the certified
   tube. Supply residual/contraction or interval-Newton witnesses and a nonzero derivative
   `1−k cos F−h sin F`, with real/periodic identities, gradients, Hessians and the next
   derivative needed by the vector-field majorants. Extend the expression/jet checker or
   introduce a proved semantic adapter. The current `sqrt`/inverse nodes help, but do not
   establish the Kepler equation. Polydisc sampling of denominators cannot replace this.
3. Certify Hamiltonian identity and all complex-domain bounds, including positive-real-part
   square-root branches, Λ positivity, modal-action margins and pair distance. Use interval
   boxes/subdivision or analytic norms. The plan's sampled majorants times two are only
   a pilot choice, and the current Delaunay box crosses its e=0 singularity.
4. Check the full analytic invariance and energy errors, Gram inverse, **bordered
   isoenergetic torsion** inverse, derivative/frame bounds, finite divisor sites and the
   infinite Diophantine tail. Ordinary twist is not the bordered torsion check.
5. Connect the packed arithmetic and the chosen route-B engine to `BaseFacts` and the
   refined `HamFacts`/`FrameFacts`. Prove equivalence of block assembly, signed products,
   truncation, norm tails, rounding and witness checks. Existing packed lemmas are reusable;
   an external FFT, GMP calculation, or checksum remains untrusted certificate production.
6. Kernel-check every arithmetic shard, then the assembled checker fact, algebraic frequency
   proof and literal application. Audit the generated closure and `#print axioms` there.

The finite `FreqEncloses` box encloses **one exact proved vector**. It is not a claim that
all vectors in that box are Diophantine: every open frequency box contains resonances.

### 4.4 Optional near-torus confinement

B5 supplies `N(J)=E*+(s∞ω*)·J` and a derivative estimate
`|∂θⱼR|≤C₃B²/2`, `C₃=64(M μcert/2)/r³`. With `|J₀ⱼ|≤aⱼ`, `bⱼ≤B` and
`aⱼ+T C₃B²/2<bⱼ`, it gives the B1-T conclusion. All chart widths, inverse/projection
checks and r must be certified. This typically gives an inverse-radius time; it does not
by itself supply a five-Gyr neighborhood. Higher Birkhoff normalization or direct
approximate integrals would be needed if that number is wanted.

There is an additional implementation gate: [CertifiedTorusRoute](../../KAM/EffectiveStability/CertifiedTorusRoute.lean)
takes `G1Hyps c ω*`. Its [definition](../../KAM/Certificate/Defs.lean) includes `hC1` and
`hdisp` for the old `Iso.Apost.isoC1/isoC2`. The [v2 engine](../../KAM/CertificateSharp/V2/Engine.lean)
returns `BaseFacts` plus `CertifiedTorus`, not those old smallness inequalities. Passing
route B therefore does not directly type-match B5. The inspected B5 proofs use standing
analytic/domain facts and the exact torus. Refactor/add ordinary adapter lemmas over
those facts and `CertifiedTorusAt`, retaining every needed hypothesis; independently
verify the resulting dependency closure. Do not fabricate `G1Hyps`, assume the old
threshold, or edit a frozen statement to hide this issue.

## 5. Adversarial checks and first unpaid inequalities

The small independently written check is in `.drafts/astra-rigor-check.py`, with receipt
`.drafts/astra-rigor-check.log`. It ran under `nice -n 10`, a 6-GiB address-space cap and
1800 CPU-second limit: 0.19 user + 0.04 system seconds, peak 41,496 KiB. Exact claims below
use integers/Fractions; the cubic conjugate evaluation is 90-digit mpmath, **not** an
interval proof. No expensive torus regeneration was attempted; the large `.npz` candidates
are not committed with the receipts.

### A. Model and literal integrity

* Hash matches the published SJSU model pin. There are 7,941 complex terms, with degree
  counts `9,36,100,225,441,784,1296,2025,3025` at degrees 2,4,…,18.
* Every term has equal z and z̄ degree, and every conjugate-swapped coefficient agrees
  **exactly** as a rational. Thus the complex-form model passes the elementary AMD/reality
  algebra check. The floating `{C,H}` coefficient residual is not a defect in that model.
* Independent conversion of degrees 2 and 4 to real variables found 47/78 rounded-real
  disagreements, maximum `2e-27`. For the `η_U^4` coefficient the converted complex form
  minus the printed real form is `−1/40000000000000000000000000000`.
  Smallness makes this inexpensive to handle, but exact equality would be false.

### B. The numerical SJSU margin is substantial but not a bound

At δ=`1e-6`, the committed full rate maximum is `1.1625307343076705e-19`; the proposed
five-Gyr threshold is **strictly below** `δ/(2T₀)=1e-16`. Their ratio is 860.1923.
Our proposed `5e-17` rate leaves `2.5e-7` of strict action-level separation. This is a
reasonable enclosure target, not evidence that every new error term fits it.

Code-level obstructions to reading gate 2 as a certificate:

* [measure.py](../../scripts/sjsu/gate2/measure.py), `profile`: sums absolute discrete FFT
  coefficients. A finite Fourier grid can alias an arbitrarily large unobserved analytic
  tail; “full grid” is not a full Fourier norm. Composition with `sqrt(B₀+u)` has infinite
  Fourier support even if B₀ is finite. The producer's alias-free finite polynomial products
  do not solve this new infinite-support issue.
* `torus2.py` computes Bmin/Bmax as minima/maxima of grid values `B₀+τ₂`, not uniform
  extrema. Prove the missing interpolation/derivative margin or use analytic enclosures.
* `measure.py:_seq` stops each binomial series at order 80; `deriv_tails` convolves those
  finite arrays, with no certified tail beyond 80. For nonintegral powers this omitted
  tail is nonzero. At the proposed ratio `2δ/B_U,min≈0.08` it should be cheap to bound;
  near the largest tested ratio ≈0.8 it is much less negligible. It must be included at
  both ratios, regardless of numerical relevance.
* `torus2.py:h_useries` describes its re-expansion as “EXACTLY” at grid angles, but uses
  floating `log`, `exp`, binomial factors and FFTs. The underlying formula is exact;
  the coefficients and the finite Taylor/Fourier representation are not.
* The measured float noise floor is an observed residual, not a rounding-error enclosure.
  Exact arithmetic removes rounding noise while exposing the exact residual of the rounded
  candidate; there is no theorem that this residual is bounded by the observed floor.

**First unpaid SJSU inequality:** on the entire specified Cartesian tube,
`sup |dAⱼ(X_H18)|≤5e-17`, together with the strict boundary enclosure. This precedes any
kernel throughput question. Returning the floating η or its FFT sum as an input hypothesis
would leave precisely the requested application unproved.

### C. Degree 18 does not answer the full-model truncation question

The reported degree-18 Hamiltonian majorant is `1.7e-20` at nominal modal radii. Multiplying
by its maximum angular order 18 gives a very rough `3.1e-19` scale for its angular
 derivative, before DF and chart factors. This is not a bound on the missing degree-20
term, let alone the sum of all missing terms. Ratios of the last two computed degrees
cannot certify convergence or an analytic tail. Conversely, no evidence here proves
that the eccentricity tail necessarily dominates the five-Gyr budget.

The more serious uncontrolled discrepancies are fast-angle averaging and omitted mass/Lie
orders: [model recovery](sjsu-model-recovery.md) reports quadratic discrepancies up to
`7.7e-4`, quartic differences of several percent, and nonlinear frequency differences
from full planar N-body numerics. Those discrepancies cannot be converted directly into
bracket lower bounds—integrable shifts may commute with the observables—but they rule out
using decimal precision as the full-model error budget.

For any fuller field the first unpaid estimate is
`sup_D |dAⱼ(X_full,pulledback−X_H18)| < 1e-16−ηⱼ`, in the **same action/year units**,
with all coordinate and initial-data transfers proved. Neither LP's existential constants
nor the exact AMD identity pays this estimate. Current evidence neither proves a useful
full-model bound nor refutes the possibility of a better adapted normalization.

### D. SJS precision, exact resonance and the changed arithmetic target

Reading X1's three printed decimal frequencies as rationals gives the exact nonzero
resonance

`k=(338240117059304358259, −839549288702546301204, 0)`, `k·ωprinted=0`.

Therefore the printed-frequency torus cannot support a positive all-k Diophantine claim.
This does not contradict X1's numerical aim or a nearby irrational torus. The cubic
candidate has `det A≠0` and is a viable way to specify such a vector, once the norm bound
is proved.

For `k₀=(27,−67,31)`, the exact printed-decimal divisor is
`1540872990536831/2000000000000000000000 ≈ 7.70436e-7`.
Our high-precision evaluation at the proposed cubic vector gives `4.50642732612e-7`.
The squared-divisor amplification increases by about 2.9. A blanket coordinate tolerance
`1e-8` permits a k₀-dot-product change as large as `125e-8=1.25e-6`, larger than the old
 divisor. X1's finite resonance census must be recomputed at the chosen exact vector.
The smaller `γ=2.7e-7` in raw units is still far below this individual divisor after
`|k₀|₁²`; the issue is generator conditioning and faithful frequency-specific constants,
not an observed failure of the algebraic Diophantine route.

Production in-band residual `7.5e-32` and out-of-band ℓ¹ mass `2.3e-26` differ by
`3.07e5`. The latter is `2.3e12` times the modeled `1e-38` threshold, even before converting
to the needed strip norm. These norms differ, so this ratio is a diagnostic scale comparison,
not a formal failed checker test. The check grid's `5.8e-25` tail is larger still. Both
reported grids omit `2k₀`; agreement through L=22 is not a proof of a small infinite tail.
The scalar energy spread `3.8e-30` is another check, not a substitute for invariance.

**First unpaid SJS inequality:** a proved complex-strip residual/energy bound and domain
majorants that pass the actual route-B finite checks at the proved algebraic frequency.
Forty-eight digits is the old *producer estimate*, not a guaranteed sufficient precision;
allow roughly 60–80 digits during the enclosure pilot if the budgets require it.

### E. Coefficient-format collision experiment

Using the actual 7,941 SJSU decimal coefficients, truncating their scaled mantissas at
`P=174` gives **0/7,941** large values with zero low 64 bits. First rounding the same
coefficients to binary64 and then scaling to P=174 gives **7,941/7,941**. This is an exact
integer census on those two proposed encodings, not a kernel timing measurement.

Binary64 mantissas have only 53 effective bits; promoting them to a much wider fixed-point
format creates long zero suffixes. Double-double has about 106 bits, so SJS values promoted
to 174 bits can also have shared low limbs, depending on exponent and the actual low word.
The large X1 arrays were not available for a complete census. Common powers-of-two
rational denominators and padded packed cells deserve the same check. High precision
alone is not a performance guarantee.

## 6. Certificate sizes, kernel costs and memory

All estimates below are **engineering scenarios**, not measured SJSU/SJS kernel costs.
No cost bound follows from a support count alone. Prices for rented hardware are deliberately
not estimated; the needed RAM, disk and execution budget should be chosen after the pilot.

### 6.1 Calibration and what survives extrapolation

| Calibration | Observation | Legitimate use |
|---|---|---|
| HH | 34 shards, 27 CPU-min, peak 3.4 GB | About 47.6 CPU-s per shard **of that workload**; unmerged list growth and recursion were binding |
| SO-3, brief's final campaign figure | 13,668 generated modules, about 10,000 modules/hour on 64 cores | At sustained full utilization, 23.0 CPU-s/module; 13,668/10,000 ≈1.37 hours is only a same-workload throughput projection |
| SO-3 DELTA-LAM-3 memory probes | Ten hard segments peaked at 17.2–25.5 GiB and passed in 32-GiB lanes | A 6-GB or 8-GB lane is not adequate for every existing proof shape |
| SO-3 literal-hash experiments | Real 410-row decode 67.7 s versus 3.2 s whitened; combining corner checks caused superlinear costs | Format and declaration boundaries matter independently of total arithmetic |

SO figures come from the brief and the read-only lock-team notes
`/root/code/KAM-inp-lockdata/.drafts/DELTA-LAM.md` (first delta), `DELTA-LAM-2.md` through
`DELTA-LAM-5.md`, and the committed [literal-hash report](lean-kernel-nat-literal-hash.md).
The latter has an earlier source census of 13,694 files; that is not the same count as the
brief's final 13,668-module chain. These are reported campaign receipts, not rerun here.
Module count is a packaging choice; do not divide a predicted SJS module count by 10,000
and call that its measured runtime.

### 6.2 SJSU: small input, potentially large composition

The useful pruned rows retain about **6,542–12,773 complex coefficients total** across
three observables (the `1e-17` and `1e-19` rows), rather than 965,745 unpruned coefficients.
Add 2,790 shift modes (396 above `1e-20`) and the 7,941 Hamiltonian monomials. Expect
roughly **1–10 MB** of initial sparse literals at 128–192-bit coefficient precision,
including indices, centers and bounds; the current JSON H alone is 3.2 MB. Exact decimal
rationals and Lean syntax have overhead, so this is an order-of-magnitude payload estimate.
The uncommitted observable arrays must first be reproducibly exported.

A naive pairing of retained observables with H already entails `5.2e7–1.0e8` monomial
pairs before derivative multiplicities and compositions; all six Poisson contributions
would multiply that work. Exploit charge symmetry, shared powers, sparse merging, Taylor
profiles and packed two-dimensional Fourier products. Retain cancellation before bounding.
A chain of naive unmerged rational lists is unlikely to inherit HH's small cost.

A **capacity scenario** of 200–5,000 arithmetic modules at 20–60 CPU-s/module gives
approximately **1–83 CPU-h**, plus input, checker and assembly costs. A defensible provisional
allocation is **10–300 CPU-h**, with a stop/re-scope before exceeding **1,000 CPU-h**.
Neither 5,000 modules nor that allocation is established sufficient. Reserve **0.1–10 GB**
for intermediate certificate/checkpoint artifacts as a pilot planning range, then measure.
Target individual production modules at 2–6 GB RSS by splitting; a sound cancellation-aware
composition pilot, not the observable file size, decides whether this range is credible.

If the proof needs repeated interval subdivision of the two-angle domain, let Ncover be
the number of cells and record cost proportional to Ncover; do not hide it inside the
coefficient count. The origin-route failure is not a reason to pay for a larger origin
certificate. The direct observable route avoids certifying all normalization intermediates.

### 6.3 SJS: retain X1's model as a conditional estimate

The committed [X1 cost JSON](../../scripts/sjs/x1/results/x1_cost.json) gives, including its
rising-slope scenario, S(45)≈`4.0–4.85e6`, box≈`9.1–11.2e6`, coefficient precision 174 bits.
The reversible packed factor is approximately **0.95–1.17 GB**; the six-component K input
is **9.5–11.6 Gbit**, approximately **1.2–1.45 GB of mathematical bits**. This is not a
340-GB file: 340–550 GB is its model of **cumulative charged kernel allocation** under
288-bit literal ingestion, spread across declarations; it is neither peak RSS nor raw data.
The plan's checkpoint ledger is approximately **55–165 GB** before source/build overhead.
K's support was measured; intermediate supports and enclosure growth were not remeasured.

| Packed policy, from X1 model | Arithmetic CPU-h | Arithmetic declarations | Modeled peak per shard | Caveat |
|---|---:|---:|---:|---|
| One large factor | 10–43 | 252–657 | 16–19 GB | Requires larger Nat limit; unsuitable for this shared research machine |
| About 3 blocks per factor | 20–94 | about 284–739 | 5.5–6.7 GB | Still exceeds the default Nat size; some exceed this brief's 6-GB research cap |
| Default Nat limit, 15–18 blocks | 107–590 | about 7,088–26,609 | about 1.5 GB | Products/checkpoints, import closure and all intermediate sizes still need measurement |

These are *declarations*, not complete module counts. With one heavy check per module,
plus input and assembly modules, a provisional **8,000–35,000 modules** for the default-limit
route is reasonable to budget, not a predicted census. At the SO throughput that would be
0.8–3.5 hours, but the arithmetic model says 107–590 CPU-h, and the graph has sequential
chains; these constraints cannot both be ignored. On 64 available cores the arithmetic
alone gives an ideal 1.7–9.2 hours; realistic utilization, I/O, ingestion, shared dependencies
and retries increase it. One modest lane takes days or weeks.

Plan **150–1,000 kernel CPU-h** provisionally for the default-limit SJS campaign, conditioned
on a successful packed pilot and ≤2× intermediate support. The lower 20–94 CPU-h scenario
is a useful large-Nat alternative only after explicit resource-policy approval and a real
literal benchmark. Reserve **hundreds of GB to about a TB** of non-root-volume disk for
source, checkpoints, build artifacts and replay; freeze a measured storage budget before
emission. The K-only literal model adds 2.4–4.2 elaboration CPU-h, but do not treat that
as the cost of ingesting the entire checkpoint ledger. That cost and reuse must be measured
without double-counting computed outputs as fresh literals.

For the new coefficient format, repeat the pilot at two support sizes and include imports,
decoding, product, tail norm, rounding, equality and proof assembly. If cost grows more
than about 3× beyond the modeled per-bit scaling, stop and change layout before emission.
A CPU estimate from native GMP alone is not the kernel estimate.

### 6.4 Apply all five lock lessons

1. **Whitening:** row-salted reversible encoding can reduce collisions among decoder
   intermediates; prove decoded equality. It does not fix decoded values divisible by `2^64`.
2. **Declaration splitting:** one row/column and sign vertex per check, then structural
   assembly, bounds the kernel cache lifetime. Avoid large `List.all` proofs that force
   all vertices in one declaration. Splitting modules also releases process memory.
3. **Elaboration:** use syntactically matching exported checkpoint statements and named
   length/lookup/equality lemmas. DELTA-LAM-1/2/4 fixed deep definitional evaluation and
   heartbeat failures this way; no resource override was necessary.
4. **Arithmetic representation:** compare exact dyadic/scaled coefficients, balanced chunks,
   and packed blocks; measure the low-limb distribution of *intermediate* arithmetic as well
   as storage. Never randomize significant coefficient bits to improve performance.
   Any rounding/requantization changes the candidate and must be enclosed and rechecked.
5. **Memory and Nat limits:** budget operand, product and transient sizes. The v4.35 reports
   identify the default `2^27`-byte Nat ceiling; keep products as well as factors below it.
   An authorized `LEAN_NAT_MAX_SIZE` choice is distinct from forbidden heartbeat/depth
   changes, but is not assumed approved here. Default-limit blocks are the baseline.

## 7. Incremental Lean work and difficulty

Estimates exclude generated data and reuse the current code, rather than rebuilding the
old 12–25k-line Program B design. They are planning ranges with roughly factor-two
uncertainty. Audit and failed approaches consume time without increasing final line count.

| New package | Handwritten Lean lines | Difficulty / existing base |
|---|---:|---|
| SJSU exact model parsing/evaluation, sign conventions, nominal literals, charge identities | 500–1,200 | Moderate; generic rational polynomial algebra exists |
| Cartesian/modal/polar bridge, positive domain, Fourier observables, exact finite shift | 1,000–2,000 | High; reuse real flow/FT and SO polar-chart patterns |
| FT models with analytic remainder, composition, derivative tails, merged bracket bounds | 2,000–4,000 | High; principal new SJSU certificate mathematics |
| Boundary/containment/observable instance and split-check assembly | 800–1,600 | Moderate–high; first exit and continuation already proved |
| **SJSU polynomial total** | **4,300–8,800** | Roughly 3–6 weeks including independent audits after successful enclosure pilot |
| Optional exact Laplace/generator enclosure and coefficient-error transfer | +2,000–5,000 | High; does not include full Newtonian averaging remainder |
| SJS regular canonical reduction, Hamiltonian identity and clock/primary conversion | 1,500–3,500 | High; reuse planetary coordinates, prove this normalization |
| Regular implicit Kepler node and complex/jet/domain soundness | 2,000–4,000 | High; existing sqrt/inverse semantics help |
| Cubic frequency, conjugate bounds and frame/clock Diophantine transfer | 500–1,200 | Moderate–high; existing cubic is a different field |
| Packed blocks/tails and route-B interfaces beyond existing packed code | 1,500–4,000 | High performance/proof integration risk |
| Literal SJS torus application, domain certificates and assembly | 500–1,200 | Moderate after previous gates |
| **SJS torus total** | **6,000–13,900** | Roughly 4–10 weeks including audit and data-pipeline iteration |
| Optional v2→B5 standing-facts adapter and literal confinement | +500–1,500 | Moderate, before any higher-order normal-form campaign |

These elapsed estimates describe a future campaign, not a commitment to launch agents or
builds in this task. Producer/writer work is additional: roughly 1–3k Python/native lines
for SJSU and 2–5k for high-precision SJS, depending on reuse. Full Newtonian SJSU transfer
has no justified finite line/time estimate from the present evidence; allocate a separate
research phase before assigning a formalization schedule. The older multi-month estimates
for model transfer remain more credible than claiming the existing LP theorem makes it
an immediate instantiation.

## 8. Gates, stop conditions and owner decisions

| Stage | Concrete pass condition | Proposed allocation / failure response |
|---|---|---|
| G0: choose and pin statements | One exact model representation, literal point, clocks, theorem scope; reproducible F/S export; exact SJS arithmetic/energy choice | 1–2 research days. No freeze until the choices and constants are reviewable |
| G1-U: enclosed SJSU tube | Every rate ≤`5e-17`, positive polar domain, strict boundary and nominal containment on δ=`1e-6` | A few days to two weeks of producer work; small jobs under the agreed cap. On failure name the largest unpaid term; do not reduce δ or change the model silently |
| G1-S: SJS frequency and analytic-domain pilot | Certified arithmetic candidate and Kepler/domain derivative bounds; actual route-B budgets computed in the correct units | 1–2 weeks, before final high-precision production. Stop if the complex domain crosses a singularity or the threshold is unaffordable |
| G2: representative kernel arithmetic | One real SJSU composition/bracket block and one real SJS 3-D packed product, at two sizes; all tails, decoding and assembly included | Future build-enabled worktree only; ≤10 CPU-h first allocation. Default heartbeats, measured RSS and literal census; redesign on superlinear behavior |
| G3: generic soundness and small full application | Audited checker contracts; a reduced-size complete replay; source identities and exact frequency lemma closed | Handwritten budgets in §7; verify the source theorem's conclusion, not only a checker return value |
| G4-U: SJSU production | All literals checked; no analytic/bracket hypothesis in application; nominal neighborhood and five-Gyr result | Release 10–300 CPU-h after measured extrapolation; seek a new decision before 1,000 CPU-h |
| G4-S: SJS production | Higher-precision candidate + all residual/energy/Gram/bordered-torsion/smallness checks + exact frequency proof | 150–1,000 CPU-h default-limit provisional budget; disk/RAM must first be reserved on a suitable machine |
| G5: freeze, seal and independent replay | Owner approves exact statement; all source/ABI/quarantine checks, targeted application build, replay and standard-only axiom audit pass | Opt-in application roots; generated roots managed by orchestrator; no core import of application data |
| G6: full-model or long-time neighborhood extension | Literal remainder/transfer inequalities pass in the same units | Separate project; no Newtonian or five-Gyr SJS neighborhood claim from G4 alone |

Owner decisions that change the theorem or campaign scope:

1. Accept the **exact complex-decimal H18 polynomial** as the first SJSU theorem, or require
   an analytic/full-Newtonian model from the outset. Recommendation: literal polynomial first,
   explicitly named as such, with analytic coefficient transfer as a separate result.
2. Accept corrected-action confinement at δ=`1e-6`, T=`5e9`, with nominal-neighborhood
   inclusion; choose whether eccentricity ranges are required in the first anchor.
3. Choose direct approximate integrals versus a canonical-chain theorem. Recommendation:
   direct observables first; preserve Program B's chain route for later reuse.
4. For SJS, approve a nearby **explicit cubic frequency direction and isoenergetic** result,
   rather than the literal printed rational frequency or exact fixed-frequency wording.
   Approve the exact Hamiltonian, energy, chart/clock conventions and reduced-system scope.
5. Allocate the Kepler/checker extension and select default-limit blocks or an explicitly
   recorded large-Nat replay policy. Recommendation: test default-limit blocks first.
6. Approve measured CPU/RAM/storage ceilings after the pilot; place large artifacts on the
   volume or dedicated production storage. This report does not authorize a remote job.
7. Approve final literal application statements only after the constants and source identity
   are audited. Reusable checker formats need not be frozen.

No owner response is required to complete this research report. These are future campaign
choices, not a request to pause already authorized work.

## 9. Errata, deviations, validation and handoff

### Source and implementation issues to carry forward

No frozen statement was found to require an edit. The B5 issue is an ordinary adapter
restriction, not a false frozen theorem. Suspected source defects already recorded in
[model recovery §6.3](sjsu-model-recovery.md#63-source-issues-resolutions-and-new-candidates)
and [the earlier audit §7](sjsu-effective-stability.md#7-source-issues-and-deliberate-deviations)
remain visible; their PDFs were **not re-adjudicated** in this task:

* SLG13 Appendix A's printed quartic coefficients violate the expected standard AMD identity;
  earlier exact witness `−2a+2b+c=3.13566324343412e-7`. This is not the exactly charge-balanced
  reconstructed H18 used here.
* SLG13 Table 2 / equation (24), “R_j=√(x_j²(0)+y_j²(0))”, do not match the printed data and
  nominal Table-1 interpretation. Preserve the chosen Table-1 mapped-point policy.
* SLG13 §3.2 says generators are “up to degree 9”, while equations (6)–(7) cap them at 6;
  GLS17 separates degree-6 χ₁,χ₂ from the degree-9 resonant generator.
* SLG13 equation (12)'s half factor on the whole resonant sum has an unresolved scope issue
  at degree 11; the reconstruction follows the printed formula. Its degree-18 consequences
  are model differences, not included error bars.
* The source phrase `3λ₁−5λ₅−7λ₃` has an invalid index in a three-planet system. The prior
  GLS17 review also flags equation (13)'s index `j=0` and equation (57)'s `ρ^(l+1)` where an
  angle derivative preserves action degree l. These are inherited candidates/confirmed
  transcription issues as labelled in those reports, not new PDF findings here.

New local findings for the orchestrator's ledger/review, without editing that ledger:

* **RIGOR-U1:** `laplace.py` docstring says the geometric tail is bounded and checked;
  its loop implements a three-small-term stop without a returned/proved tail bound.
* **RIGOR-U2:** gate-2 “Every truncation tail” / “EXACTLY” wording must be read as a floating
  study. `measure.py` omits an explicit >80 binomial tail and infinite Fourier alias tail;
  `torus2.py` uses sampled Bmin/Bmax. These are gaps to close, not a demonstrated false
  numerical confinement time.
* **RIGOR-U3:** independently rounded complex and real tables are not exact equalities
  (§5A). Choose a defining representation and prove any transfer.
* **RIGOR-S1:** `2.8e-7` is a rounded-up display of `2.7715488…e-7`; do not use it as a
  literal lower bound. The printed decimals are rationally resonant. The proposed cubic
  changes the measured small-divisor census.
* **RIGOR-B5:** existing `certifiedTorus_confinement` requires old `G1Hyps`; add a v2-compatible
  standing-facts adapter before claiming automatic reuse.

For literature scope, the [FH arXiv v1 abstract](https://arxiv.org/abs/2403.10152v1) itself
characterizes its conclusion as numerical evidence from a KAM scheme. It does not supply
a Lean certificate. No claim of being first or of a complete current novelty search is
made here. The attempted GLS17 arXiv page fetch failed; source-specific GLS17 observations
above are attributed to the repository's prior reviews, not to a new web inspection.

**Deliberate proposed deviations:** exact polynomial rather than the authors' unavailable
coefficient file/full field; exact complex table rather than independently rounded real
literals; direct pruned observables rather than replaying their normal-form derivation;
strict five-Gyr target rather than the measured optimum; an explicit nearby algebraic
frequency and selected energy rather than X1's printed rational frequency. None has been
silently installed in a frozen file.

### Checks performed and their limits

The only deliverable edit is this report. Scratch notes/checks are under `.drafts/`.
The exact audit script and receipt contain the arithmetic summarized in §5. Checks used
`nice -n 10 prlimit --as=6442450944 --cpu=1800 -- python3 -B ...`.

| Command/check | Result |
|---|---|
| `.drafts/astra-rigor-check.py` | Exit 0; model hash/symmetry, degree census, rational-frequency resonance, coefficient conversion, storage census and budget calculations completed; 0.23 CPU-s, 41,496 KiB peak |
| `python3 -B -I scripts/gen_root_imports.py --check` | Exit 0; no output |
| `python3 -B -I scripts/check_lean_modules.py --root .` | Exit 0; `check_lean_modules: PASS (18361 Lean files, 0 comparator configurations)` |
| `python3 -B -I scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json` | Exit 0; `FROZEN-ANCHOR GUARD OK` |
| Report relative-link/required-section check | PASS: 42 relative links, none missing; all nine sections present; `.lake` absent |
| `git diff --cached --check` on the staged report | PASS: no whitespace errors |
| Targeted Lean build / `#print axioms` / kernel replay | **Not run:** prohibited by this research brief; `.lake` remains absent |
| Full `scripts/lint_sources.sh` | **Not run:** inspection shows it invokes `abi_hashes.py`, which creates `.lake/abi-scratch` and runs `lake env lean`; this conflicts with the later brief's no-build/no-`.lake`/edit-scope restrictions. Safe static components above were run instead |

Axioms: this report declares no Lean result. The PR's existing ApproxIntegral and the HH
seal audit **report** only `propext`, `Classical.choice`, `Quot.sound`; those axiom receipts
were not rerun. Every future final application must have its own current `#print axioms`
and kernel replay; a static guard pass does not establish that application or a source
identity.

No Lean code is proposed in this report. Any subsequent Lean brief must repeat all eleven
AGENTS hard rules verbatim. In particular, the two rules emphasized by this research brief are:

1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure
   is a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will
   not elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.

**Disposition:** GO for bounded enclosure and arithmetic pilots. NOT YET for freezing either
application or scheduling bulk kernel emission. The first missing deliverables are actual
uniform analytic inequalities on the chosen exact model, followed by a representative
kernel receipt under the intended data format and resource caps.
