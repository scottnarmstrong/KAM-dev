# Program B: certified effective stability near a torus or an elliptic equilibrium

Research and implementation plan, 30 October 2026. Inspected checkout: `prog-b`,
`fb782d6947546b4a5121a509a76844e325f54987`. This document is the PROGRAM-B deliverable.
It proposes statements and work packages; it approves no declaration, launches no proof
campaign, and claims no new Lean theorem or completed numerical certificate.

**Recommendation.** Build B1, a checker for finite canonical normalizations and their
remainders, with a theorem giving existence, uniqueness and action confinement for an
entire initial region. Start with the short mixed-sign Hénon–Heiles calculation in
Caracciolo–Locatelli, Appendix B. Make a secular Sun–Jupiter–Saturn–Uranus lifetime the
intended ambitious application, jointly with D. Preserve a separate route to a numerical
restricted Sun–Jupiter Trojan result. Defer the asymptotic double exponential theorems
until the finite checker gives useful bounds on one complete example.

For the actual inner planets, B alone is not a plausible route to a uniform 5-Gyr
guarantee over an observational uncertainty set. Its useful contribution is the validated
normal-form machinery that C can use while retaining the important resonances. A small
neighborhood of a selected torus in a specified secular model is a plausible B target;
identifying it with the present inner Solar System is a different, unresolved problem.

## 1. Baseline and scope

The [ambition note](ambition.md), [PLAN](../PLAN.md), [DECISIONS](../DECISIONS.md),
[TRACKS](../TRACKS.md), generated [README](../../README.md), and the
[frozen manifest](../../manifest/frozen-anchors.json) were inspected. The manifest has
134 sealed definitions, 23 sealed theorems and one draft theorem, W-NLW2. These are
source/manifest observations, not fresh build or axiom receipts. Older Phase-0 labels in
PLAN/TRACKS are not evidence that the implemented N/P results are missing.

| Existing component and exact entry point | Reuse in B | Work still required |
|---|---|---|
| [Canonical setting](../../KAM/Canonical/Setting.lean), `poissonBracket`, `adPow` | Bracket, sign, weighted coordinates | Finite polynomial interpretation and efficient checked identities |
| [Flow inverse](../../KAM/Canonical/FlowInverse.lean), `flow_c`, `flow_e`; [symplectic flow](../../KAM/Canonical/Symplectic.lean), `symplectic`, `canonical_field`, `canonical_orbit` | Actual canonical flows, inverse and dynamics transfer | Certificate-facing bounds on their domains and displacement |
| [Lie Taylor formula](../../KAM/Canonical/Lie.lean), `taylor_lie` | Exact finite expansion with integral remainder | Numerically sharp bounds for the uncomputed tail and its derivatives |
| [N normal form](../../KAM/Nekhoroshev/NormalForm/NormalForm.lean), `KAM.NormalForm.normal_form` | Nonresonance, holomorphic canonical map, Fourier remainder | Finite data and local normal-form orders chosen for an application |
| [P oscillator averaging](../../KAM/Planetary/Averaging/OscillatorFinite.lean), `osc_averaging`; [planar Birkhoff result](../../KAM/Planetary/PlanarTorsion/Birkhoff/Result.lean), `p11cB_result` | Mixed fast/oscillator estimates and an existing planetary quartic construction | A general finite Birkhoff checker; these are not such a checker already |
| [ODE continuation](../../KAM/ODE/Continuation.lean), `gen_confinement`, `gen_continuation_periodic` | Existence past the requested endpoints and uniqueness | Derive their confinement premise by first exit; never expose it as an unexplained application hypothesis |
| [v2 checker](../../KAM/CertificateSharp/V2/Engine.lean), `checkTorusCertificateV2_sound`; [all routes](../../KAM/CertificateSharp/V2/RouteAll.lean), `routeV2All` | Optional exact invariant torus and bounds | A canonical neighborhood and transverse derivatives; the output is an embedding |
| [Hybrid theorem](../../KAM/Sharp2/Hybrid/G1.lean), `g1_hybrid_R`, `g1_hybrid_B`; [iso hybrid](../../KAM/Iso/Sharp2/Hybrid/G1.lean), `iso_g1_hybrid_R` | Validated correction/restart estimates | Hybrid certificate wiring and a measured arithmetic workload |
| [N explicit constants](../../KAM/Nekhoroshev/Interfaces/Constants.lean), `HeadParams`; [N headline](../../KAM/Nekhoroshev/Assembly/Headline.lean) | Optional quasi-convex stability after normalization | Discharge the actual complex Hessian, frequency and quasi-convexity assumptions |
| [P cited-mass secular box](../../KAM/Frozen/Planetary/Theorems/SecularBoxAtCitedMasses.lean) | Existing all-time safety for its exact first-order secular model | A different model/region and sharper actions are needed for a new application |

**Snapshot correction.** Ambition §2 says hybrid is a design. At this later checkout the
fixed-frequency hybrid area contains nine Lean files, and the isoenergetic companion
theorems exist. Searching `KAM/CertificateSharp/` found no hybrid implementation;
`routeV2All` lists sharp, four A routes and two B routes, selected by a witness. Thus
theorem implementation exists, while a numerical hybrid certificate is not established
here. Read [the hybrid design](../campaign/design/APOST-SHARP-V2-HYBRID.md) with that
distinction. A Newton correction of a torus embedding is not a canonical map of a
neighborhood. Neither the hybrid correction nor its residual formula supplies B's chart.

The old [LG00 scout](sjs-lg00-scout.md) also predates v2 wiring and the `sqrt` primitive;
both are present. Its measured/sampled numbers remain scouting evidence. Ordinary twist
and bordered isoenergetic twist remain different hypotheses. An exact Diophantine vector
in the frequency box is still an external arithmetic proof obligation of the v2 checker.

This plan incorporates the proper-degeneracy discussion in
[planetary-and-nekhoroshev](planetary-and-nekhoroshev.md), the distinctions between a
torus and a physical region in [realistic-kam-and-finite-size](realistic-kam-and-finite-size.md),
the later corrections in [next-demonstrations](next-demonstrations.md), and the hardware
qualifications in [sjs-feasibility](sjs-feasibility.md). In particular, Mercury spin
confinement is not Mercury orbital confinement. The Moon-lock ruling explicitly chooses
a polar chart with no Birkhoff normalization; B must not become a prerequisite for it.

## 2. Mathematical targets and the small approval surface

### 2.1 Conventions and solution quantifiers

Use `Vec n := Fin n → ℝ`, `CVec n := Fin n → ℂ`, and
`Phase n := Vec n × Vec n`. Torus coordinates are lifted real coordinates
`(φ,J)`, periodic under `φ ↦ φ+k`, `k : Fin n → ℤ`; Cartesian coordinates are `(q,p)`.
No manifold or `EuclideanSpace` carrier is needed. The Pi/product norm is the maximum
norm. When a source uses a Euclidean norm, write the plain function
`sqrt (∑ j, x j ^ 2)` and prove the conversion; do not change the ambient type.

Use the existing field and bracket conventions:

\[
 X_H=(\partial_JH,-\partial_\varphi H),\qquad
 \{F,G\}=\sum_j(F_{\varphi_j}G_{J_j}-F_{J_j}G_{\varphi_j}),\qquad
 \operatorname{ad}_\chi F=\{F,\chi\}.
\]

The preserved form is the repository's
`symplecticForm(v,w) = ∑j (v.2 j*w.1 j-v.1 j*w.2 j)`.
An explicit chart must preserve this form on derivatives. Its inverse, regularity,
domain, reality and lattice behavior are part of the mathematical data, not inferred
from a small numerical symplectic defect.

For every lifetime conclusion below, the precise meaning is: for each allowed initial
point there exist an open interval `U : Set ℝ`, with `Set.Icc (-T) T ⊆ U`, and
`z : ℝ → Phase n`, such that `z 0 = z₀`, `z(t)` belongs to the stated regular domain
for `t ∈ U`, and `HasDerivAt z (X_H (z t)) t` there. Every other solution in that
regular domain on an interval containing zero agrees on its intersection with `U`.
The displayed bounds hold for **every** `t` with `|t| ≤ T`, including the endpoints.
Values of the total function outside `U` have no meaning and are not made unique.
Do not state `∃! z : ℝ → Phase n` for a finite-interval solution.

### 2.2 B1-T: finite confinement in a canonical cylinder

The following is an exact mathematical candidate for the first frozen theorem type.
It is a sufficient-condition theorem; §3 supplies its hypotheses from finite data.

For every integer `n ≥ 1`, vectors `a,b,η : Vec n` and `ε > 0`, real `T ≥ 0`, let

\[
 C_b=\{(\varphi,J):\forall j,\ |J_j|<b_j\},\quad
 \overline C_b=\{(\varphi,J):\forall j,\ |J_j|\le b_j\},\quad
 0\le a_j<b_j,\quad \eta_j\ge0,\quad a_j+T\eta_j<b_j.
\]

Assume the following explicitly, with no unquantified constant.

1. `V ⊆ Phase n` is open and invariant under integer translations of its first
   component; `H : Phase n → ℝ` is `C²` on `V` and periodic there.
2. `Ψ : Phase n → Phase n` is a `C²` diffeomorphism from `C_(b+ε)` onto an open
   subset of `V`, with a `C²` inverse on that image. It is symplectic and
   `Ψ(φ+k,J)=Ψ(φ,J)+(k,0)`. Thus the image of the closed fundamental cell
   `[0,1]^n × ∏j[-b_j,b_j]` is compact and lies in `V`. A quantitative checker must
   certify this inclusion using positive margins.
3. `N : Vec n → ℝ` is `C²` on `{J : ∀j, |J_j|<b_j+ε}` and
   `R : Phase n → ℝ` is `C²` on `C_(b+ε)`, `R` is angle-periodic, and
   `H(Ψ(φ,J)) = N(J)+R(φ,J)` throughout `C_(b+ε)`.
4. For all `w ∈ overline C_b` and `j : Fin n`,
   `|fderiv ℝ R w (Pi.single j 1,0)| ≤ η j`.

Then every `w₀=(φ₀,J₀)` with `∀j, |J₀ j|≤a j` gives the unique physical solution
through `z₀=Ψ w₀` on the requested interval, and, writing
`w(t)=Ψ⁻¹(z(t))=(φ(t),J(t))`,

\[
 |J_j(t)-J_j(0)|\le\eta_j|t|,\qquad
 |J_j(t)|\le a_j+\eta_jT<b_j.
 \tag{B1-T}
\]

The isotropic form sets `a_j=r`, `b_j=R`, `η_j=η`, giving precisely
`ηT<R-r` and maximum-norm drift `≤η|t|`. Zero remainder is allowed. It gives the
same conclusion for each finite `T`, hence an all-time corollary by uniqueness.
No Diophantine, twist, steepness, or exact-torus hypothesis belongs in this theorem.

For a specified observable `A : Phase n → Vec m`, matrix `L : Matrix (Fin m) (Fin n) ℝ`
and `d : Vec m`, the static bound
`|A_i(Ψ(φ,J))-(LJ)_i|≤d_i` on `overline C_b` implies

\[
 |A_i(z(t))-A_i(z_0)|\le2d_i+|t|\sum_j|L_{ij}|\eta_j.
 \tag{B1-transfer}
\]

This is an internal corollary. Original actions use `L=id`; eccentricities and distances
usually require a separate nonlinear interval bound. To claim a user-specified original
box `Q`, prove `Q ⊆ Ψ({|J_j|≤a_j})` using the inverse chart. Defining an image region
alone does not prove that it contains the requested physical initial data.

**Source and proof.** The action derivative and escape-time argument are GLS17
§4.3, (56)–(58); B1-T retains the entire remainder, unlike the first-term approximation
used for the numerical estimate in (58). The anisotropic closed-initial-box version,
explicit endpoint existence, uniqueness and coordinate-transfer formula are our elementary
deductions. Prove stopped drift, contradict a first exit using the strict margin, then
apply periodic continuation. Lifted angles are unbounded, so do not claim their cylinder
is compact. [GLS17, pp. 24–25](https://arxiv.org/pdf/1702.04894v1).

### 2.3 B1-E: Cartesian oscillator confinement, including zero actions

Reuse the existing frozen
[`oscillatorAction`](../../KAM/Frozen/Planetary/Defs/OscillatorAction.lean):

\[
 I_j(q,p)=(q_j^2+p_j^2)/2,\qquad
 E_b=\{(q,p):\forall j,\ I_j(q,p)<b_j\}.
\]

For every `n ≥ 1`, `a,b,η : Vec n`, `ε>0`, `T≥0`, assume
`0≤a_j<b_j`, `η_j≥0`, `a_j+Tη_j<b_j`. Let `H` be `C²` on an open physical
domain `V`; let `Ψ` be a `C²` symplectic diffeomorphism from `E_(b+ε)` onto an open
subset of `V`, with `C²` inverse. Let `N` be `C²` on an open neighborhood of
`∏j[0,b_j+ε]`, and `R` be `C²` on `E_(b+ε)`, satisfying

\[
 H\circ\Psi=N\circ I+R,\qquad
 |\{I_j,R\}(w)|\le\eta_j\quad(w\in\overline E_b).
\]

Then for every `w₀` with `I_j(w₀)≤a_j`, the unique physical solution from `Ψ(w₀)`
exists past `[-T,T]`, its inverse chart stays in `E_b`, and

\[
 |I_j(w(t))-I_j(w_0)|\le\eta_j|t|,\qquad
 0\le I_j(w(t))\le a_j+\eta_jT<b_j.
 \tag{B1-E}
\]

There is no exit through `I_j=0`; it is an interior Cartesian point. The compact set
`overline E_b` provides continuation, and `{I_j,N∘I}=0` is an algebraic lemma to prove.
No positive definiteness of `H₂` is required. Elliptic equilibria with mixed energy signs
are included once a finite normal form is certified. No polar coordinates are introduced
at the equilibrium.

The same observable transfer formula holds with `L I` instead of `LJ`.
The source is CL20 §4.1, (32)–(37), especially the action-bracket estimate and squared
radii. Here `b_j=ρ_j²`: **an action margin is `ρ_j²-ρ_{0j}²`, not `ρ_j-ρ_{0j}`**.
Continuation, arbitrary symplectic charts and anisotropic margins are explicit additions
to the source estimate. [CL20, pp. 15–16](https://arxiv.org/pdf/2102.05959v1).

### 2.4 What to freeze, and what remains ordinary implementation

Proposed first approval surface: **B1-T and B1-E only**, together with any new
meaning-carrying domain/chart definitions actually used in their final statements.
Reuse frozen Hamiltonian fields, symplectic form and oscillator actions. Prefer an
explicit list of chart clauses over a new bundle that hides proof obligations. The
observable estimate, Taylor bounds, flow composition, expression evaluator and checker
soundness are ordinary proved lemmas with separate names and independent review.
Following the SO precedent D40, do not freeze an evolving certificate serialization.
Freeze one literal application theorem after its data pass, with the actual H, region,
time and bounds in its type.

The formulas above are not frozen Lean. Package B0 must produce the actual complete
Lean command text, check the exact types and definition bodies, obtain independent
source/binder review and owner approval, and only then ask the orchestrator to add
one-declaration anchors and manifest entries. This task edits neither. A theorem whose
premise is `HasConfinement`, `NormalFormExists` or the conclusion packaged as a structure
is not an acceptable replacement. The source-facing sufficient-condition theorems above
are legitimate; an application must discharge their conditions.

### 2.5 B2: optional general theorems, with different quantifiers

Use an analytic, period-one Hamiltonian on
`D(σ,r₀)={ (θ,I)∈CVec n×CVec n : max_j |Im θ_j|<σ, |I|₂<r₀ }`, real on real points,
with `n≥2`, `σ,r₀>0`, bounded holomorphic extension, and

\[
 H(\theta,0)=0,\quad \partial_IH(\theta,0)=\omega,\quad
 |k\cdot\omega|\ge\gamma|k|_1^{-\tau}\quad(0\ne k\in\mathbb Z^n),
 \quad\gamma>0,\quad\tau\ge n-1.
\]

Fix these data, and `H`, **before** choosing the constants and radii. One may normalize
`|ω|₂=1` by a proved time/Hamiltonian scaling; otherwise retain that scale in every time
constant. The plain function `|·|₂` avoids changing carriers. This is a fixed-H analytic
scope; it does not assert a computable uniform threshold for all Hamiltonians.

* **B2-exp.** There exist `c,C,r*>0`, with `2r*<r₀` and `Cr*≤1`, such that for
  every `0<r<r*` and `|I₀|₂≤r`, every initial angle has a unique solution with
  `|I(t)-I₀|₂≤Cr²` (thus `|I(t)|₂≤2r`) for
  `|t|≤exp(c r^(-1/(τ+1)))`. This is the stability projection of BF21 (1.3),
  obtained from its Theorem 1, (3.1)–(3.2), with an intermediate-radius buffer for
  closed initial balls. No twist is assumed.
* **B2-steep.** Put `m₀=⌊n²/2+2⌋`. Require the nonlinear Birkhoff polynomial
  `P=BNF_(m₀)(H)-ω·I` to be quantitatively stably steep. Namely, give `κ,Cs,δ>0`
  such that for every polynomial `P'` of degree at most `m₀` without constant or
  linear terms, `‖P'-P‖coeff<κ`, every real linear subspace `Λ` of dimension
  `1≤ℓ≤n-1`, and every `0<ξ≤δ`,
  \[
   \max_{0\le u\le\xi}\ \min_{x\in\Lambda,\ |x|_2=u}
       |\nabla_\Lambda(P'|_\Lambda)(x)|_2>Cs\,\xi^{m_0-1}.
  \]
  A finite coefficient maximum norm is fixed in the definition; convert it to the
  source polynomial norm. Then there exist `c,r*>0` such that all data `|I₀|₂≤r`
  remain in `|I(t)|₂≤2r` through `exp(exp(c r^(-1/(τ+1))))`, for every `0<r<r*`.
  This is BFN16 Theorem A specialized to analytic H, plus explicit continuation.
  The condition quantifies over **all** these subspaces and a neighborhood of P;
  nonsingular twist, finitely sampled Hessians or one steep polynomial are insufficient.
* **B2-most.** Without a twist or steepness condition, there exist `c,C,r*>0` such
  that for every `0<r<r*` there is an open periodic set
  `G_r ⊆ ℝ^n×{ |I|₂<r }`. For the fundamental cell
  `F_r=[0,1)^n×{ |I|₂<r }`,
  \[
   \operatorname{vol}(F_r\setminus G_r)
       <e^{-c r^{-1/(\tau+1)}}\operatorname{vol}(F_r).
  \]
  Every initial point of `G_r` has action drift `≤Cr²` for
  `|t|≤exp(exp(c r^(-1/(τ+1))))`, with existence and uniqueness. This is the action
  and measure projection of BF21 Theorem A, (2.1)–(2.2). Its phase estimate can be
  added later, using torus distance rather than an unbounded lift difference.

Sources: [BF21, pp. 2, 4–8](https://arxiv.org/pdf/2105.01297v1),
[BFN16, Definition 2 and Theorem A, p. 4](https://arxiv.org/pdf/1601.01783v1).
These are explicitly analytic, fixed-H stability specializations, not a claim to have
formalized the papers' entire statements. A uniform bounded-family version needs its
own binder audit. Euclidean/max-norm conversions change radii and constants: for
example, an input max-norm ball of radius `r/√n` fits a Euclidean ball of radius r.
Do not retain the same literal `2r` after silently changing both balls.

For B2-most, the relevant finite Birkhoff jet is `N_(m*)`, where
`V_m=span{∂^α ∇N_m(0)}` and `m*` is the eventual stabilization index of `V_m`.
The index depends on H. Equality `V_m=V_(m+1)` at one finite step does **not** prove
stabilization for all subsequent orders. BF21 is therefore not a ready-made uniform
finite certificate for arbitrary H. Its elliptic-equilibrium extension is discussed as
an expected extension on pp. 6–7, not proved as Theorem A; exclude that extension from
the first B2 scope.

All three B2 results are formalizations/deductions of known mathematics. Their numerical
application requires a usable r*, not just the expression “double exponential.” Stable
steepness certification, an effective bound on m*, or an inner-system transport theorem
with useful constants would be additional mathematical work. They are not hidden B1
dependencies.

## 3. The finite certificate: data, soundness and internal lemmas

### 3.1 A checker whose conclusion includes the dynamics

Start with exact polynomial Hamiltonians in Cartesian variables and supported algebraic
constants; extend to finite Fourier–Taylor expressions and then supported analytic
expressions. For parameters enclosed in a rational box, quantification is over **every**
parameter in that box. The model expression is interpreted exactly. A polynomial that
approximates a different H is a different model unless the difference and its derivatives
are bounded in the final remainder.

The proposed certificate contains:

| Finite input | Required checked meaning |
|---|---|
| Exact H expression, parameter box, coordinate and time conventions | A single specified real Hamiltonian, regular on the advertised domain |
| Nested complex domains, radii and rational strict margins | Every flow for `-1≤s≤1`, its inverse, and each composition remain in a domain of analyticity |
| Finite generating polynomials/functions `χ₁,…,χ_m` | Actual time-one Hamiltonian flows; an arbitrary finite generator is allowed |
| Normal-form polynomial N and retained residual polynomial P | Checked identities for the finite Lie/Taylor coefficients, including constant and linear residuals |
| Bounds on all discarded terms, expression approximation and rounding | An analytic residual tail E on an **outer** domain, with a documented derivative-loss margin |
| Divisor witnesses when a homological solve is used | Lower bounds for every denominator actually inverted; zero/small divisors are retained or cause rejection |
| Forward and inverse displacement bounds, initial-set inclusions | A meaningful region in original coordinates, not just an unspecified image |
| Drift bounds `η_j`, observable bounds `d_i`, requested rational time T | Static inequalities, particularly `a_j+Tη_j<b_j`, and the requested physical output |

The soundness statement has the shape

```text
for every supported expression Hexpr and finite certificate c,
  checkNormalForm Hexpr c = true ->
  for every parameter in c.parameterBox and every z0 in c.initialRegion,
    there is a unique Hexpr trajectory through [-c.T,c.T],
    with the stated original-coordinate observable and domain bounds.
```

This is a proposed interface, not compilable Lean syntax. The theorem must prove the
chart, residual and continuation facts from the accepted finite data. There is no extra
unexplained premise saying that the data certify them. Soundness need not prove the
generator's optimization algorithm correct: a bad generator simply fails the inequality.
Producer arithmetic is untrusted; every accepted identity and bound is replayed through
ordinary kernel-checked arithmetic and proved analytic lemmas.

### 3.2 Exact transformations and tails

For `Φ_χ^s`, the actual flow of `X_χ`, prove on the stated domain

\[
 H\circ\Phi_\chi^1
 =\sum_{k=0}^{m}\frac{\operatorname{ad}_\chi^kH}{k!}
  +\int_0^1\frac{(1-s)^m}{m!}
       (\operatorname{ad}_\chi^{m+1}H)\circ\Phi_\chi^s\,ds.
 \tag{Lie}
\]

If the last bracket is bounded by B along that flow on an outer complex domain,
the integral has bound `B/(m+1)!`. The existing `taylor_lie` is the starting point.
Composition of exact flows remains canonical; the discarded polynomial terms remain
in R. A truncated coordinate substitution is not the map being certified.

For a Fourier–Taylor polynomial
`P=Σ_(k,α)c_(k,α) exp(2πi k·φ) J^α`, use

\[
 \|P\|_{\sigma,b}=\sum_{k,\alpha}|c_{k,\alpha}|
       e^{2\pi\sigma|k|_1}\prod_i b_i^{\alpha_i},\quad
 \eta_j^{\rm poly}=2\pi\sum_{k,\alpha}|k_j|\,|c_{k,\alpha}|
       \prod_i b_i^{\alpha_i}.
\]

An analytic tail bounded by E on a strip containing closed angle discs of radius
`δθ>0` about the real domain contributes at most `E/δθ` to each `η_j`.
Here σ is a **geometric period-one strip width**. The repository's coefficient radius
is `2πσ`; do not mix its derivative-loss constant with the geometric Cauchy constant.

For oscillators, an efficient representation uses independent complex variables
`z_j=(q_j+i p_j)/√2`, `ζ_j=(q_j-i p_j)/√2`, imposing `ζ=conj z` only on the real slice.
Then `I_j=z_jζ_j` and `{I_j,z^αζ^β}=i(α_j-β_j)z^αζ^β`. Thus on `I_j≤ρ_j²`,

\[
 \eta_j^{\rm poly}=\sum_{\alpha,\beta}|\alpha_j-\beta_j|
       |c_{\alpha\beta}|\prod_i\rho_i^{\alpha_i+\beta_i}.
\]

This preserves resonant cancellations. Alternatively, a tail bounded by E on Cartesian
complex discs with margins `δq_j,δp_j>0` contributes
`w_j E(1/δq_j+1/δp_j)`, where the checker proves `w_j²≥2b_j`, `w_j≥0`.
Every radius and square-root factor must be fixed before the arithmetic run.

For the CL-style coefficient majorant `‖f_s‖≤A B^(s+2)`, the infinite derivative tail
can be checked with a rational geometric-series formula. If `x=Bρ<1` and the omitted
degrees start at d, then

\[
 \sum_{k=d}^{\infty}k x^k
   =\frac{x^d(d-(d-1)x)}{(1-x)^2}.
 \tag{Tail}
\]

Prove this identity and its domain guards once. Keeping a first omitted term without a
ratio bound is not a valid tail certificate. Store all contributions separately:
`η = η_finite + η_Lie + η_Fourier + η_model + η_rounding`. Propagate each through
later charts before adding it; a bound before composition is not automatically a bound
after composition. Likewise, compose displacement bounds with the needed derivative
factors, rather than summing them across unrelated coordinate systems.

These implementation choices follow the finite-degree and majorant strategy of
[CL20, Lemma 2.1, §2.2, Proposition 3.3 and (33)–(34)](https://arxiv.org/pdf/2102.05959v1).
The checker design, sharding and soundness theorem are new formal infrastructure.

### 3.3 Divisors, resonances and coordinate units

Finite oscillator normalization needs only the used divisors
`|ω·(α-β)|≥λ_(αβ)>0` up to the requested polynomial degree. The torus version needs
`|2π k·ω|≥λ_k>0` for the Fourier modes actually eliminated. Interval frequency boxes
must exclude zero in each such expression. A finite certificate can use rational
frequencies; they need not satisfy an infinite Diophantine statement. If a denominator
is too small, retain its monomial in R and pay its drift, or use C's resonant integrals.
Do not call a resonant normal form `N(J)` if it still depends on angles.

A published `2π` angle θold becomes `φ=θold/(2π)`. Keeping time and canonical form
requires `J=2π Iold` and `Hnew(φ,J)=Hold(2πφ,J/(2π))`. Thus
`ωnew=ωold/(2π)` and physical actions recover `Iold=J/(2π)`.
If one keeps Iold instead, the form is scaled and the Hamiltonian must also be scaled
to obtain the claimed equations. A time rescaling `tphys=c s` gives
`Hscaled=c Hold` in unchanged canonical coordinates, so a certified s-horizon S is
`cS` physical time. Carry these maps into the theorem, not only into a plot label.

### 3.4 A controlled chart around a certified torus

This is an optional adapter, not a B1 prerequisite. For an exact Lagrangian torus
`K(φ)=(x(φ),v(φ))`, `x(φ)=φ+u(φ)`, prove a projection bound
`sup ‖Du‖op≤κ<1`. Then x is a global diffeomorphism modulo the lattice, and the
explicit map

\[
 \Psi_K(\varphi,J)
  =\bigl(x(\varphi),\ v(\varphi)+Dx(\varphi)^{-T}J\bigr)
 \tag{Chart}
\]

is symplectic: it is a cotangent lift followed by the closed one-form determined by K.
The Lagrangian property is essential. This map need not be exact symplectic if the
Liouville class of K is nonzero; B1 only requires symplecticity. Subtracting the constant
action class gives the usual exact version where needed.

An invariant exact torus gives
`H∘Ψ_K=E+ω·J+O(J²)`. Derive this from `DK·ω=X_H∘K`, rather than add it as a
hypothesis to the certificate application. Cauchy bounds on a smaller strip, inverse
matrix witnesses and an explicit action radius prove that the chart remains in the
Hamiltonian domain. The v2 closeness bound must imply the projection bound; primary
winding alone does not imply it. Tori whose angle projection folds need another chart
construction and are outside this first adapter.

For an isoenergetic output with frequency `s∞ω*`, propagate its proved interval for
s∞ to all finite divisors and use the Diophantine scaling lemma for B2. Never replace
an ordinary torsion inverse by the bordered inverse. For a merely approximate torus,
the formula (Chart) is not automatically canonical: use certified generating flows or
an independently verified closed graph, and retain the invariance defect in R.

## 4. Applications ranked by scientific payoff

The rank is payoff, not execution order. All cost ranges below are **planning
allocations**, with at least factor-two uncertainty in proof size and potentially 20×
uncertainty in arithmetic extrapolation. No future Lean RSS or runtime was measured in
this task. CPU budgets refer to certificate replay after the generic proofs are built.

| Rank | Exact claim to aim for and audience | Prior rigorous/numerical evidence | Feasibility and first quantitative gate |
|---|---|---|---|
| 1 | **5 Gyr for a positive-volume region of a pinned secular SJSU Hamiltonian**, with explicit eccentricity bounds and reconstruction for every fast phase. Celestial mechanics and formal numerics. | GLS17 supplies a numerical normal-form calculation, not a rigorous certificate; its estimate reaches about `10^10 yr` near radius `<10^-7`, versus an approximate uncertainty radius `7·10^-7`. | Plausible research application of B+D, not a promised result. Start at source-normalized action radius `10^-7`; require complete model/chart data and `ηT<margin` before a 100–1,000 CPU-h pilot allocation. Full data cost is unknown. |
| 2 | **5 Gyr of local Trojan confinement in the exact planar circular restricted Sun–Jupiter problem**, massless third body, literal mass ratio `μ=477/500000`, in a specified neighborhood of L4. Asteroid dynamics. | CL20 gives rigorous computer-assisted nonresonant and resonant calculations. Its Table 2 has action bounds around `2.49·10^-4` and reported T `6.36·10^8` in its time convention. | More credible than full SJS; rough 100–1,000 CPU-h eventual replay allocation, 3–7k model/coordinate Lean lines beyond B. First replay a low-order tail and reconstruct the time scale; do not infer years from the table alone. A useful smaller region is likely; reproducing the full row is a separate gate. |
| 3 | **A full planar moving-Sun SJS finite-region lifetime at the cited masses**, around a selected reduced 3-torus, for all angles and transverse data in a literal box. Planetary dynamics. | FH25 computes a realistic approximate torus and numerical KAM checks; it does not establish a rigorous neighborhood lifetime. | Long-term target. Old scout: 3.6–4.7 million retained coefficients and roughly 10,000–33,000 kernel CPU-h for one earlier torus route, before B. Neither its large-memory products nor its cheap hypothetical hybrid extrapolation fits the present policy. |
| 4 | **A certified nontrivial normal-form lifetime for an explicit three-degree-of-freedom oscillator**, then a time–radius curve. Hamiltonian numerics, accelerator/energy-transfer studies. | CL20 supplies the method in two degrees; GCP26 supplies a rigorous three-mode FPU comparison. | 10–100 CPU-h for a modest sparse instance, conditional on ≤`10^4` active coefficients per stage and measured shards. A FPU confinement claim alone is weak when coercive energy already proves it; require individual modal-action drift substantially better than the energy bound. |
| 5 | **A finite-region theorem near an LG00 torus**, with original secular action drift and explicit chart inclusion. A compact planetary regression example. | LG00 already rigorously confines its truncated model with two tori; this checkout already proves all-time safety for a different exact secular SJS box. | Good engineering pilot, weak new-physics headline. Existing scout: 69 rational monomials; A-route support about 545–680, projected 3–75 CPU-h per torus. Add a measured finite-normalization workload; do not call the old float projection a certificate. |

Primary sources for the first three rows:
[GLS17, §2 and §4.3, Figure 2, (61)](https://arxiv.org/pdf/1702.04894v1),
[CL20, §5.2 and Table 2](https://arxiv.org/pdf/2102.05959v1),
[FH25's pinned v1 abstract and model](https://arxiv.org/abs/2403.10152v1).
The full-SJS resource figures are the qualified projections in
[sjs-feasibility §§5–6](sjs-feasibility.md), not measurements of a completed B computation.
GCP26 is an optional later improvement to inverse-remainder times:
[Theorems 2.1–2.3, §4](https://arxiv.org/pdf/2601.18268v1). Its stated resonant extension
is open; do not transfer its sharpening to C without a proof.

The application claims need a more precise contract than “stable.” For each planetary
instance, D must supply one exact Hamiltonian M, a canonical chart Ψ, its time conversion,
an explicitly represented original initial set Q of positive volume, and functions
reconstructing eccentricities and positions. Once these data are fixed, the proposed
claim quantifies over **every** `z₀∈Q` and **every** `|t|≤5·10^9 yr`, with the
existence/uniqueness convention of §2.1. Use these concrete acceptance targets:

| Instance | Region and quantitative conclusion to attempt | Missing inputs before an application type can be frozen |
|---|---|---|
| Secular SJSU | Q is the image of the normalized action box `abs(J_j)≤10^-7` about the selected torus, with every angle included; its inverse-chart actions remain in absolute value `<2·10^-7`. Each reconstructed eccentricity stays `<0.15`, with pairwise planetary separation `>1 AU` for every reconstructed fast phase. | Pin the degree-18 secular polynomial from GLS17 §2.2, (12), including the mass/order-two construction and Table-1 literals; obtain its complete coefficients, chart and physical-unit map. No full Newtonian shadowing is implied. |
| Restricted Trojan | In the fixed linear canonical oscillator coordinates centered at L4, `I_j(z₀)≤10^-4`; along the original restricted trajectory, these same linear-coordinate actions stay `<2·10^-4`. | Pin the linear map used to obtain CL20 (46) and its exact analytic remainder. Declare Jupiter's period, e.g. the literal `593/50 yr`; for a unit-angular-rate rotating Hamiltonian this requires `H_year=(2π/(593/50)) H_rot`. These are proposed goal literals, not consequences already extracted from Table 2. |
| Full planar SJS | Q is the image of the selected torus chart's box `abs(J_j)≤10^-7`, with every angle included; inverse-chart actions stay in absolute value `<2·10^-7`, both eccentricities `<0.15`, and Jupiter–Saturn distance `>1 AU`. | FH25's full moving-Sun Hamiltonian and its reduction, exact model parameters, the controlled chart and initial inclusion; all gaps identified by the existing large-data scout remain. |
| LG00 regression | The same `10^-7` to `2·10^-7` chart-action containment for its exact 69-monomial polynomial, plus explicit bounds for its original secular actions from (B1-transfer). | Choose and certify one torus/chart, state its exact units and compute the original-action constants. The already known two-torus all-time result remains the stronger qualitative confinement precedent. |

The numerical literals above are **candidate acceptance targets**, not measurements or
owner-approved statements. For either image-defined Q, claiming containment of a specified
physical box or observational uncertainty set requires a separate inverse-chart inclusion.
A failed margin returns a documented alternative, rather than
a silently altered theorem. Their missing model/chart data are why HH below is ready
for the first concrete experiment and the planetary theorem types are not yet ready.

For the three-mode oscillator, an exact optional instance is GCP26 (79) with
`x₀=x₄=y₀=y₄=0` and `α̃=1/4`:

\[
 H_{\mathrm{FPU}}(x,y)=\frac12\sum_{j=0}^{3}
       \bigl(y_j^2+(x_{j+1}-x_j)^2\bigr)
       +\frac1{12}\sum_{j=0}^{3}(x_{j+1}-x_j)^3.
\]

Use the literal linear canonical modal transformation in (80), with
`Ω_j=2 sin(jπ/8)`, `j=1,2,3`. A proposed first three-degree target is: for every
original modal-action box `I_j(z₀)≤10^-8`, each modal-action drift is `≤10^-9` through
`|t|≤10^10` model units, with existence and uniqueness. This strengthens local
energy confinement by restricting exchange between modes. E1–E3 must be rerun for
this model; neither the HH scout nor GCP26's higher-order table certifies these literals.

For SJSU, explicitly verify the common-perihelion rotation symmetry of the selected
polynomial. A planar three-planet secular model has three degrees of freedom before
fixing AMD and reducing that symmetry, and two afterwards. Thus it does not by itself
demonstrate confinement beyond the two-degree barrier setting. A planar four-giant secular
model including Neptune has three degrees after that reduction; full planar SJS has
three after angular-momentum reduction. Both are stronger possible flagships and need
new feasibility evidence. See the exact reduction in
[Migaszewski–Goździewski, §3, (43)](https://arxiv.org/pdf/0803.3246v1).

### A first instance with literal acceptance criteria

Use the Appendix-B version of CL20, **not** its different-frequency Table-1 model:

\[
 H(q,p)=I_1-\frac{\sqrt2}{2}I_2+q_1^2q_2-\frac13q_2^3,
 \qquad I_j=(q_j^2+p_j^2)/2.
 \tag{HH}
\]

The proposed first application theorem is: for every original point with
`I_j(z₀)≤(1/12500)²`, `j=1,2`, there is a unique solution through
`|t|≤10^10` in **HH model time units**, with
`I_j(z(t))<101/10^10` and `|I_j(z(t))-I_j(z₀)|≤12/10^10`.
This is a proposed acceptance target, not a theorem proved here.

A sufficient finite certificate would establish, in the normalized chart,

\[
 a_j=(81/10^6)^2,\quad b_j=10^{-8},\quad
 \eta_j\le10^{-19},\quad T=10^{10},\quad
 d_j\le10^{-10}
\]

for forward and inverse oscillator-action displacement on their required domains.
The inequalities are transparent:
`(1/12500)²+10^-10 = 6.5·10^-9 < a_j = 6.561·10^-9`,
`a_j+η_j T ≤ 7.561·10^-9 < b_j`, and
`2d_j+η_j T ≤ 1.2·10^-9`. The physical outer action bound is `b_j+d_j≤1.01·10^-8`.
There is positive four-dimensional volume, including the equilibrium, and the quadratic
energy is indefinite; energy coercivity is not being mistaken for the result.

The source's short computation uses explicit degree four (`R_I=2`), scalar majorants
through degree seven (`R_II=5`), and stops at normalization step three. It reports
`log T=24.92920` at `ρ=10^-4`, `ρ₀=0.00008165`, about `6.7083·10^10` model units.
Its reported values motivate the looser target above. They do not certify our chart
displacement or imply that a coarse reimplementation will close.
[CL20, Appendix B, pp. 33–37](https://arxiv.org/pdf/2102.05959v1).

**New measured scout.** An independent scratch calculation over `ℚ(√2)` solved the
cubic and quartic homological equations and checked their polynomial identities. It gives

\[
 N_4=\frac{13\sqrt2}{28}I_1^2
       -\left(\sqrt2+\frac47\right)I_1I_2
       +\frac{5\sqrt2}{12}I_2^2.
\]

Its coefficients agree with the Appendix-B quartic after converting the source's
`(-iz,z̄)` monomials. H₃, χ₃, the first quartic and χ₄ have respectively 2, 5, 8 and 8
nonzero real-coordinate monomials. Successive brackets of H₃ with χ₃ through degree
seven have 8, 14, 24 and 30 terms. Runtime: **1.586 CPU seconds**, peak RSS
**681,496 KiB** (about 0.65 GiB), with a 3,500-MiB address-space cap and 180-second
CPU cap. This is exact symbolic scouting, not Lean verification, an analytic-tail check
or a lifetime proof. Reproduce with `python3 -B /tmp/prog-b-astra/pilot.py`;
the complete output is `/tmp/prog-b-astra/pilot.json`.

## 5. Solar System assessment

### What is plausible with B's existing mathematics

* **Restricted Sun–Jupiter Trojan model:** planar, circular primaries, a massless third
  body, small neighborhoods of an elliptic L4/L5 equilibrium. A 5-Gyr model lifetime
  is a credible target because rigorous finite-normal-form precedent exists. This
  neither includes Saturn's perturbations nor identifies an observed asteroid's full
  uncertainty set. Spatial Trojans add a mode and further resonances; they need a new
  source, normal form and scout, rather than the same numerical estimate.
* **Explicit planar secular outer-planet models:** local neighborhoods of selected
  tori, with 5 Gyr as an attempted target. GLS17 provides the most specific calibration.
  Its source-scale radius `10^-7` is a normalization-dependent action width, not an
  astronomical distance or an established ephemeris error. Pin the canonical inverse
  and report the physical eccentricity/radial envelope before judging its usefulness.
* **Full planar SJS:** finite neighborhoods at literal parameters are compatible with
  B's theorem. The current obstruction is large quantitative/model work and resources,
  with no established useful lifetime. Classify it as mathematically plausible and
  computationally unvalidated, not as a near-term deliverable.

For the full planar model, “actual masses” must mean declared model literals or specified
mass intervals. The existing cited example uses Jupiter/Sun `0.0009546`, Saturn/Sun
`0.0002856`; the direct use of global small-μ theory at these values is not justified.
Proper degeneracy is structural: the Kepler Hamiltonian is independent of the secular
actions. Local secular normalization can supply frequencies and torsion, but they are
small and their actual divisors must be checked. B has no mass-threshold theorem that
automatically turns an asymptotic planetary result into a certificate at these ratios.

### What requires additional mathematics or a substantially new calculation

For Mercury, Venus, Earth and Mars, a specified forced **spatial secular model** including
eccentricity and inclination variables is a reasonable later target jointly with C.
Outer-planet quasiperiodic forcing makes it a skew-product system. It is not the full
autonomous eight-planet dynamics. Treat the forcing angles as a compact torus and
differentiate observables along the full skew field. Appending dummy actions does not
prove conservation of the inner subsystem's energy or AMD.

The numerical motivation is strong: a Lyapunov time around 5 Myr, order-one-percent
large Mercury eccentricity excursions over 5 Gyr in the LG09 ensemble, and the
destabilizing `g₁-g₅` secular resonance. The ensemble fraction is neither a theorem about
Lebesgue measure in a box nor exactly a collision probability. Relativistic precession
materially changes the resonance. These facts are checked against
[ML21, §§6–7 and Appendix C](https://arxiv.org/pdf/2105.14976v1).

Eliminating that resonance by division is precisely where a nonresonant B certificate
may become useless. Keeping its dynamics and certifying transverse approximate integrals
is C's extension. A useful ≥99% good-set statement would require a finite measure cover,
specified initial distribution, every escape boundary and a treatment of the unresolved
cells. B2-most does not identify an observed chaotic orbit as a member of its good set.
The suggested quasi-integrals are numerical structural evidence:
[Mogavero–Hoang–Laskar 2023](https://arxiv.org/abs/2305.01683v1).

Model fidelity cannot be reduced just to make the bound pass. In the tested forced
models, degree-four truncation nearly suppresses 5-Gyr instability, while degree-six
terms restore much of it. A certificate of the fourth-degree polynomial would therefore
answer a different transport question. See
[HML22, §§3–4](https://arxiv.org/pdf/2205.04170v1).
To claim the full Newtonian/relativistic inner system requires validated averaging and
model-error bounds over the entire requested time, as well as initial-coordinate
uncertainty. A local `O(μ²)` averaging error or numerical orbit agreement for a few
Myr does not provide that transfer.

**Best honest inner-system case:** certify a useful finite horizon for small, explicitly
selected cells of a pinned forced secular Hamiltonian, retaining Mercury-related
resonances; publish the T-versus-cell-size curve and covered fraction. Reaching 5 Gyr
for a scientifically meaningful fraction is an open quantitative research goal. It may
need sharper estimates, new approximate integrals and a new rigorous secular/model
transfer, not merely formalization of BFN16.

### What is not plausible as this program's deliverable

A blanket claim that every physically admissible current inner-planet initial condition
is safe for 5 Gyr is not a credible B target in light of the numerical excursions.
This is a feasibility judgment, not a rigorous refutation for every possible uncertainty
set. An all-time open-neighborhood claim in a general system with at least three
effective degrees of freedom is also outside B: invariant tori do not generally separate
the energy surface, and Arnold diffusion can occur. Exponentially or doubly exponentially
long stability is consistent with later diffusion; it never implies all-time stability.
Neither B nor KAM proves that the actual planets are chaotic, and a confinement theorem
does not by itself prove a positive Lyapunov exponent.

The Solar System's approximately 4.6-Gyr age is a useful scale; the plan's requested
5-Gyr horizon is a future lifetime in a declared fixed model. It does not include stellar
evolution, passing stars, tides or unmodeled forces unless those are explicitly added.

## 6. Resource design and early experiments

### 6.1 Stay below the actual limits

For this research task: Python below about 4 GB, no Lean builds; no Lean probe was used.
For a later authorized implementation campaign: one targeted build at a time, default
heartbeats and **<8 GB RSS per Lean process**, with a target of ≤6 GB for arithmetic
shards. The machine kills a Lean process above 10 GB and caps the user at 32 GB shared
with other campaigns. Other agents are not extra memory allowance. Do not rerun the
19.2-GB refined core or lunar-scale opt-in tests during a scouting package.

Use outward dyadic balls, balanced finite traversals and small checked algebra blocks.
Begin with 128–512 terms or output slots per block, 128–256-bit mantissas, then measure;
these are starting sizes, not guarantees. Bound each identity's intermediate products,
including packing and loading dependencies. A big arithmetic reduction does not become
small merely because its source is split into several files. Conversely, a proof of a
geometric tail is preferable to generating every coefficient in that tail.

The combination theorem must verify the partition and coverage of all coefficient or
convolution blocks. Checksums provide provenance, not mathematical equality. Changing
from sparse to packed representation must preserve exact coefficients and remainder
semantics. Do not use native evaluation or an external program's Boolean as proof.

The scratch counting experiment gives the dense worst-case number
`binomial(2n+d,d)` of Cartesian monomials through degree d:

| Oscillator degrees of freedom n | Degree d | Monomials through d |
|---:|---:|---:|
| 2 | 12 | 1,820 |
| 3 | 12 | 18,564 |
| 4 | 12 | 125,970 |
| 3 | 20 | 230,230 |
| 4 | 20 | 3,108,105 |
| 8 | 12 | 30,421,755 |

These are combinatorial counts, not actual supports or measured runtimes. Torus normal
forms multiply Taylor counts by Fourier support. GLS17's intermediate expansion has
94,109,751 monomials: even a hypothetical 32-byte packed record costs 3.01 GB decimal
for one array, before interval endpoints, products or indexes; 200 bytes per Python
entry would cost 18.82 GB. The original full expansion must not be recreated here in a
Python dictionary. Stream blocks and use analytic majorants, or defer generation to
separately authorized hardware. [GLS17, §2.1, p. 10](https://arxiv.org/pdf/1702.04894v1).

FH25's reported torus-generation setup used about 194 GB; a comparable run would need
a separately permitted ≥256-GB host, plus a data-storage and runtime plan. The old SJS
packed-product estimates themselves need 28–56 GB per product and an unimplemented
arithmetic design. They cannot be advertised as present-machine costs. Kernel checking
on the current host still requires genuine ≤8-GB blocks even if generation moves away.

### 6.2 Experiments that can terminate early, each under one CPU-hour

All proposed experiments have an individual 45-minute CPU cutoff and 3.5-GB Python
limit unless a smaller limit is listed. Wall time waiting for a compile gate is distinct.
Only E0 was executed in this task. Numerical success is not a theorem; numerical
failure should identify the failing bound before more proof code is assigned.

| Experiment | Input and computation | Output and decision |
|---|---|---|
| **E0: exact low jet — done** | HH; solve degree-three and degree-four homological equations over `ℚ(√2)`, check polynomial residuals, count four successive brackets | Exact N₄ above, 1.586 CPU s, 0.65 GiB. Confirms that the first algebra workload is small; no tail/lifetime conclusion. |
| **E1: full short majorant** | HH Appendix B; use exact low jet, outward rational bounds for steps 1–5 and the infinite geometric tail. Test `ρ=10^-4` and adjacent radii | Report every contribution to η and forward/inverse d. Go if `η≤10^-19`, `d≤10^-10` and domain margins pass; otherwise report which loss prevents the literal first instance. Do not silently shrink its initial box. |
| **E2: one kernel shard — future implementation only** | A representative accepted polynomial identity and a tail inequality, 128/256/512-term versions, no full application | `/usr/bin/time -v`, kernel reduction time, total RSS, file/proof size. Stop above 6 GB, a default-heartbeat failure or 45 CPU min. Extrapolate only a repeated operation of the same representation. This task's no-build instruction forbids executing E2 now. |
| **E3: normal-form advantage** | HH and later LG00; orders 0–6/8 at 8–12 radii, including all residual and chart costs | Compare **the same original initial set and observables**. Require at least 10× the direct derivative lifetime at one radius; stop if normalization only moves the loss into the chart. Direct HH variation is cubic in amplitude, whereas the normalized residual starts at a higher order. |
| **E4: SJSU source extraction gate** | D supplies a pinned expression/coefficient table and normalization. Inventory only; at most `10^5` terms processed at once and low-order divisors sampled for scouting | Exact model hash, symmetry identity task, term counts, unit conversion, first remainder/derivative budget. If coefficients are unavailable, report that dependency rather than invent them. No 94-million-term expansion. |
| **E5: lifetime sensitivity** | A fixed complete remainder model from E1/E4; 12 radii and 8 candidate orders, requested times `10^6,10^8,5·10^9 yr` where units are known | T(r), active term and displacement/initial-inclusion margin. For a torus action margin `10^-7` at 5 Gyr, half-margin reservation requires `η≤10^-17 yr^-1` in those coordinates. If a model-error term alone exceeds that, stop the claimed transfer. |
| **E6: torus chart viability** | Existing LG00 finite embedding, certified v2 error bounds when available; estimate projection inverse, Cauchy losses and transverse radius | Require a rigorous route to `‖Du‖op<1` and a nonzero useful chart radius. A sampled determinant or merely primary embedding is not success. May run before exact certification as a clearly labeled rejection scout. |

For E2, start with an already allowed tiny target; no large opt-in test is implied by
this plan. A 100–1,000 CPU-hour application allocation is considered only after these
small measurements and the mathematical budget succeed. The checker's exact operation
count times measured per-block costs, dependency-loading overhead and proof-data size
must accompany the allocation; a generic “hours per monomial” guess is insufficient.

## 7. Ordered work packages and timeline

Estimates are incremental handwritten Lean/Python lines, exclude generated certificate
data, and assume reuse of the inspected N/P/Canonical/Certificate APIs. Each Lean file
stays below 1,500 lines; target 250–700. Calendar ranges assume one primary implementer
and an independent reviewer with access to the shared compile gate, not unlimited builds.

| Package, order | Inputs → outputs | Estimated size and time | Required check and stop condition |
|---|---|---|---|
| **B0: source and exact surface** | This plan, pinned sources, existing fields/solutions → exact B1-T/E command text, domain definitions, dependency inventory and review packet | 0.3–0.8k Lean type/definition text, ≤0.3k Python; 2–4 working days | Exact binder, carrier, sign and endpoint audit; resolve source transcription findings. Stop before freeze/proof assignment if the proposed type changes the mathematical target. |
| **B1: region dynamics** | Approved B0 surface → stopped drift, first exit, continuation, chart transport and the two providers | 1.5–3k Lean; 4–8 days | Narrow targets and `#print axioms`; tests of zero drift, backward time, `T=0`, zero oscillator actions and strict endpoint margins. Never assume a trajectory already exists through T. |
| **B2: finite polynomial normalization** | Canonical flow/Taylor APIs and certificate arithmetic → polynomial bracket/evaluation, exact flow chain and checked residual/displacement bounds | 6–10k Lean, 0.8–1.5k Python; 2–4 weeks | One complete step with an infinite tail; E2. Reject unsupported denominators and unbounded tails; split before default-heartbeat or RSS failure. |
| **B3: literal HH certificate** | B1/B2, E0/E1 → data and proof of the exact first-instance statement in §4, original-coordinate inclusion and measured T(r) | 2–4k Lean, 0.4–0.8k Python; 1–2 weeks; provisional 5–30 replay CPU-h | Every tail and chart term checked, same original region compared at order zero. Stop at failed acceptance literals; return a reviewable weaker candidate only with the discrepancy documented. |
| **B4: Fourier–Taylor support** | B2 plus existing Fourier/weighted norms → mixed finite arrays, finite divisor checks, analytic Fourier/Taylor tails, B1-T checker route | 4–8k Lean, 0.8–1.5k Python; 2–4 weeks | Single-mode `2π` check, cancellation before absolute values, complete frequency-box coverage. Stop if Fourier support cannot be processed under the cap. |
| **B5: exact-torus adapter** | v2 or hybrid theorem output and (Chart) → controlled tubular coordinates, `E+ω·J+O(J²)` and interval numerical jets | 5–9k Lean, 0.3–0.8k Python; 2–4 weeks | Projection/inverse/complex-domain estimates and all derivative losses; E6. Defer folding projections and general symplectic-neighborhood theorems. |
| **B6: planetary regression and application choice** | LG00 exact polynomial and B4/B5 → finite-region certificate, original action bounds; Trojan or SJSU source/model decision | 1–3k Lean, 0.5–1k Python; 1–2 weeks plus measured replay | Source polynomial identity, model distinction and nonzero region inclusion. Do not repackage existing all-time SJS safety as a new 5-Gyr result. |
| **B7: substantial application with D** | All passing early gates → one literal Trojan or secular SJSU lifetime, physical observables and T(r) curve | Trojan 3–7k extra Lean; SJSU model work 10–25k mainly owned by D; 4–12+ weeks | End-to-end certificate and independent mathematical/model audit. No schedule promise if E4/E5 has no useful margin. |
| **B8-exp, optional** | Finite analytic normal forms → optimal-order near-torus exponential theorem | 12–25k Lean, little Python; 1–3 months | Prove the order choice, uniform analytic losses and exact torus chart; no asymptotic claim based on a finite scan. |
| **B8-steep or B8-most, optional** | B8-exp plus respectively A's steep geometry, or BF21's frequency-rank/measure argument → one B2 successor | 20–45k Lean per route, substantial overlap; 2–5+ months | Freeze the chosen source specialization separately. No automatic stable steepness from twist; no automatic finite bound on m*. |

B0–B4 provide the core at about 14–26k Lean lines, in the same range as ambition's
12–25k estimate. B5 and application adapters are additional, not included twice in D's
budget. The first meaningful end-to-end result is HH, plausibly in 5–9 weeks including
review, depending on reuse and arithmetic performance. A useful torus adapter and
planetary regression suggest roughly 10–16 weeks for the reusable B1 suite. A serious
planetary lifetime is a subsequent 3–6+ month research milestone conditional on its
early bounds. These are work estimates, not forecasts tied to the repository's earlier
multi-agent throughput. Nothing here authorizes concurrent agents or builds.

### Brief 1: B0 — source-controlled statements and dependency inventory

**Objective.** Prepare the exact two finite-region statements B1-T and B1-E for owner
approval, with every source and semantic clause pinned. Do not implement a numerical
checker or freeze anything. This is the first worker assignment when the owner elects
to start B.

**Inputs.** Read AGENTS.md, PLAN, DECISIONS, this plan §§1–3 and the pinned CL20/GLS17
pages listed in §9. Read the existing Hamiltonian field, symplectic form, oscillator
action and solution definitions; inspect `KAM/ODE/Continuation.lean`,
`KAM/Canonical/{Setting,FlowInverse,Symplectic,Lie}.lean`. Use the inspected commit as
a reference, but record the actual assigned base commit.

**Deliverables.** In the assigned scratch directory, prepare (i) exact Lean command text
and any final definition bodies; (ii) a source-to-binder table; (iii) a minimal import
list and module split; (iv) an independent-review packet answering why continuation is
proved, how lattice compactness is used and why the endpoint margin is strict; and
(v) a disposition for each source finding in §9. Suggested future names are
`KAM.EffectiveStability.torus_confinement` and `.oscillator_confinement`; they are not
approved exports. Proposed supporting modules are `Domains`, `StoppedDrift`,
`FirstExit`, `Transfer`, with frozen/provider paths assigned by the orchestrator.

**Checks and bounds.** Check the exact types in untracked scratch using `#check`,
without provisional proof bodies, new axioms, or theorem-shaped assumption bundles.
If the intended public type cannot yet be elaborated, report the missing API and retain
it as planning text. Budget 2–4 working days; no numerical data generation. The normal
implementation build policy applies only after that work is assigned; the current
PROGRAM-B research brief does not permit builds. Independent reviewer checks the
actual commands before owner approval. Do not put unapproved statements into Frozen.

**Stop/handoff.** Stop on a defect in an existing frozen declaration, a source mismatch,
or an unresolved domain convention. Return exact files, checks, output, remaining
uncertainties and source findings. The author approves concrete declaration text;
agreement with this plan alone is not statement approval.

**Hard rules, verbatim:**

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
10. **Never edit `README.md`** (generated) or `KAM.lean` and its parts `KAM/Root/*.lean` (generated by
    `scripts/gen_root_imports.py`; no module imports them).
11. **Errata:** report every suspected defect in a pinned source (location, quoted text, why it is wrong) in your
    handoff; the orchestrator records it in `docs/errata/ledger.json`. Deviations you introduce are reported too.

### Brief 2: B1 — finite-region dynamics, without numerical normal forms

**Objective.** Once B0's exact declarations are approved and frozen, prove precisely
those two theorems. Implement the derivative-to-confinement argument and coordinate
transfer, with no Diophantine or nondegeneracy premise. If the owner has not approved
the commands, inventory the dependencies and wait at that gate; do not substitute a
convenient type. This brief is ready to assign after B0, not permission to freeze today.

**Inputs and scope.** B0's manifest identities, the explicit statements in §2 and the
inspected ODE/canonical modules. Write only assigned ordinary modules under the
prospective `KAM/EffectiveStability/` area and the two registered providers. Leave
Frozen, manifest, generated files and other campaigns to their owner. No checker,
KAM iteration, Birkhoff algorithm or planetary coefficient work belongs in this packet.

**Proof sequence.** Prove a scalar derivative bound on a stopped interval, for both
time directions. For the cylinder use `J'_j=-∂φ_j R`; for oscillators prove
`(I_j∘w)'={I_j,R}` and its vanishing normal-form contribution. Establish a first-exit
contradiction at every outer face using `a_j+Tη_j<b_j`. Derive the compact-action or
Cartesian compact set required by the existing continuation theorem; then obtain an
interval open around `[-T,T]`. Transfer along the chart by the chain rule and
symplectic field identity. Finally prove uniqueness on interval intersections and the
`2d+Lη|t|` observable estimate. Handle `T=0` by local existence, and allow η=0 and
zero oscillator actions without division by them.

**Outputs and checks.** About 1.5–3k Lean lines over focused modules, 4–8 working days.
Run one `nice -n 5 lake build <assigned module>` at a time under the gate, with <8 GB
RSS. Run `scripts/lint_sources.sh`. In an untracked module-shaped probe, print axioms
of each actual provider/main result; accept only the standard axioms, and distinguish
provider verification from an eventual seal. Include small analytic edge cases for
zero residual, zero action and backward time; do not build a large numerical test.
The independent reviewer must trace the first-exit argument and ensure it does not
assume the requested existence interval or confinement conclusion.

**Stop/handoff.** Default-heartbeat failure means refactor; a module approaching 1,500
lines means split. A frozen type defect means stop and report the exact binder. Return
files, approach, commands and outputs, printed axiom lists, domain/endpoint uncertainties,
errata and deviations. The orchestrator alone seals after audit. Keep all certificate
and lunar-scale opt-in targets out of the build.

**Hard rules, verbatim:**

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
10. **Never edit `README.md`** (generated) or `KAM.lean` and its parts `KAM/Root/*.lean` (generated by
    `scripts/gen_root_imports.py`; no module imports them).
11. **Errata:** report every suspected defect in a pinned source (location, quoted text, why it is wrong) in your
    handoff; the orchestrator records it in `docs/errata/ledger.json`. Deviations you introduce are reported too.

## 8. Coordination and owner decisions

| Program/current work | B provides | B consumes; dependency status |
|---|---|---|
| **A1** | Checked local H decomposition, derivative/tail enclosures and useful domains | Explicit quasi-convex constants may improve a lifetime after normalization. Optional: B1's inverse-drift theorem does not need A. |
| **A2** | Finite Birkhoff jets and local normal forms | Steep Nekhoroshev geometry is a substantial B2-steep dependency. Agree on projected-gradient norms and constants before separate implementations. |
| **C** | Exact finite canonical maps, complete residual budgets and checked brackets | C's general boundary theorem can subsume B1's first-exit proof if it arrives first. B should publish its Hamiltonian specializations from that theorem; do not duplicate a generic ODE/barrier library. Resonant invariants and good-set covers belong to C. |
| **D** | B1 dynamics and a reusable normal-form certificate | D owns model extraction, physical units, observational sets, eccentricity/separation reconstruction and the full-versus-secular transfer. A SJSU certificate must pin the common H and chart versions. |
| **v2 / hybrid** | A consumer requiring transverse estimates and chart margins | Optional exact-torus input. B1 can work around finite canonical approximate normal forms with all defects included. Hybrid theorem improvements do not imply a finished hybrid checker. |
| **LG00** | Small planetary regression for chart and residual routines | Exact 69-monomial model and existing numerical scout. Keep its two-degree barrier result distinct from a finite neighborhood theorem. |
| **Full SJS** | Potential region lifetime after the torus/model work closes | No dependency for the core. It remains a separate data/memory campaign; a lunar hybrid success does not validate its scaling. |
| **SO and next demonstrations** | Reusable arithmetic if useful | Reuse proven dyadic/packed primitives and performance receipts. Do not change the Moon-lock route or conflate spin with orbital lifetime. |

The required ownership boundary is the mathematical object, not just a directory:
one agreed expression semantics, one canonical-flow representation, one tail convention,
and one generic first-exit API. B owns nonresonant normal-form checking and its two
Hamiltonian region interfaces; C owns retained resonant dynamics; D owns a planetary
model's physical meaning. None may promote a conditional helper into another program's
completed headline.

The owner decisions to make **after reviewing this concrete plan** are:

1. **Primary scope:** B1 checker and one literal instance (recommended), versus starting
   B2-most as a theory-first project. B2-steep is a third choice with a much larger
   dependency on A.
2. **First acceptance target:** approve the HH model, original action box and `10^10`
   model-unit time in §4 as the pilot goal. Approval of the goal still precedes review
   of exact Lean commands; it is not a freeze.
3. **Flagship:** secular SJSU with D (recommended) or a restricted Trojan lifetime first.
   If at least three degrees after reduction is essential, select full planar SJS or
   four-giant secular dynamics and commission a new scout.
4. **Minimum planetary region:** source-scale `10^-7` normalized action radius after a
   physical-coordinate audit, or the complete observational uncertainty set. The latter
   is not supported by the current evidence and changes the feasibility assessment.
5. **Compute allocation:** a 30-CPU-hour ceiling for the first HH replay, then a separately
   justified 100–1,000-hour application budget. Every process retains the current memory
   cap; bigger-generation hardware requires a separate concrete resource decision.
6. **Source deviations:** accept the analytic/fixed-H B2 specialization if that track is
   chosen, and approve the source typo dispositions before those lines guide a freeze.

No answer is required to complete this planning task. No new declarations have been
frozen and no application literals have been represented as owner-approved.

## 9. Pinned evidence, source findings and validation handoff

### Sources and locators

PDFs were downloaded as data into `/tmp/prog-b-astra/papers/`; no downloaded code was
run. `sources.json` there records complete URLs, byte counts and SHA-256 values.
The four central proof/calibration sources are pinned here so the source identity
survives disposal of scratch:

| Label | Version and exact use | SHA-256 of downloaded PDF |
|---|---|---|
| **CL20** | Caracciolo–Locatelli, *Computer-assisted estimates for Birkhoff normal forms*, JCD 7(2), 2020; [arXiv 2102.05959v1](https://arxiv.org/pdf/2102.05959v1). (1), Lemma 2.1, (8)–(11), Proposition 3.3, (32)–(37); HH (45), Appendix B; Trojan (46)–(47), Table 2. | `fe288ead9f2d02c3527875154bb1f21195eba0fac1f19bfaf55e6e0e596410e8` |
| **BFN16** | [1601.01783v1](https://arxiv.org/pdf/1601.01783v1), Definition 1 p. 3, Definition 2 and Theorem A p. 4; proof §4 and Appendix A. Analytic stable-steepness successor. | `afb2b3a9958984e08a75ff9008365ad35bac10a79204222dab11cb74760695d5` |
| **BF21** | [2105.01297v1](https://arxiv.org/pdf/2105.01297v1), (1.1)–(1.3), Theorem A (2.1)–(2.2), m* discussion p. 5; Theorem 1 (3.1)–(3.3), Proposition 1 and Theorem 2. General near-torus successor. | `613cb07b3e543abd519bc34a6bf9089f1c568d9b066f3085897e2370bcc73415` |
| **GLS17** | [1702.04894v1](https://arxiv.org/pdf/1702.04894v1), model §2, coefficient count p. 10, normalization (40)–(55), escape estimate (56)–(60), Figure 2 and uncertainty comparison (61), pp. 24–27. | `254d52fb9c545efe12cfcc4b138ac8b429c1e95aad0d63c12b4e6dfc182e1cae` |

Optional GCP26 is pinned at `2601.18268v1`, SHA-256
`51e8791b29031969edc05afaf6d7a478fdb2298a7f60752b7544c172a65e4c5d`;
its Theorems 2.1–2.3 are not part of the first frozen surface. The reduction source is
MG08 `0803.3246v1`, §3, (43), PDF SHA-256
`d7bf30d0db8bfe236506fd3eca8ae44de774f1b12f5d4d56b5aa8e65cd855177`.
ML21 and HML22 PDFs and hashes are in the same scratch receipt. Primary web records
were also checked for MHL23 and FH25. Published numerics and existing repository
receipts are attributed as such; no independent replay of their complete computations
is claimed.

### Suspected source defects and explicit deviations

Report these to the orchestrator for `docs/errata/ledger.json`; this task does not edit
that ledger. CL20 findings below were checked on rendered PDF pages 5, 23 and 34,
and the GLS17 findings on rendered page 12, not merely on OCR. They are candidates for
independent review, not claims that the papers' numerical results are invalid.

| Location and short quotation/formula | Issue and required disposition |
|---|---|
| **CL20 p. 5 after (4):** “equal to ℓ”; accompanying harmonic bound `\|k\|≤ℓ` | In (2), `f_ℓ∈P_(ℓ+2)`. Substituting oscillator polar coordinates preserves degree `ℓ+2` in square roots of actions and gives harmonics up to `ℓ+2`. A cubic `f₁` supplies a counterexample to the printed index. Use the degree from (2) and verify the homological range. |
| **CL20 p. 34 after (56):** `2\|ℓ\|=s` and `\|ℓ\|+\|ℓ̃\|=s` | The displayed expansions of `Z_s,f_s` appear to omit the same `+2`. For s=0 the source's Z₀ is quadratic, not constant; Appendix B's explicit Z₂ is quartic. Pin the corrected degree convention before indexing certificate arrays. |
| **CL20 p. 23 after (47):** `ν₂=O(μ)` | Formula (47) gives `ν₂²=(1-√(1-27μ+27μ²))/2`, hence `ν₂~-(3√3/2)√μ` as μ→0⁺. The quoted order is incorrect for ν₂ itself. Evaluate the exact formula; never use that order in divisor estimates. |
| **BFN16 Definition 1, p. 3:** `(θ(0),I(0))∈V_(2r)T` in the time conclusion | Repeats the initial point, making the confinement clause tautological. The action version on p. 4 uses I(t). This known finding is carried from ambition; use the intended trajectory conclusion only after the source ruling. |
| **GLS17 p. 12, end of §2.2:** `3λ₁−5λ₅−7λ₃` (three occurrences) | Only λ₁,λ₂,λ₃ exist in this three-planet model. The preceding construction and sum of the two stated generating harmonics give `3λ₁−5λ₂−7λ₃`. Treat the λ₅ index as a source transcription defect; do not introduce a fifth angle. |
| **GLS17 p. 12, (13):** quadratic sum `j=0,…,3` | The surrounding text and Table 2 have precisely three modal frequencies, ν₁,ν₂,ν₃. The lower limit should be 1 under those conventions. Confirm the indexing against the coefficient data before model extraction. |

**Unresolved convention to check, not a concluded erratum:** CL20 §5.2.1 converts its
requested lifetime to Jupiter revolutions, whereas the rotating-frame Hamiltonian's
unit angular rate naturally uses time with primary period `2π`. Reconstruct the exact
Hamiltonian/time scaling and whether an additional `2π` conversion was applied before
claiming that a table row proves a number of years. The HH pilot avoids this physical
unit ambiguity. The GLS17 full-tail omission in (58) and its approximate coordinate
uncertainty transfer are acknowledged numerical approximations, not rigorous inputs.

**Our deviations:** C² rather than analytic regularity for the elementary B1 theorem;
anisotropic/closed initial boxes with strict outer margins; explicit two-sided existence,
uniqueness and observable transfer; Cartesian oscillator handling at zero actions;
the finite supported-expression checker; and the explicitly weaker analytic, fixed-H
stability projections for B2. Period, norm and time conversions must be proved. No
existing frozen declaration was altered. No new mathematical breakthrough or literature
priority is claimed for these interfaces or their proposed applications.

### Work performed and checks

The only project file changed is `docs/explorations/program-b-plan.md`. All research,
downloads, page renders, scripts and logs are under `/tmp/prog-b-astra/`. No GitHub
operation, Lean build, Lean probe, dependency modification, frozen/manifest edit or
generated-file edit was performed. No agents were launched for this task.

Executed the exact symbolic scout and inspected its zero homological residuals and
resource output (§4). Ran `scripts/lint_sources.sh` through a scratch `python3` wrapper
that adds `-B` to avoid repository bytecode writes and refuses only the ABI subprocess.
That subprocess invokes Lean and writes `.lake/abi-scratch`, conflicting with the
brief's no-build/limited-probe and write-location constraints. Actual receipt:

```text
check_lean_modules: PASS (1829 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI SKIPPED: PROGRAM-B forbids builds and repository scratch; no ABI Lean probes run.
lint exit: 1
```

This is a **partial lint run**, not a passing full lint. No diagnostics were emitted by
the other phases. Targeted build: not run, as required by PROGRAM-B; no Lean module was
changed. `#print axioms`: not applicable to this documentation-only change. Axiom lists
for the reused theorems were not independently rechecked.

The document check resolved 29 local-link occurrences to 28 existing targets, found
both worker briefs' hard-rule blocks byte-for-byte identical to AGENTS.md, and checked
all nine numbered sections, balanced code/display delimiters and consistent column
counts in all ten tables. Receipt: `/tmp/prog-b-astra/document-check.json`.
`git diff --cached --check` returned exit 0 with no output; the staged scope contains
only this document. Repeat that whitespace/scope check after recording this receipt.

Remaining uncertainties are the complete numerical tail and chart bounds even for HH,
actual kernel shard costs, the SJSU coefficient/model package and its physical region,
and the quantitative feasibility of any inner-planet target. These are explicit package
gates; successful document checks cannot resolve those mathematical uncertainties.
