# Program C: certified confinement from resonant approximate integrals

30 October 2026. Planning snapshot: `fb782d6947546b4a5121a509a76844e325f54987`,
branch `prog-c`. This develops Program C of [ambition.md](ambition.md).
It proposes work; it does not freeze a statement, certify planetary data, or report a Lean build.

**Recommendation.** Build the general first-exit theorem, then a checker for derivatives
of explicit observables in the original vector field. Test it on the fully specified
13-term Hamiltonian below. In parallel with subsequent development, investigate the
three quantities identified by Mogavero–Hoang–Laskar (MHL23). The decisive planetary
tests are uniform derivative bounds and separation of the entire escape boundary.
Passing one of those tests without the other does not give confinement.

The direct-observable route is important: a numerical normal form can suggest a
polynomial approximate integral, but certification can differentiate that polynomial
against the **original** Hamiltonian. This needs neither an exact KAM torus nor a
certified canonical inverse. Exact normal forms from Program B are an additional,
potentially much sharper producer of the same certificate inputs.

The realistic first planetary ambition is a quantitative time-versus-region curve for
a pinned secular model. A five-billion-year result for a selected inner-planet region
is an ambitious experiment, not an expected outcome. A uniform five-billion-year
safety claim for the full observed inner Solar System uncertainty set is not a
credible commitment for this program.

## 1. What is already available

The manifest at the planning snapshot has 158 anchors: 134 sealed definitions,
23 sealed theorems, and one draft theorem, W-NLW2. These counts were read from
`manifest/frozen-anchors.json`; existing proofs were not rebuilt or axiom-audited here.
Older phase labels in PLAN/TRACKS and older exploration estimates are historical.

| Existing component | Reuse for C | What it does not supply |
|---|---|---|
| [Generic continuation](../../KAM/ODE/Continuation.lean), [existence](../../KAM/ODE/Existence.lean), [uniqueness](../../KAM/ODE/Uniqueness.lean), [first exit](../../KAM/ODE/Exit.lean) | `gen_confinement`, `gen_continuation_compact`, `gen_continuation_periodic`, `gen_exit`; genuine trajectories and endpoint continuation | Derivative-to-boundary certificate; the periodic API currently pairs equally sized angle/action spaces |
| [AMD first exit](../../KAM/Planetary/AMD/ConfinementExit.lean), [frozen AMD theorem](../../KAM/Frozen/Planetary/Theorems/AmdConfinement.lean) | Forward/backward bootstrap and physical transfer for its literal moving-Sun model | Its `StoppedActionBound` premise must still be proved for a new application |
| [N normal form](../../KAM/Nekhoroshev/NormalForm/NormalForm.lean), [homological equation](../../KAM/Nekhoroshev/NormalForm/Homological.lean), [lattices](../../KAM/Nekhoroshev/ResonanceGeometry/Lattice.lean) | Resonance selection, off-resonance divisors, exact analytic transformations | A finite-data producer/checker or useful numerical bounds for MHL23 |
| [Canonical transform](../../KAM/Canonical/Transform.lean), [Lie series](../../KAM/Canonical/CompositionSeries.lean) | Exact transformations with analytic remainders | A truncated substitution is not automatically such a transformation |
| [N headline](../../KAM/Frozen/Nekhoroshev/Theorems/QuasiConvexNekhoroshevComplexBound.lean), [explicit constants](../../KAM/Nekhoroshev/Interfaces/Constants.lean) | Alternative or supplementary confinement estimates from A | No need to re-prove quasi-convex Nekhoroshev; no automatic applicability to properly degenerate planetary actions |
| [Planetary exponential safety](../../KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean) | Established asymptotic planar full-model theorem | A useful threshold at actual masses; its exponent remains `2/(6n²−3n+14)` |
| [Secular SJS at cited masses](../../KAM/Frozen/Planetary/Theorems/SecularBoxAtCitedMasses.lean) | An already numerical, all-time first-order secular safety result | Neither LG00's higher-order truncated Hamiltonian nor a full Newtonian lifetime |
| [v2 theorem](../../KAM/Sharp2/G1.lean), [v2 engine](../../KAM/CertificateSharp/V2/Engine.lean), [routeV2All](../../KAM/CertificateSharp/V2/RouteAll.lean) | Optional exact torus and certificate arithmetic | A surrounding canonical chart or a region of confined initial data |
| [Hybrid theorem](../../KAM/Sharp2/Hybrid/G1.lean), [isoenergetic hybrid](../../KAM/Iso/Sharp2/Hybrid/G1.lean) | Proved restart/transfer theorems are present in this snapshot | No hybrid engine appears in `routeV2All`; the [design's](../campaign/design/APOST-SHARP-V2-HYBRID.md) floating R1 estimates are not a planetary certificate |

`routeV2All` uses a supplied witness to select a route; it does not search all routes.
Its sharp branch is definitionally the landed sharp checker. The `sqrt` primitive
is present in [HamExpr](../../KAM/Certificate/Expr/Basic.lean); older LG00 notes calling
it absent are superseded. Ordinary and bordered isoenergetic torsion remain different.
No torus checker supplies an infinite Diophantine proof from a finite numerical search.

## 2. Exact mathematical targets and the small frozen surface

All proposed names below are provisional. The mathematical binders are specified here;
the exact final Lean commands must still elaborate, undergo independent statement
review, and receive owner approval. This document is not a substitute for that process.

### C1: one general confinement theorem

Use real carriers

\[
 E_{d,q}=(\mathrm{Fin}\ d\to\mathbb R)\times
                 (\mathrm{Fin}\ q\to\mathbb R),\qquad
 S_k(x,\phi)=(x,\phi+k),\quad k:\mathrm{Fin}\ q\to\mathbb Z.
\]

The first component is any nonperiodic physical coordinate vector; the second is a
lift of period-one angles. Use the inherited maximum norms, never `EuclideanSpace`.
`q=0` is the ordinary bounded-domain theorem. For autonomous action-angle systems take
`d=q=n`, exchanging the product order through an explicit equivalence if needed.
For the forced spatial secular inner system take `d=16,q=7` in Cartesian proper modes.

Proposed frozen theorem `KAM.Confinement.approximate_integrals` has the following
quantifier order and premises. Quantify `d q m : ℕ`, `Ω D Q : Set E`,
`X : E → E`, `F : Fin m → E → ℝ`, `a b η : Fin m → ℝ`, and `T : ℝ` first.
Require:

1. `IsOpen Ω`, `IsOpen D`, `closure D ⊆ Ω`, `Q ⊆ D`, and `0 < T`.
2. `Ω` and `D` are invariant under every `S_k`; `X(S_k z)=X(z)` and
   `F_j(S_k z)=F_j(z)` for all `z∈Ω`, all `k`, and all `j`.
3. The fundamental closed piece
   \[
   K_D=\{(x,\phi)\in\overline D:0\le\phi_i\le1\text{ for every }i\}
   \]
   is compact. No assertion that the lifted cylinder itself is compact is made.
4. `ContDiffOn ℝ 1 X Ω` and `∀ j, ContDiffOn ℝ 1 (F j) Ω`.
5. For every `j`, `a j ≤ b j`, `0 ≤ η j`, and
   `∀ z∈Q, a j ≤ F j z ∧ F j z ≤ b j`.
6. For every `j` and `z∈closure D`,
   \[
   \left|\bigl(\operatorname{fderiv}_{\mathbb R} F_j(z)\bigr)(X(z))\right|
        \le\eta_j.                                                     \tag{C1a}
   \]
7. For every `y∈frontier D`, there exists `j : Fin m` such that
   \[
   F_j(y)<a_j-\eta_jT\quad\text{or}\quad b_j+\eta_jT<F_j(y).             \tag{C1b}
   \]

Then, **for every** `z₀∈Q`, there exists `z : ℝ → E` such that

\[
 z(0)=z_0,\qquad
 \forall t\in[-T,T],\quad z(t)\in D,\quad
 \operatorname{HasDerivAt}(z,X(z(t)),t),\quad
 \forall j,\ |F_j(z(t))-F_j(z_0)|\le\eta_j|t|.                           \tag{C1c}
\]

Include uniqueness explicitly: for every open order-connected `J⊆ℝ` containing zero
and every `y : ℝ → E`, if `y 0=z₀` and
`∀ t∈J, y t∈Ω ∧ HasDerivAt y (X (y t)) t`, then `y t=z t` on
`J∩[-T,T]`. One can also export the closed-interval uniqueness form already used in N.
Do **not** write `∃! z : ℝ → E`: extensions outside the required interval are arbitrary.
The derivative at both endpoints is two-sided, obtained by extending the solution
past them. Existence on the requested interval is part of the conclusion.

This first version assumes a C¹ field, which is locally Lipschitz. That is a declared
scope restriction of the locally Lipschitz formulation in ambition.md and matches the
existing generic ODE library. Every intended analytic Hamiltonian application satisfies
it. A later locally Lipschitz-only variant would require generalizing that library;
it is not needed for the first applications and must not delay the first freeze.

There is no positive lower bound on `η`; exact integrals have `η=0`. There is no
independence assumption on the `F_j`, no quasi-convexity, no small-divisor hypothesis,
and no dimension restriction. The hypotheses are static regularity, inequalities,
and geometry. No trajectory-confinement premise is allowed on this public theorem.
Empty initial sets are permitted by the generic theorem, but application acceptance
requires a separately verified positive-volume initial region.

**Proof obligations, kept internal.** Chain rule for `F_j∘z`; scalar derivative bound
on a stopped time interval; first exit in each time direction; compact continuation;
periodic reduction to a compact fundamental piece; uniqueness. If a maximal endpoint
is finite before `T`, periodicity bounds `X` on `closure D`, hence bounds the lifted
angle displacement by `M|t|`; the relevant part of the lifted closure is then compact
inside `Ω`, contradicting maximality. At an actual exit time, (C1a) contradicts (C1b).
The proof needs no differentiable boundary and does not use the number of integrals
as a substitute for separation.

**Frozen surface.** Freeze only this theorem initially, with its literal predicates
expanded in the final command. Standard function/product carriers need no new semantic
wrapper. Keep the derivative estimate, box checker, resonance algebra, and measure
assembly as ordinary implementation theorems. Freeze an eventual planetary headline
and its exact model/region/observable definitions only after that instance has been
selected and reviewed. Providers remain quarantined until their frozen anchor is sealed.

**Source and novelty.** C1 is our explicit generalization and packaging of the elementary
derivative/escape argument, not a verbatim theorem of MHL23. The estimate is the mechanism
of [GLS17 §4.3, (56)–(57)](https://arxiv.org/pdf/1702.04894v1) and
[CL21 §4.1, (32)–(37)](https://arxiv.org/pdf/2102.05959v1); continuation is supplied by
the existing ODE proofs. This is familiar mathematics. A reusable checked interface,
and any successful new numerical instance, are the prospective contributions.

### C2: the derivative certificate and resonant algebra

For canonical period-one variables `(θ,J)` use

\[
 \{F,H\}=\sum_i(\partial_{\theta_i}F\,\partial_{J_i}H
                    -\partial_{J_i}F\,\partial_{\theta_i}H).
\]

For an autonomous Hamiltonian this is `dF(X_H)`. For a forced Hamiltonian
`H(θ,J,φ)` with `φ̇=ν`, the actual operator is

\[
 \mathcal L F=\{F,H\}_{\theta,J}+\nu\cdot\partial_\phi F.               \tag{C2a}
\]

Prove these calculus identities, not just identities between formal coefficient arrays.
Use Cartesian `(q,p)` near zero oscillator actions; derivatives of `sqrt(J)` at zero
are not legal. Complex coefficient carriers are `Fin n → ℂ`; Fourier keys are
`Fin n → ℤ`, including the combined physical/forcing angles.

**Direct route, recommended first.** Supply finite literal observables `P_j` and a
supported literal field `X̂`, plus componentwise bounds
`|X_k−X̂_k|≤e_k` on `closure D`. Certify

\[
 |dP_j(X̂)|\le r_j,\qquad |\partial_kP_j|\le L_{jk},\qquad
 \eta_j=r_j+\sum_k L_{jk}e_k.                                         \tag{C2b}
\]

All `r,L,e` are nonnegative rational upper bounds. The sum runs over **every** field
component, including forcing-frequency errors. Then (C1a) follows for the actual field.
If `X=X̂`, the second term is zero. Numerical discovery of `P_j` is untrusted; the
theorem is about their literal finite expressions. A near-identity formal substitution
can generate candidates without being advertised as an exact canonical transformation.

For a chosen physical observable `A_l`, if throughout `D`

\[
 |A_l(z)-(c_l+\sum_j B_{lj}P_j(z))|\le d_l,
\]

derive `|A_l(z(t))−A_l(z₀)|≤2d_l+Σ_j |B_lj|η_j|t|`. For collision exclusion,
it is often better to prove a static lower bound on each separation throughout `D`.
A bound on a proper-mode action alone is not automatically a bound on Mercury's
eccentricity or on physical pair distances.

**Normal-form route.** If B supplies an exact C² canonical diffeomorphism `Ψ` on an
open neighborhood of the closure of the working region, with verified inverse,
`H∘Ψ=Z+R`, and `\{F_j,Z\}=0`, then `\{F_j,H∘Ψ\}=\{F_j,R\}`.
Bound the latter, apply C1, and transport trajectories through `Ψ`. Every omitted
Lie term, original-model truncation, coefficient uncertainty, and chart-domain margin
must be included. A C⁰ remainder norm needs a stated derivative loss before it bounds
this bracket. In time-dependent charts the transformed Hamiltonian also has the
time-generator term; equivalently verify the full vector-field conjugacy.

For a finite resonant Fourier polynomial

\[
 Z(\theta,J)=\sum_{k\in S}z_k(J)e^{2\pi i k\cdot\theta},\quad
 F_j(J)=b_j\cdot J,\quad b_j\cdot k=0\ (k\in S),                       \tag{C2c}
\]

prove `\{F_j,Z\}=0` coefficientwise. With full signed support for a remainder
`R=Σ_k r_k(J)e^{2πik·θ}`, a real-domain bound is
`sup |{F_j,R}|≤2πΣ_k |b_j·k| sup|r_k|`; choose `η_j` as a rational upper enclosure
of the right-hand side. If storing only one representative of each conjugate
pair, double that pair's contribution. Do not lose the factor `2π` or count both
conventions at once. Realness is certified by conjugate symmetry.

For forced finite sums `H=Σ_(k,ℓ) h_(k,ℓ)(J)e^{2πi(k·θ+ℓ·φ)}`, the linear action
integrals obey the same `b·k=0` condition. The energy-like quantity `E=H+β·J` has

\[
 \mathcal L E=\nu\cdot\partial_\phi H-\beta\cdot\partial_\theta H;
 \qquad \nu\cdot\ell-\beta\cdot k=0                                 \tag{C2d}
\]

on every retained mode. These are different nullspace tests. Adding artificial
conjugate actions for the forcing does not make physical energy or AMD conserved.

The algebra follows [MHL23 §IV.A, (11)–(20)](https://arxiv.org/pdf/2305.01683v1).
[CL21 §4.2, (39)–(44)](https://arxiv.org/pdf/2102.05959v1) already rigorously combines
nonresonant action bounds with energy in a one-resonant-angle normal form. General
finite annihilator families and checked boundary covers extend the interface; we
should not claim to have invented resonant effective stability.

### C3: a finite good-set theorem

Fix an explicitly specified initial-coordinate box
`Q₀=∏_(i:Fin d₀) [l_i,u_i)`, rational `l_i<u_i`, rational `0≤δ≤1`, and a specified
map `ι` into initial physical states. A fixed forcing phase is allowed in `ι`.
Partition `Q₀` by a checked finite rational subdivision tree. For an accepted set of
leaves `A`, let `G₀=⋃_(c∈A)c`. Each accepted leaf must have a C1 certificate for
**every** point of `ι(c)`, with the requested horizon `T` and its certified region
contained in the advertised safety region `D_*`. If

\[
 \sum_{c\in A}\prod_i(u_{c,i}-l_{c,i})
       \ge(1-\delta)\prod_i(u_i-l_i),                                \tag{C3}
\]

then Lebesgue measure in these initial coordinates satisfies
`volume(Q₀∖G₀)≤δ volume(Q₀)`, and every `u∈G₀` gives the advertised trajectory
from `ι(u)`. Half-open leaves are disjoint; excluded outer faces have zero measure.
For closed-box all-data claims those faces must also be certified.

This theorem measures the **initial coordinate box**, not a presumed distribution of
chaotic trajectories. It requires no ergodic hypothesis or volume-preserving flow.
If the advertised measure is physical canonical volume, a nonlinear chart needs its
Jacobian and injectivity proof. If it is an observational probability density, certify
cell masses or density bounds and use weighted sums. A box at one fixed forcing phase
has zero ambient 23-dimensional volume; use its 16-dimensional initial-data measure.
Failed leaves are unresolved, not proved unstable. Numerical ensemble frequencies
are not inputs to (C3).

## 3. What the finite checker must actually verify

Keep producer and checker separate. The producer may use floating optimization,
linear algebra, or numerical normal forms. Lean checks only finite identities,
outward bounds, and covers. There is no trusted external numerical oracle.

| Certificate field | Required semantics and check |
|---|---|
| Model and parameter data | Exact rational polynomial/trigonometric expression, or quantified parameter intervals with proved enclosures; canonical convention and time scale explicit |
| Domain and initial set | Strict inner/outer margins, regularity of all expression primitives, compactness modulo angles, exact containment of the initial set |
| Observables | Literal finite expressions; initial ranges enclosed on all of `Q`; constants chosen before quantifying the initial point |
| Derivative rows | Exact bracket/directional-derivative identity, then outward bound on the entire working closure; sum all error sources as in (C2b) |
| Boundary cover | A finite, proved cover of every physical exit face or algebraic boundary piece, modulo angles; a witness index `j` and sign for each leaf |
| Separation leaf | For a rational positive slack `s`, prove `sup F_j ≤ a_j−η_jT−s` or `b_j+η_jT+s ≤ inf F_j` on that leaf |
| Requested time | A rational time and checked multiplication `η_j*T`; no giant exponential is needed |
| Output | C1's existence, uniqueness, confinement, and drift conclusions, followed by the stated observable transfer |

For rectangular domains, every closed face, including edges and corners, belongs to
the checked cover. A numerical grid is not a cover proof. Start with outward interval
evaluation plus exact affine Farkas witnesses and simple algebraic sublevel identities.
For action polytopes, rational LP dual multipliers can prove separation; checking a
dual witness is much cheaper than formally implementing an optimizer. Add Bernstein
enclosures only if interval dependence demonstrably blocks a useful instance. General
sum-of-squares optimization is not an initial dependency.

A single globally assigned `j` per face can be too restrictive. Allow subdivisions
with different indices/signs and prove their union covers the face. Do not test each
point using whichever observable looks best without recording a finite cover.

Error allocation is explicit:

\[
 \eta_j=\eta_{j,\mathrm{finite}}+\eta_{j,\mathrm{Lie\ tail}}+
 \eta_{j,\mathrm{model\ tail}}+\eta_{j,\mathrm{rounding}}+
 \eta_{j,\mathrm{parameter/forcing}}.
\]

These labels denote separately proved bounds, not guessed safety factors. A zero
model tail means the result is about the chosen truncated model. If approximate
coordinates are used to state physical observables, their error also consumes the
boundary or observable margin; it cannot be silently absorbed into a plotted curve.

For a forward/backward horizon, retain absolute derivative bounds. A future one-sided
barrier version can exploit signed derivatives for a forward-only claim, but it needs
a distinct theorem and certificate interpretation.

## 4. A complete small target, and experiments already performed

### A 13-term example with a genuine approximate integral

This is an original engineering example, not a planetary model. Let
`q,p : Fin 3 → ℝ`, with indices written as 1,2,3 below, and set

\[
 I_i=(q_i^2+p_i^2)/2,\quad S=I_1+I_2+I_3,\quad
 A_{ij}=q_iq_j+p_ip_j,
\]
\[
 H_0=I_1-I_2+\tfrac12 I_3+\tfrac1{10}(A_{12}^2+A_{23}^2),\qquad
 H=H_0+10^{-8}q_1.                                                    \tag{T1}
\]

Every coefficient is an exact rational. The bracket convention is
`{F,H}=Σ(∂q F ∂p H−∂p F ∂q H)`. Each `A_ij` is unchanged by simultaneous rotation
of all oscillator planes, so

\[
 \{S,H_0\}=0,\qquad \{S,H\}=-10^{-8}p_1.                              \tag{T2}
\]

Choose `Ω=ℝ⁶`, `D={S<1/2}`, `Q={|q_i|≤1/4, |p_i|≤1/4}`, `F=S`,
`[a,b]=[0,1/4]`, `η=1/100000000`, and `T=10000000` in model time units.
On `Q`, `S≤3/16`; its volume is `1/64`. On `closure D`, `|p₁|≤1`.
The entire boundary has `S=1/2`, while `b+ηT=7/20`; the strict slack is `3/20`.
Consequently the **proposed, not yet Lean-proved** application is

\[
 \forall z_0\in Q,\quad \exists z\text{ uniquely on }[-10^7,10^7],\quad
 \dot z=X_H(z),\quad z(0)=z_0,\quad S(z(t))<\tfrac12,
 \quad |S(z(t))-S(z_0)|\le10^{-8}|t|.                                  \tag{T3}
\]

This tests a nonzero derivative, a positive-volume region, both time directions,
every boundary point, and continuation. The quadratic Hamiltonian is indefinite,
so the example is not merely positive-energy confinement. For instance, on
`q=(0,a,0), p=(a,0,0)`, `H=0` for arbitrarily large `a`:
energy alone does not confine the zero level. The symmetry of `H₀` is exact; the
small linear forcing breaks it. No chaotic trajectory is claimed.

An exact symbolic expansion has 13 Hamiltonian monomials. On the unit coordinate
box, summing absolute coefficients of the three separate action brackets gives
`3.20000001`; summing those brackets **before** taking absolute values gives only
`10⁻⁸`. Thus this benchmark tests a roughly `3.2×10⁸` improvement in this particular
crude derivative estimate. It is not a comparison against an optimized Nekhoroshev
theorem or every possible energy argument.

### Exact source algebra reproduced here

MHL23's proposed quantities, in its own radian proper-mode coordinates, are

\[
 C_{\rm inc}=\Psi_1+\Psi_2+\Psi_3+\Psi_4,\qquad
 C_2=-X_3-X_4+\Psi_1+\Psi_2+2\Psi_3+2\Psi_4,
\]
\[
 E_{2n}=H_{2n}+g_5\sum_{i=1}^4(X_i+\Psi_i).
\]

These are (18)–(20), with `I=(X₁,…,X₄,Ψ₁,…,Ψ₄)`. The leading-resonance table
does not contain all terms of the Hamiltonian. In particular, weak terms that break
these symmetries must remain in the derivative budget.

I transcribed the 30 rows of Table II, checked the rendered PDF page 5, and used
exact rational algebra in Python. With the inner columns ordered as above:

| Check | Result |
|---|---|
| Rank of the 30×8 inner wavevector matrix | 6 |
| Null vectors `(0,0,0,0,1,1,1,1)` and `(0,0,−1,−1,1,1,2,2)` | Both annihilate all 30 rows exactly |
| Minor: rows 1,2,3,4,6,8; columns 1,2,3,4,5,7, all one-based | Determinant 1; a small rank witness |
| Sum of the eight inner indices plus the `g₅` index | Zero on every row; energy-like symmetry check |
| Add Table III's `g₃−g₆+s₂−s₄` | Inner rank becomes 7 |
| Also add its `g₂−g₆+s₁−s₆` | Inner rank becomes 8 |

The last two tests are useful negative controls. Preserving two exact linear action
integrals after adding those modes would be a transcription or checker error.
This proves no drift bound: amplitudes, domains, and tails have not been checked.

For reproducing the unit minor, its six rows restricted to the six stated columns are

```text
 0  0  1 -1  0 -1
 1 -1  0  0  1  0
 0  1  0  0 -2  0
 0  0  2 -2  0 -1
 0  1  0 -1  0  0
 1  0 -1  0  0 -1
```

The complete transcription and calculation are in
`/tmp/prog-c-astra/table2-rows.json`, `scout.py`, and `scout-results.json`.
The combined rank, polynomial, size, and time-budget calculation took 0.053 CPU s
after imports and peaked at 631612 KiB RSS in this environment. These are Python
measurements, not kernel timings. The script runs with one BLAS/OpenMP thread and
uses no Lean. Its results must be independently replayed before becoming proof inputs.

## 5. The inner Solar System: the exact opportunity and the obstruction

**Plausible with this program:** prove confinement for every point of a specified
small region in an explicitly truncated, forced, spatial secular model of Mercury,
Venus, Earth, and Mars, including the chosen relativistic secular term and prescribed
outer-planet modes. Publish certified horizons beginning at 1 and 10 Myr, then test
100 Myr, 1 Gyr, and 5 Gyr without changing the model or initial region silently.
An unsuccessful long-time test still yields a meaningful curve and a quantified
obstruction. Present-day observational uncertainties are not supplied by the papers'
nominal points; no uncertainty enclosure is available in this task.

**Plausible only with substantial new quantitative mathematics or unexpectedly strong
certificate closure:** a large good fraction of an observationally relevant inner
region for 5 Gyr; transport bounds for the full spatial eight-planet force model;
or bounds that exploit cancellation over time when uniform absolute derivative
bounds fail. The first is a credible research direction, not established feasibility.
The full-model transfer needs averaging errors, outer feedback, model parameters,
physical reconstruction, and relativistic conventions to be controlled over the same
domain and horizon. It is much more than adding a coefficient file.

**Not plausible as a deliverable of this plan:** all initial conditions in the actual
inner-system uncertainty set remain safe for 5 Gyr; all-time safety of the real Solar
System; or a claimed 99% probability from a numerical sample alone. The numerically
observed rare instability makes the first a particularly poor target. Those numerical
orbits are evidence against the target, not themselves a formal counterexample.

The precise model and obstacles are as follows.

* **Model.** [ML21 §§2–4](https://arxiv.org/pdf/2105.14976v1) and
  [MHL23 §II, (1)–(6)](https://arxiv.org/pdf/2305.01683v1) supply the first-order
  averaged, relativistically corrected model and the prescribed outer forcing.
  There are eight physical degrees of freedom and seven external frequencies.
  A forced inner subsystem does not inherit conservation of total planetary AMD.
  Dropping inclinations gives a different planar problem and removes part of the
  proposed `C_inc` mechanism. The initial C application should retain the spatial model.
* **Which polynomial.** Pin the entire `H₆` coefficient table, forcing amplitudes,
  parameter conventions, and proper-mode transformation before a numerical lifetime
  is claimed. MHL23 distinguishes its two truncation procedures in Table I and §II;
  they are only approximately equivalent. Its resonance ranking uses a transformed
  Hamiltonian, discussed immediately before §IV.A. Do not identify that transform with
  the original variables without accounting for the change. The inspected PDFs do not
  themselves supply a complete executable, rigorously enclosed `H₆` table. Obtaining
  or reconstructing it is a real first dependency; author contact, if needed, is an
  owner action, not authorized by this brief.
* **Rare events.** LG09's 2,501 integrations and ML21 Appendix C support an order-one-percent
  frequency of large Mercury eccentricity excursions over 5 Gyr in those ensembles.
  This is not the same as a one-percent collision probability or a measured Lebesgue
  fraction of a box. The `g₁−g₅` resonance and relativistic precession matter. See
  [LG09](https://doi.org/10.1038/nature08096), with the detailed count checked here through
  [ML21 Appendix C](https://arxiv.org/pdf/2105.14976v1), rather than a locally obtained
  LG09 full text.
* **Truncation changes the answer.** [HML22 §4.1 and Table 1](https://arxiv.org/pdf/2205.04170v1)
  finds sharply different 5-Gyr high-eccentricity statistics at degrees four and six.
  A theorem for `H₄` or the `g₅`-only `H^•` model can be useful, but it cannot be labelled
  a certificate for `H₆` or Gauss's full secular model. With a finite-model theorem,
  no omitted-physics tail is required; with a transfer claim it is indispensable.
* **Uniform derivatives, not filtered motion.** MHL23 §IV.B filters time series before
  comparing slow variation. Nonresonant harmonics can have large oscillatory derivatives.
  C1's worst-case `ηT` ignores cancellation. Correct the observables by finite averaging,
  or prove a separate oscillatory-integral estimate, before expecting a long horizon.
  Never remove a term solely because it was nonresonant along one nominal orbit.
* **The boundary can fail even when the derivatives pass.** `C_inc` and `C₂` have no
  `X₁` or `X₂` coefficient. At quadratic order, `E₂=γ₃·I` adds only one constraint on
  those two actions. Using the displayed rounded Appendix B values `−1.61,−3.20`,
  the displacement `ΔX₁=(320/161)s, ΔX₂=−s` preserves all three linear quantities,
  until positivity of `X₂` intervenes. This is a diagnostic for the rounded linear
  surrogate, not a trajectory of `H₆`; the analogous direction exists for the exact
  quadratic coefficients. Actual nonlinear geometry and conversion to eccentricity
  must decide whether the desired escape surface is separated.
* **Masses and degeneracy.** Jupiter's mass ratio is of order `10⁻³`, not an arbitrarily
  small theorem parameter. C1 does not demand twist, steepness, or a small mass, so
  proper degeneracy is no obstruction to stating it. The same degeneracy still makes
  constructing useful approximate integrals and bounding secular denominators difficult.
  Keeping the actual coefficients is mandatory for an actual-mass instance.
* **Diffusion.** Resonance channels are allowed; C controls motion transverse to them
  only as far as the observables constrain it. For at least three degrees of freedom
  after exact reductions, KAM tori do not automatically separate an energy surface.
  Arnold diffusion is compatible with finite confinement. Neither its possibility
  nor the failure of a certificate proves that a selected planetary region escapes.

The numerical budget is severe but transparent. If an observable is normalized so that
its usable boundary gap is `d=10⁻³`, and half the gap is reserved for other margins,
5 Gyr needs

\[
 \eta\le\frac{10^{-3}}{2(5\cdot10^9)}=10^{-13}\ {
m yr}^{-1}.
\]

With one Myr as the computational time unit, the same requirement is `T=5000` and
`η≤10⁻⁷` per computational unit. These are **budget examples**, not measured planetary
rates. At `η=10⁻¹¹ yr⁻¹` the half-gap horizon is only 50 Myr. A single omitted term
of that size can therefore decide the project.

Use `χ=2πθ`, `J=2πI` when converting canonical radian angles/actions to period one:
`dχ∧dI=dθ∧dJ`. MHL's external angles have velocity `−ω_o`; therefore the period-one
velocity is `ν=−ω_o/(2π)`, and the coefficient in `E=H+β·J` is
`β=g₅(1,…,1)/(2π)`. Frequencies printed in arcseconds/year need the additional exact
factor `π/648000` before being treated as radians/year. Record the Hamiltonian scaling
and the physical time identity `t_phys=τ_unit*t_code` together; rescaling an angle
alone is not a canonical conversion.

## 6. Ranked applications and realistic costs

The ranking is by potential scientific impact. The implementation order starts with
the small example and a source-backed calibration, not with rank 1. Runtime figures
below are allocations or prior projections unless explicitly labelled measured.

| Rank | Exact proposed claim | Why it matters; existing knowledge | Feasibility and cost |
|---|---|---|---|
| 1 | For a pinned spatial forced secular `H₆`, every initial state in a certified union `G` of cells has `e_Mercury(t)<7/10` for `0≤t≤T`, with `T` tested up to `5×10⁹ yr`; separately prove pair-separation bounds if claiming collision exclusion. Report `volume(G)/volume(Q)` for a specified initial chart. | Directly addresses fast chaos versus slow orbital transport; relevant to celestial mechanics and statistical physics. MHL23 supplies a numerical mechanism, not uniform derivative or boundary certificates. | Unknown at 5 Gyr. Start with one region and a 1–10 Myr goal. Sixteen Cartesian variables already have 74,613 monomials of degree ≤6 before forcing harmonics; degree ≤10 has 5,311,735. Counts are dense upper-envelope diagnostics, not observed sparsities. No credible full-instance kernel quote yet. Authorize at most a 100 CPU-h pilot only after a representative shard and rigorous tail estimate pass. |
| 2 | Full planar moving-Sun SJS, at the cited model masses, every initial state in a specified positive-volume reduced region has explicit eccentricity and pair-distance bounds through 5 Gyr. | A true full-flow finite-region result beyond a torus; three degrees of freedom after planar angular-momentum reduction. [FH25](https://arxiv.org/pdf/2403.10152v1) gives a high-precision numerical torus, not this theorem. Existing P gives small-mass asymptotics. | Low near-term feasibility. A B/C chart-and-remainder construction or D1 route is still missing. [SJS feasibility](sjs-feasibility.md) projects 10,000–33,000 kernel CPU-h plus large elaboration/data costs for an earlier torus route, with up to 20× calibration uncertainty. These are not C lifetime costs. The cheaper packed/hybrid figures require unverified arithmetic and memory assumptions. |
| 3 | For a pinned planar secular SJSU Hamiltonian and a declared canonical chart, all points in `T³×{|J−J_*|∞≤r}` stay within a specified outer region through 5 Gyr, with eccentricity transfer. Scout `r≈10⁻⁷` in GLS17's normalization, then test the larger source uncertainty scale. | Most mature substantial planetary numerical starting point, shared with B/D. [GLS17 §4.3, (56)–(61), Fig. 2](https://arxiv.org/pdf/1702.04894v1) estimates about `10¹⁰ yr` at a radius slightly below `10⁻⁷`, versus an approximate uncertainty radius `7×10⁻⁷`. It is not a rigorous certificate. | Plausible research target with a successful tail calculation; allocate 100–1,000 kernel CPU-h only after measurement. The source's 94,109,751-monomial intermediate calculation cannot be copied into a <4 GB Python process. Streaming majorants and B's finite normal-form work are essential. This model has only two degrees of freedom after AMD/rotation reduction; it is not the flagship proving that reduced KAM barriers are unavailable. |
| 4 | Reproduce one CL21 resonant restricted-three-body stability-time bound, for its explicitly chosen mass ratio, radius and normalization, with all initial conditions in the stated region. | A rigorous external comparator for C2 and boundary closure; relevant to computer-assisted dynamics. CL21 already proves resonant results using interval arithmetic. The contribution would be Lean verification, not new celestial mechanics. | Technically plausible after B's normal-form/tail interface. Select a low-order instance with ≤10⁴ retained terms first; reserve 10–100 kernel CPU-h as an initial allocation. Reproducing the paper's largest calculation needs its own measurement. No physical-age claim or mass literal is selected by this note. |
| 5 | The exact model (T1) satisfies (T3); then certify a finite-time approximate-integral bound for the 69-monomial LG00 polynomial. | Complete tests of algebra, all-boundary geometry and continuation. LG00 has an existing rigorous two-torus confinement result for its truncated secular model; a weaker finite-time result is a calibration, not a new planetary headline. | High feasibility for (T1); allow 1–5 CPU-h for a first full proof/checker example, not a measured requirement. For LG00, start with ≤10³-term candidate observables and a 10–100 CPU-h cap. Its [scout](sjs-lg00-scout.md) projects 545–680 torus coefficients and 3–75 CPU-h per torus on v2; these are separate, unfinished torus checks, not evidence that C's boundary test closes. |

A planar four-giant secular model, including Neptune, has three degrees of freedom
after the usual one-angle reduction and is a more suitable successor if that dimension
is essential. It lacks the equally mature instance used in rank 3 here; no numerical
radius, lifetime, or kernel cost should be inherited from SJSU. A spatial full-model
Solar System claim is a further project, not a relabelling of either planar result.

For rank 4, the concrete comparator to extract first is CL21 Table 3's first resonant
Uranus row: initial action bounds `I₁<923/10⁶`, `I₂<757/10⁶`, outer action bounds
`I_i<924/10⁶`, reported time `7.18×10⁷` in the source's dynamical units. Aim first at
the conservative literal `T=6×10⁷` with those regions and its exact canonical chart.
The printed mass ratio is only approximately `4.36×10⁻⁵`; obtain the actual input
value or a valid interval before freezing an instance. These are normalization
coordinates, not measured Trojan orbital elements. Exact chart transport and the
conversion to years remain proof obligations, not implicit interpretations of the table.

For full SJS, FH25's torus generation used about 194 GB. Some hypothetical packed
products in the repository study require 28–56 GB in one process. Neither fits the
present limits. Generation would need a separately authorized machine of at least
256 GB RAM, or a demonstrated streaming algorithm. A 64 GB/process checker would
also require a changed execution policy; simply having more host RAM does not remove
the current 10 GB kill rule. C itself has no reason to wait for that campaign.

## 7. Ordered work packages

The proposed namespace is `KAM.Confinement`; finite-data implementation belongs in
`KAM.CertificateConfinement`. Paths are proposals, not files created by this task.
Keep generic ODE mathematics, coefficient arithmetic, and planetary assembly separate.
Use focused 150–600-line modules, with a cheap facade if one is useful. Do not import
the generated root or a draft anchor into implementation modules.

| Package | Inputs → outputs | Incremental size and checks | Stop/go criterion |
|---|---|---|---|
| C0 — exact statement and source packet | This note, pinned sources, ODE signatures → complete candidate Lean commands, expanded semantic dependencies, review questions and audit packet | 200–500 lines of review/type-probe material; ≤200 Python; no theorem claimed. Independent binder/source/endpoint audit before freezing | Stop the freeze if C¹ scope, cylinder compactness, endpoint semantics, or force-model conventions remain disputed |
| C1 — proof and complete small instance | Owner-frozen C1 statement → generic theorem provider, sealed anchor through the orchestrator, ordinary proof of (T3) | 1.5–3.5k handwritten Lean, ≤200 Python. Narrow builds, lint, main-result axioms, independent proof/statement review | No assumed existence through `T`, no assumed confinement, no heartbeat override; if periodic plumbing exceeds scope, seal bounded specialization only through an explicitly approved revised surface |
| C2 — finite derivative/boundary checker | C1; existing dyadic arithmetic; finite polynomial/trigonometric semantics → ordinary soundness theorem yielding C1 conclusions from finite data | 4–8k Lean; 0.8–1.8k Python; generated data separate. Complete (T1) certificate and negative fixtures | One representative data check <8 GB and <40 CPU min; no unbounded exact-rational ball growth; coverage and strict margins must be kernel checked |
| C3 — resonant and forced adapters | C2, MHL coefficient provenance; optionally B's exact normal forms → (C2a)–(C2d), checked nullspace witnesses, original-field residuals | 4–10k Lean; 1–3k Python, overlapping B. Exact 30-row replay, retained/broken-mode tests, one controlled analytic tail | No Gyr claim until every omitted interaction has a derivative budget; stop the selected model if its table or coordinate identity cannot be pinned |
| C4 — finite good-set assembly | C2/C3 and a fixed measure/initial box → (C3), disjoint cover accounting and model-to-observable bounds | 1–3k Lean; 0.4–1k Python; exact leaf volumes and weighted variant only if required | Freeze `Q`, measure and minimum acceptable covered fraction before optimization; reject duplicate leaves and unsupported Jacobian assumptions |
| C5 — first planetary curve | LG00 or D's selected secular model, chosen region and observables → verified `T(r)` with all tail/coordinate costs | 2–6k application Lean and 1–3k Python if model data already exist; do not add these mechanically to B/D estimates | Require ≥10× gain over the agreed direct-coordinate bound on the same region; record a failed desired horizon without silently shrinking the region |
| C6 — inner-system flagship | Pinned forced spatial `H₆`, parameter/phase convention, C3/C4, physical chart → a definite finite-time good-set or all-data model theorem | Additional 8–20k model/transport Lean and 3–8k Python, low confidence; certificate volume unknown | The geometry, derivative, and cost experiments below must all pass; otherwise publish shorter times or the obstruction |

The reusable C core totals roughly 11–25k handwritten Lean lines, excluding the model
and any B normal-form generator. Estimates have at least factor-two uncertainty.
Shared arithmetic work must be counted once between B and C. The 13-term example can
be proved by direct algebra before implementing a general Boolean checker; it tests
the theorem independently of the numerical pipeline. A CL21 instance subsequently
tests a genuine resonant normal-form producer.

### First worker brief: C0 — statement and source packet

**Task.** Make the exact C1 surface reviewable. Read AGENTS.md, PLAN, DECISIONS, this
plan, `KAM/ODE/{Existence,Uniqueness,Continuation,Exit}.lean`, and the source locators
in §10. Work only in the designated packet/scratch paths supplied by the orchestrator.
Do not change a frozen file, manifest, existing provider, generated file, or shared
checker. This is a bounded statement task, not a request to launch other agents.

**Output.** The complete Lean theorem command for §2, with every binder and predicate
visible, plus a source-to-binder table and a proof-dependency list. Its proof body is
not a new scratch `sorry`: the orchestrator alone creates the manifest-bound draft
after approval. If checking a type before that point, use an untracked `#check` of
the proposition expression; that probe has no frozen-declaration status. Preserve
the actual command for the final owner review.

Resolve the product order and translation equivalence explicitly. Ensure `q=0`,
`η_j=0`, endpoint derivatives, and common-interval uniqueness are meaningful. Check
that the compact-fundamental-piece premise is satisfied by physical boxes times the
forcing torus and by the bounded toy domain. Identify the exact ODE lemmas that require
C¹ regularity. Expand any reused `IsSolutionIn` or local-Lipschitz structure during
review; no hidden trajectory assumption is acceptable.

Reproduce the six-row determinant witness and the polynomial bracket (T2) from
source/data, independently of the scratch output. Record the period-one conversion
and the distinction between `H₂n`, its proper-mode truncation, and the transformed
Hamiltonian used for ranking. Do not claim a planetary table has been supplied when
only its resonance indices are available.

**Checks and handoff.** List source version/hash/locator for each borrowed formula;
give the exact type-probe command and output if one is authorized by the worker's
resource brief. No build is necessary for a prose-only packet. Give all unresolved
decisions in a single review packet and stop before freezing. Target two working days;
≤500 lines of type/review material, no heavyweight numerical computation. The owner
approves the exact command after independent review; C1 then receives a frozen anchor.
No speculative proof-progress claim or axioms claim is appropriate at this stage.

**Repository hard rules, verbatim.**

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

### Second worker brief: C1 — derivative, first exit, and the small instance

**Entry condition.** C0 has passed independent review and the orchestrator has frozen
the owner-approved exact declaration. If that condition is absent, prepare the named
dependency lemmas only; do not freeze, edit the proposed statement, or manufacture a
conditional replacement for the source-facing result.

**Task.** Prove the approved C1 theorem from chain rule, a scalar derivative bound,
first exit, compact continuation, and uniqueness. Proposed ownership:
`KAM/Confinement/{Derivative,Boundary,Periodic,Existence,Uniqueness}.lean`, the
orchestrator-designated provider, and `KAM/Confinement/Examples/ThreeOscillators.lean`.
No other shared file is assigned. Providers cannot import the draft anchor. Ordinary
lemmas live below the provider so consumers need not import a quarantined module.

**Implementation order.** First prove `|F(z(t))−F(z(0))|≤η|t|` only on an interval
where the solution is known to remain in the working closure. Prove positive-time
non-exit from this stopped estimate and the boundary disjunction. Obtain negative
time by reversing the field. Derive continuation through both endpoints; do not
assume it. Extend the periodic geometry to unequal physical/angle dimensions by a
compact fundamental piece, preserving the literal `Fin` carriers. Finish uniqueness
against any local Ω-solution on the common interval. Apply the result to the exact
polynomial (T1), all six coordinate intervals of `Q`, and every point of `S=1/2`.

**Acceptance.** (T3) must state existence, uniqueness, the literal `10⁷` horizon,
`S<1/2`, and the `10⁻⁸|t|` drift, for all points of the positive-volume box.
Prove the exact bracket, the bound `S≤3/16` initially, compactness, and slack `3/20`.
Do not replace the application by a theorem whose premise already states its bracket
bound or its desired trajectory confinement. Do not claim it proves chaos.

Useful boundary tests are: strict margin equality is insufficient for open-domain
confinement; `η=0` needs no division by zero; a constant observable does not separate
a nonempty escape boundary; periodic angle faces are identified, not extra physical
exit walls. These should inform proof review, not a large redundant test suite.

**Resources and handoff.** Expected 1.5–3.5k Lean lines, split before the cap. Run one
`nice -n 5 lake build <Module>` at a time through the compile gate, and stop any new
proof shape that reaches 8 GB RSS or default-heartbeat failure. No heavy v2 kernel
test is part of this task. Run source lint and `#print axioms` from an untracked probe
for the generic result and the toy application; expected admissible axioms are only
`propext`, `Classical.choice`, `Quot.sound`. Report actual output, not the expectation
as a result. Handoff files, proof approach, exact checks, maximum module size,
uncertainties, and every suspected erratum/deviation. The orchestrator handles sealing
and independent review. Target five to ten working days after C0; no subagent launch
is requested by this brief.

**Repository hard rules, verbatim.**

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

### Experiments that decide feasibility early

Every experiment has a hard CPU budget **below one hour**, one computational thread,
and Python RSS below 4 GB. Future Lean experiments target <8 GB per process; none was
run in this planning task. Timeout or memory exhaustion is a reported stop, not a
reason to raise a limit. Do not start a full 5-Gyr ensemble to answer these questions.

| Experiment | Budget | Output and decision |
|---|---:|---|
| E0: exact Table II nullspace and breaking modes | 5 CPU min; completed as part of the 0.053 s algebra calculation | Rank 6, unit minor and two null vectors; rank 8 after the two selected weaker modes. Ready for independent Lean replay |
| E1: exact polynomial benchmark and margin arithmetic | 5 CPU min; completed in the same calculation | 13 terms; bracket `−p₁/10⁸`; horizon `10⁷`, positive slack `3/20`. Ready for C1, without a numerical trajectory |
| E2: raw versus corrected observable derivative | 45 CPU min, after a complete model table is available | On one agreed region, compute coefficient majorants for all three raw quantities, then one finite correction retaining the strong modes. Report all tail costs separately. Stop a 5-Gyr branch if even the available lower estimate of unavoidable derivative error exceeds its margin/time budget; an oversized upper bound only rejects that certificate method |
| E3: geometry before high-order normal forms | 30 CPU min | LP bounds for the linear surrogates, then interval tests of nonlinear `E₆` on physical exit faces. A boundary point with all observables inside the allowed ranges refutes that proposed separation certificate, even at `η=0`. It does not prove dynamical escape |
| E4: one realistic arithmetic shard | 40 CPU min, future authorized Lean run | 128–512 terms at 128–256-bit dyadic precision; record input/output support, live products, kernel/elaboration CPU separately, peak RSS and object size. Stop at 8 GB. Reject extrapolation if the next doubling is superlinear without a proposed repair |
| E5: a low-order tail computation | 50 CPU min | On LG00 or a small extracted model, compare orders 2,4,6 with finite divisor lower bounds and analytic tail majorants. Keep an order only if the full derivative bound decreases and chart margins survive |
| E6: fixed-region lifetime/cover scout | 50 CPU min | Use at most 32 candidate initial cells and five horizons (1,10,100,1000,5000 Myr); print certified or unverified status for each ingredient. A grid search chooses candidates, never proves cover or derivative bounds |

For E2 a sampled lower derivative value, with a rigorous point enclosure, can refute
a proposed uniform upper bound. A large termwise majorant cannot prove no better
observable or cancellation estimate exists. Preserve that distinction in go/no-go reports.

The first checker fixtures should exercise real failure modes: add a symmetry-breaking
term and keep the old `η`; omit a boundary leaf; omit the forcing derivative in (C2a);
set the margin exactly to zero; or double-count a good cell. Each must be rejected.
Accepted fixtures should include the exact-integral case, the genuinely approximate
toy, and a forced example with a nonzero external derivative.

### Cost discipline

The machine kills Lean processes above 10 GB and caps the user at 32 GB. Use 8 GB as
the engineering ceiling, with one targeted build at a time. Python stays below 4 GB
for this program's scouts. Do not rerun `RefinedRefR1` or other heavy v2 tests to obtain
a calibration. New large numerical checks belong in opt-in data targets, as D45 states.

Use outward dyadic arithmetic, balanced traversals, cached finite products and bounded
shards. A tiny residual may require many mantissa bits; that alone is not the main cost.
The number of live terms, expression copying, and repeated kernel reduction can dominate.
Splitting a source file does not split one oversized kernel expression.

If a measured representative leaf costs `c` seconds, an estimate for `N` leaves must
include at least `Nc/3600` CPU-hours plus shared setup, loading, and certificate data
elaboration. A binary partition in sixteen initial coordinates has 65,536 cells:
at 60 s each it already costs about 1,092 CPU-h. Four cells per axis give
4,294,967,296 cells. This rules out a naive tensor grid for a 99% inner-system claim.
Use analytic elimination of angles, adaptive cells, or verified LP witnesses first.
No total runtime for the large inner model is established by this note.

## 8. Dependencies, owner decisions, and timeline

| Workstream | Dependency relationship |
|---|---|
| A | C1/C2 do not need steep or quasi-convex Nekhoroshev. A1 may supply an additional stopped bound or verify a complementary region. General steepness is not a blocker for C |
| B | Share expression semantics, coefficient arithmetic, Lie-tail bounds and canonical transport. B's nonresonant action estimate is a special case of C1. C adds retained-mode annihilators and all-boundary geometry. Direct original-field observables can proceed before B's chart |
| D | D owns the literal planetary model, parameter/initial set policy, and physical safety statement. C supplies confinement and finite good-set accounting. A stopped action output may feed `amdConfinement` only for its exact full planar moving-Sun model |
| v2 | Optional starting torus and arithmetic reuse. C does not need better smallness thresholds unless a selected B/D producer does |
| Hybrid | Optional cheaper torus production and validated Taylor infrastructure; theorem side is present, numerical certificate wiring must be checked separately. No hybrid success supplies a transverse lifetime automatically |
| LG00 | Small exact polynomial benchmark and comparison with two-torus confinement. Coordinate signs and time units are already documented by the scout. Do not replace its exact polynomial by a square-root Taylor surrogate without saying so |
| Full SJS | Later model-fidelity target; its large Fourier campaign is not a prerequisite for C's core. The current first-order secular SJS all-time theorem is not a substitute for a full-flow derivative bound |
| Lunar SO and next demonstrations | Preserve SO's N=65 rotational and approved polar libration routes. No Birkhoff prerequisite is added. Magnetic field-line and Mercury-spin demonstrations have their own value and are not Mercury orbital-safety results |

Decisions for the owner before launching the corresponding packages:

1. **Freeze scope:** approve the C¹ field version of C1 and periodic compactness
   formulation, or pay for the locally Lipschitz-only extension now. Recommendation:
   C¹ first; it covers all planned models.
2. **First substantial numerical instance:** use a CL21 resonant comparison or D's
   selected secular SJSU model before the full inner system. Recommendation: a small
   CL21 comparison for validation, with SJSU as the first planetary lifetime attempt.
3. **Inner-model contract:** exact `H₆` with all specified outer modes and secular
   relativity, versus an explicitly named reduced model. Recommendation: keep `H₆`
   as the ambition and permit a reduced model only as a separately labelled milestone.
4. **Initial region and observable:** an agreed small neighborhood, a source uncertainty
   scale, or a rigorous ephemeris enclosure; `e_M<0.7` versus actual pair-distance safety.
   Recommendation: first a published, fixed small region with explicit eccentricity
   transfer. Require a new gate for observational containment or collision exclusion.
5. **Quantifier:** all points of the chosen small box, or a declared measure fraction
   of a larger one. Recommendation: all points first. Do not commit to 99% until C4
   has a viable cell-count and geometry estimate.
6. **Compute allocation:** 100 CPU-h pilot, rising to 1,000 only after a representative
   measured shard and full error budget. Recommendation: those two staged allocations;
   a cluster or >8 GB process is a separate decision with concrete data needs.

These choices do not block completion of this planning document. They are the decisions
needed before the corresponding implementation or physical claim is authorized.

**Calendar estimate, conditional on source/data access and prompt statement review.**
Week 1: C0 plus E0/E1 independent replay, source-table availability and E3 geometry
scout. Weeks 2–3: C1 and the handwritten toy. Weeks 3–6: C2 and a small C3 adapter,
with E4/E5 measurements. Weeks 6–10: a first source-model `T(r)` curve and finite cover
prototype. Weeks 10–14: an independently reviewed modest planetary instance if the
earlier numerical gates close. An inner `H₆` 5-Gyr good-set result is a several-month
research attempt with no justified completion date; unsuccessful geometry or tails
can stop that branch while leaving the reusable library complete.

This schedule assumes access to proof writers and an independent auditor through the
project's existing campaign policy, but does not launch or request any agents here.
All Lean builds remain serialized. Calendar estimates are not cumulative kernel CPU
estimates, and neither is a promise that the desired planetary time will be attained.

## 9. Uncertainties, source issues, and deliberate deviations

**Candidate E-C-CL21-1: slow-frequency order.** CL21 arXiv:2102.05959v1, printed/PDF
p. 23, immediately after (47), states “ν₂ = O(μ) for μ → 0”. The same displayed
equation gives

\[
 \nu_2=-\sqrt{\frac{1-\sqrt{1-27\mu+27\mu^2}}2},\qquad
 \frac{\nu_2^2}{\mu}
   =\frac{27(1-\mu)}{2(1+\sqrt{1-27\mu+27\mu^2})}\longrightarrow\frac{27}{4}.
\]

Thus `ν₂/√μ→−√27/2` as `μ→0+`; the order is `√μ`, not `μ`. The text was checked
against the rendered PDF, saved as `/tmp/prog-c-astra/cl21-page23.png`. This is a
specific source-error candidate for independent verification and the orchestrator's
errata ledger. It does not by itself invalidate computations using the exact (47).
Do not import the incorrect asymptotic assertion into a Lean statement.

**Candidate E-C-CL21-2: time-unit ambiguity, unresolved.** CL21 p. 24, §5.2.1, describes
`T_e.l.t.=(6 Gyr)ν₁/(2π)` as “in number of Jupiter revolutions”. But the normalized
rotating Hamiltonian on p. 22 and its frequencies (47) use angular frequencies, with
`ν₁→1`. A lifetime computed from Hamilton's equations in that normalized time needs
an explicit conversion to revolution counts before this comparison. The inspected
text does not establish whether such a conversion was applied to the table's `T`.
This is a suspected unit mismatch to resolve from the numerical normalization, not
a confirmed factor error in the tables. Keep the rank-4 pilot in declared dynamical
units until the factor is checked; do not inherit its age-in-years interpretation.

No suspected defect in an existing frozen declaration was found. MHL23's coordinate/
truncation identifications and filtered diagnostics are disclosed modelling choices,
not alleged misprints. The strict distinction between those diagnostics and a uniform
theorem is our responsibility. Neither candidate above is written into the central
ledger by this worker; both are included here for the orchestrator, as AGENTS.md requires.

GLS17 p. 25, immediately after (58), says it has “kept just the first term” of a
remainder series. This is a disclosed estimate, not a certified tail inequality.
Its displayed time therefore cannot be imported as a rigorous lower bound without
controlling the omitted sum. Record that limitation in the implementation source
packet; it is not a newly asserted erratum. Existing project errata have not been
independently re-audited here.

Deliberate proposed deviations are: C¹ fields for the initial C1 freeze; a general
periodic first-exit theorem with explicit existence and uniqueness; period-one and
maximum-norm conventions; finite certificates and exact boundary coverage; and the
original toy (T1). Directly certified approximate observables may differ from MHL's
displayed quantities after correction, and must receive distinct names with the
correction and its original-field residual explicit. Do not claim source identity
until it is proved.

The [Guzzo–Caracciolo–Pinzari 2026 preprint](https://arxiv.org/pdf/2601.18268v1),
Theorems 2.1–2.3 and its introduction, may improve nonresonant remainder estimates.
Its general resonant extension is left open. It is not a ready-made theorem to plug
into C for the inner-planet resonance web.

The strongest unknowns are the full forced-model coefficient provenance, uniform
tails, whether the selected approximate integrals separate a scientifically useful
boundary, and whether the eventual good-set cover is affordable. A literature check
of the primary sources above and targeted arXiv/APS searches found no uniform
5-Gyr certification of the observed inner Solar System. This is a scoped finding,
not a universal absence or priority claim. A first-in-Lean or first-rigorous numerical
claim needs a new literature check when an actual instance is ready.

## 10. Pinned evidence and validation receipt

PDFs were copied as data from the existing ambition research scratch into
`/tmp/prog-c-astra/papers/`; their bytes were hashed anew. Public versioned records
were checked online. No downloaded code was executed and no GitHub operation was
performed. The source index is `/tmp/prog-c-astra/papers/sources.json`.

| Key and exact version | Locators used | SHA-256 of PDF |
|---|---|---|
| [MHL23, 2305.01683v1](https://arxiv.org/pdf/2305.01683v1) | §II (1)–(6), Table I; p. 5 Table II; §IV (11)–(25), Table III; §VI (32); Appendix B (B2) | `c44419c0dfefba8492af1f648753d0ddd90313b64acffd31e56f8549a460d1c7` |
| [ML21, 2105.14976v1](https://arxiv.org/pdf/2105.14976v1) | §§2–4 forced secular construction, §§6–8 numerical validation, Appendix C LG09 statistics | `7537e3b2536766d18fcf5db1844e9586eefba46318645373ee0ed532f9c32526` |
| [HML22, 2205.04170v1](https://arxiv.org/pdf/2205.04170v1) | §2 model conventions; §4.1 and Table 1 degree sensitivity | `66a18c8fe1c24419172b163bf51170735d6016d7917133191a46a48c85038bc4` |
| [GLS17, 1702.04894v1](https://arxiv.org/pdf/1702.04894v1) | §2.2 expansion count; §4.3 (56)–(61), pp. 24–27 and Fig. 2 | `254d52fb9c545efe12cfcc4b138ac8b429c1e95aad0d63c12b4e6dfc182e1cae` |
| [CL21, 2102.05959v1](https://arxiv.org/pdf/2102.05959v1) | §3, especially (22), (29); §4.1 (32)–(37); §4.2 (39)–(44); §5 and Appendix B for pilot selection | `fe288ead9f2d02c3527875154bb1f21195eba0fac1f19bfaf55e6e0e596410e8` |
| [FH25, 2403.10152v1](https://arxiv.org/pdf/2403.10152v1) | §4 model/candidate, numerical computation and memory discussion | `379c8b41b53a1fd50cbc890cca06d646ccd93f5c0d5e0226d1303885d2df7cf7` |
| [GCP26, 2601.18268v1](https://arxiv.org/pdf/2601.18268v1) | Introduction's resonant-extension limitation; Theorems 2.1–2.3 | `51e8791b29031969edc05afaf6d7a478fdb2298a7f60752b7544c172a65e4c5d` |

LG00 data and theorem locators in this plan come from the repository's
[source transcription and scout](sjs-lg00-scout.md), especially its §§1–2 and 7,
not a new full-paper audit here. The model has 69 nonzero printed monomials; 129 is
the larger index range. The SJS/LG00 cost projections retain their original uncertainty
and are superseded where their claims about missing v2, hybrid theorems, or `sqrt`
conflict with the inspected checkout.

**Files and checks.** The sole repository deliverable is this document. Scratch,
source copies, the independent-of-Lean algebra script, and check logs are under
`/tmp/prog-c-astra/`. No Lean source, frozen file, manifest, generated root, or README
was edited. No build, Lean probe, or `#print axioms` was run. Axioms of new results:
not applicable; this change introduces no Lean declaration. Existing-results axiom
status was not rechecked.

The command `scripts/lint_sources.sh` was run with a scratch `python3` wrapper that
adds `-B` and rejects only `scripts/abi_hashes.py`. That subprocess writes
`.lake/abi-scratch` and invokes Lean on all frozen imports, contrary to this brief's
scratch restriction and tiny-probe limit. The wrapper is not a repository change.
Exact output:

```text
check_lean_modules: PASS (1829 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI SKIPPED: PROGRAM-C forbids builds and repository scratch; the ABI probe is not the permitted tiny Lean probe.
lint exit: 1
```

All other lint phases completed without diagnostics. This is a **partial lint run**,
not a full lint pass. The implementation briefs retain the full targeted-build,
lint, axiom, and independent-review requirements for later Lean work.

Additional checks and their output:

- `python3 -B /tmp/prog-c-astra/scout.py`: exit 0; rank 6, the two exact
  annihilators verified, determinant 1, added-resonance ranks 7 and 8, and the
  exact toy bracket and slack reported in §§3 and 6.
- `python3 -B /tmp/prog-c-astra/check_doc.py`: exit 0; 26 local links, zero broken
  links, two verbatim hard-rule copies, balanced code/math delimiters, no
  placeholders, and no trailing whitespace.
- The separate symbolic cross-check reported: `PASS: printed minor; unbounded
  zero-energy ray; slow-frequency squared ratio; toy slack; 5-Gyr derivative budget.`
- `git diff --cached --check`: exit 0, no output.

Scripts and logs are in `/tmp/prog-c-astra/`. The final commit contains only this
planning document.
