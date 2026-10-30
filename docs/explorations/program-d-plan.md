# Program D: a checked planetary lifetime with a named model

Planning report, 30 October 2026. Inspected checkout: `prog-d`,
`fb782d6947546b4a5121a509a76844e325f54987`. This is a proposal, not an approved
Lean surface, a numerical certificate, or a proof-status audit. Only this document
is changed. Research and arithmetic receipts are in `/tmp/prog-d-astra/`.

**Recommendation:** pursue a five-billion-year **secular action-confinement**
certificate for a precisely specified planar Sun–Jupiter–Saturn–Uranus (SJSU)
model. Use Program B's finite normal-form checker and Program C's boundary method
where needed. In parallel in the work plan, give D1 a bounded task: make the
existing partial-convex planetary theorem executable and publish its actual
mass/time/region tradeoff. Do not make a realistic full-model lifetime depend on
the raw asymptotic constants becoming sharp enough.

Three findings determine the plan.

1. **The literal existing stopped estimate fails a concrete realistic-mass test
   before any analytic constants are computed.** For the admissible SJS-like box
   in §4, AMD permits action drift less than `1/2000`, whereas the existing
   `Stopped.stopped` route at the cited mass requires drift at least `0.260512`.
   That route needs a mass below `10^-32` for this box. This is a rejection of a
   sufficient formula, not evidence that the planets are unstable. The internal
   block estimate is sharper and deserves its own numerical test.
2. **A long secular safety theorem alone may be too weak a flagship.** An AMD
   calculation from the SJSU source's nominal elements already suggests generous
   all-time non-crossing margins in a rotation-invariant secular model. The new
   result should bound individual normal-form actions over 5 Gyr, with a chart
   back to eccentricities. It must demonstrate more than conservation of total AMD.
3. **SJSU has two effective secular degrees of freedom on a regular fixed-AMD
   reduced leaf.** It is a serious numerical verification target, but does not
   establish a transport theorem beyond the dimension in which torus barriers
   can work. A four-giant planar secular model, or full reduced planar SJS, is the
   next target if at least three effective degrees of freedom is essential.

The answer for the observed inner Solar System is **not yet**. A specified forced
secular resonance model and selected good regions are plausible research targets;
a uniform 5-Gyr theorem for the complete observed uncertainty region is neither
supported by this plan nor consistent with the numerical motivation for it.

## 1. What can be reused, and what cannot

The manifest contains 157 `SEALED` entries and one `DRAFT_SORRY` entry: 134 sealed
definitions, 23 sealed theorems, and the W theorem draft. These are inspected
manifest states, not a fresh build or `#print axioms` receipt. Historical Phase 0
labels in PLAN/TRACKS do not override the current sources.

| Component inspected | Reuse in D | Remaining obligation |
|---|---|---|
| [N partial-convex anchor](../../KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean) | Stopped fast-action control, `n ≥ 2`, `k ≥ 1`, convex or concave fast part | Replace existential smallness by checked numerical inequalities, below the frozen anchor |
| [Partial constants](../../KAM/Nekhoroshev/Partial/Constants.lean), [explicit threshold](../../KAM/Nekhoroshev/Partial/ThresholdExplicit.lean), [block](../../KAM/Nekhoroshev/Partial/Block.lean) | Explicit formulas and stronger block drift/time | `thrMuA`–`thrMuE` are explicit; the final `μf` still comes from an eventual-limit argument. Evaluate the required inequalities directly |
| [Planetary stopped assembly](../../KAM/Planetary/Exponential/Stopped.lean) | Chart lifting, reverse time, fast and slow erosions | Effective complex tube and perturbation bound; no numerical `B0` or threshold follows merely from compactness |
| [KeplerData](../../KAM/Planetary/Exponential/KeplerData.lean), [Perturbation](../../KAM/Planetary/Exponential/Perturbation.lean) | Literal Kepler derivatives and analytic identification of the full perturbation | Construct numerical lower/upper bounds and complex branch margins |
| [AMD confinement](../../KAM/Frozen/Planetary/Theorems/AmdConfinement.lean), [exponential safety](../../KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean) | Existence, uniqueness, Newtonian reconstruction, eccentricity and distance bounds | Discharge `StoppedActionBound` from the specified Hamiltonian; it is never a final application hypothesis |
| [Secular cited-mass theorem](../../KAM/Frozen/Planetary/Theorems/SecularBoxAtCitedMasses.lean) | Existing all-time first-order averaged SJS result | It already has literal masses, `e < 0.15`, and separation `399/200`. A 5-Gyr restatement of it adds nothing |
| [Quasi-convex constants](../../KAM/Nekhoroshev/Interfaces/Constants.lean) | Share arithmetic enclosure machinery with A1 | The full Kepler Hamiltonian is degenerate in the slow variables; the quasi-convex theorem cannot simply be applied to it |
| [v2 route selection](../../KAM/CertificateSharp/V2/RouteAll.lean), [soundness interface](../../KAM/CertificateSharp/V2/Engine.lean) | Routes A/B, refined bounds, frequency-specific constants, old sharp route | `routeV2All` checks the supplied route witness; it does not search. A torus does not give a canonical neighborhood or a lifetime |
| [Hybrid G1](../../KAM/Sharp2/Hybrid/G1.lean), [iso hybrid](../../KAM/Iso/Sharp2/Hybrid/G1.lean) | The first-step/restart theorems are implemented in this checkout | No hybrid certificate engine appears in this checkout. The [design](../campaign/design/APOST-SHARP-V2-HYBRID.md) numerical gains are sampled R1 experiments, not planetary kernel receipts |

The older [ambition note](ambition.md) calls hybrid only a design. Its theorem-side
status is now stale. Conversely, the implementation of the theorem does not turn
the design's timings into a checked application. The `sqrt` expression already
exists; the old LG00 “missing sqrt” task is also stale.

### Primary sources and exact roles

Page numbers below refer to the pinned preprints unless stated otherwise. New
paper pins are research evidence here; an orchestrator must register them before
a source-facing freeze. No source registry or frozen file is edited by this task.

| Source | Locator and role |
|---|---|
| [Nek77](https://doi.org/10.1070/RM1977v032n06ABEH003859) | English pp. 30, Thm 4.4 and Remarks 4.5.A–B; pp. 55–56, Thm 12.3. Existing convex specialization and planar specialization, with the repository's adopted deviations. The local PDF is absent in this worktree; these locators and its hash are inherited from the frozen anchors/registry, not newly verified |
| [Laskar–Petit 2017](https://arxiv.org/abs/1703.07125v2) | Eqs. (5)–(11), §3, Appendix B, especially (B.5), (B.8): heliocentric Hamiltonian, AMD, secular invariance and crossing criterion. Use the simpler frozen radial-separation criterion first |
| [GLS17](https://arxiv.org/abs/1702.04894v1) | §2, (1)–(12), Tables 1–2: model and units; §3, (21), (35)–(37): torus coordinates; §4, (46)–(60): norm recursion and lifetime estimate. Source for D2's construction, not a theorem to import without new remainder work |
| [Migaszewski–Goździewski 2008](https://arxiv.org/abs/0803.3246v1) | §3, (43): reduction by the cyclic common perihelion angle. Verify the same symmetry for the selected polynomial, rather than assume a truncation preserves it |
| [LG00](https://doi.org/10.1023/A:1011139523256) | Theorem 1; (11), Appendix A; §4.3, (51)–(52): rigorous truncated secular SJS benchmark and two confining tori. DOI checked against the [author's institutional record](https://art.torvergata.it/handle/2108/52180) |
| [Barbieri–Niederman](https://arxiv.org/abs/1810.05987v1) | §5.1, Tables 1–3, pp. 40–41: quantitative full-planar, near-5:2, reduced-mass comparison. These are not bounds for today's masses |
| [Figueras–Haro](https://arxiv.org/abs/2403.10152v1) | §2, §4 and Appendix A: full planar SJS reduced Hamiltonian and numerical torus. Basis for a later full-model local route |
| [ML21](https://arxiv.org/abs/2105.14976v1) | §§2, 6–8 and Appendix C: forced inner secular model, chaos, high-eccentricity statistics and the LG09 ensemble |
| [HML22](https://arxiv.org/abs/2205.04170v1), [MHL23](https://arxiv.org/abs/2305.01683v1) | HML22 §§3–4: degree-six interactions matter for rare excursions; MHL23 resonance/symmetry analysis: candidate quasi-integrals for C, not certified invariant barriers |

The [LG09 Nature result](https://doi.org/10.1038/nature08096) is numerical context.
Its full text was not independently obtained here; ensemble qualifications were
checked in the authors' ML21 Appendix C. No universal novelty claim is made.

## 2. Exact mathematical targets and a small frozen surface

### Conventions shared by the targets

Use `Vec n = Fin n → ℝ`, complex vectors `Fin n → ℂ`, Fourier indices
`Fin n → ℤ`, and `Phase n = Vec n × Vec n`. Vector norms are max norms;
`sqrt (∑ i, v i ^ 2)` is an explicitly defined scalar when a Euclidean estimate
is needed. `Phase (n*2)` is planar heliocentric position/momentum space for `n`
planets. It has real dimension `4*n`, not `2*n`.

In the canonical convention, `X_H(q,p) = (∂p H, -∂q H)` and
`dF(X_H) = {F,H}`. An interval solution means `HasDerivAt z (X_H (z t)) t`
at every `t ∈ Icc (-T) T`, with an exhibited trajectory on that interval.
Write the uniqueness clause as agreement with every other local solution through
the initial point on its common interval. Do **not** use `∃! z : ℝ → Phase n`
when the ODE is required only on `[-T,T]`: values outside the interval are arbitrary.

Period-one KAM angles and radian planetary angles are different interfaces.
The canonical conversion of a radian pair `(q,p)` is
`θ=q/(2π), J=2π p`, with Hamiltonian `H(2πθ,J/(2π))` and unchanged time.
Thus source action radii and derivative bounds both acquire a factor `2π`.
Never divide the angle alone and still claim the same canonical vector field.

A physical time scale is part of the model. If length unit is `L0` and
gravitational parameter is `GM0`, the `G=m0=1` time unit is
`t0 = sqrt(L0^3/GM0)`. Check `Tyear/t0 ≤ Tmodel` using outward intervals.
For the *chosen conventional model* `GM0=4π² AU³/yr²`, this is
`Tmodel=2π Tyear`. This equality is not a measurement of the Sun's GM.
GLS17 uses AU, years, `G=1`, `m0=(2π)²`; its displayed time already is in years.

### D1: a checked full-planar lifetime at a supplied positive mass

Keep the existing literal Hamiltonian
`Hμ = movingHamiltonian 1 1 B.mass μ`. In coordinates it is

\[
 H_\mu(q,p)=\sum_i\left[\tfrac12(1/m_i+\mu)|p_i|_2^2-
                 m_i/|q_i|_2\right]
 +\mu\sum_{i<j}\left[p_i\cdot p_j-m_i m_j/|q_i-q_j|_2\right].
\]

The indirect kinetic terms, including the diagonal term, are included. The Sun
moves after barycentric reconstruction. Frozen osculating elements are canonical
heliocentric elements; equality with an observational element convention is a
separate coordinate calculation.

**Proposed public theorem D1-SOUND.** For every `n ≥ 2`, rational box data `Bq`
interpreted as the existing `AMDBox n`, positive rational `μ,T,δ`, and finite
certificate `c`,

\[
 \operatorname{checkPlanarLifetime}(B_q,\mu,T,\delta,c)=\mathrm{true}
 \Longrightarrow
 \forall z_0\in\operatorname{LowAMDRegion}
       (m,L^{\rm in},U^{\rm in},C_{\rm in}),\ \exists z,\quad \mathcal S(z,z_0).
\]

Here the conclusion `𝒮` is to be written out in the final Lean command, with:

- `z 0 = z0`, `IsMovingSolutionOn m μ (Icc (-T) T) z`, and `MovingUniqueOn`;
- `IsNewtonSolutionOn (actualMasses 1 m μ)` for the frozen barycentric positions
  and velocities on that same interval;
- for every `|t| ≤ T`, membership in the outer low-AMD region, conserved total
  angular momentum, `physicalAMD m (z t) ≤ C_in+nδ`, and
  `|keplerAction m (z t) i - keplerAction m z0 i| ≤ δ` for every planet;
- `e_i(t) < B.ecc`, heliocentric radii between `B.distance` and `B.radius`, and
  `PairBounds B.distance (2*B.radius)` for all bodies, including the Sun.

The checker verifies `B.Admissible`, positivity, and exactly the existing margins

\[
 L_i+2\delta<L_i^{\rm in},\qquad
 U_i^{\rm in}+2\delta<U_i,\qquad C_{\rm in}+2n\delta<C_{\rm out}.
\tag{D1.1}
\]

`c` is finite numerical/algebraic data, with no fields of type `Prop`, no
trajectory, and no field asserting a stopped bound. It contains rational domain
widths, complex Kepler inversion and square-root witnesses, outward coefficient
or expression enclosures, a normalization `B0`, and arithmetic witnesses for the
comparisons below. Every accepted analytic claim follows from a proved checker
lemma. Unsupported expressions or inconclusive comparisons return false.

The final application theorem for one selected box and mass will have **only**
initial membership as its premise; its provider proves that the literal data
passes. Checking advice is a valid premise of the reusable soundness theorem,
but it is not an application result until that check is proved in the kernel.

**D1's numerical gate.** Choose `κ, A_s, ρ > 0` and enlarged eccentricity `e'`
meeting `EnlargedData`, `ρ ≤ κ`. Set

\[
 G=\prod_i(L_i-\kappa,U_i+\kappa),\quad
 G'=\prod_i(L_i-2\kappa,U_i+2\kappa),\quad
 D=\{(x,y):\tfrac12\sum_i(x_i^2+y_i^2)<A_s\}.
\]

Prove on the frozen partial complex domain that
`Hμ ∘ poincareProd = h + ν P`, with
`h(I)=-∑ m_i³/(2I_i²)`, `ν=B0 μ`, `B0 ≥ 1`, and
`IsPartialPerturbation G' D ρ P`. This includes holomorphy, reality, fast-angle
periodicity and `‖P‖ ≤ 1`; the real identity must be differentiated on an open set.
Use the sign `-1` for the concave Kepler part and `+1` for its negative.

If `ℓ_i=L_i-3κ>0`, `u_i=U_i+3κ`, sufficient explicit Kepler constants are

\[
 0<g\le\min_i m_i^3/u_i^3,\quad
 0<m_f\le\min_i 3m_i^3/u_i^4,\quad
 M_c\ge\sum_i 3m_i^3/\ell_i^4.
\tag{D1.2}
\]

They are independent of `μ`, perturbations, or initial points when evaluating a
mass family. The curried Hessian operator norm uses the sum, not an unjustified
max of diagonal entries. Positive rational bounds can avoid computing minima
inside Lean.

For `cN=(n,ρ,g,m_f,M_c)`, use **the exact definitions** in `PartialConstants`:

\[
\begin{gathered}
 a=2/(6n^2-3n+14),\quad b=3a/2,\quad s=\rho/(4\pi),\quad
 r_0=\min(\rho/2,32g/m_f),\quad A_N=40M_c/m_f,\\
 \epsilon_0=(m_f/(2\pi))r_0^2/(2^{14}A_N^{2n}),\quad
 \kappa_C=\coth(\pi s)^n,\quad \epsilon=\kappa_C\nu/(2\pi),\\
 K=(\epsilon_0/\epsilon)^{1/(2n)},\quad R_0=r_0/A_N,\quad d=\nu^b,\quad
 \chi=2\pi Ks/\sqrt n,\\
 r_\theta=r_0/(A_NK)^n,\qquad
 T_b=\frac{s m_f r_\theta}{240 M_c\epsilon}\exp(\chi/6).
\end{gathered}
\tag{D1.3}
\]

The useful internal lemma is the **finite-inequality version of the existing
block assembly**, with tests

\[
 \epsilon\le\epsilon_0,\quad d\le\rho,\quad 6\le\chi,\quad
 256n\rho R_0/d^2\le K,\quad
 T\le T_b,\quad R_0/(2K)\le\delta,
\tag{D1.4}
\]

and strict erosions

\[
 d<\kappa,\qquad \sqrt{2C_{\rm out}}+\sqrt{2n}\,d<\sqrt{2A_s}.
\tag{D1.5}
\]

Apply the block theorem in both time directions on arbitrary stopped segments,
using the existing field conversion and lift, then apply `amdConfinement`.
`StoppedActionBound` is an internal **output** of that proof. Do not import a
provider: reproduce/extract the necessary assembly into an ordinary module using
`Partial.Block`, `Partial.Domain` and the sealed definitions. The frozen
existential theorem and its provider remain unchanged.

This keeps the stronger block drift `R0/(2K)` and requested block time `T`.
The conservative compatibility route instead also checks
`R0/(2K) ≤ ν^b/2 ≤ δ` and
`T ≤ ν^-1 exp(ν^-a) ≤ T_b`; that is the route rejected by §4's simple box test.
Neither route is a proved new API in this report. The block route still pays
the very restrictive `d=ν^b` slow collar and its numerical smallness conditions.
Freeing the slow collar from this asymptotic power requires a separately audited
internal generalization; no claim of a `1/(2n)` **planetary headline exponent**
follows from the exponent appearing in `K` or `T_b`.

For arithmetic, bound logarithms of positive time expressions and use rational
root inequalities after checking signs; never materialize an astronomical
exponential. For example,
`log T ≤ log(s*m_f*rθ/(240*M_c*ε))+χ/6` is sufficient. Bounds for subtraction,
division, `coth`, logs and roots must be outward. A positive `μf` obtained by
`Classical.choose` from a limit theorem is not numerical data.

**Complex-domain obligations.** Real radial separation does not establish a
complex tube. The checker must bound the complex Kepler inversion derivative,
choose square-root branches consistently, and exclude zeros of the complex
bilinear squared distances. A usable sufficient witness is a disk about a
positive real squared distance with relative radius strictly below one. Bound
the variation throughout the disk, not just at a real grid. These are D1's main
analytic tasks, and likely its largest loss in practical constants.

### D2: tight secular drift for an explicit SJSU region

**Model choice.** Start with the degree-18, planar secular construction described
by GLS17 (12), with its specified treatment of the 5:2, 7:1 and three-body
quasi-resonant contributions. Pin the exact generating recipe, truncation
orders, averaged reference actions `Λ*`, masses, coordinate signs and units.
The paper prints only a small part of the coefficient information; its nominal
Table 1 axes are not automatically the averaged `Λ*` of §2.1.

Use a deterministic finite-expression specification of each coefficient,
evaluated with certified enclosures. If the recovered source instead supplies
only decimal coefficient tables, there are two legitimate choices: prove
enclosures for the intended coefficients, or openly select the exact rational
polynomial as a new mathematical model. A rational midpoint without a coefficient
error bound does not reproduce the original model. Package D-P0 decides this
before any theorem is frozen. Failure to recover the data is a real stop, not
permission to call an invented polynomial “GLS17”.

Write the selected secular Hamiltonian in Cartesian canonical variables as

\[
 H_{\rm sec}(x,y)=\sum_{(\alpha,\beta)\in S}c_{\alpha\beta}
                  x^\alpha y^\beta,\quad
 S\subset(\mathrm{Fin}\ 3\to\mathbb N)^2,
 \quad 2\le|\alpha|+|\beta|\le18,\quad |\alpha|+|\beta|\text{ even}.
\tag{D2.1}
\]

Here `(x,y)` follows the source's momentum/coordinate ordering: in the repository
`Phase 3` convention evaluate this polynomial at `x=z.2`, `y=z.1`.
Attach `(ξ,η)` to `(p,q)` in the same order before the normal-mode map. Prove
that attachment from the Poincaré formulas; copying a polynomial into
`(q,p)=(x,y)` would reverse its Hamiltonian flow. The sign check belongs to D-P3.

The **full** selected polynomial is the ODE model. Its higher-degree terms may
be bounded in a remainder but cannot be discarded from the theorem. Certifying
an untruncated secular average would additionally require bounds on the
degree-20-and-higher tail. Transfer from the secular construction to the full
Newtonian system is a different result still.

**Exact generic instance shape.** Let `Ψ` be a canonical analytic diffeomorphism
from a neighborhood of `T³ × [-R,R]³` into the regular domain of (D2.1), with a
certified inverse on its image. Let `r,R,T > 0`, `r<R`, `η≥0`, and in source radian
coordinates let

\[
 H_{\rm sec}\circ\Psi(q,p)=Z(p)+\mathcal R(q,p),\qquad
 \sup_{q\in\mathbb T^3,\ |p|_\infty\le R}
       |\partial_q\mathcal R(q,p)|_\infty\le\eta,\qquad
 \eta T<R-r.
\tag{D2.2}
\]

All the displayed premises are **checker outputs**, established by B's finite
Lie-flow/tail machinery on the actual polynomial and by D's chart adapter.
For every `z0 ∈ Q := Ψ(T³ × [-r,r]³)`, conclude existence and local uniqueness
for the exact `Hsec` trajectory through `z0` on `[-T,T]`, with

\[
 p(t)=\pi_p\Psi^{-1}(z(t)),\quad
 |p(t)-p(0)|_\infty\le\eta|t|,\quad |p(t)|_\infty<R.
\tag{D2.3}
\]

The image is understood on the angle quotient; chart injectivity is modulo the
angle lattice, not injectivity of a periodic map on all of `ℝ³`. Positive
canonical volume of `Q` is `(2π)^3(2r)^3` in radian coordinates. Fixing one AMD
leaf would give a conditional measure statement instead; we retain an interval
of AMD values in the first all-data target. The chart's compact image inside the
regular domain supplies continuation. An existence theorem that assumes a
solution lasting for `T` does not meet D2.

**Proposed numerical target for owner selection, not a successful instance:**

- `T = 5,000,000,000 yr`, `r = 1/10^7` in **GLS source action units**, with
  `R = 2/10^7`. Fix these minimum/maximum radii before optimizing the checker.
- Aim for `η ≤ 10^-17` action units/year, leaving half of `R-r` unused.
  Conclude action drift at most `5·10^-8`, and expose a more readable upper
  bound `10^-7` if desired. These are transformed actions, not eccentricities.
- Require the validated inverse chart to contain a specified nominal source
  point and a nonempty neighborhood of it. A torus merely close to a numerical
  point is insufficient. No observational uncertainty-set claim is included.
- Proposed additional physical outputs: `e_J,e_S < 3/20`, `e_U < 1/4` and
  at least 1 AU between the radial annuli of each adjacent pair, uniformly in
  **all** reconstructed fast phases. Publish sharper bounds if the checker
  proves them. These thresholds are acceptance proposals, not extracted results.

The published source estimates roughly `10^10 yr` near an action radius slightly
below `10^-7`, versus an approximate uncertainty radius `7·10^-7`; it explicitly
does not give a rigorous computer-assisted proof. Its intermediate expansion has
94,109,751 monomials. Those facts motivate a scout, not a promise that the chosen
`r=10^-7` will pass. [GLS17, pp. 6, 10, 26–27](https://arxiv.org/abs/1702.04894v1).

The eccentricity map must be explicit. In the selected secular Poincaré chart,
`Γ_i=(ξ_i²+η_i²)/2`,
`e_i²=2Γ_i/Λ_i-(Γ_i/Λ_i)²`, with `0≤Γ_i<Λ_i`. Certify every intermediate
map between `(x,y)` and `(ξ,η)`, including the averaging conventions. Radial
separation follows from `a_i(1±e_i)` after these identifications. Reconstructed
ellipses of a secular orbit are geometric predictions of that model; they are
not full Newtonian trajectories.

Also report drift in the original modal actions
`J_j(x,y)=(x_j²+y_j²)/2`. If the chart checker proves
`sup |J∘Ψ-(I*+p)|∞≤dchart`, then (D2.3) gives
`|J(z(t))-J(z0)|∞≤2*dchart+η*|t|`. Compare this explicit bound with what AMD
alone permits. A tiny transformed-action bound with an uncontrolled chart error
does not establish tight control of the source's physical observables.

**Remainder accounting.** The chart starts with an exact polar map into the
source's modal Cartesian variables,
`Ψ0(q,p)=((sqrt(2*(I*_j+p_j))*sin q_j)_j,
          (sqrt(2*(I*_j+p_j))*cos q_j)_j)` in repository `(qcart,pcart)` order.
Require `I*_j>R+σ` on the larger domain used for tail bounds. Compose this with
the certified linear symplectic maps and finite time-one Hamiltonian flows
needed by the chosen normalization (or a separately proved exact generating-map
construction). Verify the order and domains of these maps against the source.
A truncated substitution is not automatically symplectic.
The checked derivative budget is

\[
 \eta=\eta_{\rm low\ order}+\eta_{\rm omitted\ terms}
       +\eta_{\rm Lie\ tails}+\eta_{\rm coefficient\ enclosure}
       +\eta_{\rm rounding}.
\tag{D2.4}
\]

Each term is in the same chart, norm, action units and time units. The first term
includes every residual constant/linear-in-action angular term of a finitely
normalized approximate torus. Its size cannot be suppressed by assuming the
torus is exact. An exact v2 torus is optional for a finite-time result and useful
for an asymptotic near-torus theorem. It still does not supply a transverse
canonical chart by itself.

An inexpensive first bound can use only majorants for high orders, retaining
explicit low orders. At a larger radius `R+σ`, a rigorous sup tail bound `E`
gives derivative bounds through Cauchy with the appropriate angle loss. On a
real Fourier polynomial, sum `|k_j c_{α,k}| R^|α|` in radians, or
`2π|k_j c_{α,k}| R^|α|` in period-one angles. The tail must be bounded by an
actual convergent majorant; “the first omitted term dominates” is not a proof.

### D3: transfer to a fuller Hamiltonian

For `Hfull ∘ Φ = Hsec + Rfast` on a specified fast-angle/slow-variable domain,
accept a full-model certificate only after adding bounds on
`{F_j,Rfast}` to each confinement budget and proving the domain and inverse
chart conditions for `Φ`. `Rfast` includes fast-action dependence, every
discarded averaging term and all parameter errors. An `O(μ²)` label or phase
agreement over a short integration is not a 5-Gyr error bound.

For full planar SJS at `μ=4773/5000000`, the preferred later route is a local
finite normal form about a numerical FH25 candidate, with AMD/physical
reconstruction from P. Target a specified positive-volume tube and explicit
time-versus-radius curve first. No specific full-model 5-Gyr radius can be
responsibly supplied from the present data. Full SJS has three effective degrees
of freedom after angular-momentum reduction; neighboring 3-tori do not bound a
five-dimensional energy surface.

For a forced inner secular model, use the vector field on physical variables
and the forcing torus, `X(x,φ)=(X_H(x,φ),ωext)`. Neither subsystem energy nor
subsystem AMD is automatically conserved. Bound
`d_x F·X_H + ∂φ F·ωext` and every exit face. Adding dummy conjugate actions
does not restore a physical conservation law that the forcing has broken.

### Frozen surface versus internal work

Only exact elaborated Lean commands can be approved or frozen. The descriptions
above fix the intended mathematics but are **not** frozen declarations. The
final selected coefficient data, chart, tolerances and units are missing today;
it would be misleading to present a named SJSU theorem as already ready to seal.

| Candidate owner surface | Meaning to freeze | Keep internal |
|---|---|---|
| `checkPlanarLifetime` data semantics and soundness | Accepted finite data implies the full D1 physical conclusion, including existence | Interval primitives, Kepler tubes, scalar tests, stopped assembly |
| Selected `sjsuHamiltonian` | Exact coefficient/recipe semantics, with every data dependency pinned | Data layout, expression evaluation, polynomial normalization |
| Selected chart and `sjsuInitialRegion` | Exact construction/image and radius; units; nonempty/positive-volume and source-point inclusion proved | Inverse estimates, Lie-flow implementation, derivative bounds |
| `sjsuSecularLifetime` | D2 all-data 5-Gyr statement with explicit drift and eccentricity/separation bounds | B/C application, arithmetic shards, ODE continuation |

Do not freeze separate wrappers for every numeric comparison. Reuse B/C's agreed
general soundness surface. A chosen mathematical chart is specified by literal
linear/polar maps and finite flow compositions, with well-definedness and inverse
proved before freezing an exposed definition; no arbitrary `choose` with an unspecified
characterization. Large model data are split into modules below 1500 lines and
included in the semantic closure inspected at freeze time. A hash string alone
does not define a Hamiltonian.

This is principally formalization and rigorous numerical verification of known
methods. New contributions would be the reusable checker, effective bounds
currently obtained only by compactness, and a successfully certified planetary
instance. A useful realistic-mass D1 threshold, complete D3 transfer, or a
99%-volume inner-system result may require new estimates and substantial new
mathematics; none is being attributed to the cited papers.

## 3. Applications ranked by scientific impact

This ranks potential impact; execution order is deliberately different. Every
claim below quantifies all initial data in the *specified* set, or the stated
good-set fraction. A set still to be selected is identified as such.

| Impact rank | Exact intended claim and audience | Rigorous/numerical baseline | Feasibility judgment |
|---|---|---|---|
| 1 | A specified spatial inner-planet model, including GR and outer forcing: at least 99% of a declared probability/volume distribution on a declared uncertainty set stays below declared crossing/escape boundaries for 5 Gyr | ML21/HML22/MHL23 explain numerical statistics and quasi-integrals; no uniform certified estimate for this set is supplied | Research destination requiring new bounds on resonant transport and a validated measure/model bridge. No credible Lean runtime or completion date yet |
| 2 | Full planar moving-Sun SJS at the cited masses: existence, eccentricity/separation bounds and small action drift for a positive-volume tube for 5 Gyr | Frozen small-mass results; FH25 numerical torus with residual around `10^-54`, not a lifetime certificate | Hard. The earlier SJS scout's per-slot route projects `10,000–33,000` kernel CPU-h and TB-scale advice; local-normal-form cost is additional and unmeasured |
| 3 | Planar secular J–S–U–N, after symmetry reduction: tight modal-action bounds on a fixed region for 5 Gyr | General methods exist; no recovered instance comparable to the SJSU calculation in this task | Plausible only after a new numerical/model study. Three effective secular degrees of freedom. Degree-18 dense support can already reach 920,490 Cartesian terms before transformations |
| 4, recommended first flagship | Selected GLS-style SJSU secular polynomial: D2.3 on the specified `r=10^-7` tube for 5 Gyr, with physical reconstruction | GLS17 numerical estimate at a slightly smaller radius; no complete rigorous tail in that calculation | Plausible with B/D engineering if the data and first remainder tests pass. Reserve `100–1,000` kernel CPU-h only after a measured shard; do not equate this allocation with a benchmark |
| 5 | D1 lifetime curve for a fixed full-planar AMD box as mass decreases; eventually a positive-volume 5-Gyr example with explicitly scaled-down planetary masses | Existing qualitative theorem and explicit internal formulas | Strong feasibility for a small-mass demonstration; poor prospect for realistic masses from the current asymptotic formula. D1 code can be valuable even if its realistic-mass column is entirely rejected |
| 6, useful pilot | Formal LG00 confinement between two tori at the stated energy, or a uniform family over an energy interval | Rigorous interval-arithmetic result in 2000; repository scout has an exact 69-monomial transcription | Good calibration. Existing v2 projections are roughly 545–680 Fourier keys and `3–75` CPU-h per torus, unvalidated at full interval precision. One torus alone is not confinement |

The full SJS scout's cheap `6–19` or `34–351` CPU-hour scenarios assume
hypothetical packed arithmetic and/or untested hybrid extrapolation. Its
28–56-GB product estimates do not fit this machine. FH25 used about 194 GB
for numerical generation. A faithful large-grid replication needs separately
authorized hardware with at least 256 GB available, or a newly tested streaming
algorithm; that does not relax the 8-GB kernel design target here.
[SJS scout, §§5–6, 9](sjs-feasibility.md);
[FH25, §4](https://arxiv.org/abs/2403.10152v1).

BN18's Table 1 reaches `5.75·10^10 yr` at `ε=10^-11.25` for actions exactly
on its chosen 5:2 resonance; at `10^-11` its estimate is `3.08·10^7 yr`.
Its Table 3 concerns nonzero action radii and has different times. These numbers
are calibration for that paper's normalization, not mass thresholds for our
AMDBox or evidence that its zero-radius result covers an observational region.
[BN18, §5.1](https://arxiv.org/abs/1810.05987v1).

### Direct answer about the Solar System

| Scope | Time and initial region | Verdict |
|---|---|---|
| Exact first-order averaged planar SJS at the frozen decimal masses | All time in the frozen illustrative box | Already available; not an ephemeris enclosure |
| Selected planar SJSU secular degree-18 model | 5 Gyr near a specified numerical torus, target radius `10^-7` in source actions | **Plausible with this program**, contingent on data and rigorous tails; complete observational uncertainty coverage is not established |
| Planar four-giant secular model | 5 Gyr on a newly selected region | **Plausible only after a new quantitative study**; formal methods are available, no numerical closure is known here |
| Full planar SJS at actual-scale masses | Finite time on a small explicitly certified region | **Plausible with a substantial local-normal-form campaign**; 5 Gyr is unpriced and unverified. Raw D1 is not a plausible shortcut |
| Spatial forced secular Mercury–Venus–Earth–Mars with specified outer forcing and relativistic precession | Shorter lifetimes or a good subset of a named initial region, then possibly 5 Gyr | **Plausible only with new quantitative mathematics/data**, especially resonant approximate integrals and all-boundary separation |
| Full spatial eight-planet observed uncertainty set, no exceptional data, 5 Gyr | Complete uncertainty set and realistic force model | **Not a plausible first claim**. Numerical instability branches are a serious obstruction; no proof here that the exact universal proposition is false |
| “The actual Solar System is safe forever” | No model boundary, no initial-set qualification | **Not plausible as this program's output** |

The inner-system obstruction is specific. The `g1-g5` Mercury–Jupiter secular
resonance can exchange eccentricity; GR changes the relevant precession.
Laskar–Gastineau's 2,501 integrations give order-one-percent large Mercury
eccentricity events over 5 Gyr. This is neither a one-percent collision theorem
nor Lebesgue measure of a box. A roughly 5-Myr Lyapunov time measures local phase
separation, not escape time. [ML21, §§6–8, Appendix C](https://arxiv.org/abs/2105.14976v1).

Do not certify a degree-four forced model and advertise it as the degree-six
transport problem: the latter terms restore much of the numerical instability.
[HML22, §§3–4](https://arxiv.org/abs/2205.04170v1).
Proper degeneracy obstructs a direct application of A's global steep theorem;
actual mass ratios are not a tunable tiny parameter once the model is fixed.
Arnold diffusion makes a general higher-dimensional torus-barrier inference
invalid, but does not imply that a particular planetary region escapes within
5 Gyr. Neither the stability theorem nor a numerical Lyapunov plot proves
chaotic dynamics in the certified set.

A claim about observations additionally needs an epoch, element convention,
parameter intervals, uncertainty distribution, and a validated map into `Q`.
Planarity is not a spatial uncertainty set. A fixed Newtonian/relativistic model
also omits solar evolution, tides and other selected physical effects; the result
must name those model boundaries rather than be described as literal future
history of the planets.

## 4. Feasibility experiments performed for this plan

`python3 -B /tmp/prog-d-astra/scout.py` produced
`/tmp/prog-d-astra/scout.json`. It uses exact Python `Fraction` assertions for
the box test and 60-digit `mpmath` for diagnostics. Reported CPU time was
0.0015 s and peak RSS 16,064 KiB. These are untrusted calculations, not kernel
certificates. No orbit integration, normal form, or Lean process ran.

### E0: a concrete rejection test for the literal stopped formula

Choose `n=2`, `μ=4773/5000000`, and the following rational `AMDBox`:

| Field | Jupiter | Saturn |
|---|---:|---:|
| `mass` | `1` | `476/1591` |
| `lower` | `9/4` | `9/10` |
| `innerLower` | `113/50` | `91/100` |
| `innerUpper` | `23/10` | `47/50` |
| `upper` | `231/100` | `19/20` |

Set `ecc=3/20`, `initialAMD=7/1000`, `outerAMD=9/1000`, `distance=1`,
`radius=12`. All 17 rational positivity, nesting, squared-root, radial and
separation tests passed. For the AMD test, verify `1-Cout/L_i > 0` and
`1-ecc² < (1-Cout/L_i)²`. The adjacent radial gap before subtracting the required
distance is `1036470429/666400000 > 1`. The box is illustrative canonical data,
not a claim to contain the observed planets' uncertainty set.

The strict margin (D1.1) implies `δ<1/2000`. For two planets, `b=3/32`.
The old `stopped` export requires `δ ≥ (B0 μ)^(3/32)/2` with `B0≥1`.
Consequently acceptance would require

\[
 \mu^{3/32}<1/1000,\quad \mu^3<10^{-96},\quad \mu<10^{-32}.
\]

At the selected mass the required lower drift is `0.2605123181…`, over 520
times the allowed upper drift. The rational assertion `μ³ > 1/10^96` verifies
the contradiction without evaluating a fractional power. This test concerns
the literal asymptotic drift route; D1.4 uses the stronger internal block drift.
It also does not rule out a different physical region or a proved change of
normalization, whose entire analytic data would have to be recomputed.

### E1: sensitivity of the existing scalar thresholds

For a deliberately simple scalar input `g=m_f=1`, `M_c=n`, `ρ=1`, `k=n`,
the formulas in `ThresholdExplicit` give the following. Scaling `M_c` with
dimension avoids a misleading dimension-independent Hessian bound in the max
norm; these inputs are still illustrative, not derived planetary data.

| `n` | `a` | `b` | `log10 thrMuA` | `log10 (thrMuD k)` |
|---:|---:|---:|---:|---:|
| 2 | 0.062500 | 0.093750 | -13.6508 | -62.6856 |
| 3 | 0.033898 | 0.050847 | -19.1245 | -56.8334 |
| 4 | 0.020408 | 0.030612 | -24.8934 | -56.7117 |
| 8 | 0.005348 | 0.008021 | -49.7867 | -77.8527 |

These are **not planetary constants** and not final thresholds; other tests can
be smaller. The `ρ=0.1` repeat is in the receipt. It changes different tests
in opposite directions, so maximizing a tube width blindly is not an optimizer.
The experiment identifies a cheap scalar rejection gate to run before any large
coefficient or proof-term generation.

### E2: test whether coarse SJSU safety is already explained by AMD

Using GLS17 Table 1 and its canonical action formula (2) gives approximately

\[
 \Lambda=(0.54004966,0.21897501,0.04748436),\qquad C=0.00100152937.
\]

If these actions and total AMD are conserved in the selected secular model,
the elementary bound `e_i ≤ sqrt(2C/Λ_i-(C/Λ_i)²)` gives
`(0.060874,0.095533,0.204301)` and adjacent radial gaps about `3.108` and
`4.843 AU`. This is a **diagnostic inference**, not a certified statement about
the transformed GLS model: the averaged `Λ*`, chart transfer, symmetry and
initial-set interval bounds still need proof. It strongly suggests that a
5-Gyr no-crossing theorem alone would not justify the expensive normal form.

### E3: budget and support arithmetic

For `r=10^-7`, `R=2r`, `T=5·10^9 yr`, reserving half the available action
margin requires `η≤10^-17` action units/year. With the source's order-20
optimal-radius heuristic `R=(21/20)r`, the corresponding bound is `5·10^-19`.
The optimum must be recomputed with **all** tails and a residual floor included.
For the conventional `G=m0=1` AU model, 5 Gyr is `3.1415926536·10^10` internal
time units, with natural logarithm `24.17058082`.

Combinatorial upper bounds are small enough to inform the architecture:

- Even Cartesian degrees 2 through 18 in six variables: 76,713 monomials;
  in eight variables: 920,490. Symmetry can reduce these counts further.
- Fourier `|k|₁≤50`: 171,801 keys in three angles, 5,101 in two.
  Action degree at most 20: 1,771 monomials in three actions, 231 in two.
  A naive Cartesian product of these supports is already prohibitive.
- The 94,109,751-term intermediate source expansion uses 5.61 GiB even at a
  hypothetical 64 bytes per term, and 22.44 GiB at 256 bytes. A Python dictionary
  of large rational objects will exceed the 4-GB research budget. Stream pair
  contributions or evaluate certified coefficient recurrences instead.

No kernel cost is inferred from Python speed. No <8-GB arithmetic shard has
been measured for D2. That measurement is a gate before scaling, not a task
silently completed by this report.

## 5. Ordered work packages and stop conditions

Estimates below are incremental handwritten lines, excluding generated data,
with roughly factor-two uncertainty. B/C contributions are not counted again.
No package may depend on an unfrozen substitute for an existing anchor.

| Order/package | Inputs → concrete output | Lean / Python estimate | Checks and stop condition |
|---|---|---|---|
| D-P0: model and region charter | GLS17, local SJS data, source recipes → exact model inventory, units, missing-data list, symmetry/AMD baseline, fixed region proposal | 0 / 400–800 | Every coefficient source and `Λ*` identified; no silent midpoint substitution. Stop model production if data cannot be recovered |
| D-P1: finite partial gate | `PartialConstants`, `Block`, E0 box → checker for finite scalar tests and soundness; mass/time/box rejection report | 1.5–3k / 300–700 | Default-heartbeat focused builds; positive toy passes, E0 conservative route rejects, sign/boundary/units mutations reject. Stop before analytic expansion if all physically interesting scalar candidates fail |
| D-P2: quantitative planetary adapter | D-P1 and existing P charts → checked complex tubes, Kepler/interaction bounds and D1-SOUND | 7–15k / 0.5–1.5k | No compactness witness masquerades as a number; full Hamiltonian identity and both time directions. Start with a scaled-mass instance; stop promising realistic masses unless D1.4 closes |
| D-P3: secular model and chart attachment | D-P0 selected data and B interface → exact Hsec, symmetry identity, coefficient enclosures, inverse-chart/source-point bounds | 4–10k / 1–3k | Independent coefficient/sign/time audit. Check `{∑Γ_i,Hsec}=0` exactly when claimed; residual symmetry defects must instead enter C's budget |
| D-P4: bounded normal-form producer | D-P3 and B's checked finite Lie scheme → candidate normal forms, tail ledger, complete `T(r)` curve | 1–3k adapter / 2–5k | Each exploratory run <1 CPU-h and Python <4 GB. Stop if the certified low-order residual alone exceeds the time budget; more high-order normalization cannot cure that floor |
| D-P5: small certificate before scale | One complete low-order example/shard → measured kernel time, RSS, bit width, artifact size, and sound recombination | 1–3k / 0.5–1k | Ordinary kernel checking; <8 GB including imports and aggregation; no overrides. If projection exceeds 1,000 CPU-h or advice exceeds agreed storage, redesign before a production run |
| D-P6: SJSU lifetime and physical outputs | D-P3–P5, B, optional C → literal 5-Gyr application, positive-volume/source-point proof, eccentricity and radial bounds | 3–6k / <0.5k | Full remainder sum, chart coverage, existence/uniqueness, units; independent statement and numerical audit; opt-in certificate replay; final `#print axioms` |
| D-P7: fidelity increase | Successful D-P6 plus selected target → four-giant secular, full SJS, or inner forced-model scout | New estimate after scout | No transfer based only on `O(μ²)`. Stop/re-scope openly if all-boundary separation or model-error budget fails |

D1 is approximately 9–18k additional Lean lines; D2 approximately 10–22k
beyond B's common core. These overlap through arithmetic/chart utilities and
are not commitments. A full inner forced-model adapter could require a further
20–50k lines before quantitative usefulness is known.

### Next experiments, each strictly below one CPU-hour

Set a process CPU limit as well as a wall/RSS watchdog; a wall timeout alone
does not limit multithreaded CPU consumption. Keep numerical libraries to one
thread. Research Python limit is 4 GB. The future kernel probes below belong to
the implementation phase; none is authorized or run as part of this no-build
planning task.

| Experiment | CPU ceiling | What it decides |
|---|---:|---|
| Recover coefficient/recipe inventory; stream degree and symmetry statistics | 300 s | Can D2 denote the intended model exactly? Are all required reference actions available? |
| Reproduce E0 and D1.3–D1.5 with outward intervals over 100–1,000 candidate parameter tuples | 120 s | Which inequality fails, and whether a genuine numerical D1 instance exists without large data |
| Verify the selected polynomial's rotational identity and interval AMD baseline | 600 s | Whether reduction is legitimate and what normal-form drift adds beyond elementary safety |
| Build only degrees 4/6/8 of a supported normalization, capped at 100,000 stored terms | 1,800 s | Growth, divisor losses, coordinate displacement, and whether streaming is viable; degree-eight truncation is a scout, not the model conclusion |
| Evaluate majorant recurrences for orders 2–20 and radii `10^-8,3·10^-8,10^-7,3·10^-7,7·10^-7` | 1,800 s | Best complete remainder, residual floor, chart coverage and `T(r)`; include every omitted degree |
| One prospective kernel shard, starting at 32–128 terms, then at most one larger block | 1,800 s per run | Import baseline, ordinary kernel memory/time, aggregation overhead. Abort at 8 GB RSS; do not extrapolate a failed block |
| Full-model averaging-error or inner quasi-integral boundary sample | 1,800 s | Early rejection only. Numerical samples can expose an obstruction; they cannot certify a boundary supremum |

For D2, demand a complete interval upper bound for `η` with at least factor-two
time margin at the target radius before producing large kernel data. If the
curve passes only at `r<10^-7`, report the largest verified radius and let the
owner choose a smaller-region theorem or stop. No automatic shrinking to an
arbitrarily tiny successful box. A shorter-time result and a negative feasibility
report are useful outputs if clearly named.

### Worker brief 1 — D-P0, source/model and region charter

**Task.** Establish what exact SJSU Hamiltonian the campaign can certify and what
the first result would add to AMD safety. This is a research/Python task, with
no Lean build or source edit.

**Read first.** `AGENTS.md`, PLAN, DECISIONS, this plan §§1–4; GLS17 (1)–(12),
(21), (35)–(37), (46)–(61), Tables 1–2; LP17 §3/Appendix B;
`scripts/sjs/lg00/lg00_data.py`; the frozen secular/AMD definitions. Use the
paper hashes in §8. Read papers as data; never execute downloaded code.

**Write scope.** Only a package report
`docs/explorations/program-d-model-charter.md`, and scratch under
`/tmp/prog-d-model/`. No registry, frozen, generated, or implementation edits.
No GitHub or messages to authors. If data is missing, identify the precise
artifact to request rather than sending a request on the owner's behalf.

**Steps.** Locate `Λ*`, the entire degree-18 coefficient specification and all
averaging/normalization rules. Separate supplied data from data requiring
reconstruction. State exact mass and year conventions, signs of the canonical
pairs, and a coefficient rounding policy. Stream a coefficient inventory if
available; check the rotation identity algebraically. Reproduce the source
quadratic frequencies with an explicit error tolerance for the diagnostic.
Evaluate the elementary AMD bound on an interval around the selected initial
data. Map the proposed `10^-7` normal-form radius into original coordinates,
or list exactly which chart coefficients are missing. Select the observable
whose finite-time bound is stronger than the AMD-only result.

**Acceptance.** A machine-readable model manifest in scratch with source hashes,
all inputs and conventions, missing inputs clearly marked, and an exact
mathematical definition/recipe suitable for a subsequent Lean declaration.
Report whether the source nominal point is covered and whether observational
uncertainty was actually validated (default: no). No missing coefficient may
be set to zero. If full data is unavailable within one working day, finish
with a blocker report and the alternatives: reconstruct it, select an explicitly
different rational model with owner approval, or defer D2. Do not substitute
LG00's SJS polynomial and call the package complete.

**Budget.** Two working days, 400–800 Python lines; each experiment <1 CPU-h,
RSS <4 GB. Deliver exact commands/logs, numerical versus rigorous labels,
suspected errata and deviations. Run the source-only lint phases without
invoking Lean; disclose the skipped ABI phase as in §8.

### Worker brief 2 — D-P1, finite numerical partial-convex gate

**Task.** Make the numerical part of (D1.3)–(D1.5) checkable without an
existential threshold. Do not attempt the full complex planetary adapter yet.
This brief is for a subsequent authorized implementation phase, not execution
during the present planning task.

**Read first.** `AGENTS.md`, PLAN, DECISIONS, this plan §§2,4;
`KAM/Nekhoroshev/Partial/{Constants,Threshold,ThresholdExplicit,Block}.lean`,
`KAM/Planetary/Exponential/{Setting,Stopped}.lean`, existing rational interval
and exponential-bound primitives under `KAM/Certificate/`. Read provider source
only to understand assembly; no new module imports it.

**Write scope.** New focused modules under
`KAM/Planetary/Quantitative/Numbers/`, a narrow facade
`KAM/Planetary/Quantitative/Numbers.lean`, producer scripts under
`scripts/planetary/quantitative/`, and a package handoff. Coordinate the exact
new prefix with the orchestrator before the first edit if another worker owns
it. Do not alter public frozen bytes, existing checker semantics, or generated
roots. Keep all large generated instances in opt-in targets.

**Inputs.** Natural `n≥2`, `k≥1`; positive rational `ρ,g,m_f,M_c,ν,T,δ`;
positive rational `κ,A_s,Cout`; rational witnesses enclosing (D1.3), with
`n` as fast dimension and `k` in the slow-loss factor and the slow collar's
`sqrt(2*k)` (`k=n` only for the planetary adapter). The carrier contains only
numbers and finite advice.

**Outputs.** A computable Boolean checker and ordinary, sorry-free soundness
lemmas proving the first four comparisons of D1.4, `T≤T_b`,
`R0/(2K)≤δ`, and D1.5 with slow dimension `k` from acceptance. Prove an optional conservative mode
with `ν^b/2≤δ` and `T≤ν^-1 exp(ν^-a)` separately. Do not freeze this helper
or call it planetary safety: the analytic and Hamiltonian obligations belong
to D-P2. Log the direction of every interval comparison and the failed test.

**Implementation order.** First mirror the existing formulas, including all
`2π` factors, and reproduce §4. Next isolate real arithmetic lemmas over named
constants; add rational enclosure soundness using existing primitives. Prefer
rational powers by positive-root comparisons and a logarithmic time comparison.
Avoid unfolding all transcendental expressions into `nlinarith`. Supply a small
accepted scalar example and a checked rejection of the conservative E0 request.
The example is a scalar test, not a Newtonian theorem. Do not invent `μf`.

**Acceptance/checks.** One targeted `nice -n 5 lake build
KAM.Planetary.Quantitative.Numbers` at a time; `scripts/lint_sources.sh`;
`#print axioms` for the soundness results from temporary audit scratch. Expected
axioms are at most `propext`, `Classical.choice`, `Quot.sound`, with no
`sorryAx`. Meaningful mutation cases must reject a nonpositive denominator,
a reversed enclosure, a violated slow collar and an incorrect time-unit factor.
The internal threshold output must imply the exact Lean inequalities read from
`Partial.Block`; it is not enough to agree with the Python mirror. Stop and
report a default-heartbeat failure or an import baseline above 8 GB.

**Budget.** Three to five working days, 1.5–3k Lean and 300–700 Python lines.
One compile gate, <8 GB per Lean process and <4 GB Python. Handoff files,
approach, complete checks/output, axiom output, uncertainties, errata and
deviations. No public source theorem changes in this package.

**Hard rules (verbatim).**

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

## 6. Dependencies and resource design

| Other work | Dependency direction |
|---|---|
| A1 | Share certified transcendental arithmetic and finite analytic-bound witnesses. Its quasi-convex theorem is not the planetary partial-convex theorem. D-P1 can start independently |
| A2 steepness | Optional after a planetary normal form actually passes a quantitative steepness criterion; neither prerequisite for D2 nor automatic cure for proper degeneracy |
| B1 finite normal form | Hard dependency of the recommended D2 route: exact canonical maps, complete remainders, drift/continuation. D owns model coefficients, inverse-chart coverage and physical units |
| B2 near-torus asymptotics | Optional stronger general result. A finite 5-Gyr certificate can include a nonzero torus defect |
| C1/C2 | Alternative/resonant confinement backend; essential for a realistic inner forced-model attempt. D supplies physical escape boundaries and forcing semantics |
| C3 good-set measure | Needed only for the fraction-of-initial-data target. It must include cell coverage, overlap accounting and density/Jacobian bounds |
| v2 `routeV2All` | Optional exact-torus certificate and LG00 calibration; route selected by measured data. Infinite Diophantine claims need proofs, not finite divisor scans |
| Hybrid | Optional cost reduction for torus validation; not a normal-form or transverse-tail theorem. Wire and test its checker before using any projected savings |
| LG00 | Compact regression/model-convention pilot; source-driven existing rigorous result. No reason to make the D1 scalar work wait for it |
| Lunar SO / next demonstrations | Reuse arithmetic and shard measurements. Preserve their scopes and N=65 rulings; Mercury spin confinement is not Mercury orbital confinement |
| Full SJS/FH25 | Later input for D3. A numerical torus alone neither traps a neighborhood nor validates a 5-Gyr lifetime |

Use bounded sparse blocks and outward dyadic rounding. Keep numerical generation
untrusted and ordinary kernel checking authoritative. Split a large arithmetic
reduction itself: putting the same huge expression in a smaller source file
does not reduce its memory. Measure the import baseline, worst multiplication,
recombination, and final theorem loading. Balanced traversals and independently
proved norm summaries are more useful than a single enormous `decide`.

For a first D2 production run propose a 1,000-CPU-hour ceiling and a 100-GB
advice/storage ceiling, conditional on owner choice and a measured sample.
These are stop limits, not predicted costs. Keep each Lean process below 8 GB,
leaving room below the 10-GB kill guard and the 32-GB user cap. Do not run four
8-GB processes alongside producers; the one-targeted-build gate applies.
An import baseline or final aggregation can violate the limit even if each
isolated product fits. Do not rerun RefinedRefR1 or other heavy v2 tests.

## 7. Decisions and timeline

The owner should decide the following after D-P0/P1 provide concrete evidence.
No decision here is a request to change an existing frozen statement.

1. **First scientific result:** recommend tight 5-Gyr SJSU secular action bounds;
   accept the two-effective-degree-of-freedom qualification. If three effective
   degrees are mandatory, choose four-giant secular or full SJS and re-scout.
2. **Model identity:** prefer the exact recovered GLS construction. If unavailable,
   choose explicitly between reconstruction and a named rational-polynomial
   model; do not conflate the latter with the untruncated secular average.
3. **Minimum region:** recommend source-action radius `10^-7`, all torus phases,
   and proved nominal-source-point inclusion. Full modern uncertainty coverage
   is a separate milestone. A smaller successful radius needs a new choice.
4. **Time and observables:** recommend 5 Gyr, transformed-action drift at most
   `10^-7`, plus the eccentricity/separation targets in §2. Publish `T(r)` even
   if this particular point fails. For inner planets, select the measure and
   exceptional fraction before attempting a 99% statement.
5. **D1 value:** recommend a reusable explicit small-mass interface and honest
   rejection tables; do not commission a large realistic-mass expansion unless
   the finite gates show a viable route.
6. **Resources:** recommend the conditional 1,000-CPU-hour/100-GB D2 ceiling.
   A 256-GB generation machine or cluster is a separate full-SJS resource
   decision. Extra hardware cannot fix a missing mathematical tail bound.

With the common B1 core available, a reasonable conditional schedule is:

| Elapsed implementation time | Deliverable/decision |
|---|---|
| Days 1–2 | D-P0 model/data verdict; exact elementary AMD comparison |
| Week 1 | D-P1 scalar checker and rejection curve; no realistic-mass promise |
| Weeks 2–4 | D-P2 quantitative chart work and a scaled-mass D1 example; D-P3 secular model attachment |
| Weeks 4–6 | D-P4 complete interval remainder curve and D-P5 measured kernel shard; stop/go on target radius and budget |
| Weeks 6–10 | D-P6 certificate production, physical transfer and independent audits if all gates pass |
| Weeks 10–14 | Contingency for interval losses, kernel sharding and final replay; select D-P7 only after closeout |

This is an engineering estimate for sustained prover/reviewer work with a
serial compile gate, not a booking of agents or a guaranteed delivery date.
If B1 is not ready, add its own campaign schedule. If the data or tail gate
fails, the first-week report or the `T(r)` curve is the deliverable; no date for
a 5-Gyr theorem should be retained. The observed full inner system has no
credible completion timeline from current evidence.

## 8. Provenance, defects, deviations and handoff

Versioned PDFs were copied from existing research scratch or downloaded into
`/tmp/prog-d-astra/papers/`; only data was read. Full hashes are recorded here
so the evidence does not depend solely on temporary files.

| Source | SHA-256 of PDF |
|---|---|
| Nek77, registry pin only | `0bfe624cf108096badd7e27fc40ca800e2948b68dce2bf8b9c653e0eaec4def6` |
| LP17 v2 | `6b3c7aad2c2bf69612c0e0a65a5409f40a03e330253f8b3880f8e53d40f09361` |
| GLS17 v1 | `254d52fb9c545efe12cfcc4b138ac8b429c1e95aad0d63c12b4e6dfc182e1cae` |
| MG08 v1 | `d7bf30d0db8bfe236506fd3eca8ae44de774f1b12f5d4d56b5aa8e65cd855177` |
| LG00 local author copy | `a4f1ace6293ca9fd3792e50d1ab158d509e64f5bfaf25074ed7a8149c1db24a3` |
| BN18 v1 | `b543c39ee7731b8b6b9cf229a3304ba6b6dd14058a3310d84871107283514815` |
| FH25 arXiv v1 | `379c8b41b53a1fd50cbc890cca06d646ccd93f5c0d5e0226d1303885d2df7cf7` |
| ML21 v1 | `7537e3b2536766d18fcf5db1844e9586eefba46318645373ee0ed532f9c32526` |
| HML22 v1 | `66a18c8fe1c24419172b163bf51170735d6016d7917133191a46a48c85038bc4` |
| MHL23 v1 | `c44419c0dfefba8492af1f648753d0ddd90313b64acffd31e56f8549a460d1c7` |

**Suspected source defects for the orchestrator's ledger.** The following were
checked against rendered GLS17 v1 PDF pages 12 and 25, saved in scratch. They
are reported as candidates pending independent review; this task does not edit
the errata ledger.

- **GLS17 p. 12, §2.2.2, repeated harmonic:** printed
  `3λ₁ − 5λ₅ − 7λ₃`. The model has only three planetary angle indices, and
  (10)–(11) and the contributing 5:2 harmonic use `λ₂`. Candidate correction:
  replace `λ₅` by `λ₂` in those three occurrences.
- **GLS17 p. 12, (13), summation lower limit:** printed `j=0`. The declared
  mode coordinates and frequencies have indices `1,2,3`; the surrounding text
  explicitly names those three frequencies. Candidate correction: `j=1`.
- **GLS17 p. 25, (57):** printed factor `ρ^(l+1)` multiplying the coefficient
  norm of `{p_j,R_l}`. By (54)–(56), `R_l` has action degree `l`, and an angle
  derivative preserves that degree, so the factor should be `ρ^l`. For
  `R_l=p_1^l cos q_1`, the derivative supremum on `|p|≤ρ` is `ρ^l`; at
  `0<ρ<1` the printed power is too small. Equation (58) uses the expected
  first-remainder degree `r+1`, so this does not by itself establish an error
  in the reported numerical curve.

**Source limitation rather than a hidden repair:** GLS17 p. 25, (58) keeps
the first omitted contribution without a complete upper bound for the rest.
The paper explicitly qualifies its calculation as non-rigorous. D2 will prove
an entire tail bound and retain finite-normalization residuals; (58) is not
imported as a rigorous lower-bound theorem. The observation is not a new
claim that the authors asserted a completed computer-assisted proof.

Existing Nek77/LP17 ledger findings and adopted planar/stopped deviations are
inherited, not re-audited. No suspected defect in a frozen Lean declaration was
identified by this inspection.

**Proposed deviations, all visible:** finite numerical checker interfaces;
explicit existence/local-uniqueness conclusions; stronger internal block output
instead of discarding constants into an asymptotic exponent; an exact selected
secular polynomial before an untruncated/full-model theorem; positive-volume
torus tubes across AMD values; period and time conversions; and optional
rational-coefficient model selection only by an explicit owner choice. None
changes a frozen statement. A new tight-action result must be described by its
actual chart and not as constant physical eccentricity.

**Checks and scope of this handoff.** Sole project file:
`docs/explorations/program-d-plan.md`. No Lean, frozen, manifest, README or
generated-root file changed. No GitHub operation, subagent, Lean build, Lean
probe, or `#print axioms` ran. Axioms of new results: not applicable, because
there are no new Lean declarations. Existing axiom status was not independently
rechecked.

The required lint invocation used a scratch `python3` wrapper that adds `-B` to prevent
bytecode writes and refuses only `scripts/abi_hashes.py`, which would write
repository scratch and invoke Lean. This obeys PROGRAM-D's no-build and
restricted-write scope. It is a partial lint run, not a passing full lint.

Exact lint command:

```sh
PATH=/tmp/prog-d-astra/bin:$PATH scripts/lint_sources.sh > /tmp/prog-d-astra/lint.log 2>&1
```

Output, exit status **1** because the ABI phase was deliberately refused:

```text
check_lean_modules: PASS (1829 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI SKIPPED: PROGRAM-D prohibits Lean builds and repository scratch writes.
```

The other source-only lint phases emitted no findings. A targeted Lean build
and ABI/axiom replay are intentionally absent under the more specific PROGRAM-D
restriction; this document introduces no Lean target to build.

`python3 -B /tmp/prog-d-astra/validate_plan.py` exited **0**:

```text
PASS: 18 local links, 9 downloaded PDF pins, scalar-table transcription.
PASS: verbatim hard rules, whitespace, 14 paired math displays and code fences.
```

This checks the downloaded PDF hashes against the pins above; Nek77's inherited
registry pin is deliberately excluded. The numerical scout's 17 exact rational
assertions passed; its floating estimates remain diagnostics. Staging is limited
to this plan. `git diff --cached --check` exited **0**, with no output.
