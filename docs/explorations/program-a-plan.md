# Program A: explicit stability certificates, then the steep theorem

Research and implementation plan, 30 October 2026. Inspected branch `prog-a`,
commit `fb782d6947546b4a5121a509a76844e325f54987`.
This document proposes work; it approves no declaration and reports no new Lean proof.

**Recommendation:** complete A1, a small numerical interface to the existing quasi-convex
Nekhoroshev theorem, with a fully checked three-degree-of-freedom example. Then make
an explicit choice between improving useful constants and undertaking A2, the general
steep theorem of Guzzo–Chierchia–Benettin. A2 is a substantial generalization of the
mathematics formalized here, but it will not, by itself, certify the observed planets.
For an actual planetary lifetime, combine A with the normal forms of B and the physical
and resonant confinement work of C/D.

The first calculation is sobering: on a simple quadratic model, the existing global
threshold is about **1.16 × 10⁻³⁰ in the analytic perturbation norm**. The checker can be
small even when this threshold is extremely small. More RAM will not improve that bound.
Conversely, at a sufficiently small perturbation the same theorem gives times far beyond
a direct derivative estimate; the pilot below makes that distinction testable.

## 1. Baseline and source authority

The manifest at this commit records 134 sealed definitions, 23 sealed theorems and one
draft theorem, W-NLW2. These are inspected manifest states, not a new build or axiom audit.
Older phase labels in TRACKS and early explorations are not current proof-status evidence.

| Existing component | Exact use in A | Boundary of reuse |
|---|---|---|
| [N-HEAD-C](../../KAM/Frozen/Nekhoroshev/Theorems/QuasiConvexNekhoroshevComplexBound.lean) | Uniform quasi-convex theorem, dimension n ≥ 3, existence and uniqueness, exponent 1/(2n) | Requires both a complex Hessian bound and a positive frequency lower bound |
| [Constants](../../KAM/Nekhoroshev/Interfaces/Constants.lean), [explicit assembly](../../KAM/Nekhoroshev/Assembly/Headline.lean) | `HeadParams`, `HeadHyp`, `head`; formulas already proved before existential packaging | Real-valued, noncomputable formulas are not an executable numerical certificate |
| [Projection](../../KAM/Nekhoroshev/ResonanceGeometry/Projection.lean), [normal forms](../../KAM/Nekhoroshev/NormalForm/NormalForm.lean), [ODE specialization](../../KAM/Nekhoroshev/ODE/Specialization.lean) | Coordinate Euclidean norms/projectors, lattice geometry, exact transformations, continuation | Quasi-convex block confinement cannot be reused as if it proved steep block confinement |
| [Stopped planetary assembly](../../KAM/Planetary/Exponential/Stopped.lean), [AMD transfer](../../KAM/Frozen/Planetary/Theorems/AmdConfinement.lean) | Later application interfaces for D | A1 does not prove `StoppedActionBound` for a planetary Hamiltonian |
| [Expression evaluator](../../KAM/Certificate/Expr/Basic.lean), certificate arithmetic | Rational expressions, structural analyticity/periodicity, dyadic enclosures | Torus certificates check a different mathematical property |
| [v2 engine](../../KAM/CertificateSharp/V2/Engine.lean), [routeV2All](../../KAM/CertificateSharp/V2/RouteAll.lean) | Reuse arithmetic and soundness architecture; optional input to B | A witness selects one route; this is not a search or a Nekhoroshev checker |
| [Hybrid first step](../../KAM/Sharp2/Hybrid/G1.lean), [design](../campaign/design/APOST-SHARP-V2-HYBRID.md) | The mathematical restart/transfer theorems have landed at this snapshot | No hybrid certificate wiring was found under `KAM/CertificateSharp`; sampled R1 savings are not planetary measurements |

In particular, `ambition.md`'s “hybrid is a design” description has been overtaken by
code. A1 and A2 do not depend on finishing that wiring. The `sqrt` expression is also
present; the older LG00 “missing sqrt” statement is stale.

Sources for the proposed mathematical surface:

- **A1:** Pöschel 1993, Theorem 1, printed pp. 190–191, and Normal Form Lemma,
  p. 192; the theorem's main displays are unnumbered. Read against the pinned
  [journal scan](https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0213/LOG_0021.pdf)
  and the repository's [conversion packet](../tracks/N/sources.md), especially
  POS190-HESS, POS190-QC, POS190-T1 and POS191-LOW/TIME. Use the *landed* `HeadParams`
  formulas, including its √n loss, rather than reconstructing a stronger theorem from the scan.
- **A2:** [GCB16, arXiv:1403.6776v1](https://arxiv.org/pdf/1403.6776v1), equation (3),
  Theorem 1 and (4)–(5), pp. 3–4; quantitative assumptions and (6)–(9), pp. 4–5;
  Lemmas 2.1–2.3, Lemma 3.1, §4 and Appendices A/B for the proof. The preprint is
  the pinned text; the journal reference is CMP 342 (2016), 569–601.
- **Arithmetic interface and finite witnesses:** new deductions from those theorems,
  elementary matrix inequalities and exact finite-expression semantics. These are not
  attributed to a numbered theorem in either paper.

A1 formalizes an application interface for established mathematics. A2 formalizes an
established broader theorem. Neither is a new mathematical stability theorem. Better
application constants or a previously unproved numerical instance could be new results;
that requires a separate mathematical and priority assessment.

## 2. A1: exact target and an inexpensive certificate

### 2.1 Carriers, hypotheses and quantifiers

Use `Fin n → ℝ`, `Fin n → ℂ`, and `Fin n → ℤ`; angles are period-one lifts.
The default coordinate norm is the maximum norm. For Euclidean estimates write
`euclid v = sqrt (∑ i, v i ^ 2)` explicitly, using the existing coordinate API.
Never change the ambient norm by introducing `EuclideanSpace`.

Fix, **before h, f, ε and the initial point**,

\[
n\ge3,\qquad R,s,M,m,M_{\mathbb C},w>0.
\]

Take `h : (Fin n → ℂ) → ℂ` and
`f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ`. The premises are exactly:

1. `IsAnalyticIntegrable R s h`: holomorphy on the complex s-neighborhood of the
   open maximum-norm ball B∞(0,R), continuity on its closure, boundedness, realness
   on the real slice, and its recorded real C³ regularity.
2. `HasComplexHessianBound R s h Mc`: the **iterated operator norm** of the complex
   second derivative is at most Mc throughout that complex neighborhood.
3. `w ≤ ‖frequencyMap h I‖∞` for every I in B∞(0,R).
4. `IsStrictlyQuasiConvex (realActionDomain n R s) h m`: on the larger real slice,
   the gradient is nonzero and
   `m * ‖v‖∞² ≤ D²h(I)[v,v]` whenever `∑ i, ω(I)i * v i = 0`.
5. `HasDerivativeBounds (realActionDomain n R s) h M`: every coordinate partial
   of orders 1, 2 and 3 is bounded by M. This is not an operator-norm substitute.
6. `IsAnalyticPerturbation R s ε f`: nonnegative ε, holomorphy, closure continuity,
   period one, realness and `‖f(z)‖ ≤ ε` on `complexDomain n R s`.

In particular, the lower bound in item 3 and the nonvanishing in item 4 have different
domains. An implementation must verify both. Initial angles are arbitrary; initial
actions satisfy the **strict** condition `‖I₀‖∞ < R/2`.

### 2.2 An explicit mathematical root, derived from `head`

Use the following literal constants, all fixed by the six positive scalar inputs:

\[
\begin{aligned}
q&=m/n,& B&=nM_{\mathbb C}+q,& \mu&=q/2,\\
\ell&=wq/[8(B+q)],&
r_0&=\min\{s/2,R/8,\ell/(2B),4w/\mu\},& A&=11B/\mu,\\
E&=\frac{\mu r_0^2}{2^{10}A^{2n}\coth(\pi s/4)^n},&
d&=r_0/A,& T_0&=A^2s/(4nM),& K&=\pi s/(6\sqrt n).
\end{aligned}
\]

Here E is `epsStar/F`. Algebra plus `const_size` gives `HeadParams.eps0 = E`:
`d ≤ R/176` makes the additional radius cutoff in `eps0` redundant. This equality
is a **new helper to prove**, not a claimed existing export. The existing constants are

\[
a=1/(2n),\qquad C=dE^{-a},\quad c=KE^a,\quad T=T_0.
\]

**Proposed A-QC-WINDOW.** Under §2.1, for every `ε,x,L,Δ : ℝ` satisfying

\[
0<\varepsilon\le Ex^{2n},\qquad 0<x\le1,\qquad
0\le L\le T_0\exp(K/x),\qquad dx\le\Delta,
\]

and every θ₀,I₀ with `‖I₀‖∞ < R/2`, there exists
`z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)` with:

- `z 0 = (θ₀,I₀)`;
- `IsSolutionOn (realHamiltonian h f) (actionBall n R) (Icc (-L) L) z`;
- `∀ t, |t| ≤ L → ‖(z t).2 - I₀‖∞ ≤ Δ`;
- for every `0 ≤ L' ≤ L` and every solution y in the same action domain on
  `[-L',L']` with the same initial point, `∀ t ∈ [-L',L'], y t = z t`.

Use this precise agreement clause, not uniqueness of a total function on ℝ whose
values outside the interval are unconstrained. `IsSolutionOn` includes two-sided
`HasDerivAt` even at the endpoints. Restrict the solution supplied by `head`;
never assume existence for the requested lifetime. Keep the separate integrable
zero branch from [N-ZERO](../../KAM/Frozen/Nekhoroshev/Theorems/ZeroPerturbation.lean).

The proof is monotonicity with `(ε/E)^a ≤ x`: drift decreases with this quantity
and the exponential time increases with its reciprocal. The root is useful even
without a checker. A scalar comparison with a requested lifetime is a static
inequality, not a hypothesis that the solution is confined.

**Frozen surface:** propose one new root, A-QC-WINDOW, with the displayed constants
as inline `let` expressions and the six existing frozen predicates expanded in the
review packet. This avoids silently making mutable `HeadParams` definitions part
of a new frozen meaning. Keep N-HEAD-C unchanged. No new certificate syntax or
checker implementation needs to be frozen; their soundness theorems remain ordinary
independently reviewed declarations, following the existing certifier precedent.

### 2.3 Certificate semantics and soundness

The first format supports a rational action polynomial h and a finite real
Fourier–Taylor perturbation f, with integer Fourier keys. Use `HamExpr` for
denotation and a checked action-only subgrammar for h; permit only constants,
actions, addition, multiplication and natural powers in that subgrammar. The
first f grammar adds sine/cosine of integer modes. This is a sufficient checker
for a useful finite class, not a decision procedure for analytic Hamiltonians.

A certificate contains the expression data, n and positive rational bounds, a
finite cover for real inequalities, matrix witnesses, and scalar witnesses below.
Every list has checked dimensions and support. No record field is a proof of
`HeadHyp`, stability, existence, a remainder estimate or a stopped action bound.

| Obligation | First supported witness and its soundness obligation |
|---|---|
| Analyticity, realness, periodicity, closure continuity | Polynomial/trigonometric syntax; prove its denotation matches the frozen predicates |
| Perturbation bound | Bound polynomial coefficients on `\|Iᵢ\| ≤ R+s`; weight each mode by an upper bound for `cosh(2πs\|k\|₁)` or `exp(2πs\|k\|₁)`; sum absolute contributions |
| Coordinate derivatives of h | Exact symbolic derivatives through order three, with coefficient majorants on the real cube `\|Iᵢ\| ≤ R+s` |
| Complex Hessian | Bound `∑ᵢⱼ sup \|∂ᵢ∂ⱼh\|`, a valid sufficient iterated-norm bound on the complex polydisc; never use eigenvalue modulus |
| Frequency | Certified component lower bound on each covering cell, with separate coverage of B∞(0,R) and nonvanishing on B∞(0,R+s) |
| Quasi-convexity | On each cell certify `D²h + λ ωωᵀ ≥ m Id`, for a supplied rational λ ≥ 0, by interval diagonal dominance initially; LDLᵀ witnesses are a later stronger option |
| Cell coverage | Exact box-union coverage, not sampled point checks; all interval variations accounted for |

The quasi-convex witness works because the extra rank-one term vanishes on
`ω⊥`, and `‖v‖₂² ≥ ‖v‖∞²`. It is intentionally sufficient, not equivalent to
the source hypothesis. Some quasi-convex inputs will be rejected. For a diagonal
quadratic h the entire domain needs one cell and λ=0.

For rational inputs, q,B,μ,ℓ,r₀,A,d,T₀ are rational. Choose rational Q,u,k with

\[
Q\ge\coth(\pi s/4),\quad u>0,\quad u^2\ge n,\quad
0<k\le\pi s/(6u),\qquad
\underline E=\mu r_0^2/(2^{10}A^{2n}Q^n).
\]

A deliberately simple implementation can use
`Q ≥ 1 + 4/(3s)` and `k = s/(2u)`, from π > 3 and
`coth y ≤ 1+1/y`. Sharper outward bounds are optional.
For `x,ε,Δ,L : ℚ` and `N : ℕ`, check only

\[
0<x\le1,\quad 0<\varepsilon\le\underline E x^{2n},\quad
dx\le\Delta,\quad 0\le L\le T_0 2^N,\quad N\le k/x.
\]

Since `2^N ≤ exp N`, these imply A-QC-WINDOW. This avoids computing either a
real root or a giant exponential in the kernel. A logarithmic comparison is a
later optional improvement; it must check an outward bound on `log(L/T₀)`.

To supply the original A1 report fields, also accept `v > 0` rational with
`v^(2n) ≤ underline E`. Then

\[
\widehat C=d/v\ge C,\qquad 0<\widehat c=kv\le c,\qquad
\widehat T=T_0,\qquad
\widehat\varepsilon_0=
\min\{\underline E,(R/(4\widehat C))^{2n}\}\le\varepsilon_0.
\]

The additional minimum preserves the advertised radius margin for the *rounded*
C as well. Output exact rational bounds alongside readable decimals.

**Soundness target:** for every supported finite certificate c,
`checkQCCertificate c = true` implies the full existence, drift and agreement
conclusion of §2.2 for its literal Hamiltonian, rational L and Δ and **every**
initial angle/action in its declared inner ball. The only external premise is a
separately stated equality/transfer if a caller wants another Hamiltonian. A
polynomial surrogate is never silently identified with an untruncated model.
A translated action ball is handled by proving the canonical translation
`I = Icentre + J`; inclusion of a supplied initial box is another exact check.

### 2.4 Concrete pilot and fresh feasibility calculation

Fix n=3, R=1, s=1/4, M=13/4, m=1, Mc=3 and w=1. Set

\[
\begin{aligned}
h(I)&=2(I_1+I_2+I_3)+\tfrac12(I_1^2+I_2^2+I_3^2),\\
V(\theta)&=\cos(2\pi\theta_1)+\cos(2\pi\theta_2)+\cos(2\pi\theta_3)\\
&\quad+\cos(2\pi(\theta_1-\theta_2))+\cos(2\pi(\theta_2-\theta_3)),\\
H_\kappa&=h+\kappa V.
\end{aligned}
\]

The mathematical witnesses are transparent: Hessian Id, `Mc=3` because the
maximum-norm iterated bilinear norm is 3, coordinate derivative bound 13/4,
frequency components greater than 1 on B∞(0,1), and greater than 3/4 on the
larger real domain. The perturbation norm is at most
`κ[3 cosh(π/2)+2 cosh(π)] < 31κ` for κ>0.
There are six action monomials and ten signed Fourier keys, not a large torus array.

A 90-digit arithmetic scout using the literal landed formulas gives

| Quantity | Value, rounded for display |
|---|---:|
| r₀ | 3/12992 ≈ 2.3091133 × 10⁻⁴ |
| A | 616 |
| E=ε₀ | 1.15731149 × 10⁻³⁰ |
| C | 0.0365838566 |
| c | 7.74378074 × 10⁻⁷ |
| T₀ | 94864/39 ≈ 2432.41026 |
| Drift at ε=E | 3.74856055 × 10⁻⁷ |

| κ | ε=31κ admissible? | Drift from `head` | log₁₀ of certified-formula time | Direct derivative time at that same drift |
|---:|---|---:|---:|---:|
| 10⁻³⁰ | No | — | — | — |
| 10⁻³⁶ | Yes | 6.48 × 10⁻⁸ | 3.576 | 3.44 × 10²⁷ |
| 10⁻⁴² | Yes | 6.48 × 10⁻⁹ | 5.284 | 3.44 × 10³² |
| 10⁻⁴⁸ | Yes | 6.48 × 10⁻¹⁰ | 22.361 | 3.44 × 10³⁷ |
| 10⁻⁶⁰ | Yes | 6.48 × 10⁻¹² | 1900.865 | 3.44 × 10⁴⁷ |

The derivative comparison uses `‖İ‖∞ ≤ 6πκ` and the same continuation margin.
Thus “exponential time” need not mean a useful improvement at the threshold.
These decimal evaluations are **not interval-certified or Lean-checked**.

A precise first Lean instance can avoid the decimals altogether. Propose:

\[
\kappa=10^{-60},\quad \varepsilon=31\,10^{-60},\quad
x=1/40000,\quad \Delta=10^{-11},\quad L=10^{500}.
\]

With Q=7, u=2, k=1/16 and N=1661, the lower threshold is exactly

\[
\underline E=3/6478289759380182686275192487936.
\]

All four rational inequalities
`ε ≤ underline E*x^6`, `d*x ≤ 10⁻¹¹`,
`10^500 ≤ (94864/39)*2^1661`, and `1661 ≤ (1/16)/x`
passed exact Python `Fraction` comparisons. The requested lifetime integer has
1661 bits; the result does not require storing `exp(10^1900)`.
The proposed theorem covers every angle and `‖I₀‖∞<1/2`, gives unique solutions
through |t|≤10⁵⁰⁰, and action drift ≤10⁻¹¹. Time is dimensionless, not years.
Its purpose is a full checker demonstration; the tiny perturbation is not a physical claim.

The scout took 0.05 s wall time, 0.03 s user CPU and 16,024 KiB peak RSS under
`/usr/bin/time`. Budget **1–10 kernel CPU-hours**, 200–500 arithmetic bits normally,
<2,000 bits for this time literal, <10 MB initial data, and <8 GB per Lean process
for the eventual pilot. These are acceptance allocations, not measured Lean costs.
First measure loading plus one complete arithmetic leaf before accepting them.

For the same quadratic family with Mc=n and the other scalar bounds unchanged,
E is approximately 3.35×10⁻⁴¹ at n=4, 1.94×10⁻⁶³ at n=6 and 6.32×10⁻⁸⁷ at n=8.
These are norm thresholds, not planetary mass limits. They expose the deterioration
of this particular sufficient bound; they do not measure optimal Nekhoroshev stability.

## 3. A2: a general steep theorem with its actual constants

### 3.1 Meaning of steepness

On `Fin n → ℝ` use the explicit Euclidean dot product and norm. A plane is a
`Submodule ℝ (Fin n → ℝ)` with `Module.finrank ℝ Λ = j`. Its projector is the
existing `proj Λ`, consumed through `projection_exists_unique` and `proj_spec`.
If a new frozen steepness definition mentions that implementation, freeze its
meaning-carrying closure too, or use the following equivalent inline quantification
over every self-adjoint idempotent linear map P with range Λ.

For each I∈U, integer 1≤j<n, Λ⊂ω(I)⊥ of dimension j, and 0<ξ≤r, require

\[
\exists\eta\in[0,\xi],\quad
\forall v\in\Lambda,\quad \|v\|_2=\eta\Longrightarrow
\|P\omega(I+v)\|_2\ge C_j\xi^{\alpha_j}.
\]

Include a **uniform positive lower bound** on ω over U, not merely pointwise
nonvanishing: `∃ w>0, ∀ I∈U, w ≤ ‖ω(I)‖₂`; A-STEEP uses w=wLower.
Guard the gradient by C¹ regularity on the real tube; the headline supplies this
through holomorphy. This is the attained-max/min form of GCB (3),
not the stronger claim that the bound holds at **every** radius or in every direction
separately with a different radius. Prove equivalence using compact unit spheres
and continuity before approving the definition. No `sInf` of an empty sphere and
no arbitrary projector choice may change its meaning. Use
`α,C : Fin (n-1) → ℝ`, with position j−1 representing the source index j.
The parameters satisfy αⱼ≥1, Cⱼ>0.

For complex vectors use `sqrt (∑ i, ‖z i‖ ^ 2)` as the Hermitian norm,
again on the coordinate carrier. Let
`U_r = {z : ℂⁿ | ∃ I∈U, ‖z - complexify I‖₂ ≤ r}` and
`U^{-d} = {I∈U | ∀ J, ‖J-I‖₂ ≤ d → J∈U}`.
The closed-ball erosion is essential. Do not substitute the existing maximum-norm
`innerCore` without a proved √n conversion.

### 3.2 Complete quantitative assumptions

Fix n≥3, the indices α, and positive
`r,s,C₁,…,Cₙ₋₁,wLower,wUpper,M,F` **before U,h,f,ε or initial data**.
Use nonempty open U; require h holomorphic on an open neighborhood of U_r,
real on the real slice, and f holomorphic on an open neighborhood of
`U_r × {θ : |Im θᵢ| ≤ s/(2π)}`, real on reals and period one.
Here f is the normalized perturbation; the physical Hamiltonian is `h+εf`.

The precise conversion to the source is

\[
\phi=2\pi\theta,\quad
\widetilde H(\phi,I)=2\pi H(\phi/(2\pi),I).
\]

It preserves physical time. Apply the source with `ω=∇(2πh)` and require:

- quantitative steepness in §3.1 for 2πh on U with radius r;
- `wLower ≤ ‖ω(I)‖₂ ≤ wUpper` for all I∈U;
- `‖ω(z)-ω(z')‖₂ ≤ M‖z-z'‖₂` for **all** z,z'∈U_r;
- the source Fourier norm of `2π f(φ/(2π),I)` is at most F:
  `2π ∑_k (sup_{I∈U_r}|f_k(I)|) exp(s|k|₁) ≤ F`, with each supremum
  meaningful and finite and the nonnegative series summable.

The last is a **sum of suprema**, as on GCB p. 4. Pöschel's p. 190 norm has the
supremum outside the sum. The former bounds the latter; they must not be identified
by definition. A finite Fourier–Taylor majorant supplies the stronger norm directly.

For all these inputs use the formulas below with the common upper bound F replacing
`|f|_{r,s}`. For 0<|f|≤F, the source constants scale as
`ε₀ ∝ F⁻¹`, `R₀ ∝ F^b`, `c ∝ F⁻ᵃ`, `T ∝ F⁻¹ᐟ²`.
Thus this substitution decreases thresholds/times and increases the drift/erosion
radius, and is a valid uniformization. Prove it explicitly; f=0 uses the integrable
branch. Merely citing an existential theorem for fixed f would not give these quantifiers.

### 3.3 Literal constant map and conclusion

Using source indices 1,…,n−1, set

\[
p_j=\prod_{k=j}^{n-2}\alpha_k,\quad q_j=np_j-j,\quad
\beta_j=\alpha_j+j(\alpha_j-1)\quad(1\le j\le n-2),
\qquad a=(2np_1)^{-1},\quad b=a/\alpha_{n-1}.
\]

For 1≤j≤n−1 define

\[
\kappa_j=\frac{w_L}{M}(C_j/w_L)^{1/\alpha_j}
+4\left(\frac{2(2w_U+Mr)}{w_L}\right)^{1/\alpha_j},
\]
\[
\mathcal E=\max\left\{4,
\max_{1\le j\le n-2}
\left[\frac{(4M\kappa_j)^{\alpha_j}6^{q_j(\alpha_j-1)}}
{C_j(w_L/(2\sqrt2))^{\alpha_j-1}}\right]^{1/\beta_j}\right\}.
\]

Then GCB (9) becomes

\[
\varepsilon_*=
\frac{w_L^2}{2^8 6^{4np_1-5}\mathcal E^{2np_1-1}MF},
\]
\[
\varepsilon_0=\varepsilon_*\min\left\{
\left(\frac{6\sqrt2 Mr}{nw_L}\right)^{1/b},
\left(\frac{18\sqrt2}{n}\right)^{1/b},
\left(\frac{r}{4n\kappa_{n-1}}\right)^{1/b}
\left(\frac{12\sqrt2\mathcal E C_{n-1}}{w_L}\right)^{1/a},
(s/6)^{1/a},1\right\},
\]
\[
\begin{aligned}
\mu_0&=\max\left\{\frac{w_L}{24\sqrt2 Mr},\frac1{6^2 2\sqrt2},
\frac{\kappa_{n-1}}r
\left(\frac{w_L}{12\sqrt2\mathcal E C_{n-1}}\right)^{1/\alpha_{n-1}}\right\},\\
R_0&=rn\mu_0/\varepsilon_*^b,\qquad
c=\varepsilon_*^a s/6,\\
T_0&=\frac{s}{24\sqrt2}\frac{w_L}
{M(6\mathcal E)^{1/a}\sqrt{\varepsilon_*}F}.
\end{aligned}
\]

**Proposed A-STEEP:** for every admissible U,h,f as above, every
`0<ε<ε₀`, every θ₀ and every `I₀∈U^{-2R₀εᵇ}`, exhibit a solution in U through

\[
|t|\le L_\varepsilon=T_0\varepsilon^{-1/2}\exp(c\varepsilon^{-a}),
\qquad \|I(t)-I_0\|_2\le R_0\varepsilon^b.
\]

State existence, two-sided endpoint derivatives and agreement with every other
solution on each smaller symmetric interval exactly as in §2.2, now with action
domain U. Supply a separate ε=0 all-time integrable theorem. The source's
`ε⁻¹ᐟ²` prefactor, strict ε<ε₀, and closed-ball erosion are retained.
The maximum-norm conclusion is an immediate weaker corollary; no silent norm change.

**Frozen surface:** A-STEEP, the literal quantitative-steepness definition, and
one literal constant-map definition for (ε₀,R₀,T₀,c), together with any new domain/
norm meanings actually referenced. If imports already provide frozen meanings,
reuse them. Do not freeze the lattice toolkit, every auxiliary constant, or the
certificate format. These formulas and binders are Lean-ready mathematics, not
elaborated final Lean commands; exact commands and independent review precede approval.

### 3.4 Internal proof obligations and a non-quasi-convex test

| Internal work | Source/proof and expected reuse |
|---|---|
| Projectors, angles, restricted gradients, attained radial minimum | GCB (3), Appendix A; extend the existing coordinate projection library |
| Constant inequalities and resonance scales | GCB (6)–(9), §2.1, Appendix B; isolate real arithmetic from exp/rpow |
| Resonance cover indexed by maximal integer lattices | GCB §2.2; reuse N lattices, ranks, covolumes and finite cutoffs |
| Fast-drift component diameter | GCB Lemma 2.1, notably (45); new steep argument through possible folds |
| Small divisors on extended blocks | GCB Lemma 2.2; new scales with existing integer geometry |
| Non-overlap of same-rank extended blocks | GCB Lemma 2.3; major new topological obligation |
| Local normal form with exponential tail and controlled chart | GCB §3 / Pöschel p. 192; adapt `Nekhoroshev/NormalForm`, with explicit norm conversion |
| Exit decreases resonance rank | GCB Lemma 3.1; prove as a stopped intermediate lemma |
| Finite resonance descent and global time | GCB §4; rank induction, then N's ODE continuation/uniqueness |
| Arithmetic/finite-expression certificate | Follow A1 only after the theorem and a sufficient steepness witness are proved |

Do not assume “blocks have bounded diameter”, “the trajectory stays in its chart”
or “the normal form has a small remainder” in A-STEEP. Those are internal theorems.
Ordinary nonzero Hessian determinant and Rüssmann nondegeneracy are not steepness.

A small explicit test separates A2 from A1:

\[
h_4(I)=I_1+\tfrac12 I_1^2+\tfrac14 I_2^4+\tfrac14 I_3^4,
\qquad U=(-1/4,1/4)^3,\quad H=h_4+\varepsilon V.
\]

At I=0 the transverse Hessian vanishes, so no positive uniform quasi-convex m
exists on U. Nevertheless, for `‖v‖₂=u≤1`, the identity

\[
((x+v)^3-x^3)v=3v^2(x+v/2)^2+v^4/4
\]

gives `(∇h₄(I+v)-∇h₄(I))·v ≥ u⁴/12`. On a plane orthogonal to
∇h₄(I), Cauchy–Schwarz therefore gives
`‖P∇h₄(I+v)‖₂ ≥ u³/12`. This works at η=ξ and proves steepness
with α₁=α₂=3, C₁=C₂=1/12 and r=1/4. This elementary sufficient witness
is preferable to sampling planes or promising a general steepness decision algorithm.

For the time-preserving 2π conversion, valid conservative source data are
`wL=4, wU=8, M=7, C₁=C₂=1/2, r=1/4, s=1, F=150`.
Indeed `2π(3e+2e²)<150`. The complex domain is convex and its Hessian norm
is at most 2π, so M=7 is valid. A fresh formula scout gives

| Quantity | Value |
|---|---:|
| a, b | 1/18, 1/54 |
| κⱼ, script-E | 8.56735, 8281.075 |
| ε* | 1.108 × 10⁻⁹⁵ |
| ε₀ | 1.942 × 10⁻¹⁶⁰ |
| R₀, c, T₀ | 56.6898, 8.842 × 10⁻⁷, 9.899 × 10⁻⁴² |
| Limiting drift as ε approaches ε₀ from below | 1/16 |
| Limiting log₁₀ lifetime | about 325.40 |

The strict endpoint is not an admissible instance. This is unverified numerical
planning evidence plus a mathematical witness sketch, not a Lean certificate.
The polynomial witness should need 0.5–1.5k Lean lines and little numerical data;
the general steep theorem, not the example arithmetic, is the expensive part.
A general polynomial steepness checker, genericity, Gevrey regularity and sharper
stability exponents are separate later projects.

## 4. Applications ranked by scientific value and readiness

The ranking combines what would make a strong result with an honest path to it.
Allocation ranges below are speculative until a representative kernel leaf is measured.

| Rank | Exact intended claim and audience | Existing rigorous/numerical evidence | Feasibility and decision |
|---|---|---|---|
| 1: launch | The §2.4 Hκ, every angle and `‖I₀‖∞<1/2`, drift ≤10⁻¹¹ through abs(t)≤10⁵⁰⁰ | Existing `head` supplies the theorem once finite hypotheses are checked; fresh scalar checks above | A1 checker users and formal-methods researchers. 4–10k Lean plus 0.5–1.5k Python overall; 1–10 kernel CPU-h for the instance; <8 GB. A reusable demonstrated interface, not a realistic perturbation threshold |
| 2: broader theorem | A-STEEP for every analytic input in §3, with the quartic H₄ as a positive-volume example excluded by A1 | GCB16 is rigorous; the quartic witness is elementary. No chaos claim for that example | Strongest self-contained A result for Hamiltonian analysts. Another 30–70k Lean, 0.5–2k Python; 16–36 worker-weeks; small arithmetic pilot 1–20 CPU-h. Adopt for generality, not because it promises observed-planet masses |
| 3: joint flagship with B/D | In a fixed, symmetry-reduced planar giant-planet secular Hamiltonian and a published positive-volume chart box Q, unique solutions with stated action/eccentricity bounds for 5×10⁹ yr | GLS17 computes a candidate SJSU neighborhood; its computation is not a rigorous certificate | Plausible research application after normal-form remainder and steepness/convexity checks. Target source-scale radius near 10⁻⁷ first; 100–1,000 kernel CPU-h only after a successful shard. Model/coordinate work shared with B/D, not included in A1's estimate |
| 4: full planetary test at scaled masses | All data in an explicitly chosen planar low-AMD box for a specified Sun–Jupiter–Saturn Hamiltonian, safe through 5×10⁹ yr, at a certified mass bound | N/P qualitative theorem is already sealed; BN18 supplies a sharp periodic-averaging comparison | Useful calibration of quantitative D1, but not a direct A1/A2 application to Kepler's degenerate full action space. Expect a separate 10–25k Lean quantitative planetary effort; actual mass feasibility remains open |
| 5: long-term destination | A certified good subset of a fixed inner-planet uncertainty region, with explicit measure fraction, surviving 5 Gyr in a specified spatial relativistic or forced secular model | Numerical evidence of slow transport and rare escape; no qualifying certified region established here | Not a deliverable of A alone. Needs C/D, model reduction/error control and possibly a forced P-steep extension. No credible full kernel runtime estimate yet |

For rank 3, [GLS17](https://arxiv.org/pdf/1702.04894v1), §3.3 and §5/Fig. 3,
reports an intermediate **94,109,751 monomials** and roughly 10¹⁰ yr for a radius
slightly below 10⁻⁷, against an approximate uncertainty scale 7×10⁻⁷. The authors
explicitly distinguish their calculation from a rigorous computer-assisted proof.
The chart and the meaning of those radii must be reconstructed before selecting Q.
Even a hypothetical 32–64 bytes per monomial is 3.0–6.0 GB before indexing and
working arrays; Python object storage will be larger. A complete expansion cannot
be the first under-4-GB Python experiment. Stream degree blocks and bound tails.

Planar SJSU has three secular degrees of freedom before angular-momentum reduction,
two after fixing AMD and quotienting the common angle. Do not advertise it as a
three-effective-degree example solely from its unreduced count. A reduced planar
four-giant secular system has three, but needs a new model scout; see
[the reduction in MG08, §3](https://arxiv.org/pdf/0803.3246v1).

For rank 4, [BN18, §5.1, Tables 1–3](https://arxiv.org/pdf/1810.05987v1)
is an especially useful warning. The 10⁻¹¹·²⁵ row gives 5.75×10¹⁰ yr with initial
fast actions **exactly** at the 5:2 resonance. It is not a positive-volume box.
The table with a nonzero initial fast-action radius instead gives 1.99×10¹⁰ yr at
10⁻¹⁴, 3.04×10⁹ yr at 10⁻¹²·²⁵, and 1.04×10⁹ yr at 10⁻¹¹·⁵.
These are source calculations to reproduce and enclose, not automatically kernel
certificates. The displayed widths are around 10⁻⁶ of the resonant action scale.

Do not choose LG00 as the headline of A: its system has two degrees of freedom,
LG00 already gave rigorous tori, and the repository's exact first-order secular SJS
box already has an all-time theorem. Adding a dummy action to meet n≥3 introduces
flat directions; it does not create a valid steepness example. LG00 remains a useful
small arithmetic and coordinate test for the shared tools.

## 5. Solar System verdict

**Plausible with this program:** finite-time drift certificates for explicit
low-dimensional near-integrable models, including resonances and all angles; small
normal-form neighborhoods in a selected secular giant-planet model, jointly with B/D;
and a curve showing lifetime versus region size and perturbation size. A 4.6–5-Gyr
number is plausible only after the time unit, chart, initial set, observables and all
tails are fixed and the inequalities actually close. An extremely tiny neighborhood
or artificially reduced masses must be labeled as such.

**Plausible only after additional mathematics/verification:** full planar SJS at
actual masses; the full spatial giant-planet problem; a physically substantial
inner-planet region. Some required mathematics is known but not formalized or not yet
effective for this input. Other required improvements in bounds or resonant geometry
may genuinely be new. A should not promise which of these will suffice before a scout.

**Not plausible as a direct A1/A2 conclusion:** all observed inner-planet uncertainty
sets confined for 5 Gyr merely because planet/Sun mass ratios are small; all-time
confinement of every orbit in dimensions ≥3; or a 99% probability statement obtained
from an all-data deterministic theorem without a proved initial measure/cover.

The first secular application is the **planar Sun–Jupiter–Saturn–Uranus** model
of GLS17, or a separately reconstructed four-giant model adding Neptune. An inner
candidate should explicitly name **Mercury, Venus, Earth and Mars**, include spatial
eccentricity/inclination variables and the relativistic perihelion term, and specify
whether Jupiter, Saturn, Uranus and Neptune are prescribed quasiperiodic forcing or
coupled dynamical variables. These are different Hamiltonian problems.
An observed uncertainty set needs a named ephemeris and epoch, enclosed input
uncertainties and a certified coordinate image. No such set is supplied by this plan;
the GLS17 radius comparison does not define an inner-planet uncertainty region.

The concrete obstacles are these.

- **Proper degeneracy.** `hKep(Λ) = -∑ cᵢ/(2Λᵢ²)` is independent of eccentricity
  and inclination actions. Along a slow-action direction the projected gradient
  stays zero. Both quasi-convexity on the full action space and steepness fail.
  Averaging and a secular normal form may repair this on selected regions, but their
  curvatures, remainder and domains carry their own small factors. An invertible
  KAM twist does not establish steepness.
- **Actual masses.** The repository's cited model uses Jupiter/Sun = 0.0009546
  and Saturn/Sun = 0.0002856, as in
  [FH25 §4](https://arxiv.org/pdf/2403.10152v1). Those are about eight orders above
  the 10⁻¹¹·²⁵ comparison scale, before correcting the initial-region mismatch.
  A perturbation norm after scaling/normalization is not numerically equal to a
  mass ratio. Inner planets have smaller masses, but their slow secular curvature
  and resonant denominators are small too. No inference from a mass ratio alone is valid.
- **Mercury and relativity.** The important secular resonance is g₁−g₅; relativistic
  perihelion precession changes access to it. Numerical ensembles give roughly 1%
  high-eccentricity instability over 5 Gyr, with a Lyapunov time near 5 Myr.
  This is not a theorem of a 1% collision probability or a measure bound for an
  ephemeris box. [ML21, §§6–8 and Appendix C](https://arxiv.org/pdf/2105.14976v1)
  discusses the 2,501-run LG09 ensemble and the forced model comparison.
- **Truncation and forcing.** Degree-four secular stability can miss the degree-six
  interactions responsible for much of the numerical 5-Gyr instability.
  [HML22, Table 1 and §4](https://arxiv.org/pdf/2205.04170v1).
  A prescribed quasiperiodic outer forcing is not an exact reduction of the full
  coupled system; physical energy and AMD need not be conserved by that subsystem.
- **Diffusion and observables.** In ≥3 effective degrees of freedom a Lagrangian
  torus need not separate an energy surface. Nekhoroshev bounds allow later Arnold
  diffusion; they do not prove any particular orbit chaotic or diffusing.
  Small semimajor-axis drift alone does not prevent eccentricity growth or collision.
  Coordinate and AMD/separation bounds from D, or boundaries from C, remain necessary.

A relevant update to the source landscape is
[Bambusi–Barbieri–Giralt–Langella, June 2026, Theorem 2.3](https://arxiv.org/pdf/2606.30841v1):
a preprint extending the steep-resonance construction to quasiperiodic forcing under
**P-steepness** and a Diophantine forcing vector. For n physical actions, m forcing
angles and exponents α₁,…,αₙ, it gives
`a = 1/[2(α₁⋯αₙ₋₁)(n+1)(τ+1)]` and
`b = [1-n/((n+1)(τ+1))]/[2α₁⋯αₙ]`.
This is a possible later A3, not something A2 already proves. Adding m dummy
conjugate actions to an autonomous steep theorem fails in flat forcing directions.
Before adopting A3, audit its actual P-steepness premise and the issue in §8 below;
no inner-planet coefficients or constants have been verified for it.

The honest best case for the inner system is therefore a rigorously defined reduced
model, selected small regions or a certified good-set cover, and a useful finite
lifetime allowing chaotic motion. Approximate invariants identified numerically by
[MHL23](https://arxiv.org/pdf/2305.01683v1) suggest C as a complementary route.
The full observed spatial system and its complete uncertainty region remain a research
program, not an advertised consequence of formalizing GCB. A 5-Gyr theorem for a
fixed Newtonian/relativistic model also does not include stellar evolution, tides or
external encounters unless they are explicitly part of the stated model.

## 6. Ordered work packages, experiments and calendar

All sizes are incremental handwritten lines, usually uncertain by a factor of two;
data and proof artifacts are separate. Do not add the overlapping A/B/C/D estimates.

| Package | Inputs → outputs | Estimated size and elapsed allocation | Check / stop condition |
|---|---|---|---|
| A-P0: approve the small surface | Frozen N statements, `head`, §2 → exact A-QC-WINDOW review commands and source/binder table | 0.2–0.5k proposal/probe lines; 1–2 days | Independent review; owner approves exact text before any new frozen anchor or provider assignment. Stop on a mismatch, do not edit N-HEAD-C |
| A-P1: rational constants | Landed formulas → executable scalar witness checks and ordinary soundness lemmas | 0.8–1.5k Lean, 0.2–0.5k Python; 2–4 days | Compare at 90/160 digits, exact rational pilot, prove positivity and correct inequality directions; first leaf <8 GB |
| A-P2: finite analytic inputs | Expression syntax → derivative, frequency, QC and norm checks | 2–4k Lean, 0.3–0.7k Python; 1–2 weeks | One-cell quadratic and at least one nonconstant example; malformed/cell-gap/incorrect-norm inputs rejected. No sampled-QC surrogate |
| A-P3: QC assembly and pilot | Approved root, A-P1/A-P2 → checker soundness, translated-box adapter, §2.4 instance | 1.2–3k Lean, 0.1–0.3k Python; 3–5 days | Lint, narrow builds, standard-axiom receipt, kernel evaluation of the literal input, independent end-to-end audit. Target 1–10 CPU-h for data |
| A-P4: usefulness decision | T(ε,R,s) and direct-bound comparison → decide constants optimization versus steepness | <0.5k Python; 1–2 days | If no agreed interesting example improves a direct bound at useful parameters, label the A1 interface infrastructure and redirect application work to B/C |
| A-P5: steep surface and witness | GCB, source corrections, §3 → exact steep anchors, source graph, quartic witness | 2–5k Lean plus 0.3–0.8k Python; 1–2 weeks | Independent norm/quantifier audit and owner approval. Detect failure of QC and prove steepness for the quartic; no grid of planes |
| A-P6: steep geometry | A-P5 and existing lattice APIs → Lemmas 2.1–2.3 | 15–35k Lean; 4–10 weeks | Each source lemma proved from source premises, default heartbeats; independent non-overlap/topology audit. Stop if an unproved geometric claim has entered a hypothesis |
| A-P7: steep normal forms and descent | A-P6 plus N analytic theorem → A-STEEP and zero/uniqueness branches | 10–22k Lean; 3–6 weeks | Exact constant map, both time directions, nonvacuous inner domain, full frozen identity and axiom audits |
| A-P8: steep certificate/application | A-P7 plus sufficient algebraic witness and optional B normal form → a checked non-QC instance | 3–8k Lean, 0.5–1.5k Python; 1–3 weeks | Representative data shard before allocating 100+ CPU-h; no claim of a general steepness decision procedure |

Package labels A-P0–A-P8 denote work order. Program A1 is the quasi-convex
interface; program A2 is general steepness; a possible A3 is the forced extension.

With one principal writer and an independent reviewer, budget **2–4 calendar weeks
for the A1 program**, with first numerical gates in 1–2 days. For general steepness,
allow **8–18 further calendar weeks** with two bounded proof workers and a reviewer,
or roughly 16–36 worker-weeks; this is a planning range, not an agent-speed promise.
Abstract interface and integration checks may need tens to hundreds of cumulative
CPU-hours. A full clean rebuild is neither required nor budgeted. No planetary date
should be committed until the radius/time scout and one kernel leaf pass.

Every feasibility experiment below has a **hard ceiling below one CPU-hour** and
Python RSS <4 GB. Cutoffs are stop rules, not targets to exceed:

| Experiment | Budget | Output and go/no-go evidence |
|---|---:|---|
| E0: scalar reproduction | 5 CPU-min | Mirror exact `HeadParams` formulas, 90/160-digit agreement, rational witness comparisons; this task's 0.03-CPU-s pilot is the first result |
| E1: useful domain/width sweep | 15 CPU-min | ≤1,000 choices of R,s and certified coarse h bounds; rederive every bound when changing the domain; output log lifetime, drift and direct-time ratio. Reject ε outside cutoff |
| E2: witness validation | 10 CPU-min | Symbolic quadratic derivatives, quartic identity, one nonconstant interval-QC cell. Try a negative curvature direction and a missing cell. Success means exact bounds, not a sampled minimum |
| E3: data scale forecast | 15 CPU-min | Stream 10²/10³/10⁴ coefficient records with 128/256/512-bit enclosures; count operations, bits and bytes. No dense high-dimensional FFT or whole GLS17 expansion |
| E4: first kernel leaf, in the later implementation task | 30 CPU-min, <8 GB | One small leaf and its imports at default settings; then one complete scalar/analytic pilot if it fits. Stop on 8 GB, heartbeat failure or an estimated >10 CPU-h pilot; redesign before scaling |
| E5: optional B/D model intake | 45 CPU-min | On a bounded low-order secular jet, test a rigorously enclosed Hessian/jet and a coarse full remainder budget. Failure of a sufficient QC test is not proof of non-steepness. Report missing data, do not fabricate a planetary threshold |

E4 was **not run in this planning task**: PROGRAM-A prohibits Lean builds and allows
at most one tiny <2-GB probe. The later implementation brief must carry the proper
resource authorization. Use the compile gate; never run concurrent Lake builds.

### Brief 1, ready to hand off: A-P0 — source and declaration packet

**Objective:** make A-QC-WINDOW in §2.2 precise enough for approval, without changing
any frozen file. Read AGENTS.md, PLAN, DECISIONS, this plan, the seven cited frozen
N definitions, `Interfaces/Constants.lean`, `Assembly/Headline.lean`, the source
packet and Pöschel pp. 190–191. Work in an isolated assigned worktree.

**Deliver:** a review packet containing the complete intended Lean command (inline
constants, full binders and agreement clause), expanded meaning-carrying definitions,
a source-to-binder table, the algebra proving `eps0=E`, and a proof-dependency list.
Use a temporary `#check` of the proposed proposition if permitted; no unauthorized
placeholder theorem may be added. Distinguish a checked proposition type from an
elaborated final declaration. The orchestrator arranges independent statement review,
shows the complete command to the owner, and only then freezes it. If final-command
elaboration needs the approved draft location, record that explicitly before freeze.

**Boundaries:** source/design work only; no new frozen anchor, provider, generated
root, manifest, README or other program file. Expected ≤500 lines of proposal/probe
text and ≤200 Python lines. If the existing theorem cannot supply the stated endpoints,
domains or uniformity, report the precise mismatch; do not strengthen its premises.
No proof assignment against a changing source-facing statement.

**Acceptance/handoff:** exact proposed command, whether/how it was elaborated, pinned
source hash and locations, every norm/period factor, uncertainties/errata, and the
explicit approval decision still needed. No passing numerical or kernel result is
implied by this source packet.

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

### Brief 2, ready to hand off: A-P1 — rational scalar engine

**Objective:** implement the scalar checks of §2.3 as ordinary arithmetic helpers,
independent of a new frozen theorem's proof. Read the same repository instructions,
`HeadParams` and `const_size`, and this plan. The allowed area is new focused modules
under `KAM/Nekhoroshev/Certificate/Scalar/` and a small producer under a separately
assigned `scripts/nekhoroshev/` path. Do not touch A-P0's files or any shared certifier code.

**Deliver:** a finite rational witness type and Boolean checker; soundness proving
`0<Elo≤E`, `d*x≤Δ`, `ε≤E*x^(2*n)` and `L≤T₀*exp(K/x)` from an accepted witness;
optional Ĉ,ĉ,T̂,ε̂₀ output with the four enclosure directions in §2.3. Separate pure
rational identities from real exp/rpow lemmas. Start with Q≥1+4/(3s), `u²≥n`,
`k=s/(2u)` and `N≤k/x`; do not implement a transcendental optimizer first.
Use balanced small arithmetic declarations and an untrusted Python producer.

**Checks:** reproduce the exact §2.4 rational inequalities; malformed dimensions,
zero widths, negative lower bounds, reversed threshold comparison and an insufficient
time exponent must be rejected. Use kernel reduction only for closed finite checks.
Run one targeted `nice -n 5 lake build KAM.Nekhoroshev.Certificate.Scalar.Soundness`
at a time once that module exists, under an 8-GB watchdog, followed by source lint.
Print axioms for the main ordinary soundness result from an approved scratch probe;
only `propext`, `Classical.choice`, `Quot.sound` are acceptable. Record exact outputs,
peak RSS, CPU time, artifact size and imports. Do not assert the dynamical pilot yet.

**Size/time and stops:** 0.8–1.5k Lean split across small modules; 200–500 Python
lines; 2–4 working days. The first arithmetic leaf gets at most 30 CPU-min. Stop and
report a default-heartbeat failure, >8-GB memory, or a dependence on a draft/provider.
The mathematical root and analytic input checker are separate consumers, not premises
hidden inside the scalar record.

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

### Owner decisions prepared by this plan

These are recommendations for the next launch, not questions blocking this document.

1. Approve A1 as the immediate engineering deliverable, including the tiny-perturbation
   pilot, and assess its utility using the direct-time comparison.
2. After the source packet, approve the **exact** A-QC-WINDOW Lean text. Later approve
   the exact A-STEEP and meaning-carrying definitions; do not approve them merely from
   the names or this Markdown schema.
3. Choose whether the next main result is general steepness (A2) or useful planetary
   bounds via B/C/D. Recommendation: A2 only if broad theorem coverage itself is a priority.
4. For an application, fix the model, minimum initial-region size, observables and time
   before optimizing. Recommend a secular giant-planet model first; specify whether
   ≥3 effective degrees of freedom is required.
5. Keep the <8-GB kernel target and approve only a 1–10-CPU-h A1 pilot initially.
   A 100–1,000-hour planetary allocation requires measured samples. A larger process
   requires a different authorized resource; installed RAM does not override the guard.

## 7. Dependencies on B–D and the current applications

A1 depends only on the existing N theorem and numerical primitives. It need not wait
for a torus, a Diophantine proof, hybrid wiring, LG00, SO or SJS. A2 depends on the
source-approved steepness surface, N's normal-form machinery and new geometry;
no KAM theorem supplies that geometry.

**B → A:** a certified exact canonical change `H∘Ψ=N+R`, its domain and inverse,
its displacement, and the full analytic norm of R can turn a moderate original
perturbation into an admissible small remainder. A verifies QC/steepness of N and
applies its theorem on an interior region. B must supply control of a neighborhood,
not just an embedding of a torus. For finite time, an approximate torus defect can
be included in the remainder; an exact torus is not automatically necessary.
The coordinate-transfer drift has two chart-displacement contributions, one at
the initial point and one at the final point.

**A → B:** the steep theorem may become a module in a later superexponential
near-torus result. Quantitative *stable* steepness of a Birkhoff jet is an additional
premise to prove; A-STEEP does not silently supply it.

**C ↔ A:** C handles retained resonances and approximate integrals when a global
QC/steep test does not close. A can certify individual cells of a C good-set cover;
C owns finite cover measure and boundary escape checks. A1 is all-data on each
accepted region, with no probability model. Neither a Monte Carlo survival fraction
nor iteration of N's O(1/ε)-time averaging result supplies C's measure theorem.

**D ↔ A:** D owns the named planetary Hamiltonian, coefficient/ephemeris enclosures,
physical time scale, AMD/separation and coordinate reconstruction. A supplies a
proved bound only after the analytic hypotheses and required chart are certified.
The sealed planetary exponent is `2/(6n²-3n+14)`, with drift exponent 3a/2;
substituting A's 1/(2n) is not an authorized theorem. D's partial-convex quantitative
route can succeed or fail independently of A2.

**v2/hybrid/SO/LG00:** share dyadic balls, exact polynomial identities and measured
kernel costs. Preserve current lunar targets and its polar-chart route; do not add
A's normal forms as a prerequisite. LG00 has 69 rational monomials and an estimated
545–680-coefficient v2 torus at the scout settings; its projected 3–75 CPU-hours per
torus is not a measured complete certificate. Do not reinterpret Mercury spin
confinement in [next-demonstrations](next-demonstrations.md) as orbital safety.

**Full SJS:** the [existing scout](sjs-feasibility.md) projects 10,000–33,000 kernel
CPU-hours and 1–3.5 TB advice for one earlier per-slot route. Its 6–19-hour
hybrid/packed figure is an unimplemented extrapolation, not a current budget.
Some proposed products need 28–56 GB and FH25's numerical torus generation used
about 194 GB. None fits the current per-process policy as a single computation.
If such a route is chosen, generation needs an authorized ≥256-GB machine and
kernel products still need sharding or a separately authorized larger-process host.
A small successful A1 scalar certificate does not validate those estimates.

## 8. Sources, suspected defects, deviations and validation receipt

The sole repository deliverable is this file. Research data, scripts, extracted text
and rendered pages are under `/tmp/prog-a-astra/`; no downloaded content was executed.
No GitHub operation, Lean build or Lean probe was performed. No frozen file, manifest,
README, generated root, Lean source or dependency artifact was changed.

Pinned PDFs used directly (full SHA-256; `papers/sources.json` in scratch records
URLs and byte sizes):

| Source | SHA-256 |
|---|---|
| Pöschel journal scan | `27568ec63af069ab6d6c02e0327aa2d822998be47888f20dea0c6418552dc869` |
| GCB16 arXiv v1 | `7b89f25ed0e1b4815df095bac4af5095bff9e205287a6822f39a77122d44b176` |
| BN18 arXiv v1 | `b543c39ee7731b8b6b9cf229a3304ba6b6dd14058a3310d84871107283514815` |
| GLS17 arXiv v1 | `254d52fb9c545efe12cfcc4b138ac8b429c1e95aad0d63c12b4e6dfc182e1cae` |
| ML21 arXiv v1 | `7537e3b2536766d18fcf5db1844e9586eefba46318645373ee0ed532f9c32526` |
| HML22 arXiv v1 | `66a18c8fe1c24419172b163bf51170735d6016d7917133191a46a48c85038bc4` |
| MHL23 arXiv v1 | `c44419c0dfefba8492af1f648753d0ddd90313b64acffd31e56f8549a460d1c7` |
| FH25 arXiv v1 | `379c8b41b53a1fd50cbc890cca06d646ccd93f5c0d5e0226d1303885d2df7cf7` |
| MG08 arXiv v1 | `d7bf30d0db8bfe236506fd3eca8ae44de774f1b12f5d4d56b5aa8e65cd855177` |
| BBGL26 arXiv v1 | `d18bb2990d9928ee0683b53302cda6aeec1675ed9396ba340440d7a15f39e4b2` |

The mathematical statement pages of Pöschel, GCB and BBGL were also read as rendered
images. This is not an independent audit of their complete proofs.

**Source findings for the orchestrator's ledger; no ledger edits here:**

- Rechecked existing **E-N-GCB-1/2/3**: zero-ε time convention; p. 3's
  `α₁=…=αₙ=1` index; footnote 5's `|u|=Σᵢ|u₁|`, which is not a norm.
  Use the already recorded n−1 and sum-over-i corrections and a separate zero branch.
- Rechecked existing **E-N-POS-1**, printed p. 190: “For the symmetric operator Q
  this norm amounts to the spectral radius norm.” This fails for complex symmetric
  Q; the nonzero matrix `[[i,1],[1,-i]]` has square zero. Use the actual operator
  norm, as the frozen complex-Hessian predicate already does.
- **Candidate A-GCB-KAPPA**, GCB p. 5, (6)–(9): the introductory range
  “1 ≤ j ≤ n−2” is followed by κⱼ in (7), but (9) needs κₙ₋₁.
  This is at least a range ambiguity. Proposed transcription: apply that range
  to pⱼ,qⱼ,βⱼ and define κⱼ for 1≤j≤n−1. Have an independent source reader
  confirm this before freezing the constant map; it is not a refutation of the theorem.
- **Candidate A-BN-MASS**, BN18 §5.1, p. 40: “the ratio of their masses is close
  to 10⁻³”, immediately after naming Jupiter and Saturn. Their mutual mass ratio
  is not 10⁻³; a planet/Sun ratio is presumably intended. Check the actual
  Hamiltonian scaling in §3, rather than using this prose for a mass conversion.
- **Candidate A-BBGL-PSTEEP**, BBGL26 p. 5, after Definition 2.1:
  “convex and quasiconvex functions are P-steep”, with α₁=…=αₙ=1 in (2.4).
  For `h(I)=I₁+½∑_{j≥2}Iⱼ²` on a bounded neighborhood, ∇h is nonzero and its
  Hessian is uniformly positive on ∇h⊥, so it is strictly quasi-convex in the usual
  quantitative sense. But along Λ=span(e₁), `∇h(I+te₁)-∇h(I)=0` for every t,
  contradicting Definition 2.1's positive lower bound. This refutes the quoted
  implication, not Theorem 2.3 under its actual P-steepness hypothesis. Treat A3 as
  source-audit work; do not infer P-steepness from a QC certificate.

The new candidates have not received independent review. No new suspected defect
in an existing frozen declaration was found. Known source-ledger issues outside
these inspected passages were not re-audited.

**Declared adaptations:** period-one/time-preserving 2π conversion; explicit coordinate
Euclidean norms; a finite sufficient certificate grammar; uniform replacement of the
perturbation norm by F; separate zero branches; existence/uniqueness and endpoint
continuation; the rational-window corollary; and restricted pilot models. The positive
frequency lower bound and complex Hessian bound of A1 are existing approved inputs,
not newly added assumptions. All changes to a future frozen surface require the normal
exact-text approval; this plan changes none.

**Remaining uncertainties:** numerical usefulness after normal forms, domain size,
steep block geometry proof cost, sufficient steepness witnesses for planetary jets,
physical coordinate/time transfer, and kernel cost on real application data. No
success at actual planetary masses, 5-Gyr uncertainty-region theorem, chaos theorem
or complete numerical certificate is claimed here.

**Checks in this task:**

- `python3 -B /tmp/prog-a-astra/constants_scout.py` and the 160-digit variant:
  every reported mathematical field agrees; all four exact `Fraction` comparisons
  return `true`. Timed 90-digit run: `elapsed=0.05 user=0.03 sys=0.00 maxrss_KiB=16024`.
  Timed 160-digit run: `elapsed=0.03 user=0.03 sys=0.00 maxrss_KiB=16032`.
- `python3 -B /tmp/prog-a-astra/validate_plan.py`: 17 local links resolve; all ten
  Markdown tables (93 rows) have consistent columns; 21 math displays balance;
  both briefs contain the eleven hard rules verbatim; all ten PDF hashes and byte
  counts match; the symbolic quartic identity expands to zero. Initial full validation
  used `elapsed=0.24 user=0.20 sys=0.03 maxrss_KiB=65888`.
- `PATH="/tmp/prog-a-astra/bin:$PATH" scripts/lint_sources.sh`: **exit 1, partial
  check only**. A scratch Python wrapper delegates the source checks to the system
  interpreter with bytecode writes disabled, and deliberately refuses the ABI phase.
  Its exact output was:

  ```text
  check_lean_modules: PASS (1829 Lean files, 0 comparator configurations)
  FROZEN-ANCHOR GUARD OK
  ABI SKIPPED: PROGRAM-A prohibits Lean builds and repository scratch writes; no ABI probe authorized by this task.
  ```

  The ABI script writes `.lake/abi-scratch` and invokes `lake env lean` importing all
  frozen modules. That exceeds the brief's one tiny optional probe and its scratch
  boundary. No complete lint/ABI pass is claimed; no repository lint script was edited.
- No targeted build or `#print axioms` run: this task creates no Lean module or
  theorem, and its brief prohibits builds. New Lean axioms: **not applicable**;
  existing main results' axiom sets were not rechecked.
- `git diff --cached --check`: exit 0 before commit; only this document is staged.
  Uncertainties, source findings and deliberate mathematical adaptations are listed above.
