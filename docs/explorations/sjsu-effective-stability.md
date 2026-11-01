# Certified effective stability for secular SJSU: scope and prototype

1 November 2026. Branch `sjsu-scope`; inspected core commit
`2e64d027c2f0129bfd69171064f0e3f6531e056d`. Research and numerical scouting only.
This report freezes no declaration and proves no new Lean theorem.

**Recommendation:** pursue a small model-recovery and certificate pilot, with a
five-billion-year action-confinement theorem as a conditional research target.
Use finite approximate integrals, checked against the **entire chosen original
secular Hamiltonian**, followed by first exit and continuation. Do not commit to
the long-time instance until its coefficients, initial region and complete
derivative bounds are available.

The prototype recovers the 78 printed quadratic/quartic monomials of
Sansottera–Locatelli–Giorgilli (SLG13), computes normal forms through Cartesian
degree 10, and measures complete original-polynomial bracket majorants.
At nominal amplitudes its best tested confinement ratio is only **34,419 yr**;
the higher-order boundary tests fail. Estimates above \(10^{10}\) yr occur at
30% of the nominal amplitudes, which **excludes the nominal point**. These are
floating estimates for a separate degree-four model, not certified lifetimes
or a reproduction of the degree-18 calculation.

Two additional findings matter. The printed polynomial has an exactly nonzero
bracket with the standard quadratic AMD, considerably exceeding last-digit
rounding; the source's printed radii also disagree with its stated formula
and Table 2. Both are documented below as source issues requiring review.
The full degree-18 coefficients, averaged reference actions and near-torus
coordinate maps were not recovered. Their absence prevents a defensible
new \(10^9\)–\(10^{10}\)-year estimate at the real initial conditions.

| Evidence label | Meaning in this report |
|---|---|
| **proved** | Existing Lean result according to inspected source/handoff, explicitly distinguished from a fresh replay; or elementary mathematics with its argument given here. No new Lean result |
| **measured** | This task's exact rational arithmetic or floating computation, with the distinction stated |
| **estimated** | Proposed target, resource extrapolation, or engineering judgment |
| **literature** | A result/estimate attributed to the cited paper, with its rigor qualification |

## 1. Which model, and which published result?

The principal sources are [SLG13, *Mathematics and Computers in Simulation* 88,
1–14](https://doi.org/10.1016/j.matcom.2010.11.018),
[its versioned preprint](https://arxiv.org/abs/1010.2609v1), and
[GLS17, *Regular and Chaotic Dynamics* 22(1), 54–77](https://rcd.ics.org.ru/S156035471701004X/),
[preprint v1](https://arxiv.org/abs/1702.04894v1). The page numbers below identify
the journal-copy SLG13 or the 31-page GLS17 preprint, respectively.

**Literature.** SLG13 §§2–3 constructs a planar secular Hamiltonian in three
canonical pairs. It expands the Kepler term to quadratic order in translated
fast actions, the perturbation to linear order in those actions, slow degree
18 and fast Fourier degree 16. Its two-step averaging includes the 5:2 and 7:1
near-resonances and selected contributions from the three-body harmonic

\[
2\lambda_J-5\lambda_S,\qquad \lambda_J-7\lambda_U,\qquad
3\lambda_J-5\lambda_S-7\lambda_U.
\]

The construction is described as second order in the masses; equation (12)
also retains selected formal \(\mu^4\) terms from the latter harmonic.
It is not a complete fourth-order mass expansion. Appendix A prints only
degrees two and four. The equilibrium calculation uses normalization orders
through 30; its reported optimum at nominal amplitude is 16, with roughly
\(10^7\) yr (§4.3, Fig. 1). Its remainder multiplier is chosen as 2 rather
than supplied with a validated full-tail bound (§4.2). These facts do not
constitute a rigorous SJSU certificate.

**Literature.** GLS17 uses the degree-18 secular construction, then a local
torus normalization and a Birkhoff estimate near that torus. Its finite torus
calculation uses two 25-step algorithms, action degree five and Fourier degree
50 (§3.3); the subsequent majorant calculation runs through action order 20
(§4.3). Figure 2 estimates about \(10^{10}\) yr slightly below source action
radius \(10^{-7}\). Its comparison uncertainty scale is approximately
\(7\cdot10^{-7}\), without a certified coordinate enclosure. The numerical
calculation is explicitly not a rigorous computer-assisted proof; (58) keeps
only the first omitted remainder contribution. This is encouraging evidence
for a small tube, not a proved lifetime or a guarantee for an observational box.

These two orders and radii are different: degree 16 about the circular
equilibrium, degree 20 **in transverse actions** about a nonzero torus, and
degree 10 in our Cartesian prototype cannot be compared as one common K.
Nor can shrinking the eccentricities toward zero reproduce shrinking a tube
around the actual secular orbit. This distinction determines the recommendation.

### Reproducible model hierarchy

| Model | Definition/provenance | Present status |
|---|---|---|
| `SJSU4-table` | The 78 Appendix A decimals as exact rational coefficients, with higher degrees absent by definition | **measured:** complete transcription and prototype in this change |
| `SJSU18-source` | Full polynomial prescribed by the averaging recipe, with source reference actions and all degree-18 terms | Intended first substantial target; full data and some recipe choices missing |
| `SJSU18-rational` | A deliberately selected rational polynomial approximating a reconstructed degree-18 model | Possible alternative after explicit model selection; requires a stated coefficient-error policy |
| Untruncated secular average | Exact averaged Hamiltonian with analytic tails controlled | Additional theorem; neither of the preceding polynomials supplies it |
| Full Newtonian SJSU | Fast angles, semimajor-axis variation and indirect kinetic terms retained | Separate fidelity upgrade; no billion-year transfer established |

For the intended model the original coordinates are
\((\xi,\eta)\in\mathbb R^3\times\mathbb R^3\), with
\(\xi_i=\sqrt{2\Gamma_i}\cos\varpi_i\),
\(\eta_i=-\sqrt{2\Gamma_i}\sin\varpi_i\).
The repository phase ordering is **\(q=\eta,p=\xi\)**. Thus
\(\dot\eta=H_\xi,\dot\xi=-H_\eta\).
For the source's units, AU and year, \(G=1\) and \(m_0=4\pi^2\).
The mass ratios are the literal Table 1 values
\(1/1047.355,1/3498.5,1/22902.98\), not modern uncertainty enclosures.
Time is already in years. A later period-one conversion must transform both
members of an angle/action pair:
\(\theta=\varphi/(2\pi),J=2\pi I\).

**Data recovery gate.** Obtain or reconstruct the numerical values of
\(a_i^*\), hence
\(\Lambda_i^*=m_0m_i(m_0+m_i)^{-1}\sqrt{(m_0+m_i)a_i^*}\), from the
specified averaging procedure; the instantaneous Table 1 axes do not specify
these averages. Also obtain every retained coefficient, truncation order in
each Lie step, the linear diagonalizer and the initial-condition transformation.
For the GLS17 route add its finite torus embedding, translations/generators,
inverse substitutions, and the input majorant arrays. A frequency vector alone
does not reconstruct any of these objects. The papers and public searches did
not reveal a complete machine-readable release; no author was contacted.

An independent reconstruction can start from the moving-Sun heliocentric
Hamiltonian, derive Kepler/Poincaré series and Laplace coefficients with interval
tails, then perform the finite averaging algebra. Rational reference axes
chosen afresh would define a reproducible variant, requiring separate naming
and comparison. The 78-term table provides a useful low-order regression, but
its exact discrepancies below prevent treating its digits as certified
enclosures of a symmetry-preserving analytic derivation.

**Size, calculated here.** The often-quoted 94,109,751 terms belong to an
intermediate fast-angle expansion, not to the final six-variable polynomial.
The dense upper bound for even degrees 2–18 in six real variables is
\(\sum_{d=1}^9\binom{2d+5}{5}=76,713\). Reversibility (even total eta degree)
reduces that bound to 38,466. Exact common-rotation symmetry, in complex
coordinates, would allow at most
\(\sum_{d=1}^9\binom{d+2}{2}^2=7,941\) charge-balanced monomials.
These are combinatorial bounds, not a measured census of the missing model;
the symmetry reduction must be proved before using the last number.
Streaming pair interactions and harmonic convolutions should avoid retaining
the entire intermediate expansion. This is a generation strategy to benchmark,
not an implemented reproduction.

The model omits Neptune, the inner planets, inclination dynamics in its planar
form, and forces beyond its chosen gravitational approximation. Averaging also
removes fast dynamics. A high-degree eccentricity expansion cannot compensate
for missing bodies or missing mass orders. Its resemblance to secular Solar
System motion must remain a model-validation statement, not part of the formal
lifetime conclusion.

## 2. Proposed theorem and certificate mechanism

Fix the **whole** Hamiltonian \(H\), initial set \(Q\), bounded open working
region \(D\), literal polynomial observables \(F_1,F_2,F_3\), action and
eccentricity maps, and a rational time \(T>0\) before quantifying initial data.
Let \(\overline D\) lie in the regular domain. Prove \(Q\subset D\) and

\[
 a_j\le F_j(z_0)\le b_j\ (z_0\in Q),\qquad
 |\{F_j,H\}(z)|\le\eta_j\ (z\in\overline D).
\tag{1}
\]

Every boundary point must violate an enlarged initial range:

\[
\forall z\in\partial D,\quad\exists j:\quad
 F_j(z)<a_j-T\eta_j\quad\hbox{or}\quad b_j+T\eta_j<F_j(z).
\tag{2}
\]

**Elementary mathematical argument, not a new Lean proof:** along a stopped
solution, the chain rule and integration give
\(|F_j(z(t))-F_j(z_0)|\le\eta_j|t|\). A first boundary hit contradicts
(2). Compact containment and local Lipschitz regularity extend the solution
past both requested endpoints. Polynomial Hamiltonians provide that regularity;
bounded confinement supplies the missing global-existence ingredient.
The conclusion holds for **every** initial point in Q, both time directions,
and every time \(|t|\le T\). Independence of the F's is unnecessary; separation
of the whole boundary is essential.

To state modal-action drift, verify on D that
\(|A_i(z)-c_i-\sum_j B_{ij}F_j(z)|\le d_i\). Then

\[
 |A_i(z(t))-A_i(z_0)|\le 2d_i+|t|\sum_j|B_{ij}|\eta_j.
\tag{3}
\]

For physical secular eccentricities also establish
\(\Gamma_i=(\xi_i^2+\eta_i^2)/2<\Lambda_i\) and
\(e_i^2=2\Gamma_i/\Lambda_i-(\Gamma_i/\Lambda_i)^2\).
Modal actions and individual planets' eccentricity actions are different
observables: exchange already occurs in linear secular dynamics. Bound the
latter on the entire certified D using the explicit coordinate map. A small
drift of corrected actions alone does not give an equally small change in e.

**Estimated acceptance target, not selected literals:** a tube containing a
specified nominal secular point, transverse source-action radius
\(r=10^{-7}\), outer radius \(R=2\cdot10^{-7}\),
\(T=5,000,000,000\) yr and \(\eta_j\le10^{-17}\) action units/yr.
This gives corrected-action drift at most \(5\cdot10^{-8}\), leaving half
the raw radius margin for other costs. The actual boundary test must still pay
coordinate/observable errors. At 1 Gyr or 10 Gyr the same half-margin budget
would require \(5\cdot10^{-17}\) or \(5\cdot10^{-18}\), respectively.
Specify numerical eccentricity intervals after enclosure; tentative loose
ceilings \(e_J,e_S<0.15,e_U<0.25\) would be secondary outputs, not the
main improvement over AMD.

The first initial set should be an explicit positive-volume subset of the
selected secular coordinates with a proved nominal-point inclusion. The next
target may enclose a whole ephemeris uncertainty set after a validated
osculating-to-mean conversion. No uncertainty interval was supplied or certified
here. A single-point theorem is easier to describe but less useful; a tiny
unidentified successful set is not an acceptable substitute for the selected Q.

### Lean statement shape and exact reuse

Use `E := (Fin 3 → ℝ) × (Fin 3 → ℝ)`, the existing
`KAM.hamiltonianVectorField`, and `KAM.ODE.IsSolutionIn`. The following is a
**proposition shape**, not an elaborated declaration or an approval object.
`Hsec`, `Q`, `D`, `F`, `eta`, `A`, `drift`, `ecc`, `eccLo`, `eccHi`, and `T`
must become the complete audited model/region/literal definitions before a
final statement is presented for freezing.

```lean
∀ z₀ ∈ Q, ∃ (U : Set ℝ) (z : ℝ → E),
  IsOpen U ∧ U.OrdConnected ∧ Set.Icc (-T) T ⊆ U ∧ z 0 = z₀ ∧
  KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField Hsec) Set.univ U z ∧
  (∀ t ∈ Set.Icc (-T) T, z t ∈ D ∧
    (∀ j, |F j (z t) - F j z₀| ≤ eta j * |t|) ∧
    (∀ j, |A j (z t) - A j z₀| ≤ drift j) ∧
    (∀ j, eccLo j ≤ ecc j (z t) ∧ ecc j (z t) ≤ eccHi j)) ∧
  (∀ (J : Set ℝ) (y : ℝ → E), IsOpen J → J.OrdConnected →
    (0 : ℝ) ∈ J → y 0 = z₀ →
    KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField Hsec) Set.univ J y →
    Set.EqOn y z (J ∩ U))
```

This avoids a false `∃! z : ℝ → E` assertion when values outside the solution
interval are arbitrary. For a nonpolynomial model replace `univ` by its regular
open domain. Add nonemptiness/positive volume and nominal containment as
separately proved application facts. The literal application has initial
membership as its only substantial premise; bracket bounds, a successful
checker and a stopped drift estimate belong in its proof, not its hypotheses.

| Inspected core interface | Actual reuse and missing work |
|---|---|
| [ODE/Exit](../../KAM/ODE/Exit.lean), `KAM.ODE.gen_exit` | First boundary hit; apply to reversed time as well |
| [ODE/Continuation](../../KAM/ODE/Continuation.lean), `gen_confinement`, `gen_continuation_compact` | Existence through endpoints once first exit has established the internal confinement premise |
| [ODE/Uniqueness](../../KAM/ODE/Uniqueness.lean), `gen_uniqueness` | Agreement of solutions, with no arbitrary-total-function uniqueness claim |
| [Application/Transport](../../KAM/Application/Transport.lean), `IsFieldTransport.hasDerivAt_comp` | If a chart is used, `DΨ X_Hc = κ F ∘ Ψ` makes physical time `κ` times model time; polynomial Cartesian route can use the identity chart |
| [Application/Observables](../../KAM/Application/Observables.lean), `abs_sub_le_of_convex` | Spatial mean-value bound for observable transfer; time drift still needs the chain rule and integration. Torus-specific theorems do not bound an entire surrounding region |
| [Application/Confinement/TwoTorus](../../KAM/Application/Confinement/TwoTorus.lean) | Alternative on a justified two-degree reduced model; it is not a general approximate-integral checker |
| [Canonical/Lie](../../KAM/Canonical/Lie.lean), `taylor_lie` | Exact finite Lie expansion with analytic remainder, if the more expensive chart route is needed |

Source inspection found the ODE and application components, not a finished
Program-C polynomial lifetime checker. [The application contract](../campaign/design/APPLICATION-CONTRACT.md)
correctly separates the model, coordinate identity, clock and observable output.
No provider or draft frozen theorem should be imported by this implementation.

### Why check direct approximate integrals first?

Compute a numerical Birkhoff or near-torus Kolmogorov normal form **as an
untrusted producer**. Pull its nominal integrals back and retain finite literal
polynomials or supported Fourier expressions in the original coordinates.
The kernel need only verify (1)–(2) for those literal functions. It need not
certify the numerical diagonalizer, the formal normal-form derivation, an
infinite Diophantine assertion, or a canonical inverse.

For a polynomial H and polynomial F, their bracket is a finite exact polynomial.
Check its entire support, including degrees higher than the generation cutoff.
There is no infinite Lie tail to certify for the *literal F*. The cost of
truncating its discovery formula is already visible in its actual bracket
and its boundary/observable approximation. With an analytic original field
\(X=\widehat X+\Delta X\), add
\(\sum_k\sup|\partial_kF_j|\sup|\Delta X_k|\) to the derivative budget.
That is where missing model terms enter; they cannot be replaced by zero.

By contrast, certifying a canonical transformation can preserve cancellation
and much sharper domains without expanding the inverse observables. It needs
flow existence, symplecticity, inverse-domain coverage, the full Lie remainder
and its derivatives, plus initial-region transport. Use that route if direct
observables become too dense or their boundary approximation dominates.
Both routes share first exit. No normal-form order is accepted merely because
the first omitted term became small.

Near resonances, retain the offending monomials instead of dividing by tiny
numbers. A resonant normal form may preserve combinations \(b\cdot I\)
with \(b\cdot k=0\) for all retained modes. Combine them with energy and
verified boundary inequalities. There may be too few independent quantities
to separate D; that is a numerical/geometric gate, not an additional dynamical
hypothesis to assume in the application theorem.

## 3. Prototype: what was actually computed

The complete scripts and data are under [scripts/sjsu](../../scripts/sjsu/README.md).
`slg13_quartic.json` records each exact decimal, six exponents and its PDF token.
The journal-copy table was inspected on rendered p. 12. A separate parser of
arXiv v1, whose eta text-layer ordering differs, reproduced **all 78 exponent
tuples and rational coefficients**. No source software was executed.

The prototype diagonalizes the mean of the two quadratic blocks numerically.
The resulting frequencies are

\[
(-1.1212724892\cdot10^{-4},\;-1.9688444678\cdot10^{-5},\;
 -1.1134564418\cdot10^{-5})\quad\mathrm{rad/yr},
\]

matching the printed quadratic frequencies to their quoted precision.
The original quadratic residual is kept when evaluating final brackets.
For future exact checking use a rational symplectic map
\(\eta=Qy,\xi=Q^{-\mathsf T}x\), or literal original-coordinate F's,
instead of treating a floating orthogonal matrix as exact.

Write \(z_j=(x_j+iy_j)/\sqrt2\),
\(I_j=z_j\bar z_j\), so \(\{z_j,\bar z_j\}=i\) in the stated
coordinate ordering. The producer solves finite homological equations, applies
degree-truncated Lie series through K, and applies the inverse series in reverse
generator order to obtain F. It then computes **all** of \(\{F,H_4\}\),
through degree K+2. The final bracket is not truncated back to K.

There are two initial-data policies:

* **Table 1:** convert its printed orbital elements to \((\xi,\eta)\), and
  apply our diagonalizer. This defines a precise nominal point for the literal
  polynomial. It does not validate the omitted averaging correction. The modal
  actions are approximately \((3.1279904,6.5873653,0.29993795)10^{-4}\).
* **Table 2:** use its modal coordinates directly. This is an independent
  source-data interpretation, with no certified identification with Table 1.
  The similar feasibility result below is a sensitivity check, not proof that
  the two coordinate conventions agree.

Let \(s_j=|z_j^0|\) for either policy. The initial polydisk is
\(I_j\le r^2s_j^2\); the outer one is \(I_j<R^2s_j^2\).
For \(\epsilon_j=\|F_j-I_j\|_R\) and
\(\eta_j=\|\{F_j,H_4\}\|_R\), the sufficient boundary gap is

\[
 m_j=(R^2-r^2)s_j^2-2\epsilon_j,\qquad
 T_{\rm ratio}=\min_j m_j/\eta_j.
\tag{4}
\]

The norm is the sum of absolute complex coefficients times
\(\prod_i(Rs_i)^{\alpha_i+\beta_i}\), a valid majorant formula when its
arithmetic is enclosed. We search
\(R/r\in\{1.025,1.05,1.1,1.2,1.3,1.5,2\}\).
The table reports limiting ratios; a certified statement would use a strict
margin, for example \(T=T_{\rm ratio}/2\).

**Measured, floating, Table 1 policy; years.** A dash means no positive gap for
that K on the tested R-grid, not zero dynamical lifetime.

| r | K=2 | K=4 | K=6 | K=8 | K=10 |
|---:|---:|---:|---:|---:|---:|
| 0.1 | 3.44e6 | 5.85e8 | 8.63e10 | 1.50e13 | 3.05e15 |
| 0.2 | 8.60e5 | 3.43e7 | 1.26e9 | 5.29e10 | 2.70e12 |
| 0.3 | 3.82e5 | 6.02e6 | 9.78e7 | 1.69e9 | 3.84e10 |
| 0.5 | 1.38e5 | 5.13e5 | 2.43e6 | 1.47e7 | 1.00e8 |
| 0.7 | 7.02e4 | 3.02e4 | — | — | — |
| **1.0, nominal** | **3.44e4** | **—** | **—** | **—** | **—** |
| 1.1 | 2.84e4 | — | — | — | — |

At r=0.3, K=10, the selected R is 0.33 and the three derivative majorants are
approximately \((1.0703,1.8349,1.0621)10^{-17}\) per year. At r=1 the
selected uncorrected R is 1.5, giving 34,419 yr and a very broad outer region.
The Table 2 policy gives 34,042 yr at r=1 and \(2.24\cdot10^{10}\) yr at
r=0.3, K=10. Neither computation validates a small tube about the actual orbit.

| K | Terms per F | Terms in first complete bracket | Smallest divisor inverted, rad/yr |
|---:|---:|---:|---:|
| 2 | 1 | 90 | none |
| 4 | 81 | 598 | 8.55e-6 |
| 6 | 543 | 1,885 | 5.16e-6 |
| 8 | 1,830 | 4,888 | 3.02e-8 |
| 10 | 4,833 | 11,076 | 3.02e-8 |

Each degree-ten run took about **14.1 CPU-s, 50 MiB RSS** on this machine.
The producer considered about 6.61 million monomial pairs including discovery.
Normalized homological residuals were below \(1.2\cdot10^{-16}\).
Independent evaluation via partial derivatives agrees with expanded brackets;
the substitution check and realness checks pass. These are numerical
consistency tests, not directed rounding or interval certification.

**Feasibility verdict.** A low-degree experiment is cheap and reproduces the
expected improvement at small amplitudes. It does **not** support the desired
nominal-amplitude claim. Failure of the coarse closeness/boundary majorant is
not a lower bound on unavoidable drift, and does not rule out a better
observable, a resonant domain or a near-torus computation. Conversely, the
large times at r<1 cannot be advertised for nominal SJSU. Missing degree-6–18
terms and the missing near-torus maps prevent estimating their effect here.
No numerical fit to GLS17's graph is presented as a new remainder calculation.

## 4. AMD, reduction, spatial extension and model fidelity

For an exactly rotation-invariant planar secular model with fixed \(\Lambda\),
\(C=\sum\Gamma_i\) is conserved. Fixing a regular C level and quotienting
the common perihelion rotation reduces three degrees of freedom to two.
This follows from one conserved momentum and its one-dimensional symmetry;
see also [Migaszewski–Goździewski, §3](https://arxiv.org/abs/0803.3246v1).
**This reduction is conditional on the identity for the selected model.** It
cannot be applied as an exact reduction to `SJSU4-table`, whose defect is
measured below. In particular, earlier explorations' general observation
about two effective degrees needs this qualification for printed truncations.

**Measured nominal baseline, conditional on exact C conservation:** Table 1
gives \(\Lambda\approx(0.54005,0.218975,0.0474844)\) and
\(C\approx0.0010015294\). The elementary inequalities
\(\Gamma_i\le C\) give

| Planet | Eccentricity ceiling from total AMD alone |
|---|---:|
| Jupiter | 0.060874 |
| Saturn | 0.095533 |
| Uranus | 0.204301 |

The corresponding conservative adjacent radial gaps are about 3.108 AU and
4.843 AU. This is a floating evaluation at nominal axes, not an interval box
certificate. It shows why an all-time *non-crossing* result for a suitable
exact secular model may already be easier than a useful individual-action
bound. It also shows why the proposed headline should improve action control,
rather than merely restrict an AMD safety conclusion to five billion years.

[Laskar–Petit 2017, §3 and Appendix B](https://doi.org/10.1051/0004-6361/201630022)
provides the secular AMD and crossing framework. A crossing criterion is a
geometric condition on allowed ellipses. It is not a proof that a secular
trajectory shadows the full Newtonian one. [Laskar 1988, pp. 341–362](https://adsabs.harvard.edu/pdf/1988A%26A...198..341L)
uses a different, eight-planet secular differential system including inclination,
lunar and relativistic contributions; its numerical agreement and frequency
analysis do not provide the missing uniform error estimate for this model.

The [track LP source](../tracks/LP/source/MAIN.md), especially Lemmas 4–6
and the LP0 barrier, supplies the appropriate geometric endpoint: a strong-AMD
margin plus sufficiently small **Kepler fast-action drift** yields separated
annuli and collision avoidance. It does not turn the slow proper actions
of SJSU18 into those fast actions, and it does not bound the error of secular
averaging. LP's full Newtonian asymptotic constants also do not establish a
useful numerical threshold at the cited masses. Its geometry can save work
after a genuine full-field estimate is obtained; it does not close that estimate.

To transfer observables directly to a fuller field, one must bound
\(dF(X_{\rm full})\) after a justified coordinate/clock map, including fast
terms. The omitted contribution must fit the same margin/T budget, around
\(10^{-17}\)–\(10^{-18}\) in the proposed source action units per year.
An unquantified \(O(\mu^2)\) approximation or a numerical trajectory match
over millions of years does not establish that. Uniform trajectory shadowing
via a naive Grönwall estimate is also unlikely to be useful over 5 Gyr.

**Spatial extension, estimated separate project.** Before rotational reduction,
three planets have six secular canonical pairs (eccentricity and inclination).
At a regular nonzero angular-momentum level full SO(3) reduction leaves four
secular degrees of freedom: fixing the momentum vector and quotienting its
one-dimensional stabilizer removes four real dimensions. This agrees with
the fully reduced secular carrier in
[Chierchia–Pinzari, planetary Birkhoff normal forms](https://www.mat.uniroma3.it/users/chierchia/PREPRINTS/Chierchia_Pinzari_NBP_10.pdf).
The dimension statement is an inference from that carrier, not a spatial SJSU
coefficient calculation. Singular behavior near exact coplanarity requires
regular coordinates and a separate domain audit.

New obligations include nodal frequencies and resonances, exact angular-momentum
reduction, inclination actions \(Z_i=\Lambda_i\sqrt{1-e_i^2}(1-\cos i_i)\),
and the conversion to inclinations relative to a specified plane. Mixed signs
of the eccentricity/nodal quadratic energies remove a simple definite-energy
argument. Dense even-degree counts through 18 rise from 76,713 (six variables)
to 920,490 (eight reduced variables), or 53,886,780 (twelve unreduced
variables), before symmetry savings. No spatial coefficient set, normal form,
or useful time bound was computed here. Treat it as a new 3–6-month research
phase after the planar gates, not a small dimension change in the same proof.

## 5. Kernel cost and implementation work

There is **no SJSU kernel benchmark** in this task. All costs below are
extrapolations or historical measurements, with their scope stated.

The latest inspected LG00 evidence is stronger than the old scout's predictions.
At branch `lg00-cert` commit `fd82fef5`,
`docs/campaign/handoffs/LG00-CERT.md` records a completed one-torus run:
5,183 generated modules, 30.1 CPU-h for passing modules, 31.4 including failed
attempts/reruns, and maximum RSS 7.78 GB. Its main results reportedly use only
`propext`, `Classical.choice`, `Quot.sound`. Those are inherited receipts,
not rerun here. `lg00-app` at `77d65c0c`, `LG00-CONF.md`, records the core
two-torus assembly and check adapters; it does not by itself supply two
completed torus certificates and a closed SJSU confinement theorem.

[V2-PACKED](../campaign/design/V2-PACKED.md) §8 measures about 70 s for a
split landed product versus 14.9 s for the bridged packed product. The faster
0.18–0.30 s resident-integer operation is a different, then-unbridged boundary.
Section 13 measures a 3.54 CPU-h saving on selected LG00 stages, about 11.8%
of the passing total. Section 12's roughly 0.75 CPU-h packed-jet projection
for the two composition chains is an estimate, not an end-to-end production
measurement. None of these two-dimensional Fourier timings is a measured
six-variable Taylor product rate.

| Stage | Estimated finite work/data | Conditional kernel budget |
|---|---|---:|
| Literal quartic pilot, F through K=6–10 | 1.6k–14.5k F coefficients; up to 33.3k complete bracket coefficients; around 1–10 MB literals depending on precision and whether intermediates are stored | 1–15 CPU-h, to be replaced by a 128–512-term measured shard |
| Recovered degree-18 model, modest local F | Model up to tens of thousands of real coefficients; sparse Taylor or Fourier–Taylor blocks, about 10⁷–10⁹ scalar enclosure operations if sparsity survives | Roughly 10–1,000 CPU-h before a whole-boundary cover; no present instance supports the upper end as sufficient |
| Dense high-order pullback of three full F's | Degree grows to K+16 in `{F,H18}`; output support may reach millions and dominate data | Unpriced; reject the representation before committing a large run |
| Spatial variant | Larger supports, new resonances and chart | Unpriced; planar timings cannot be multiplied by two |

For scale, 10 million scalar operations at the historical 0.2–1.5 ms
per-coefficient range consume 0.56–4.17 CPU-h; one billion consume
55.6–417 CPU-h. Loading, coefficient growth, proof assembly and boundary
subdivision add costs. A single source file split does not split a large
kernel reduction. The producer's 14-second floating run is not a prediction
of kernel time.

Use 128–256-bit outward dyadic balls initially, escalating only from a measured
error budget. Keep final approximate integrals as literal finite functions;
their coefficients may be rounded freely if their **actual** full brackets
are rechecked. Exact rational Hamiltonian coefficients need directed conversion
to balls. Existing ball arithmetic, expressions, jets, polynomial product
lemmas, and checkpoint aggregation are reusable. Fourier–Taylor or Cartesian
polynomial differentiation, weighted norms on polydisks, full bracket semantics
and the first-exit acceptance checker still need application-independent code.

Packed arithmetic should stay behind a proved enclosure interface. A dense
six-dimensional rectangular packing can waste far more slots than it saves;
start with total-degree slices and sparse blocks, and compare a packed block
with a landed coefficient block on the same data. Avoid repeated unpacks,
memoize shared inputs once, and split on actual operation/memory counts.
Budget **under 4 GB charged memory per pilot process**, including imports and
assembly, with RSS reported separately. The existing lock's larger exception
is not a permission for SJSU. Use one targeted Lean process at a time on the
current machine and opt-in application data under the D51 convention.

Estimated new handwritten work, overlapping rather than mechanically additive:
2–4k Lean lines for approximate-integral first exit/observable transfer;
3–7k for finite polynomial/bracket bounds and checker soundness;
3–8k for the selected model, coordinates and numerical instance;
1–3k Python for a first producer beyond this scout. A certified reconstruction
of the averaging recipe or a canonical near-torus chart may add 5–15k Lean
lines and several weeks. Sharing Program B/C work should reduce duplication;
there is no reason to implement all of B's canonical machinery before the
direct-observable pilot.

## 6. Milestones, alternatives and decisions

This is a proposed sequence, not a launch of agents or compute jobs. Calendar
estimates assume a model/numerics worker, one Lean worker and an independent
reviewer when needed; compile jobs remain serialized and current LP/SO work
keeps its assigned resources.

| Phase | Effort / workers | Deliverable and gate |
|---|---|---|
| 0. Source/model recovery | 3–5 working days, one numerical researcher | Reconstruct or obtain full H18, averaged actions, signs/units and initial map; resolve the table defects. Stop the GLS17 reproduction claim if these cannot be pinned |
| 1. Small formal pilot | 1–2 weeks, one prover plus one numerics worker | Exact literal quartic, a useful finite-time instance at nominal data or a clearly scaled set, complete first-exit theorem and one arithmetic shard under 4 GB; independent statement/checker review |
| 2. Local numerical feasibility | 2–4 weeks, one numerics worker; prover maintains checker | Compare direct F, resonant F and a local torus chart for the recovered model; entire remainder/rounding/parameter budget, initial inclusion and a T(r) curve. Require factor-two slack at the agreed target |
| 3. Freeze and production | 2–4 weeks after gate 2, one prover and independent auditor | Exact final Lean commands, owner approval, frozen definitions/anchor, bounded certificate shards, axiom and source audits; final application no bracket hypotheses |
| 4. Broader initial set / fidelity | New scout | Enclose measured uncertainty, add Neptune, or control the full Newtonian field; each changes a substantive model/quantifier obligation |
| 5. Spatial | Separate 3–6-month estimate | Inclination model/reduction, new numerical gate, new statement and cost review |

A planar result might take **6–12 weeks after full data recovery**, provided
the local numerical gate succeeds. There is no supported delivery date for a
billion-year result if that gate fails. All-time AMD safety for a reconstructed
exactly symmetric secular model is a valuable early comparison; it should not
be presented as the desired tight-action result. A shorter certified lifetime
at the nominal point is another useful first milestone. On a genuinely
two-degree reduced leaf, two certified tori might give stronger confinement
than a finite-time normal form, but uniformity over a range of AMD levels is
additional work.

The owner decisions needed **before a later campaign**, not to finish this
report, are:

1. Recover the source model, or approve a separately named reconstructed
   rational variant? Recommend recovery first; use the printed quartic only as
   an explicitly labelled pilot.
2. Require the whole observational uncertainty set, or a proved neighborhood
   of the nominal mean point? Recommend the latter first, with a minimum
   acceptable size and observable tolerance fixed before optimization.
3. Target 1, 5 or 10 Gyr? Recommend 5 Gyr as the research target and accept an
   honest shorter-time curve when the gate fails. Do not silently shrink Q.
4. Allocate at most 100 CPU-h for measured pilots and consider up to 1,000
   only after a complete validated budget and projected data volume exist?
   Recommend that staged allocation, with no new memory exception.
5. Is three degrees **after reduction** a requirement? If so, choose a
   four-giant planar secular model including Neptune, or spatial SJSU, and
   re-scout. Merely naming three unreduced planar pairs does not meet it.

**Strongest honest prospective headline:** “For every initial state in a
specified nonzero-volume neighborhood of the nominal secular SJSU state,
Lean verifies explicit corrected-action drift and eccentricity bounds for
five billion years under the specified degree-18 planar Hamiltonian.”
The model, neighborhood, drift, and initial inclusion must all be in the
statement. This report establishes the scope and a reproducible pilot, not
that headline.

For rigorous methodological comparators, [Locatelli–Giorgilli 2000,
*CMDA* 78, 47–74](https://doi.org/10.1023/A:1011139523256) already uses interval
arithmetic for secular SJS tori/confinement. [Caracciolo–Locatelli 2020,
*JCD* 7, 425–460](https://www.aimsciences.org/article/doi/10.3934/jcd.2020017),
also [arXiv:2102.05959v1](https://arxiv.org/abs/2102.05959v1), gives rigorous
finite normal-form remainder estimates in Hénon–Heiles and restricted
three-body examples, including resonant comparisons. It is a suitable
checker regression, not an SJSU result. The later
[Guzzo–Caracciolo–Pinzari 2026 preprint](https://arxiv.org/abs/2601.18268v1)
improves certain nonresonant action bounds and has a three-degree rigorous
example; its general resonant extension is left open. It is an optional
method to investigate, not an assumed replacement for the missing data.
Targeted searches found no later rigorously certified nominal-SJSU 5-Gyr
action tube to replay. That scoped search result is not an exhaustive novelty
or priority claim.

## 7. Source issues and deliberate deviations

These findings belong in the orchestrator's errata review; this task does not
edit the central ledger or any frozen file.

**SJSU-E1, new candidate: AMD of the printed coefficient table.** Appendix A
prints the coefficients of
\(\eta_S^2\eta_U^2,\xi_S^2\eta_U^2,\xi_S\xi_U\eta_S\eta_U\) as

\[
 a=-1.3020117317952618\cdot10^{-4},\quad
 b=-7.7905487286026464\cdot10^{-5},\quad
 c=-1.0427780546265602\cdot10^{-4}.
\]

For \(C=\tfrac12\sum_i(\xi_i^2+\eta_i^2)\), the coefficient of
\(\xi_S\eta_S\eta_U^2\) in \(\{C,H_4\}\) is

\[
 -2a+2b+c
 =\frac{78391581085853}{250000000000000000000}
 =3.13566324343412\cdot10^{-7}\ne0.
\tag{5}
\]

This was checked by exact `Fraction` arithmetic, by a separate three-term
calculation, and against both PDF versions' tables. In total 65 nonzero bracket
monomials remain. The witness exceeds ordinary last-digit rounding by many
orders of magnitude. Higher homogeneous degrees cannot cancel a degree-four
defect against a quadratic C. This establishes a defect in interpreting the
printed literals as a standard AMD-conserving secular polynomial. It does
**not** identify the authors' underlying implementation error: the possibilities
include a table error, an approximation breaking the identity, or an unstated
transformed momentum convention. Ask for the correct invariant/data before
an exact reduction. No coefficient was repaired or projected in this scout.

**SJSU-E2, new candidate: source radii.** SLG13 p. 11, (24), gives
\((0.025558203988,0.030601862602,0.011223294461)\) and then states
“\(R_j=\sqrt{x_j^2(0)+y_j^2(0)}\)” using Table 2. Direct evaluation gives
\((0.029640120995,0.031025415863,0.012725782364)\). The rendered page confirms
the square root and the Table 2 reference. The discrepancies are much larger
than the printed precision. Possibly coordinates at another normalization
stage were intended; the written identification does not establish nominal
containment in the reported polydisk. Both data policies and the discrepancy
are preserved in the prototype output.

**Inherited GLS17 candidates, not silently adopted corrections.** The
[Program-D report](program-d-plan.md#8-provenance-defects-deviations-and-handoff)
records p. 12's “\(3\lambda_1-5\lambda_5-7\lambda_3\)” (invalid planet
index), (13)'s lower index “\(j=0\)” (three modes indexed 1–3), and p. 25
(57)'s factor “\(\rho^{l+1}\)” for an action-homogeneous degree-l remainder.
An angle derivative preserves action degree, so that factor should be
\(\rho^l\). These affect transcription/replay; they do not alone establish
an error in the plotted numerical results. The first-term-only bound following
(58) is a disclosed nonrigorous approximation, not a newly alleged concealed
proof gap.

**Deviations in this task:** degree-four literal polynomial in place of the
unavailable degree-18 instance; direct Table 1 or Table 2 nominal interpretation
without a certified averaging map; floating diagonalization/normal forms and
majorants; finite K≤10 and a small radius grid; no new kernel cost measurement.
These choices are explicit prototype limitations. Nothing here changes an
approved source-facing statement, assumes confinement in an application
premise, or asserts physical observational coverage.

## 8. Evidence and validation receipt

Required background read for this scope: the exploration catalogue and
`ambition.md`, Programs B/C/D, `sjs-plan.md`, `sjs-lg00-scout.md`,
`planetary-and-nekhoroshev.md`; the current application contract, ODE/application
interfaces, LP source endpoint, LG00 status/branch handoffs and packed-cost
design. Historical reports' forecasts were kept distinct from newer branch
receipts. The model and numerical calculations are this task's new evidence.

Source pins (PDFs remain outside git):

| Source | SHA-256 / locator |
|---|---|
| SLG13 journal-layout article-in-press copy | `915002b163d9efaeb7eea0a6b335bfda674a15944a7b7cf4fad0934d91e5147c`; `/home/scott/kam-tools/papers/slg13-sjsu-mcs/paper.pdf`, pp. 5, 8, 11–12 |
| SLG13 arXiv:1010.2609v1, downloaded independently | `3a231dd11ee3e9d20a64832f6886b9be6eed6b064cfb0cbe99bd88f4699b6cfb`; Appendix A agrees exactly with the committed table |
| GLS17 local supplied preprint | `bb11bb4ba2fd03519d293889860b432119221a61146c0c6f216d83b9cb13ce1d`; `/home/scott/kam-tools/papers/gls17-sjsu-rcd/paper.pdf` |
| GLS17 public arXiv v1, existing research copy rehashed | `254d52fb9c545efe12cfcc4b138ac8b429c1e95aad0d63c12b4e6dfc182e1cae`; §§2–4, Tables 1–2, Fig. 2; distinct bytes from supplied preprint |
| Caracciolo–Locatelli arXiv v1, existing research copy rehashed | `fe288ead9f2d02c3527875154bb1f21195eba0fac1f19bfaf55e6e0e596410e8`; §§3–5 |
| Laskar–Petit arXiv v2, existing research copy rehashed | `6b3c7aad2c2bf69612c0e0a65a5409f40a03e330253f8b3880f8e53d40f09361`; §3, Appendix B |

Reproduction commands, all from the worktree root:

```sh
python3 -I scripts/sjsu/extract_table.py /home/scott/kam-tools/papers/slg13-sjsu-mcs/paper.txt
nice -n 10 python3 -I scripts/sjsu/scout.py --order 10
nice -n 10 python3 -I scripts/sjsu/scout.py --order 10 --initial table2
python3 -I scripts/sjsu/compare_arxiv_table.py /tmp/sjsu-slg13-v1.txt
python3 -I scripts/sjsu/validate.py
```

The last text file is produced with `pdftotext -layout` from the pinned arXiv
PDF. Generation forces one BLAS thread, 3 GiB address space and 3,300 seconds
CPU per run. Both final runs completed in about 14.1 CPU-s. Results include
coefficient provenance hashes, all 35 order/radius rows for each initial policy,
correction and derivative bounds, support counts and numerical check residuals.

Validation output:

```text
PASS: all 78 rational coefficients and exponent tuples agree with arXiv:1010.2609v1.
PASS: 78 exact decimal terms; independent nonzero AMD-bracket witness.
PASS: scout-k10.json: provenance, substitution, homological solve, bracket, 35 margin rows.
PASS: scout-k10-table2.json: provenance, substitution, homological solve, bracket, 35 margin rows.
STATUS: numerical consistency checks only; no interval proof or Lean theorem.
```

Source lint was run as
`PATH=/tmp/sjsu-lint/bin:$PATH nice -n 10 scripts/lint_sources.sh`.
The temporary Python wrapper passes every source check through isolated Python
with bytecode writing disabled, and refuses only `abi_hashes.py`: that step
writes `.lake/abi-scratch` and invokes Lean outside this brief's write scope.
The result is **partial validation, exit 1**, not a full lint pass:

```text
check_lean_modules: PASS (4159 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI SKIPPED: SJSU-SCOPE is documentation/Python only; ABI checking writes .lake/abi-scratch and invokes Lean outside the permitted write scope.
LINT_EXIT=1
```

No other source-lint error was reported. The one-off document/data check,
`python3 -I /tmp/sjsu-document-check.py`, returned exit 0:

```text
PASS: syntax of 4 Python scripts (AST only; no bytecode writes).
PASS: balanced fences/math delimiters and 13 local links in the new report/README.
PASS: both CSV curves agree with all 70 stored JSON rows.
PASS: all five stated combinatorial support bounds.
PASS: one new report entry in each authorized catalogue location.
```

`git diff --check` returned exit 0 with no output. The numerical producers and
both validation scripts returned exit 0; none is a kernel check.

No Lean source or target was changed; targeted builds and `#print axioms` are
not applicable to new results. Existing axiom claims above are attributed to
handoffs, not independently replayed. All writes are the report, its catalogue
entry and `scripts/sjsu/**`; scratch is under `/tmp`. The commit is local to
`sjsu-scope`, with no push or merge.
