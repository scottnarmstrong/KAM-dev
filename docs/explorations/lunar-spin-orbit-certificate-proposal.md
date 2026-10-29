# Lunar spin–orbit confinement with a Lean-checked certificate

**Project proposal — 29 October 2026**

**Status:** proposed mathematical statements, architecture, and implementation milestones. No lunar certificate has yet been generated or checked as part of this proposal.

**Source baseline:** the relevant KAM-dev modules were inspected at commit [`608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29`](https://github.com/scottnarmstrong/KAM-dev/tree/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29). This was source inspection, not a fresh compilation or dependency audit. Proposed declaration and module names below are design sketches.

## 1. Objective and deliverables

Prove, in Lean, perpetual rotational confinement for an explicit conservative lunar spin–orbit model at the classical lunar parameter values. The proof will construct two invariant quasiperiodic tori from finite numerical certificates and use them as barriers for an open region of initial conditions.

The principal quantitative target is

$$
|p(t)-1|\le \frac{3}{100}\qquad\text{for every }t\in\mathbb R,
$$

where $p$ is the spin angular velocity divided by the orbital mean motion. The initial condition must belong to an explicitly described, certified region between the two barriers.

The deliverables are:

1. An exact definition of the seven-mode lunar Hamiltonian and its equations of motion.
2. A finite certificate format and a proved certificate-soundness theorem.
3. Two concrete certificates at the specified lunar parameters and frequencies, with Lean proofs that their checks succeed.
4. Exact invariant graph tori, with explicit enclosures in physical coordinates.
5. An explicit nonempty region of initial conditions and a global existence, uniqueness, and confinement theorem for every initial condition in that region.
6. Reproduction instructions, numerical margins, certificate sizes, verification costs, and an audit of the final theorem's axioms.

The existing KAM-dev convergence argument is the analytic engine. The new contribution is the complete path from finite data to a quantitative theorem about a specified model.

This first project formalizes an established celestial-mechanics benchmark. Its scientific extensions include removing the forcing truncation, verifying parameter ranges, and improving the certified confinement region. A claim of priority among formalizations would require a separate literature review at publication time.

## 2. Scope and exact model

### 2.1 Physical and mathematical scope

The model describes a rigid triaxial satellite with a prescribed Keplerian orbit and a spin axis perpendicular to the orbital plane. The first deliverable uses a particular finite Fourier–Taylor truncation of the conservative torque. The eccentricity and asphericity parameter are exact rational constants representing the classical lunar benchmark.

The theorem establishes a bound on angular velocity in this model. It does not establish permanent libration of the resonant angle, tidal capture, stability of the full Earth–Moon system, or coverage of present observational uncertainty. Those are different theorem targets.

### 2.2 Period-one normalization

Use angles $q,\phi\in\mathbb T:=\mathbb R/\mathbb Z$, with $\phi$ the orbital phase. Measure time $t$ in orbital periods, so $\dot\phi=1$. The momentum $p$ is the ratio of spin angular velocity to orbital mean motion; synchronous rotation corresponds to $p=1$.

To compare with the usual radian convention, write $x=2\pi q$ and $s=2\pi t$, where $s$ is time normalized so the orbital mean motion is one radian per unit time. Then

$$
\frac{dx}{ds}=\frac{dq}{dt}=p.
$$

The formalization must prove this change of variables, including the force scaling. Converting angles without converting time would introduce an incorrect factor of $2\pi$.

### 2.3 Exact parameters and coefficient table

Fix

$$
e_*:=\frac{549}{10000},\qquad \varepsilon_*:=\frac{69}{200000}.
$$

Define

$$
V(q,\phi):=-\varepsilon_*\sum_{m=1}^{7}A_m(e_*)\cos\bigl(2\pi(2q-m\phi)\bigr),
$$

with the following exact polynomial coefficients:

| $m$ | $A_m(e)$ |
| --- | --- |
| 1 | $-e/4+e^3/32$ |
| 2 | $1/2-5e^2/4+13e^4/32$ |
| 3 | $7e/4-123e^3/32$ |
| 4 | $17e^2/4-115e^4/12$ |
| 5 | $845e^3/96-32525e^5/1536$ |
| 6 | $533e^4/32$ |
| 7 | $228347e^5/7680$ |

This fixes the finite model in Celletti's equation (7.55). The corresponding classical benchmark uses the frequencies below and the outer spin interval $[0.97,1.03]$. [Celletti, *Stability and Chaos in Celestial Mechanics*, equations (7.50), (7.55), §7.3.1](https://www.studmed.ru/view/celletti-a-stability-and-chaos-in-celestial-mechanics_86b600371e9.html?page=17)

The physical equations in period-one coordinates are

$$
\begin{aligned}
&\dot q=p,\\
&\dot p=-\partial_qV(q,\phi)
 =-4\pi\varepsilon_*\sum_{m=1}^{7}A_m(e_*)\sin\bigl(2\pi(2q-m\phi)\bigr),\\
&\dot\phi=1.
\end{aligned}
$$

All seven terms are part of the definition. No additional neglected forcing term may be silently absorbed into the certificate error. A theorem for the untruncated forcing needs a separate analytic remainder argument.

### 2.4 Autonomous extension and frequencies

Introduce the auxiliary action $J$ and define

$$
\mathcal H(q,\phi,p,J):=J+\frac12p^2+V(q,\phi).
$$

The action ordering is $(p,J)$ and the angle ordering is $(q,\phi)$. For the integrable part $h_0(p,J)=p^2/2+J$, the ordinary action Hessian is singular, whereas

$$
\det\begin{pmatrix}1&0&p\\0&0&1\\p&1&0\end{pmatrix}=-1.
$$

This identifies the isoenergetic theorem as the appropriate route. It does not replace the certificate's obligation to verify the actual bordered torsion of the approximate torus.

Fix the benchmark frequencies

$$
g:=\frac{\sqrt5-1}{2},\qquad
\nu_-:=1-\frac1{40+g},\qquad
\nu_+:=1+\frac1{40+g}.
$$

The desired flow frequencies on the two tori are $(\nu_-,1)$ and $(\nu_+,1)$. These are quadratic irrational frequency vectors. The proposed Diophantine exponent is $\tau=1$; explicit positive rational lower bounds for the Diophantine constants must be proved in the convention used by KAM-dev.

## 3. Final theorem surface

The public result should expose the fixed model, explicit initial region, and spin bound. Strip widths, inverse bounds, Newton constants, and arithmetic witnesses belong in the proof and certificate API.

### 3.1 Exact barrier theorem

**Target theorem A — certified lunar barriers.** There exist real-analytic, one-periodic functions $P_-,P_+:\mathbb R^2\to\mathbb R$ such that:

1. For every $(q,\phi)$,

   $$
   \frac{97}{100}\le P_-(q,\phi)<P_+(q,\phi)\le\frac{103}{100}.
   $$

2. Each graph $p=P_\pm(q,\phi)$ is invariant under the physical spin–orbit flow.
3. The flow on each graph is analytically conjugate to the linear flow with frequency $(\nu_\pm,1)$ on $\mathbb T^2$.
4. The graph functions satisfy the invariance equation

   $$
   \partial_\phi P_\pm+P_\pm\partial_qP_\pm=-\partial_qV.
   $$

The certificate calculation fixes explicit real trigonometric polynomials $Q_\pm$ and positive rational numbers $d_\pm$ for which

$$
\sup_{q,\phi}|P_\pm(q,\phi)-Q_\pm(q,\phi)|\le d_\pm.
$$

The polynomials and error radii become named constants in the finished code. They are not arbitrary inputs to theorem A.

### 3.2 Explicit initial region

Define

$$
\mathcal R_{\rm cert}:=\left\{(q,p,\phi):
Q_-(q,\phi)+d_-<p<Q_+(q,\phi)-d_+\right\}.
$$

The final application must prove that this region is nonempty. The preferred certificate proves a positive uniform gap

$$
Q_+(q,\phi)-d_+-Q_-(q,\phi)-d_-\ge\eta_{\rm gap}>0
$$

for every phase pair, with an explicit rational $\eta_{\rm gap}$.

For a readily usable example, also certify a nonempty box of initial conditions near $p=1$ and stated angle representatives. Its endpoints must come from the validated computation. This proposal does not assign an unverified width to that box.

### 3.3 Global confinement theorem

**Target theorem B — lunar spin confinement.** For every initial condition $(q_0,p_0,\phi_0)\in\mathcal R_{\rm cert}$, there is a unique global solution of the specified equations through that initial condition. For every $t\in\mathbb R$,

$$
P_-(q(t),\phi(t))<p(t)<P_+(q(t),\phi(t)),
$$

and therefore

$$
\boxed{|p(t)-1|\le\frac3{100}.}
$$

Uniqueness may be expressed using real lifts of the angles with fixed initial representatives, or equivalently on the torus. The implementation must use one convention consistently.

The exact slab between $P_-$ and $P_+$ is invariant. The smaller explicit set $\mathcal R_{\rm cert}$ is a certified set of starting points; the statement does not assert that trajectories remain in that smaller set.

### 3.4 What is fixed and what remains to be computed

| Item | Status |
| --- | --- |
| Seven-mode Hamiltonian, units, $e_*$, $\varepsilon_*$ | Fixed proposed target |
| Frequencies $\nu_-$ and $\nu_+$ | Fixed proposed target |
| Outer bound $[97/100,103/100]$ | Fixed benchmark to be tested by the pilot |
| Fourier coefficient tables and resolutions | To be computed |
| Strip widths and certified norm bounds | To be selected and verified |
| Diophantine lower bounds | To be proved explicitly |
| $Q_\pm$, $d_\pm$, $\eta_{\rm gap}$, initial box | To be computed and verified |
| Certificate replay cost | To be measured |

If the pilot cannot reach the benchmark, report the failed inequality and the proposed remedy. A wider band, different frequencies, or smaller perturbation parameter would be a changed target, not completion of this one.

## 4. Reuse from KAM-dev

Links in this section point to the inspected commit. They identify existing mathematical infrastructure; they do not assert that every API can be applied without adaptation.

| Existing component | Reuse | Required adaptation |
| --- | --- | --- |
| [`KAM.Iso.Apost.g1_explicit`](https://github.com/scottnarmstrong/KAM-dev/blob/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29/KAM/Iso/Apost/G1.lean) | Explicit a posteriori isoenergetic KAM theorem, convergence, energy identity, and displacement bounds | Discharge its exact hypotheses from finite certificate data |
| [`KAM.Iso.Apost.Defs`](https://github.com/scottnarmstrong/KAM-dev/blob/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29/KAM/Iso/Apost/Defs.lean) | `isoC1`, `isoC2`, standing assumptions, and iteration data | Computable upper bounds on the constants and a transparent parameter mapping |
| [`KAM.Strip`](https://github.com/scottnarmstrong/KAM-dev/tree/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29/KAM/Strip) and [`KAM.Fourier`](https://github.com/scottnarmstrong/KAM-dev/tree/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29/KAM/Fourier) | Analyticity, Cauchy estimates, Fourier differentiation, and cohomological analysis | Finite-expression evaluators and proved bounds in the existing norm conventions |
| [`KAM.Matrix.Neumann`](https://github.com/scottnarmstrong/KAM-dev/blob/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29/KAM/Matrix/Neumann.lean) | Inverse stability and maximum row-sum operator norms | Approximate-inverse certificate lemmas and arithmetic enclosures |
| [`KAM.Iso.Confinement.Graph`](https://github.com/scottnarmstrong/KAM-dev/blob/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29/KAM/Iso/Confinement/Graph.lean) | Phase inversion and representation of a torus as a graph | Extract or specialize the argument for direct a posteriori certificate output; track explicit graph errors |
| [`KAM.Iso.Confinement.Invariance`](https://github.com/scottnarmstrong/KAM-dev/blob/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29/KAM/Iso/Confinement/Invariance.lean) | Passage from the torus equation to flow invariance | A wrapper for the lunar embedding and physical projection |
| [`KAM.ODE.Exit`](https://github.com/scottnarmstrong/KAM-dev/blob/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29/KAM/ODE/Exit.lean) | `gen_barrier`, the no-crossing argument | Identify the boundary of the graph slab and prove invariance of its two components |
| [`KAM.ODE.Continuation`](https://github.com/scottnarmstrong/KAM-dev/blob/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29/KAM/ODE/Continuation.lean) and [`KAM.ODE.Uniqueness`](https://github.com/scottnarmstrong/KAM-dev/blob/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29/KAM/ODE/Uniqueness.lean) | Global continuation and uniqueness infrastructure | Verify the regularity and boundedness properties of the explicit force |

The headline qualitative confinement theorem has an existential perturbation threshold. That does not establish that the particular number $\varepsilon_*$ is admissible. The intended quantitative entry point is `g1_explicit`, together with its explicit constants.

The existing graph and confinement modules are partly organized around the current chart construction. Reuse their mathematical arguments while keeping the lunar application independent of unnecessary chart-generation machinery.

## 5. Approximate tori from one scalar polynomial

### 5.1 Representation

For one of the chosen frequencies $\nu$, let $u$ be a finite real Fourier polynomial on $\mathbb T^2$. Its coefficients can be chosen as exact rationals or dyadic rationals. A sine–cosine representation makes real-valuedness automatic; a complex representation requires explicit conjugacy symmetry.

Define

$$
D_\nu:=\nu\partial_{\theta_1}+\partial_{\theta_2}.
$$

Construct the approximate embedding $K$ in angle–action order by

$$
\begin{aligned}
&q(\theta)=\theta_1+u(\theta),\qquad \phi(\theta)=\theta_2,\\
&p(\theta)=\nu+D_\nu u(\theta),\\
&J(\theta)=-\frac12p(\theta)^2-V(q(\theta),\phi(\theta)).
\end{aligned}
$$

The action $J$ is a finite analytic expression involving compositions, rather than necessarily a Fourier polynomial. The certificate evaluator must support this representation.

### 5.2 Exact identities

Two angle equations and the energy identity hold by construction:

$$
D_\nu q=p,\qquad D_\nu\phi=1,\qquad \mathcal H\circ K=0.
$$

Define the scalar residual

$$
r:=D_\nu^2u+\partial_qV(\theta_1+u,\theta_2).
$$

For $E:=X_{\mathcal H}\circ K-DK(\nu,1)$, the components are exactly

$$
E=((0,0),(-r,pr)).
$$

Consequently, in the relevant maximum norm,

$$
\|E\|_\rho\le\max(1,\|p\|_\rho)\|r\|_\rho.
$$

These identities should be proved once symbolically. The certificate then verifies a scalar residual and the needed auxiliary norms. There is no independently estimated energy defect, and the auxiliary action does not require a separate numerical solve.

### 5.3 Residual evaluation

Compute the residual in a representation that preserves cancellation between $D_\nu^2u$ and the force. A practical candidate is finite Fourier algebra plus a rigorous remainder for composition. Bounds on the two summands separately would usually destroy the accuracy gained by Newton iteration.

The external solver may use FFTs, arbitrary precision, Newton iteration, and continuation in parameters to find $u$. Its rounded output defines an exact new candidate polynomial. Lean checks that polynomial's residual; it need not prove that the external solver followed its advertised algorithm.

## 6. Certificate data and proof obligations

### 6.1 Data format

Start with a model-specific format. Generalize after the two lunar examples succeed.

| Certificate field | Purpose |
| --- | --- |
| Lower/upper frequency tag | Select the exact expression $\nu_-$ or $\nu_+$ |
| Finite Fourier support and rational coefficients for $u$ | Define the approximate torus |
| Rational radii $\rho>\rho_\infty>\rho_{\rm graph}>0$ | Separate residual estimates, KAM output, and derivative estimates |
| An ambient complex-domain specification and positive margins | Establish that the torus and its correction stay in the Hamiltonian domain |
| Bounds $M,\sigma_K,\sigma_B,\sigma_T$ | Match the existing theorem's derivative and inverse hypotheses |
| Rational Diophantine bound, with $\tau=1$ | Control all small divisors |
| Approximate inverse data and defect bounds | Certify Gram and bordered-torsion invertibility |
| Fourier-composition and averaging witnesses | Certify nonlinear expressions and analytic remainders |
| Residual and displacement bounds | Verify the KAM inequality and quantify the output |
| Graph monotonicity bounds and fitted graph data | Transport embedding errors to $Q_\pm,d_\pm$ |

Hashes, generator versions, and solver logs belong in reproducibility metadata. Mathematical validity must follow from the parsed data and soundness proofs, independently of those metadata fields.

### 6.2 Analytic enclosures

Use the period-one Fourier convention. A basic estimate to connect finite coefficients to a complex-strip supremum is

$$
\left\|\sum_k a_k e^{2\pi i k\cdot\theta}\right\|_\rho
\le\sum_k|a_k|e^{2\pi\rho|k|_1}.
$$

Formalize or reuse the matching derivative estimates, including every factor of $2\pi$. The evaluator needs sound bounds for the elementary transcendental expressions that occur, in particular exponential weights, trigonometric composition, $\pi$, and the algebraic frequency.

Products and nonlinear compositions can produce frequencies outside the stored support. Their omitted terms need proved remainder bounds. If FFT samples are used in verification, aliasing and interpolation error must also be bounded. An exact finite convolution backend avoids that additional obligation for products.

The pilot should decide between weighted Fourier enclosures, subdivisions with analytic remainders, or a small combination of the two. The final checker should implement only the operations the application actually needs.

### 6.3 Derivatives, inverses, and averages

The existing theorem requires bounds for $D\mathcal H$, $X_{\mathcal H}$, $DX_{\mathcal H}$, $D^2X_{\mathcal H}$, and $D^2\mathcal H$, as well as the embedding derivative. The Hamiltonian is entire, but these bounds require a suitable bounded complex angle strip and momentum neighborhood. Its linear dependence on $J$ simplifies the auxiliary-action direction.

The Gram matrix in KAM-dev uses the complex bilinear expression $DK^T DK$. Real positive definiteness alone does not prove its invertibility throughout a complex strip. The checker must certify the matrix defined by the existing API on the required domain.

Use approximate inverses and small inverse defects to prove invertibility and row-sum norm bounds. The averaged bordered torsion is a $3\times3$ matrix when $n=2$. Its average must itself have a rigorous enclosure, including the effect of inverse and composition remainders. An unvalidated numerical quadrature is insufficient.

### 6.4 Infinite Diophantine condition

Prove an explicit rational $\gamma>0$ such that

$$
|k_1\nu+k_2|\ge\frac{\gamma}{|k_1|+|k_2|}
\qquad\text{for all }(k_1,k_2)\in\mathbb Z^2\setminus\{0\}.
$$

Quadratic irrationality supplies a tractable exact route. An algebraic-norm proof can provide an initial bound; continued-fraction estimates may improve it if the numerical margin requires that improvement. Search existing Mathlib number-theoretic APIs before introducing new definitions.

A finite search over Fourier modes can sharpen a bound when combined with a proved estimate for the remaining modes. By itself it cannot establish the hypothesis.

Track the factor of two when passing from $(\nu,1)$ to the reference vector $(\nu/2,1/2)$ used by the isoenergetic theorem.

### 6.5 The actual KAM inequality

Use $\eta$ for the full invariance-error upper bound, reserving $e_*$ for orbital eccentricity. The central inequality has the form

$$
\frac{C_1\eta}{\gamma^4\rho^{4\tau}}<1,
$$

where $C_1$ is the existing `isoC1` evaluated at the certified parameters. The corresponding torus-error bound is

$$
d_K\le\frac{C_2\eta}{\gamma^2\rho^{2\tau}}.
$$

For the present theorem, $C_1$ and $C_2$ have explicit definitions in terms of the iteration constants and $\delta_0=\min(1,(\rho-\rho_\infty)/8)$. A smaller strip can improve a residual enclosure while worsening these losses. Parameter selection must therefore evaluate the whole inequality and the final graph margins together.

The checker must also verify the other hypotheses: holomorphy, periodicity, reality, primary winding, domain clearance, all derivative and inverse bounds, the energy condition, and the frequency-ray margins. Checking the scalar smallness inequality alone is not a certificate.

## 7. The two geometric bridges

### 7.1 Fixing the clock frequency

The isoenergetic theorem permits an output frequency $s_\infty\omega_*$. Choose

$$
\omega_*=(\nu/2,1/2),\qquad s_{\rm initial}=2,
$$

and an admissible ray interval containing $2$, for example with upper endpoint $3$. Verify its required endpoint margins.

The exact torus's clock lift has primary winding, so it has the form $\theta_2+w(\theta)$ with periodic $w$. The clock component of the invariance equation is

$$
D_{s_\infty\omega_*}(\theta_2+w)=1.
$$

Averaging gives $s_\infty/2=1$. Thus $s_\infty=2$, and the physical frequency is exactly $(\nu,1)$.

The remaining equation $D_{(\nu,1)}w=0$ and nonresonance imply that $w$ is constant. Account for that phase constant when transporting errors to physical coordinates. It may be removed by reparametrization, but the effect of that reparametrization on closeness estimates must be bounded.

### 7.2 From embeddings to graph enclosures

The certificate should establish a positive lower bound on the real angular derivative of the approximate torus. A Cauchy estimate on a smaller strip transfers the KAM displacement bound to a derivative bound for the exact torus. This proves monotonicity and invertibility of the exact angular projection at each clock phase.

The current graph construction provides useful continuous graph infrastructure. The real-analytic conclusion in theorem A additionally requires an analytic inverse argument: establish local analytic inverses where the angular derivative is nonzero, then identify them with the global periodic inverse. Include this step explicitly in the graph module.

A bound on embedding distance is not automatically the same bound on graph distance. The inverse angular map and the clock phase shift must enter the estimate.

For example, suppose the candidate has $\partial_{\theta_1}q\ge m>0$. Let $d_q,d_p,d_\phi$ bound the exact-versus-candidate coordinate errors; after the clock lemma, $d_\phi$ bounds a constant phase shift. Let $L_{q,2},L_{p,1},L_{p,2}$ bound the indicated candidate derivatives. Then an appropriate comparison of real lifts yields the graph-error estimate

$$
d_{\rm graph}\le d_p+
\frac{L_{p,1}}{m}(d_q+L_{q,2}d_\phi)+L_{p,2}d_\phi+d_{\rm fit},
$$

where $d_{\rm fit}$ is a certified error for approximating the candidate's physical graph by a finite polynomial $Q$. The formal proof must state the invertibility and periodicity assumptions that make this comparison valid.

An alternative implementation can certify the inverse angular map directly. The pilot should choose the representation giving the simpler and sharper proof.

### 7.3 Separation, invariance, and continuation

Use the graph enclosures to prove ordering and the outer band. The boundary of the open slab between the exact graphs is their union. Flow invariance and uniqueness prevent a trajectory starting strictly between them from crossing either boundary; `gen_barrier` supplies the existing general argument.

For the physical vector field $(p,-\partial_qV,1)$, periodic smooth forcing also makes global existence straightforward to establish. Reuse the available ODE infrastructure, either through global derivative bounds or through continuation on the confined region. Prove the statement in both time directions.

Both autonomous tori can lie on $\mathcal H=0$. Every physical initial state lifts to that same energy by setting $J=-p^2/2-V(q,\phi)$. This avoids constructing a family of tori over auxiliary energies.

## 8. Trust boundary and Lean interfaces

The external generator is allowed to be a conventional numerical program. It produces candidate data and diagnostics. The Lean checker supplies the proof.

The intended interfaces are schematically:

```lean
-- Proposed interfaces, not existing declarations or compilable signatures.
def checkTorusCertificate (c : TorusCertificate) : Bool

theorem checkTorusCertificate_sound
    (h : checkTorusCertificate c = true) :
    CertifiedTorusWithBounds c

def lunarLowerCertificate : TorusCertificate
def lunarUpperCertificate : TorusCertificate

theorem lunarLowerCertificate_passes :
    checkTorusCertificate lunarLowerCertificate = true

theorem lunarUpperCertificate_passes :
    checkTorusCertificate lunarUpperCertificate = true

theorem lunar_confined
    (hz : z0 ∈ lunarCertifiedRegion) :
    UniqueGlobalSolutionWithSpinBound lunarVectorField z0 (3 / 100)
```

The reusable soundness theorem is conditional on a checker result. The final lunar theorem must discharge that condition using the concrete certificates. Its only substantive input is membership of the initial condition in the explicit region.

The target trust boundary is ordinary Lean kernel checking plus the standard logical foundations of the imported library. Imported arithmetic results must have proved soundness. Numerical observations, unchecked native evaluation, external solver assertions, and file hashes must not become mathematical assumptions.

Evaluate any candidate arithmetic package against the project's exact Lean/Mathlib versions and repository rules. Verify the trust path of the particular APIs used. Adoption is an implementation decision after inspection, not a dependency assumed by this proposal.

Large certificate evaluation may need staged proofs and arithmetic reflection. Prototype that cost early. A mathematically sound checker that cannot replay the examples within practical resources is not yet a usable deliverable.

## 9. Proposed code organization

Keep the first application narrow. The following repository-relative paths are proposed, not existing files:

```text
KAM/Certificate/
  Arithmetic.lean             -- verified arithmetic backend bridge
  FiniteFourier.lean          -- exact data, evaluation, derivatives, products
  StripBounds.lean            -- coefficient-to-analytic norm estimates
  Composition.lean            -- nonlinear composition with proved remainders
  Inverse.lean                -- inverse-defect certificates
  QuadraticDiophantine.lean   -- exact frequency lower bounds
  Isoenergetic.lean           -- finite certificates imply I-G1 hypotheses

KAM/SpinOrbit/
  Model.lean                  -- exact coefficients and Hamiltonian
  PeriodOne.lean              -- normalization and equation equivalence
  ScalarEmbedding.lean        -- candidate K and residual identities
  Clock.lean                  -- exact forcing frequency and phase shift
  GraphBounds.lean            -- graph inversion and error transport
  Barrier.lean                -- physical confinement and global solutions
  LunarData.lean              -- model constants and certificate data imports
  LunarCertificate.lean       -- successful checks for both tori
  LunarConfinement.lean       -- final public theorems

certificates/lunar-spin-orbit/
  lower.*                    -- exact serialized numerical data
  upper.*
  metadata.*                 -- schema, provenance, generator settings

scripts/spin_orbit/
  ...                        -- generator, diagnostics, and reproduction tools
```

Choose the actual serialization format after measuring proof replay. Large tables may need partitioned generated Lean modules or an explicitly verified parsing path. Data shards must respect repository file-size rules.

Foundational modules should use the existing ambient types `Fin n → ℝ`, `Fin n → ℂ`, and `Fin n → ℤ`. Follow current module conventions and keep imports narrow. Search existing KAM-dev and Mathlib APIs before duplicating finite Fourier, interval, inverse, or number-theoretic infrastructure.

Do not modify frozen theorem statements to make a certificate pass. Proposed new public anchors should follow the repository's statement-review process. Implementation should respect the current default-heartbeat, file-size, provider, and build rules; difficulty elaborating a proof calls for refactoring.

## 10. Milestones and acceptance criteria

### M0 — Freeze the model and statement

**Work:** check the source coefficient table, parameter convention, period-one scaling, frequency definitions, and exact interpretation of the final initial region. Document the imported theorem interface and expected axiom boundary.

**Deliverable:** a reviewed statement specification and a list of unresolved numerical quantities.

**Acceptance:** every coefficient, unit conversion, and theorem quantifier is explicit. The chosen model and target band are fixed before expensive implementation.

### M1 — Quantitative feasibility pilot

**Work:** compute both approximate tori, estimate analytic widths, evaluate the actual KAM-dev constants, and estimate all geometric margins. Use arbitrary precision as necessary. Start with the fixed benchmark frequencies and parameters.

**Deliverable:** a report containing Fourier resolutions, numerical precision, proposed strip widths, candidate norm bounds, residual thresholds, predicted exact-torus errors, graph margins, and barrier separation.

**Acceptance:** either a plausible complete path through every required inequality with positive margins, or an explicit diagnosis of which inequality fails and what mathematical improvement it requires. Label numerical estimates as estimates; they are not Lean certificates.

This milestone is the first stop/go checkpoint for the expensive checker work. Do not assume that an explicit theorem has practical constants merely because they can be evaluated.

### M2 — Formalize the model and scalar reduction

**Work:** define the exact model, prove normalization, holomorphy, reality, periodicity, primary winding of the candidates, the energy identity, and the residual formula. Begin the clock bridge.

**Deliverable:** a small compiled analytic interface for scalar candidate polynomials.

**Acceptance:** the residual and force scaling agree symbolically with the Hamiltonian, and no numerical oracle is involved.

### M3 — Arithmetic and enclosure prototype

**Work:** implement the minimal certificate arithmetic operations, finite Fourier evaluation, strip bounds, and a representative nonlinear residual calculation. Prototype inverse and average enclosures.

**Deliverable:** a sound checker on representative data at a scale informed by M1, with measured replay cost.

**Acceptance:** all accepted bounds are proved to enclose the intended expressions; known invalid witnesses are rejected; the evaluation strategy has a credible route to the full certificate size.

### M4 — Complete certificate soundness

**Work:** discharge every I-G1 hypothesis, prove the quadratic-frequency bounds, connect to `g1_explicit`, and complete the clock lemma.

**Deliverable:** `checkTorusCertificate_sound` with explicit output bounds.

**Acceptance:** the theorem covers complex-strip residuals, nonlinear remainders, inverses, averages, all small divisors, and all standing assumptions. No premise restates existence of the desired exact torus.

### M5 — Graph and barrier theorem

**Work:** prove graph inversion, phase-shift accounting, graph-error transport, separation, invariance, and global existence and uniqueness. Define the explicit inner region and verify its geometric properties from graph certificates.

**Deliverable:** a reusable two-certificate confinement theorem.

**Acceptance:** the initial-region test is explicit, the graph band is proved, and the no-crossing theorem applies for all real times. The exact invariant slab and the computable initial region are distinguished in the statement.

### M6 — Close the lunar application

**Work:** generate final exact tables, prove both checks succeed, certify the initial region and example box, and assemble the public theorem.

**Deliverable:** the closed lunar barrier and confinement theorems, certificate data, and reproduction instructions.

**Acceptance:** the fixed lunar benchmark passes in Lean, with no residual certificate assumptions. Report the targeted build and lint results, `#print axioms` output, file hashes, numerical margins, certificate sizes, and replay resources.

Model lemmas can proceed while the numerical pilot runs. Large investments in a general checker should follow evidence from M1 and the replay prototype. This proposal assigns no calendar or line-count estimate before those measurements.

## 11. Risks and remedies

| Risk | Diagnostic | Response |
| --- | --- | --- |
| Existing KAM constants are too conservative | Required residual is far smaller than the candidate can economically certify | Improve approximation and parameter selection; then consider proved sharper bounds using the existing iteration machinery |
| A tiny real residual hides a large complex residual | Fourier weights or composition bounds grow rapidly with strip width | Adjust strip allocation and resolution using the complete KAM inequality |
| Nonlinear interval evaluation loses cancellation | Force and derivative enclosures swamp their difference | Evaluate residuals coefficientwise with controlled composition remainders |
| Bordered torsion estimates are pessimistic | The approximate inverse has a large certified defect or norm | Improve inverse representation, averaging, coordinates, or matrix bounds |
| The torus exists but the graph claim fails | Derivative-error bound consumes the monotonicity margin | Refine the candidate or derivative estimate; use a verified inverse map if advantageous |
| Graphs exist but miss the target band | Error radii or actual graph extrema exceed the 3% bound | Diagnose geometry separately from KAM convergence; revise estimates or explicitly reconsider the target |
| Verification is too slow | Kernel replay or generated terms exceed practical resources | Stage arithmetic proofs, shard data, and improve reflection without changing the stated trust boundary |
| A generic library dominates the project | New abstractions have no immediate lunar consumer | Keep the first implementation model-specific and extract reuse from successful code |

Increasing floating-point precision addresses arithmetic error, but cannot by itself repair every analytic bound. Increasing Fourier resolution addresses approximation error, but can worsen proof replay cost. The pilot report should distinguish these effects.

## 12. Verification and reproducibility

The verification package should include:

- Exact source and dependency revisions, a fixed coefficient table, and the period-one convention.
- The generator implementation, its precision and truncation settings, and the exported exact data.
- A machine-readable list of certified bounds and the corresponding inequalities they discharge.
- Separate margins for KAM smallness, domain clearance, inverse defects, graph invertibility, separation, and the outer spin band.
- Targeted Lean builds and required repository lint checks.
- An axiom audit for the final theorems and the arithmetic soundness path.
- Certificate size, proof replay wall time, peak memory, and the machine used for those measurements.

Useful negative checks include a deliberately false residual upper bound, an invalid inverse witness, or an inadmissible zero domain margin. Select cases whose failure is known; arbitrary coefficient changes can still describe valid certificates. Negative checks exercise the implementation but do not replace the soundness proof.

Plots of the candidate and certified graph bands can make the result easier to inspect. They should be labeled by what is rigorously bounded and what is a numerical visualization. Sampling a plot never establishes a global inequality.

## 13. Research extensions after the benchmark

### 13.1 Untruncated Kepler forcing

Replace the seven-mode potential by the exact conservative Kepler forcing. Reuse the certificate, clock, graph, and barrier architecture, while adding analytic control of Kepler's equation, its complex domain, and the forcing tail.

This extension must compare the relevant force and derivative norms, not merely the real pointwise potential. It is a focused way to move from a historical truncated benchmark to a more faithful model.

### 13.2 Parameter-box certificates

Prove the relevant inequalities uniformly for $(e,\varepsilon)$ in an explicit rectangle. The resulting theorem can state that for every parameter pair in that rectangle there exist suitable barriers, with a uniform confinement band.

A pointwise certificate with strict margins suggests a starting point, but a uniform theorem still requires verified parameter dependence. Decide explicitly whether the initial region is common to all parameters or varies with them. Coverage of measurement uncertainty requires a separately justified observational parameter box.

### 13.3 Sharper confinement and robust initial sets

Optimize the barrier frequencies and approximations to reduce the outer band or enlarge the certified initial region. Report both quantities: a tighter outer band can come with a smaller admissible region.

For a fixed benchmark family, Lean can certify each successful improvement. Identifying useful coordinates, estimates, and representations is a genuine quantitative research task even though the soundness framework remains the same.

### 13.4 Additional bodies and different resonance questions

The same conservative certificate machinery can support other spin–orbit parameter choices and other rotational resonances. Permanent libration needs a different geometric target, such as certified librational barriers around a periodic orbit. Dissipative tidal models require an appropriate conformally symplectic or attracting-orbit theorem; they should be scoped as a separate extension.

## 14. Immediate next work package

Begin with M0 and M1. Freeze the exact model and theorem surface, produce both scalar Fourier candidates, and evaluate the current explicit KAM constants against them. The first report should answer four questions:

1. What residual is required by the existing theorem, and what residual can be enclosed on a useful complex strip?
2. How large are the verified inverse bounds and the resulting exact-torus displacement?
3. Do the graph and separation margins fit inside the fixed 3% band?
4. What certificate representation and verification cost does this suggest?

Those measurements determine the smallest credible implementation. The project is complete only when the concrete lunar data discharge the soundness theorem and yield the public global confinement result.

## References

- [KAM-dev, inspected source revision](https://github.com/scottnarmstrong/KAM-dev/tree/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29).
- [KAM-dev exploration note, “Realistic KAM and finite size”](https://github.com/scottnarmstrong/KAM-dev/blob/608bea1ed1b01ac7c0fe5e24ccaea4f638c0bc29/docs/explorations/realistic-kam-and-finite-size.md), particularly proposal C2. This proposal refines that conditional target into a concrete certificate application.
- [Celletti, *Stability and Chaos in Celestial Mechanics*, relevant book excerpt](https://www.studmed.ru/view/celletti-a-stability-and-chaos-in-celestial-mechanics_86b600371e9.html?page=17), for the coefficient table and classical benchmark.
- [Celletti, “Analysis of resonances in the spin–orbit problem in celestial mechanics: Part I”](https://doi.org/10.1007/BF00945107), ZAMP 41 (1990), 174–204.
- [Celletti, 2019 lecture slides](https://ethz.ch/content/dam/ethz/special-interest/math/department/News_Events/Events/Women_in_Mathematics/Symposium/celletti-alessandra-slides.pdf), for the physical model and the confinement mechanism.
