# Significance and pitch: the sealed magnetic barrier

Date: 10 November 2026. Branch: `mag-pitch`.
Scope: literature and source review, floating-point experiments, publication framing.
Repository input: `bf5241acc625c02d39dd0991c369015274a4b881`.
The magnetic seal is recorded at `ab78ed4ea`.
This report does not recheck the Lean proof or change its statement.

## 1. Recommendation and priority verdict

Present this as a **kernel-checked, finite-parameter transport barrier for an
explicit quadratic-control Hamiltonian, with the original equations covered**.
The mathematical result is substantial; a broad historical first is unnecessary.

Of the brief's three labels, the defensible narrow choice is **first
machine-checked for this exact specified model, to the extent of this search**.
No earlier proof for the literal coefficients, amplitude and frequency below
was located. This is evidence from a bounded search, not proof of priority.
“First rigorous for this model” needs the same finite-parameter qualification
and is a less suitable headline than the explicit theorem description.

For “first rigorous magnetic barrier,” “first machine-checked magnetic torus,”
or “first proof-assistant KAM application,” the answer is **neither**.
Earlier rigorous magnetic work exists, and earlier formal applications were
located in PlasmaLean. An independent 2026 formalization also reports a general
analytic Hamiltonian KAM theorem. The evidence and limitations appear below.

The new numerical comparison supports the relevance of the control at the
sealed amplitude: the selected uncontrolled circle appears already broken
at ε = 0.0012, whereas the controlled one is well resolved there.
This comparison is numerical evidence, not an additional Lean theorem.

The recommended publication unit is the common certificate method together
with the magnetic and two lunar applications. The magnetic example alone is
a plausible computational-dynamics paper if the exact-model comparison and
reproducibility material receive enough attention.

## 2. What the frozen statement actually proves

The controlling declaration is `KAM.Magnetic.magnetic_barrier` in
[`MagneticBarrier.lean`](../../../KAM/Frozen/Magnetic/Theorems/MagneticBarrier.lean).
Read it with the six frozen definitions in
[`KAM/Frozen/Magnetic/Defs/`](../../../KAM/Frozen/Magnetic/Defs/).
The accessible description is [`Magnetic.md`](../../results/Magnetic.md).

The amplitude is exactly ε = 3/2500 = 0.0012; both angular variables have
period one and are represented by real lifts. The model is

\[
h(p)=p-\frac34p^2+\frac13p^3-\frac1{16}p^4,\qquad
a=2\pi(2q-\phi),\quad b=2\pi(3q-2\phi),
\]
\[
A=\frac{32000}{2777}\cos a-\frac{96000}{7669}\cos b,\qquad
V=\epsilon(\cos a+\cos b)+\frac{1427}{3200}\epsilon^2 A^2.
\]

The field-line equations are q̇ = h′(p), ṗ = −V_q, φ̇ = 1.
The autonomous extension is H = J + h(p) + V(q,φ).
The dummy action J accounts for the clock; energy zero is not a claim
that the physical magnetic energy vanishes.

The fixed rotation number is

\[
\alpha=\frac{7913-\sqrt5}{13618}
=0.580904973712916743303245030572\ldots.
\]

There exists one real-analytic graph p = P(q,φ), periodic in both arguments,
with 8/25 ≤ P ≤ 39/100 everywhere. The same P is tied to an exact invariant
torus of frequency (α,1), with holomorphic lift on the strip of width
3/1000000, real values on real angles, primary periodicity, energy zero,
and clock coordinate φ = θ₁ on the real torus.

For every real initial state the statement supplies a global solution.
Every other solution on an order-connected time set containing zero agrees
with it there. For every real time, a trajectory initially below, on, or
above P remains respectively below, on, or above the same P.
There are no certificate assumptions in the public theorem.

In particular, a trajectory starting with p < 0.32 cannot attain p ≥ 0.39.
The reverse one-sided obstruction holds for trajectories starting above 0.39.
This consequence uses the graph bounds and sign preservation directly.

One separating graph does not bound a slab. Motion below it need not have
a lower flux bound; motion above it need not have an upper flux bound.
The theorem neither proves plasma confinement nor treats charged particles,
MHD stability, coils, dissipation, or parameter uncertainty.

The polynomial is defined on all real p for the global ODE assertion.
Its physical interpretation is limited to the intended flux domain.
The certified graph lies inside that domain, but the polynomial extension
does not become a measured equilibrium profile outside it.

The result page records standard axioms only: `propext`, `Classical.choice`,
and `Quot.sound`, and a kernel certificate in 5,807 generated modules.
These are inherited seal receipts; this task ran no `#print axioms`.
An untrusted numerical producer is not part of the logical assumptions:
the checker and its soundness theorem must discharge its finite output.

## 3. Literature audit and model identity

### 3.1 Comparison table

| Work | Actual subject | Relation to this claim |
|---|---|---|
| Chandre, Vittot, Ciraolo, Ghendrih and Lima (2005/2006), §3, (5)–(8), §4.1 | Exact full feedback; quadratic approximation; magnetic numerics | Establishes the control idea; full feedback differs from the frozen quadratic polynomial. |
| Valvo and Locatelli (2022), arXiv v2 §4, Theorem 2, (61)–(64) | Interval-assisted torus for transformed, truncated H⁽⁰⁾ | Close predecessor, different formal target; see the compact audit below. |
| Kallinikos, MacKay and Martínez-del-Río (2023), §§2–4, Theorem 3.1 | Converse KAM for helical magnetic fields | Excludes specified classes of surfaces; different fields and conclusion. |
| Escande and Momo (2024), §§2–4 | Field-line action principle and magnetic coordinates | Analytical background; no certificate for the frozen model. |
| Martínez-del-Río and MacKay (2025), §§2–4 | Conefield converse KAM and “killends” | Surface nonexistence diagnostics, not this positive existence theorem. |
| MacKay (2025), §§II–VI | Pressure-jump Hamiltonian | Different Hamiltonian and interface problem. |
| Gómez-Serrano, Liehr and Taylor (2026), Theorem 1.1, §16 | Lean-certified MHS equilibria with nested pressure tori | Earlier formal magnetic surfaces; not this Diophantine field-line KAM certificate. |
| Yu (2026), `arnold1963-kam`, release v1.0.0 | General nondegenerate analytic Hamiltonian KAM in Lean | Earlier reported formal KAM theorem; no fixed-amplitude instance of this model. |
| Gadgil / PlasmaLean contributors (2026), K3/K4 and N-33 | Explicit magnetic and guiding-centre KAM applications in Lean | Earlier application-level formal KAM; rules out broad first claims. |
| Present sealed result | Literal quadratic-control field at 3/2500; all-time graph separation | Exact original model, explicit literals, kernel certificate and ODE conclusion. |

Primary references and exact URLs are listed in §11.
The comparison is about exported conclusions and model identity, rather than
the occurrence of “rigorous,” “formal,” or “KAM” in a title.

### 3.2 The closest computer-assisted predecessor

ArXiv v2 Theorem 2, p.14, covers transformed, Fourier-truncated H⁽⁰⁾,
§4 (61)–(64), at ε = 0.003, α from (12), RI = 150, RII = 8500.
The trusted interval C implementation (§3.1) includes `INTERVAL`,
`int_arit_lib.c`, `expl_transf.c`, `iteration+proof.c`, and Xρóνoς inputs.
The run took about 62 hours on two Xeon Gold 5220 CPUs with 384 GB
installed RAM; peak use and CPU-hours are unspecified.
No proof-assistant kernel or rigorous original-model tail transfer is supplied.
The numerical §2 barrier-region threshold 0.0045–0.0046 is not interchangeable
with this α-circle threshold. The scope distinction does not refute their CAP.
[Valvo–Locatelli, arXiv v2](https://arxiv.org/pdf/2101.07785v2).

Published in J. Comput. Dyn. 9 (2022), 505–527; publisher full text was
restricted here. Equation/page locators above refer specifically to arXiv v2.
[Publisher record](https://www.aimsciences.org/article/doi/10.3934/jcd.2022002).

### 3.3 Why the full feedback theorem does not settle this model

Chandre et al.'s exact surface construction uses the full feedback (5),
with graph (7); equation (8) retains only the quadratic contribution.
For quartic h, the omitted cubic and quartic feedback terms generally remain.
Consequently the exact full-feedback argument cannot simply be cited as an
exact invariant-graph proof for the frozen quadratic-only V.
[Chandre et al., §§2–4 and Appendix A](https://arxiv.org/html/nlin/0504033v2).

Independent substitution of p_c = 7/20 gives
h′(p_c) = 18777/32000 and h″(p_c) = −1427/1600.
Thus −h″(p_c)/2 = 1427/3200; the two homological ratios are precisely
32000/2777 and −96000/7669. The frozen choice is the general-(8) choice.
The exact invariant graph of a different, fuller control is not a substitute.

There is also a frequency distinction: h′(p_c) is about 0.58678125,
whereas the certified α is about 0.58090497. Choosing a control centre
does not automatically impose the desired exact rotation number.

### 3.4 Earlier proof-assistant work must be acknowledged

Yu's v1.0.0 release is dated 8 October 2026, source `7985c9b`, archived
at DOI 10.5281/zenodo.23232025. The source-facing scope describes actual
analytic tori, original-Hamiltonian trajectories, and a large-measure result.
The documented audit example is one-dimensional; semantic self-review and
standard-axiom checks are reported, independent peer review is not.
This report inspected the scope and review records, not a new kernel replay.
[Release](https://github.com/ybq1415926-droid/arnold1963-kam/tree/7985c9b),
[scope](https://github.com/ybq1415926-droid/arnold1963-kam/blob/7985c9b/docs/SCOPE.md),
[review](https://github.com/ybq1415926-droid/arnold1963-kam/blob/7985c9b/docs/REVIEW_STATUS.md).

PlasmaLean is the closer application-level precedent. The snapshot inspected
is `79b6152e779a62287da76fb4a49918e38575b3d6`, dated 4 November 2026.
Its `KamTorusAExact.lean` supplies `torusA_exact`, at rotational transform
(75+√5)/562, by supplying concrete constants to its KAM iteration.
`RationalStellaratorConfinedForever.lean` then proves
`rationalStellarator_confined_forever` for that exact rational field.
The latter statement bounds every supplied two-sided field line starting
inside the torus; its displayed conclusion should be read with that premise.
[Exact torus source](https://github.com/siddhartha-gadgil/PlasmaLean/blob/79b6152e779a62287da76fb4a49918e38575b3d6/PlasmaLean/Design/KamTorusAExact.lean),
[trapping source](https://github.com/siddhartha-gadgil/PlasmaLean/blob/79b6152e779a62287da76fb4a49918e38575b3d6/PlasmaLean/Design/RationalStellaratorConfinedForever.lean).

Its N-33 note also records concrete Dommaschk and guiding-centre instances,
the exact residual interface and certificate machinery; dated updates put
the Dommaschk torus and nested pair on 1–2 November 2026.
Those claims were read as primary project evidence, not independently rebuilt.
They suffice to prevent a responsible assertion of worldwide first priority.
[N-33](https://github.com/siddhartha-gadgil/PlasmaLean/blob/79b6152e779a62287da76fb4a49918e38575b3d6/notes/theory/dommaschk-kam-certificate.md),
[dated model history](https://github.com/siddhartha-gadgil/PlasmaLean/blob/79b6152e779a62287da76fb4a49918e38575b3d6/notes/theory/dommaschk-qa.md).

Gómez-Serrano–Liehr–Taylor was submitted on 21 September 2026.
Theorem 1.1 and §16 concern smooth magnetic equilibria with nested pressure
tori; §16.9 distinguishes the explanatory `sorry` showcase from the proved
companion and reports standard axioms. Its magnetic leaves carry closed
field lines in the construction, rather than the present irrational rotation.
[Paper](https://arxiv.org/abs/2609.24739),
[formalization](https://github.com/lukasliehr/Grad-Conjecture).

A search hit titled “a KAM criterion ... gives invariant tori” explicitly
takes the KAM implication as an argument. Its own page says Lean does not
check the KAM theorem. It is not a competing completed KAM application.
[Exact claim and displayed declaration](https://gocheckyourself.org/result/three-body/result-37/).
Likewise, the Lean evaluation problem is a benchmark statement, not evidence
that the displayed `sorry` has been eliminated in a completed application.
[Benchmark](https://lean-lang.org/eval/problems/kam_invariant_curve/).

### 3.5 Search coverage and remaining priority uncertainty

The public search covered 2022–10 November 2026 using combinations of
“magnetic field lines,” “rigorous,” “computer-assisted,” “invariant torus,”
“transport barrier,” “Lean,” “proof assistant,” “Coq” and “Isabelle,” plus
the predecessor's title and authors. The two named reference repositories
were located through GitHub's repository search and inspected directly.
The downloaded Valvo–Locatelli v2 PDF matches the plan's pinned SHA-256:
`02e3daaa037cdcb243ff82bbb9478d95027de61c9c29a10becb097b60bf0148e`.

Positive follow-up hits included the 2023 and 2025 converse-KAM papers,
the 2025 pressure-jump paper, the 2024 action-principle paper, and the
2026 magnetic-equilibrium formalization. None targets this literal V.
No relevant later proof for the exact quadratic-control coefficients was found.
There was no exhaustive citation-index export or audit of every private repo.

Generic KAM theory already gives small-perturbation existence for suitable
analytic models. Therefore “first rigorous for this model” must mean an
explicit nonzero amplitude with the stated frequency and conclusion; an
unqualified claim would confuse a concrete certificate with classical theory.

## 4. Numerical question, model and algorithms

Every number in §§4–6 is an untrusted floating-point diagnostic.
The uncontrolled potential deletes the ε² term and changes nothing else.
The controlled runs use exactly the frozen factored expression above.
Neither model uses the printed specialized control from the earlier papers.

The Poincaré section is φ ∈ ℤ. The requested circle rotation is α in
poloidal turns per forcing period, not its reciprocal or an angular frequency
in radians. The code retains the 2π factors in V_q and V_qq explicitly.

Two independent computational formulations were used.
The Fourier formulation solves the continuous-time invariance equation,
which simultaneously supplies a circle for the period-one map.
The periodic-orbit formulation works directly with the field-line flow.

### 4.1 Direct parameterization and refinement

Write q = θ + u(θ,φ), D = α∂θ + ∂φ and
p = (h′)⁻¹(α + Du). The remaining equation is L = Dp + V_q = 0.
Odd Fourier coefficients fix phase. The quasi-Newton correction solves
D(a DW) = −N L, with N = 1+u_θ and a = N²/h″(p), and sets Δu = NW.
Two diagonal cohomological solves impose the appropriate zero means.

Grids were 64², 128², 256², 512², and, for controlled refinement, 1024².
The retained Fourier rectangle uses |k|,|l| ≤ floor(N/3).
Continuation starts at ε = 0, normally increases by 0.0001, and halves
the step to 0.000003125 on failure. A damped step must lower the residual.
Acceptance is sampled sup |L| < 3·10⁻¹¹; at most 35 iterations are used.

Each requested successful candidate is evaluated after zero-padding to
a (2N)×(2N) mesh. This checks sampled aliasing effects;
it does not enclose an infinite Fourier tail or certify a complex strip.
The residual sum of coefficient magnitudes becomes roundoff dominated
as the grid grows. Its increase alone is not evidence of torus destruction.

### 4.2 Periodic orbits and Greene residues

The α continued fraction is [0;1,1,2,1,1,2,3,1,1,...].
Convergents used include 7/12, 18/31, 61/105, 79/136 and 140/241.
The periodic orbit continues from h′(p₀) = m/n on each of the symmetry
lines q₀ = 0 and q₀ = 1/2, by solving q(n/2) = q₀ + m/2.
These are reversible branches, not a claim to enumerate every periodic orbit.

The integrator is a fourth-order Yoshida composition of exact Hamiltonian
drifts and kicks in extended phase space, including the clock drift.
Its tangent matrices are differentiated analytically through those maps.
For half-period matrix [[a,b],[c,d]], reversibility gives residue R = −bc.
Independent integration over the full period checks R = (2−tr M)/4.
The determinant defect checks numerical area preservation.

Production used at least 64 steps per forcing period, with 32/64/128
refinement at selected orbits. A batch uses the longest denominator's step
count, so shorter-period members actually receive finer time steps.
Branch loss is reported as a solver limitation, never assigned a residue.
Finite Greene sequences estimate breakup; they are not a nonexistence proof.

### 4.3 Independent consistency checks

Finite differences of the literal potential agree with the coded force to
8.1·10⁻¹² and its q derivative to 1.3·10⁻¹⁰ on the fixed validation points.
At ε = 0, periodic shooting is the integrable rotation and residues vanish.
Full-period matrices reproduce the half-period residue formula; see §5.

For controlled candidates, 24 points on φ = 0 were evolved one period
and compared with the parameterization shifted by α. Step doubling from
32 to 64 to 128 to 256 resolves the integration error independently of FFT
residuals. The two methods therefore do not share the same numerical solve.
At 0.003 the momentum errors are 1.074·10⁻⁸, 6.712·10⁻¹⁰,
4.194·10⁻¹¹ and 2.608·10⁻¹², showing the expected fourth-order refinement.

## 5. Numerical results

### 5.1 The two requested amplitudes

| Potential | ε | Numerical verdict for the selected α circle |
|---|---:|---|
| Uncontrolled | 0.0012 | Appears broken; residues grow beyond the estimated breakup. Direct torus attempts fail. |
| Controlled | 0.0012 | Well resolved; consistent with the independently sealed theorem. |
| Uncontrolled | 0.003 | Far beyond the observed breakup; direct attempts fail and rapid inter-region transport occurs. |
| Controlled | 0.003 | Well resolved numerically; no Lean certificate at this amplitude is asserted. |

For the controlled model, independently repeated mesh results are:

| ε | N | sampled sup residual | sampled p range | minimum sampled 1+uθ |
|---:|---:|---:|---|---:|
| 0.0012 | 256 | 4.43·10⁻¹² | [0.327983356884, 0.385661649946] | 0.760292577250 |
| 0.0012 | 512 | 4.63·10⁻¹² | [0.327983356884, 0.385661649946] | 0.760292577250 |
| 0.0012 | 1024 | 4.96·10⁻¹² | [0.327983356884, 0.385661649946] | 0.760292577250 |
| 0.003 | 512 | 5.71·10⁻¹³ | [0.285547685110, 0.430009537427] | 0.477778184759 |
| 0.003 | 1024 | 1.11·10⁻¹² | [0.285547685110, 0.430009537427] | 0.477776855225 |

At N = 1024, padded sup residuals are 5.72·10⁻¹² at 0.0012 and
2.00·10⁻¹² at 0.003. The corresponding coefficient sums are about 5·10⁻¹⁰.
These are real-mesh diagnostics, many orders above the production
multiprecision certificate gate, and must not be advertised as new certificates.

The sampled extrema are stable to the displayed precision; derivative minima
at 0.003 have several micro-units of sampling variation. Quoting additional
digits for the latter would obscure the remaining angular sampling error.

The uncontrolled direct attempts at both requested ε were made separately
from the last accepted candidate on 128², 256² and 512² grids.
All failed the same explicit residual/monotonicity acceptance criteria.
Failure strengthens the residue evidence but cannot itself exclude a circle.

### 5.2 Breakup of the uncontrolled α circle

Positive-branch residues from the 64-step production/refinement are:

| ε | 7/12 | 18/31 | 61/105 | 79/136 |
|---:|---:|---:|---:|---:|
| 0.00092 | 0.226376 | 0.148785 | 0.073173 | 0.071889 |
| 0.00094 | 0.252991 | 0.199172 | 0.199087 | 0.262298 |
| 0.00095 | 0.267231 | 0.229983 | 0.326592 | 0.496821 |
| 0.00096 | 0.282123 | 0.265221 | 0.533859 | 0.935382 |
| 0.00100 | 0.348694 | 0.463403 | 3.676812 | 10.968089 |

The transition from decay with denominator to rapid growth suggests
ε_break ≈ 0.00094; retain [0.00092,0.00096] as a conservative numerical
transition window. It is not a certified upper/lower existence bracket.
At 140/241 the positive-branch residue is about 0.19962 at 0.00094;
one companion branch loses shooting convergence there and is excluded.

At ε = 0.0012, the 18/31 positive branch gives R = 5.91944263
at 64 steps and 5.91944302 at 128; 32 steps gives 5.91943648.
The full-period residue agrees within 9·10⁻⁹, with full-period position
and momentum closure below 2·10⁻¹¹ and determinant defect below 6·10⁻¹².
At ε = 0.00105 the 61/105 branches already have residues about
37.57 and −49.90; high-period shooting becomes increasingly fragile.

The strict spectral acceptance limit moves from 0.000425 at N = 128 to
0.00068125 at N = 256 and 0.00080625 at N = 512. These are resolution
limits of that solver, not three different physical breakup thresholds.

### 5.3 Controlled breakup and distance from it

For the controlled model, the transition is near ε = 0.00426.
Positive-branch residues at 64 steps are:

| ε | 18/31 | 61/105 | 79/136 | 140/241 |
|---:|---:|---:|---:|---:|
| 0.00420 | 0.114938 | 0.154078 | 0.119547 | 0.072170 |
| 0.00426 | 0.144719 | 0.268704 | 0.247060 | 0.261003 |
| 0.00435 | 0.205503 | 0.617117 | 0.728059 | 1.786446 |
| 0.00450 | 0.369920 | 2.422815 | 4.205069 | 41.815279 |

Retain [0.00420,0.00435] as a conservative numerical transition window,
with central estimate 0.00426. It is not a validated existence bracket.
The 1024² spectral solver reaches only 0.003840625 before its strict
residual tolerance fails; this again reflects resolution, not physical breakup.
Companion shooting branches lose convergence before the surviving positive
branch; those failed orbits were not used as evidence of an earlier breakup.

For 140/241 at 0.00426, step refinement gives R = 0.260004885
(32), 0.261002595 (64), 0.261065073 (128), consistent with fourth order.
At 0.00420 the 128-step value is 0.072187833; at 0.00430 it is 0.614462713.
Shooting closure is below 6·10⁻¹¹ in those checks and determinant defects
below 5·10⁻¹². The refinement leaves the stated transition window unchanged.

Relative to this estimate, 0.0012 is about 28% of controlled breakup,
and 0.003 is about 70%. The uncontrolled estimate is about 4.5 times smaller;
0.0012 is already about 27% above it. These ratios describe the selected
circle and this literal control, not all surviving barriers of either family.

The largest ε here means the apparent termination of the α-circle branch
continued from ε = 0 near p ≈ 0.3566. A finite continuation cannot establish
a global supremum over all parameter values, disconnected branches or reappearance.
The quoted uncertainty includes this interpretation and finite-denominator limits.

### 5.4 Direct finite-time transport

Sixty-four initial angles q₀ = j/64 were integrated for 512 periods.
At 0.0012 the initial momentum was 0.31, below the theorem's lower bound;
at 0.003 it was 0.27, below the sampled controlled graph's lower extent.
The runs compare identical initial grids in the two potentials.

At 0.003, an uncontrolled trajectory with q₀ = 33/64 reaches
p = 0.46168534955 by period 7 using 64 steps, 0.46168534978 using 128,
and 0.46168534979 using 256. This is a well resolved rapid crossing.
The 32-step uncontrolled ensemble has 59/64 trajectories above 0.45;
the controlled ensemble has none and sampled maximum p = 0.407584.

At 0.0012 the 32-step uncontrolled ensemble reaches 0.397578, but its
earliest apparent crossing does **not** survive refinement: the same seed
has maximum about 0.383216 through period 180 at 256 steps. Reject that
crossing as evidence. The controlled ensemble's sampled maximum is 0.364644.
The 0.0012 breakup verdict therefore rests on residues and parameterization,
not a falsely validated chaotic-trajectory comparison.

No observed crossing in a finite controlled ensemble would establish an
invariant circle. Its role is a consistency check; the controlled proof at
0.0012 comes from the sealed theorem. A numerically resolved crossing for
the uncontrolled potential obstructs a graph confined to that flux window,
but still does not exclude every conceivable barrier elsewhere.

### 5.5 Is control needed at the sealed amplitude?

**Numerically, yes for the selected α barrier.** The evidence places
0.0012 above the uncontrolled α-circle breakup and well inside the controlled
survival range. The fallback amplitude therefore does not merely certify
a circle that our comparison finds intact without control.

This is a comparison of the specified two families. It proves neither optimal
control nor the absence of all uncontrolled invariant circles, and there is
no formal nonexistence theorem for the uncontrolled α circle in this package.

## 6. Reproduction, resource use and retained evidence

The small scripts to commit are in `scripts/magnetic/pitch/`:
`circle_scan.py`, `greene.py`, `diagnostics.py`, `transport.py`, and `reproduce.sh`.
They use Python and NumPy; the short continued-fraction cross-check also
used mpmath at 60 decimal digits. No SciPy, Lean, Lake or native certifier ran.

Each production numerical command used the required prefix:

```sh
systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  python3 -B scripts/magnetic/pitch/circle_scan.py \
    --model controlled --max-n 1024 --out .drafts/mag-pitch/repro-controlled
```

Run the uncontrolled scan similarly with `--model uncontrolled --max-n 512`.
The output path is scratch; neither generated candidate arrays nor downloaded
papers belong in the commit. Original runs used the same scripts in scratch.
All scripts inherit a hard 3,500-second CPU limit, below 60 CPU-min/job.
`bash scripts/magnetic/pitch/reproduce.sh` reproduces the complete numerical
sequence sequentially in `.drafts/mag-pitch/reproduction/`, with every job scoped.
The driver records process CPU; measured costs are summarized below.

For residues, the initial production command was:

```sh
systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  python3 -B scripts/magnetic/pitch/greene.py --model controlled \
    --max-den 241 --spp 64 --stop .0045 --step .00005 \
    --out .drafts/mag-pitch/repro-greene-controlled.json
```

`--resume FILE` restarts from the last epsilon where every requested branch
was accepted. `--tolerance` controls the shooting stopping test; failed
branches remain explicitly marked. Refinement commands and summarized
outputs are retained under `.drafts/mag-pitch/`, as are the literature downloads.

Python was 3.12.3, NumPy 2.5.0 and mpmath 1.3.0.
Fourteen retained numerical JSON receipts total 1,624.1 CPU-seconds of timed
calculation (27.1 CPU-min), including exploratory repeats. Imports and the
small metadata/continued-fraction checks are outside these loop timers;
even a conservative additional five CPU-min keeps the campaign below 33 CPU-min.
The longest timed job was 587.4 seconds; the highest peak RSS was
986,308 KiB (0.94 GiB), comfortably within the 4 GiB scope limit.
No job approached either the 3,500-second hard CPU cap or the memory cap.
The largest controlled scan took 271.8 timed CPU-seconds; the uncontrolled
scan took 21.5. Literature downloads and source-only guards are not numerics.

The numerical limit was 3 CPU-hours in total; it is a ceiling, not a target.
No production certificate was regenerated. The report distinguishes elapsed
time, process CPU and peak RSS; the systemd cgroup supplied the actual memory cap.

## 7. What is new, and how to describe it

The contribution is a complete chain from a literal nonlinear Hamiltonian
through a finite numerical certificate and a formal KAM theorem to a real
all-time separation statement. The original equations remain the target;
there is no unpaid normal-form truncation remainder at the public conclusion.

The graph and dynamics clauses matter: an invariant parameterization alone
would not provide the stated global solutions, common graph witness and
strict side preservation for every initial state and both time directions.
The exact constants and narrow holomorphic strip make the result inspectable.

The numerical comparison adds a useful scientific interpretation of the
fallback choice. The controlled theorem lies beyond the apparent loss of
the corresponding uncontrolled α circle, even though it is comfortably
below controlled breakup. That claim must retain its numerical qualifier.

The local implementation also demonstrates reuse of one certifier across
applications with different geometry. This is an engineering and formalization
contribution even in light of other proof-assistant KAM developments.
Do not infer a speed or memory advantage over another project from unmatched
hardware, modules, strip widths, amplitudes or trust policies.

## 8. Headline, abstract and publication framing

### Suggested headline

**A kernel-checked transport barrier for an explicit controlled field-line model**

For a broader article:
**Kernel-checked KAM certificates: magnetic barriers and lunar spin dynamics**

Both communicate the theorem's subject without relying on a disputed first.
Avoid “plasma confined forever,” “fusion solved,” “first rigorous magnetic
barrier,” and “first formal KAM theorem.”

### Abstract-length summary

We give a Lean 4 proof of an all-time transport barrier for an explicit
time-periodic Hamiltonian model of magnetic field lines. At perturbation
amplitude 3/2500, with a prescribed quadratic control term and quadratic
irrational rotation number, a finite certificate proves an analytic invariant
torus for the original Hamiltonian. A geometric and ODE argument turns this
torus into a periodic graph with flux in [0.32,0.39], supplies unique global
field lines, and proves that no trajectory crosses the graph in either time
direction. Certificate soundness and the application are checked by Lean's
kernel with standard axioms. Separate numerical comparisons indicate that
the corresponding uncontrolled circle is already broken at this amplitude.
The result concerns one exact mathematical model and one separating surface;
it does not assert plasma confinement or the physical realization of control.

### Venue options and reasons

| Venue / audience | Recommended emphasis | What would improve the submission |
|---|---|---|
| Journal of Automated Reasoning | Trusted checker, soundness, model correspondence, reusable arithmetic | Package the lunar and magnetic applications with a reproducible proof inventory. |
| Certified Programs and Proofs | Certificate construction, efficient kernel checking, formal mathematics | A concise methods paper with artifact instructions and rejection tests. |
| Journal of Computational Dynamics | Explicit original-model theorem and quantitative validation | Larger ε, threshold diagnostics, and fair comparison with interval CAPs. |
| Journal of Plasma Physics / plasma audience | Exact field-line barrier and significance of control | More physically grounded field models, control realizability and parameter robustness. |

The first two recommendations follow the venues' stated coverage of proof
assistants and certification; JCD explicitly covers new computational methods
for dynamics. These are editorial-fit judgments, not acceptance predictions.
[JAR scope](https://link.springer.com/journal/10817/aims-and-scope),
[CPP series](https://popl27.sigplan.org/series/CPP),
[JCD scope](https://www.aimsciences.org/jcd).
No conference deadline or presently open submission window is assumed here.

### Standalone versus the lunar collection

A standalone magnetic article has one clear target and a close literature
comparison. Its weakness is a single small-amplitude example in a longstanding
control literature. The exact-model and all-time formal conclusion should
therefore carry the paper, with the floating-point comparison clearly separate.

A collection better exhibits reusable mathematics and implementation.
The lunar band gives two barriers and a spin-rate slab; the lunar lock gives
a solid-torus trapping argument around a periodic orbit; the magnetic example
gives one graph barrier in another application area.
[Lunar band](../../results/SO-2.md), [lunar lock](../../results/SO-3.md).
Their physical model qualifications must remain separate in a joint abstract.

Prefer the collection for a formal-methods venue. Prefer a standalone magnetic
paper for a dynamics venue only if the controlled/uncontrolled comparison,
source normalization and quantitative certificate cost are developed fully.
Neither framing should represent this task as a fresh audit of those proofs.

## 9. Additional results with the highest value

1. **Certify ε = 0.003 for this same V and α.** The numerical circle exists
   at the tested resolution; the previous multiprecision gate missed its
   weighted target. Improve resolution and finite-candidate enclosures rather
   than confusing a double residual with certificate smallness.
   This needs a separately approved statement with its own amplitude and bounds.
2. **Prove a controlled/uncontrolled separation.** A rigorous converse-KAM
   obstruction, a validated crossing with suitable topological consequences,
   or an uncontrolled certificate below breakup would turn the numerical
   comparison into a theorem with an explicit scope.
3. **Add a second magnetic barrier.** This would bound a genuine slab for an
   explicit initial window; one cannot obtain two-sided confinement merely
   by retitling the existing one-sided result.
4. **Certify a parameter interval.** Uniform statements in ε or control
   strength would show robustness beyond one rational sample.
5. **Measure the checker fairly.** Publish cold/warm replay commands, CPU,
   elapsed time, peak cgroup memory, certificate bytes and exact trust base.
6. **Connect to a realizable field.** Control spectra, equilibrium constraints
   and coil errors would strengthen plasma relevance, but require new models.

The first and third give the most direct extensions of the existing proof.
The second most directly strengthens the scientific case for control.
The fourth is stronger evidence of robustness than a finer plot of one torus.

## 10. Source defects, deviations and verification scope

The following items are reported here, without editing frozen sources,
the errata ledger, generated roots or the result page.

* `Magnetic.md`, final source/proof paragraph: “No kernel-checked certificate
  chain for it is on `main` yet.” This contradicts that page's sealed status
  and the actual frozen `by exact` provider body at this input snapshot.
* `Magnetic.md`, ε bullet: “the planning value 3/1000 was not attempted.”
  The plan's §4 records multiprecision attempts at that value. A precise
  reading is “not certified/sealed,” or “not attempted in the fallback run.”
* Chandre et al. v2 (14), “−d(1/q)/dψ”: the coefficient lacks the
  factor 1/2 obtained by substituting action-independent forcing into (8).
  This inherited candidate discrepancy is why the literal general-(8)
  expression is always specified; no silent source repair is made.
* Valvo–Locatelli v2 (7), “k₁ω̃+k₂”: missing imaginary unit; (8)/(10),
  “−ε²/2” and “−9/2 cos(6θ−4ϕ)”: inherited order/sign/divisor discrepancies
  (plan §8). Implementation correctness was not audited.

The frozen Lean declaration itself was not found defective by this source
reading. Its reported standard-axiom status comes from the existing result
record, not new computation. The freeze proposal is historical evidence;
its draft `sorryAx` printout must not be described as the sealed axiom list.

The brief forbids Lean and Lake. Consequently the usual repository handoff's
targeted build, fresh axiom printout and full `scripts/lint_sources.sh` were
not run: inspection shows the lint script calls `abi_hashes.py`, which invokes
`lake env lean`. Static checks that do not invoke Lean are listed below.
This follows the task-specific restriction and is not a clean-build claim.

| Check | Exact output / result |
|---|---|
| `python3 -B scripts/gen_root_imports.py --check` | exit 0, no output; generated files unchanged |
| `python3 -B scripts/render_errata.py --check` | exit 0, no output |
| `python3 -B scripts/check_lean_modules.py --root .` | `check_lean_modules: PASS (29057 Lean files, 0 comparator configurations)` |
| `python3 -B scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json` | `FROZEN-ANCHOR GUARD OK`, exit 0 |
| Python AST parsing of the four numerical scripts | all four `syntax OK` |
| `bash -n scripts/magnetic/pitch/reproduce.sh` | exit 0 |
| Report link, line-count and member-name checks | PASS |
| `git diff --cached --check` | exit 0, no output |

The source-only frozen guard completed normally after about twelve minutes;
it was not interrupted. No ABI elaboration or kernel replay is implied.
The local commit uses the hook's documented `HQ_UPDATING=1` bypass to avoid
the generated-HQ/README post-commit action prohibited by this brief.

## 11. Primary references

* Chandre, Vittot, Ciraolo, Ghendrih and Lima (2006), *Control of stochasticity
  in magnetic field lines*, Nuclear Fusion 46, 33–45; 2005 preprint v2,
  [§3 (5)–(8), §4.1, Appendix A](https://arxiv.org/html/nlin/0504033v2).
* Valvo and Locatelli (2022), J. Comput. Dyn. 9, 505–527,
  [DOI](https://doi.org/10.3934/jcd.2022002);
  [arXiv v2, §§2–4, Theorem 2](https://arxiv.org/pdf/2101.07785v2).
* Kallinikos, MacKay and Martínez-del-Río (2023), *Regions without flux surfaces
  of given class for magnetic fields in toroidal geometry*, Plasma Phys.
  Control. Fusion 65, 095021, [paper](https://doi.org/10.1088/1361-6587/acea3f);
  [published erratum, 129602](https://doi.org/10.1088/1361-6587/ad0853).
* Escande and Momo (2024), *Description of magnetic field lines without arcana*,
  Reviews of Modern Plasma Physics 8, 16,
  [paper](https://doi.org/10.1007/s41614-024-00152-9).
* Martínez-del-Río and MacKay (2025), *Conefield approach to identifying regions
  without flux surfaces for magnetic fields*, Plasma Phys. Control. Fusion 67,
  055005, [§§2–4](https://arxiv.org/abs/2501.06796).
* MacKay (2025), *Invariant tori for the pressure-jump Hamiltonian*, Physics
  of Plasmas 32, 052507, [paper](https://arxiv.org/abs/2501.10353).
* Gómez-Serrano, Liehr and Taylor (2026), *Counterexamples to Grad's conjecture*,
  [Theorem 1.1 and §16](https://arxiv.org/abs/2609.24739).
* Yu (2026), *Arnold 1963 KAM in Lean 4*,
  [v1.0.0 archive](https://doi.org/10.5281/zenodo.23232025).
* Gadgil / PlasmaLean contributors (2026), the dated source snapshot and exact
  declaration links in §3.4; source inspection, not independent proof replay.

The committed deliverable is this report and its small numerical scripts.
Downloaded papers, candidate arrays, logs and JSON receipts remain scratch.

## Addendum (2026-11-10): PlasmaLean, corrected comparison and timeline

Checked against PlasmaLean's Lean sources at `79b6152e779a62287da76fb4a49918e38575b3d6` and its commit history.

- **Existence of field lines is proved there too.** Besides `rationalStellarator_confined_forever` (which quantifies
  over given two-sided field lines), PlasmaLean proves `rationalStellarator_confined_forever_exists`
  (`PlasmaLean/Design/RationalStellaratorFieldLines.lean`): every starting point on the axis or inside the torus has a
  unique field line for all time (`∃! γ, IsFieldLine (field (1/4)) γ ∧ γ 0 = x₀`), and all such lines stay inside.
  Global existence and uniqueness is therefore not a distinguishing feature of this repository's result.
- **Timeline.** PlasmaLean's verified-KAM confinement for its exact stellarator field dates from 2026-10-20 (commits
  `a30b3d62`, then `a9a042f4` adding field-line existence), before this repository's magnetic statement was frozen
  (2026-11-01, D68) and sealed (2026-11-10). No PlasmaLean commit or source refers to this repository; the two
  projects developed independently and converged on similar kernel-scale techniques.
- **Comparison, as it stands.** PlasmaLean: earlier, physically richer (an exact 3-D vacuum field; trapping in a solid
  torus around the magnetic axis; guiding-centre and alpha-particle extensions), KAM via one Newton step with explicit
  constants. This repository: a general kernel-checked certificate method demonstrated on three systems (two lunar,
  one magnetic), an exact controlled field-line Hamiltonian, and numerical evidence that the control creates the
  barrier at the sealed amplitude.
