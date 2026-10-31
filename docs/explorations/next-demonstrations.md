# The next two KAM demonstrations

30 October 2026. IDEAS-NEXT, branch `ideas`, base commit
`540ba7fdbb1e72a7081dbb7bd4ace1a17d9f3e51`.
Research and numerical feasibility study: **no new torus is certified here**.
Only this report is committed; experiments and downloads are under `/tmp/ideas-astra/`.
No Lean process, build, GitHub operation or implementation edit was performed.

## Executive summary

**Recommend a magnetic transport barrier, followed by Mercury's 3:2 spin confinement with exact
Kepler forcing.** Both use the existing canonical, two-degree-of-freedom **isoenergetic** theorem
and certifier. The magnetic example opens a different application area; Mercury offers a named,
readable result with particularly small numerical data.

| Rank | Demonstration | Novelty to pursue, subject to a priority check | Fresh numerical evidence | Certificate design estimate | Projected kernel cost |
|---|---|---|---|---|---|
| **1** | An impenetrable surface in a controlled magnetic field-line model at ε = 0.003 | Fully formal barrier for the explicitly specified, untransformed quadratic-control model | 512² grid; real residual 1.41·10⁻¹²; flux range 0.28555–0.43001 | Classical-constant v2 A′ tolerance ≈ 1.17·10⁻²³; target error 10⁻²⁵; 10–16k full Fourier keys | **40–180 CPU-h per torus**, sharded; one torus for non-crossing |
| **2** | All-time Mercury spin confinement near 3:2, with untruncated Kepler forcing | Fully formal confinement; removal of the forcing truncation is the mathematical extension to investigate | Both barriers converge on 256×96 grids; residuals 1.3–1.4·10⁻¹²; observed spin deviation ≤ 0.017348 | Same engine: tolerances ≈ 3.80·10⁻²³ and 3.12·10⁻²³; target 10⁻²⁵; 1.5–2.5k full keys each | **8–40 CPU-h per torus**, **16–80** for the pair |

Thresholds evaluate the current design mirror on **sampled bounds**, not interval or kernel
certificates. Supports and costs are projections. These experiments achieve approximately twelve
digits on the real torus, **not** the twenty-five-digit strip error needed by the proposed
certificates. Actual multiprecision enclosures are the next decision gate.

Two corrections to [the earlier scout](striking-applications.md) affect the recommendation:

- Mercury already has rigorous trapping tori: the original Celletti–Falcolini (1992) abstract
  explicitly describes rigorously constructed separating invariant surfaces. “First rigorous
  Mercury trapping result” would be wrong. [Original article](https://doi.org/10.1007/BF00049460).
- The scout's uncontrolled magnetic calculation is not the controlled ε = 0.003 problem.
  Moreover, Valvo–Locatelli's Theorem 2 names the **truncated transformed** Hamiltonian
  \(H^{(0)}\), not the original Hamiltonian before that truncation.
  [VL21, §4, equations (61)–(64), Theorem 2](https://arxiv.org/pdf/2101.07785v2).

The report recommends exact mathematical models, not confinement of a real plasma device or a
complete physical model of Mercury.

### Baseline technology and evidence

The checkout contains `routeARefinedR` and `routeAV2'` in
[RouteARefinedRefEngine.lean](../../KAM/CertificateSharp/V2/RouteARefinedRefEngine.lean), and
`checkTorusCertificateV2_sound` in [Engine.lean](../../KAM/CertificateSharp/V2/Engine.lean).
The `sqrt` expression, compiler, ball arithmetic and composition implementation have also landed:
[Expr/Basic.lean](../../KAM/Certificate/Expr/Basic.lean),
[Expr/BallSqrt.lean](../../KAM/Certificate/Expr/BallSqrt.lean).
The old “needs a sqrt node” estimates are stale.

| Evidence | What it establishes |
|---|---|
| [APOST-SHARP-V2 §11–12](../campaign/design/APOST-SHARP-V2.md) | Finite comparisons of theorem formulas, not universal dominance or an application certificate |
| [C6](../campaign/handoffs/SHARP2-C6.md), [C6L8](../campaign/handoffs/SHARP2-C6L8.md) | Toy tori and kernel evaluation of lunar numerical cores at supplied bounds; those tests do not establish a lunar torus |
| [Hybrid design](../campaign/design/APOST-SHARP-V2-HYBRID.md) | Proposed restart; R1 truncations give 23 half-lattice terms and a threshold near 10⁻⁵·²⁸, versus 87 terms for plain v2; design and sampled evidence |
| This report | New double-precision tori, sampled engine inputs, resource projections |

I have **not** transferred R1's hybrid tolerance to these candidates. It depends on the actual
correction, linearized residual, transfer margins and final displacement. The composition still
needs fine accuracy. After the hybrid lands, measure those quantities here; it is an optional
saving, not a prerequisite.

Both proposed Hamiltonians are linear in the dummy clock action. Their ordinary twist is
degenerate; use the **bordered isoenergetic twist**, never its inverse as a substitute for an
ordinary twist inverse in a fixed-frequency theorem. The hybrid design §4.5 explains the same
issue for R1. Rüssmann's qualitative theorem does not supply these concrete error tolerances.

## 1. Magnetic field lines: a surface that cannot be crossed

### Exact model, audience and novelty

Use period-one angles \((q,t)\), flux action \(p\), and clock action \(J\). Define **the proposed
model itself** by

\[
\begin{aligned}
h(p)&=p-\tfrac34p^2+\tfrac13p^3-\tfrac1{16}p^4,\qquad p_c=7/20,\\
\omega_c&=h'(p_c)=0.58678125,\qquad h''(p_c)=-0.891875,\\
a&=2\pi(2q-t),\qquad b=2\pi(3q-2t),\\
A(q,t)&=\frac{2\cos a}{2\omega_c-1}+\frac{3\cos b}{3\omega_c-2},\\
H_\varepsilon&=J+h(p)+\varepsilon(\cos a+\cos b)
 -\tfrac12h''(p_c)\varepsilon^2 A(q,t)^2,\qquad \varepsilon=3/1000.
\end{aligned}
\]

This selects the **general quadratic-control formula (8)** in Chandre et al. Their specialized
(14), and VL21's displayed control formulas, disagree with that formula; see the discrepancy
ledger below. This is an explicit model choice, not an identification of incompatible formulas.
The equilibrium and two forcing modes follow the papers. All coefficients above are rational
apart from the Fourier \(2\pi\).
[Chandre et al., arXiv v2, (8), (11)–(14)](https://arxiv.org/pdf/nlin/0504033v2).

The target is an analytic invariant graph \(p=P(q,t)\), with a rational flux enclosure, which
field-line trajectories cannot cross. It provides researchers in Hamiltonian control and
magnetic topology with a verified finite-parameter barrier, rather than a Poincaré plot.
It says nothing about particle confinement, plasma stability, transport rates or a specified
coil geometry.

The novelty would be **formal verification of this controlled model and its non-crossing
conclusion**. Magnetic KAM barriers and computer-assisted proofs already exist; the local
PlasmaLean comparison also precludes a broad “first formal magnetic torus” claim. VL21 reports
62 hours for \(H^{(0)}\), with \(R_I=150,\ R_{II}=8500\), on a workstation with 384 GB installed
RAM. Installed RAM is not measured peak usage. Certifying the original explicit model would
avoid a transformation-truncation transfer; priority for that narrower result remains unchecked.
[VL21, §4](https://arxiv.org/pdf/2101.07785v2).

Do not assert that the uncontrolled system has no barrier: numerical failure does not prove
nonexistence. Also, the full feedback law with an explicitly constructed invariant surface is a
different, less informative KAM demonstration than this quadratic truncation of that law.

### Fit with Lean

- **Two degrees of freedom, canonical and analytic:** quartic in \(p\), finite trigonometric
  polynomial in the angles. Existing `const`, `action`, `add`, `mul`, `pow` and `cosMode` suffice.
  Expanding \(A^2\) gives four control harmonics and a constant. No noncanonical theorem or chart
  inversion is needed.
- **Frequency and energy:** target energy zero and
  \(\omega_D=(43+18\varphi)/(74+31\varphi)=0.5809049737129167\ldots\),
  \(\varphi=(1+\sqrt5)/2\), with vector \((\omega_D,1)\), as in VL21 (12).
  Its continued fraction is \([0;1,1,2,1,1,2,3,\overline1]\). Use the conservative
  \(\gamma=1/10,\tau=1\), after an infinite Diophantine proof. The finite scan below is not one.
- **Strict ray convention:** final reference frequency is \((\omega_D,1)/(1+2\cdot10^{-6})\),
  nominal scalar \(s=1+2\cdot10^{-6}\), with correspondingly scaled \(\gamma\). This leaves
  room for the design frequency margin \(\nu=10^{-6}\). Diagnostics used \(s=1\);
  the final certificate must use the strict interior ray and recompute its bounds.
  The clock identity recovers a unit clock in the conclusion.
- **Non-crossing:** adapt [SpinOrbit/Graph](../../KAM/SpinOrbit/Graph),
  [SpinOrbit/Barrier.lean](../../KAM/SpinOrbit/Barrier.lean) and `KAM.ODE.gen_barrier`.
  The SO wrappers contain lunar-specific data, so are ingredients, not a ready magnetic theorem.
  One torus proves non-crossing; a bounded flux slab needs two ordered barriers or a separately
  justified inner boundary.

### Fresh experiment and quantitative feasibility

Continuation used 30 increments of \(10^{-4}\), additive isoenergetic Newton, reversibility
projection (\(u\) odd, actions even), and a \(2\cdot10^{-15}\) coefficient cleanup. Without that
cleanup an uncleaned 320² solve stalled earlier than a smaller grid: high-mode numerical noise
can mimic breakup.

| Quantity | 256² | 512² refinement |
|---|---:|---:|
| Real invariance residual | 6.52·10⁻⁹ | **1.41·10⁻¹²** |
| Flux minimum / maximum | 0.285547686 / 0.430009538 | 0.285547685 / 0.430009537 |
| Minimum \(1+\partial_1u_1\) | 0.477778149 | 0.477778185 |
| Full nonzero keys above 10⁻¹² | 934 | **1112** |
| Full nonzero keys above 10⁻¹⁴ | 1218 | **1662** |
| Wall time, including analysis | 81.5 s | 148.6 s |
| Peak RSS | 1.01 GiB | **3.83 GiB** |

Geometry is stable, but the changing high-mode counts show that 256² is insufficient for a tail
claim. At \(\rho=.003,\rho_\infty=.000003,\mu=.002\), the sampled bounds are

| Input | Value |
|---|---:|
| \(M,M_1,M_2\) | 153.357, 3.353, 153.357 |
| \(\sigma_K,\sigma_B,\sigma_{T^{ext}}\) | 3.5471, 6.0249, 1.8335 |
| \(\sigma_{L^T},\sigma_N,\sigma_{N^T}\) | 4.8824, 2.3146, 3.5821 |
| Initial torsion supremum | 15.4479 |

With 10% sampling slack and 10% internal budgets, **classical-constant route A′ with three
explicit stages** gives \(\log_{10}e_*=-22.93195\), binding at the tail error condition.
This is a sufficient-tolerance estimate, not a physical breakup threshold.

Coefficient cuts \(L=6,8,10\) give sampled weighted-ℓ¹ residuals
\(4.43\cdot10^{-4},1.50\cdot10^{-5},5.43\cdot10^{-7}\). The fitted log error is
\(1.015-0.7280L\). Extrapolating to \(10^{-25}\) gives **\(L\simeq36\)** and
**10–16k full embedding keys**, with 40% support allowance. Character/inverse witnesses need
separate counts. This extrapolation is unvalidated.

Plan **70–90 decimal working digits** and **192–256-bit fixed-point certificate arithmetic**,
with outward radii paying for every truncation and rounding. The slowest fitted decay is
0.0621 decimal digits per mode: the production grid may need 1024–2048 points in that direction.
Stream derivative bounds/FFT work arrays to remain below 8 GB; do not scale up the probe's
full third-derivative tensor unchanged.

Reserve **40–180 CPU-hours per torus**, including composition, frames and torsion; reassess at
200 hours. No candidate kernel shard ran. Main risks: normalization, rigorously required support,
and accumulation of model radii.

### Packages, order and first decision

| Order | Package | Estimated size | Acceptance condition |
|---|---|---|---|
| M0 | Model and source reconciliation | Source note; 200–400 Lean lines after approval | Independently settle coefficient/sign/divisors; owner approves exact model and statement |
| M1 | Multiprecision producer | 500–1000 Python lines | Two resolutions agree; error plus radii ≤ 10⁻²⁵; ≤ 16k embedding keys; witness sizes reported |
| M2 | Frequency and certificate assembly | 500–1000 Lean lines, excluding data | Infinite Diophantine inequality, frequency box, all sub-checks, full kernel certificate |
| M3 | Field-line graph and non-crossing | 900–1700 Lean lines | Positive graph derivative after certified displacement; rational flux enclosure; non-crossing |
| Optional M4 | Second barrier or parameter box | New data; 200–500 assembly lines | Nonempty ordered slab or actual uniform box checks |

Total bespoke Lean before M4: **1.6–3.1k lines**, plus data and review; roughly **2–4 weeks**
after the numerical gate. These are planning estimates; split packages into files of at most
1500 Lean lines. Future Lean briefs must repeat all eleven AGENTS.md hard rules and follow
the normal statement-approval pipeline.

**First cheap confirmation/kill experiment:** symbolic M0 comparison, then a 70-digit solve at
ε=.003 and a certificate-mirror pass for invariance and graph checks. Budget half a day and 8 GB.
Stop the flagship if the weighted tail cannot reach 10⁻²⁵ within the support budget, or the graph
margin disappears. A clearly relabeled ε=.0012 pilot is the fallback. The double-precision part
of the ε=.003 test is already positive.

## 2. Mercury: all-time spin confinement with exact forcing

### Model, significance and novelty

Use conservative planar spin–orbit dynamics on a prescribed Kepler ellipse, with zero obliquity,
\(e=257/1250=.2056\), and \(\varepsilon=3/20000=.00015\). These are the **historical benchmark
values** in Celletti–Chierchia (1998), Table 1, not current geodetic estimates.
[Source and original TeX](https://web.ma.utexas.edu/mp_arc-bin/mpa?yn=98-581).

The public target is readable: every initial spin in a certified window around 3/2, at every
initial angle, remains in an explicit spin band for all time. For celestial mechanicians, the
useful extension is the **untruncated Kepler forcing** and full formal verification.

Celletti–Falcolini already proved Mercury trapping tori. I read its publisher abstract but could
not access the full article, so claim neither mathematical priority nor an improvement over its
exact band. [Celletti–Falcolini 1992](https://doi.org/10.1007/BF00049460).
This target is spin-rate confinement, not libration of the resonant angle, capture, or tidal
evolution. Moon-lock's distinct librational geometry is already an active campaign.

### Exact expression and required bridges

Let \(w\) be eccentric anomaly divided by \(2\pi\), \(r=1-e\cos(2\pi w)\), and

\[
c_f=\frac{\cos(2\pi w)-e}{r},\qquad
s_f=\frac{\sqrt{1-e^2}\sin(2\pi w)}{r},\qquad q=Q+\tfrac32w.
\]

The expression computed in the experiment is

\[
H_K=P_2-\tfrac32p+
r\left[\frac{p^2}{2}-\frac{\varepsilon}{2r^3}
\left(\cos(4\pi q)(c_f^2-s_f^2)+2\sin(4\pi q)c_fs_f\right)\right].
\]

It uses existing nodes and **one constant square root**. Keep that root exact; a decimal
replacement changes the model. Its operand \(1-e^2\) is positive rational. On the real torus
\(r\ge.7944\); on a complex domain use \(1-e\cosh(2\pi r_w)>0\), with \(r_w\) bounding the
entire clock domain.

Derivation: apply
\(\phi=w-e\sin(2\pi w)/(2\pi),\ J=U/r\), multiply the pulled-back Hamiltonian by \(r\)
**on energy zero**, then set \(Q=q-3w/2,\ P_2=U+3p/2\).
On that level \(X_{rH}=rX_H\); positivity transfers trajectories and confinement by a monotone
time change. This avoids an inverse Kepler function and any Taylor/Hansen truncation.

Two obligations deserve explicit packages:

1. **Half-integer shear:** \(q=Q+3w/2\) is not an integer shear of a period-one torus.
   Work on the double orbital-angle cover \(w\bmod2\), or carefully use the body's half-turn
   orientation quotient. An integral-coordinate version is \(w=2r_0,\ q=Q+3r_0\), with Hamiltonian
   \(2H_K(Q,2r_0,p,J_2/2)\). Certificates here concern \(H_K\): lift their graphs to the double
   cover, prove confinement there, then project trajectories. Do not assert a global
   period-one symplectomorphism.
2. **Time change:** invariant sets and bounds transfer, but the displayed linear-flow
   parameterization does not transfer automatically. Confinement needs only the positive
   time-change lemma; physical-time quasiperiodicity would need an additional time conjugacy.

Thus use the existing **canonical isoenergetic** engine in two degrees of freedom, with a
bordered twist. New Lean concerns model identity, cover/time transport and graph assembly.
Reuse the SO graph and ODE ingredients. No general noncanonical KAM theorem is needed.

### Fresh experiment and budget

Choose rotating frequencies \((\nu_\pm,1)\), where
\(\nu_\pm=\pm1/(74+g),\ g=(\sqrt5-1)/2\).
[QuadraticDiophantineN.lean](../../KAM/Certificate/QuadraticDiophantineN.lean) is the starting
point for \(\gamma=1/76,\tau=1\); prove the infinite inequality and scale to the strict
interior ray as above.

Both signs were computed afresh with 14 perturbation steps and reversible cleanup:

| Quantity | Lower | Upper |
|---|---:|---:|
| Grid | 256×96 | 256×96 |
| Real invariance residual | 1.292·10⁻¹² | 1.356·10⁻¹² |
| Spin minimum | 1.482652152 | 1.509985329 |
| Spin maximum | 1.490056921 | 1.517301355 |
| Minimum \(1+\partial_1u_1\) | 0.7494906 | 0.7495003 |
| Full nonzero keys above 10⁻¹² / 10⁻¹⁴ | 190 / 268 | 190 / 274 |
| Estimated \(\log_{10}e_*\), classical A′ | −22.42048 | −22.50548 |

Combined time including analysis: **63.5 s**, peak **0.45 GiB**. The band agrees with the earlier
scout, now tested for both signs in the untruncated expression; this is not independent interval
validation.

Design inputs: \(\rho=.01,\rho_\infty=10^{-5},\mu=.002\).
Lower/upper \(M=69.571/71.937,\sigma_K=1.757/1.764,\sigma_B=2.611/2.623\),
\(\sigma_{T^{ext}}=1.1154\), and torsion suprema 14.383/14.851. With 10% slack/budgets and
three classical-constant stages, the tail error condition binds.

For the lower torus, cuts \(L=6,8,10\) give weighted residuals
\(9.66\cdot10^{-5},3.00\cdot10^{-6},8.24\cdot10^{-8}\).
The fitted log error \(0.589-0.7673L\) predicts **\(L\simeq34\)** for \(10^{-25}\), or
**1.5–2.5k full keys** per embedding. The upper torus is similar. Plan **70–90 working decimal
digits**, **192–256 certificate bits**, and test a 512×192 or larger dealiased production grid.
Count reciprocal and character witnesses independently.

A conservative **proposed, unfrozen** observable is

\[
p(0)\in[1.492,1.508]\ \Longrightarrow\
|p(t)-3/2|\le.018\quad(t\in\mathbb R),
\]

for all initial angles. Recompute literals from certified graph bounds. The .018 is in units
of orbital mean motion, not 1.8% of Mercury's spin rate. Include global existence and uniqueness,
using bounded spin and nonsingular periodic forcing.

Reserve **8–40 CPU-hours per torus**, **16–80** for the pair. Exact Kepler forcing has more
operations than the lunar polynomial, although clock-only factors are one-dimensional. Main
risks are reciprocal enclosure inflation, the cover/time-change bridge, and validated tail
growth. A parameter-box theorem would be a separate uniform certification, not an interpretation
of these two exact parameter literals.

### Packages and first decision

| Order | Package | Estimated size | Acceptance condition |
|---|---|---|---|
| R0 | Model, parameters, statement | 200–400 Lean lines after approval | Exact model/observable approved; exact square root |
| R1 | Producer for both signs | 600–1200 Python lines reusing SO tools | Two-resolution agreement; bounded error ≤ 10⁻²⁵; ≤ 2.5k embedding keys each |
| R2 | Eccentric-anomaly identity and time change | 400–800 Lean lines | Exact zero-energy identity; positive time correspondence |
| R3 | Cover transport and ordered graph barriers | 500–1000 Lean lines | Well-defined lifted graphs and all-phase initial window |
| R4 | Frequency, certificate and ODE assembly | 300–600 Lean lines, plus data | Kernel certificates and global confinement theorem |

Total bespoke Lean **1.4–2.8k lines**, plus data/review; estimate **1–3 weeks** after the numerical
gate and shared SO tools. R1 and the geometric proofs are independent tasks; sealing waits for both.

**First cheap confirmation/kill experiment:** an 80-digit lower torus, followed by mirror
Hamiltonian, invariance, energy and graph checks using the exact sqrt expression. Compare
256×96 against 512×192 weighted tails. Budget half a day. Stop/change the chart if radii still
dominate after increasing precision, or support exceeds 5k keys without sufficient margin.
Then repeat for the upper torus. Before full kernel evaluation, benchmark one reciprocal/character
witness and one product shard under an 8 GB watchdog.

## Shared resource model and handoff

### Kernel costs and machine limits

The CPU ranges include composition, frame and torsion work. Their baseline is
[CERTIFIER-SHARPNESS §4.2](../campaign/design/CERTIFIER-SHARPNESS.md): 35–95 seconds and
0.7–0.9 GB **per compose operation** on an 8.5k-term lunar model, projecting 20–53 CPU-hours
for repeated compositions. Scale by expected model support and expression size, then allow for
products, witness growth and refined frame checks. This is a planning model, not a measured
candidate runtime or a complexity theorem.

A fresh first-jet trace gives 13 product/witness operations for the factored magnetic expression,
38 for exact Mercury, and 3 for the lunar reference. It omits full derivative-jet and some
character-power work; many Mercury operations are clock-only. It is a warning against treating
these clients as identical-cost lunar data, not an exact operation count.

- Target **≤ 8 GB RSS per kernel job**, below the 10 GB kill limit. Bound product shards and
  split compositions into checked intermediate results. A provisional 3–7 GB per module/shard
  budget must be measured by the first benchmark. No whole-certificate peak is established here.
- One targeted kernel/build process at a time. Keep the application's producer/checker working
  set below 24 GB, leaving room under the 32 GB user cap; stop the producer during kernel runs.
- Use **classical small-divisor constants** initially. C6's R1 module used 10.4 GB;
  C6L8's extra single bite used 18.8 GB and the module 19.2 GB. Splitting only the module cannot
  fix that single-bite failure. Rounded or internally blocked arithmetic is a prerequisite for
  those large enumerations; none was rerun.
- Require separately a multiprecision mirror pass, a small memory benchmark, and a full kernel
  certificate. Never raise heartbeat/recursion limits. Heavy generated data belongs in opt-in
  targets. Keep SO-owned checker changes coordinated with that campaign.

The **10⁻²⁵ targets are inferred feasibility goals, not achieved errors**. LG00's multiprecision
success demonstrates relevant producer techniques, not the validity of these tails. The
LG00 prep (`docs/explorations/lg00-prep.md` on the unpublished branch `lg00-prep`) and SJS studies
were read without duplicating that separately assigned campaign.

### Suspected source defects and explicit deviations

These are **candidates for independent review**, not approved ledger entries. No source,
frozen declaration, manifest or errata ledger changed. Relevant formulas were checked in
rendered PDF pages.

| Local ID | Location and short quoted fragment | Why it is suspect; disposition |
|---|---|---|
| IDEA-VL-1 | VL21 v2, p. 2, (7), denominator `k₁ω̃+k₂` | The printed exponential convention requires an \(i\) in the inverse derivative. Differentiation does not recover (6). |
| IDEA-VL-2 | VL21 v2, p. 3, (8), `−ε²/2 {X}²h₂`; (10), `−9/2 cos(6θ−4ϕ)` | \(v\) in (3) already includes ε, so the prefactor double-counts ε when \(X\) solves (6); the two expressions in (8) disagree in sign. Equation (10) lacks the divisors required by (6). Do not use this chain as an identity. |
| IDEA-CH-1 | Chandre et al. v2, p. 9, (14), `−d(1/q)/dψ` | The general formula (8), p. 7, gives half this coefficient when \(H_1\) is action-independent. Our model selects (8). |
| IDEA-CH-2 | Same paper, p. 11, `≈ 35ε` | Its maximum-cosine-coefficient norm applied to (8) at .35 gives approximately \(64.3251\varepsilon\). Here the largest control coefficient is .000578926, or 19.3% of ε. Recheck conventions before quoting a control percentage. |

Separate scope observation, not a refutation: VL21's Theorem 2 concerns \(H^{(0)}\), whose
truncation is explicit in (64); transferring it to the original model needs a tail estimate.

Our deviations are the explicit quadratic-control choice, exact Kepler forcing, the diagnostic
ray's later move to a strict interior scalar, sampled rather than certified majorants, and the
Mercury double-cover transport. None is silently inserted into a frozen statement.

### Reproduction and verification receipt

Repository ingredients at the pinned base commit:
[kamlib.py](../../scripts/apps_scout/kamlib.py),
[models.py](../../scripts/apps_scout/models.py),
[thresholds_v2.py](../../scripts/apost_sharp/thresholds_v2.py).
The speculative `thresholds_est.py` “v2” column was **not** used.

~~~sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 /tmp/ideas-astra/probe.py quadratic 256
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 /tmp/ideas-astra/refine_mag.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 /tmp/ideas-astra/mercury.py
OPENBLAS_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 /tmp/ideas-astra/threshold_scan.py
~~~

Receipts are `quadratic-256.json`, `quadratic-512.json`, `mercury.json`, `threshold-scan.json`,
logs, and `.npz` embeddings in that scratch directory. Archive scratch before beginning the
campaign: it is **not durable committed evidence**. The formulas, settings and method above
also permit reconstruction from the pinned scripts.

Threshold reconstruction: \(n=2,\tau=\kappa=1\), displayed \(\rho,\rho_\infty,\gamma,\mu\),
\(\nu=10^{-6},\Theta_\omega=2,c_{Th}=2M_1\); `kamlib.package` supplies Hamiltonian bounds.
Measure \(L^T,N,N^T,T\) on four strip corners. Use `with_caps(D, 1/10)` and `thresholdA`
with `L1`, `omega_eta`, `avg_full_bite`, `keep_delta`, `caps_tilde`, `free_budgets` and `b5`,
`torsion_cap = torsion_real = Tsup_cap`, `iso=True`, `k=3`,
`c_stages(D, 'classical', 3)`. Rationalizing sampled numbers does not prove upper bounds:
the certificate's domain/frame checks must replace them.

Support rule: fit log residual at \(L=6,8,10\), extrapolate to \(10^{-25}\), multiply the
\(L=12\) full-key count by \((L/12)^2\), and add 40% allowance. Do not fit \(L\ge12\) residuals:
weighted floating-point noise is already significant. The finite magnetic divisor scan through
denominator 100,000 gives minimum 0.394655 for \((|p|+|q|)|q\omega_D-p|\); only the planned
infinite Diophantine proof can certify \(\gamma\).

| Artifact | SHA-256 |
|---|---|
| `probe.py` | `e46afba6a1e0c1a2d5d64d40ec0b3d1af519d105750128719534937d0745d59b` |
| `mercury.py` | `d7877af3cd935fa462b74bf8548e5ce0b19dcde74764c135611578efbda110dd` |
| `refine_mag.py` | `74b6865bbe7b53e7e5d02557cf89b53196c138d012ebbdb3610851bc2172875d` |
| VL21 v2 PDF | `02e3daaa037cdcb243ff82bbb9478d95027de61c9c29a10becb097b60bf0148e` |
| Chandre et al. v2 PDF | `e63bf2eea3ac49a97308a7b6493e24de8bdc688f179fbcb4a70b4a8be7b40153` |
| Celletti–Chierchia 1998 TeX | `e24cc302023106c0fb38a71dff335640670451873b5920e5a25c1e59cb188660` |

Checks and limitations:

- Numerical scripts completed successfully; maximum measured Python RSS was 3.83 GiB.
  No interval enclosure or kernel certificate was produced.
- `scripts/lint_sources.sh` was run with a transparent `python3 -B` wrapper refusing only its
  ABI subprocess, which writes `.lake/abi-scratch` and invokes Lean outside this brief's scope.
  **Partial lint, not PASS:** `check_lean_modules: PASS (1813 Lean files, 0 comparator configurations)`;
  `FROZEN-ANCHOR GUARD OK`; a pre-existing 101-character line at
  `kernel-tests/CertificateSharp/V2/C6L1R1.lean:39`; `ABI CHECK SKIPPED`. Exit 1.
  Log: `/tmp/ideas-astra/lint.log`.
- No targeted build or `#print axioms` was run: no Lean declaration changed and the brief forbids
  builds. Axioms of future application theorems remain to be checked.
- Local Markdown file links resolve; scratch receipts parse; listed artifact hashes match.
- Staged whitespace check and one-file commit verification are the final repository checks.

## Candidates not selected for the next launch

- **Sun–Jupiter–Saturn, including LG00:** separately assigned; the later feasibility/prep reports supersede the initial scout, and no duplicate experiments were run.
- **Moon lock or another lunar band:** active owner-approved SO work; complete that campaign.
- **Golden standard-map circle:** excellent later flagship, but needs a map theorem and map small-divisor/validation machinery; flow v2 does not apply. Rigorous existence at 0.9716 already exists. [FHL17, §6.1](https://arxiv.org/pdf/1601.00084v1).
- **Accelerator thin-lens/Hénon maps:** the same map-theorem gap; higher-dimensional tori also do not automatically bound a dynamic aperture.
- **Real-coil stellarator or the PlasmaLean example:** noncanonical geometry and field-data validation are larger additions; duplicating PlasmaLean is not a broad novelty claim.
- **FPUT/lattice nonthermalization:** needs normal-mode reduction, suitable twist/nonresonance and higher-dimensional data; one torus does not prove that typical initial data fail to thermalize.
- **Hénon–Heiles/molecular dynamics:** promising after a resonant-chart pilot; the previous scout's failed oscillator continuation provides no feasibility evidence.
- **Exact restricted three-body/Trojans:** more chart/denominator cost; truncated Victoria is closer but adds less application range to this pair.
- **Kicked-rotor atom optics or generic engineering oscillators:** the former needs maps/discontinuous-time treatment; the latter is cheaper but less distinctive than the magnetic-control benchmark.
- **Time-periodic fluid particle paths:** good follow-up using the magnetic wrapper; an imposed streamfunction does not establish an Euler/Navier–Stokes solution.
- **Nonlinear PDE tori:** track W is already approved and active; finite-dimensional certificates do not control its infinite tail.
- **Euler vortex leapfrogging:** a separate source/design route with a larger analytic interface, as in [the existing exploration](pde-kam-and-leapfrogging.md).
