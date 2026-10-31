# Plan: a magnetic field-line barrier at ε = 0.003

30 October 2026. DEMO-PLANS; branch `demo-plans`, input commit
`377591e0fd09d8abe64d06e2a127cc570f7a80c5`. Planning evidence, not an approved
statement or a certificate. The companion is [Mercury 3:2](plan-mercury-32.md).

**Recommendation:** fund the multiprecision/finite-certificate gate before
committing to the full kernel run. This remains the proposed first demonstration
in a new application area; Mercury currently has stronger direct-certificate
numerical evidence. Prove one separating graph at the exact model below. A
second barrier is a separate project. Use plain isoenergetic v2 with classical
small-divisor bounds
as the reproducible baseline; adopt the hybrid only after its implementation,
audits, and this candidate's measured restart checks pass.

The previous [demonstrations study](next-demonstrations.md) supplies a good
numerical start, not the required strip enclosure. This plan adds an explicit
public statement, concrete expression coefficients, graph-transfer budgets,
worker boundaries, and a resource-gated certificate pipeline. Fresh numerical
receipts and their limitations are in §4 and §9.

## 1. Exact model and proposed theorem

### 1.1 Model to approve

Let angles be real lifts with period one. Set

\[
\begin{gathered}
 p_c=7/20,\quad \epsilon=3/1000,\quad
 h(p)=p-\tfrac34p^2+\tfrac13p^3-\tfrac1{16}p^4,\\
 \omega_c=h'(p_c)=18777/32000,\qquad h''(p_c)=-1427/1600,\\
 a=2\pi(2q-\phi),\quad b=2\pi(3q-2\phi),\qquad
 A=\tfrac{32000}{2777}\cos a-\tfrac{96000}{7669}\cos b,\\
 V(q,\phi)=\epsilon(\cos a+\cos b)
       -\tfrac12h''(p_c)\epsilon^2 A^2,\\
 H((q,\phi),(p,J))=J+h(p)+V(q,\phi).
\end{gathered}
\]

This is the **quadratic control chosen from the general formula (8)** in
[Chandre–Vittot–Ciraolo–Ghendrih–Lima, v2](https://arxiv.org/pdf/nlin/0504033v2),
with their equilibrium and two modes. It is the definition of the proposed
model. Do not identify it with their inconsistent specialized (14), the full
feedback law, or Valvo–Locatelli's printed (10). The disagreements are listed
in §8. The source is read as data, not as executable software.

An exact expansion gives the following control coefficients. The constant
stays in the energy-zero model; dropping it would require shifting the named
energy level.

| Fourier cosine key | Coefficient in the control term |
|---|---:|
| `(0,0)` | `6586872735384/11338856098924225` |
| `(4,-2)` | `51372/192793225` |
| `(6,-4)` | `462348/1470339025` |
| `(1,-1)` | `-308232/532420325` |
| `(5,-3)` | `-308232/532420325` |

Add coefficients `3/1000` at `(2,-1)` and `(3,-2)`. These are cosine
coefficients, not complex Fourier coefficients: each nonzero cosine contributes
half to each of its two opposite keys. Prove equality of the expanded and
factored expressions before using either compiler output. No new `HamExpr`
constructor is needed.

The field-line ODE, on `Fin 3 → ℝ` ordered `(q,p,φ)`, is

\[
 F(q,p,\phi)=(h'(p),-\partial_qV(q,\phi),1).
\]

The time variable here is the toroidal angle divided by `2π`; the angle `q` is
the poloidal angle divided by `2π`, and `p` is the source's flux variable. The
radian change gives `dq/dt = h'(p)` and `dp/dt = -∂q V` with precisely the
factors of `2π` displayed above. Work on all real lifts; the certified barrier
lies inside the physical flux interval `(0,1)`. The polynomial extension beyond
that interval is a mathematical convention, not a statement about a device.

### 1.2 Exact torus and barrier claim

Define

\[
 \varphi_g=(1+\sqrt5)/2,\quad
 \alpha=\frac{43+18\varphi_g}{74+31\varphi_g}
       =\frac{7913-\sqrt5}{13618},\qquad \omega=(\alpha,1).
\]

Target an analytic primary embedding `K∞` of the two-torus, represented by a
holomorphic lift on `complexStrip 2 (3/1000000)`, real on real arguments, with

\[
 K_\infty(\theta+k)=K_\infty(\theta)+(k,0),\quad
 DK_\infty\,\omega=X_H\circ K_\infty,\quad H\circ K_\infty=0.
\]

The quotient embedding assertion must be justified by the clock coordinate and
the strict first-angle monotonicity, not inferred merely from the word
`CertifiedTorus`. Phase-translate the clock so that on real arguments it is
`θ₁`; before normalization it is `θ₁+c`. The action component gives an analytic
periodic graph `p=P(q,φ)`, with the proposed rational enclosure

\[
             57/200\le P(q,\phi)\le431/1000.
\]

The graph theorem and the dynamics theorem should share the **same** witness
`P`. Their joint public conclusion is:

- `P` is real analytic and one-periodic in both arguments, has the displayed
  bounds, and its graph is invariant under `F`.
- For every `x₀ : Fin 3 → ℝ` there is a global solution `z : ℝ → Fin 3 → ℝ`
  with `z 0=x₀` and `∀ t, HasDerivAt z (F (z t)) t`.
- Every solution `y` on an order-connected interval `I` containing zero, with
  the same initial value and `KAM.ODE.IsSolutionIn F Set.univ I y`, equals `z`
  at each time in `I`.
- For every real `t`, the sign of `z(t).p - P(z(t).q,z(t).φ)` equals the sign at
  time zero. Equivalently state the three implications for `<`, `=`, and `>`
  separately. Include both time directions and the on-graph case.

This means **the surface cannot be crossed**. It does not mean every field line
has bounded flux: one surface separates two regions but does not bound both
sides. A useful corollary is that data with `p₀ < 57/200` can never reach
`p ≥ 431/1000`, and conversely for data starting above `431/1000`.

The unconditional application theorem has no certificate, inverse-torsion,
smallness, graph, or invariant-set premise. Such premises belong to distinctly
named reusable helpers; the concrete proof discharges them with checked data.

### 1.3 What a referee should accept

The claim is a fully formal, finite-parameter transport barrier for this exact
quadratic-control Hamiltonian, without a transformation/truncation remainder.
Prior magnetic barriers and computer-assisted proofs are acknowledged:
[Valvo–Locatelli v2, §4, Theorem 2](https://arxiv.org/html/2101.07785v2)
concerns the explicitly truncated transformed `H^(0)` of (64). Its reported
62-hour computation and 384 GB installed RAM are not measurements for this
checker. No claim of first rigorous magnetic confinement, first formal magnetic
torus, optimal control, absence of an uncontrolled barrier, charged-particle
confinement, coil realizability, or plasma stability is authorized. Mathematical
priority for the narrower untransformed model remains a literature-audit task.

## 2. Existing Lean path and missing work

### 2.1 Available at the pinned integration commit

1. [The isoenergetic theorem](../../KAM/Iso/Sharp2/G1.lean),
   `KAM.Iso.Sharp2.iso_g1_v2`, combines v1/A/B. The applicable twist is the
   **bordered** average; `H` is linear in `J`. An ordinary twist inverse is not
   an interchangeable hypothesis for a fixed-frequency theorem.
2. [EngineV2](../../KAM/CertificateSharp/V2/Engine.lean) supplies
   `checkTorusCertificateV2_sound` and `checkV2With_sound`, yielding
   `KAM.Certificate.CertifiedTorus` from the actual base checks, a frequency
   enclosure, and an infinite Diophantine proof.
3. [RouteAll](../../KAM/CertificateSharp/V2/RouteAll.lean) supplies `routeV2All`.
   It dispatches on the emitted witness; it does **not** optimize or try routes.
   The default L8′ witness is
   `Sum.inr (Sum.inl (Sum.inl (Sum.inr w)))`, `w : RefinedWitR`.
   Its soundness uses `KAM.Iso.Sharp2.RouteA.Ref.iso_g1_branch_R`.
4. [Clock](../../KAM/Certificate/Clock.lean), `clock_frequency`, proves
   `s∞ ω*₁=1` and the constant clock phase. The generic portions of
   [Graph/Cert](../../KAM/SpinOrbit/Graph/Cert.lean), especially
   `checkSoGraph_sound`, `soGraph_deriv_transfer`, and
   `soGraph_exactTorus_of_certified`, do not require a lunar Hamiltonian.
   They can be used read-only with this certificate.
5. The inverse/ODE wrappers in [Graph/Inverse](../../KAM/SpinOrbit/Graph/Inverse.lean)
   and [Barrier](../../KAM/SpinOrbit/Barrier.lean) do require the lunar field.
   Adapt their proof to a generic clock graph; do not call `so_confinement`
   with a magnetic field. `KAM.ODE.gen_barrier`, `gen_uniqueness`, `gen_maximal`,
   and `gen_confinement` are genuinely reusable.
6. [Kernel/SegBridges](../../KAM/CertificateSharp/Kernel/SegBridges.lean),
   `SegChain`, `ProductSplit`, and `Stage` already support checked composition
   checkpoints, product shards, and Gram/torsion entry assembly.

The [C6](../campaign/handoffs/SHARP2-C6.md),
[C6L8](../campaign/handoffs/SHARP2-C6L8.md),
[C6L1](../campaign/handoffs/SHARP2-C6L1.md),
[C6B](../campaign/handoffs/SHARP2-C6B.md), and
[C6ALL](../campaign/handoffs/SHARP2-C6ALL.md) receipts distinguish toy torus
certificates from arithmetic tests at sampled lunar inputs. None certifies
this magnetic torus. The hybrid C8a–C8d modules are **absent at this commit**;
[their design](../campaign/design/APOST-SHARP-V2-HYBRID.md) is an optional future
dependency, not an available theorem.

### 2.2 Proposed module boundaries

Use a separate repository, provisionally `KAM-demos`, pinned to KAM-dev and its
toolchain/dependencies. Prefixes below denote proposed modules, not existing
files. Its default target contains light definitions/helpers only. Full data,
providers, and concrete theorem assemblies are explicit opt-in targets. Do not
make KAM-dev's generated root depend on them.

| New module | Lines excluding generated data | Obligation |
|---|---:|---|
| `KAMDemos.Magnetic.Model` | 180–280 | Exact `h,V,F,H`, period-one/radian identities, bounded force |
| `KAMDemos.Magnetic.HamExpr` | 180–300 | Both exact expression forms, equality to `H`, clock derivative |
| `KAMDemos.Magnetic.Frequency` | 180–300 | Exact surd/CF data, enclosure, scaled Diophantine theorem |
| `KAMDemos.ClockGraph.Inverse` | 300–450 | Invert a strictly increasing degree-one angle lift, continuous/analytic inverse |
| `KAMDemos.ClockGraph.FromTorus` | 300–500 | Clock theorem, quotient embedding, invariant graph for a generic field |
| `KAMDemos.ClockGraph.Barrier` | 180–300 | Sign preservation from graph invariance and ODE uniqueness |
| `KAMDemos.Magnetic.Global` | 250–400 | Global existence and agreement with every local solution |
| `KAMDemos.Magnetic.Graph` | 150–250 | Magnetic specialization and rational flux/monotonicity margins |
| `MagneticProof.Certificate`, `.Assembly` | 100–180 each | Checked data → torus → the joint public conclusion |

Budget approximately **2.0–3.1k bespoke Lean lines**, plus 0.7–0.9k if the
continued-fraction infrastructure must be ported. The generic graph modules
are shared with Mercury. Keep individual modules below 800 lines where possible,
never above 1500. A facade is cheap and imports only the required modules.

For the frequency proof, the LG00 branch has `CF.CFData.isDiophantine` in
`KAM/Planetary/LG00/CFCertificate.lean`; those modules are **not in this
checkout**. Arrange an audited landing of the generic machinery or port it with
its proofs into the demo dependency. Use
`α=[0;1,1,2,1,1,2,3,overline(1)]`; prove the prefix and golden tail, then
`IsDiophantine (1/10) 1 ![α,1]`. A finite divisor scan is insufficient.
The exact polynomial `6809 α² - 7913 α + 2299 = 0` is a useful independent
identity check, but its crude conjugate-product bound alone is too weak to
justify `γ=1/10`.

For global existence, `|p(t)| ≤ |p₀|+C|t|` follows from the bounded periodic
force; then `|q'| ≤ 1+(3/2)R+R²+R³/4` on `|p|≤R`, and `φ'=1`.
These bounds on every finite time interval feed the existing compact
continuation theorem. Do not claim that the cubic `h'` is globally Lipschitz.

### 2.3 Approval and freeze gate

Before freezing, present complete elaborated Lean commands for the exact model,
frequency, graph predicate if one is public, and joint torus/non-crossing theorem.
The owner must approve: the general-(8) control coefficient; `ε=3/1000`; the
frequency and zero energy; the rational flux bounds; universal real-lift ODE
scope; and the separation-only wording. The strip width is part of the stronger
torus statement and must also be approved. A changed amplitude, weaker band,
or reduced time claim requires a new review; it is not an implementation choice.

No declaration is frozen by this document. The orchestrator performs the freeze
in the demonstration repository only after independent source/binder review.
Workers keep frozen files/manifests read-only. Exact data hashes, the expression
identity and the graph margins must be bound to the final statement; the final
proof must consume the particular checked certificate.

## 3. Producer and certificate pipeline

### 3.1 Numerical producer

Reuse the methods, not the success claim, of
LG00-PREP (`docs/explorations/lg00-prep.md` on the unpublished branch `lg00-prep`):

1. Archive inputs and hashes. Reproduce the 30-step continuation from `ε=0`
   to `.003` with additive isoenergetic quasi-Newton, starting near `h'(p)=α`.
   Preserve energy zero through the dummy action; use the bordered system.
2. Use 80 decimal working digits plus guards (320-bit fixed point is the pilot),
   high-precision residual/FFT and a double-precision preconditioner. Project
   exactly onto odd angle corrections/even actions after each step. Rebuild
   low-amplitude coefficients rather than retaining double-precision noise.
3. Begin at 512², then 1024²; permit an anisotropic power-of-two grid or streamed
   2048 resolution in the slow direction if diagnostics require it. `hpfft.py`
   is radix two: an arbitrary 192-point direction is not supported unchanged.
   Stream gradients and second derivatives. Never allocate the old full
   third-derivative tensor at production grid size.
4. Compare retained coefficients and residuals on a larger dealiased grid;
   record edge mass. Derivative and strip weights are `2πk` and
   `exp(2πρ|k|₁)`, with `ρ=3/1000`, not `exp(ρ|k|₁)`.
5. Emit a **finite** rational/dyadic embedding. Truncation of an unknown exact
   torus need not be proved: the checker must bound the residual of this finite
   object for the exact `H`, including every composition remainder. Agreement
   of grids is a diagnostic, not that bound.

Initial production reservation: 0.5–2 working days for a robust producer,
0.5–4 CPU-hours for solves/scans after it works, 1–6 GB RSS with streaming.
These are estimates; the fresh probe below is narrower. Stop at 7.5 GB and
change the numerical representation before going larger. A measured slow
convergence or aliasing floor changes the numerical gate, not the model.

### 3.2 Exact emitted data and enclosures

Start with `CertFixed 192`; increase to 256 only if the measured rounding ledger
requires it. Store high-precision input at 320–400 bits. Emit:

- exact Hamiltonian AST and its compiled jet, `CertEmbedding` with all four
  components, integer Fourier keys and exact conjugate symmetry;
- rational `π` and exponential-weight enclosures, action-domain centre/radii,
  `weightH`, `cfgFull`/`cfgLow`, all packed-product advice;
- character witnesses generated **from the rounded finite embedding**, including
  keys needed by the expanded control. The factored and expanded expressions
  can have different certified costs; choose after measuring both;
- Gram inverse witness and bordered torsion-average inverse witness, checked
  through Neumann defects; these are suggestions, never assumed inverses;
- every `RefClaim` bound and a route witness, graph lower-bound witnesses, the
  frequency box, and a complete rounding/truncation ledger.

Use a normal form for sparse coefficients which combines equal keys before
bounding. LG00 found that mixed real/imaginary packed products can retain
separate copies of a key and lose cancellation; exact reversibility avoids
much of this problem but is not a proof that every product is single-part.
Check the current mirror against all four product parts when necessary.

Domain selection must certify the **entire** `μ`-ball of the torus, with
`μ=1/500`, not just sampled strip corners. The seven base checks, the refined
Hamiltonian/frame checks, the route core, and graph checks all get separate
receipts. Suggested total target is `err ≤ 10^-25`; allocate at most `2·10^-26`
each to the finite-polynomial residual, character/composition radii, and
rounding/product truncation, leaving `4·10^-26` contingency. This is a budget
to test, not a theorem that those contributions will be attained. Energy error
must separately satisfy the same `params.err` bound.

### 3.3 Frequency ray, route choice and margins

Use `s₀=500001/500000`, `ω*=ω/s₀`, `σω=2`, `νRay=1/1000000`, and
`γ=(1/10)/s₀`, `τ=1`. Prove the scaled infinite inequality and enclose `ω*`
with a rational surd box (zero radius in its rational clock coordinate).
Since `‖ω*‖∞=1/s₀`, the left ray room is
`(s₀-1)/s₀ > 10^-6`. This is why using `s=1` in the numerical diagnostic is
not an admissible final ray. It is the same physical frequency `s₀ω*=ω`;
recompute every certificate bound with the strict interior parameters.
The clock theorem later forces `s∞=s₀` exactly.

| Route | Role in this application |
|---|---|
| Frozen A / frozen B | Cheap correctness baseline; try in the exact mirror, but do not attach refined thresholds to these wrappers |
| Refined A | First fully available candidate; certify its own frame/Hamiltonian claims |
| Refined A, L8′ | Recommended initial emission, three prefix stages, classical constants; benchmark ordinary refined A too |
| ℓ¹ entry | Optional after actual `L1Claim` and `Γ∞` checks; pay the narrower strip and the `coth` amplification of model remainders |
| Refined B | Evaluate the same certificate/caps; its `ρ≤1` guard holds here; retain it only if error or cost improves |
| Hybrid restart | Optional C8 dependency; compare total certificate cost at fixed final graph budget, not residual tolerance alone |

The earlier sampled A′ design threshold is `1.17·10^-23`, giving a nominal
factor **117**, or 2.07 decimal orders, above `10^-25`. A longer prefix gave
only about 0.18 orders. These are **expected sufficient tolerances based on
sampled bounds**, not certified thresholds or a breakup amplitude. Replacing
sampled bounds by exact enclosures may consume all of that margin. Accept the
production package only if its actual rational engine witness passes and leaves
at least a factor ten residual margin after all remainders; otherwise retune
strips/caps, use more coefficients, or stop the gate.

For the graph, aim to certify on the finite candidate
`pLo=2853/10000`, `pHi=4303/10000`, `mono=2/5`, and total
`disp≤1/10000000`. Then Cauchy transfer loses at most `1/30` from the angle
derivative and `10^-7` from each flux endpoint. These imply the public bounds
with room. `checkSoGraph` requires `disp < mono·ρ∞`, not merely small invariance
error. Use its paid SOS-residual mechanism if the coefficient triangle bound
is too weak. For the hybrid `disp` includes the measured first correction.

### 3.4 Hybrid adoption gate

The C8 restart accepts any finite additive correction `ΔK`, not a kernel
small-divisor solver. At restart frequency `ω₁=s₁ω*`, certify

\[
 \widetilde E=E_{\omega_1}(K)+DX_H(K)\Delta K-D\Delta K\,\omega_1,
 \quad e_1\le\|\widetilde E\|+\tfrac12M_2\|\Delta K\|^2.
\]

Also certify the linearized average energy and its quadratic remainder, real
and strip step norms/derivatives, Gram/torsion Neumann margins, reduced domain
budget, reduced ray budget `ν₁=νRay-|Δs|‖ω*‖`, and the final sum
`d∞+D₁`. Search `ρ₁=ρ`, `3ρ/4`, `ρ/2`, always above `ρ∞`. Retain the plain
branch as a fallback. Composition at the coarse `K` still needs accuracy
comparable to `e₁`, here about `10^-25`; coarse input does not authorize coarse
character witnesses.

No magnetic hybrid threshold is measured here. If an actual bound
`e₁≤A e²` and passing transferred caps were obtained, `e≤sqrt(e* /(10A))`
would leave one order of restart error margin. At `e*=1.17·10^-23`, `A=1,100,10000`
would mean roughly `1.1·10^-12, 1.1·10^-13, 1.1·10^-14`. This sensitivity table
is conditional arithmetic, **not** an estimate of `A`. Never import R1's
`10^-5.25` tolerance. Adopt the hybrid only if full witnesses and checkpoints
predict at least a twofold cost saving and the graph budget still passes.

## 4. Numerical feasibility and first cheap gate

Inherited double-precision evidence: at 512² the real residual was
`1.41·10^-12`, flux range `[0.285547685,0.430009537]`, and minimum angle
slope `0.477778185`. The support projection of 10–16k full union keys at a
`10^-25` residual was extrapolated from low-accuracy cuts; neither it nor the
threshold was validated. Full keys are not half-lattice storage terms and are
not the sum over all components. Witnesses and intermediate models are counted
separately.

Fresh pilots used the old 512² start, 320-bit fixed-point residuals/FFTs,
400-bit transcendental evaluation and a double preconditioner. After five
corrections at 512², the real-grid residual stalled near `5.94·10^-14` and
the weighted grid residual near `2.01·10^-11`, despite mean-energy defect
`−2.68·10^-28`. The iteration loop took 338 seconds, excluding initialization;
peak RSS was 894928 KiB (0.85 GiB). Increasing arithmetic precision alone
therefore did not solve the resolution problem.

At 1024², three corrections reduced the real-grid residual to
`8.88·10^-24`, but the weighted grid residual stalled near `5.12·10^-19`.
The mean-energy defect was `−1.48·10^-40`. The loop took 1425 seconds
(23.8 minutes), excluding initialization, and peak RSS was 2712592 KiB
(2.59 GiB). Thus the larger grid improved the weighted diagnostic by about
eight orders, yet still missed `10^-25` by more than six orders. This is a
**failed numerical gate at the tested resolutions**, not a certified barrier
or a disproof of one. It justifies a resolution/finite-support investigation
before budgeting the full checker run.

These norms are floating summaries of MP grid/FFT evaluations. No interval
rounding or infinite composition/aliasing bound is included. As in the Mercury
pilot, purely imaginary/real coefficient projection did not initially enforce
opposite-key conjugacy; exact pairing was checked separately at both resolutions.
The residuals diagnose the real-valued grid function, not a directly emitted
complex certificate. The production producer must enforce exact conjugacy
before every correction and recheck the final finite embedding.

The 512² candidate's unweighted coefficient triangle gives flux interval about
`[.25058,.46484]` and a negative angle-slope lower bound (`−.496`), despite the
good sampled graph. Thus the graph package needs paid SOS residuals even on
the real torus; merely narrowing the strip or increasing precision cannot make
this triangle estimate prove the proposed bounds. The noisy high-mode tail
does not validate the inherited 10–16k support forecast. After exact pairing,
the 1024² arrays retain 9995/12427/16435 union keys at weighted coefficient
cuts `10^-28/10^-30/10^-32`. These are useful size diagnostics, but none of
those finite cuts was re-evaluated with an interval model or shown to meet
the residual target.

The first *remaining* decision experiment is a controlled larger-resolution
and finite-support scan, before full mirror work. Budget half a day initially:
try 2048×1024 if edge mass identifies the first angle as the slow direction,
or stream the necessary grid to stay below 7.5 GB. Require the exactly real
finite candidate's weighted grid residual below `2·10^-26`, retained-coefficient
stability and an explicit support census. Then spend half a day on a
finite-candidate mirror pass for invariance, energy, Hamiltonian domain and
graph bounds. Require weighted error **plus model radii** `≤10^-25` and a
positive graph margin after displacement. Allow at most one additional day
for resolution or measured hybrid restart before reviewing the plain route.
Stop the plain flagship route if it cannot reach that target within roughly
16k union embedding keys and an 8 GB producer. A larger support needs a new
measured kernel budget. A separately labeled `ε=.0012` pilot is a possible
owner decision, not silent completion of `.003`.

## 5. Kernel plan on lemma.farm

The [SO-CSPLIT calibration](../tracks/SO/studies/SO-CSPLIT-GATE.md) is newer
than the original cost estimate. At 96-bit lunar data, sampled segments cost
about `0.13 ms` per census call, packed shards 3–4 seconds, and decoding about
`0.8 ms` per target slot. The largest measured RSS was 7.05 GB (4.05 GB cgroup
charge); imports alone mapped about 3.55 GB. Its complete-torus estimate of
1.6–2.5 CPU-hours is **not** a measurement of these magnetic data, which are
larger and use more bits. Its `B=200k` budget must not be copied blindly.

Production architecture:

1. Emit small literal modules, preferably at most 1000 lines, balanced
   concatenation trees, and short numeral chunks. Every module stays below
   1500 lines and every literal equality is actually forced by the kernel.
2. Check the compiled jet against the literal program. Use `SegChain` and
   `SegBridges` to check composition once and reuse its equality in energy and
   invariance rows. Do not recompute the whole program inside each Boolean.
3. Separate packed-input ties, individual shard groups, decoding, and remainder
   assembly with `ProductSplit`. Start at 8–16 rows per factor block and around
   50k census calls per theorem at 192 bits; these are calibration inputs, not
   a guarantee. Split one expensive operation internally if it exceeds budget.
4. Use `Stage` to prove Gram and torsion entries individually; assemble checked
   matrix/norm equalities into the original tests. Prove graph inequalities and
   each rational engine stage independently. The final soundness application
   imports proved facts and performs no large reduction.
5. Target at most 7 GB RSS, stop an owned process at 7.5 GB, and require every
   successful Lean process to remain below 8 GB. Monitor cgroup charge **and**
   RSS. The site's 10 GB kill limit is not a working budget. Pause producers
   during kernel runs; allow one targeted `nice -n 5 lake build <Module>` through
   the compile gate at a time and stay below the 32 GB total user limit.

First benchmark only representative data: a worst character residual, one
packed product/decode, a composition segment, one Gram/torsion entry, and graph
bounds. Include an intentionally wrong coefficient/advice/radius rejection.
Measure default-heartbeat elaboration as well as kernel time. No declaration
is accepted with a raised heartbeat/recursion limit. A failure triggers finer
sharding or a sound arithmetic change with independent audit.

Use classical small-divisor constants initially. C6's unsharded R1 sites used
10.4 GB, and C6L8's single `l=13` bite used 18.8 GB. Splitting files cannot
repair an oversized individual bite. Frequency-specific enumeration requires
its own rounded/blocked implementation and calibration; it is not necessary
for this baseline. Never build `kernel-tests/` in this campaign.

Reserve **40–180 CPU-hours** for the complete plain certificate including data
elaboration, compositions, geometry and kernel checks. This remains an
unmeasured application estimate. On one serial, shared compile slot, use a
1.5–2 wall/CPU factor: approximately **3–15 calendar days**, including contention,
not a promise of continuous access. Reforecast after the first census/benchmarks;
stop for review if the projection exceeds 200 CPU-hours. Reserve 50–500 MB of
emitted text as an initial disk estimate and measure it before committing data;
checkpoint imports and parse overhead can dominate.

For reproducibility report `Ncalls`, shard count, target slots, theorem count,
literal KB and literal module count. Calibrate each term in
`T = a·Ncalls + b·Nshards + c·Nslots + d·Ntheorems + e·KB + f·Nmodules`
at the actual precision, rather than scaling only the embedding's term count.
A larger machine could use more workers and larger shards or divisor bites;
it changes throughput, not soundness, the tail requirement, or the global
confinement argument. Retain an under-8-GB replay profile for this demonstration.

## 6. Worker packages and milestones

Owners below are roles to assign, not agents launched by this planning task.
Every worker receives the exact input commit, approved statement commands,
allowed files, the hard rules in §10, and a no-overlap boundary with SO/C8.

| Order / owner | Inputs → outputs; size | Checks and stop condition |
|---|---|---|
| **M0 — source/statement lead**, 1–2 days | Pinned PDFs, formulas above and M1's cheap feasibility evidence → source normalization note, audited final Lean statements and owner approval/freeze; 200–350 lines of definitions | Exact rational expansion, coefficient/sign audit, no contradiction hidden by a model name; stop for owner ruling on the (8)/(14) choice |
| **M1 — numerical lead**, 1–3 days | Archived pilot and exact AST → producer, finite candidates at two resolutions; 700–1200 Python lines | Residual/energy/radius ledger and graph gate of §4; stop for support, aliasing or RAM failure |
| **M2 — arithmetic/CF owner**, 1–2 days, alongside M1 | Exact surd and LG00 generic checker → infinite Diophantine theorem and strict-ray enclosure; 180–300 Lean lines plus optional CF port | Prefix/tail kernel checks, negative control, `#print axioms`; stop if claimed `γ` is not actually proved |
| **M3 — certificate producer owner**, 2–4 days | M1 finite data and current checker → complete bit-exact mirror and emitter; 600–1000 Python lines | Every base/refined/core/graph test, witness counts, actual threshold and margin; stop on missing primitive or sample-only bound |
| **M4 — kernel/data owner**, 1–2 days calibration, then §5 | M3 ledger → shard modules, checked checkpoints and certificate theorem; 200–360 Lean glue lines plus generated data | RAM gate, mutation rejection, full forced tests and standard axioms; stop on >7.5 GB, default-heartbeat failure or >200 CPU-h forecast |
| **M5 — geometry/ODE owner**, 4–7 days, alongside M1–M4 | Generic SO ingredients, M0 model → `ClockGraph`, magnetic specialization and global ODE lemmas; 1.2–1.9k Lean lines | All phases, quotient embedding, both time directions, local-solution agreement; no barrier assumed in final result |
| **M6 — independent auditors and integrator**, 2–4 days | M0–M5 → re-audited frozen statements, provider, sealed anchor and handoff | Independent mathematical statement audit; checker/data-consumption audit; clean targeted replay; axiom/dependency audit; stop on any unresolved semantic or data identity mismatch |

M0 drafts before M1 and returns for the approval gate after its cheap numerical
feasibility test. Freeze the exact root commands and meaning-carrying definitions
before assigning application proofs, with a reviewed source-level dependency
plan; untrusted numerical exploration may precede that gate. The certificate
is still an obligation after freezing: a later failure stops the campaign or
requires a newly approved version, never a silent weakening. M5 and M2 can
start after the gate without waiting for the full certificate. M6 audits the
already frozen statements and seals only when their proofs are complete.
Baseline elapsed time is **3–5 weeks** with
several owners and the serial resource gate; a solo worker should budget more.
C8 is optional and must not delay the plain numerical gate. An independent
reviewer should challenge the model, graph separation and data consumption,
not merely rerun the producer.

## 7. Main risks and mitigations

| Risk | Mitigation / concrete failure test |
|---|---|
| Wrong model due to printed control discrepancies | Freeze the explicit rational expression and its exact expansion; report source candidates below |
| Narrow analyticity, slow Fourier decay | Two resolutions, finite-candidate error check; streamed larger grid or audited hybrid; no tolerance inferred from real residual |
| Sampled frame/Hamiltonian bounds too optimistic | Compute actual ball/corner/refined checks early; one-order final margin is an acceptance gate |
| Graph slope survives numerically but not certified displacement | Explicit `mono,ρ∞,disp` budget; paid SOS residual, no plot-based positivity |
| Producer/checker mismatch | Pin mirror commit and all four witness fields; literal jet, product, and model equality tests |
| Repeated composition and long exact rational arithmetic | Checkpoint/shard through proved APIs; outward fixed-point arithmetic; classical constants first |
| Imported CF or hybrid work not landed/audited | Explicit external dependency gate; no hypothetical theorem name in a claimed proof |
| Underestimated data source/import overhead | Census literal bytes and cold RSS; do not import the whole application data graph into every shard |
| Confusing one barrier with a bounded slab | Public sign-preservation theorem; require a new package and statement for a second barrier |

## 8. Suspected errata and declared deviations

All entries are **candidates**, inherited from the previous study and checked
against its pinned PDF pages, not new approved ledger entries. The orchestrator
records them in `docs/errata/ledger.json`; this task does not edit that file.

| ID / source location | Short quoted fragment | Reason and disposition |
|---|---|---|
| IDEA-VL-1 — VL21 v2 p.2 (7) | `k₁ω̃+k₂` | In the displayed complex-exponential convention, the inverse derivative needs the factor `i`; differentiation does not solve (6) as printed |
| IDEA-VL-2 — VL21 v2 p.3 (8), (10) | `−ε²/2 {X}²h₂`; `−9/2 cos(6θ−4ϕ)` | (3) already includes ε in `v`, so (6)'s `X` is O(ε); the extra ε² changes the order. The displayed equal forms also disagree in sign, and (10) omits the homological divisors |
| IDEA-CH-1 — Chandre et al. v2 p.9 (14), compared to p.7 (8) | `−d(1/q)/dψ` | Action-independent perturbation in the general (8) gives half the specialized coefficient. The proposed model explicitly chooses the general formula |
| IDEA-CH-2 — same paper p.11 | `≈ 35ε` | Its stated maximum-cosine-coefficient norm gives `64.5457 ε` for the general-(8) model if the constant is included, or `64.3251 ε` for nonconstant harmonics only. At `.003` these are about 19.36% and 19.30% of ε. The specialized (14) doubles them. Reconcile the coefficient and zero-mode conventions before quoting a control percentage |

VL21 Theorem 2's restriction to `H^(0)` is a **scope distinction**, not a
claimed error in that theorem. No defect in a frozen Lean statement was found.
Declared project deviations: explicit general-(8) model selection; strict
interior ray instead of diagnostic `s=1`; global polynomial extension for the
real-lift ODE; graph-based separation instead of a two-barrier slab; and use of
current checkpoint calibration instead of treating old monolithic costs as fixed.
The prior study's `64.3251 ε` comparison omitted the constant coefficient;
this plan makes that convention explicit and records the slightly larger
constant. No quantitative percentage should silently switch these norms.

## 9. Planning verification and provenance

Source SHA-256: VL21 v2
`02e3daaa037cdcb243ff82bbb9478d95027de61c9c29a10becb097b60bf0148e`;
Chandre v2 `e63bf2eea3ac49a97308a7b6493e24de8bdc688f179fbcb4a70b4a8be7b40153`.
The previous scratch inputs remain under `/tmp/ideas-astra/`; new scratch is
only `/tmp/demo-plans-astra/`. Archive these receipts with the campaign before
relying on their availability. Model formulas and methods above remain the
reconstruction specification.

Scratch commands, with bytecode writing disabled:

```text
python3 -B hp_probe.py mag 512 512 5
python3 -B hp_probe.py mag 1024 1024 3
python3 -B symmetrize_data.py
python3 -B magnetic_symmetry1024.py
python3 -B magnetic_algebra_checks.py
```

The large-grid command ran at `nice -n 5` with `ulimit -v 7800000`.
Both grid runs and both exact-conjugacy assertion checks exited zero. SymPy reported
five `true` checks: `h'(pc)`, `h''(pc)`, all five exact control coefficients,
the frequency's surd formula, and its minimal-polynomial identity. It also
recomputed both control-norm conventions in §8. These are algebra/numerical
checks, not a torus proof or an infinite Diophantine proof.

Selected scratch SHA-256 identifiers:

| Artifact | SHA-256 |
|---|---|
| `hp_probe.py` | `f37a3c593e5425c69f52fbe1a99705da9bbef16f2770de91743932defa79b5dc` |
| `mag--1-512x512.json` | `d9d8d5c9ec7f0ca73b70ef104da4bbe2e0701a9c9611bef527d04cca13b6effc` |
| `mag--1-1024x1024.json` | `10e0d22cf041735dcef5af9c0dc176cdbb3cc3c7e14d36267e7598a5c801f03d` |
| `magnetic_algebra_checks.py` | `980d856ae99be143a8a079e0a5e3e37a1b1be9e006281d767e3e589d0af9f48b` |
| `magnetic_algebra_checks.json` | `01324e66fb7b487859620fa9071a4e295a2372c394af889006a02e5c33dfa8ac` |

The inherited seed `tok-quadratic-512.npz` has SHA-256
`a01f21033b7a008a9b50f78d65064caf8bf5c17fa672ee0c648a956921097f91`.

Documentation checks: `python3 -B /tmp/demo-plans-astra/check_documents.py`
confirmed every local Markdown target and the verbatim hard rules below.
`git diff --cached --check` passed for the two deliverables. Only this plan
and `plan-mercury-32.md` are committed; no source, frozen or manifest file changed.

`PATH=/tmp/demo-plans-astra/bin:$PATH scripts/lint_sources.sh` ran with a
transparent wrapper passing through to `/usr/bin/python3 -B`, except that
the ABI probe was refused: it writes outside the allowed deliverables/scratch
and no Lean probe was justified. This is **partial lint, exit 1**, with output:

```text
check_lean_modules: PASS (1815 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI CHECK SKIPPED: planning brief permits writes only to two deliverables and /tmp/demo-plans-astra; no Lean probe justified
```

No Lean build, kernel-test target or `#print axioms` was run. Axioms of new main
results are **not applicable: this document contains no proved Lean result**.
The eventual torus, graph and non-crossing results each require an independent
axiom/dependency audit with no `sorryAx`. Numerical, support and runtime
uncertainties are explicit above; source candidates and deviations are in §8.

## 10. Hard rules for every issued Lean brief (verbatim)

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

Before handoff: run `scripts/lint_sources.sh` and targeted builds of the changed
modules. Report files, approach, exact checks/output, `#print axioms` of the main
results, uncertainties, errata and deviations. Mirror the frozen/provider layout
in the demonstration repository; moving data out of KAM-dev does not relax
statement integrity or the resource rules.
