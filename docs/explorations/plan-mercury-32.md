# Plan: Mercury's 3:2 spin-rate confinement with exact Kepler forcing

30 October 2026. DEMO-PLANS; branch `demo-plans`, input commit
`377591e0fd09d8abe64d06e2a127cc570f7a80c5`. This is a proposed campaign,
not an approved Lean statement or a certified Mercury result. Companion:
[magnetic barrier](plan-magnetic-barrier.md).

**Recommendation:** launch the exact-model and producer packages now, sharing
the clock-graph infrastructure with the magnetic demonstration. Use two
rotational barriers and state spin-rate confinement, with the proposed window
`[1.492,1.508]` and band `|p−3/2|≤.018`. The numerical evidence is favorable;
the remaining decisive gate is the exact certificate mirror, including square
root/reciprocal witnesses, followed by memory-calibrated kernel shards.
Neither a dissipative capture claim nor libration of the resonant angle is the
goal. Plain isoenergetic v2 is sufficient as a baseline; hybrid restart is an
optional saving, not a prerequisite.

## 1. The exact claim to formalize

### 1.1 Model, parameters and units

Use a rigid triaxial body, planar prescribed Kepler motion, zero obliquity and
no dissipation, with the **exact benchmark literals**

\[
 e=257/1250,\qquad \epsilon=3/20000,\qquad \beta=\sqrt{1-e^2}.
\]

These are the historical Mercury values of
[Celletti–Chierchia 1998, Table 1](https://web.ma.utexas.edu/mp_arc-bin/mpa?yn=98-581),
not a current measurement or a parameter-uncertainty box. Their §2 equation
(2.1) is the untruncated conservative model; the later finite Fourier
approximation (2.3) is not the model here. The source's parameter is
`ε=3(B−A)/(2C)`, so the potential has coefficient `−ε/2`.

Let `q=x/(2π)` be body orientation, `w=E/(2π)` eccentric anomaly, and `p`
the spin angular velocity divided by orbital mean motion. Define on real lifts

\[
\begin{aligned}
 r(w)&=1-e\cos(2\pi w),&
 \ell(w)&=w-\frac{e}{2\pi}\sin(2\pi w),\\
 c_f(w)&=\frac{\cos(2\pi w)-e}{r(w)},&
 s_f(w)&=\frac{\beta\sin(2\pi w)}{r(w)},\\
 C_f&=c_f^2-s_f^2,& S_f&=2c_fs_f,\\
 V(q,w)&=-\frac{\epsilon}{2r(w)^3}
       [\cos(4\pi q)C_f(w)+\sin(4\pi q)S_f(w)].
\end{aligned}
\]

Time `t` is physical time in units of orbital revolutions. Define the field on
`Fin 3 → ℝ`, ordered `(q,p,w)`, by

\[
 F(q,p,w)=\left(p,
 -\frac{2\pi\epsilon}{r(w)^3}
 [\sin(4\pi q)C_f(w)-\cos(4\pi q)S_f(w)],\ \frac1{r(w)}\right).
\]

Everything is explicit: `r≥993/1250=.7944`, and no inverse Kepler function or
chosen branch of the true anomaly occurs. Prove `cf²+sf²=1` and
`dℓ/dw=r`. Every solution has `ℓ(w(t))=ℓ(w₀)+t`. The map `ℓ` is strictly
increasing and onto, so allowing all `w₀` is exactly allowing all initial mean
anomalies. If an inverse is later defined publicly, first prove its unique
existence and characterization; a choose-or-default definition is not allowed.

For source comparison put `s=2πt` and `x(s)=2πq(s/(2π))`. Then
`dx/ds=p` and `dp/ds=−ε r^-3 sin(2x−2f)`; this is (2.1) with orbital mean
motion one. The `.018` band is in units of orbital mean motion: it is **1.2% of
the resonant spin 1.5**, not 1.8% of that spin.

### 1.2 Public confinement theorem, with all quantifiers

For all `q₀,w₀,p₀ : ℝ` with

\[
                  373/250\le p_0\le377/250,
\]

there exists a global `z : ℝ → Fin 3 → ℝ` such that

1. `z 0 = ![q₀,p₀,w₀]` and `∀ t, HasDerivAt z (F (z t)) t`;
2. `∀ t : ℝ, |z(t).p−3/2| ≤ 9/500`;
3. for every order-connected time set `I` containing zero and every local
   solution `y` of the same field with that initial value,
   `∀ t∈I, y t=z t`.

Thus existence and confinement hold for **all real time**, both directions,
and every initial spin angle and orbital phase in the displayed spin window.
The closed window endpoints are allowed because the barrier inequalities
will be strict there. A theorem only about a pre-assumed global trajectory
would omit a requested part of the claim.

The supporting joint barrier theorem exhibits two graphs `P⁻,P⁺` on the
physical real-lift coordinates `(q,w)`, analytic, one-periodic in `q` and
**two-periodic in `w`**, whose graphs are invariant for `F`, and satisfying

\[
\begin{aligned}
 3/2-9/500&\le P^- <373/250,\\
 377/250&<P^+\le3/2+9/500.
\end{aligned}
\]

These inequalities hold at every `(q,w)` and imply `P⁻<P⁺`; no pointwise ordering
hypothesis is added to the public theorem. Sign preservation with respect to
each graph is proved, and their open intervening slab confines the solution.
The same two witnesses must be used in the existence and confinement proofs.

### 1.3 Canonical certificate model and exact chart

Set `q=Q+3w/2`, with momenta `(p,P₂)`. The Hamiltonian to certify is

\[
 H_K(Q,w,p,P_2)=P_2-\tfrac32p+
 r(w)\bigl[p^2/2+V(Q+3w/2,w)\bigr].
\]

For an economical exact expression, write `c=cos(2πw)`, `s=sin(2πw)`,
`C=(c−e)²−(1−e²)s²`, `S=2β(c−e)s`, and
`Φ=2π(2Q+3w)`. Then

\[
 H_K=P_2-\tfrac32p+\tfrac12r p^2
        -\frac{\epsilon}{2r^4}(C\cos\Phi+S\sin\Phi).
\]

Prove these two formulas equal wherever `r≠0`. This combines repeated
reciprocals and replaces `β²` by its exact rational value, while keeping the
one occurrence of `β` as an exact square root. Modes `(0,1)` and `(2,3)` are
integer keys; `HamExpr.const`, `action`, `cosMode`, `sinMode`, `add`, `mul`,
`pow`, `div`, and the **landed** `sqrt` node suffice. There is no new trusted
Hamiltonian primitive in this plan.

The chart calculation must state its domain and energy restriction:

- Start from the physical extended Hamiltonian `H₀=J+p²/2+V(q,w(φ))`, with
  mean anomaly `φ`; this notation is explanatory. The formal calculation can
  use the explicit forward map only.
- Pull back by `φ=ℓ(w)`, `J=U/r(w)`. Its canonical one-form is exactly
  `p dq+J dφ=p dq+U dw`.
- On **energy zero**, multiply the pullback by `r`: `H₁=U+r(p²/2+V)`.
  The identity `X_(rH)=r X_H` is asserted only on `H=0`; off that level it has
  the extra `H X_r` term.
- Set `Q=q−3w/2`, `P₂=U+3p/2`; then
  `p dq+U dw=p dQ+P₂ dw`, giving `H_K` above.
- `w'=1` for the `H_K` time `σ`, and `dt/dσ=r(w)>0`.
  For any physical initial state choose
  `P₂=3p/2−r(p²/2+V)` to put its lift on `H_K=0`. Thus zero extended energy
  imposes no physical restriction on `(q,p,w)`.

The half-integer shear is a global canonical map on **real lifts**, but not a
map of the ordinary period-one two-torus. Use the double orbital cover: reduce
`w` modulo 2 and `q` modulo 1. A period-one canonical graph `p=G(Q,w)` lifts to

\[
                   P(q,w)=G(q-3w/2,w),
\]

which is periodic under `(q,w)↦(q+1,w)` and `(q,w)↦(q,w+2)`.
Do not infer its one-periodicity in `w` from that of the field or from symmetry
of an approximate torus. Nor may one average two invariant graphs to force
periodicity. The all-phase spin bound on real lifts projects to physical
initial conditions regardless of this choice of cover.

As an optional coordinate check, `w=2η`, `J₂=2P₂` gives the period-one
integral-cover Hamiltonian `2H_K(Q,2η,p,J₂/2)`; its frequency and bounds differ.
Do **not** transfer the numerical thresholds to that Hamiltonian without
recomputing them. The baseline certificate is for `H_K`, followed by the
explicit double-cover transport.

### 1.4 Tori, frequencies, novelty and limits

Let `g=(√5−1)/2` and `ν±=±1/(74+g)`. Certify two primary holomorphic tori
`K∞±` for `H_K` on `complexStrip 2 (1/100000)`, both at energy zero,
with exact canonical frequencies `(ν±,1)`. The clock coordinate theorem and
positive first-angle derivative turn them into the two graphs. Their real
orbits are parameterized by `θ+σ(ν±,1)` **in eccentric-anomaly time**.
Physical-time quasiperiodicity is not asserted by this theorem: transferring
that parameterization would require an additional time conjugacy. Invariance
and spin bounds need only the positive time correspondence.

The novelty sought is a kernel-checked all-phase confinement theorem for the
specified conservative Mercury benchmark with **untruncated Kepler forcing**.
Mercury trapping tori already appear in
[Celletti–Falcolini 1992](https://doi.org/10.1007/BF00049460)
([institutional bibliographic record](https://art.torvergata.it/handle/2108/95439)).
The earlier study read the publisher abstract; this pass could verify the
bibliographic record but did not obtain the full article. Do not claim the
first rigorous trapping result, priority for exact forcing, a tighter published
band, tidal capture, permanent libration of `2x−3ℓ`, or stability of the real
Solar System. A completed proof concerns this exact idealized model and its
initial-condition window.

## 2. Statement path and new Lean

### 2.1 Reuse, with exact boundaries

Use [the v2 certifier](../../KAM/CertificateSharp/V2/Engine.lean) and
[routeV2All](../../KAM/CertificateSharp/V2/RouteAll.lean) over the **isoenergetic**
branch of [Sharp2](../../KAM/Iso/Sharp2/G1.lean). The dummy-action degeneracy
rules out substituting the fixed-frequency ordinary twist theorem. A passing
certificate plus `FreqEncloses` and an infinite `IsDiophantine` proof produces
`CertifiedTorus`, with energy, strip, domain, derivative and displacement data.
It does not itself produce a physical-time confinement theorem.

Existing generic ingredients:

- `KAM.Certificate.clock_frequency` in [Clock](../../KAM/Certificate/Clock.lean);
- `soGraph_exactTorus_of_certified`, `checkSoGraph_sound`, and Cauchy derivative
  transfer in [Graph/Cert](../../KAM/SpinOrbit/Graph/Cert.lean);
- `KAM.ODE.gen_barrier`, `gen_uniqueness`, `gen_maximal`, compact continuation;
- the infinite rotated-frequency lemmas
  `lunarNuMinusN_rot_isDiophantine` and `lunarNuPlusN_rot_isDiophantine` in
  [QuadraticDiophantineN](../../KAM/Certificate/QuadraticDiophantineN.lean), at
  `N=74`, giving `γ=1/76`, followed by positive scalar scaling;
- [Expr/Basic](../../KAM/Certificate/Expr/Basic.lean), `BallSqrt`,
  `DiffNodeSqrt`, `Model/SqrtWitness`, and their soundness already implement the
  exact square root. Its operand is the positive rational `1−e²`.

The SO `soRotBarrier_of_certified` and `so_confinement` wrappers contain the
lunar model and its integer shear. They are proof templates, not Mercury
specializations. Do not edit SO-owned modules. Share the new generic clock-graph
helpers of the magnetic plan, and add explicit Mercury chart/field proofs.

The [C6](../campaign/handoffs/SHARP2-C6.md),
[C6L8](../campaign/handoffs/SHARP2-C6L8.md),
[C6L1](../campaign/handoffs/SHARP2-C6L1.md),
[C6B](../campaign/handoffs/SHARP2-C6B.md), and
[C6ALL](../campaign/handoffs/SHARP2-C6ALL.md) lunar-input numbers are not Mercury
certificates. The [C8 hybrid](../campaign/design/APOST-SHARP-V2-HYBRID.md) is
being implemented elsewhere; its proposed modules do not exist at this pin.

### 2.2 Modules and ownership

Use the separate `KAM-demos` repository described in the magnetic plan. Proposed
names, not current exports:

| Module | New Lean lines | Required result |
|---|---:|---|
| `KAMDemos.Mercury.Model` | 250–400 | Exact constants, `r,ℓ,cf,sf,V,F`; periodicity and physical units |
| `KAMDemos.Mercury.KeplerClock` | 200–350 | `r>0`, `ℓ'=r`, bijectivity, physical orbital phase |
| `KAMDemos.Mercury.HamExpr` | 250–400 | Factored AST, algebraic identity, denominator/root domain and clock derivative |
| `KAMDemos.Mercury.Chart` | 300–500 | Canonical one-form identities, exact zero-energy lift and field relation |
| `KAMDemos.Mercury.TimeChange` | 250–400 | All-real-time correspondence using positive bounded `r` |
| `KAMDemos.Mercury.Cover` | 150–250 | Real-lift shear, double periodicity and projection of bounds |
| `KAMDemos.Mercury.Frequency` | 80–150 | `N=74`, both signs, strict ray and algebraic enclosure |
| `KAMDemos.Mercury.Graph` | 200–350 | Two canonical graphs → two physical barriers, common bounds |
| `KAMDemos.Mercury.Global` | 200–350 | Finite-time growth, global ODE existence and local uniqueness |
| `MercuryProof.Lower`, `.Upper`, `.Assembly` | 100–180 each | Checked certificate facts and unconditional confinement |

Total bespoke Mercury code is **2.2–3.7k Lean lines**, excluding generated data
and the shared 0.8–1.3k clock-graph layer. These estimates are higher than the
first scout because cover/time transport, domain control and global existence
are now explicit packages. Keep modules focused, below 800 lines where possible,
and absolutely below 1500. Kernel-scale data and the final provider/anchor
closure stay opt-in; KAM-dev's normal root cannot import them.

A short proof of the time correspondence is preferable to a general flow API:
on a canonical orbit `w(σ)=w₀+σ`, put
`t(σ)=ℓ(w₀+σ)−ℓ(w₀)`. Its derivative lies in `[1−e,1+e]`, so it is a
bijection `ℝ→ℝ` with differentiable inverse. Prove the chain rule in both
directions and apply uniqueness. For general physical solutions, `σ=w−w₀`
provides the reverse clock. This establishes all-time rather than merely
local time transport.

### 2.3 What needs owner approval

Present exact elaborated Lean commands, after independent source/binder audit,
for the meaning-carrying definitions and the joint barrier/confinement targets.
Approval covers: historical rational parameters; exact forcing rather than the
seven-mode approximation; time/angle/spin units; universal real-lift ODE and
all initial phases; the double cover; `N=74` frequencies and energy zero;
`[373/250,377/250]`, `9/500`, and the torus strip width. Review these literals
against the numerical and mirror feasibility evidence, then freeze before
assigning application proofs. The full kernel bounds remain proof obligations.
If either torus fails, changing `N`,
the band, or the window requires reapproval, not an extra hypothesis.

No statement is frozen here. Do not add `HasBarriers`, a passing certificate,
KAM smallness, or global existence to the public theorem's assumptions. A
conditional generic helper is allowed only with a different name, and the
concrete proof must discharge every such input. Providers and draft anchors
remain quarantined in the demonstration repository under the same rules.

## 3. Data pipeline and route decision

### 3.1 Multiprecision producer

Follow LG00-PREP (`docs/explorations/lg00-prep.md` on the unpublished branch `lg00-prep`)
for mixed-precision iteration, exact reversibility, witness generation and the
receipt ledger. Do not inherit its Taylor model, thresholds, or incomplete
`L=36` mirror status.

Start each sign at `ε=0`: `p₀=3/2+ν±`,
`u_Q=−p₀ e sin(2πw)/(2π)`, `u_w=0`, and
`P₂=3p₀/2−r p₀²/2`. Continue ε in fourteen increments, using the bordered
isoenergetic Newton equation. This clock-only angle modulation is essential;
starting with constant `Q` correction changes the zero-perturbation defect.

Use 80 working decimal digits plus guards; the scratch pilot uses 320-bit
fixed point and 400-bit transcendental evaluation. The residual/FFT is
multiprecision; the correction preconditioner may be double precision.
Project odd angle corrections/even actions exactly. Remove initial numerical
noise and truncate tiny *correction* noise before adding it to the high-precision
coefficients. Track error in energy and all four invariance components.

Use **256×128 then 512×256**, both radix two, rather than feeding the existing
`hpfft.py` an unsupported 96- or 192-point dimension. The earlier floating FFT
used 256×96; that does not establish mixed-radix support in `hpfft.py`.
If needed, validate on 1024×512 with streamed derivative arrays. Budget
0.5–1 day for adapting the producer, then minutes to a few hours for both
solves/scans, and 0.5–3 GB RSS at the initial production resolutions. Larger-grid
memory is measured before use; stop at 7.5 GB.

The final finite embedding may use SO's `angleDeg=-1` convention, storing a
dyadic numerator approximating `2πu`; actions use degree zero. Recompute the
residual of **that denoted embedding**, including π-enclosure effects. The
pilot's period-one coefficient arrays are not automatically certificate data.
A high-precision torus can contain aliasing/noise far below real-space accuracy
but significant after strip weighting. Retained modes must be selected by paid
weighted tail/error estimates, not the requested number of decimal digits.

### 3.2 Producer gap: exact expression support

At the pinned commit, Lean has `sqrt`, but `scripts/spin_orbit/sofx_model.py`
still has a three-field `Witnesses` constructor and no square-root branch.
The `adv_jet.py` mirror covers the lunar constructors and also needs coverage
for this client's expression. The [LOCK-SQRT receipt](../tracks/SO/audits/LOCK-SQRT-handoff.md)
records the same gap. This is **new untrusted tooling**, not a new Lean axiom
or a reason to replace β by a decimal.

Assign a separate mirror adapter, preferably outside SO-owned files, implementing
exact rational AST constants; required sine/division/sqrt compiler cases;
ball arithmetic with outward rounding; and slot-keyed `sqrtWit` as the fourth
witness field. Match the actual `DiffNodeSqrt`, ball and composition code.
Test a positive constant root, wrong-sign root rejection, reciprocal residual,
a nontrivial Mercury jet and one small composition with the kernel. The sqrt
witness itself is a one-term positive dyadic approximation `B`, with the
residual `|B²−(1−e²)|` paid by `sqrtWitnessRadius`.

The simplified `r^-4` expression has one reciprocal chain; higher derivatives
are generated from it. Build reciprocal/character witnesses from the rounded
embedding, not from the untruncated numerical solution. On the candidate
`u_w=0` these orbital factors are one-dimensional. Soundness must still use
the actual expression/embedding, not assume the exact torus's clock phase is
zero before the clock theorem.

The real denominator margin is `.7944`. For complex-domain Hamiltonian bounds,
prove `|r|≥1−e cosh(2πρ_H)>0`, with `ρ_H` covering **the entire certificate
domain**, including the embedding's clock correction and the `μ` ball.
`ρ_H=.02` gives about `.7927745`; it is a candidate domain bound, not a
certificate result. The nearest clock-plane singularity is at imaginary
height about `.36036348`, so the proposed strip `.01` is not close to a Kepler
collision singularity.

An 80-digit scalar check used the exact Fourier identity

\[
 r(w)^{-1}=\frac1\beta\sum_{k\in\mathbb Z}a^{|k|}e^{2\pi ikw},
 \qquad a=\frac{1-\beta}{e}=0.10390996\ldots.
\]

At strip `.01`, truncating at `|k|≤28` has geometric weighted tail
`4.33·10^-28` or less in this numerical evaluation; at 32 it is about
`6.48·10^-32`. This is a useful witness-size forecast (57 or 65 full terms),
not a kernel enclosure of `r^-4` or its derivatives. Those products and powers
amplify the error and are checked separately. Preserve the exact algebraic
root and certify the reciprocal residual; no Hansen tail needs to be proved.

### 3.3 Certificate fields, route and error budget

Emit both full `TorusCertificate` objects, with separate data hashes: exact AST,
compiled jet, finite embedding, all character/inverse/root witnesses, Gram and
bordered torsion inverse witnesses, domain balls, π/weight enclosures,
product advice, refined bounds, graph data, and route witnesses. Supports of
clock factors, character witnesses, intermediate models and inverse witnesses
are distinct counts. All seven base checks must pass, including energy zero.

Use `s₀=500001/500000`, `ω*±=(ν±,1)/s₀`, `σω=2`, `νRay=10^-6`,
`γ=(1/76)/s₀`, `τ=1`. Existing `N=74` rotated-frequency lemmas give the
infinite inequality, and scaling gives the reference-vector bound. The clock
coordinate is rational with zero box radius. Enclose the remaining algebraic
coordinate with exact rational bounds. Since `‖ω*±‖∞=1/s₀`, both strict ray
margins have room; the clock theorem later forces `s∞=s₀`. There is no need
to transfer `γ` across the half-integer physical shear for set confinement.

Initial strips/budget: `ρ=1/100`, `ρ∞=1/100000`, `μ=1/500`. Start certificate
arithmetic at 192 bits and escalate to 256 only for an observed rounding limit.
Aim for `err≤10^-25`, separately bounding energy by that number. A useful
ledger allocates `2·10^-26` each to the finite candidate residual, composition
witness radii, and product/rounding loss, leaving `4·10^-26` contingency. The
producer's MP precision is separate from the emitted arithmetic precision.

| Route | Decision rule |
|---|---|
| Frozen A or frozen B | Check as a low-cost baseline; accept only its actual thresholds |
| Refined A | Available baseline with certified frame and Hamiltonian data |
| Refined A with L8′ | Default candidate, three prefix stages and classical constants |
| ℓ¹ entry | Try only with measured `L1Claim`, paid sup-to-ℓ¹ strip loss and certified `Γ∞` |
| Refined B | Compare at the same exact bounds; `.01≤1` meets its strip guard; no assumption it beats A |
| Hybrid | Optional after C8 lands/audits and measured restart/graph/cost gates pass |

Use `routeV2All` with the witness of the winning route. For L8′ the witness is
`Sum.inr (Sum.inl (Sum.inl (Sum.inr w)))`, `w : RefinedWitR`.
`routeV2All` does no route search itself. Record the chosen route, prefix,
classical/site constants, caps and binding inequality in the emitted ledger.

The previous design used sampled bounds and found sufficient tolerances
`3.80·10^-23` (lower), `3.12·10^-23` (upper), classical A′. At `10^-25` these
are factors **380** and **312**, about 2.58 and 2.49 decimal orders. They are
**expected thresholds, not established certified values**. A full mirror must
replace the sampled Hamiltonian/frame bounds, then evaluate the exact rational
core. Require at least one order of actual residual margin and every side
condition, not merely a favorable scalar threshold.

### 3.4 Explicit graph and observable margins

Suggested finite-candidate graph bounds, chosen with room relative to the
sampled extrema, are

| Torus | `pLo` | `pHi` | `mono` | `disp` ceiling |
|---|---:|---:|---:|---:|
| lower | `7411/5000 = 1.4822` | `1491/1000 = 1.491` | `7/10` | `10^-7` |
| upper | `1509/1000 = 1.509` | `7589/5000 = 1.5178` | `7/10` | `10^-7` |

Cauchy transfer loses at most `.01` in the first-angle derivative and `10^-7`
in action. Thus the exact slopes are at least `.69`; lower graph upper bound
is below `1.492`; upper graph lower bound is above `1.508`; both outer bounds
lie strictly inside `[1.482,1.518]`. This proves the public literals with
visible margins and covers all phases. Certify these on the finite polynomial
with `checkSoGraph`. The fresh real-torus coefficient triangle bounds are
promising, but that checker uses the certificate's **strip weight** even in
its real lower-bound residual. At `ρ=.01` the triangle bounds are too loose:
lower action range `[1.48193,1.49127]`, upper `[1.50871,1.51809]`, and angle
slopes about `.670`. Therefore budget paid SOS residuals for the baseline.
An optional small helper could check exact polynomial real bounds at weight
one and transfer them with the same displacement theorem, but its soundness
would be new Lean to audit (roughly 150–250 lines); do not assume it exists.
The positive clock map
and shear do not change `p`, so they do not enlarge this observable band.

For the hybrid, use **total** displacement `max(d∞+D₁,dω+D₁ω)` as required
by its interface. The first correction cannot be discarded in graph or ray
bounds. Even when the scalar restart test passes, a coarse correction that
exhausts the `.01` derivative budget is rejected.

### 3.5 Hybrid experiment, separately budgeted

Compare finite coarse candidates, for example coefficient cuts giving residuals
between `10^-9` and `10^-14`. Produce a finite additive `ΔK` and `Δs`; certify
linearized invariance error at `s₁ω*`, linearized energy and both Taylor
remainders. Transfer Gram, bordered torsion, derivative and domain caps, reduce
the ray budget, and rerun the isoenergetic engine at `ρ₁=ρ,3ρ/4,ρ/2`.
Certify the real-torus and strip step norms separately. Keep the original
composition accurate to the **restart** target, around `10^-25`, even though
`K` is coarse. Products must preserve cancellation in the linearized residual.

No Mercury hybrid threshold is established by this plan. Conditional on
`e₁≤A e²` and all transferred caps passing, a one-order margin at the weaker
plain threshold `3.12·10^-23` would allow
`e≤sqrt(3.12·10^-24/A)`; for `A=1,100,10000` this is approximately
`1.8·10^-12,1.8·10^-13,1.8·10^-14`. These are sensitivity examples, not
measured constants. R1's `10^-5.25` restart tolerance is not transferable.
Use the hybrid only if a complete census predicts at least a twofold total
saving; this small client may be cheaper to certify directly than to adapt C8.

## 4. Fresh experiments and first remaining decision

Inherited double-precision evidence from [the earlier study](next-demonstrations.md):

| Quantity | Lower | Upper |
|---|---:|---:|
| Real residual on 256×96 | `1.292·10^-12` | `1.356·10^-12` |
| Spin extrema | `[1.482652152,1.490056921]` | `[1.509985329,1.517301355]` |
| Minimum angle derivative | `.7494906` | `.7495003` |
| Predicted full union embedding keys for `10^-25` | 1.5–2.5k | 1.5–2.5k |

These numbers do not include outward rounding or infinite composition tails.
The old support estimate extrapolated low-accuracy residual cuts; it is not
an attained certificate size.

Fresh mixed-precision runs used the inherited starts, 320-bit fixed-point
residuals/FFTs, 400-bit transcendental evaluation and the double preconditioner.
On 256×128 the lower torus reached weighted grid residual `1.67·10^-22` after
five corrections; on 512×256 it reached `1.25·10^-34` after ten. The upper
512×256 run reached `5.84·10^-30` after six. These are diagnostics of the
untruncated numerical arrays, not bounds on their infinite compositions.
The lower/upper large-grid iteration loops took 272/259 seconds, excluding
initialization; peak RSS was 608232/605972 KiB (about 0.58 GiB each).

An additional structural check found that projecting coefficients to purely
real or imaginary parts had not enforced exact opposite-key conjugacy. The
real-grid evaluator discarded the resulting imaginary part, so its residual
alone could not detect this defect. Before the following finite-candidate
tests, opposite keys were paired exactly (even actions, odd angles), and the
conjugacy identities were asserted. Production must impose this at each step.

Retain the union of keys where at least one component has
`|c_k| exp(2π·.01·|k|₁)>10^-L`, together with the constant key. Re-evaluation
of the resulting **exactly real, finite dyadic candidates** on 512×256 gave:

| Cut | Lower full union keys | Lower weighted grid residual | Upper full union keys | Upper weighted grid residual |
|---|---:|---:|---:|---:|
| `L=24` | 971 | `2.32·10^-21` | 987 | `1.87·10^-21` |
| `L=28` | 1365 | `3.32·10^-25` | 1363 | `3.83·10^-25` |
| `L=30` | **1579** | **`4.73·10^-27`** | **1583** | **`4.38·10^-27`** |

For the final row the real-grid residuals were `3.46·10^-28` and
`3.00·10^-28`; mean-energy defects were `−8.59·10^-56` and `2.09·10^-50`.
The three-cut re-evaluation loops took 81/80 seconds, again excluding setup.
Thus the proposed finite-residual allocation `2·10^-26` has about a factor
four numerical margin at fewer than 1.6k union keys per sign. This materially
supports the plain route's size forecast; it is **not a passing certificate**.
Weights and reported norms are floating summaries of MP residual coefficients;
no outward rounding or infinite alias/composition bound was computed here.

A lower-grid comparison after exact conjugacy found common-coefficient
weighted differences about `1.35·10^-25` in the angle, `5.58·10^-28` in spin,
and `6.33·10^-25` in the dummy action. The coarser solve had only five
corrections, so this is not convergence verification at the target tolerance.
Validate the emitted finite object on a larger grid and with the actual
certificate model. In particular, these numbers do not settle root/reciprocal
model radii, frame/torsion caps, graph SOS costs or the final KAM inequality.

Independent symbolic checks also verified all four partial derivatives of the
factored `H_K`, its `Q` and `w` periods, its half-turn symmetry in `Q`, and
`(∂p H_K+3/2)/r=p`. These are SymPy checks, not Lean proofs. Half-turn symmetry
of the Hamiltonian does not by itself prove symmetry of a chosen exact KAM
graph. The scalar reciprocal experiment of §3.2 used 80 decimal digits.

The first *remaining* cheap confirmation/kill experiment is the lower finite
candidate with the actual exact-forcing checker mirror. Spend half a day after
the mirror adapter: check Hamiltonian balls, root/reciprocal witnesses,
invariance, energy and graph range/slope before generating expensive frame
advice. Compare two dealiased resolutions at the retained modes. Require
`err≤10^-25`, the §3.4 budgets and initially at most 2.5k union keys; 5k is a
stop/reforecast threshold, not an automatic rejection of the mathematical
claim. Then repeat independently for the upper sign. If increasing precision
does not reduce model radii, change the expression/witness layout rather than
merely increasing digits. Both signs are necessary for confinement.

## 5. Kernel plan and machine limits

Keep full certificates in a separate repository or explicit opt-in targets,
never in KAM-dev's default build. Use the existing
[checked segment](../../KAM/CertificateSharp/Kernel/SegBridges.lean),
[product split](../../KAM/CertificateSharp/Kernel/ProductSplit.lean), and
[stage](../../KAM/CertificateSharp/Kernel/Stage.lean) interfaces. Put each sign's
literal data, character/root/reciprocal witnesses, product shards, decoded
models, checkpoints, Gram/torsion facts, route core and assembly in separate
small modules. A final theorem must reuse proved equalities, not force the
entire certificate again by reduction.

The current [SO-CSPLIT gate](../tracks/SO/studies/SO-CSPLIT-GATE.md) measured
about `.13 ms` per census call, 3–4 seconds per product shard, and `.8 ms` per
decoded target slot at 96 bits. Maximum observed RSS was 7.05 GB, despite a
4.05 GB warm cgroup peak. Its projected complete lunar torus cost is
1.6–2.5 CPU-hours. Mercury has reciprocal/root operations and more precise
arithmetic; these rates are a calibration starting point, not its runtime.
The earlier first-jet count of 38 product/witness operations omitted full jets
and cannot be used as the full work count.

Start with about 50k census calls per theorem and 8–16 packed rows per factor
block at 192 bits; measure both time and memory. Separate shards from decodes,
and even a single reciprocal residual from its final radius comparison if
needed. A constant sqrt is a cheap one-term witness; a large character witness
is likely to be more expensive. Count one-dimensional orbital supports
separately so their cost is not inflated to that of a dense two-dimensional
model. Reuse shared composition in energy/invariance/refined claims.

Targets and gates:

- Aim for ≤7 GB RSS; stop the owned process at 7.5 GB; every successful Lean
  process must stay below 8 GB, under the site's 10 GB kill guard. Record RSS
  and cgroup peak, including imported data. A smaller warm-cache charge is
  insufficient evidence of a cold-memory budget.
- One targeted `nice -n 5 lake build <Module>` at a time through the compile
  gate. Pause producers for kernel runs and remain below the 32 GB user cap.
  Never build `kernel-tests/`, use heartbeat/recursion overrides, or trigger a
  fresh full dependency/library build in a worktree.
- Before production, check one root witness, reciprocal residual, worst
  character product, packed decode, composition segment, torsion entry and
  graph comparison. Include wrong-sign root and mutated coefficient/advice
  rejections. Establish actual kernel truth, not a shape probe with stubs.
- Use classical constants first. C6/C6L8 frequency-specific R1 bites include
  individual computations above 10 GB. Smaller files alone do not solve an
  oversized bite; rounded/blocked arithmetic is a separate audited project.

Reserve **8–40 CPU-hours per torus**, **16–80 for both**, including data
elaboration and geometry checks. Retain this conservative range until the
actual ledger is calibrated; clock-only factors and the new segmented checker
may improve it substantially. Serial wall time at a 1.5–2 multiplier is about
**1–7 calendar days**, plus queue delay. Reforecast at the first benchmark;
stop/review above 80 projected CPU-hours for the pair. Initial emitted-source
reservation is 10–150 MB per torus, to be replaced by a measured census before
data generation is committed. Source parsing and imports count in the budget.

Use the six-term census model from the magnetic plan: calls, shards, decoded
slots, theorem count, literal KB and literal module count, each calibrated at
actual precision. Hybrid savings, if any, must include its extra step models
and retained fine character witnesses. A larger machine principally permits
the two tori or more shards in parallel and larger per-job batches. It does
not fix normalization, missing exact sqrt support, or a failed analytic bound;
retain a replay recipe that fits this machine.

## 6. Packages, milestones and audits

Owners are assignable roles; no application implementation or delegation is
started by this planning document. Every issued brief repeats §10, pins the
input commit and approved declarations, and states allowed files and a resource
budget. SO/checker/C8-owned work is coordinated, not edited by Mercury workers.

| Order / owner | Inputs → outputs; expected size | Acceptance and stop condition |
|---|---|---|
| **R0 — mathematical/source lead**, 1–2 days | CC98, exact formulas and R1–R2 cheap feasibility evidence → audited model/units/claim commands and owner approval/freeze; 250–400 Lean lines | Independent parameter, ε/2, 2π, energy and double-cover audit; stop on a model mismatch |
| **R1 — numerical producer owner**, 1–2 days | Both existing starts and exact `H_K` → multiprecision finite candidates, residual/edge/support logs; 600–1100 Python lines | Two resolutions and both signs; stop/reforecast on >5k keys or >7.5 GB |
| **R2 — mirror/emitter owner**, 2–4 days | Landed sqrt/division compiler and SO mirror → client adapter, exact witness/jet/ball emission; 500–1000 Python lines | Small bit-exact kernel probes including root-sign rejection; no rational substitute for β; stop on a missing branch or witness-arity mismatch |
| **R3 — chart/time owner**, 3–5 days, alongside R1–R2 | R0 and generic ODE lemmas → `KeplerClock`, `Chart`, `TimeChange`, `Cover`; 0.9–1.5k Lean lines | Canonical identity, energy-zero field relation, complete time bijection and correct periods; stop if only a local or period-one shear claim is proved |
| **R4 — frequency/graph owner**, 2–4 days | `N=74` lemmas and shared clock-graph API → both ray proofs and physical graph transfer; 280–500 bespoke Lean lines | Same torus witnesses, all phases, exact p bounds, total displacement; stop on sampled positivity only |
| **R5 — data/kernel owner**, 1–2 days calibration, then §5 | R1–R2 data and route comparison → two complete kernel certificates; 300–540 Lean glue lines plus data | All base/refined/core/graph checks, memory receipts, mutations; stop on one-sign-only success, >7.5 GB or >80 CPU-h forecast |
| **R6 — ODE/assembly owner**, 1–3 days | R3–R5 and the generic graph theorem → global unique confinement; 300–550 Lean lines | Local-solution agreement, closed initial window, both time directions and exact observable units |
| **R7 — independent auditors/integrator**, 2–4 days | Frozen commands and data manifests → re-audited statements, provider and sealed anchors | Separate statement/model, checker/mirror, data-consumption, and final axiom audits; stop on any unresolved premise, cover, or data-hash mismatch |

Aim for **2–4 weeks** with shared graph infrastructure and independent owners;
3–5 weeks if those helpers must be built first. This includes a realistic
mirror adapter and geometry audit, which were missing from the scout's shortest
estimate. R0 drafts immediately and returns for approval after the cheap
R1–R2 feasibility gate. Freeze the exact root commands and meaning-carrying
definitions before assigning application proofs; review their source-level
dependency plan. Thereafter numerical and chart proof work can proceed
independently. Kernel certification is still an obligation, and failure requires
a stop or a newly approved frozen version. R7 re-audits the existing freeze and
seals only after both certificates and the physical confinement proof pass.
No release or GitHub action is part of this brief.

Specific audit challenges:

1. Reconstruct the physical ODE from CC98 (2.1) independently; check the exact
   parameter and unit conventions, the conservative assumptions and every
   denominator/root carrier.
2. Test the energy-zero restriction and double-cover map adversarially. Check
   that the two graph bounds apply to every physical initial phase and that
   time maps onto all `ℝ` in both directions.
3. Compare the adapter's literal jet and small compositions with Lean. Check
   the root sign, reciprocal domain, repeated key merging and all remainder
   allocations; Python success is not the proof.
4. Trace the final provider into both particular kernel certificate theorems,
   their expressions, boxes and graph tests. Reject unused certificates,
   conclusion-shaped assumptions, draft imports and a theorem about only a
   truncated forcing.
5. Run `#print axioms` for the two torus results, both graph results and final
   confinement; require only the standard Lean/Mathlib axioms and no `sorryAx`.
   Replay exact targets from the pinned checkout with the cache/build policy.

## 7. Risks and mitigations

| Risk | Mitigation / decisive test |
|---|---|
| A factor of 2 or 2π changes the physical spin band | Source equation and period-one/radian chain-rule proof before data emission |
| Half-integer shear treated as a torus automorphism | Real lifts plus double orbital cover; certify its periods explicitly |
| Time change used off zero energy or only locally | Explicit zero-energy lift for every initial state and global monotone clock bounds |
| Decimal sqrt changes the model | Exact `HamExpr.sqrt`, positive operand, checked one-term witness and wrong-sign rejection |
| Reciprocal/Hamiltonian balls inflate constants | Factored `r^-4` AST, clock-only witnesses, full-domain denominator margin and measured refined bounds |
| MP residual hides aliasing/weighted high-mode noise | Two dealiased grids; re-evaluate emitted finite candidate; interval model radii are the final criterion |
| Real coefficient bounds do not pass a strip-weighted graph checker | Budget paid SOS residuals; separately audit any new weight-one graph adapter; do not infer upper bounds from lower-torus symmetry |
| Hybrid saves frames but not expensive fine compositions | Benchmark complete plain and hybrid ledgers at the same observable displacement budget |
| Capture/libration/real-Mercury claims creep into the statement | Freeze the exact conservative spin-rate theorem and its numerical window; separate later questions |

## 8. Errata, uncertainties and deviations

No new defect in CC98's exact equation (2.1) or Table 1 was established here.
No source erratum is inferred from its explicit choice to truncate (2.2) later.
The magnetic source candidates IDEA-VL-1/2 and IDEA-CH-1/2 are unrelated to this
model and are recorded with locations and quotations in the companion plan.
No frozen Lean declaration was changed or found defective.

Two project-documentation issues affect implementation:

| Location and short quotation | Why it cannot be used literally |
|---|---|
| `scripts/apps_scout/models.py`, `spin_kepler` docstring: “a HamExpr of version 1” | The exact coefficient β needs the now-landed sqrt semantics; the function itself uses floating `math.sqrt`, and the production mirror lacks that branch. Its output is a numerical diagnostic, not an exact certificate AST |
| `next-demonstrations.md`, production-grid suggestion: “512×192” | NumPy supports it, but the selected `hpfft.py` uses radix-two bit reversal. Use 512×256 or implement and validate another FFT; no claim that the mathematical model is wrong |

Declared deviations from the truncated SO precedent: exact Kepler forcing;
eccentric-anomaly canonical time and zero-energy time change; a half-integer
shear handled on a double cover; historical Mercury literals; two frequencies
at `N=74`; and a new square-root/division mirror adapter. The strict interior
ray is also a change from the diagnostic `s=1`. These are visible model or
implementation choices, not premises smuggled into a source theorem.
Priority and quantitative comparison with the full CF92 article remain open.
The actual certificate threshold, full witness supports and kernel runtime
remain unknown until the mirror and calibration gates; no numerical probe here
establishes an all-time Mercury theorem.

## 9. Verification receipt and durable evidence

CC98 source TeX SHA-256:
`e24cc302023106c0fb38a71dff335640670451873b5920e5a25c1e59cb188660`.
Relevant lines in that artifact: 175–207 (physical assumptions and exact
ODE), 218–264 (subsequent approximation), 1158–1166 (Table 1). Archive it and
the new scratch receipts with the campaign. The symbolic expressions above
are the reconstruction specification; `/tmp` paths are not durable evidence.

Scratch directory: `/tmp/demo-plans-astra/`. The following commands ran with
bytecode writing disabled. Timings in §4 are observed wall time
for the iteration/re-evaluation loops, not end-to-end kernel benchmarks.

```text
python3 -B hp_probe.py mercury 256 128 5 -1
python3 -B hp_probe.py mercury 512 256 10 -1
python3 -B hp_probe.py mercury 512 256 6 1
python3 -B symmetrize_data.py
python3 -B tail_real_probe.py mercury 512 256 0 -1
python3 -B tail_real_probe.py mercury 512 256 0 1
python3 -B support_compare_real.py
python3 -B algebra_checks.py
```

The first three exited zero; the exact-conjugacy assertions and both finite
tail scans passed. `algebra_checks.py` reported eight `true` identities; the
scalar bounds are recorded in §3.2. No one of these checks is an interval or
Lean proof. Selected SHA-256 identifiers (all paths relative to scratch):

| Artifact | SHA-256 |
|---|---|
| `hp_probe.py` | `f37a3c593e5425c69f52fbe1a99705da9bbef16f2770de91743932defa79b5dc` |
| `symmetrize_data.py` | `77ad5b89e936dd026ae48161c41879e8369511bb974cb4f05cfe556ba2d76fe2` |
| `tail_real_probe.py` | `ad6e79641849c27a44c5035191ed5dc7804bea886bc39a38c3123ea02fb6002e` |
| `mercury--1-512x256-real-tails.json` | `2e6969e9eb82c8817de617848224c6221ba848b930ec60f6f62097f11d06bbe7` |
| `mercury-1-512x256-real-tails.json` | `f855040045c98e940061d9f9700e1690f786001ccaf2b28f63e840389dd71f2a` |
| `support_compare_real.json` | `825eda42ed58d1f54c2b0dcfe711d5f60ec0298fbe0414a967c7c3eef98499bc` |
| `algebra_checks.py` | `3592e5e641aea150b0c7297b5f04ba1a3aea721580f3f8565c11bd31e7de57be` |
| `algebra_checks.json` | `f42c469fd383e58f37740f1f45ac3926c3220096e2fc8883384abbaec8587a1a` |

Inherited seed hashes (`/tmp/ideas-astra/`): `mercury--1.npz`,
`6eca2e02090e7d795ed8a596fae12f1cd2402c751704a9c4801b0c47dab4d27d`;
`mercury-1.npz`,
`115f266764f178897411df13009f9a23ca05a00938fad6dc35783f5bbe4235bc`.

Documentation checks: `python3 -B /tmp/demo-plans-astra/check_documents.py`
confirmed all local Markdown targets exist and all eleven hard rules below
match `AGENTS.md` verbatim. `git diff --cached --check` passed for the two
deliverables. Only this file and `plan-magnetic-barrier.md` are committed.

Source lint was invoked as
`PATH=/tmp/demo-plans-astra/bin:$PATH scripts/lint_sources.sh`. Its transparent
Python wrapper passes through to `/usr/bin/python3 -B` except that it refuses
the ABI probe with exit 1: that probe writes outside the two deliverables and
scratch, and no Lean probe was justified by this planning task. The receipt is
**partial lint, exit 1**, not a full pass:

```text
check_lean_modules: PASS (1815 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI CHECK SKIPPED: planning brief permits writes only to two deliverables and /tmp/demo-plans-astra; no Lean probe justified
```

No Lean file changed; no Lean build, kernel-test target or `#print axioms`
was run. New result axioms are **not applicable: these are plans, not proofs**.
The future axiom checks are specified in §6. Uncertainties and source deviations
are recorded in §7–8; all-time confinement remains a proposed result.

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

Before handoff: run `scripts/lint_sources.sh` and targeted builds. List files,
approach, commands/output, axioms of the main results, uncertainties and errata.
Use the same frozen/provider layout in the separate demonstration repository;
opt-in data does not relax proof or module rules.
