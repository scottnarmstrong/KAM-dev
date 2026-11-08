# The Moon stays locked in synchronous rotation forever (track SO, part 3)

**Status:** proved and sealed (statements frozen 2026-10-31, D49; sealed 2026-11-05, D63; seal audit LOCK-SEAL-1
PASS WITH NOTES) · frozen ids `spinorbit.lock.lunarSyncOrbit_spec.v1`, `spinorbit.lock.lunarSyncOrbit_unique.v1`,
`spinorbit.lock.lunarSyncOrbit_bound.v1`, `spinorbit.lock.lunar_sync_lock.v1`, with the definitions `IsSyncOrbit`,
`lunarSyncOrbit`, `libAction`, `lunarOmega` and the model of part 2 · axioms: standard only (`propext`,
`Classical.choice`, `Quot.sound`)

## In brief

Part 2 bounds the Moon's spin rate; this part bounds its orientation. In the same spin–orbit model (a rigid,
slightly elongated Moon on a fixed elliptic orbit), there is exactly one odd periodic motion in which the Moon turns
once per orbit while its long axis rocks slightly about the mean direction to the Earth (a forced libration of at
most about 22 arcseconds). The main theorem shows that every motion starting close enough to this periodic orbit
(within an explicit ellipse that allows initial librations up to about 66°) stays close to it for all time: the long
axis never swings more than 75.6° from the periodic orbit, never makes a quarter turn away from the mean Earth
direction, and the spin rate stays within 2.6 % of the periodic orbit's. The proof uses one invariant torus around
the periodic orbit, computed numerically and verified by Lean's kernel.

## Exactly what is proved

Lean: the four theorems in [`KAM/Frozen/SpinOrbit/Theorems/`](../../KAM/Frozen/SpinOrbit/Theorems/), the definitions in
[`KAM/Frozen/SpinOrbit/Defs/`](../../KAM/Frozen/SpinOrbit/Defs/).

### Model and notation

The model is that of [part 2](SO-2.md): state (q, p, φ) ∈ ℝ³, angles in turns, time in orbital periods,
q̇ = p, ṗ = −∂V/∂q(q, φ), φ̇ = 1, with V(q, φ) = −ε* Σ_{m=1}^{7} A_m(e*) cos(2π(2q − mφ)), e* = 549/10000,
ε* = 69/200000 ([`soField`](../../KAM/Frozen/SpinOrbit/Defs/SoField.lean)). Write ψ = q − φ for the angle of the long
axis relative to the uniformly rotating mean direction (synchronous rotation means ψ stays bounded). All quantities
are real numbers, not reduced modulo 1.

### The synchronous periodic orbit

A function ψ : ℝ → ℝ is a *synchronous orbit* ([`IsSyncOrbit`](../../KAM/Frozen/SpinOrbit/Defs/IsSyncOrbit.lean#L25))
if it is C², has period 1, is odd (ψ(−φ) = −ψ(φ)), and
ψ″(φ) = −∂V/∂q(φ + ψ(φ), φ) for all φ;
equivalently, q(t) = φ(t) + ψ(φ(t)), p(t) = 1 + ψ′(φ(t)) solves the equations of motion.
ψ* = [`lunarSyncOrbit`](../../KAM/Frozen/SpinOrbit/Defs/LunarSyncOrbit.lean#L24) is defined as some synchronous orbit if
one exists (by choice) and 0 otherwise; the first two theorems make it canonical.

- [`lunarSyncOrbit_spec`](../../KAM/Frozen/SpinOrbit/Theorems/LunarSyncOrbitSpec.lean#L28): ψ* is a synchronous
  orbit (existence).
- [`lunarSyncOrbit_unique`](../../KAM/Frozen/SpinOrbit/Theorems/LunarSyncOrbitUnique.lean#L28): every synchronous orbit
  ψ equals ψ* (uniqueness among C², 1-periodic, **odd** solutions).
- [`lunarSyncOrbit_bound`](../../KAM/Frozen/SpinOrbit/Theorems/LunarSyncOrbitBound.lean#L27): for every real φ,
  |ψ*(φ)| ≤ 17/1000000 and |ψ*′(φ)| ≤ 27/200000.
  (17·10⁻⁶ turn ≈ 22 arcseconds; the spin rate on the orbit differs from 1 by at most 1.35·10⁻⁴.)

### The lock (`lunar_sync_lock`)

The libration action around ψ ([`libAction`](../../KAM/Frozen/SpinOrbit/Defs/LibAction.lean#L26)), with
Ω = [`lunarOmega`](../../KAM/Frozen/SpinOrbit/Defs/LunarOmega.lean) = 8/65, is

  𝓘(q, p, φ) = π (Ω X² + Y²/Ω),  X = q − φ − ψ*(φ),  Y = p − 1 − ψ*′(φ),

the area-type action of an ellipse in the deviation (X, Y) from the periodic orbit.

[`lunar_sync_lock`](../../KAM/Frozen/SpinOrbit/Theorems/LunarSyncLock.lean#L31):

> For all real q₀, p₀, φ₀ with **𝓘(q₀, p₀, φ₀) < 129/10000**, there is a global solution z(t) = (q(t), p(t), φ(t))
> with z(0) = (q₀, p₀, φ₀) such that for **every real t**:
> 1. |q(t) − φ(t) − ψ*(φ(t))| ≤ **21/100** (0.21 turn = 75.6°);
> 2. |p(t) − 1 − ψ*′(φ(t))| ≤ **26/1000**;
> 3. |q(t) − φ(t)| < **1/4** (strictly less than a quarter turn);
>
> and every global solution y with y(0) = (q₀, p₀, φ₀) equals z.

Reading the hypothesis: with Ω = 8/65 it is the interior of an ellipse in (X₀, Y₀); for Y₀ = 0 it allows
|X₀| < 0.1827 turn (about 66°), for X₀ = 0 it allows |Y₀| < 0.0225. Combined with the bound on ψ*′, conclusion 2
gives |p(t) − 1| ≤ 0.026135 for all t. Conclusion 3 says the long axis never reaches the unstable orientation at a
quarter turn (the separatrix), and since q − φ is not taken modulo 1, the Moon never slips a turn, forward or
backward in time.

## What is assumed and what is not claimed

- **Model, not the Moon.** As in part 2: a conservative, truncated seven-mode model with exact rational e and ε; no
  tides or dissipation, a fixed Kepler orbit, spin axis perpendicular to the orbit, no parameter uncertainty.
  Nothing is asserted about the physical Moon.
- **One orientation.** ψ* + 1/2 (the long axis pointing the other way) is also a synchronous orbit; it is not odd, so
  uniqueness does not cover it, and the lock theorem says nothing about states near it. Uniqueness among all
  1-periodic orbits is false for this reason.
- **Literal hypothesis.** The hypothesis uses q₀ − φ₀ as a real number. A state differing by a whole turn in q₀ is
  physically the same orientation but is not covered as stated (it is covered by the 1-periodicity of the model,
  which is not part of the statement).
- **Constants.** The spin bound 2.6 % is the ellipse bound; the true torus maximum is about 2.51 % (owner question Q3,
  accepted). Ω = 8/65 and the literals 129/10000, 21/100, 26/1000 come from the N = 65 data by the rules of the design;
  17/1000000 and 27/200000 come from an analytic contraction argument with no data (D49).
- **Route rulings.** One librational torus, no shell between two tori (D45, statement L1); bounds stated around the
  certified periodic orbit ψ*, not around a rational approximation (D45); no Birkhoff normalisation; N = 65 directly.
  The rational centre used in the proof appears in no frozen text (Q7). Whether this result is new relative to
  Celletti (1994) is left conditional in the project's wording (D45).
- No owner premise or numerical assumption enters the theorems; the only hypothesis of `lunar_sync_lock` is the
  action bound.

## Sources and proof

Model as in part 2 (Celletti 2010, eq. (7.55)); librational tori for spin–orbit problems follow the idea of Celletti
(1994). **The periodic orbit** ([`KAM/SpinOrbit/Lock/PO/`](../../KAM/SpinOrbit/Lock/PO/)) is found without numerical
data: odd 1-periodic functions vanish at half-integers, so the orbit equation becomes a Dirichlet problem on
intervals of length 1/2; its Green operator turns the equation into a fixed-point problem that is a contraction with
constant 1/2 in the sup norm, which gives existence, uniqueness among odd orbits and the bounds (from rational
majorants of the Lipschitz constant and the forcing). **The lock** ([`KAM/SpinOrbit/Lock/`](../../KAM/SpinOrbit/Lock/)):
an exact symplectic change to elliptic polar coordinates (Ω = 8/65) around a rational approximate centre, a new
square-root node in the certificate's expression language, and the v2 certifier `checkTorusCertificateV2 routeAV2`
of [part 1](SO-1.md), unchanged, applied to one librational torus at libration about 74° with a Diophantine
frequency built from 1 + 1/(65 + g), g = (√5 − 1)/2 (γ = 1/67, τ = 1). A graph certificate shows the torus is a graph
of the polar action over the polar angle and φ, with action between 13155/1000000 and 163/10000; the solid torus
inside it is invariant, so solutions starting inside stay inside (`lock_confinement`), and an exact rational
literal check converts this into the bounds around ψ*
([`AssemblyN65.lean`](../../KAM/SpinOrbit/Data/LockN65/AssemblyN65.lean)). The certificate chain has 13,668 generated
modules (about 242 MB of source, D67, D70) in the opt-in library `KAMLunarLock` (D51); it passed Lean's kernel on a
rented remote machine. The frozen theorems are proved by the providers in
[`KAM/Provider/SpinOrbit/`](../../KAM/Provider/SpinOrbit/) through the bridges of
[`FrozenBridge.lean`](../../KAM/SpinOrbit/Lock/FrozenBridge.lean). Design: [`SO-LOCK-DESIGN.md`](../tracks/SO/design/SO-LOCK-DESIGN.md),
[`FREEZE-PROPOSAL-LOCK.md`](../tracks/SO/design/FREEZE-PROPOSAL-LOCK.md); decisions D42, D45, D49, D55, D63, D67, D70 in
[`DECISIONS.md`](../DECISIONS.md); seal audit [`LOCK-SEAL-audit-1.md`](../tracks/SO/audits/LOCK-SEAL-audit-1.md).
