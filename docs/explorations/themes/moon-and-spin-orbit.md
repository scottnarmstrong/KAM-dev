# Realistic KAM, the Moon and spin–orbit

[← Back to the catalogue](../README.md)

Three documents from 27–30 October 2026. The question "can KAM be made more realistic, and what about bodies of finite
size?" led to proposal C2 (a spin–orbit confinement theorem with a certificate). The lunar proposal turned C2 into a
project, which the owner started as track SO on 29 October (D30). The band target then moved three times: from 3 % in the
proposal to 3.3 % (D30, after its numerical pilot), to 2.8–2.9 % (D37, the lunar-band note), and to barriers at N = 65
with a band of about 2.71 % (D38). The Moon-lock follow-up (D42, D45) lives in track SO; see
[SO-LOCK-SCOPE](../../tracks/SO/studies/SO-LOCK-SCOPE.md). The scouting of the Moon and other spin–orbit targets in
[striking-applications](../striking-applications.md) §4 is catalogued under
[applications and demonstrations](applications-and-demonstrations.md).

| Document | Status | One line |
|---|---|---|
| [realistic-kam-and-finite-size](../realistic-kam-and-finite-size.md) | partly adopted (C2 → track SO) | A-posteriori KAM plus a computer proof is the realistic form; finite size surveyed |
| [lunar-spin-orbit-certificate-proposal](../lunar-spin-orbit-certificate-proposal.md) | adopted (D30), running | Two certified barriers confine the Moon's spin rate in a seven-mode model |
| [lunar-band-2p8-2p9](../lunar-band-2p8-2p9.md) | adopted (D37), then overtaken (D38) | Move the barriers toward the separatrix floor 2.62 % |

## Realistic KAM and bodies of finite size

**[realistic-kam-and-finite-size.md](../realistic-kam-and-finite-size.md)** · 27 October 2026 · research report built on
three literature surveys · status: **partly adopted** (proposal C2 became track SO, D30; C1 and C3 remain proposals);
one claim corrected later

The report argues that the realistic form of KAM is the a-posteriori theorem plus a computer-assisted proof: fix the
actual Hamiltonian, compute an approximate torus and verify its error against an explicit threshold, with no small
parameter. That is the campaign's G1 route. Results proved at true parameters exist only for reduced models (the secular
Sun–Jupiter–Saturn model of Locatelli–Giorgilli 2000, truncated restricted problems, Trojans, exoplanet analogues); the
full planar Sun–Jupiter–Saturn torus of Figueras–Haro 2025 is computed to error about 10⁻⁵⁴ but not certified. On finite
size: spherical bodies cost nothing (shell theorem); asphericity and spin are a different problem, understood only in
the 1½-degree-of-freedom spin–orbit model (Celletti 1990); tides make "for all time" false; self-gravitating fluid bodies
are open.

- **Numbers and verdicts.** Hénon's estimate for Arnold's theorem needs masses below about 10⁻³³³ (10⁻¹¹³¹ for spatial
  Sun–Jupiter–Saturn, per Laskar). Giorgilli–Locatelli–Sansottera 2017 reach the age of the Solar System only in a
  neighbourhood about 10 times smaller than the observational uncertainty; Barbieri–Niederman need ε ≲ 10⁻¹¹·²⁵.
  Arnold diffusion is proved in planetary regimes, so with three or more degrees of freedom "every orbit in an open set is
  stable for all time" cannot hold in general.
- **Proposals.** C1: spheres corollary of track P (a few hundred lines). C2: spin–orbit confinement with a certificate,
  "the first formally verified KAM statement about a real body (the Moon, in the truncated model of Celletti 1990)".
  C3: conformally symplectic a-posteriori KAM for tidal models (5–10k lines). C4, not recommended now: N rigid bodies,
  1PN planetary KAM, fluid bodies, tidal all-time statements.
- **Followed by.** [lunar-spin-orbit-certificate-proposal](../lunar-spin-orbit-certificate-proposal.md) cites C2 as its
  starting point.
- **Disagreement.** §B2 says there is no rigorous KAM statement for Mercury's 3:2 resonance at its true parameters.
  [next-demonstrations](../next-demonstrations.md) and [plan-mercury-32](../plan-mercury-32.md) report that the abstract
  of Celletti–Falcolini (1992) describes rigorously constructed trapping surfaces for Mercury (full article not read).

## Lunar spin–orbit confinement with a Lean-checked certificate

**[lunar-spin-orbit-certificate-proposal.md](../lunar-spin-orbit-certificate-proposal.md)** · 29 October 2026 · project
proposal · status: **adopted** (D30) as track SO, **running** (certificate checker done; the Moon's spin-rate theorem
in progress)

The proposal asks for a Lean proof that, in an explicit conservative seven-mode spin–orbit model (Celletti, eq. 7.55) at
e = 549/10000 and ε = 69/200000, every initial condition in an explicit region between two invariant graph tori satisfies
|p(t) − 1| ≤ 3/100 for all real t, where p is the spin rate divided by the orbital mean motion. It lays out the route: a
finite certificate format and a soundness theorem through the explicit isoenergetic theorem `g1_explicit`; a scalar
Fourier candidate whose invariance error reduces to one residual; a clock lemma that fixes the physical frequency;
transport of embedding errors to graph bounds; and the barrier argument `gen_barrier`. Milestones M0–M6 have a stop/go
point after a numerical pilot; no line counts or calendar are given.

- **Numbers.** Barrier frequencies ν± = 1 ± 1/(40 + g), g = (√5 − 1)/2, Diophantine exponent τ = 1; outer band
  [97/100, 103/100]. The ordinary Hessian of p²/2 + J is singular while the bordered determinant is −1, so the
  isoenergetic theorem is the right one.
- **Extensions listed.** Untruncated Kepler forcing; parameter boxes; a sharper band; other bodies; librational tori as a
  different target.
- **Later changes.** According to the [track SO plan](../../campaign/design/SPIN-ORBIT-PLAN.md), the pilot found the 3 % band
  fails numerically (the tori reach 0.968007 and 1.031992), so D30 set the target to 33/1000.
  [lunar-band-2p8-2p9](../lunar-band-2p8-2p9.md) explains why: in the pendulum approximation the N = 40 barrier reaches
  about 3.19 %. Later targets: D37 (2.8–2.9 %) and D38 (N = 65, about 2.71 %). The certificate now goes through the sharp
  and v2 certifiers rather than `g1_explicit` (D36, D37, D44).

## Lunar spin–orbit band: aim for 2.8–2.9 %

**[lunar-band-2p8-2p9.md](../lunar-band-2p8-2p9.md)** · 30 October 2026 · proposal for the SO track · status:
**adopted** (D37), then **overtaken** by D38 (barriers at N = 65)

Once the sharp a-posteriori theorem lands (it moves the required invariance error for the lunar package from about
10⁻⁷⁵ to about 10⁻²⁵), the note proposes moving the barriers from 1 ± 1/(40 + g) to 1 ± 1/(50 + g) or 1 ± 1/(60 + g),
which shrinks the band from 3.3 % to about 2.9 % or 2.8 %. No rotational barrier can beat the separatrix of the synchronous
resonance, at |p − 1| ≈ 2.62 % (2√(εA₂) ≈ 0.02617). The cost driver near the separatrix is slower Fourier decay, not the
Diophantine constant (0.4–0.7 orders). A certified 2.8–2.9 % band would be tighter than Celletti's ≈ 3 % rotational
benchmark and, as far as the authors found, the first kernel-checked band of this kind. It does not supersede the
published librational tori, which prove a different, stronger confinement for near-synchronous initial data.

- **Numbers.** Pendulum estimate of the band on the barrier: N = 40: 3.19 %; 50: 2.89 %; 60: 2.75 %; 80: 2.64 %;
  100: 2.62 %. The first row explains why the 3 % target of the
  [lunar proposal](../lunar-spin-orbit-certificate-proposal.md), with barriers at N = 40, became 3.3 %.
- **In-document corrections (30 October).** The binding Diophantine mode in the rotated frame is (1, 0); the Gram inverse
  grows 41 % at N = 50 (v2 design §8); [striking-applications](../striking-applications.md) measured 2.65 % at N = 80
  with floor 2.617 %.
- **Disagreement.** The note says librational barriers need a Birkhoff-type normal form or a G1 for non-graph tori.
  [striking-applications](../striking-applications.md) §3 shows that an explicit polar chart makes librational tori
  primary (only a `sqrt` primitive is needed), and D45 chose that route with no Birkhoff normalization.

[← Back to the catalogue](../README.md)
