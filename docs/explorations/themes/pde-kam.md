# PDE KAM

[← Back to the catalogue](../README.md)

One document, from 28 October 2026. Its recommendations were adopted the same day as track W (decision D30, recorded
inside the document, §9). The exact statements were approved and frozen on 30 October (D41): the theorem `nlw2` is
frozen with a `sorry` body and is being proved by the track-W sub-orchestrator; see
[`docs/STATEMENTS.md`](../../STATEMENTS.md#nlw2) and [W-STATEMENTS](../../tracks/W/W-STATEMENTS.md).

## PDE KAM and perpetual leapfrogging

**[pde-kam-and-leapfrogging.md](../pde-kam-and-leapfrogging.md)** · 28 October 2026 · research exploration ·
status: **adopted** (D30) as track W; statements frozen (D41); proof **running**

The report recommends a bounded first PDE target: two-frequency quasi-periodic solutions of the cubic wave equation
u_tt = u_xx − m u − u³ on (0, π) with Dirichlet conditions, built on modes 1 and 2, for every fixed mass m > 0 (Pöschel
1996, using Kuksin–Pöschel 1996 and Pöschel's abstract PDE KAM theorem). The nonlinear field gains one derivative, so no
Nash–Moser scheme is needed. The proposed headline W-NLW2 gives, for each m, a Borel set of small action parameters of
density one at the origin, two Diophantine frequencies, small analytic embedded tori, exact invariance and classical
solutions for all real time. The density is in a finite-dimensional parameter set, not a measure on PDE initial data.
The report says GO-LATER for Hassainia–Hmidi–Masmoudi's leapfrogging vortex patches: those solutions are periodic in
time, not two-frequency, and their proof uses Nash–Moser with loss of derivatives.

- **Numbers and verdicts.** The printed quartic normalization in Pöschel's wave paper is inconsistent: recomputed from
  the Hamiltonian, the action twist is A_ii = 9/(8πλ_i²), A_ij = 3/(2πλ_iλ_j), and the printed diagonal is 16 times
  larger (candidate erratum E-PDE-W-1). The refined measure estimate (Pöschel's Theorem D) is decisive: with κ = 2 the
  coarse exponent sits at the borderline, while the refined exponent 16/23 leaves a margin. Milestones W0–W8 total
  34k–70k Lean lines (low confidence); leapfrogging would add 70k–160k after W (very low confidence). The cubic NLS
  equation is a cheaper fallback (integer quartic divisors), at an estimated saving of 5k–10k lines.
- **Main risks named.** The refined wave measure estimate, boundedness of the infinite homological operator,
  weak-symplectic flow calculus, and the source normalization.
- **Candidate errata.** E-PDE-W-1 (factor 16), E-PDE-W-2 (real/complex recovery and action normalization),
  E-PDE-KP-1 (a factor 4 in the Kuksin–Pöschel author version), E-PDE-KP-2 (for mass m = −9 a lemma's premise fails, a
  gap in the unrestricted-mass assertion; the proposals restrict to m > 0).
- **Owner decision (D30).** The wave equation rather than NLS; density one in action parameters as the measure
  conclusion; the first headline without linear stability or Whitney regularity; normalization repaired in the
  blueprint after independent checking, never frozen from the printed formulas.
- **Connection.** It notes that the fluid-body discussion in
  [realistic-kam-and-finite-size](../realistic-kam-and-finite-size.md) does not rule out the planar-vorticity
  leapfrogging result, which concerns vortex patches rather than self-gravitating bodies.

[← Back to the catalogue](../README.md)
