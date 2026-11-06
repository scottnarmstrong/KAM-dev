# SJSU gate 2 in Lean (program T2-CONF): overview

The goal is a kernel-checked theorem that, in the planar secular Sun–Jupiter–Saturn–Uranus model `SJSU18-O2`,
every state within 10⁻⁶ of the nominal state stays confined for 5·10⁹ years, with all three eccentricities in explicit
intervals. Decisions D74–D76 are in [`docs/DECISIONS.md`](../DECISIONS.md).

## Read in this order

1. [`sjs-rigor-plan.md`](sjs-rigor-plan.md): the scoping plan. It covers the target theorems, the route through the
   repository, cost estimates, gates and owner decisions (§6).
2. [`sjsu-g2-gates.md`](sjsu-g2-gates.md): phase 1, the numerical gates SR-1..SR-7. All pass.
   - SR-1 chose the complex form of the model as the model of record (D75).
   - The rigorous arb mirror gives T ≈ 6.7·10¹² yr.
   - The checker cost is about 1–2 CPU-h of kernel time.
3. [`sjsu-g2-t2conf-proposal.md`](sjsu-g2-t2conf-proposal.md): the exact Lean statement `sjsu_secular_confinement`
   and the frozen data definition `sjsu18O2`, approved by the owner (D76). Its audit is
   [`sjsu-g2-audits/STMT-AUDIT-1.md`](sjsu-g2-audits/STMT-AUDIT-1.md).
4. [`sjsu-g2-decisions.md`](sjsu-g2-decisions.md): the program's decision log.

## Method in one paragraph

The confinement engine is the ordinary theorem
`KAM.Application.Confinement.hamiltonian_approxIntegrals_confinement`
([`ApproxIntegral.lean`](../../KAM/Application/Confinement/ApproxIntegral.lean)). Its hypotheses are:
- the drift bounds |{F_j, H}| ≤ η_j on the tube D;
- the face condition on ∂D.

From them it gives existence, uniqueness and confinement for |t| ≤ T, by a first-exit argument.

The approximate integrals F_j come from the near-torus Kolmogorov-then-Birkhoff normal form of the SJSU gate-2
exploration. They are produced in Python and are untrusted. A new Lean checker, `checkTube_sound`, proves the
hypotheses from finite exact computations. Those use packed trigonometric and Taylor models with whitened big-Nat
literals, the lesson of the Moon's lock in [`lean-kernel-nat-literal-hash.md`](lean-kernel-nat-literal-hash.md). No KAM
theorem is used.

**Caveat:** the theorem concerns the averaged, truncated secular model, not the full Newtonian problem.

## Lean packages (in progress; the completion meter is on the README)

| Package | Content |
|---|---|
| N2 | symplectic and polar charts |
| N3 | trigonometric models and packed products |
| N4 | square-root witnesses |
| N5 | Hamiltonian Taylor models and the tube checker's soundness |
| N6 | eccentricity enclosure |
| N7 | producer, data, kernel run and the opt-in library `KAMSJSU` |

After N2–N7, the theorem is frozen and sealed in one pass.
