# Package LP3-COVERPERT: the finite sharp cover and the normalized perturbation (LP3-COVER + LP3-PERT)

LP3, phase 2 (the plan passed review: `docs/tracks/LP/lp3/LP3-PLAN-REVIEW-1.md`, PASS WITH NOTES, changes applied).
Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff; it carries the
D58 (OD-13) import exception for the sealed `partialConvex_nekhoroshev`; never import a provider). Base: `inp-lp`.

## Source

`docs/tracks/LP/lp3/LP3-PLAN.md`: §2.1 (the frozen interface), §2.2 (fixed data (F1)–(F7), chosen before `μ`), §2.3
(discharging the premises cell by cell), §3 (the whole sublevel), §5 rows LP3-COVER and LP3-PERT; and the review's
NOTEs. Write the scalar small parameter `B₀μ` as `ε` (review C4).

## Owned files

`KAM/Planetary/StrongAMD/Nek/Cover.lean` and `KAM/Planetary/StrongAMD/Nek/Perturbation.lean` (split if needed). Do
not edit other files. LP3-KEP (`Nek/Kepler.lean`) runs in parallel on another branch; do not depend on it.

## Statements

**LP3-COVER** (plan §2.2–§2.3, (F3)–(F7)):
- the widths;
- a finite cover of `𝓛_δ` by balls `G_j = ball(c_j, η)` with `c_j ∈ 𝓛_δ`, cells `G_j ⊆ G′_j` (open, convex, with the
  collar `closedBall I ρ ⊆ G′_j`) and slow levels `D_j = slowBall(B(c_j) − 5δ/16)`;
- the per-cell threshold bound `|B(I⁰) − B(c_j)| ≤ δ/16`;
- the containment `partialComplexDomain G′_j D_j ρ ⊆ complexTube(strongCore, R/2)` (via LP-DOM's
  `strongCore_containment` with centre `c_j`);
- `ε_D > 0`.

All constants come before `μ`. Every admissible initial action lies in some `innerCore G_j (·)`.

**LP3-PERT** (plan §2.3):
- the global normalized `P = fc/B₀` (LP-DOM's `exists_strongTube`), with `IsPartialPerturbation G′_j D_j ρ P` on every
  cell, and the same for `−P`;
- the cell Hamiltonian identity: on the real cell region, `degenerateHamiltonian (realPart h) (P.re) ε` with
  `ε = B₀ μ` equals the chart Hamiltonian exactly, with no time conversion (plan §0.4, §2.3; corrected per audit
  LP-W5A-1 N1: the earlier wording "divided by `B₀`" was wrong);
- equality of Hamiltonian fields on the open set (track P's `fderiv_eq_of_eqOn_open`,
  `hamiltonianVectorField_eq_of_eqOn_open` in `Exponential/Hamiltonian.lean`).

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` (expect only the standard three; no `sorryAx`).

If a premise of the frozen theorem cannot be met as the plan says, STOP and report the exact premise and
inequality. Expected size 350–600 lines.

## Handoff

`docs/tracks/LP/audits/LP3-COVERPERT-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP3-COVERPERT.md`,
then `touch .drafts/READY-LP3-COVERPERT`.
