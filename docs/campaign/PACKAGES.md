# Work packages

The board of open work, for agents and collaborators. Pick an **open** package, mark it `claimed (name, date)` in this
file in the same commit as your first work on it, and mark it `done (commit)` when it lands.

Rules for every package are in [`AGENTS.md`](../../AGENTS.md). The most important ones:
- every `.lean` file is a module;
- never `set_option maxHeartbeats`; no file over 1500 lines; no `sorry` or `axiom`;
- never edit `KAM/Frozen/`, `manifest/` or `KAM.lean` (run `python3 scripts/gen_root_imports.py`);
- never import a frozen theorem or a provider;
- run `scripts/lint_sources.sh` and `lake build` before pushing.

Statements are in [`blueprint/`](../../blueprint) (labels `bp:…`). A package proves its blueprint lemmas as stated,
or reports why it cannot. Infrastructure packages (`I-…`) may start before the dependency graph is complete; this is
recorded as off-frontier infrastructure needed by several graph nodes. Provider packages (`P-…`), which prove frozen
theorems, start only from the reviewed dependency graph.

Uses of `KAM.IsDiophantine` and `KAM.Diophantine.Condition` convert through
`KAM.Diophantine.condition_iff_isDiophantine` (`KAM/Diophantine/Frozen.lean`).

## Infrastructure (open now)

| ID | Goal | Blueprint | Owned files | Depends on | Status |
|---|---|---|---|---|---|
| I-FOURIER-1 | Weighted coefficient norm, derivative bound, convolution | `docs/fourier-conventions.md` | `KAM/Fourier/` | — | done (Zohar, 4f1976a) |
| I-DIOPH-1 | Coefficient cohomological solver, small-divisor estimate, Lipschitz dependence on ω | `docs/cohomological-equation.md` | `KAM/Diophantine/` | I-FOURIER-1 | done (Zohar, a987e91) |
| I-DIOPH-2 | Bridge `Condition ↔ IsDiophantine` | — | `KAM/Diophantine/Frozen.lean` | I-DIOPH-1 | done (orchestrator) |
| I-STRIP-1 | Cauchy estimates on strips and on open sets | `bp:p1:cauchy-strip`, `bp:p1:cauchy-open` | `KAM/Strip/Cauchy.lean`, `Regularity.lean`, `HigherCauchy.lean` | — | done (Zohar, a664728) |
| I-STRIP-2 | Fourier coefficients of periodic holomorphic functions: decay and summation | `bp:p1:decay`, `bp:p1:summation` | `KAM/Strip/Fourier.lean` | I-FOURIER-1 | claimed (Zohar, 2026-10-27); `bp:p1:decay` done, `bp:p1:summation` in progress |
| I-STRIP-3 | Cohomological equation on strips (sup norms, crude exponent τ + n), real on reals | `bp:p1:cohomological` | `KAM/Strip/Cohomological.lean` | I-STRIP-2, I-DIOPH-1 | open |
| I-STRIP-4 | Averages of derivatives; Neumann series for matrix-valued functions | `bp:p1:averages`, `bp:p1:neumann` | `KAM/Strip/Averages.lean`, `KAM/Matrix/Neumann.lean` | — | done (Zohar, c2b079d) |
| I-STRIP-5 | Holomorphic on an open subset of ℂᵐ implies analytic (power series); real restriction is real-analytic. Not in Mathlib beyond one variable; worth upstreaming | `bp:p1:holomorphic-analytic`, `bp:p1:real-restriction` | `KAM/Strip/Analytic.lean` | I-STRIP-1 (Regularity) | claimed (orchestrator, Sonnet prover, 2026-10-27; brief docs/campaign/briefs/I-STRIP-5.md) |

Notes for the `I-STRIP` packages:
- Use the frozen `KAM.complexStrip` for strips.
- Holomorphy is `DifferentiableOn ℂ` on the open strip.
- Sup norms are expressed as `∀ θ ∈ complexStrip n ρ, ‖u θ‖ ≤ A`, not through `sSup`, so that the lemmas plug
  into the frozen G1 and G2 hypotheses directly.
- The one-variable Cauchy estimate in Mathlib is `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`; apply it to
  the restriction to one coordinate.

## Track K proof campaign: wave 1 (claimed 2026-10-27)

Sonnet provers in their own worktrees; GPT-6.1-Sol medium audits before landing (D21, D24). Briefs are in
[`docs/campaign/briefs/`](briefs). The graph is [`docs/graph/K/DEPGRAPH.md`](../graph/K/DEPGRAPH.md).

| ID | Goal | Graph nodes | Owned files | Status |
|---|---|---|---|---|
| P-G3 | Provider of the frozen G3 `KAM.volume_not_diophantine_le` | closure of `bp:p0:g3` (Part 4 §G3) | `KAM/Measure/{Lattice,Slab}.lean`, `KAM/Provider/VolumeNotDiophantineLe.lean` | claimed (orchestrator, 2026-10-27) |
| I-MAT | Matrix norms, real and holomorphic inverses | `bp:p1:operator-norms`, `matrix-norms`, `real-inverse`, `holomorphic-inverse` | `KAM/Matrix/{Norms,Inverse}.lean` | claimed (orchestrator, 2026-10-27) |
| I-LIP | Lipschitz images, McShane, lipeomorphisms | `bp:p1:lip-image(-product)`, `mcshane`, `lipeo(-fixed)` | `KAM/Measure/{Lipschitz,McShane,Lipeo}.lean` | claimed (orchestrator, 2026-10-27) |
| I-STRIP-5 | Several-variable analyticity; real restrictions | `bp:p1:holomorphic-analytic`, `real-restriction(-consequences)`, `hamiltonian-real` | `KAM/Strip/{Analytic,RealRestriction}.lean` | claimed (orchestrator, 2026-10-27) |

I-STRIP-2 (decay, summation) and I-STRIP-3 (cohomological equation on strips) stay open for Zohar, building on his
Fourier and Diophantine packages.

## Waiting for the blueprint

| ID | Goal | Blueprint | Waits for |
|---|---|---|---|
| P-G3 | Provider of `KAM.volume_not_diophantine_le` | Part 4, G3 section | blueprint §G3 and its graph |
| I-GEOM | Approximate geometric properties of HL19 §4 (Lagrangian defect, frame, torsion) | Part 2 | blueprint Part 2 |
| I-STEP | The Newton step and the iteration (HL19 §5, App. B) | Part 2 | blueprint Part 2 |
| I-UNIQ | Local uniqueness for flows | Part 3 | blueprint Part 3 |
| I-MEAS | Lipschitz dependence, McShane extension, measure assembly | Part 4 | blueprint Part 4 |
