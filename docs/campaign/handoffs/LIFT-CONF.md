# LIFT-CONF handoff: the confinement lemmas in the core

Branch `lift-conf` from `origin/main` (`7a01a22d`), worktree `/home/scott/KAM-dev-worktrees/lift-conf`. Local commits
only. The lemmas come from LG00-CONF (`lg00-conf2`, `applications/lg00/LG00/Confinement/{GlobalODE,Level,Periodic,
TwoTorus}.lean`); they are moved here unchanged in substance. The changes:
- the namespace is `KAM.Application.Confinement`;
- the docstrings are stated for general Hamiltonian fields on a chart;
- `boxSet`, `openBoxSet` and the periodic Lipschitz lemma are generalized to charts `(Fin n → ℝ) × (Fin m → ℝ)`.

The change is additive: five new files, and no existing `KAM/**.lean` is edited. The generated root needs
`python3 -I scripts/gen_root_imports.py` at landing; I did not edit the generated files (rule 10).

## Files

| Module | Imports | Content |
|---|---|---|
| `KAM/Application/Confinement/GlobalODE.lean` (132) | Mathlib | `exists_global_solution`: a bounded, globally Lipschitz autonomous field on a Banach space has a solution on `ℝ` through every point (Picard–Lindelöf on `[-(n+1), n+1]`, glued by uniqueness). `clampBox α β`: the coordinatewise clamp to a box (1-Lipschitz, the identity on the box) |
| `KAM/Application/Confinement/Level.lean` (182) | Mathlib | `Phase := ℝ² × ℝ²`; `boxSet α β` (any `n`, `m`); `actLine`. In two degrees of freedom: `eq_of_energy_eq` (on the box, with `∂H/∂a₂ < 0`, a level point is determined by `(θ, a₁)`) and `face_of_cone` (the faces `a₂ = α₂, β₂` are off the level over a strip of `a₁`, from `|∂H/∂a₁| ≤ M`, `∂H/∂a₂ ≤ −m` and the cone inequalities) |
| `KAM/Application/Confinement/Periodic.lean` (106) | `Level` | `exists_lipschitzOnWith_of_periodic`: a map on `ℝⁿ × ℝᵐ`, `C¹` on an open set containing `ℝⁿ × [α, β]` and `ℤⁿ`-periodic in the angles, is Lipschitz and bounded on the box |
| `KAM/Application/Confinement/TwoTorus.lean` (266) | the above | `GraphTorus` (an invariant torus that is a graph over the angles, with the linear flow of `V` on a level `H = E`); `openBoxSet`; **`twoTorus_confinement`**: the solution through a point of the level strictly between two graph tori exists for all times and stays strictly between them and inside the box |
| `KAM/Application/Tests/Confinement.lean` (98) | `TwoTorus`, `Periodic` | toy `H(θ, a) = −a₂`: `toy_clampBox`, `toy_lipschitz`, `flatTorus`, and `toy_confined`, which is `twoTorus_confinement` end to end with the flat tori `a₁ = ∓1/2` |

**Uses.**
- LG00's confinement (`LG00.Confinement`, which will import these modules in place of its copies).
- The extended phase space `(θ, t; p, E)` of a periodically forced one-degree-of-freedom system (e.g. the Moon's
  spin, between two invariant curves): there `H̃ = H(θ, t, p) + E`, the solved action is `a₂ = E` with
  `∂H̃/∂E = 1` (use `−H̃`, or relabel, for the sign), and the separating action is `a₁ = p`.

## Checks

- **Builds:** `lake build KAM.Application.Confinement.<M>` and `KAM.Application.Tests.Confinement`, one at a time
  under a 4 GB cap (`systemd-run --scope -p MemoryMax=4G`, `nice -n 5`): `exit 0`, 3–4 s, ≤ 1.5 GB each.
  `lake build --no-build` beforehand showed `main`'s build fully up to date (3275 jobs).
- **Diagnostics:** no warnings in these files; lines ≤ 100; no `sorry`/options.
- **`#print axioms`:** `exists_global_solution`, `lipschitzWith_clampBox`, `eq_of_energy_eq`, `face_of_cone`,
  `exists_lipschitzOnWith_of_periodic`, `twoTorus_confinement` and `toy_confined` all give
  `[propext, Classical.choice, Quot.sound]`.
- **`scripts/lint_sources.sh`:**
  - `check_lean_modules: PASS (3705 Lean files)`, `FROZEN-ANCHOR GUARD OK`;
  - "KAM.lean is out of date (KAM/Root/Application.lean)": expected for new modules; regenerate at landing;
  - the ABI stage stops on an olean missing from the seeded snapshot (`FixedSunPlanetaryKAM`), as on the other
    branches.
