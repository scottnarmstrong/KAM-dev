# LIFT-CONF handoff: the confinement lemmas in the core

## LIFT-CONF-FIX (audit AUDIT-LIFT-CONF-1, PASS WITH CHANGES)

All findings are addressed on `lift-conf`. The branch is still additive: no existing `KAM/**.lean` is edited.

- **C1 (uniqueness).** `twoTorus_confinement` (and its new invariance form) now has a third conjunct:
  `∀ w', w' 0 = w₀ → (∀ t, HasDerivAt w' (V (w' t)) t) → w' = w`. Every global solution through `w₀` is the
  confined one, so "the solution" in the docstrings is accurate. The proof uses a new lemma in `GlobalODE`,
  `eq_of_lipschitzOnWith_of_mem_open`: if `V` is Lipschitz on `S`, a global solution stays in an open `O ⊆ S`, and a
  second global solution starts at the same point, then the two are equal (the agreement set is clopen;
  `ODE_solution_unique_of_eventually` near each time).
- **C2 (`hH : Continuous H` dropped).** The theorem has no hypothesis on `H` off the box. The closed region is now
  `boxSet α β ∩ H⁻¹{E} ∩ {g₁ ≥ 0} ∩ {g₂ ≥ 0}`. It is closed by `ContinuousOn.preimage_isClosed_of_isClosed`, using
  the continuity of `H` on the box that differentiability there gives. Chart Hamiltonians defined only on positive
  actions fit.
- **C3 (Moon claim, invariance variant).**
  - The Moon "Use" is reworded below, and the extended-phase-space sentence is removed from the `Level`
    docstring.
  - New structure `InvariantGraph V H E lo hi`: the `GraphTorus` data with the linear flow replaced by invariance,
    `∀ θ, ∃ γ, γ 0 = k θ ∧ ∀ s, HasDerivAt γ (V (γ s)) s ∧ γ s ∈ range k`.
  - New main theorem `twoTorus_confinement_of_invariant` for two `InvariantGraph`s.
  - `GraphTorus` is kept with the same fields. `GraphTorus.toInvariantGraph` uses the lines `s ↦ k (θ + s ν)`, and
    `GraphTorus.graph₁` is definitionally the same.
  - `twoTorus_confinement` (for `GraphTorus`) is a one-line corollary with the same conclusion.
- **Tilted toy.** New test `tilt_confined`:
  - Setup: `H = −a₂ + a₁/4`, field `((1/4, −1), 0)`, flat tori `a = ∓(1/2, 1/8)` on the level `H = 0`, box
    `[−1, 1]²`.
  - The faces `a₂ = ±1` come from `face_of_cone`, with `M = 1/4`, `m = 1`, `Wd = 1/2` and the reference point
    `a = 0` on the level.
  - The conclusion includes `−1 < a₂ < 1` and the uniqueness conjunct.
  - `toy_confined` now also states uniqueness.
- **Clamped-field step factored out.** The step is now `lipschitzWith_clamped` in `GlobalODE`: if `V` is `K`-Lipschitz
  on `ℝⁿ × [α, β]`, then `p ↦ V (p.1, clampBox α β p.2)` is `K`-Lipschitz. `TwoTorus` uses it.

**Consumer impact (LG00 switch).**
- `twoTorus_confinement` loses its `hH` argument (the 5th explicit argument, after `hVC`), and its result gains a third
  conjunct (`obtain ⟨w, hw0, hw, huniq⟩`).
- `GraphTorus`'s fields and `graph₁` are unchanged.
- The prepared LG00 switch patch is regenerated for this API.

**Checks (LIFT-CONF-FIX).**
- **Builds:** `lake build` of `KAM.Application.Confinement.{GlobalODE, Level, Periodic, TwoTorus}` and
  `KAM.Application.Tests.Confinement`, one at a time, under a 4 GB cap with `nice -n 5`. All give `exit 0` in
  1.4–4.8 s, ≤ 1.52 GB each, with no warnings.
- **Source checks:** lines ≤ 100; no `sorry`/`admit`/`axiom`/`native_decide`/options.
- **File lengths:** GlobalODE 173, Level 182, Periodic 106, TwoTorus 352, Tests 186.
- **`#print axioms`:** all of the following give `[propext, Classical.choice, Quot.sound]`:
  - `exists_global_solution`, `eq_of_lipschitzOnWith_of_mem_open`, `lipschitzWith_clampBox`,
    `lipschitzWith_clamped`;
  - `eq_of_energy_eq`, `face_of_cone`, `exists_lipschitzOnWith_of_periodic`;
  - `twoTorus_confinement_of_invariant`, `twoTorus_confinement`;
  - `toy_confined`, `tilt_confined`.
- **`scripts/lint_sources.sh`:** as before. `check_lean_modules: PASS (3705 Lean files)` and
  `FROZEN-ANCHOR GUARD OK`. The expected stale-root message (`KAM/Root/Application.lean`; regenerate at landing).
  The ABI stage stops on the seeded snapshot's missing `FixedSunPlanetaryKAM.olean`.

**Not done.** The auditor's note on reusing the core `KAM.ODE` layer (`gen_maximal` etc.) instead of the clamp is
left as is. The modules stay Mathlib-only.

## LIFT-CONF (original)

Branch `lift-conf` from `origin/main` (`7a01a22d`), worktree `/home/scott/KAM-dev-worktrees/lift-conf`. Local commits
only. The lemmas come from LG00-CONF (`lg00-conf2`, `applications/lg00/LG00/Confinement/{GlobalODE,Level,Periodic,
TwoTorus}.lean`); they are moved here unchanged in substance. The changes:
- the namespace is `KAM.Application.Confinement`;
- the docstrings are stated for general Hamiltonian fields on a chart;
- `boxSet`, `openBoxSet` and the periodic Lipschitz lemma are generalized to charts `(Fin n → ℝ) × (Fin m → ℝ)`.

The change is additive: six new files (five Lean files and this handoff), and no existing `KAM/**.lean` is
edited. The generated root needs `python3 -I scripts/gen_root_imports.py` at landing; I did not edit the generated
files (rule 10).

## Files

| Module | Imports | Content |
|---|---|---|
| `KAM/Application/Confinement/GlobalODE.lean` (173) | Mathlib | `exists_global_solution`: a bounded, globally Lipschitz autonomous field on a Banach space has a solution on `ℝ` through every point (Picard–Lindelöf on `[-(n+1), n+1]`, glued by uniqueness). `eq_of_lipschitzOnWith_of_mem_open`: uniqueness of a global solution staying in an open set where the field is Lipschitz. `clampBox α β`: the coordinatewise clamp to a box (1-Lipschitz, the identity on the box); `lipschitzWith_clamped` |
| `KAM/Application/Confinement/Level.lean` (182) | Mathlib | `Phase := ℝ² × ℝ²`; `boxSet α β` (any `n`, `m`); `actLine`. In two degrees of freedom: `eq_of_energy_eq` (on the box, with `∂H/∂a₂ < 0`, a level point is determined by `(θ, a₁)`) and `face_of_cone` (the faces `a₂ = α₂, β₂` are off the level over a strip of `a₁`, from `|∂H/∂a₁| ≤ M`, `∂H/∂a₂ ≤ −m` and the cone inequalities) |
| `KAM/Application/Confinement/Periodic.lean` (106) | `Level` | `exists_lipschitzOnWith_of_periodic`: a map on `ℝⁿ × ℝᵐ`, `C¹` on an open set containing `ℝⁿ × [α, β]` and `ℤⁿ`-periodic in the angles, is Lipschitz and bounded on the box |
| `KAM/Application/Confinement/TwoTorus.lean` (352) | the above | `InvariantGraph` (an invariant graph over the angles on a level `H = E`); `GraphTorus` (the same with a linear flow of `V`) and `GraphTorus.toInvariantGraph`; `openBoxSet`; **`twoTorus_confinement_of_invariant`**: the solution through a point of the level strictly between two invariant graphs exists for all times, stays strictly between them and inside the box, and is the only global solution through that point; `twoTorus_confinement`: the same for two `GraphTorus`es |
| `KAM/Application/Tests/Confinement.lean` (186) | `TwoTorus`, `Periodic` | toy `H(θ, a) = −a₂`: `toy_clampBox`, `toy_lipschitz`, `flatTorus`, and `toy_confined` (`twoTorus_confinement` end to end with the flat tori `a₁ = ∓1/2`); tilted toy `H = −a₂ + a₁/4`: `tiltTorus` and `tilt_confined` (with `face_of_cone` for the faces) |

**Uses.**
- LG00's confinement (`LG00.Confinement`, which will import these modules in place of its copies).
- A possible further use, not checked here: barriers in other two-degree-of-freedom charts, e.g. the extended
  phase space `(θ, t; p, E)` of a periodically forced one-degree-of-freedom system. That needs barriers given as
  `InvariantGraph`s (or `GraphTorus`es, if a linearizing conjugacy is available), a box bound on the field, and the
  sign convention reached by relabelling or `H ↦ −H`. The core's spin-orbit barriers (`SoBarrier`) are not of this
  form as they stand, and that case is already covered by the core's `so_confinement`.

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
