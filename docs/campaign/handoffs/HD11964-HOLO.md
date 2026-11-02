# Handoff HD11964-HOLO (phase 2: the complex extension of `P`, `G₂`; the tail of `T₃`)

Worker kamx-hd11964, branch `hd11964-p2`. Task from the orchestrator (2 November 2026), while the audit of CHI-FIX + ROT
(`f5fcee29..4cf155a0`) runs:
1. the obligation found in HD11964-ROT: the complex extension of `P` (and `G₂`) on the anisotropic strip —
   holomorphic, `1`-periodic in `θ`, equal to `P` at real points — which needs the moving Hamiltonian free of collisions
   on the complex strip. **Scope it first**: the exact Lean statements and the margin (min `Re` of the complexified
   distance² over the strip and the cells, numerically); then prove it if the margin is comfortable;
2. the tail of `T₃ = {D_i r₁, χ₁}`.

Statements first. Nothing pushed.

**Status: DONE** (part 2, after DESIGN A).

- **Proved, part 1** (`HD11964.Holo`, `HD11964.HoloSlab`):
  - (1a) the Kepler contraction, on the uniform and the per-slab strips;
  - (1b) from a certified enclosure of `d²`;
  - (2a) the bracket by coordinates.
- **Proved, part 2** (`HD11964.HoloExt`, `HD11964.HoloG2`):
  - (1c) the extension of `P`: pointwise analyticity in all complex variables, periodicity, agreement with LP's real
    chart; in the drafted form on the three strips;
  - (1d) the real derivatives of `P` as complex derivatives, and the extension of `G₂` on the three strips;
  - the decided cell-to-slab check.

  In (1c) and (1d), (1b) enters as the named premise `NoCollisionOn`. All use only the standard axioms.
- **Evaluated:** all 50 cells (AUDIT-HD11964-ROT-1 C2, R1), which fixed the per-slab strips.
- **Not needed under DESIGN A**, so not proved: (2b)–(2e). See *Part 2*.
- **Left to the layer:**
  - (1b), discharged by its enclosure of `d²`;
  - `T₁` and `T₂`, as masks of its per-mode majorants. These supersede the anisotropic-strip estimate of `T₂`,
    which needed `r_G`.

## (1) Scope: what has to be holomorphic

- **Only the mutual distance needs a branch.** On the chart domain,
  `liftChartHam = hProd + μ fMov(Ψ)` (`lpChart_hamiltonian`), so `P = μ fMov(Ψ)` with
  `fMov = |p_c + p_b|²/2 − ν_c ν_b/|q_c − q_b|`. Its continuation to complex angles is
  `P_C = μ((p_c + p_b)·(p_c + p_b)/2 − ν_c ν_b (d²)^{−1/2})`, with bilinear (not Hermitian) squares and
  `d² = (q_c − q_b)·(q_c − q_b)`. It is holomorphic where:
  - **(K)** the chart is holomorphic: the complex Kepler equation `F − v₀ sin F + v₁ cos F = λ` has a holomorphic
    solution. The core's `KAM.Kepler.KeplerData` / `keplerSol y₀` gives it under two inequalities:
    `|Im λ| + (|Re v₀| + |Re v₁|) sinh y₀ + (|Im v₀| + |Im v₁|) cosh y₀ < y₀` and `(|v₀| + |v₁|) cosh y₀ ≤ κ < 1`;
  - **(R)** the radicand `(1 − Γ/(2Λ))/Λ` has `Re > 0`; it is about 15 here;
  - **(D)** `Re d² > 0`. Then `(d²)^{−1/2}` is the principal branch, holomorphic and nonzero.
- **No collision with the star is possible.** Bilinearly, `q_j·q_j = a_j²(1 − v·c)²` holds for complex angles too
  (`k² + v·v = 1` and `c·c = 1`), and `|v·c| ≤ κ < 1`. Only the mutual distance can vanish.
- **LP's `poincareC` does not reach this domain.** It is holomorphic on `poincareNbhd`: `|Im λ| < 1/4` and
  `‖ξ‖, ‖η‖ < √Λ/16`, i.e. `e ≲ 0.06`. Here `e_c ≤ 0.65` and `|Im λ_b|` reaches `0.94`. Hence `planetChartC`:
  LP's formula with `keplerSol y₀` and a chosen strip `y₀`.

**The margins** (`scripts/holo_margin.py` on the plan's cells, and `scripts/holo_domain.py` on R(1/500); estimated,
floating point, sampled).
- `Re d²` is pluriharmonic in the angles, so its minimum over the strip is attained at `Im λ_j = ±2πρ_j`; that is
  where it is sampled.
- On the cells: 3⁶ cell points × 48² real angle pairs × 4 imaginary signs.

| domain | strip `(ρ_c, ρ_b)` | Kepler `c`: best slack (κ ≤ 0.95) | Kepler `b` | min `Re d²` |
|---|---|---:|---:|---:|
| cells, real slow variables | (0.03, 0.15) | 0.026 (cell 49, `e_c` 0.66) | ≥ 0.54 | 3.32 |
| cells, real slow variables | **(0.025, 0.15)** | **0.057** | ≥ 0.54 | **3.40** |
| cells, complex polydisc `‖u‖ ≤ 1` | (0.03, 0.15) | −0.020 (fails) | ≥ 0.10 | 2.63 |
| cells, complex polydisc `‖u‖ ≤ 1` | (0.025, 0.15) | 0.011 | ≥ 0.10 | 2.72 |
| R(1/500), `|η_c| ≤ 1/500` | (0.025, 0.15) | — | — | **3.30** |
| R(1/500), `|η_c| ≤ 1/500` | (0.025, 0.10) | — | — | 4.95 |
| ℓ¹ eccentricities `≤ (0.68, 0.17)`, any orientation, no AMD budget | (0.025, 0.15) | — | — | 0.19 |

**Reading.**
- **The strip.** *(Superseded by the all-cells evaluation below: the strip is chosen per slab.)* I use
  `ρ = (0.025, 0.15)` rather than `(0.03, 0.15)`.
  - At `ρ_c = 0.03` the Kepler slack for planet `c` on the worst cell is 0.026; that is not comfortable.
  - At 0.025 it is 0.057.
  - The tails stay inside the budget at `(0.025, 0.15)`: HD11964-ROT measured `T_c ≤ 1.5e-7` and `T_b ≤ 1.6e-9`.
- **The domain.** The claimed real domain is `R(1/500)` with planet `c` rotation-reduced (`|η_c| ≤ 1/500`):
  - that is where the tails are consumed (the representatives);
  - the AMD budget `Γ_c + Γ_b ≤ 0.014` keeps `e_c` and `e_b` from being large together.

  Without the budget, the margin collapses to 0.19 (last row).
- **(D) is comfortable numerically: `min Re d² ≈ 3.3`, against `a_b² ≈ 10`.**
- **(D) is not comfortable with an elementary proof chain.**
  - The chain `Re d² ≥ Re(q_b·q_b) − |q_c·q_c| − 2‖q_c‖‖q_b‖`, with `y₀`-based bounds
    (`‖c‖ ≤ √cosh 2y₀`, `|v·c| ≤ ē cosh y₀`), fails by a factor of about 2. With the sampled sup norms in place of
    the bounds it gives ≥ 1.76.
  - The polar form (`q_c·q_b = r_c r_b cos(φ_c − φ_b)`) is worse.
  - The real margin comes from correlations the chain cannot see.
- **The complex polydisc in the cell variables is not comfortable** (Kepler slack ≤ 0.011, or negative). The tail
  theorems use the extension only at real slow variables, so the claim is made there. Cauchy estimates in the cell
  variables, which the layer needs, would use a thin complex neighbourhood of the real cell, not the unit polydisc.

**Recommendation for (D).**
- Certify `Re d² > 0` from the layer's certified model of `d²`: the enclosure `|d² − D| ≤ r_D` with `Re D − r_D > 0` on
  `stripA ρ` × the cell. This is the same data as its `sqrt`/`inv` witness of the pair potential.
- Lean then gets (1b) by a two-line lemma, and proves (1a) and (1c) analytically, with (1b) as a distinctly named
  premise.
- An analytic proof of (1b) would need a sharper argument than any I have found, or an interval subdivision in the
  kernel. It is not proposed.

**Constants** (all with margin):
- planet `c`, `y₀ = 4/5`, `ē_c = 0.68` (0.69 in the Lean, see *Deviations*): invariance `0.157 + 0.68 sinh 0.8 = 0.761 < 0.8`, and
  `0.68 cosh 0.8 = 0.909 ≤ κ_c = 0.95`;
- planet `b`, `y₀ = 13/10`, `ē_b = 0.18`: `0.942 + 0.18 sinh 1.3 = 1.248 < 1.3`, and `0.18 cosh 1.3 = 0.355 ≤ 0.5`.

## (2) Scope: the tail of `T₃ = {D_i r₁, χ₁}`

- **The coordinate formula** (`pb_eq_sum`) gives `|T₃| ≤ Σ_k |∂_{x_k} D_i r₁| |∂_{y_k} χ₁| + |∂_{y_k} D_i r₁| |∂_{x_k} χ₁|`.
- **Every first derivative of the tail is a tail.**
  - For an angle direction, `∂_{λ_j} Π_S = Π_S ∂_{λ_j}`, since `(∂_{λ_j} Q)^_k = i k_j Q̂_k` by integration by parts on
    the slice.
  - For a slow direction, differentiation under the integral sign.
  - With the symmetry of second derivatives, `D_v D_i (Q − Π_S Q) = D_i (D_v Q − Π_S D_v Q)`.
- **The bound.** `abs_dirDeriv_sub_projS_le_of_coeff` (HD11964-ROT) applies to `Q' = D_v P`, with coefficient bounds
  for `D_v P`. The layer gets them from the derivative of its model of `P`: exact on the polynomial part, Cauchy for
  the remainder. The isotropic or anisotropic cell forms supply them as before.
- **`χ₁`'s derivatives** are bounded by the generator's enclosure (2b of HD11964-ROT) and Cauchy. They are
  hypotheses `B_v` here.

## The all-cells evaluation (AUDIT-HD11964-ROT-1, C2 and R1)

**Setup.** `scripts/radius2a.py` ran on every cell of the fitted plan (`validation/cover2-plan-k0.2-d2e-3.json`):
- arguments `--FB=120 --PREC=160 --N1=384 --N2=64 --rho=0.01,0.02`, so `N1 = 384` as R1 requires;
- serially, one process at a time under `MemoryMax=8G`: about 130 s and 7.3–7.6 GB peak RSS per cell;
- the records are in `~/kam-data/hd11964/radius/allcells/radius2a-cK.json`, `K = 0..49`, with `times.log`.

Every cell's final run exited 0. Cells 2–49 of the first launch failed in the systemd outage (see *Infrastructure*)
and were re-run.

The Kepler slack of planet `c` per cell comes from `scripts/holo_margin.py` at `ρ_c ∈ {0.02, 0.025, 0.03, 0.035}` with
`ρ_b = 0.15` and `κ ≤ 0.95`.

**The strip per cell.** `scripts/allcells_summary.py --rhob=0.15` takes the strips with Kepler slack ≥ 0.04 and picks
the one minimising `max(T_c, T_b)`. The summary is `validation/allcells-summary.json`. All numbers are estimated: floating
point, a sampled cell, `σ = 0.98ρ`.

| slab (cells) | `ξ_c ≤` | strip `(ρ_c, ρ_b)` | Kepler `c` slack (min) | min `Re d²` | worst `T₁ = (T_c, T_b)` | % of `2.73e-7` | (2b) radius, real / `ρ' = 0.005` |
|---|---|---|---:|---:|---|---:|---|
| 0 (0–15) | 0.06 | (0.035, 0.15) | 0.84 | 2.81 | (6.5e-10, 3.8e-11), cell 5 | 0.2 | 7.0 % / 8.8 % |
| 1 (16–26) | 0.0816 | (0.035, 0.15) | 0.56 | 2.89 | (4.9e-10, 2.8e-11), cell 22 | 0.2 | 1.4 % / 1.7 % |
| 2 (27–35) | 0.1030 | (0.035, 0.15) | 0.36 | 2.95 | (5.8e-10, 3.4e-11), cell 30 | 0.2 | 1.9 % / 2.4 % |
| 3 (36–41) | 0.1237 | (0.035, 0.15) | 0.21 | 2.95 | (1.0e-9, 6.0e-11), cell 39 | 0.4 | 3.0 % / 3.8 % |
| 4 (42–45) | 0.1431 | (0.035, 0.15) | 0.10 | 3.12 | (2.3e-9, 1.3e-10), cell 44 | 0.8 | 5.0 % / 6.2 % |
| 5 (46–48) | 0.1611 | (0.03, 0.15) | 0.050 | 3.85 | (6.1e-8, 9.1e-10), cell 47 | 22 | 8.9 % / 11.1 % (cell 47) |
| 6 (49) | 0.1673 | (0.025, 0.15) | 0.057 | 5.04 | (1.48e-7, 1.7e-9), cell 49 | 54 | 3.7 % / 4.5 % |

**Reading.**
- **The worst `T₁` is cell 49**: `T_c ≤ 1.48e-7` at `(0.025, 0.15)`, 54 % of the bracket budget `η < 2.73e-7`. That
  leaves `1.25e-7` for `T₂–T₅`.
  - Freeing `ρ_b` gives `(0.025, 0.10)` with `T_c = 1.38e-7`, but `T_b = 2.8e-8`.
  - `(0.03, 0.15)` gives `1.37e-7`, but its Kepler slack, 0.026, is not admissible.
- **The audit's cell 46 is not the worst (2b) radius.** Cell 47 is: 8.9 % at real `θ` and 11.1 % at `ρ' = 0.005`.
  Cells 46 and 48 are 7.9 % and 10.0 %.
- **A uniform strip does not fit the budget.** At `(0.025, 0.15)` cell 47 gives `T_c = 2.70e-7`, 99 % of the budget.
  The strips must be per slab, and the Lean (1a) is proved on exactly these strips (`HD11964.HoloSlab`):
  - slabs 0–4, `|ξ_c| ≤ 0.1431`: `keplerData_HD_A`, `ρ = (7/200, 3/20)`;
  - slab 5, `|ξ_c| ≤ 0.1612`: `keplerData_HD_B`, `ρ = (3/100, 3/20)`;
  - slab 6 (all of `holoDomHD`): `keplerData_HD`, `ρ = (1/40, 3/20)`.

  The slab bounds are the plan's slab ends: every cell of slab `s` has `ξ_c ≤ hi_s`, since `c + h = hi_s` for the
  `ξ_c` coordinate in the plan's data.
- **`T₂` is not estimated.** It needs a model radius `r_G` for `G₂` (the analogue of `r_P`), which nothing computes
  yet. Degree and strip are therefore fixed for `T₁` only. The audit asked that `T₂` be included before fixing them, so
  this remains open.

## Proved (Lean)

**`applications/hd11964/HD11964/Holo.lean`** (`bd81f7d7a`, 290 lines). Definitions as in the draft below:
`planetChartC`, `chartQPC`, `distSqC`, `chartPertC`, `rhoHolo`, `yHolo`, `kappaHolo`, `eBar`, `holoDomHD`.

| theorem | content |
|---|---|
| `eccL1_le_eBar` | on `holoDomHD`, `β_j(\|ξ_j\| + \|η_j\|) ≤ ē_j`, `ē = (0.69, 0.18)` |
| `keplerData_HD` | **(1a)**: `KeplerData {\|Im λ\| < 2πρ_j}` (`ρ = (1/40, 3/20)`, `y = (4/5, 13/10)`, `κ = (19/20, 1/2)`) for both planets on `holoDomHD` |
| `noCollision_of_enclosure` | **(1b) from the layer's enclosure**: `‖d² − D‖ ≤ r < Re D` on `stripA rhoHolo` ⇒ `0 < Re d²` there |
| `abs_pb_le` | **(2a)**: `\|{a, b}\| ≤ Σ_k \|∂_{x_k}a\|\|∂_{y_k}b\| + \|∂_{y_k}a\|\|∂_{x_k}b\|` |

Supporting lemmas: `lpGamma_le_chartAMD`, `eccL1_le_of_sq`, and rational bounds on `exp`, `sinh` and `cosh` at
`±4/5` and `13/10`.

**`applications/hd11964/HD11964/HoloSlab.lean`** (this commit, 204 lines):

| theorem | content |
|---|---|
| `eccC_le_of_xi` | planet `c` on `\|ξ\| ≤ X`, `\|η\| ≤ 1/500`, `Λ ≥ Λ₀`: `β(\|ξ\| + \|η\|) ≤ E` if `G = (X² + 1/500²)/2 ≤ Λ₀` and `E²Λ² − (2G + 2X/500)Λ + G²` is `≥ 0` with nonnegative slope at `Λ₀` |
| `keplerData_of_ecc` | `KeplerData` from `β(\|ξ\| + \|η\|) ≤ E`, `2πρ + E sinh y < y`, `E cosh y ≤ κ < 1` |
| `keplerData_HD_A` | **(1a), slabs 0–4**: `w ∈ holoDomHD`, `\|ξ_c\| ≤ 0.1431` ⇒ `KeplerData` on `ρ = (7/200, 3/20)`, `y = (1, 13/10)`, `κ = (23/25, 1/2)`; `ē_c = 0.59` |
| `keplerData_HD_B` | **(1a), slab 5**: `\|ξ_c\| ≤ 0.1612` ⇒ `KeplerData` on `ρ = (3/100, 3/20)`, `y = (9/10, 13/10)`, `κ = (47/50, 1/2)`; `ē_c = 0.65` |

Margins of the per-slab constants (with `π < 3.15`):
- slabs 0–4: `0.2205 + 0.59 · 1.17525 = 0.914 < 1`, and `0.59 · 1.5433 = 0.911 ≤ 0.92`;
- slab 5: `0.189 + 0.65 · 1.0266 = 0.856 < 0.9`, and `0.65 · 1.43325 = 0.932 ≤ 0.94`.

Planet `b` reuses `keplerData_HD 1`.

The root `applications/hd11964/HD11964.lean` imports both modules (docstring paragraph extended).

**Checks.**
- `lake build HD11964.HoloSlab`: built (4.5 s), with no warnings in the new module.
- `lake env lean HD11964.lean` (root): exit 0.
- `lake build HD11964.Holo`: 11.4 s at 4.0 GB, earlier.
- All builds ran under `systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 nice -n 5`.
- `scripts/lint_sources.sh`:
  - passes the line-length check, `check_lean_modules` (4477 files), the 25 unit tests and the frozen-anchor guard;
  - its ABI step fails because this worktree's build lacks `KAM/Frozen/Magnetic/Defs/MagAlpha.olean`. That gap is
    pre-existing and unrelated to these files.
- Scratch check files, `lake env lean`, exit 0:
  - `HoloCheck.lean` derives the drafted `KeplerDataHD` (1a) and `AbsPbLe` (2a) Props from the theorems;
  - `HoloSlabCheck.lean` prints the axioms.
- `#print axioms`: `keplerData_HD`, `noCollision_of_enclosure`, `abs_pb_le`, `keplerData_HD_A`,
  `keplerData_HD_B`, `eccC_le_of_xi` and `keplerData_of_ecc` all depend only on
  `[propext, Classical.choice, Quot.sound]`.

## Infrastructure

- From about 11:26 UTC the systemd user manager was down: no login session and no linger, so `/run/user/1004`
  vanished.
- Every capped `systemd-run --user` failed. The first all-cells launch lost cells 2–49 (rc 143, then 1), and the
  `holo_margin.py` runs at `ρ_c = 0.03` and `0.035` failed.
- Nothing ran uncapped.
- After the orchestrator enabled linger, the failed work was re-run: the all-cells driver skips finished cells, and
  both `holo_margin.py` runs were repeated (rc 0).

## Deviations and errata

- **`eBar_c = 0.69`, not the draft's 0.68.** The polynomial proof of `eccL1_le_eBar` at `Λ_c ≥ 0.0563` needs it. The
  sampled maximum is `A ≤ 0.668` (cell 49).
  - This is used only inside the proof of (1a); no statement changes.
  - Margins at 0.69: `0.157 + 0.69 · 0.8882 = 0.770 < 0.8`, and `0.69 · 1.3376 = 0.923 ≤ 0.95`.
- **The strips of (1a) are per slab** (`HoloSlab`), not the draft's single `rhoHolo`.
  - The draft statement `KeplerDataHD` (uniform `(1/40, 3/20)`) still holds and is proved.
  - The per-slab theorems are additions.
  - The drafted (1b) and (1c) are stated over `stripA rhoHolo`. They need per-slab versions with `rhoHoloA` and
    `rhoHoloB` (same shape, different `ρ` and `y`).
- **The audit's C2 reading is refined.** It named cell 46 for the (2b) radius; the worst is cell 47 (8.9 % / 11.1 %).
  Its `T_c` at `(0.025, 0.15)`, 2.5e-7, is reproduced on cell 46 (2.55e-7); cell 47 is 2.70e-7.
- **My own defect in ROT-FIX (`3b50ee2b4`):** its C1 docstring edit left `TailSum.lean:23` at 105 characters, over the
  100-character limit, and the linter flags it. This commit rewraps the bullet; the change is docstring only. The
  audited and committed history is not rewritten.
- No suspected errata in pinned sources.

## Open

- **(1b), no complex collision**, analytically: not proposed. It should come from the layer's certified enclosure of
  `d²` on `stripA ρ(slab)` × cell, through `noCollision_of_enclosure`. That lemma is stated for `rhoHolo`, so the
  per-slab copy is a one-line generalisation.
- **(1c), `ChartPertExtHD`**: holomorphic, periodic and equal to `chartPert` at real points.
  - Holomorphy: `keplerSol_differentiableOn` from (1a), the principal power from (1b), and the radicand
    (`Re > 0`, about 15).
  - Periodicity: uniqueness of `keplerSol` in the strip under `λ ↦ λ + 2π`.
  - The real points: `keplerSol y₀ = keplerLongC` on the real line, both being the unique real solution.
- **(1d), `G2ExtHD`**: the existence of `G_C` from (1c) and the generator's construction.
- **(2b)–(2e)**: the derivative/tail commutations and the `T₃` bound, as drafted.
- **`T₂`'s estimate** needs `r_G`.
- **The cell-to-slab glue**: a cell of slab `s` lies in `|ξ_c| ≤ hi_s`. This is decidable from the plan's data, and
  the consumer needs it to pick `keplerData_HD_A`/`_B` per cell.

## Part 2 (2 November, after DESIGN A): statements of (1c), (1d) and the cell-to-slab check

The orchestrator relayed Scott's approval of DESIGN A for the kernel side (kamx-hd-layer, branch `hd-layer`:
`HD-LAYER-PIECES.md` §"Scope: derivative models without Cauchy", `HD-LAYER-interface.md` §6). Each model carries a
per-mode remainder majorant `ρ_k`:
- angle derivatives are `|k_i| ρ_k` ramps;
- `(1 − Π_S)` is an exact mask;
- slow derivatives use per-mode Cauchy in `u`;
- the Kepler fixed point is solved in the majorant cone.

Priorities: (1c) and (1d) on the per-slab strips, with (1b) as a named premise; the cell-to-slab check; the T₃ tail
lemmas re-assessed against the design.

**What DESIGN A needs from this side.**
- **Holomorphy at points, in all complex variables.** The layer's `hR` (`TFPin.dLam_of_rem`, `TFPin.dU_of_remZ`)
  needs `f − poly` holomorphic on a neighbourhood of `T_ρ × D(1)`, with complex angles **and complex cell variables**.
  A θ-only extension at real slow variables does not discharge it. So (1c) is stated pointwise in
  `x = (θ, Λ, ξ, η) ∈ ℂ⁸` (`PertAnalyticAt`), under conditions that are all strict and hence open:
  - the chart conditions `ChartOkAt` (Kepler invariance and contraction, radicand in the slit plane, `Λ ≠ 0`,
    `1 + k ≠ 0`);
  - `Re d² > 0`.

  Analyticity at every point of the compact `T_ρ × D(1)` (modulo periodicity) gives it on a neighbourhood. The layer
  discharges `Re d² > 0` from its enclosure of `d²`, and `ChartOkAt` from its `v` models; the margins at its strip are
  measured below.
- **The link from real to complex derivatives** (`PertDerivReal`, (1d-P)). The layer differentiates the complex
  function (`dTh`, `dU`), while the bracket and the bridge differentiate the real `P`. The two agree at real points.
  This replaces the coefficient-commutation lemmas.
- **The per-slab strip extension** (`ChartPertExt`, `G2Ext`, the drafted form) remains the source of decay for the
  modes beyond the layer's window (the scalar tail `τ`): `|P̂_k| ≤ M e^{−2π(ρ_c|k_c| + ρ_b|k_b|)}`, with `M` from
  `Re d²`'s lower bound. It is also the hypothesis set of the anisotropic route (`tails_HD_of_cell_aniso`), which
  DESIGN A's masks supersede for the in-window modes.

**(2b)–(2e) under DESIGN A: not needed; not proved.**
- `T₃ = {D_i r₁, χ₁}` is one of the five bracket terms (`a₃`) that the layer computes from its models:
  - `r₁ = (1 − Π_S) P` is already proved (`residual₁_tail`);
  - its model is the masked model of `P`, `D_i` is the ramp, the slow derivatives are `u`-shifts with per-mode Cauchy;
  - the bracket is a product of models.
- The coefficient-form lemmas would only bound `T₃` from Fourier coefficients of `D_v P`. Their role is taken by:
  - (2b), (2c) `SlowDerivComm`/`AngleDerivComm` → `PertDerivReal` plus the layer's `dU`/`dLam` on the complex
    function;
  - (2d) `TailDerivComm` → masks commute with ramps on models (layer side);
  - (2e) `T3TailBound` → `a₃` from the models.
- (2a) `abs_pb_le` is proved and harmless, but unused by DESIGN A.
- **Caveat:** the layer's `Major.lean` (the majorant link to the real-torus coefficients) is not built yet. If it
  ends up stated on the real function's coefficients instead of on the complex function, (2b) and (2c) would be
  needed after all. I will check its statement when it lands.

**Statements** (type-checked as `Prop`s, scratch `ExtDraft.lean`, `lake env lean` exit 0; the proofs go in
`HD11964/HoloExt.lean`):

```lean
/-! ## Fully complex chart variables -/

/-- The complex chart variables `x = (θ, Λ, ξ, η)` (`λ = 2πθ`, planet `c` = index `0`). -/
abbrev CVar : Type := (Fin 2 → ℂ) × (Fin 2 → ℂ) × (Fin 2 → ℂ) × (Fin 2 → ℂ)

/-- Planet `j`'s complexified chart at the complex point `x`. -/
def qpCC (y : Fin 2 → ℝ) (x : CVar) (j : Fin 2) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  planetChartC (y j) (nu j) (2 * π * x.1 j) (x.2.1 j) (x.2.2.1 j) (x.2.2.2 j)

/-- The complexified mutual distance squared at `x` (bilinear). -/
def distSqCC (y : Fin 2 → ℝ) (x : CVar) : ℂ :=
  ((qpCC y x 0).1 0 - (qpCC y x 1).1 0) ^ 2 + ((qpCC y x 0).1 1 - (qpCC y x 1).1 1) ^ 2

/-- **The fully complexified perturbation** `P_C(θ, Λ, ξ, η)`. -/
def pertCC (y : Fin 2 → ℝ) (x : CVar) : ℂ :=
  (mu : ℂ) * ((((qpCC y x 0).2 0 + (qpCC y x 1).2 0) ^ 2 +
    ((qpCC y x 0).2 1 + (qpCC y x 1).2 1) ^ 2) / 2 -
    (nu 0 : ℂ) * (nu 1 : ℂ) * distSqCC y x ^ (-(1 / 2 : ℂ)))

/-- The real chart state `w` with complex angles `θ`. -/
def realVar (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) : CVar :=
  (θ, fun j => (fast w.2 j : ℂ), fun j => (slow w.1 j : ℂ), fun j => (slow w.2 j : ℂ))

/-- The embedding of real chart states (`θ = λ/2π`). -/
def cEmb (z : Phase (2 + 2)) : CVar := realVar z fun j => ((fast z.1 j / (2 * π) : ℝ) : ℂ)

/-- The complex direction of a real chart direction (`ℝ`-linear part of `cEmb`). -/
def cDir (v : Phase (2 + 2)) : CVar := cEmb v

/-- The radicand `(1 - Γ/(2Λ))/Λ`. -/
def radC (Λ ξ η : ℂ) : ℂ := (1 - (ξ ^ 2 + η ^ 2) / 2 / (2 * Λ)) / Λ

/-- The eccentricity vector `v = radC^{1/2} (ξ, η)` (principal branch). -/
def eccC (Λ ξ η : ℂ) : Fin 2 → ℂ := radC Λ ξ η ^ (1 / 2 : ℂ) • ![ξ, η]

/-- **One planet's chart conditions at a complex point** (all strict, hence open): `Λ ≠ 0`, the
radicand in the slit plane, `1 + k ≠ 0`, and the Kepler invariance and contraction (`< 1`). -/
structure PlanetOk (y₀ : ℝ) (lam Λ ξ η : ℂ) : Prop where
  ne_zero : Λ ≠ 0
  rad_mem : radC Λ ξ η ∈ Complex.slitPlane
  one_add_k : 1 + (1 - (ξ ^ 2 + η ^ 2) / 2 / Λ) ≠ 0
  y_pos : 0 < y₀
  invariant : |lam.im| + (|(eccC Λ ξ η 0).re| + |(eccC Λ ξ η 1).re|) * Real.sinh y₀ +
      (|(eccC Λ ξ η 0).im| + |(eccC Λ ξ η 1).im|) * Real.cosh y₀ < y₀
  contraction : (‖eccC Λ ξ η 0‖ + ‖eccC Λ ξ η 1‖) * Real.cosh y₀ < 1

/-- Both planets' chart conditions at `x`. -/
def ChartOkAt (y : Fin 2 → ℝ) (x : CVar) : Prop :=
  ∀ j, PlanetOk (y j) (2 * π * x.1 j) (x.2.1 j) (x.2.2.1 j) (x.2.2.2 j)

/-! ## (1c) Statements -/

/-- (1c-i) **Holomorphy at a point** (the form a layer hypothesis `hR` consumes: analyticity at
every point of `T_ρ × D(1)` gives it on a neighbourhood). -/
def PertAnalyticAt : Prop :=
  ∀ (y : Fin 2 → ℝ) (x : CVar), ChartOkAt y x → 0 < (distSqCC y x).re →
    AnalyticAt ℂ (pertCC y) x

/-- (1c-ii) **Periodicity** in each angle. -/
def PertPeriodic : Prop :=
  ∀ (y : Fin 2 → ℝ) (x : CVar), ChartOkAt y x → ∀ j : Fin 2,
    pertCC y (x.1 + Pi.single j 1, x.2) = pertCC y x

/-- (1c-iii) **Agreement at real points**. -/
def PertReal : Prop :=
  ∀ (y : Fin 2 → ℝ) (w : Phase (2 + 2)) (t : Fin 2 → ℝ), w ∈ poincareProdDom 2 →
    ChartOkAt y (realVar w fun j => (t j : ℂ)) →
    pertCC y (realVar w fun j => (t j : ℂ)) = (chartPert nu mu (withAngles w fun j => 2 * π * t j) : ℂ)

/-- (1b) as a named premise: no complex collision on the strip `ρ` at the real state `w`. -/
def NoCollisionOn (y ρ : Fin 2 → ℝ) (w : Phase (2 + 2)) : Prop :=
  ∀ θ ∈ stripA ρ, 0 < (distSqC y w θ).re

/-- (1c) **on a strip**, in the drafted form (one instance per slab: `rhoHolo`/`yHolo`,
`rhoHoloA`/`yHoloA` with `|ξ_c| ≤ 0.1431`, `rhoHoloB`/`yHoloB` with `|ξ_c| ≤ 0.1612`). -/
def ChartPertExt (y ρ : Fin 2 → ℝ) (w : Phase (2 + 2)) : Prop :=
  DifferentiableOn ℂ (chartPertC y w) (stripA ρ) ∧
    (∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ →
      chartPertC y w (θ + Pi.single j 1) = chartPertC y w θ) ∧
    ∀ t : Fin 2 → ℝ,
      chartPertC y w (fun j => (t j : ℂ)) = (chartPert nu mu (withAngles w fun j => 2 * π * t j) : ℂ)

def ChartPertExtSlabs : Prop :=
  (∀ w ∈ holoDomHD, NoCollisionOn yHolo rhoHolo w → ChartPertExt yHolo rhoHolo w) ∧
  (∀ w ∈ holoDomHD, |slow w.1 0| ≤ 1431 / 10000 → NoCollisionOn yHoloA rhoHoloA w →
    ChartPertExt yHoloA rhoHoloA w) ∧
  (∀ w ∈ holoDomHD, |slow w.1 0| ≤ 1612 / 10000 → NoCollisionOn yHoloB rhoHoloB w →
    ChartPertExt yHoloB rhoHoloB w)

/-! ## (1d) Statements -/

/-- (1d-P) **The first derivatives of `P` extend**: at a real state where the conditions hold,
the real derivative of `P` in a chart direction `v` is the complex derivative of `P_C` in `cDir v`. -/
def PertDerivReal : Prop :=
  ∀ (y : Fin 2 → ℝ) (z : Phase (2 + 2)), z ∈ poincareProdDom 2 → ChartOkAt y (cEmb z) →
    0 < (distSqCC y (cEmb z)).re → ∀ v : Phase (2 + 2),
      (fderiv ℝ (chartPert nu mu) z v : ℂ) = fderiv ℂ (pertCC y) (cEmb z) (cDir v)

/-- (1d) **The complex extension of `G₂`** on a strip (one instance per slab, as in (1c)). -/
def G2Ext (ρ : Fin 2 → ℝ) (w : Phase (2 + 2)) : Prop :=
  ∃ Gc : (Fin 2 → ℂ) → ℂ,
    DifferentiableOn ℂ Gc (stripA ρ) ∧
    (∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ → Gc (θ + Pi.single j 1) = Gc θ) ∧
    ∀ t : Fin 2 → ℝ, Gc (fun j => (t j : ℂ)) = (G2HD (withAngles w fun j => 2 * π * t j) : ℂ)

def G2ExtSlabs : Prop :=
  (∀ w ∈ holoDomHD, NoCollisionOn yHolo rhoHolo w → G2Ext rhoHolo w) ∧
  (∀ w ∈ holoDomHD, |slow w.1 0| ≤ 1431 / 10000 → NoCollisionOn yHoloA rhoHoloA w →
    G2Ext rhoHoloA w) ∧
  (∀ w ∈ holoDomHD, |slow w.1 0| ≤ 1612 / 10000 → NoCollisionOn yHoloB rhoHoloB w →
    G2Ext rhoHoloB w)

/-! ## The cell-to-slab check -/

/-- The cells of one slab. -/
def Slab.cells (s : Slab) : List AffineCell := s.disc.toList ++ (s.upper ++ s.lower).map (·.cell)

/-- Decidable: every cell of the slab has `|c₂| + |h₂| ≤ X` (`ξ_c`). -/
def Slab.xiOk (s : Slab) (X : ℚ) : Bool := s.cells.all fun k => |k.c 2| + |k.h 2| ≤ X

/-- **The cell-to-slab statement**: every cell of slabs 0–4 of `fitPlan` lies in
`|ξ_c| ≤ 0.1431`, every cell of slab 5 in `|ξ_c| ≤ 0.1612`. -/
def FitPlanSlabsXi : Prop :=
  (∀ s ∈ fitPlan.slabs.take 5, ∀ k ∈ s.cells, ∀ w ∈ k.toSet, |slow w.1 0| ≤ 1431 / 10000) ∧
  (∀ s ∈ (fitPlan.slabs.drop 5).take 1, ∀ k ∈ s.cells, ∀ w ∈ k.toSet,
    |slow w.1 0| ≤ 1612 / 10000)
```

## Part 2 results (proved)

**`applications/hd11964/HD11964/HoloExt.lean`** (631 lines):

| theorem | content |
|---|---|
| `keplerSol_analyticAt` | the strip solution of Kepler's equation is analytic at any point where the invariance and contraction hold strictly (generic analytic coefficients on a complete space) |
| `planetChartC_analyticAt` | one planet's complexified chart is analytic at a point with `PlanetOk` |
| `pertCC_analyticAt` | **(1c-i)** `P_C` is analytic at every `x ∈ ℂ⁸` with `ChartOkAt y x` and `0 < Re d²(x)` |
| `pertCC_add_single` | **(1c-ii)** `P_C(θ + e_j, ·) = P_C(θ, ·)` where `ChartOkAt` holds (`keplerSol_shift`) |
| `planetChartC_ofReal`, `pertCC_realVar_ofReal` | **(1c-iii)** at real points, the chart is LP's `poincare m 1`: the strip solution is `keplerLong`, by uniqueness. `P_C` is `chartPert = μ fMov(Ψ)` (`lpChart_hamiltonian`, `fMov_two`) |
| `chartOkAt_of_keplerData` | the chart conditions on `stripA ρ` at a real state, from (1a) |
| `chartPertExt_of`, `chartPertExt_HD` / `_A` / `_B` | **(1c) in the drafted form** on `rhoHolo`, `rhoHoloA` (`\|ξ_c\| ≤ 0.1431`) and `rhoHoloB` (`\|ξ_c\| ≤ 0.1612`), with the premise `NoCollisionOn y ρ w` |
| `Slab.cells`, `Slab.xiOk`, `fitPlan_xiOk`, `fitPlan_slabs_xi` | **the cell-to-slab check**: decided by `decide +kernel` on `fitPlan`. Every cell of slabs 0–4 lies in `\|ξ_c\| ≤ 0.1431`, every cell of slab 5 in `\|ξ_c\| ≤ 0.1612` |

**`applications/hd11964/HD11964/HoloG2.lean`** (401 lines):

| theorem | content |
|---|---|
| `cEmbL`, `cEmbL_apply`, `cEmbL_withAngles` | the real-linear embedding `z ↦ (λ/2π, Λ, ξ, η)` |
| `planetOk_eventually`, `chartOkAt_eventually` | the chart conditions are open |
| `fderiv_chartPert_eq` | **(1d-P)** `↑(fderiv ℝ P z v) = fderiv ℂ P_C (cEmbL z) (cEmbL v)` at a real state of the chart domain with the conditions and `Re d² > 0`. This links DESIGN A's `dTh`/`dU` on the complex function to the bracket's real derivatives |
| `trigSlice_ext` | the slices of the first derivatives of `Re Σ_{k∈S} B_k e^{ik·λ}` (angle-invariant `B_k`, differentiable at `w`) extend to entire `1`-periodic functions |
| `projS_slice_ext`, `chi1_slice_ext` | its instances `Π_S P` and `χ₁` on `openHD` |
| `dPC`, `dPC_analyticAt`, `dPC_add_single`, `dPC_ofReal` | the extension of `θ ↦ ∂_v P`: analytic, periodic, the real derivative at real `θ` |
| `G2Ext`, `g2Ext_of`, `g2Ext_HD` / `_A` / `_B` | **(1d) in the drafted form** on the three strips, with the premise `NoCollisionOn`. The extension is `Σ_k (∂_{x_k}P_C − ½T^Π)T^χ_{y_k} − (∂_{y_k}P_C − ½T^Π)T^χ_{x_k}` (`pb_eq_sum`) |

**Checks.**
- `lake build HD11964.HoloExt`: 12 s. `lake build HD11964.HoloG2`: 4.6 s.
- `lake env lean HD11964.lean` (root, which imports both): exit 0.
- All builds ran under `MemoryMax=4G`, one at a time. `HoloExt` peaks at about 3.97 GB RSS, close to the cap.
- No warnings in the new modules.
- `scripts/lint_sources.sh`:
  - line length, `check_lean_modules` (4479 files) and the frozen-anchor guard pass;
  - the ABI step fails on the worktree's missing `MagAlpha.olean`, which is pre-existing.
- Scratch `G2Check.lean` derives every drafted Prop of `ExtDraft.lean` from the theorems: `PertAnalyticAt`,
  `PertPeriodic`, `PertReal`, `ChartPertExtSlabs`, `PertDerivReal` (with `cEmbL`), `G2ExtSlabs` and
  `FitPlanSlabsXi`. Exit 0.
- `#print axioms`: all depend only on `[propext, Classical.choice, Quot.sound]`. The theorems checked are
  `pertCC_analyticAt`, `pertCC_add_single`, `pertCC_realVar_ofReal`, `chartPertExt_HD` / `_A` / `_B`,
  `fitPlan_slabs_xi`, `fderiv_chartPert_eq`, `trigSlice_ext` and `g2Ext_HD` / `_A` / `_B`.

**The layer's domain** (`holo_margin.py --rho=0.001,0.001 --complex --urad=R`; estimated, sampled). These are the
conditions of `pertCC_analyticAt` on `T_{1/1000} ×` the complex cell polydisc, so they are what the layer's `hR`
needs:

| polydisc radius | Kepler `c` slack (min, cell 46) | Kepler `b` | min `Re d²` | min `Re` radicand |
|---|---:|---:|---:|---:|
| `\|u\| ≤ 1` | 0.162 | 0.99 | 6.04 | 0.555 |
| `\|u\| ≤ R₀ = 64/49` | 0.125 | 0.80 | 5.66 | 0.555 |

They are comfortable. The layer certifies `ChartOkAt` from its `v` models and `Re d² > 0` from its enclosure, at each
point.

**Deviations from the part-2 draft.**
- `PertDerivReal` is stated with `cEmbL` (a continuous `ℝ`-linear map) in place of the draft's `cEmb`/`cDir`.
  `cEmbL_apply` shows that `cEmbL z` is the draft's `realVar z (λ/2π)`.
- `G2Ext` takes only `ρ`; the draft's `y` was unused.
- `Slab.xiOk` uses `decide (|c₂| + |h₂| ≤ X)`, as drafted.
- No suspected errata in pinned sources.

## Split of `HoloExt` (after the audit request; a pure move)

The orchestrator asked for `HoloExt` (3.97 GB maxrss) to be split into two modules, with a facade keeping the
public names.

**The split.**
- `HD11964/HoloExt/Point.lean` (319 lines): the definitions, `keplerSol_analyticAt`, (1c-i), (1c-ii). It imports
  `HoloSlab` only.
- `HD11964/HoloExt/Real.lean` (346 lines): (1c-iii), (1c) on the per-slab strips, the cell-to-slab check. It
  imports `Point` and `CoverPlan`.
- `HD11964/HoloExt.lean` is now the facade: it imports both parts and holds no code.

**It is a pure move.** A script checked that the 52 declarations, in order, and the text of the proof bodies are
identical to `86695f338`'s `HoloExt.lean`. Downstream code (`HoloG2`, the root) imports `HD11964.HoloExt`
unchanged.

**Checks.**
- `lake build HD11964.HoloG2` rebuilt through the facade: `Point` 9.3 s, `Real` 7.9 s, `HoloExt` 2.6 s, `HoloG2`
  5.6 s.
- Root: exit 0.
- `G2Check.lean` and `ExtCheck.lean` still derive every drafted Prop, with the same axioms.
- `lint_sources.sh`: line length, `check_lean_modules` (4480 files) and the frozen guard pass.

**Measured** (`lake env lean`, one at a time under `MemoryMax=4G`, two runs each). Peak `memory.current` and anon
come from polling the scope's cgroup every 50 ms. Kernel 5.15 has no `memory.peak`, and systemd 249 does not report
it.

| file | cgroup peak (GB) | anon peak (GB) | maxrss (GB) | wall (s) |
|---|---:|---:|---:|---:|
| baseline: a module importing `HoloSlab` only | 0.63–0.65 | 0.46 | 3.82 | 3.8 |
| `HoloExt` before the split (`86695f338`) | 0.76–0.80 | 0.58 | 3.98 | 14.7–15.0 |
| `HoloExt/Point` | 0.69–0.70 | 0.52 | 3.91 | 10.1–10.4 |
| baseline: `Point` + `CoverPlan` imports only | 0.63 | 0.46 | 3.82 | 3.5 |
| `HoloExt/Real` | 0.73–0.74 | 0.55 | 3.94 | 8.5–8.8 |
| `HoloExt` (facade) | 0.63–0.64 | 0.46 | 3.82 | 3.4–4.0 |

**Reading.**
- **The 3.97 GB was maxrss, not the capped charge.**
  - 3.82 GB of it is the floor of loading the imports. A module that imports `HoloSlab` and declares nothing has
    the same maxrss.
  - Most of that floor is file-backed `.olean` mappings, which are not charged to the scope: its cgroup peak is
    0.63 GB.
- **Against `MemoryMax=4G`, the old module peaked at 0.80 GB.** The parts peak at 0.70 and 0.74 GB.
- **What the split changes is the module's own share.** Above the import floor, maxrss was 0.15 GB before the split
  and is 0.08 or 0.11 GB after. The cgroup share was 0.13–0.15 GB before and is 0.06 or 0.10 GB after.
- **The maxrss figure cannot drop below 3.82 GB by splitting.** Only fewer or lighter imports would lower it.
- **I recommend gating on the cgroup charge or on anon, not on maxrss.** Under `MemoryMax=4G` it has more than 5×
  headroom.

## The statements (type-checked as `Prop`s; scratch `lake env lean`, exit 0)

The file is also at `~/kam-data/hd11964/lemmas/HoloDraft.lean`.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.TailAniso
public import KAM.Kepler.EquationComplex
public import KAM.Planetary.StrongAMD.PlanarDictionary

/-!
# DRAFT (HD11964-HOLO): statements of the complex extension of `P`, `G₂`, and of the tail of `T₃`

Statements only, as `Prop`s (type-checked, no proofs), for the handoff.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real ContDiff

namespace HD11964.Cover

/-! ## (1) Definitions -/

/-- One planet's complexified Poincaré chart (`κ = 1`) with the Kepler strip `y₀`: positions and
momenta at the complex mean longitude `lam` and slow variables `(Λ, ξ, η)`. It is LP's
`poincareC m 1` with `KAM.Kepler.keplerSol y₀` in place of `keplerLongC` (whose strip is `1`). -/
def planetChartC (y₀ m : ℝ) (lam Λ ξ η : ℂ) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  let Γ := (ξ ^ 2 + η ^ 2) / 2
  let k := 1 - Γ / Λ
  let v : Fin 2 → ℂ := ((1 - Γ / (2 * Λ)) / Λ) ^ (1 / 2 : ℂ) • ![ξ, η]
  let F := KAM.Kepler.keplerSol y₀ (v 0) (v 1) lam
  let c : Fin 2 → ℂ := ![Complex.cos F, Complex.sin F]
  let vc := v 0 * c 0 + v 1 * c 1
  ((Λ ^ 2 / ((m ^ 2 : ℝ) : ℂ)) • (k • c - v + (vc / (1 + k)) • v),
    (((m ^ 2 : ℝ) : ℂ) / (Λ * (1 - vc))) • (![-c 1, c 0] - (vc / (1 + k)) • ![-v 1, v 0]))

/-- Planet `j`'s complexified chart at the real chart state `w` with complex angles `θ = λ/2π`. -/
def chartQPC (y : Fin 2 → ℝ) (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) (j : Fin 2) :
    (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  planetChartC (y j) (nu j) (2 * π * θ j) (fast w.2 j) (slow w.1 j) (slow w.2 j)

/-- **The complexified mutual distance squared** (bilinear, not Hermitian):
`d² = (q_c - q_b)·(q_c - q_b)`. -/
def distSqC (y : Fin 2 → ℝ) (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) : ℂ :=
  ((chartQPC y w θ 0).1 0 - (chartQPC y w θ 1).1 0) ^ 2 +
    ((chartQPC y w θ 0).1 1 - (chartQPC y w θ 1).1 1) ^ 2

/-- **The complexified perturbation** `P_C = μ (|p_c + p_b|²/2 - ν_c ν_b (d²)^{-1/2})` (bilinear
squares, principal branch). -/
def chartPertC (y : Fin 2 → ℝ) (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) : ℂ :=
  (mu : ℂ) * ((((chartQPC y w θ 0).2 0 + (chartQPC y w θ 1).2 0) ^ 2 +
    ((chartQPC y w θ 0).2 1 + (chartQPC y w θ 1).2 1) ^ 2) / 2 -
    (nu 0 : ℂ) * (nu 1 : ℂ) * distSqC y w θ ^ (-(1 / 2 : ℂ)))

/-- The strip widths (`θ = λ/2π`): `ρ = (1/40, 3/20)`. -/
def rhoHolo : Fin 2 → ℝ := ![1 / 40, 3 / 20]

/-- The Kepler strips `y₀ = (4/5, 13/10)` and contraction constants `κ = (19/20, 1/2)`. -/
def yHolo : Fin 2 → ℝ := ![4 / 5, 13 / 10]

def kappaHolo : Fin 2 → ℝ := ![19 / 20, 1 / 2]

/-- The bounds on the ℓ¹ eccentricity vectors `|v₀| + |v₁|` that the proof derives on `holoDomHD`:
`ē = (0.68, 0.18)` (sampled maxima 0.665, 0.176). -/
def eBar : Fin 2 → ℝ := ![17 / 25, 9 / 50]

/-- **The real chart states of the claim**: the certificate region `R(1/500)` with planet `c`
rotation-reduced, `|η_c| ≤ 1/500` (every representative of the fitted plan's cover is in it; the
plan's cells have `|η_c| ≤ 0.002`). -/
def holoDomHD : Set (Phase (2 + 2)) := {w | w ∈ region (1 / 500) ∧ |slow w.2 0| ≤ 1 / 500}

/-! ## (1) Statements -/

/-- (1a) **The Kepler contraction on the strip** (`KAM.Kepler.KeplerData`, coefficients constant in
`λ`): for `w ∈ holoDomHD` and each planet, `|Im λ| < 2πρ_j` lies in the parameter set of a
`KeplerData` with strip `y_j` and constant `κ_j`. -/
def KeplerDataHD : Prop :=
  ∀ (j : Fin 2), ∀ w ∈ holoDomHD,
    KAM.Kepler.KeplerData {lam : ℂ | |lam.im| < 2 * π * rhoHolo j}
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.1 j : ℝ) : ℂ))
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.2 j : ℝ) : ℂ))
      (fun lam => lam) (yHolo j) (kappaHolo j)

/-- (1b) **No complex collision**: on `holoDomHD` × `stripA ρ`, `Re d² > 0` (so `(d²)^{-1/2}` is the
principal branch, holomorphic and nonzero). -/
def NoComplexCollisionHD : Prop :=
  ∀ w ∈ holoDomHD, ∀ θ ∈ stripA rhoHolo, 0 < (distSqC yHolo w θ).re

/-- (1c) **The complex extension of `P`**: at every `w ∈ holoDomHD`, `θ ↦ P_C(w, θ)` is holomorphic
and `1`-periodic on `stripA ρ`, and equals `P(withAngles w (2πt))` at real `θ = t`. -/
def ChartPertExtHD : Prop :=
  ∀ w ∈ holoDomHD,
    DifferentiableOn ℂ (chartPertC yHolo w) (stripA rhoHolo) ∧
    (∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA rhoHolo →
      chartPertC yHolo w (θ + Pi.single j 1) = chartPertC yHolo w θ) ∧
    ∀ t : Fin 2 → ℝ,
      chartPertC yHolo w (fun j => (t j : ℂ)) = (chartPert nu mu (withAngles w fun j => 2 * π * t j) : ℂ)

/-- (1d) **The complex extension of `G₂`** (existence form, what `tails_HD_of_cell_aniso` consumes
per point): the slice of `G₂ = {P - ½ Π_S P, χ₁}` at `w ∈ holoDomHD` extends holomorphically
and `1`-periodically to `stripA ρ`. -/
def G2ExtHD : Prop :=
  ∀ w ∈ holoDomHD, ∃ Gc : (Fin 2 → ℂ) → ℂ,
    DifferentiableOn ℂ Gc (stripA rhoHolo) ∧
    (∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA rhoHolo → Gc (θ + Pi.single j 1) = Gc θ) ∧
    ∀ t : Fin 2 → ℝ, Gc (fun j => (t j : ℂ)) = (G2HD (withAngles w fun j => 2 * π * t j) : ℂ)

/-! ## (2) The tail of `T₃ = {D_i r₁, χ₁}` -/

/-- (2a) **The bracket by coordinates**:
`|{a, b}| ≤ Σ_k |∂_{x_k} a| |∂_{y_k} b| + |∂_{y_k} a| |∂_{x_k} b|`. -/
def AbsPbLe : Prop :=
  ∀ (d : ℕ) (a b : Phase d → ℝ) (w : Phase d),
    |pb a b w| ≤ ∑ k, (|fderiv ℝ a w (Pi.single k 1, 0)| * |fderiv ℝ b w (0, Pi.single k 1)| +
      |fderiv ℝ a w (0, Pi.single k 1)| * |fderiv ℝ b w (Pi.single k 1, 0)|)

/-- A direction that does not move the fast angles. -/
def IsSlowDir (v : Phase (2 + 2)) : Prop := ∀ j : Fin 2, v.1 (Fin.castAdd 2 j) = 0

/-- (2b) **Slow derivatives commute with the Fourier coefficients and with `Π_S`** (differentiation
under the integral). -/
def SlowDerivComm : Prop :=
  ∀ (U : Set (Phase (2 + 2))) (Q : Phase (2 + 2) → ℝ) (S : Finset (Fin 2 → ℤ)) (v : Phase (2 + 2)),
    IsOpen U → IsAngleSaturated U → ContDiffOn ℝ ∞ Q U → IsSlowDir v → ∀ w ∈ U,
      (∀ k, chartCoeff (dirDeriv v Q) k w = fderiv ℝ (fun y => chartCoeff Q k y) w v) ∧
      dirDeriv v (projS S Q) w = projS S (dirDeriv v Q) w

/-- (2c) **Angle derivatives commute with `Π_S`**: `(∂_{λ_j} Q)^_k = i k_j Q̂_k` for `Q` periodic in
the angles, so `∂_{λ_j} Π_S Q = Π_S ∂_{λ_j} Q`. -/
def AngleDerivComm : Prop :=
  ∀ (U : Set (Phase (2 + 2))) (Q : Phase (2 + 2) → ℝ) (S : Finset (Fin 2 → ℤ)) (j : Fin 2),
    IsOpen U → IsAngleSaturated U → ContDiffOn ℝ ∞ Q U → IsAnglePeriodicOn U Q → ∀ w ∈ U,
      (∀ k, chartCoeff (dirDeriv (angleDir (Fin.castAdd 2 j)) Q) k w =
        Complex.I * (k j : ℂ) * chartCoeff Q k w) ∧
      dirDeriv (angleDir (Fin.castAdd 2 j)) (projS S Q) w =
        projS S (dirDeriv (angleDir (Fin.castAdd 2 j)) Q) w

/-- (2d) **Every first derivative of a tail is a tail**: for a slow or angle direction `v`,
`D_v D_i (Q - Π_S Q) = D_i (D_v Q - Π_S D_v Q)` at points of `U`. -/
def TailDerivComm : Prop :=
  ∀ (U : Set (Phase (2 + 2))) (Q : Phase (2 + 2) → ℝ) (S : Finset (Fin 2 → ℤ)) (i : Fin 2)
    (v : Phase (2 + 2)), IsOpen U → IsAngleSaturated U → ContDiffOn ℝ ∞ Q U →
    IsAnglePeriodicOn U Q → (IsSlowDir v ∨ ∃ j, v = angleDir (Fin.castAdd 2 j)) → ∀ w ∈ U,
      dirDeriv v (dirDeriv (angleDir (Fin.castAdd 2 i)) (fun y => Q y - projS S Q y)) w =
        dirDeriv (angleDir (Fin.castAdd 2 i)) (fun y => dirDeriv v Q y - projS S (dirDeriv v Q) y) w

/-- (2e) **The tail of `T₃` at a point**, from bounds on the Fourier coefficients of the eight
first derivatives `D_v P` (`v` the coordinate directions `(e_k, 0)`, `(0, e_k)`) and on the first
derivatives of `χ₁`: `|{D_i r₁, χ₁}(w)| ≤ Σ_k A_{(e_k,0)} B_{(0,e_k)} + A_{(0,e_k)} B_{(e_k,0)}`, with
`A_v = Σ_{T_v \ S} |κ_i| |a^v_κ| + Σ_{κ ∉ S} |κ_i| d^v_κ` (the bound of
`abs_dirDeriv_sub_projS_le_of_coeff` for `D_v P`). -/
def T3TailBound : Prop :=
  ∀ (ν : Fin 2 → ℝ) (U : Set (Phase (2 + 2))) (S : Finset (Fin 2 → ℤ)) (P : Phase (2 + 2) → ℝ)
    (i : Fin 2) (w : Phase (2 + 2)) (T : Phase (2 + 2) → Finset (Fin 2 → ℤ))
    (a : Phase (2 + 2) → (Fin 2 → ℤ) → ℂ) (d : Phase (2 + 2) → (Fin 2 → ℤ) → ℝ)
    (B : Phase (2 + 2) → ℝ),
    IsOpen U → IsAngleSaturated U → U ⊆ poincareProdDom 2 → ContDiffOn ℝ ∞ P U →
    IsAnglePeriodicOn U P → IsModeSet S (keplerFreq ν) U → w ∈ U →
    (∀ v, ∀ κ, ‖chartCoeff (dirDeriv v P) κ w - (if κ ∈ T v then a v κ else 0)‖ ≤ d v κ) →
    (∀ v, Summable fun κ : Fin 2 → ℤ => |(κ i : ℝ)| * d v κ) →
    (∀ v, |dirDeriv v (chiStar S (keplerFreq ν) P) w| ≤ B v) →
    let A : Phase (2 + 2) → ℝ := fun v =>
      ∑ κ ∈ T v \ S, |(κ i : ℝ)| * ‖a v κ‖ + ∑' κ, if κ ∈ S then 0 else |(κ i : ℝ)| * d v κ
    |pb (dirDeriv (angleDir (Fin.castAdd 2 i)) (residual₁ (hProd 1 ν) P (chiStar S (keplerFreq ν) P)))
        (chiStar S (keplerFreq ν) P) w| ≤
      ∑ k, (A (Pi.single k 1, 0) * B (0, Pi.single k 1) + A (0, Pi.single k 1) * B (Pi.single k 1, 0))

end HD11964.Cover

end
```
