# Handoff HD11964-COVER-D (phase 2: the order-2 cover at larger `d`, and the `F_b − Λ_b` range)

Worker kamx-hd11964, branch `hd11964-p2`. Task from the orchestrator (1 November 2026). The ruling is that the
80-cell cover is the reference, and its weak point is the `F_b − Λ_b` range bound (17 % slack). Two levers:
1. rerun the order-2 cover (float64) at `d = 1.5e-3` and `2e-3`, and report the margin per cell and the tolerance on
   the range bound;
2. estimate the effect of absorbing the reduced-mass kinetic oscillation of `Λ_b` into `F_b`.

Python only, no Lean. Nothing pushed.

**Status: done.**
- **Lever 1 works.** The 10³ yr margin rises from 2.33 (`d = 10⁻³`) to 3.06 (`d = 1.5e-3`) and to **4.07**
  (`d = 2e-3 = 1/500`, the largest `d` that `D.ok` allows with `r = 1/250`).
- The tolerance on the width of the `F_b − Λ_b` range bound rises from ×1.17 to ×1.53 and to **×2.04**.
- Nothing else changes:
  - the Lean statement is uniform in `D`;
  - `liftData` and `δ` do not involve `d`;
  - the region stays below the Laplace limit, by 0.003 at `d = 2e-3`;
  - the bracket terms stay negligible (`η T ≤ 1.4e-5`).
- **Lever 2 (estimate):** the range is the physical oscillation of the osculating `Λ_b`, so no `F` absorbs it. A
  reduced-mass Kepler action would cut it about 7×, but that changes frozen LP objects.
- **A third lever found on the way:** the range bound is set by the b-squares' corners, which reach far outside
  `R(d)`. At `d = 2e-3`:
  - the sampled `F_b − Λ_b` width on `R(d)` is 2.27e-4;
  - over the boxes it is 3.39e-4, and the ℓ¹ bound is 4.88e-4.
  Cells fitted to `R(d)` would give margin about 5.8 (estimate).

Commits: this handoff's commit (`cover2.py` `--d=` option and summary fields, the two new tables, the regenerated
reference summary, the in-region check script and table, the application README, the handoff).

## Lever 1: larger `d`, and what stays unchanged

- **Lean.**
  - `HD11964.noCrossing_of_regionBounds` quantifies over every `D : DriftData 2` with `D.ok = true` and
    `D.r = 1/250`. `d` enters only through `region D.d` (the bridge's `hR`, `HD11964.mem_region`) and `D.ok`,
    which asks for `2d ≤ r`.
  - So `d ≤ 1/500 = 2e-3`. `d = 1/500` is the largest `d` allowed, and is decided as `2/500 ≤ 1/250`.
  - No Lean changes are needed for any `d ≤ 1/500`.
- **`liftData`** concerns the initial set only. Its `δ = Λlo_c − Cbar = 96621/2000000 = 0.0483` and
  `r = 1/250` do not depend on `d`. The budget `3r ≤ δ/4` is unchanged. `r` is already within 1 % of its maximum
  `δ/12 = 4.03e-3`.
- **The region `R(d)`** has `Λ ∈ box ± d` and `Γ_c + Γ_b ≤ 0.010 + 2d`:

  | `d` | `Cmax` | `Λ_c` min | `Λ_c min − Cmax` | `e_c` max | below the Laplace limit 0.66274? | `ξ_c` intervals | cells (`h_b = 0.04`) |
  |---:|---:|---:|---:|---:|---|---:|---:|
  | 1e-3 | 0.012 | 0.057311 | 0.0453 | 0.6123 | yes, by 0.050 | 6 | 80 |
  | 1.5e-3 | 0.013 | 0.056811 | 0.0438 | 0.6366 | yes, by 0.026 | 6 | 88 |
  | 2e-3 | 0.014 | 0.056311 | 0.0423 | 0.6599 | yes, by 0.003 | 7 | 100 |

  - The AMD gap inside the region, `Λ_c min − Cmax`, stays ≥ 0.042, so `e_c < 1` with room.
  - At `d = 2e-3` the region reaches `e_c = 0.660`, 0.003 below the Laplace limit.
  - The cover does not expand in powers of `e` about 0. Its cells are local Taylor polynomials, so the Laplace limit
    is not a hard constraint for it. The local convergence is what matters, and it holds: the degree ratios stay
    ≤ 0.38 (table below).

## Results (float64, ℓ¹ bounds plus remainder estimates; *estimated*, not certified)

Tables:
- `applications/hd11964/validation/cover2-order2-d1.5e-3.json` (88 cells);
- `applications/hd11964/validation/cover2-order2-d2e-3.json` (100 cells);
- the reference `cover2-order2.json` (80 cells, `d = 10⁻³`). Its summary was regenerated with the new fields
  `region`, `range_width_tolerance` and `per_cell[].margin_local`; every old field is unchanged (checked).

The raw records are in `~/kam-data/hd11964/cover2/d1.5e-3.jsonl` and `d2e-3.jsonl`.

| | `d = 1e-3` (80 cells) | `d = 1.5e-3` (88) | `d = 2e-3` (100) |
|---|---:|---:|---:|
| `η_c` (max over cells) | 1.11e-9 | 1.45e-9 | 2.03e-9 (cell 98, `ξ_c = 0.1642`) |
| `η_b` | 3.86e-10 | 3.88e-10 | 5.20e-10 (cell 94) |
| `η_c T` / `η_b T` | 7.5e-6 / 2.6e-6 | 9.8e-6 / 2.6e-6 | 1.37e-5 / 3.5e-6 |
| `a₁` (Fourier tail of `S`), max (c) | 1.4e-12 | 1.2e-11 | 1.9e-10 |
| `F_c − Λ_c` ℓ¹ bound (width) | ±2.80e-5 (5.6e-5) | ±3.02e-5 (6.0e-5) | ±3.20e-5 (6.4e-5) |
| `F_b − Λ_b` ℓ¹ bound (width) | ±2.13e-4 (4.26e-4) | ±2.44e-4 (4.87e-4) | ±2.44e-4 (4.88e-4) |
| `F_b − Λ_b` sampled (width) | [−1.26e-4, 1.83e-4] (3.09e-4) | [−1.38e-4, 2.07e-4] (3.45e-4) | [−1.38e-4, 2.07e-4] (3.45e-4) |
| largest degree ratio (c / b) | 0.37 / 0.29 | 0.38 / 0.30 | 0.38 / 0.30 |
| identity check (max at the centres) | 1.4e-14 | 1.2e-14 | 2.0e-14 |
| **10³ yr margin** (ℓ¹ range bounds) | **2.33** | **3.06** | **4.07** |
| 10³ yr margin, sampled range | 3.21 | 4.32 | 5.74 |
| **tolerance on the `F_b − Λ_b` width** (margin ≥ 2, `η` fixed) | **×1.17** | **×1.53** | **×2.04** |
| tolerance on the `F_c − Λ_c` width | ×8.8 | ×12.3 | ×15.4 |
| tolerance on `η_c` / `η_b` (ranges fixed) | ×59 / ×28 | ×71 / ×100 | ×68 / ×146 |
| float64 CPU (2 processes) | 3,798 s | 4,379 s (2,203 s wall, ≤ 2.6 GB) | 5,097 s (2,563 s wall, ≤ 3.3 GB) |

Definitions:
- `margin = d / max_i (η_i T + hi_i − lo_i)`, with `T = 6741.9` units (10³ yr);
- the width tolerance is `(d/2 − η_i T) / (hi_i − lo_i)`: the factor by which the kernel's range bound may exceed
  the float64 one with the margin still ≥ 2;
- the `η` tolerance is `(d/2 − (hi_i − lo_i)) / (η_i T)`.

**Per-cell margins.** In the bridge `lo_i, hi_i` are global constants, so the margin of a cell is
`d / max_i (η_i(cell) T + hi_i − lo_i)` with the global range (`per_cell[].margin`). The JSON also gives
`margin_local`, which uses the cell's own range: it shows which cells set the global range.

| `d` | cell margin: min / median / max | local margin: min / median / max |
|---:|---|---|
| 1e-3 | 2.33 / 2.34 / 2.34 | 2.33 / 3.00 / 4.79 |
| 1.5e-3 | 3.06 / 3.07 / 3.07 | 3.07 / 4.46 / 7.13 |
| 2e-3 | 4.07 / 4.09 / 4.09 | 4.08 / 5.95 / 9.51 |

**Per `ξ_c` interval, `d = 2e-3`** (the `d = 1.5e-3` cover has the same first five intervals, up to rounding, and
one top interval `0.1524 ± 0.0089`, `e_c ≤ 0.637`, 4 cells, grid 480×64, `η_c ≤ 1.45e-9`):

| `ξ_c` centre ± half-width | `e_c` max | cells | grid (N1) | `η_c` max | `η_b` max | `a₄`, `a₅` (c) of the worst cell | degree ratio (c) | `F_b − Λ_b` bound | cell margin (min) | local margin | CPU s |
|---|---:|---:|---:|---:|---:|---|---:|---|---:|---|---:|
| 0.0300 ± 0.0300 | 0.251 | 24 | 256 | 1.16e-10 | 2.67e-10 | 2.6e-11, 1.8e-10 | 0.38 | ±2.44e-4 | 4.08 | 4.08–9.23 | 1,086 |
| 0.0708 ± 0.0108 | 0.339 | 16 | 256 | 1.66e-10 | 2.46e-10 | 3.7e-11, 2.6e-10 | 0.23 | ±2.11e-4 | 4.09 | 4.74–9.47 | 661 |
| 0.0923 ± 0.0107 | 0.424 | 16 | 256 | 2.82e-10 | 2.92e-10 | 6.2e-11, 4.4e-10 | 0.25 | ±2.12e-4 | 4.08 | 4.69–9.47 | 663 |
| 0.1134 ± 0.0103 | 0.503 | 16 | 288 | 4.99e-10 | 3.57e-10 | 1.1e-10, 7.8e-10 | 0.26 | ±2.14e-4 | 4.08 | 4.65–9.47 | 746 |
| 0.1334 ± 0.0097 | 0.575 | 12 | 368 | 8.62e-10 | 3.90e-10 | 1.8e-10, 1.4e-9 | 0.28 | ±1.77e-4 | 4.08 | 5.62–9.47 | 690 |
| 0.1521 ± 0.0090 | 0.639 | 12 | 496 | 1.63e-9 | 5.20e-10 | 3.4e-10, 2.6e-9 | 0.30 | ±1.78e-4 | 4.07 | 5.56–9.45 | 930 |
| 0.1642 ± 0.0031 | 0.660 | 4 | 544 | 2.03e-9 | 4.28e-10 | 3.8e-10, 2.9e-9 | 0.23 | ±1.17e-4 | 4.08 | 8.45–9.51 | 317 |

**Reading.**
- The margin is almost linear in `d`: `d/(width + η T)`, with the width nearly fixed.
- The `F_b − Λ_b` bound grows from 4.26e-4 to 4.87e-4 between `d = 1e-3` and `1.5e-3`, then stays at 4.88e-4.
  The jump is a tiling effect, not physics (next section).
- The rate side grows with `e_c` (`η_c` ×1.8 from `d = 1e-3` to `2e-3`). The Fourier tail `a₁` of the global
  `S` (`|k_c| ≤ 80`) grows ×140, to 9 % of `η_c` at `e_c = 0.66`. Both stay negligible against `d`: `η T` is 1.4 %
  of `d/2`.
- If the kernel's `a₁` came out much larger, `|k_c| ≤ 96` would restore it, as an estimate from `σ(0.66) = 0.225`.

## The range is set by the corners of the b-squares (a cheap third lever)

- The global `F_b − Λ_b` bound comes from the outermost b-squares of the lowest `ξ_c` interval, where `Γ_c ≈ 0` and
  the b-disc is largest.
- These squares only have to *meet* the disc `Γ_b ≤ Cmax − Γ_c`. Their far corners reach well outside `R(d)`:

  | `d` | disc radius (`Γ_c = 0`) | widest squares (centre) | their outer corner radius | their `F_b − Λ_b` width |
  |---:|---:|---|---:|---:|
  | 1e-3 | 0.155 | (0.12, ±0.12) | 0.226 | 4.26e-4 |
  | 1.5e-3, 2e-3 | 0.161, 0.167 | (0.20, ±0.04), (±0.04, 0.20) | 0.253 | 4.87e-4 |
  | all | | (0.04, 0.04), inside the disc | 0.113 | 2.3e-4 |

- The oscillation is about linear in `e_b`. Across the squares, the width is about
  `2.4e-5 + 1.8e-3 · (outer corner radius)`.
- The sampled range of the reports is also taken over the whole square. So it too overstates the range on `R(d)`.

**Sampled check.**
- Script `scripts/cover2_inregion.py`; table `validation/cover2-inregion-d2e-3.json`.
- `d = 2e-3`, the 24 cells of the lowest `ξ_c` interval, with the same producer, grid and `S` as the cover.
- Per cell: 600 random box points, and 200 random points on the rim `Γ_b = Cmax − Γ_c`, each on the full angle grid.
  554 s wall.

| `F_b − Λ_b` at `d = 2e-3` | lo | hi | width | 10³ yr margin at that width |
|---|---:|---:|---:|---:|
| ℓ¹ bound on the box cells (the cover) | −2.44e-4 | 2.44e-4 | 4.88e-4 | 4.07 |
| sampled over the whole boxes | −1.36e-4 | 2.04e-4 | 3.39e-4 | 5.8 |
| sampled on `R(d)` (box points inside it, and the rim) | −0.98e-4 | 1.29e-4 | 2.27e-4 | 8.7 |

- Every outer cell has the same rim width, 2.27e-4. The oscillation is set by `e_b`, which is largest on the rim,
  and hardly by the direction of b's eccentricity vector.
- On the four inner squares (inside the disc), box and region coincide: sampled width 1.5e-4, against an ℓ¹ width
  of 2.3e-4. So the cell ℓ¹ bound is about 1.5× the sampled range.
- Planet c is not affected: its range on this interval is 2.7e-5 over the boxes and 2.5e-5 on `R(d)`.

**Estimate.**
- An ℓ¹ range bound on cells that stay inside `R(d)` (polar cells in `(Γ_b, φ_b)`, or a range bound taken on
  `cell ∩ R(d)`) would have width about `1.5 × 2.27e-4 ≈ 3.4e-4` at `d = 2e-3`. That is margin about 5.8, and the
  linear fit above gives the same, `3.3e-4`.
- The floor, the range on `R(d)` itself, is margin 8.7.
- Finer squares at the rim help only slowly: the overhang of a square that meets the disc is up to its diagonal,
  `2√2 h_b`.
- This is a design option for the cell check (owner question 2). It is not built here.

## Lever 2: absorbing the kinetic oscillation of `Λ_b` (estimate)

**Measured source of the range.** The first-order part of `F_b − Λ_b` is `D_b χ₁`. Split by the source in
`P = μ f`, it has these ranges over the angle grid at the cell centre:

| point | total | `μ|p_b|²/2` (kinetic, b) | `μ p_c·p_b` | `−μ ν_c/|q_c − q_b|` |
|---|---:|---:|---:|---:|
| `Γ_b = 0.012`, c circular (`e_b = 0.116`) | 2.10e-4 | 2.19e-4 | 2.2e-5 | 2.7e-5 |
| `Γ_c = Γ_b = 0.006` (`e_b = 0.082`) | 1.59e-4 | 1.54e-4 | 2.1e-5 | 8.0e-6 |

The kinetic term, the reduced-mass part of LP's Kepler split, is the whole range. The other two partly cancel it.
This is phase 1's `2μ(1 − ν_c) e_b √a_b` (AUDIT-HD11964-PILOT-1, finding 4).

**It cannot be absorbed into `F_b`.**
- The range of `F_b − Λ_b` is the physical oscillation of the osculating `Λ_b = keplerAction`, not a defect of `F`.
  Phase 1's direct N-body integration measured a `Λ_b` excursion of `1.86e-4` in 20 yr.
- Any `F_b` with a small bracket `{F_b, H}` differs from `Λ_b` by that oscillation. So `hi − lo ≥` the oscillation
  range, whatever `F` is, at any order.
- `hstop` (LP-CONF) bounds the drift of `keplerAction` itself, so the oscillation must fit inside `d ≤ r/2`.

**What would remove it** (estimate; needs owner and LP-lane decisions):
- A Kepler split with the reduced-mass kinetic coefficient, so that `Λ̃_b` is the Kepler action of
  `(1/ν_b + μ)|p_b|²/2 − ν_b/|q_b|`. The kinetic oscillation would then sit in the Kepler part. The range would
  drop to about `5e-5` (cross plus direct), about 7× smaller, and the margin would then be set by planet c's range
  (`5.6e-5`): about 15 at `d = 10⁻³`, about 25 at `2e-3`.
- But LP0, `strongAMD` and `LiftData` are stated with `keplerAction` (mass `ν_i`). Changing the action changes
  frozen objects: an owner decision, not a producer change.
- Alternatively, the weighted per-planet drift lemma (`d_b` up to `δ/8 = 6e-3`, LP-QUANT §5.2) would triple `d_b`.
  The provisional ruling is no weighted lemma.

## Checks

- **Identity check.** At every cell centre of both new covers, the direct exact-gradient rate equals the five-term
  right side to ≤ 2.0e-14 absolute.
- **Convergence.** Every degree ratio of `T4`, `T5` is ≤ 0.38 (c) and ≤ 0.31 (b).
- **In-region check.** It recomputes the cover's `F − Λ` polynomials (same `cover2.run_cell` set-up). Its
  box-sampled `F_b − Λ_b` range, [−1.36e-4, 2.04e-4], is consistent with the cover's sampled
  [−1.38e-4, 2.07e-4] on the same `d` (fewer, different random points).
- **The reference is unchanged.** The regenerated `cover2-order2.json` equals the committed one in every old field
  (scripted comparison); only `region`, `range_width_tolerance` and `per_cell[].margin_local` are new.
- **`D.ok` at `d = 1/500`.** `2d = 1/250 = r`, and `η T + width ≤ 5.0e-4 < 1/500`.
- No Lean in this task. Everything ran under the 8 GB cap, two processes, user anon ≤ 5 GB at the start.

## Owner questions

1. **Which `d` for the kernel run.** `d = 1/500` gives margin 4.07 and ×2.04 of room on the critical range bound,
   for 100 cells instead of 80 (+34 % float64 CPU; the top `ξ_c` interval needs grid 544×64).
   - The costs: `e_c` up to 0.660, 0.003 below the Laplace limit, and `2d = r` exactly.
   - `d = 1.5e-3` is in between (margin 3.06, 88 cells).
   - Taken (most conservative for the margin): report all three; recommend `d = 1/500`.
2. **Cell shape for the range bound.** Polar b-cells, or a range bound on `cell ∩ R(d)`, would remove the corner
   overhang. At `d = 1/500` the estimate is margin about 5.8 with ℓ¹ bounds, and at most 8.7 (the sampled range
   on `R(d)`). This needs a decision on how the kernel's cell check represents a cell.
   - Taken: not done; estimate only.
3. **Reduced-mass Kepler action** (lever 2): a frozen-statement change; recorded, not pursued.

## Resume after reboot

- **Committed:**
  - `cover2.py` (`--d=`, summary fields);
  - `validation/cover2-order2-d1.5e-3.json`, `cover2-order2-d2e-3.json`;
  - the regenerated `cover2-order2.json`;
  - `scripts/cover2_inregion.py` and `validation/cover2-inregion-d2e-3.json` (the in-region check);
  - the application README (`cover2.py`, `cover2_inregion.py` rows and regenerate lines);
  - this handoff.
- **Raw records** are in `~/kam-data/hd11964/cover2/d1.5e-3.jsonl`, `d2e-3.jsonl` and `inregion-d2e-3.jsonl`
  (88, 100 and 24 lines; they survive the reboot).
- **To regenerate**, from the repository root, under the 8 GB cap:
  - `python3 -I applications/hd11964/scripts/cover2.py OUT.jsonl --procs=2 --hb=0.04 --d=2e-3` (about 43 min wall);
  - `… cover2.py --summary OUT.jsonl SUMMARY.json --d=2e-3`. The summary needs the same `--d=`.
  - `… cover2_inregion.py OUT.jsonl --d=2e-3 --hb=0.04 --procs=2` (about 9 min), then
    `… cover2_inregion.py --summary OUT.jsonl SUMMARY.json --d=2e-3 --hb=0.04`.

  The cover run resumes from an existing `OUT.jsonl`.
- **Open:**
  - the kernel measurement (kamx-hd-layer), now with `d` to be chosen (owner question 1);
  - owner questions 2 and 3.
