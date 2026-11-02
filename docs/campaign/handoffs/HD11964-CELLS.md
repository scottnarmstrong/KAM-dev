# Handoff HD11964-CELLS (phase 2: region-fitted cells for the order-2 cover, float64)

Worker kamx-hd11964, branch `hd11964-p2`. Task from the orchestrator (2 November 2026), after the HD11964-COVER-D
rulings:
1. `d = 1/500` for the kernel run;
2. region-fitted cells are worth it: design and measure them in float64, covering
   - cell shapes that hug `R(d)`,
   - how the cell check states membership,
   - cost against the 100-cell cover,
   - the resulting `F_b − Λ_b` range and margin;
3. the reduced-mass Kepler action is recorded for Scott (it changes frozen LP statements; the LP lane's call), not
   pursued.

Python only, no Lean. Nothing pushed.

STATUS: RUNNING

## Why the box cover loses margin

- **The model.** On a cell, the ℓ¹ range bound of `F_b − Λ_b` behaves like `k · ρ_eff`, with
  `ρ_eff = |centre_b| + h₁ + h₂` (the centre's distance from the origin of b's `(ξ_b, η_b)` disc, plus the two
  half-widths) and `k ≈ 1.70e-3`. It fits all the box cells of HD11964-COVER-D within a few %.
- **The reason.** The oscillation of `Λ_b` is linear in `(ξ_b, η_b)`, roughly `Re((ξ_b − i η_b) e^{iλ_b})`.
  - The centre value contributes `|centre|`, since the Fourier modulus is Euclidean.
  - Each linear Taylor term contributes its half-width, since ℓ¹ adds them.
- **The cost.** An axis square that only *meets* the disc of radius `R` has `ρ_eff` up to about `R + 2√2 h`.
  - At `d = 1/500` (`R = 0.167`) the widest squares have `ρ_eff = 0.284`, so the width is 4.88e-4.
  - The range on `R(d)` itself is 2.27e-4 (sampled; COVER-D), which corresponds to `ρ_eff ≈ R`.

## The design: sectors carried by rotated boxes

**Cells.** For each `ξ_c` interval `[a, b]` (unchanged from `cover2.py`), b's disc of radius
`R = √(2 Cmax − a²)` is cut into rings `ρ_b ∈ [ρ_in, ρ_out]` of `n` annular sectors. A ring with `ρ_in = 0` is a fan
of wedges from the origin.
- Each sector of half-angle `α = π/n` around the direction `φ` is carried by the smallest box in its own frame
  `e_r = (cos φ, sin φ)`, `e_t = (−sin φ, cos φ)`:
  - radial coordinate in `[ρ_in cos α, ρ_out]`;
  - tangential coordinate in `±ρ_out sin α`.
- So `ρ_eff = ρ_out (1 + sin α)`. The overshoot is the tangential half-width only; the radial one is exact.
- A small disc (the top `ξ_c` interval) gets one square at the origin, with `ρ_eff = 2R`.

**Choice of `n`.** Every cell must have `ρ_eff ≤ ρ* = R_max (1 + κ)`, where `R_max = √(2 Cmax)` is the disc radius
at `ξ_c = 0`. Half-widths are capped at `h_max = 0.085`, the Taylor convergence range of the `h_b = 0.08` cover. The
planner tries 1–3 rings and keeps the fewest cells. It always ends up choosing wedges from the origin: one fan per
`ξ_c` interval.

**Producer.** Same as `cover2.run_cell`: the same `S`, grid rule, degree and centre jets. The jets of the five terms
and of `F − Λ` are then rotated into the cell frame by the exact linear substitution
`x_b = cos φ r − sin φ t`, `y_b = sin φ r + cos φ t` (checked to 8e-16) before the ℓ¹ bounds. Brackets are taken
in the original canonical variables. The rotation only reparametrises the cell.

**Cell counts** at `d = 1/500` (`--plan-only`). `nmult = 4` rounds every `n` up to a multiple of 4, for the Lean
covering argument below:

| `κ` | `ρ*` | cells | cells, `n` a multiple of 4 | lowest interval (sectors) |
|---:|---:|---:|---:|---:|
| 0.1 | 0.184 | 79 | 85 | 32 |
| 0.15 | 0.192 | 60 | 69 | 21 |
| 0.2 | 0.201 | 50 | 57 | 16 |
| 0.3 | 0.218 | 39 | 45 | 11 |
| box cover (COVER-D) | 0.284 | 100 | | 24 |

## How the cell check states membership

**A cell is an affine box.** Cell `k` carries rational data:
- a centre `w_k`: `Λ = Λ̂`, `ξ_c` at the interval's midpoint, `η_c = 0`, and `(ξ_b, η_b) = c_k e_r`;
- half-widths `h`;
- a frame `e_r = (1 − s², 2s)/(1 + s²)`, `e_t = (−2s, 1 − s²)/(1 + s²)` with `s ∈ ℚ`. This frame is exactly
  orthonormal (a rational point of the circle, `s ≈ tan(φ/2)`).

With `p = (ξ_b, η_b) = (slow w.1 1, slow w.2 1)`, membership is a conjunction of linear inequalities with rational
coefficients:

    w ∈ K_k  ↔  |Λ_i − Λ̂_i| ≤ h_Λi ∧ |ξ_c − x_k| ≤ h_ξ ∧ |η_c| ≤ h_η
               ∧ |⟨p, e_r⟩ − c_k| ≤ h_r ∧ |⟨p, e_t⟩| ≤ h_t.

**The kernel's per-cell enclosure is unchanged.**
- It evaluates on `w = w_k + M_k u`, `u ∈ [−1, 1]⁶`.
- `M_k` is diagonal except for the 2×2 rational rotation block in `(ξ_b, η_b)`.
- The polynomial data are Taylor coefficients in `u`, as now (`cover2_fit.rotate` produces them). Alternatively the
  kernel seeds its jets with the columns of `M_k`.

**The only new requirement on the cell check is a non-diagonal affine cell map.**

**The cover lemma.**
- Statement: every `w ∈ region d` with `η_c = 0` and `ξ_c ≥ 0` lies in some `K_k`. This is the set the rotation
  lemmas `bracket_bound_of_rotation` and `range_bound_of_rotation` need.
- Every step of the proof is finite and rational:
  1. **`ξ_c` interval.** `ξ_c ∈ [a_j, b_j]` for some `j`. The endpoints are rational and consecutive, with `a_0 = 0`.
     The last endpoint satisfies `b_last² ≥ 2 Cmax ≥ 2 chartAMD w ≥ ξ_c²`.
  2. **Disc.** `|p|² = 2 chartAMD w − ξ_c² ≤ 2 Cmax − a_j² ≤ R_j²`, where `R_j²` is a rational upper bound. It
     uses `chartAMD w = Σ_i (slow w.1 i² + slow w.2 i²)/2` and `η_c = 0`.
  3. **Direction.** The sector boundaries are rational rays `v_0, …, v_{n−1}`. With `n` a multiple of 4 and the
     axes among the rays (`--nmult=4`), a case split on the signs of `(ξ_b, η_b)` leaves, in each quadrant, rays
     sorted by rational slope. `p` lies between two consecutive ones: a linear-order search, proved as one generic
     lemma.
  4. **Sector ⊆ box** (one generic lemma, then per cell only rational side conditions, decided by
     `decide +kernel` / `norm_num`). Write `p = α v_s + β v_{s+1}` with `α, β ≥ 0`, where both rays have
     `⟨v, e_r⟩ > 0`. Then:
     - `0 ≤ ⟨p, e_r⟩ ≤ |p| ≤ R` (Cauchy–Schwarz, with `|e_r| = 1` exactly);
     - `|⟨p, e_t⟩| ≤ τ ⟨p, e_r⟩`, where `τ = max |⟨v, e_t⟩|/⟨v, e_r⟩` over the two rays (rational, by linearity);
     - hence `⟨p, e_t⟩² ≤ R² τ²/(1 + τ²) ≤ h_t²`.

     The per-cell conditions are:
     - `⟨v, e_r⟩ > 0` for both rays;
     - `h_t² (1 + τ²) ≥ R² τ²`;
     - for a wedge, `c_k − h_r ≤ 0` and `c_k + h_r ≥ R`; for a ring `ρ_in > 0`, `c_k − h_r` is at most the
       rational lower bound of `⟨p, e_r⟩` on the sector.

  The float64 plan uses exact angles `2πj/n`. A Lean cover would replace them by rational points of the circle,
  with the box widths computed from those rational rays. With `s` of denominator 10⁶, the angles move by less
  than 1e-6 and the widths by less than 2e-7. This is not built here.
- **Checked numerically:**
  - 200,000 random points of the representative slice of `R(1/500)`, half of them on the rim, all lie in some cell,
    for each of the plans `κ = 0.2`, `κ = 0.1` and `κ = 0.2` with `nmult = 4`;
  - 2,000 points of every sector, including its corners, lie in its box.

## Results at `d = 1/500` (float64, ℓ¹ bounds plus remainder estimates; *estimated*, not certified)

Tables:
- `applications/hd11964/validation/cover2-fit-k0.2-d2e-3.json` (50 cells);
- `cover2-fit-k0.1-d2e-3.json` (79 cells);
- `cover2-fit-k0.2-n4-d2e-3.json` (57 cells, `nmult = 4`).

Each table has per-cell centre, frame angle, kind, `ρ_eff`, half-widths, grid, `a₁..a₅`, `η`, the `F − Λ` bound, the
degree ratios, the cell margin and the local margin. The raw records are in
`~/kam-data/hd11964/cover2/fit-*.jsonl`.

| at `d = 1/500` | box cover (COVER-D) | fitted, `κ = 0.2` | fitted, `κ = 0.2`, `nmult = 4` | fitted, `κ = 0.1` |
|---|---:|---:|---:|---:|
| cells | 100 | **50** | N4_CELLS | 79 |
| largest `ρ_eff` | 0.284 | 0.200 | N4_REFF | 0.184 |
| `F_b − Λ_b` ℓ¹ bound (width) | ±2.44e-4 (4.88e-4) | ±1.68e-4 (3.35e-4) | N4_WB | ±1.54e-4 (3.08e-4) |
| `F_b − Λ_b` sampled over the cells | [−1.38e-4, 2.07e-4] | [−1.01e-4, 1.34e-4] | N4_SB | [−1.00e-4, 1.32e-4] |
| `F_b − Λ_b` sampled on `R(d)` (box points inside it) | [−0.98e-4, 1.29e-4] † | [−0.98e-4, 1.29e-4] | N4_RB | [−0.98e-4, 1.28e-4] |
| `F_c − Λ_c` ℓ¹ bound (width) | ±3.20e-5 (6.4e-5) | ±3.11e-5 (6.2e-5) | N4_WC | ±3.11e-5 (6.2e-5) |
| `η_c` / `η_b` | 2.03e-9 / 5.20e-10 | 1.98e-9 / 4.36e-10 | N4_ETA | 1.98e-9 / 4.36e-10 |
| largest degree ratio (c / b) | 0.38 / 0.30 | 0.40 / 0.34 | N4_Q | 0.39 / 0.33 |
| identity check (max at the centres) | 2.0e-14 | 6.9e-15 | N4_ID | 6.9e-15 |
| **10³ yr margin** (ℓ¹ range bounds) | 4.07 | **5.92** | N4_M | **6.43** |
| 10³ yr margin, sampled over the cells | 5.74 | 8.38 | N4_MS | 8.49 |
| per-cell margin: min / median / max | 4.07 / 4.09 / 4.09 | 5.92 / 5.94 / 5.95 | N4_PC | 6.43 / 6.47 / 6.47 |
| **tolerance on the `F_b − Λ_b` width** (margin ≥ 2) | ×2.04 | **×2.98** | N4_TOL | ×3.24 |
| tolerance on `η_c` / `η_b` | ×68 / ×146 | ×70 / ×226 | N4_ETOL | ×70 / ×235 |
| float64 CPU (2 processes) | 5,097 s | **2,609 s** (1,307 s wall) | N4_CPU | 3,787 s (1,911 s wall) |
| CPU relative to the box cover | 1 | **0.51** | N4_REL | 0.74 |

† COVER-D's in-region check (`cover2_inregion.py`), on the lowest `ξ_c` interval.

**Per `ξ_c` interval** (`κ = 0.2`, 50 cells; widths are the largest cell `F_b − Λ_b` ℓ¹ width):

| `ξ_c` centre | `e_c` max | cells (box cover) | grid N1 | `η_c` max | `η_b` max | degree ratio (c) | `ρ_eff` max | `F_b − Λ_b` width | local margin | CPU s |
|---:|---:|---|---:|---:|---:|---:|---:|---:|---|---:|
| 0.0300 | 0.251 | 16 wedges (24) | 256 | 1.03e-10 | 1.80e-10 | 0.40 | 0.200 | 3.29e-4 | 6.06–6.21 | 757 |
| 0.0708 | 0.339 | 11 wedges (16) | 256 | 1.58e-10 | 2.02e-10 | 0.27 | 0.200 | 3.32e-4 | 5.99–6.36 | 507 |
| 0.0923 | 0.424 | 9 wedges (16) | 256 | 2.68e-10 | 2.38e-10 | 0.28 | 0.196 | 3.29e-4 | 6.05–6.54 | 434 |
| 0.1134 | 0.503 | 6 wedges (16) | 288 | 4.79e-10 | 2.98e-10 | 0.31 | 0.198 | 3.35e-4 | 5.93–6.44 | 303 |
| 0.1334 | 0.575 | 4 wedges (12) | 368 | 8.75e-10 | 3.74e-10 | 0.33 | 0.192 | 3.27e-4 | 6.07–6.56 | 268 |
| 0.1521 | 0.639 | 3 wedges (12) | 496 | 1.58e-9 | 4.36e-10 | 0.33 | 0.162 | 2.74e-4 | 7.23–8.18 | 246 |
| 0.1642 | 0.660 | 1 square (4) | 544 | 1.98e-9 | 3.84e-10 | 0.24 | 0.090 | 1.69e-4 | 11.68 | 90 |

**Reading.**
- **The model holds.** Every cell's width is `k ρ_eff` with `k = 1.65–1.69e-3` (1.9e-3 for the one square), so the planner's target `ρ*`
  sets the global range: 3.35e-4 at `κ = 0.2` (predicted 3.4e-4) and 3.08e-4 at `κ = 0.1` (predicted 3.1e-4). Every
  interval reaches about the same width, so no interval dominates.
- **Fewer cells and a tighter range.** The box cover pays twice: its corner squares raise the range, and it has 12–16
  cells in the expensive high-`e_c` intervals. The fitted cover has 3–4 cells there. Its CPU is 51 % of the box
  cover's at `κ = 0.2`.
- **The rate side is unchanged.**
  - `η_c` is set by the top square (1.98e-9, as before), and `η_b` falls slightly.
  - The long wedges (radial half-width 0.084) converge as well as the 0.04 squares: degree ratio ≤ 0.40.
  - The identity check holds to ≤ 6.9e-15.
- **The floor.**
  - With `ρ_eff → R = 0.167` (`κ → 0`) the ℓ¹ width tends to `k R ≈ 2.8e-4`, which is margin about 7.0 at
    `d = 1/500`.
  - The range on `R(d)` itself, sampled, is 2.27e-4, margin 8.7. The remaining factor of about 1.2 is the ℓ¹ norm's own
    loss (harmonics, the `Λ`- and `ξ_c`-dependence), not the cell shape.
  - `κ = 0.1` buys +0.5 of margin for 29 more cells. `κ = 0.2` is the better trade.

## Cost against the 100-cell box cover

| | box cover | fitted `κ = 0.2` | fitted `κ = 0.2`, `nmult = 4` | fitted `κ = 0.1` |
|---|---:|---:|---:|---:|
| cells | 100 | 50 | N4_CELLS | 79 |
| cells in the two high-`e_c` intervals (grids 496, 544) | 16 | 4 | N4_TOP | 4 |
| `Σ N1·N2` over cells (grid-weighted count) | 2.46e6 | 1.12e6 (0.46) | N4_SUMN | 1.70e6 (0.69) |
| float64 CPU | 5,097 s | 2,609 s | N4_CPU2 | 3,787 s |

The kernel's per-cell cost scales with the grid area, so the grid-weighted count is the best proxy. On it the
fitted `κ = 0.2` cover costs 46 % of the box cover, and `κ = 0.1` costs 69 %.
- The fitted cells' smaller corner radius also lowers `N2` on the low-`e_c` intervals: 80 everywhere, against up to
  96.
- In float64 the rotation of the jets (a 462×462 matrix product per jet) adds about 5 s per cell, about 10 %. That
  is why the CPU ratio, 0.51, is a little above 0.46.
- In the kernel the rotation is a different jet seed, at no cost.

## Checks

- **Rotation.** The jet substitution matches direct evaluation to ≤ 8e-16 (random degree-4 jets, random points).
- **Coverage.**
  - 200,000 random points of the representative slice of `R(1/500)` (half on the rim) are covered by each of the
    three plans;
  - every sector lies inside its box (2,000 points per sector, corners included).
- **Identity check.** At every cell centre, the direct exact-gradient rate equals the five-term right side to
  ≤ 6.9e-15 (`κ = 0.2` and `0.1`).
- **Convergence.** Degree ratios are ≤ 0.40 (c) and ≤ 0.34 (b).
- **Consistency with COVER-D.** The in-region sampled range of `F_b − Λ_b` is the same here, [−0.98e-4, 1.29e-4],
  as in COVER-D's separate check. The rotated cells and the axis squares see the same function.
- No Lean in this task. Everything ran under the 8 GB cap, two processes, at most 2.9 GB each.

## Owner questions

1. **Which fitted cover for the kernel.** `κ = 0.2` with `nmult = 4` is the recommended target: N4_CELLS cells,
   margin N4_M, ×N4_TOL on the range width. Its sector counts allow the quadrant-split covering lemma. `κ = 0.1`
   gives +0.5 of margin for about 30 more cells.
   - Taken: report all three; recommend `κ = 0.2`, `nmult = 4`.
2. **Kernel interface.** The cell map becomes affine with a 2×2 rational rotation block (Pythagorean frames). This
   needs kamx-hd-layer's agreement: its cell check must accept a non-diagonal `M_k`, or take polynomial data already
   in `u` (the producer's rotated jets).
3. **Cover lemma in Lean.** The four-step cover proof above (interval, disc, quadrant/sector, sector ⊆ box) is new
   application-side Lean: two generic lemmas plus decided per-cell data. It is not written yet; it waits for the
   kernel cell format.
4. **Reduced-mass Kepler action.** Recorded for Scott (ruling 3): it changes frozen LP statements, the LP lane's
   call. Not pursued. For scale, it would cut the `F_b − Λ_b` range about 7× (COVER-D lever 2), which on fitted
   cells would leave planet c's range (6.2e-5) as the limit: margin about 25 at `d = 1/500`.

## Resume after reboot

- **Committed** (this handoff's commit):
  - `applications/hd11964/scripts/cover2_fit.py`;
  - `validation/cover2-fit-k0.2-d2e-3.json`, `cover2-fit-k0.1-d2e-3.json`, `cover2-fit-k0.2-n4-d2e-3.json`;
  - the application README rows;
  - this handoff.
- **Raw records** are in `~/kam-data/hd11964/cover2/fit-k0.2-d2e-3.jsonl`, `fit-k0.1-d2e-3.jsonl` and
  `fit-k0.2-n4-d2e-3.jsonl`.
- **To regenerate**, from the repository root, under the 8 GB cap:
  - `python3 -I applications/hd11964/scripts/cover2_fit.py OUT.jsonl --d=2e-3 --kappa=0.2 --nmult=4 --procs=2`
    (about 25 min wall);
  - then `… cover2_fit.py --summary OUT.jsonl SUMMARY.json --d=2e-3 --kappa=0.2 --nmult=4`;
  - `--plan-only` prints the plan.

  The run resumes from an existing `OUT.jsonl`.
- **Open:**
  - owner questions 1–3;
  - then the kernel measurement on the fitted cells (kamx-hd-layer).
