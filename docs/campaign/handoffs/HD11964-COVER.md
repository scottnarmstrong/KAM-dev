# Handoff HD11964-COVER (phase 2: the order-2 cover of `R(d)`, float64)

Worker kamx-hd11964, branch `hd11964-p2`. Task from the orchestrator (1 November 2026):
- generate the cover of the region `D.d`, with rotation representatives;
- run the float64 five-term evaluation on every cell;
- report per cell `a₁..a₅`, `η` and the `F − Λ` range, the worst cell, and whether the 10³ yr rung closes with
  margin ≥ 2 on every cell.

Python only, no Lean. Nothing pushed.

**Status: done.**
- On every cell the degree-3 Taylor × Fourier bounds converge (degree ratio ≤ 0.37).
- The 10³ yr rung closes on every cell with margin ≥ 2: 2.33 on the 80-cell cover, 2.06 on the 21-cell cover.

Commits: `fb2f83d0` (script, pass 1) and this handoff's commit.

## The cover

**Region.** `R(d)`, `d = 10⁻³` (`HD11964.region`): `Λ ∈ [Λlo − d, Λhi + d]`, `Γ_c + Γ_b ≤ 0.012`, every angle.

**Rotation representatives** (`bracket_bound_of_rotation`, `range_bound_of_rotation`).
- Every chart state rotates to one with `η_c = 0`, `ξ_c ≥ 0`: planet c's eccentricity vector along `+ξ`.
- So the cover needs only `{η_c = 0, 0 ≤ ξ_c ≤ √(2·0.012)} × {(ξ_b, η_b) : Γ_c + Γ_b ≤ 0.012} × Λ-box`.
- Planet c's hard direction (high `e_c`) becomes one-dimensional. Planet b's disc, `e_b ≤ 0.116`, needs a few
  squares.

**Cells** are boxes `|u_j| ≤ 1` in `prod2.py`'s normalised variables:

| variable | cells |
|---|---|
| `Λ_c`, `Λ_b` | one each: centre `Λ̂`, radius `ρ + d` = (1.1e-3, 4.0e-3) |
| `ξ_c` | intervals of half-width `w(ξ) = clamp(0.15 σ(e)/|dσ/dξ|, 0.004, 0.03)`, set at the interval's upper end (the e-dependence of the Fourier decay, HD11964-PROD finding 1) |
| `η_c` | radius 0.002 around 0 (the representatives) |
| `(ξ_b, η_b)` | squares of half-width 0.08 (or the disc radius, if smaller) meeting the disc `Γ_b ≤ 0.012 − Γ_c(min)` |

**The mode set `S`** is global, `|k_c| ≤ 80`, `|k_b| ≤ 20`, because the Lean `F` is one function on `R(d)`.

**Per cell.**
- `prod2.Prod2` runs at the cell centre with base degree 5, on the grid of `gate.grid_for` at the cell's largest
  `(e_c, e_b)`, with `N1 ≥ 256` and `N2 ≥ 64`.
- It reports the five terms' bounds (ℓ¹ of the degree ≤ 3 polynomial on the cell, plus the remainder estimate),
  `η = a₁ + a₂ + a₃ + a₄ + a₅/2`, the sampled sups (105 cell points × the angle grid), the degree ratios
  `q = ‖deg 3‖/‖deg 2‖` of `T4`, `T5`, and the `F − Λ` range (sampled, and the ℓ¹ bound).
- It also runs the identity check at the centre (the direct exact-gradient rate against the five-term right side).

## Results

Two passes with the same `ξ_c` intervals:
- pass 1 has `(ξ_b, η_b)` squares of half-width 0.08: **21 cells**;
- pass 2 has half-width 0.04: **80 cells**.

The tables are `applications/hd11964/validation/cover2-order2-pass1.json` (21 cells) and `cover2-order2.json` (80
cells, the reference). Each has, per cell, the centre, radii, grid, `a₁..a₅` and `η` for both planets, the `F − Λ`
bound, the degree ratios, the cell margin and the CPU time. The raw per-cell records are in
`~/kam-data/hd11964/cover2/*.jsonl`.

**Global numbers** (*estimated*: float64, ℓ¹ bounds plus remainder estimates, sampled checks):

| | 21 cells (`h_b` = 0.08) | 80 cells (`h_b` = 0.04) |
|---|---:|---:|
| `η_c` (max over cells) | 1.13e-9 (cell 20, `ξ_c` = 0.1494 ± 0.0055) | 1.11e-9 (cell 78, same `ξ_c` interval) |
| `η_b` | 5.25e-10 (cell 18) | 3.86e-10 (cell 74, `ξ_c` = 0.1341, `(ξ_b, η_b)` = (0.12, −0.04)) |
| `F_c − Λ_c`: ℓ¹ bound / sampled | ±2.87e-5 / [−1.39e-5, 2.37e-5] | ±2.80e-5 / [−1.35e-5, 2.41e-5] |
| `F_b − Λ_b`: ℓ¹ bound / sampled | ±2.40e-4 / [−1.27e-4, 1.83e-4] | ±2.13e-4 / [−1.26e-4, 1.83e-4] |
| largest degree ratio of `T4`, `T5` (c / b) | 0.42 / 0.39 | 0.37 / 0.29 |
| largest direct rate at a cell centre (c / b) | 2.93e-10 / 7.70e-11 | 3.18e-10 / 8.65e-11 |
| identity check (max difference at the centres) | 9.3e-15 | 1.4e-14 |
| **10³ yr margin**, ℓ¹ range bounds | **2.06** | **2.33** |
| 10³ yr margin, sampled range | 3.19 | 3.21 |
| smallest per-cell margin | 2.06 | 2.33 |
| float64 CPU | 1,321 s (2 processes, 680 s wall, ≤ 2.9 GB) | 3,798 s (1,915 s wall, ≤ 2.4 GB) |

**Per `ξ_c` interval** (80-cell cover):

| `ξ_c` centre ± half-width | `e_c` max | cells | grid | `η_c` max | `η_b` max | `a₄`, `a₅` (c) of the worst cell | degree ratio (c) | `F_b − Λ_b` bound | margin | CPU s |
|---|---:|---:|---|---:|---:|---|---:|---|---:|---:|
| 0.0300 ± 0.0300 | 0.249 | 16 | 256×96 | 1.07e-10 | 2.18e-10 | 2.4e-11, 1.7e-10 | 0.37 | ±2.09e-4 | 2.34 | 732 |
| 0.0709 ± 0.0109 | 0.337 | 16 | 256×96 | 1.63e-10 | 2.42e-10 | 3.7e-11, 2.5e-10 | 0.22 | ±2.10e-4 | 2.34 | 722 |
| 0.0926 ± 0.0108 | 0.422 | 16 | 256×96 | 2.78e-10 | 2.87e-10 | 6.1e-11, 4.3e-10 | 0.23 | ±2.12e-4 | 2.34 | 709 |
| 0.1139 ± 0.0104 | 0.501 | 16 | 288×96 | 4.91e-10 | 3.52e-10 | 1.1e-10, 7.7e-10 | 0.25 | ±2.13e-4 | 2.33 | 754 |
| 0.1341 ± 0.0098 | 0.573 | 12 | 368×80 | 8.48e-10 | 3.86e-10 | 1.8e-10, 1.3e-9 | 0.26 | ±1.76e-4 | 2.33 | 662 |
| 0.1494 ± 0.0055 | 0.612 | 4 | 432×64 | 1.11e-9 | 3.32e-10 | 2.3e-10, 1.75e-9 | 0.22 | ±1.16e-4 | 2.33 | 219 |

**The worst cell** (planet c, cell 78):
- centre `Λ̂`, `ξ_c = 0.1494`, `η_c = 0`, `(ξ_b, η_b) = (0.04, −0.04)`;
- radii `(1.1e-3, 4e-3, 5.5e-3, 2e-3, 0.04, 0.04)`;
- `a = (1.4e-12, 1.6e-14, 5.4e-14, 2.3e-10, 1.75e-9)`, `η_c = 1.11e-9`.

`T1`–`T3` (the tails and the tail bracket) are negligible everywhere. `η` is `a₄ + a₅/2`, which is about 5× the
direct rate at the centres because `T4` and `½ T5` cancel partly.

## The 10³ yr rung

- **What sets the margin.** `margin = d / max_i (η_i T + hi_i − lo_i)` with `T = 6741.9` units and `d = 10⁻³`. The
  rate terms are small: `η_c T = 7.5e-6`, `η_b T = 2.6e-6`. The margin is set by the **range of `F_b − Λ_b`**, which is
  planet b's reduced-mass oscillation (phase 1). The ℓ¹ bound gives a width of 4.26e-4; the sampled range is 3.09e-4.
- **Tolerance for the kernel measurement.** For margin ≥ 2, the kernel's bounds may exceed these float64 numbers by:
  - up to ×28 on `η_b`, or ×59 on `η_c`, with the range unchanged;
  - up to **×1.17 on the width of the `F_b − Λ_b` range**, with `η` unchanged.

  So the critical quantity for the cell check is the range bound of `F_b − Λ_b`, not the bracket bound.
  - The ℓ¹ bound is symmetric about the angle average.
  - A tighter range bound (asymmetric, or on smaller b-cells) has room: the sampled width is 3.09e-4, which would
    give margin 3.2.
  - Halving the b squares raised the margin from 2.06 to 2.33.
- **Cells and cost.** The order-2 cover needs only 21 cells for margin 2.06, and 80 cells for 2.33: the low end of
  design §8's 50–200, or below it. kamx-hd-layer's measured per-cell cost × 21–80 is the extrapolation. The top
  `ξ_c` interval (`e_c` up to 0.612) is the most expensive: grid 432 × 64.

## Checks

- **Identity check.** At every cell centre, the direct rate (exact gradient of `H∘Ψ`) equals the five-term right
  side to ≤ 1.4e-14 absolute.
- **Convergence.** Every degree ratio ≤ 0.42 (pass 1) / 0.37 (pass 2). The remainder estimate is 2× the degree-4
  ℓ¹ norm for `T1`–`T3`, and the geometric continuation for `T4`, `T5`.
- **Reflection.** With `η_c = 0`, mirrored cells (`η_b → −η_b`) give identical numbers, as the reflection symmetry
  predicts. This is a sanity check; the cover does not rely on it.
- No Lean in this task. Everything ran under the 8 GB cap, two processes.

## Owner questions

1. **Which cover for the kernel run.** The 21 cells reach margin 2.06; the 80 cells reach 2.33. The kernel's
   rounding radii and witness radii loosen the bounds, so 80 cells, or a tighter `F_b − Λ_b` range bound, is the
   safer target.
   - Taken: report both, with the 80-cell cover as the reference table.
2. **Representatives.** The cover uses the rotation representatives `η_c = 0`, `ξ_c ≥ 0`
   (`bracket_bound_of_rotation`). Part B's `F` must be rotation-invariant, which the exact `χ*` is. The cell check
   needs `D_k` and `pb` to commute with `chartRot` (AUDIT-HD11964-P2B-1's forward note).

## Resume after reboot

- **Committed:**
  - `fb2f83d0`: `cover2.py` and the pass-1 table;
  - this handoff's commit: the pass-2 table and the handoff.
- **Raw records** are in `~/kam-data/hd11964/cover2/pass1.jsonl` and `pass2-hb004.jsonl`.
- **To regenerate**, from the repository root, under the 8 GB cap:
  - `python3 -I applications/hd11964/scripts/cover2.py OUT.jsonl --procs=2 --hb=0.04` (about 32 min wall);
  - `… cover2.py --summary OUT.jsonl SUMMARY.json`.
  The run resumes from an existing `OUT.jsonl`, skipping finished cells.
- **Open:**
  - the kernel measurement (kamx-hd-layer);
  - the choice of cover (owner question 1).
