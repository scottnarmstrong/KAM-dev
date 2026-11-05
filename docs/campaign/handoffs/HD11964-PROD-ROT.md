# Handoff HD11964-PROD-ROT (phase 2: the order-2 generators in the rotated cell variables)

Worker kamx-hd11964, branch `hd11964-p2`. Task from the orchestrator (2 November 2026), while AUDIT-HD11964-COVER-1
ran:
- extend the producer `prod2_hp.py` to expand the generators in the rotated cell variables of the 50-cell fitted
  cover;
- check it on the worst cell against the box-cell result;
- Python only, 8 GB cap.

Nothing pushed.

**Status: done.** On the worst rotated cell (#46), the rotated expansion and the box expansion at the same centre
agree, coefficient by coefficient through the exact substitution, to rounding:

| generator | largest difference | relative to the largest coefficient | entries compared |
|---|---:|---:|---:|
| `χ₁` (degree 4) | 4.4 units of 2⁻¹⁶⁰ | 1.5e-43 | 692,045 |
| `χ₂` (degree 3) | 2.8 units of 2⁻¹⁶⁰ | 2.6e-40 | 277,200 |

## What changed in `applications/hd11964/scripts/prod2_hp.py`

- **`chart(..., rot=(a, b))`.** Planet b's slow pair is seeded as the affine cell map of the fitted cover:
  `ξ_b = c₄ + a h₄ u_r − b h₅ u_t` and `η_b = c₅ + b h₄ u_r + a h₅ u_t`.
  - This is `HD11964.Cover.AffineCell.map`, and `tf_cell.py --rot_b`'s convention.
  - Every Taylor coefficient is then one of `u^m` in the cell variables `(u_Λc, u_Λb, u_ξc, u_ηc, u_r, u_t)`.
- **Nothing downstream changes**: the DFT, the homological solve and `G₂ = {P − ½Π_S P, χ₁}`.
  - The rotation is symplectic with determinant 1, so the bracket of the `(ξ_b, η_b)` pair keeps its form in
    `(u_r, u_t)`, scaled by `1/(h₄ h₅)`.
  - `1/(k·ω(Λ))` involves only the `Λ` variables.
- **`omega_inv_jets(..., hL)`** takes the cell's `Λ` half-widths instead of the global `H_CELL`.
- **New options:**
  - `--plan=PLAN.json --cell=K` takes the centre, half-widths and frame from the exact rational plan
    (`validation/cover2-plan-k0.2-d2e-3.json` = `HD11964.CoverPlan.fitPlan`). `K` indexes the plan's distinct
    cells, in the same order as the float64 cover's cell ids; `--list-cells` prints them.
  - The grid is `cover2_fit`'s (`gate.grid_for`, `N1 ≥ 256`, `N2 ≥ 64`) unless `--N1`/`--N2` are given.
  - `--box` keeps the centre and `h` but drops the rotation; it is the comparison run.
  - `--compare=ROT,BOX` is the exact check below.
- **`--check`** (the float64 cross-check against `prod2.py`) rotates the float64 jets with `cover2_fit.rotate`
  for a rotated cell.
- **The output's `cell` record** holds the plan, the index, the slab, the exact `c`, `h`, `a`, `b`, the variables
  and the map.
- **Backward compatibility.** Without `--plan`, the script is unchanged: kamx-hd-layer's box cell, `H_CELL`,
  448×72.

## The check

**The cell.**
- #46 is slab 5 (`ξ_c ∈ [0.143097, 0.161123]`, `e_c ≤ 0.639`), the wedge at 60°.
- Its frame is `(a, b) = (266666791, 461880000)/533333209`, a Pythagorean point.
- Half-widths: `h_r = 0.0434`, `h_t = 0.0751`. Grid 496×64.
- It is the worst *rotated* cell of the 50-cell cover: `η_c = 1.58e-9` in HD11964-CELLS (#48 is its mirror). The
  cover's worst cell overall is the top disc cell #49, whose frame is the identity.

**Two runs** at the production settings (`Kc = 80`, `Kb = 20`, `DJ = 4`, 2⁻¹⁸⁴ fixed point, output 2⁻¹⁶⁰):
- the rotated expansion;
- the box expansion at the same centre with the same `h`.

**The comparison** (`--compare`) pushes the box polynomial in `u'` through the exact substitution
`u' = diag(1/h') Rot(a, b) diag(h) u` (fractions, then exact integers per Fourier mode), and compares with the rotated
polynomial.

| degree | 0 | 1 | 2 | 3 | 4 |
|---|---:|---:|---:|---:|---:|
| `χ₁`: largest difference (units of 2⁻¹⁶⁰) | 0 | 1.43 | 2.00 | 2.69 | 4.36 |
| `χ₂` | 0 | 1.42 | 2.00 | 2.82 | |

The record is in `applications/hd11964/validation/prod2-rot-check-c46.json`.

**The float64 cross-check** of the rotated expansion against `prod2.py` plus `cover2_fit.rotate` on the same grid:
`χ₁` to 3.05e-20 (largest coefficient 2.3e-5), `χ₂` to 2.07e-23 (8.4e-9). This is the same agreement as the
original box cell's (HD11964-PROD).

**A small-grid smoke test** (96×32, degree 3, `Kc = 20`, `Kb = 8`): ≤ 2.5 units, float64 check 1.5e-20.

## Cost and outputs

- Each run: 336 s wall, 237 s user. The largest stage is the inverse DFTs, 200 s.
- **Memory:** 7.67 GB max RSS under the 8 GB cap. Max RSS overstates the cgroup charge, but the margin is small. A
  larger cell grid would need `--SB` or a split run.
- **Outputs** (`~/kam-data/hd11964/prod2/`, not in git):

  | file | size | sha256 |
  |---|---:|---|
  | `generators-fit-c46-rot.json.gz` | 25.7 MB | `fbde9c65…eb588` |
  | `generators-fit-c46-box.json.gz` | 25.6 MB | `35b2cd86…c81fd` |

- `load_box(path, "chi1", P=128)` reads the rotated file unchanged: its keys are monomials in the cell variables.

## Open

- The other 49 cells are not run. Owner decision: build pieces only, with a 2-cell rehearsal at the end. One cell
  takes about 6 minutes at ≤ 7.7 GB.
- The tails `T1`, `T2` of the rotated cell (5.40e-12 and 5.94e-14 for planet c) match the box run's to 4 digits.
  They are ℓ¹ sums over the modes outside `S`; the rotation changes the monomial basis, not the mode set.

## Resume

From the repository root, under the 8 GB cap, after
`export XDG_RUNTIME_DIR=/run/user/1004 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1004/bus`:

    P=applications/hd11964/validation/cover2-plan-k0.2-d2e-3.json
    systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 nice -n 10 python3 -I \
      applications/hd11964/scripts/prod2_hp.py --out=$HOME/kam-data/hd11964/prod2/generators-fit-c46-rot.json.gz \
      --plan=$P --cell=46 --check                                  # add --box for the comparison run
    python3 -I applications/hd11964/scripts/prod2_hp.py --compare=ROT.json.gz,BOX.json.gz --out=SUMMARY.json
