# Handoff HD11964-PROD (phase 2: the order-2 producer in the exact form of the Lean identity)

Worker kamx-hd11964, branch `hd11964-p2`. Task from the orchestrator (1 November 2026). It feeds the one-cell gate of
kamx-hd-layer. The deliverables:
- the generators χ₁, χ₂ of the Lean `F` (≥ 128-bit coefficients);
- on the worst cell (`e_c ≈ 0.6`), the sup bounds `a₁..a₅` of the five terms and the range of `F − Λ`;
- a cross-check against the phase-1 gate's order-2 rate;
- the data format for kamx-hd-layer.

Python only, new files under `applications/hd11964/scripts/`. Nothing pushed. kamx-hd-layer's branch `hd-layer` was
read only (`tf_cell.py`, `tf_slice.py`, `PackedTF/Model.lean`, `Pair.lean` at `011008a6`/`76c7b17e`).

**Status: done.** Both legs ran; the results and the data format are below.

## What is computed, exactly

The Lean identity is `chartRate_approxIntegral₂` (`KAM/Application/LambdaDrift/LieRemainderChart.lean`, commit
`3ca3c132`). For planet `i`, `k = Fin.castAdd 2 i`:
- the action is `Λ_i` and its angle `λ_i`, with `D_i = ∂/∂λ_i`;
- `h = hProd 1 ν` and `P = H∘Ψ − h = μ f∘Ψ`, with `f = |p_c + p_b|²/2 − ν_c ν_b/|q_c − q_b|`;
- the bracket is `{a, b} = Σ_j a_λ b_Λ − a_Λ b_λ + a_ξ b_η − a_η b_ξ` (Lean `pb`).

```
F_i = Λ_i + D_i χ₁ + D_i χ₂ − ½ {D_i χ₁, χ₁}                    (Lean approxIntegral₂)
{F_i, H} = −T1 − T2 + T3 + T4 − T5/2,
T1 = D_i r₁,  T2 = D_i r₂,  T3 = {D_i r₁, χ₁},  T4 = {D_i χ₂, P},  T5 = {{D_i χ₁, χ₁}, P},
r₁ = P − {χ₁, h},   r₂ = {P − ½{χ₁, h}, χ₁} − {χ₂, h}.
```

**The generators** solve the homological equations exactly on the design's mode set
`S = {0 < |k| : |k_c| ≤ Kc, |k_b| ≤ Kb}` (`Kc = 80`, `Kb = 20`; every mode is non-resonant, `|k·ω| ≥ 0.176`):
- `ω(Λ)·∂_λ χ₁ = Π_S P`;
- `ω(Λ)·∂_λ χ₂ = Π_S G₂`, with `G₂ = {P − ½ Π_S P, χ₁}`.

`ω(Λ)` is the exact Kepler frequency at the point, expanded in `Λ`. Hence `r₁ = (1 − Π_S) P` and `r₂ = (1 − Π_S) G₂`
are Fourier tails. Every term is computed as its own function — tails by projection, brackets by products — so
nothing cancels.

**The cell** is kamx-hd-layer's worst cell (`tf_cell.py`):
- centre `Λ = Λ̂ − (ρ + d)` (corner −1−1), `e_c = 0.6` (`ξ_c = √(2Γ_c)`, `η_c = 0`), `ξ_b = η_b = 0`;
- radii `h = (1.1e-3, 4e-3, 3e-2, 1.5e-2, 8e-2, 8e-2)` for `u = (dΛ_c, dΛ_b, dξ_c, dη_c, dξ_b, dη_b)`;
- the cell is `|u_j| ≤ 1`.

## Files

| file | content |
|---|---|
| `applications/hd11964/scripts/prod2.py` | float64 leg. The five terms and `F − Λ` on the cell, as Taylor (6 variables, base degree 5, so the terms are exact to degree 3) × Fourier (the 448 × 72 grid). Their cell bounds and sampled sups, the identity check, and the phase-1 cross-check. |
| `applications/hd11964/validation/prod2-cell-f64.json` | its output (52 KB) |
| `applications/hd11964/scripts/prod2_hp.py` | high-precision leg. `χ₁` (degree 4) and `χ₂` (degree 3) at 2^-184 fixed point, written as 2^-160 integers. The tails `T1`, `T2` at that precision. `load_box` expands a generator for the cell check. |
| `~/kam-data/hd11964/prod2/generators-cell-ec06.json.gz` | the generators. Not in git: regenerate with the command below. |
| `applications/hd11964/README.md` | the two scripts and their commands |

## Results (float64 leg, *estimated*: floating point, sampled)

**Identity check at the cell centre.**
- The direct rate `{F_i, H}`, with the exact gradient of `H∘Ψ` (as phase 1's `residual`), is compared with the five-term
  right side, as the sup over the 448 × 72 angle grid:

  | planet | direct rate | right side | max difference |
  |---|---:|---:|---:|
  | c | 3.287e-10 | 3.287e-10 | 2.4e-15 |
  | b | 6.882e-11 | 6.882e-11 | 1.8e-16 |

- The Lean identity, with the signs and conventions used here, holds numerically to the float64 floor of the larger
  terms.

**Cross-check against phase 1.**
- `normal_form.NormalForm(N=2)` at the same centre gives `3.2863e-10` (c) and `6.882e-11` (b). That equals the direct
  rate, since its `F^{(2)}` is the same truncated Lie series.
- The phase-1 gate's worst corner (corner −1−1, `e_c = 0.612`) had `3.70e-10` and `7.41e-11`. That is consistent: this
  centre has `e_c = 0.6`.

**Terms on the cell.**
- `a_j` is the ℓ¹ bound of the degree ≤ 3 Taylor × Fourier polynomial on the real cell, plus a Taylor-remainder
  estimate. "sup" is the sampled max over 265 cell points × the angle grid.
- `η = a₁ + a₂ + a₃ + a₄ + a₅/2` is what the bridge consumes.

| cell | planet | a₁ (T1) | a₂ (T2) | a₃ (T3) | a₄ (T4) | a₅ (T5) | η | sampled sups T1..T5 |
|---|---|---:|---:|---:|---:|---:|---:|---|
| kamx-hd-layer's `h` | c | 2.0e-9 | 2.1e-11 | 7.0e-11 | ∞ | 2.0e-6 | ∞ | 9.0e-10, 2.5e-12, 9.0e-12, 3.6e-10, 3.3e-9 |
| | b | 1.8e-11 | 4.4e-13 | 7.0e-13 | 1.2e-9 | 4.1e-9 | 3.3e-9 | 8.0e-12, 4.6e-14, 8.2e-14, 7.6e-11, 4.7e-10 |
| `h` with `(ξ_c, η_c)` radii / 4 | c | 1.7e-11 | 2.0e-13 | 6.4e-13 | 3.6e-10 | 2.7e-9 | **1.7e-9** | 4.5e-12, 3.3e-14, 1.3e-13, 1.5e-10, 1.3e-9 |
| | b | 1.7e-13 | 4.3e-15 | 6.8e-15 | 1.3e-10 | 7.0e-10 | **4.8e-10** | 4.3e-14, 6.4e-16, 1.2e-15, 5.1e-11, 2.9e-10 |
| all radii / 4 | c | 1.3e-11 | 1.3e-13 | 4.4e-13 | 2.6e-10 | 2.0e-9 | 1.3e-9 | 2.9e-12, 2.3e-14, 8.9e-14, 1.3e-10, 1.1e-9 |
| | b | 1.1e-13 | 2.8e-15 | 4.4e-15 | 7.0e-11 | 3.9e-10 | 2.7e-10 | 2.6e-14, 4.2e-16, 8.0e-16, 3.5e-11, 2.1e-10 |

The range of `F − Λ` on kamx-hd-layer's cell, sampled:
- c: `[−1.26e-5, 2.97e-5]`, with ℓ¹ bound `4.9e-5`;
- b: `[−7.41e-5, 9.01e-5]`, with ℓ¹ bound `1.4e-4`. This is phase 1's reduced-mass oscillation; it was `2.1e-4` over
  the whole region.

## Findings for the one-cell gate

1. **kamx-hd-layer's cell is too wide in `(ξ_c, η_c)` for degree-3 models of the order-2 terms.**
   - On `h = (…, 3e-2, 1.5e-2, …)` the ℓ¹ norms of `T4`, `T5` per Taylor degree do not decay. For `T5` (c) they are
     1.2e-9, 2.4e-9, 2.9e-9, 2.9e-9; the pure powers of `u_ξc` are 1.2e-9, 1.2e-9, 7e-10, 3e-10. The tails `T1`–`T3`
     grow by ×10 per degree.
   - The cause is the `e`-dependence of the Fourier decay. Mode `k` gains about `k·|dσ/dξ_c|·h` per degree, with
     `dσ/dξ_c ≈ 8.7` at `e_c = 0.6`.
   - With the `(ξ_c, η_c)` radii divided by 4 (0.0075, 0.00375), the degree norms decay by about 0.4 per degree, and
     `η_c ≈ 1.7e-9`, `η_b ≈ 4.8e-10`.
2. **The cell is not inside the region.**
   - The centre has `Γ_c = 0.01146`, against the region's `Γ_c + Γ_b ≤ 0.012` (`ξ_c ≤ 0.1549`).
   - `ξ_c + 0.03` reaches `e_c = 0.70` (`Γ_c = 0.0165`). `ξ_c + 0.0075` reaches `e_c = 0.626`, still slightly out.
   - A worst cell inside `R(d)` sits at `ξ_c ≈ 0.149`, with radius ≤ 0.006 in `ξ_c` and `η_c`.
3. **The rung closes on the smaller cell.**
   - `η_c T` at `T = 6742` (10³ yr) is `1.2e-5`. With `hi − lo ≤ 1.6e-4` (b), the drift is far below `d = 1e-3`.
   - The term-by-term `η` is about 5× the true rate. `T4` and `½ T5` partly cancel at the centre: the rate is 3.3e-10,
     against 1.7e-9. This is the expected `O(1)` loss.
4. **The tails are negligible at `Kc = 80` on the smaller cell** (`a₁`, `a₂` ≪ `a₄`, `a₅`). `Kc` could drop to about
   70. On kamx-hd-layer's cell, `a₁` grows with the Taylor degree for the reason in finding 1.

## The data format for kamx-hd-layer (through the orchestrator)

`generators-cell-ec06.json.gz` (gzipped JSON), written by `prod2_hp.py`:

| key | content |
|---|---|
| `cell` | `Lam[2]`, `xi[2]`, `eta[2]` (40 digits), `ec`, `h[6]` (exact decimals), `vars` = `dLam_c, dLam_b, dxi_c, deta_c, dxi_b, deta_b`; `x = centre + h u` |
| `model` | `nu`, `mu` (exact rationals), `P` (= `μ f`), `bracket` (Lean `pb`) |
| `S` | `Kc`, `Kb`: the mode set `0 < |k|`, `|k_c| ≤ Kc`, `|k_b| ≤ Kb` |
| `convention` | `χ(λ, u) = Σ_m u^m Σ_k c[m][k] e^{i(k_c λ_c + k_b λ_b)}`, `c[−k] = conj c[k]` |
| `OUTB` | 160: every coefficient is an integer pair `[re, im]` at scale `2^OUTB` |
| `chi1` | `{"e1,…,e6": {"kc,kb": [re, im]}}`, degree ≤ 4 (210 monomials), the half plane `k_b > 0` or (`k_b = 0`, `k_c > 0`) |
| `chi2` | the same, degree ≤ 3 (84 monomials) |
| `T1_l1`, `T2_l1` | the ℓ¹ bounds of `D_i (1 − Π_S) P`, `D_i (1 − Π_S) G₂` (i = c, b), degree ≤ 3, on the cell |
| `float64_check` | the largest difference from `prod2.py`'s float64 construction on the same grid |

- **Monomial order.** The keys are exponent tuples, so no order is assumed. `tf_cell.py`'s `mons(6, 3)` order is the
  first 84 keys.
- **`load_box(path, "chi1", P=128)`** returns `{monomial tuple: {(k_c, k_b): (re, im)}}` on the full box at scale
  `2^P`, with conjugates. That is the dict `tf_slice.py`'s `leaves` packs with `JG.pack` (keys `(k0, k1) = (k_c, k_b)`).
- **The Lean side.** `F_i` is `approxIntegral₂ (Fin.castAdd 2 i) χ₁ χ₂` with these `χ₁`, `χ₂` as functions on the
  cell. The five terms are those of `chartRate_approxIntegral₂`. `chartRate_bound` takes the term bounds, and
  `approxIntegral₂_sub_fast` gives `F_i − Λ_i`. The drift data close with `D.ok = true` by `decide +kernel`.
- **The Lean `χ` must be the exact generator; these data are the centres of its enclosures.**
  - Define `χ₁* = Π_S P / (i k·ω(Λ))` and `χ₂* = Π_S G₂* / (i k·ω(Λ))` by exact Fourier projection of
    `μ f∘Ψ`. Then `r₁ = (1 − Π_S) P` and `r₂ = (1 − Π_S) G₂*` exactly, and the data here are their Taylor
    polynomials at the cell centre: degree 4 for `χ₁`, degree 3 for `χ₂`.
  - If the polynomial itself were used as `χ₁` in Lean, `r₁` would also contain the `S`-part of `P`'s Taylor terms
    beyond degree 4. Measured (`prod2.py` machinery, base degree 5), the degree-5 part of `D_c Π_S P` has ℓ¹ norm
    `8.6e-7` on the smaller cell and `2.4e-4` on kamx-hd-layer's cell, against the order-2 rate of about `1e-9`.
  - So the cell check needs Taylor × Fourier enclosures of `χ*` (centre polynomial plus remainder radius), built
    from `P`'s model with its remainder, `Π_S` and the `inv` of `k·ω`. It cannot treat the polynomial as `χ`.
- **Rescaling to a smaller cell.** For a cell with the same centre and smaller radii, multiply the coefficient of
  `u^m` by `Π_j (h'_j / h_j)^{m_j}`. To move the centre, rerun with `--ec`, or change `cell_centre` / the `Lc`
  lines.

## Results (high-precision leg)

`prod2_hp.py --N1=448 --N2=72 --Kc=80 --Kb=20 --DJ=4 --FB=184 --OUTB=160 --check`, under the 8 GB cap:

| stage | wall |
|---|---:|
| charts (mpmath, 256 bits, 448 + 72 angles) | 9.3 s |
| `P` on the grid (integer jets, degree 4, 210 monomials) | 24.4 s |
| exact DFT of `P` (all 448 × 37 modes) | 41.7 s |
| `χ₁` (mode by mode, `1/(k·ω)` series) | 0.8 s |
| six exact inverse DFTs (`A`, `∂_λ A`, `χ₁`, `∂_λ χ₁`) | 172 s |
| `G₂ = {A, χ₁}` on the grid | 15.1 s |
| exact DFT of `G₂`, `χ₂` | 13.2 s |
| total | **291 s** wall, 282 s user, **6.7 GB** peak |

- **Output.** `~/kam-data/hd11964/prod2/generators-cell-ec06.json.gz`: 13,273,511 bytes, SHA-256 `c0ed560ab5d6f62e
  64601ce14edfab159ee974cec15560b754b20c4f276901e1`.
- **Accuracy against the float64 construction** (same grid, `prod2.py`'s `solve`/`bracket`):

  | generator | max \|difference\| | max \|coefficient\| | relative |
  |---|---:|---:|---:|
  | `χ₁` | `2.2e-20` | `2.45e-5` | `9e-16` |
  | `χ₂` | `1.5e-23` | `9.0e-9` | `1.7e-15` |

  These differences are the float64 errors. The high-precision values are exact to a few units of `2^-184` per
  operation. The grid's aliasing (448 × 72 at `e_c = 0.6`) is estimated below `2^-130` of the function: the
  `k_c`-decay is `e^{−0.30|k|}` with polynomial factors from the Taylor degree, and the `k_b`-decay is `0.116^{|k|}`.
- **The tails at high precision** (ℓ¹, degree ≤ 3, kamx-hd-layer's cell), which match the float64 leg:

  | | c | b |
  |---|---:|---:|
  | `T1 = D_i (1 − Π_S) P` | `2.158e-10` | `1.923e-12` |
  | `T2 = D_i (1 − Π_S) G₂` | `2.318e-12` | `4.773e-14` |

  The float64 values are `2.1e-10`, `1.9e-12`, `2.3e-12`, `4.8e-14`.
- **`T3`–`T5` were not recomputed at high precision.** They are brackets of `O(μ)` and `O(μ²)` functions with no
  cancellation, so float64 gives them to about `1e-12` relative, far below the `O(1)` the bound needs. A
  high-precision run would cost about 3 min per bracket with the same code: 8 brackets for both planets.

## Checks

- `prod2.py` (float64): 71 s wall, 2.6 GB. The identity check and the phase-1 cross-check are in the tables above.
- `prod2_hp.py`: the small grid (96 × 32, degree 3) cross-check gives `4.8e-20` and `2.7e-23`. The full run is
  above.
- No Lean in this task. The Lean follow-ups of AUDIT-HD11964-P2B-1 are in `9262b215`:
  - `LieCalculus.lean`: `differentiableOn_approxIntegral₂`, the public linearity rules, and `pb_eq_sum`;
  - all of them use only the standard axioms;
  - built with no warning.

## Owner questions

1. **The cell.** kamx-hd-layer's worst cell is outside `R(d)` and too wide in `(ξ_c, η_c)` for degree-3 models
   (findings 1–2).
   - Suggested: centre `ξ_c ≈ 0.149` (inside `ΣΓ ≤ 0.012`), radii `(ξ_c, η_c) ≤ (0.006, 0.006)`, the others as now.
   - This is kamx-hd-layer's decision. The generators rescale; a new centre needs a rerun (5 min).
2. **`χ` in Lean.** The Lean `F` must use the exact generators `χ*` and enclose them (above). Using the polynomial
   is not viable. That fixes part of the cell check's design.
3. **Data in git.** The 13 MB generator file is in `~/kam-data`, not in git. Each future cell gets its own file.
   Taken: do not commit generated data.

## Resume after reboot

- **Committed:**
  - `2cb2fdaf`: the float64 leg and its output;
  - `06180501`: the high-precision script and README;
  - `9262b215`: the P2B follow-ups;
  - this handoff's commit.
- **Data:** `~/kam-data/hd11964/prod2/generators-cell-ec06.json.gz` survives the reboot, under `/home`.
- **To regenerate:**
  1. `prod2.py OUT.json`: 1 min, 2.6 GB.
  2. `prod2_hp.py --out=… --check`: 5 min, 6.7 GB.
  Both run from the repository root under `systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 nice -n 10
  python3 -I`.
- **Open:**
  - the data handed to kamx-hd-layer through the orchestrator;
  - the cell choice (owner question 1).
