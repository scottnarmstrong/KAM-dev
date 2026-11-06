# N4-Witness handoff (T2-CONF, worker g2-n4)

6 November 2026, branch `inp-sjsu-g2`, shared worktree. Package brief `.drafts/g2/BRIEF-N4-Witness.md`.
Status: **targets (1)–(3) done**; optional (4) not done (reason below). No `sorry`, no `set_option`.

## Files

All in `KAM/EffectiveStability/Tube/Witness/`, namespace `KAM.EffectiveStability.Tube`. Line counts from `wc -l`.

| File | Lines | Content |
|---|---:|---|
| `Sqrt.lean` | 118 | `sqrtErr₀`, `sqrtErr₁`, `pderiv_sqrt`, `pderiv_sub_mul_self`, `le_sqrt_of_sq_le`, **`C1Close.sqrt_witness`** |
| `InvSqrt.lean` | 143 | `invSqrtErr₀`, `invSqrtErr₁`, `pderiv_one_div`, `pderiv_one_sub_mul`, **`C1Close.invSqrt_witness`** |
| `Binomial.lean` | 252 | `gbinom`, `binomTaylor`, `binomRem`, derivative identities, a fencing lemma, **`abs_binomRem_le`**, **`abs_binomRem_le_box`**, `abs_binomTerm_le_box` |
| `BinomialProd.lean` | 266 | slots (`binomSlot`, `slotMaj`, `binomSlotDu`, `slotMajDu`), `truncSet`, `tailSet`, `binomProd`, `binomTrunc`, `binomProdRem`, `tailSum`, `tailSum_eq`, `tailSum_mono`, `binomProdRem_eq`, **`abs_binomProdRem_le_box`** |
| `BinomialProdDeriv.lean` | 240 | `u`- and `φ`-derivatives: **`abs_fderiv_binomProdRem_u_le_box`**, **`abs_fderiv_binomProdRem_phi_le_box`**, `remBound₀`, `remBoundU`, `remBoundPhi`, **`binomProd_tube`** |
| `HalfPow.lean` | 64 | `rpow_half_int`, `rpow_half_sub`, `gbinom_eq_prod`, `gbinom_ratCast` (glue for the checker) |
| **Total** | **1083** | each file ≤ 1500 |

Imports: `Sqrt` imports N3's `Tube/Algebra/C1.lean` (for `pderiv` and `C1Close.intro`); the binomial files import
only Mathlib. Scratch files: `.drafts/g2/scratch/n4/` (axiom check, numeric comparison).

## Main theorems (exact statements)

`pderiv f φ a = fderiv ℝ f φ (Pi.single a 1)` is N3's abbreviation.

**(1) Square root.** The errors are `sqrtErr₀ σ₀ w₀ ρ = ρ / (σ₀ + w₀)` and
`sqrtErr₁ σ₀ w₀ ρ ρ' ω₁ = (ρ' + 2 · sqrtErr₀ σ₀ w₀ ρ · ω₁) / (2 σ₀)`.
```lean
theorem C1Close.sqrt_witness {B W : (Fin 2 → ℝ) → ℝ} {σ₀ w₀ ρ ρ' ω₁ : ℝ}
    (hBd : Differentiable ℝ B) (hWd : Differentiable ℝ W) (hσ : 0 < σ₀)
    (hB : ∀ φ, σ₀ ^ 2 ≤ B φ) (hw₀ : 0 ≤ w₀) (hW : ∀ φ, w₀ ≤ W φ)
    (hρ : ∀ φ, |B φ - W φ * W φ| ≤ ρ)
    (hρ' : ∀ φ a, |pderiv (fun φ => B φ - W φ * W φ) φ a| ≤ ρ')
    (hω : ∀ φ a, |pderiv W φ a| ≤ ω₁) :
    C1Close (fun φ => √(B φ)) W (sqrtErr₀ σ₀ w₀ ρ) (sqrtErr₁ σ₀ w₀ ρ ρ' ω₁)
```

**(2) Inverse square root.** The errors are `invSqrtErr₀ σ₀ e₀ q Y₀ = (q + e₀ Y₀) / σ₀` and
`invSqrtErr₁ σ₀ e₀ e₁ ω₁ q q' Y₀ Y₁ = (q' + e₁ Y₀ + e₀ Y₁) / σ₀ + (q + e₀ Y₀)(ω₁ + e₁) / σ₀²`.
```lean
theorem C1Close.invSqrt_witness {B W Y : (Fin 2 → ℝ) → ℝ} {σ₀ e₀ e₁ ω₁ q q' Y₀ Y₁ : ℝ}
    (H : C1Close (fun φ => √(B φ)) W e₀ e₁) (hσ : 0 < σ₀) (hB : ∀ φ, σ₀ ^ 2 ≤ B φ)
    (hω : ∀ φ a, |pderiv W φ a| ≤ ω₁) (hYd : Differentiable ℝ Y)
    (hq : ∀ φ, |1 - W φ * Y φ| ≤ q) (hq' : ∀ φ a, |pderiv (fun φ => 1 - W φ * Y φ) φ a| ≤ q')
    (hY₀ : ∀ φ, |Y φ| ≤ Y₀) (hY₁ : ∀ φ a, |pderiv Y φ a| ≤ Y₁) :
    C1Close (fun φ => 1 / √(B φ)) Y (invSqrtErr₀ σ₀ e₀ q Y₀)
      (invSqrtErr₁ σ₀ e₀ e₁ ω₁ q q' Y₀ Y₁)
```

**(3a) Binomial remainder, one variable.** Definitions:
`gbinom s m = (descPochhammer ℝ m).eval s / m!`;
`binomTaylor s M B u = Σ_{m < M} gbinom s m * B ^ (s - m) * u ^ m`;
`binomRem s M B u = (B + u) ^ s - binomTaylor s M B u`. Here `^ (s - m)` is `Real.rpow` and `u ^ m` is a
natural power.
```lean
theorem abs_binomRem_le (M : ℕ) (s : ℝ) {B r u : ℝ} (hBr : r < B) (hu : |u| ≤ r) :
    |binomRem s M B u| ≤ |gbinom s M| * max ((B - r) ^ (s - M)) ((B + r) ^ (s - M)) * |u| ^ M
theorem abs_binomRem_le_box (M : ℕ) (s : ℝ) {bmin bmax B r u : ℝ} (h1 : bmin ≤ B) (h2 : B ≤ bmax)
    (hr : r < bmin) (hu : |u| ≤ r) :
    |binomRem s M B u| ≤
      |gbinom s M| * max ((bmin - r) ^ (s - M)) ((bmax + r) ^ (s - M)) * r ^ M
```
Derivatives:
- `hasDerivAt_binomRem_u : 0 < B + u → HasDerivAt (fun u => binomRem s (M+1) B u) (s * binomRem (s-1) M B u) u`;
- `hasDerivAt_binomRem_B : 0 < B → 0 < B + u → HasDerivAt (fun B => binomRem s M B u) (s * binomRem (s-1) M B u) B`.

So the one-variable `u`- and `B`-derivative bounds are `|s|` times `abs_binomRem_le_box` at `s - 1` (orders `M - 1` and
`M`). The `max` of the two endpoints avoids a case split on the sign of the exponent.

**(3b) Three variables** (any `Fintype ι`, `DecidableEq ι`; in practice `Fin 3`). Definitions:
- `truncSet ι L = {m ∈ {0..L}^ι | Σ_j m_j ≤ L}`;
- `binomProd s B u = Π_j (B j + u j) ^ s j`;
- `binomTrunc s L B u = Σ_{m ∈ truncSet ι L} Π_j gbinom (s j) (m j) * B j ^ (s j - m j) * u j ^ m j`;
- `binomProdRem = binomProd − binomTrunc`.

The bounds are tail sums `tailSum G L = Σ_{p ∈ tailSet ι L} Π_j G j (p j)` over
`tailSet ι L = {0..L+1}^ι \ truncSet ι L`. Closed form (`tailSum_eq`):
`tailSum G L = Π_j (Σ_{m ≤ L+1} G j m) − Σ_{p ∈ truncSet} Π_j G j (p j)`.

`boxMaj s L bmin bmax r j m = slotMaj (s j) L (bmin j) (bmax j) r m`, with
- `m ≤ L`: `|binom(s,m)| · max(bmin^{s−m}, bmax^{s−m}) · r^m`;
- `m = L+1`: `|binom(s,L+1)| · max((bmin−r)^{s−L−1}, (bmax+r)^{s−L−1}) · r^{L+1}`.

The packaged statement:
```lean
theorem binomProd_tube (s : ι → ℝ) (L : ℕ) (Bf : ι → (Fin 2 → ℝ) → ℝ) {bmin bmax β : ι → ℝ}
    {r : ℝ} (hBd : ∀ j, Differentiable ℝ (Bf j)) (hr : ∀ j, r < bmin j)
    (h1 : ∀ j φ, bmin j ≤ Bf j φ) (h2 : ∀ j φ, Bf j φ ≤ bmax j)
    (hβ : ∀ j φ a, |fderiv ℝ (Bf j) φ (Pi.single a 1)| ≤ β j)
    (φ : Fin 2 → ℝ) (u : ι → ℝ) (hu : ∀ j, |u j| ≤ r) :
    binomProd s (fun j => Bf j φ) u =
        binomTrunc s L (fun j => Bf j φ) u + binomProdRem s L (fun j => Bf j φ) u ∧
      |binomProdRem s L (fun j => Bf j φ) u| ≤ remBound₀ s L bmin bmax r ∧
      DifferentiableAt ℝ (fun v => binomProdRem s L (fun j => Bf j φ) v) u ∧
      (∀ i, |fderiv ℝ (fun v => binomProdRem s L (fun j => Bf j φ) v) u (Pi.single i 1)| ≤
        remBoundU s L bmin bmax r i) ∧
      DifferentiableAt ℝ (fun φ => binomProdRem s L (fun j => Bf j φ) u) φ ∧
      (∀ a, |fderiv ℝ (fun φ => binomProdRem s L (fun j => Bf j φ) u) φ (Pi.single a 1)| ≤
        remBoundPhi s L bmin bmax r β)
```
The bounds in it:
- `remBound₀ = tailSum (boxMaj s L bmin bmax r) L`;
- `remBoundU … i = tailSum (update (boxMaj …) i (slotMajDu (s i) L (bmin i) (bmax i) r)) L`, where `slotMajDu` is
  `m · |binom(s,m)| · max(bmin^{s−m}, bmax^{s−m}) · r^{m−1}` for `m ≤ L` and
  `|s| · |binom(s−1,L)| · max((bmin−r)^{s−1−L}, (bmax+r)^{s−1−L}) · r^L` for the remainder slot;
- `remBoundPhi … β = Σ_i β_i · tailSum (update (boxMaj …) i (fun m => |s i| * slotMaj (s i − 1) L (bmin i) (bmax i) r m)) L`.

The components are also stated separately: `abs_binomProdRem_le_box`, `abs_fderiv_binomProdRem_u_le_box`,
`abs_fderiv_binomProdRem_phi_le_box`, and the exact derivatives `fderiv_binomProdRem_u` and
`fderiv_binomProdRem_phi` as slot sums.

**Glue for the checker** (`HalfPow.lean`):
- `rpow_half_sub : 0 < x → x ^ ((n:ℝ)/2 − m) = √x ^ ((n:ℤ) − 2m)`, so Taylor coefficients `B^{s−m}` are integer powers
  of the `W`/`Y` models;
- `gbinom_ratCast : gbinom (q:ℝ) m = ((Π_{i<m} (q − i) / m! : ℚ) : ℝ)`;
- `tailSum_mono` (nonnegative majorants): the checker may replace `slotMaj`/`slotMajDu` by rational upper bounds.

## Approach

- **(1)** Uses `√B − W = (B − W²)/(√B + W)`. For the derivative, `∂√B − ∂W = (∂D − 2(√B − W)∂W)/(2√B)` with
  `D = B − W²`. This needs no bound on `∂B` (see deviations).
- **(2)** Uses `1/s − Y = N/s` with `N = (1 − WY) − (s − W)Y`, and the quotient rule
  `∂(N/s) = ∂N/s − N ∂s/s²` with `|∂s| ≤ ω₁ + e₁`.
- **(3a)** Induction on `M`, generalizing `s`.
  - `binomRem s (M+1) B 0 = 0`.
  - `∂_u binomRem s (M+1) = s · binomRem (s−1) M`, by `(m+1) binom(s,m+1) = s binom(s−1,m)`.
  - The fencing lemma (`image_norm_le_of_norm_deriv_right_le_deriv_boundary`, applied on both sides of 0 through
    `τ ↦ g(−τ)`) turns `|g'| ≤ c|τ|^M` into `|g| ≤ c|t|^{M+1}/(M+1)`, which gives the exact Lagrange constant
    `|binom(s, M)|`.
  - Endpoint monotonicity of `x ↦ x^e` gives the `max`.
- **(3b)** Slot expansion.
  - Each factor `(B_j + u_j)^{s_j}` is written as `L + 2` slots: the Taylor terms `m ≤ L` and the remainder
    `binomRem s_j (L+1)` (`sum_binomSlot`).
  - `Finset.prod_univ_sum` expands the product over slot tuples. The truncation is exactly the sum over `truncSet`,
    so the remainder is the sum over `tailSet` (`binomProdRem_eq`). It is bounded slot by slot.
  - Derivatives: only factor `i` depends on `u_i` or `B_i`, so `HasFDerivAt.finsetProd` gives the same slot sum with
    the `i`-th family replaced (`prod_update_slot`, `abs_tail_update_le`).
  - The `B`-derivative of a slot is `s · slot(s − 1)` (`binom(s,m)(s − m) = s binom(s−1,m)`). The `φ`-derivative
    follows by the chain rule through `Bf j φ`.
  - The `u`-derivative of `binomProd` itself is that of `binomTrunc` (a polynomial the checker differentiates
    exactly) plus that of the remainder, so no reindexing to `s − e_i` is needed.

## Checks run (output)

- Targeted builds, each through `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Witness.<M>` for
  `M ∈ {Sqrt, InvSqrt, Binomial, BinomialProd, BinomialProdDeriv, HalfPow}`: `Build completed successfully` for every
  module.
- `g2lake env lean` on each of the six files: no output (no errors, no warnings).
- `#print axioms` (`.drafts/g2/scratch/n4/Axioms.lean`): **`[propext, Classical.choice, Quot.sound]`** for each of
  `C1Close.sqrt_witness`, `C1Close.invSqrt_witness`, `abs_binomRem_le`, `abs_binomRem_le_box`,
  `hasDerivAt_binomRem_u`, `hasDerivAt_binomRem_B`, `abs_binomProdRem_le_box`, `abs_fderiv_binomProdRem_u_le_box`,
  `abs_fderiv_binomProdRem_phi_le_box`, `binomProd_tube`, `tailSum_mono`, `tailSum_eq`, `rpow_half_sub`,
  `gbinom_ratCast`.
- `scripts/lint_sources.sh` (second run, after reflowing 9 lines over 100 characters in `Witness/`): exit 1, with
  **no finding in `KAM/EffectiveStability/Tube/Witness/`**.
  - The remaining findings are outside this package: lines over 100 characters in other packages' files (`SJSU/Ecc`,
    `Tube/Ecc`, `Tube/Trig`, …), and `KAM.lean is out of date` (the generated root does not list the new modules;
    kam-g2 or the orchestrator regenerates it).
  - Everything else passed: `check_lean_modules: PASS`, unit tests OK, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`.
- **Numeric sanity** (`.drafts/g2/scratch/n4/compare.py`, floats): `remBound₀` against phase 1's geometric tail
  (`sr4_ball_mirror.py` `Tails.tail`), with the phase-1 `B_min`, `B_max = 1.3 B_min` (assumed), `r = 2·10⁻⁶`, `L = 8`.
  - The ratio is 1.72–1.84 for half-integer exponent tuples.
  - Both bounds are exactly 0 for nonnegative integer exponents ≤ L.

## Design signals

- A default-heartbeat timeout at `isDefEq` came from building `hasFDerivAt_slotProd_u` as one term. The cause was
  higher-order unification of `h₂ ∘ (fun f => f j)` against the slot lambda.
- The fix was to give each factor an explicitly typed `have` with `h₂ := …` and `𝕜 := ℝ`. Now it elaborates
  instantly. No option was used.

## Uncertainties

- **Lagrange vs. geometric tail.** The Lagrange remainder carries `(1 − r/b_min)^{s−L−1}`. With `r/b_min ≤ 0.08` (U
  mode) and `L = 8` this is about 2. Phase 1's H tails were 1.0–1.8·10⁻²¹ against η = 3–7·10⁻²⁰, so the effect on η
  is ≤ 6 % (estimate). If ever needed, the geometric tail would need a convergent binomial series, which is not
  proved here.
- **Interface fit with N3/N5.**
  - The `u`-partials are stated as `fderiv` on `ι → ℝ` in the direction `Pi.single i 1` at fixed `B`.
  - The `φ`-partials are stated as `fderiv` on `Fin 2 → ℝ` at fixed `u`.
  - N3's tube predicate (`Trig/Tube.lean`) was not yet written when this package was done, so adapting to it is left
    to N5.
- `Sqrt.lean` depends on N3's `Algebra/C1.lean` (`pderiv`, `C1Close.intro`, `e₀_nonneg`, `e₁_nonneg`,
  `differentiable_left/right`, `abs_sub_le`, `abs_pderiv_sub_le`). A rename there breaks N4.

## Deviations from the brief

- **(1) Lower bound of `B` as `σ₀² ≤ B` with `σ₀ > 0`, not `B ≥ b₀`.** This keeps every error bound rational
  (`√b₀` never appears).
- **(1) No bound on `∂B` is needed.** The hypothesis `|∂_a B| ≤ β₁` was dropped, and `e₁ = (ρ' + 2e₀ω₁)/(2σ₀)`. To
  first order this is the same as the quotient-rule bound.
- **(1) The residual is written `B φ − W φ * W φ`**, not `W²`.
- **(2) Needs `|∂_a W| ≤ ω₁` and `σ₀² ≤ B`** in addition to (1)'s conclusion, to bound `∂√B`.
- **(3) Real exponents `s : ℝ`.** Rational `s` enters through `gbinom_ratCast`.
- **(3) Bound form.** The binomial bound is the Lagrange form, and the multivariable bookkeeping is by slot tuples, so
  the remainder slot of each factor is a Lagrange remainder rather than a geometric tail (see uncertainties).
- **(4) Not done.** `C1Close` powers by induction are optional. N3's `C1Close.mul` already gives each product step
  with explicit numbers, and the checker multiplies the trig polynomials `W`, `Y` exactly before truncating, so a
  generic `pow` lemma would add little.

## Suspected errata

None in pinned sources.
