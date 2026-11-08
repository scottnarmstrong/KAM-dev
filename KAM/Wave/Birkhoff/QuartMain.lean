/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.QuartForm

/-!
# Quartic forms: the diagonal in class `𝒜`, bounds, coefficient sets (blueprint-W `bpW:w3:quartic`)

Package W3-SETTING, blueprint label `bpW:w3:quartic`.

For `c` with `IsBirkQuartCoef`, the diagonal `P = birkQuartP` and the field `X_P = birkQuartX`:

* `birkQuart_isClassA`: `P ∈ 𝒜(𝔚)` with field `X_P` (`P` real, both analytic);
* `norm_birkQuartX_le` (`‖X_P(w)‖₊ ≤ C_* ‖w‖³`), `norm_birkQuartP_le` (`|P(w)| ≤ (C_*/4)‖w‖⁴`),
  `norm_birkQuartX_sub_le` (`‖X_P(y) - X_P(w)‖₊ ≤ 3 C_* max(‖y‖,‖w‖)² ‖y - w‖`);
* `birkQuartCoefOn S`, `isBirkQuartCoef_on`: the coefficient `𝔤·1_S` for a set `S` invariant under
  permutations and `x ↦ -x`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} {c : (Fin 4 → BirkIdx) → ℂ}

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (hc : IsBirkQuartCoef m hm c)

include ha hp hc in
/-- The diagonal `P(w) = 𝔓(w,w,w,w)`. -/
def birkQuartP (w : BirkSpace) : ℂ := birkDiag (birkQuartForm m hm ha hp hc) w

include ha hp hc in
/-- The Hamiltonian field `X_P(w) = 4 ∇𝔓(w,w,w)`. -/
def birkQuartX (w : BirkSpace) : BirkSpace := birkDiagField (birkGradML m hm ha hp hc.bound) w

include ha hp hc in
/-- (`bpW:w3:quartic`) The diagonal `P` is real and belongs to `𝒜(𝔚)`, with Hamiltonian field
`X_P(w) = 4 ∇𝔓(w,w,w)`: both are analytic on `𝔚`. -/
theorem birkQuart_isClassA :
    IsBirkClassA a p ha (by linarith) Set.univ (birkQuartP m hm ha hp hc) (birkQuartX m hm ha hp hc)
        :=
  birkDiag_isClassA (birkQuart_isSmoothing m hm ha hp hc) (birkQuartForm_rho m hm ha hp hc)

include ha hp hc in
theorem birkQuartP_rho (w : BirkSpace) :
    birkQuartP m hm ha hp hc (birkRho w) = conj (birkQuartP m hm ha hp hc w) :=
  (birkQuart_isClassA m hm ha hp hc).real w trivial

include ha hp hc in
/-- (`bpW:w3:quartic`) `|P(w)| ≤ (C_*/4) ‖w‖⁴`. -/
theorem norm_birkQuartP_le (w : BirkSpace) :
    ‖birkQuartP m hm ha hp hc w‖ ≤ waveCubicConst p / 4 * ‖w‖ ^ 4 :=
  norm_birkDiag_le (birkQuart_isSmoothing m hm ha hp hc) w

include ha hp hc in
/-- (`bpW:w3:quartic`) `‖X_P(w)‖₊ ≤ C_* ‖w‖³`. -/
theorem norm_birkQuartX_le (w : BirkSpace) :
    ‖birkQuartX m hm ha hp hc w‖ ≤ waveCubicConst p * ‖w‖ ^ 3 := by
  have h := norm_birkDiagField_le (birkQuart_isSmoothing m hm ha hp hc) w
  calc ‖birkQuartX m hm ha hp hc w‖ ≤ ((3 : ℕ) + 1) * (waveCubicConst p / 4) * ‖w‖ ^ 3 := h
    _ = _ := by push_cast; ring

include ha hp hc in
/-- (`bpW:w3:quartic`) `‖X_P(y) - X_P(w)‖₊ ≤ 3 C_* max(‖y‖,‖w‖)² ‖y - w‖`. -/
theorem norm_birkQuartX_sub_le (y w : BirkSpace) :
    ‖birkQuartX m hm ha hp hc y - birkQuartX m hm ha hp hc w‖ ≤
      3 * waveCubicConst p * max ‖y‖ ‖w‖ ^ 2 * ‖y - w‖ := by
  have h := norm_birkDiagField_sub_le (birkQuart_isSmoothing m hm ha hp hc) (by norm_num) y w
  calc ‖birkQuartX m hm ha hp hc y - birkQuartX m hm ha hp hc w‖
      ≤ ((3 : ℕ) + 1) * (3 : ℕ) * (waveCubicConst p / 4) * max ‖y‖ ‖w‖ ^ (3 - 1) * ‖y - w‖ := h
    _ = _ := by
      have e : (3 - 1 : ℕ) = 2 := rfl
      rw [e]; push_cast; ring

end

/-! ### Coefficients supported on a set -/

/-- The coefficient `𝔤 · 1_S`. -/
def birkQuartCoefOn (S : Set (Fin 4 → BirkIdx)) (x : Fin 4 → BirkIdx) : ℂ :=
  open Classical in if x ∈ S then ((birkG m hm x : ℝ) : ℂ) else 0

theorem birkG_perm (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → BirkIdx) :
    birkG m hm (fun i => x (σ i)) = birkG m hm x := by
  have key : ∀ v : Fin 4 → ℕ+, waveTriCoef m hm (v 0) (v 1) (v 2) (v 3) =
      sineQuarticCoeff (v 0) (v 1) (v 2) (v 3) / ∏ t, Real.sqrt (lam m hm (v t)) := fun v => by
    simp [waveTriCoef, waveQuartic, Fin.prod_univ_four, mul_assoc]
  unfold birkG
  have h1 := key (fun i => (x (σ i)).2)
  have h2 := key (fun i => (x i).2)
  rw [h1, h2]
  congr 1
  · exact sineQuarticCoeff_perm (fun i => (x i).2) σ
  · exact Equiv.prod_comp σ (fun t => Real.sqrt (lam m hm (x t).2))

theorem birkG_neg (x : Fin 4 → BirkIdx) : birkG m hm (birkNegPi x) = birkG m hm x := rfl

/-- The coefficient `𝔤 · 1_S` satisfies `IsBirkQuartCoef` for `S` invariant under permutations and
`x ↦ -x`. -/
theorem isBirkQuartCoef_on (S : Set (Fin 4 → BirkIdx))
    (hperm : ∀ (σ : Equiv.Perm (Fin 4)) x, x ∈ S → (fun i => x (σ i)) ∈ S)
    (hneg : ∀ x, x ∈ S → birkNegPi x ∈ S) :
    IsBirkQuartCoef m hm (birkQuartCoefOn m hm S) where
  perm σ x := by
    classical
    unfold birkQuartCoefOn
    have : (fun i => x (σ i)) ∈ S ↔ x ∈ S := by
      refine ⟨fun h => ?_, hperm σ x⟩
      have := hperm σ⁻¹ _ h
      simpa using this
    simp only [this, birkG_perm]
  conj_neg x := by
    classical
    unfold birkQuartCoefOn
    have : birkNegPi x ∈ S ↔ x ∈ S :=
      ⟨fun h => by simpa using hneg _ h, hneg x⟩
    simp only [this, birkG_neg, Complex.conj_ofReal, apply_ite (starRingEnd ℂ), map_zero]
  bound x := by
    classical
    unfold birkQuartCoefOn
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs]
    · simp

end KAM.Wave

end
