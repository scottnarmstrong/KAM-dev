/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The parameters of the applications of G1 and G2, and the smallness consequences

Blueprint Part 4: Definition `bp:p4:parameters` (its claims) and Lemma `bp:p4:smallness`.

The constants (`sigmaK`, ..., `A0`-`A4`, `lamStar`, `cT`, `etaStar`, `cStar`) are defined in
`KAM/Head/Defs.lean`. This module proves, once and for all, the inequalities about them; later
modules never unfold a constant. The module needs the constants `gc` of the frozen G1 and G2 only
through their positivity (`GConsts.Pos`).

* `KAM.Head.parameters` is the list of claims of Definition `bp:p4:parameters`: the side
  conditions of the three frozen applications, the values `σ_K - μ = σ_B - μ = 2` and
  `σ_T - μ = 4 L₊`, the identity `δ_*² / (2 L₊ c̄) = 1 / (2 L₊ F₂)` for the second entry of `c_*`,
  and the positivity of `λ_*`, `c_T`, `η_*(δ)`, `A₀`-`A₄` and `c_*`.
* `KAM.Head.smallness` is Lemma `bp:p4:smallness`, items (s1)-(s7). Each item has the exact shape
  its consumer needs.

The proofs go through the namespace `KAM.Head.Parameters`:

* a pack of positivity and monotonicity lemmas for the constants (`Fconst_pos`, `Mconst_pos`,
  `cT_pos`, `etaStar_pos`, `etaStar_mono`, ...);
* `cStar_pos` and the eight inequalities `cStar_le_1`, ..., `cStar_le_8` (one for each entry
  of the minimum defining `c_*`);
* the item lemmas `smallness_s1`, ..., `smallness_s7`, each reduced to the abstract inequality
  `mul_le_of_le_cStar` (`ε ≤ c x` and `c ≤ P / Q` give `Q ε ≤ P x`).
-/

@[expose] public section

namespace KAM.Head

namespace Parameters

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ} {gc : GConsts}

/-! ### Positivity of the elementary constants -/

theorem cbar_pos (n : ℕ) : 0 < cbar n := by
  rw [cbar_eq]
  norm_num

theorem Lplus_pos (Lh : ℝ) : 0 < Lplus Lh := one_pos.trans_le (one_le_Lplus Lh)

theorem Fconst_pos (n : ℕ) (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (j : ℕ) : 0 < Fconst n s₀ r₀ j :=
  div_pos (cbar_pos n) (pow_pos (deltaStar_pos hs₀ hr₀) j)

theorem Hconst_nonneg (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (j : ℕ) : 0 ≤ Hconst s₀ r₀ B h j :=
  div_nonneg (mul_nonneg (cbar_pos n).le (hBound_nonneg h B r₀))
    (pow_nonneg (deltaStar_pos hs₀ hr₀).le j)

theorem Mconst_pos (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) : 0 < Mconst s₀ r₀ B h :=
  div_pos (mul_pos (cbar_pos n) (add_pos_of_nonneg_of_pos (hBound_nonneg h B r₀) one_pos))
    (pow_pos (deltaStar_pos hs₀ hr₀) 3)

theorem Winf_nonneg (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) : 0 ≤ Winf s₀ r₀ B h :=
  Hconst_nonneg hs₀ hr₀ 1

theorem LambdaG_nonneg (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) : 0 ≤ LambdaG s₀ r₀ B h :=
  le_max_of_le_left (Hconst_nonneg hs₀ hr₀ 2)

theorem lamStar_pos (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) : 0 < lamStar Lh s₀ r₀ :=
  div_pos (deltaStar_pos hs₀ hr₀) (mul_pos four_pos (Lplus_pos Lh))

theorem cT_pos (hn : 2 ≤ n) (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) : 0 < cT s₀ r₀ B h := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hM := Mconst_pos (B := B) (h := h) hs₀ hr₀
  have hW := Winf_nonneg (B := B) (h := h) hs₀ hr₀
  unfold cT
  positivity

/-- `n ≤ c_T`, since `c_T ≥ 304 n³`. -/
theorem natCast_le_cT (hn : 2 ≤ n) (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) :
    (n : ℝ) ≤ cT s₀ r₀ B h := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hM := Mconst_pos (B := B) (h := h) hs₀ hr₀
  have hW := Winf_nonneg (B := B) (h := h) hs₀ hr₀
  have h3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := le_self_pow₀ hn1 (by norm_num)
  have h4 : (1 : ℝ) ≤ Mconst s₀ r₀ B h + Winf s₀ r₀ B h + 1 := by linarith
  have h5 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  unfold cT
  calc (n : ℝ) ≤ (n : ℝ) ^ 3 := h3
    _ ≤ 304 * (n : ℝ) ^ 3 * 1 := by linarith
    _ ≤ 304 * (n : ℝ) ^ 3 * (Mconst s₀ r₀ B h + Winf s₀ r₀ B h + 1) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

/-! ### The function `η_*` -/

theorem etaStar_pos (hn : 2 ≤ n) (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) {δ : ℝ} (hδ : 0 < δ) :
    0 < etaStar s₀ r₀ B h Lh δ :=
  lt_min (muParam_pos hs₀ hr₀)
    (div_pos (pow_pos hδ 2)
      (mul_pos (mul_pos (by norm_num) (cT_pos hn hs₀ hr₀)) (Lplus_pos Lh)))

theorem etaStar_le_muParam (s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (Lh δ : ℝ) :
    etaStar s₀ r₀ B h Lh δ ≤ muParam s₀ r₀ :=
  min_le_left _ _

theorem etaStar_le_div (s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (Lh δ : ℝ) :
    etaStar s₀ r₀ B h Lh δ ≤ δ ^ 2 / (16 * cT s₀ r₀ B h * Lplus Lh) :=
  min_le_right _ _

theorem etaStar_mono (hn : 2 ≤ n) (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) {δ δ' : ℝ} (hδ : 0 ≤ δ)
    (hδδ' : δ ≤ δ') : etaStar s₀ r₀ B h Lh δ ≤ etaStar s₀ r₀ B h Lh δ' := by
  have hden : 0 ≤ 16 * cT s₀ r₀ B h * Lplus Lh :=
    (mul_pos (mul_pos (by norm_num) (cT_pos hn hs₀ hr₀)) (Lplus_pos Lh)).le
  unfold etaStar
  exact min_le_min le_rfl (div_le_div_of_nonneg_right (pow_le_pow_left₀ hδ hδδ' 2) hden)

/-! ### Positivity of `σ_K, σ_B, σ_T` and of `A₀, ..., A₄` -/

theorem sigmaK_pos (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) : 0 < sigmaK s₀ r₀ :=
  add_pos two_pos (muParam_pos hs₀ hr₀)

theorem sigmaB_pos (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) : 0 < sigmaB s₀ r₀ :=
  add_pos two_pos (muParam_pos hs₀ hr₀)

theorem sigmaT_pos (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) : 0 < sigmaT Lh s₀ r₀ :=
  add_pos (mul_pos four_pos (Lplus_pos Lh)) (muParam_pos hs₀ hr₀)

theorem A0_pos (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hgc : gc.Pos) : 0 < A0 n τ s₀ r₀ gc := by
  have hs := stripWidth_pos hs₀
  exact div_pos (mul_pos (mul_pos two_pos hgc.C21_pos) (Fconst_pos n hs₀ hr₀ 1))
    (Real.rpow_pos_of_pos (by positivity) _)

theorem A1_pos (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hgc : gc.Pos) :
    0 < A1 τ s₀ r₀ B h Lh gc := by
  have hs := stripWidth_pos hs₀
  have hA0 := A0_pos (n := n) (τ := τ) hs₀ hr₀ hgc
  have hH3 := Hconst_nonneg (B := B) (h := h) hs₀ hr₀ 3
  have hF2 := Fconst_pos n hs₀ hr₀ 2
  have hL := Lplus_pos Lh
  unfold A1
  positivity

theorem A2_pos (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hgc : gc.Pos) :
    0 < A2 τ s₀ r₀ B h Lh gc := by
  have hs := stripWidth_pos hs₀
  have hA1 := A1_pos (τ := τ) (B := B) (h := h) (Lh := Lh) hs₀ hr₀ hgc
  have hσ := sigmaK_pos hs₀ hr₀
  have hC22 := hgc.C22_pos
  exact div_pos (mul_pos (mul_pos (by linarith) hC22) hA1)
    (Real.rpow_pos_of_pos (by positivity) _)

theorem A3_pos (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hgc : gc.Pos) :
    0 < A3 τ s₀ r₀ B h Lh gc :=
  lt_max_of_lt_left (A2_pos hs₀ hr₀ hgc)

theorem A4_pos (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hn : 2 ≤ n) (hgc : gc.Pos) :
    0 < A4 n τ s₀ r₀ gc := by
  have hs := stripWidth_pos hs₀
  have hA0 := A0_pos (n := n) (τ := τ) hs₀ hr₀ hgc
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold A4
  positivity

/-! ### The eight entries of `c_*` -/

theorem cStar_le_1 : cStar τ s₀ r₀ B h Lh gc ≤ 1 :=
  min_le_left _ _

theorem cStar_le_2 :
    cStar τ s₀ r₀ B h Lh gc ≤ deltaStar s₀ r₀ ^ 2 / (2 * Lplus Lh * cbar n) :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem cStar_le_3 :
    cStar τ s₀ r₀ B h Lh gc ≤
      (stripWidth s₀ / 4) ^ (4 * τ) / (2 * gc.C11 * Fconst n s₀ r₀ 1) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem cStar_le_4 :
    cStar τ s₀ r₀ B h Lh gc ≤
      etaStar s₀ r₀ B h Lh (stripWidth s₀ / 32) / A0 n τ s₀ r₀ gc :=
  (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))

theorem cStar_le_5 :
    cStar τ s₀ r₀ B h Lh gc ≤ (3 * stripWidth s₀ / 32) ^ (4 * τ) /
      (2 * gc.C12 * A1 τ s₀ r₀ B h Lh gc * lamStar Lh s₀ r₀) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))

theorem cStar_le_6 :
    cStar τ s₀ r₀ B h Lh gc ≤ gc.cG * (stripWidth s₀ / 16) ^ (2 * τ) /
      (2 * A0 n τ s₀ r₀ gc +
        gc.C22 * A1 τ s₀ r₀ B h Lh gc * lamStar Lh s₀ r₀ / (3 * stripWidth s₀ / 32) ^ (2 * τ)) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))

theorem cStar_le_7 :
    cStar τ s₀ r₀ B h Lh gc ≤
      1 / (4 * (A3 τ s₀ r₀ B h Lh gc * LambdaG s₀ r₀ B h + A4 n τ s₀ r₀ gc)) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))))

theorem cStar_le_8 : cStar τ s₀ r₀ B h Lh gc ≤ 1 / (2 * A0 n τ s₀ r₀ gc) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))))))

theorem cStar_pos (hn : 2 ≤ n) (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hgc : gc.Pos) :
    0 < cStar τ s₀ r₀ B h Lh gc := by
  have hs := stripWidth_pos hs₀
  have hA0 := A0_pos (n := n) (τ := τ) hs₀ hr₀ hgc
  have hA1 := A1_pos (τ := τ) (B := B) (h := h) (Lh := Lh) hs₀ hr₀ hgc
  have hA3 := A3_pos (τ := τ) (B := B) (h := h) (Lh := Lh) hs₀ hr₀ hgc
  have hA4 := A4_pos (τ := τ) hs₀ hr₀ hn hgc
  have hΛ := LambdaG_nonneg (B := B) (h := h) hs₀ hr₀
  have hlam := lamStar_pos (Lh := Lh) hs₀ hr₀
  have hF1 := Fconst_pos n hs₀ hr₀ 1
  have hL := Lplus_pos Lh
  have hδ := deltaStar_pos hs₀ hr₀
  have hC11 := hgc.C11_pos
  have hC12 := hgc.C12_pos
  have hC22 := hgc.C22_pos
  have hcG := hgc.cG_pos
  have hr4 : 0 < (stripWidth s₀ / 4) ^ (4 * τ) := Real.rpow_pos_of_pos (by positivity) _
  have hr332 : 0 < (3 * stripWidth s₀ / 32) ^ (4 * τ) := Real.rpow_pos_of_pos (by positivity) _
  have hr332' : 0 < (3 * stripWidth s₀ / 32) ^ (2 * τ) := Real.rpow_pos_of_pos (by positivity) _
  have hr16 : 0 < (stripWidth s₀ / 16) ^ (2 * τ) := Real.rpow_pos_of_pos (by positivity) _
  have hη := etaStar_pos (B := B) (h := h) (Lh := Lh) hn hs₀ hr₀ (δ := stripWidth s₀ / 32)
    (by positivity)
  unfold cStar
  refine lt_min one_pos (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))))))
  · exact div_pos (pow_pos hδ 2) (mul_pos (mul_pos two_pos hL) (cbar_pos n))
  · exact div_pos hr4 (mul_pos (mul_pos two_pos hC11) hF1)
  · exact div_pos hη hA0
  · exact div_pos hr332 (mul_pos (mul_pos (mul_pos two_pos hC12) hA1) hlam)
  · exact div_pos (mul_pos hcG hr16)
      (add_pos (mul_pos two_pos hA0) (div_pos (mul_pos (mul_pos hC22 hA1) hlam) hr332'))
  · exact one_div_pos.2 (mul_pos four_pos (add_pos_of_nonneg_of_pos (mul_nonneg hA3.le hΛ) hA4))
  · exact one_div_pos.2 (mul_pos two_pos hA0)

/-- The second entry of `c_*`: `δ_*² / (2 L₊ c̄) = 1 / (2 L₊ F₂)`. -/
theorem deltaStar_sq_div_eq (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) :
    deltaStar s₀ r₀ ^ 2 / (2 * Lplus Lh * cbar n) = 1 / (2 * Lplus Lh * Fconst n s₀ r₀ 2) := by
  have hδ := (deltaStar_pos hs₀ hr₀).ne'
  have hc := (cbar_pos n).ne'
  have hL := (Lplus_pos Lh).ne'
  unfold Fconst
  field_simp

/-! ### The smallness lemmas -/

section Smallness

variable {ε γ : ℝ}

/-- The abstract form of every item of `bp:p4:smallness`: `ε ≤ c x` and `c ≤ P / Q` give
`Q ε ≤ P x`. -/
theorem mul_le_of_le_cStar {ε c P Q x : ℝ} (hQ : 0 < Q) (hx : 0 ≤ x) (hε : ε ≤ c * x)
    (hc : c ≤ P / Q) : Q * ε ≤ P * x := by
  have h1 : c * Q ≤ P := (le_div_iff₀ hQ).1 hc
  calc Q * ε ≤ Q * (c * x) := mul_le_mul_of_nonneg_left hε hQ.le
    _ = (c * Q) * x := by ring
    _ ≤ P * x := mul_le_mul_of_nonneg_right h1 hx

/-- Under `(SA)`, `ε ≤ c_*` (since `γ ≤ 1`). -/
theorem eps_le_cStar (hn : 2 ≤ n) (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) : ε ≤ cStar τ s₀ r₀ B h Lh gc := by
  have hc := cStar_pos (τ := τ) (B := B) (h := h) (Lh := Lh) hn hs₀ hr₀ hgc
  have hγ4 : γ ^ 4 ≤ 1 := pow_le_one₀ hSA.gamma_pos.le hSA.gamma_le
  exact hSA.eps_le.trans (mul_le_of_le_one_right hc.le hγ4)

/-- Under `(SA)`, `η₀ ≤ A₀ c_* γ²`. -/
theorem eta0_le_mul (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    eta0 n τ s₀ r₀ gc ε γ ≤ A0 n τ s₀ r₀ gc * cStar τ s₀ r₀ B h Lh gc * γ ^ 2 := by
  have hA0 := A0_pos (n := n) (τ := τ) hs₀ hr₀ hgc
  have hγ2 : 0 < γ ^ 2 := pow_pos hSA.gamma_pos 2
  unfold eta0
  rw [div_le_iff₀ hγ2]
  calc A0 n τ s₀ r₀ gc * ε ≤ A0 n τ s₀ r₀ gc * (cStar τ s₀ r₀ B h Lh gc * γ ^ 4) :=
        mul_le_mul_of_nonneg_left hSA.eps_le hA0.le
    _ = A0 n τ s₀ r₀ gc * cStar τ s₀ r₀ B h Lh gc * γ ^ 2 * γ ^ 2 := by ring

/-- `η₀ ≤ X γ²` as soon as `A₀ c_* ≤ X`. -/
theorem eta0_le_of (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) {X : ℝ}
    (hX : A0 n τ s₀ r₀ gc * cStar τ s₀ r₀ B h Lh gc ≤ X) :
    eta0 n τ s₀ r₀ gc ε γ ≤ X * γ ^ 2 :=
  (eta0_le_mul hs₀ hr₀ hgc hSA).trans
    (mul_le_mul_of_nonneg_right hX (pow_pos hSA.gamma_pos 2).le)

theorem A0_mul_cStar_le_etaStar (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hgc : gc.Pos) :
    A0 n τ s₀ r₀ gc * cStar τ s₀ r₀ B h Lh gc ≤ etaStar s₀ r₀ B h Lh (stripWidth s₀ / 32) := by
  have hA0 := A0_pos (n := n) (τ := τ) hs₀ hr₀ hgc
  have := (le_div_iff₀ hA0).1 (cStar_le_4 (τ := τ) (B := B) (h := h) (Lh := Lh) (gc := gc))
  linarith

theorem A0_mul_cStar_le_half (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hgc : gc.Pos) :
    A0 n τ s₀ r₀ gc * cStar τ s₀ r₀ B h Lh gc ≤ 1 / 2 := by
  have hA0 := A0_pos (n := n) (τ := τ) hs₀ hr₀ hgc
  have := (le_div_iff₀ (mul_pos two_pos hA0)).1
    (cStar_le_8 (τ := τ) (B := B) (h := h) (Lh := Lh) (gc := gc))
  linarith

theorem smallness_s1 (hD : Data τ s₀ r₀ B h Lh) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    ε ≤ 1 ∧ Lplus Lh * Fconst n s₀ r₀ 2 * ε ≤ 1 / 2 := by
  obtain ⟨hn, -, hs₀, hr₀, -⟩ := hD
  have hεc := eps_le_cStar hn hs₀ hr₀ hgc hSA
  refine ⟨hεc.trans cStar_le_1, ?_⟩
  have hQ : 0 < 2 * Lplus Lh * Fconst n s₀ r₀ 2 :=
    mul_pos (mul_pos two_pos (Lplus_pos Lh)) (Fconst_pos n hs₀ hr₀ 2)
  have hε : ε ≤ cStar τ s₀ r₀ B h Lh gc * 1 := by rw [mul_one]; exact hεc
  have := mul_le_of_le_cStar hQ zero_le_one hε
    (deltaStar_sq_div_eq (Lh := Lh) (n := n) hs₀ hr₀ ▸ cStar_le_2 (τ := τ) (B := B) (h := h)
      (Lh := Lh) (gc := gc))
  linarith

theorem smallness_s2 (hD : Data τ s₀ r₀ B h Lh) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    gc.C11 * (Fconst n s₀ r₀ 1 * ε) / (γ ^ 4 * (stripWidth s₀ / 4) ^ (4 * τ)) ≤ 1 / 2 := by
  obtain ⟨hn, -, hs₀, hr₀, -⟩ := hD
  have hs := stripWidth_pos hs₀
  have hγ := hSA.gamma_pos
  have hr4 : 0 < (stripWidth s₀ / 4) ^ (4 * τ) := Real.rpow_pos_of_pos (by positivity) _
  have hQ : 0 < 2 * gc.C11 * Fconst n s₀ r₀ 1 :=
    mul_pos (mul_pos two_pos hgc.C11_pos) (Fconst_pos n hs₀ hr₀ 1)
  have := mul_le_of_le_cStar hQ (pow_pos hγ 4).le hSA.eps_le
    (cStar_le_3 (τ := τ) (B := B) (h := h) (Lh := Lh) (gc := gc))
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem smallness_s3 (hD : Data τ s₀ r₀ B h Lh) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    eta0 n τ s₀ r₀ gc ε γ ≤ etaStar s₀ r₀ B h Lh (stripWidth s₀ / 32) ∧
      etaStar s₀ r₀ B h Lh (stripWidth s₀ / 32) ≤ etaStar s₀ r₀ B h Lh (stripWidth s₀ / 16) ∧
      eta0 n τ s₀ r₀ gc ε γ ≤ muParam s₀ r₀ ∧
      16 * n * eta0 n τ s₀ r₀ gc ε γ / stripWidth s₀ ≤ 1 / 2 := by
  obtain ⟨hn, -, hs₀, hr₀, -⟩ := hD
  have hs := stripWidth_pos hs₀
  have hγ := hSA.gamma_pos
  have hγ2 : γ ^ 2 ≤ 1 := pow_le_one₀ hγ.le hSA.gamma_le
  have hη0 : 0 ≤ etaStar s₀ r₀ B h Lh (stripWidth s₀ / 32) :=
    (etaStar_pos (B := B) (h := h) (Lh := Lh) hn hs₀ hr₀ (by positivity)).le
  have h1 : eta0 n τ s₀ r₀ gc ε γ ≤ etaStar s₀ r₀ B h Lh (stripWidth s₀ / 32) :=
    (eta0_le_of hs₀ hr₀ hgc hSA (A0_mul_cStar_le_etaStar hs₀ hr₀ hgc)).trans
      (mul_le_of_le_one_right hη0 hγ2)
  refine ⟨h1, etaStar_mono hn hs₀ hr₀ (by positivity) (by linarith), h1.trans
    (etaStar_le_muParam _ _ _ _ _ _), ?_⟩
  have hcT := cT_pos (B := B) (h := h) hn hs₀ hr₀
  have hL := Lplus_pos Lh
  have hden : 0 < 16 * cT s₀ r₀ B h * Lplus Lh := by positivity
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : eta0 n τ s₀ r₀ gc ε γ * (16 * cT s₀ r₀ B h * Lplus Lh) ≤ (stripWidth s₀ / 32) ^ 2 :=
    (le_div_iff₀ hden).1 (h1.trans (etaStar_le_div _ _ _ _ _ _))
  have hns : (n : ℝ) * stripWidth s₀ ≤ cT s₀ r₀ B h * Lplus Lh :=
    calc (n : ℝ) * stripWidth s₀ ≤ n * 1 :=
          mul_le_mul_of_nonneg_left (stripWidth_le_one s₀) hnn
      _ ≤ cT s₀ r₀ B h := by rw [mul_one]; exact natCast_le_cT hn hs₀ hr₀
      _ ≤ cT s₀ r₀ B h * Lplus Lh := le_mul_of_one_le_right hcT.le (one_le_Lplus Lh)
  rw [div_le_iff₀ hs]
  refine le_of_mul_le_mul_right ?_ hden
  have e1 : 16 * (n : ℝ) * eta0 n τ s₀ r₀ gc ε γ * (16 * cT s₀ r₀ B h * Lplus Lh) ≤
      16 * n * (stripWidth s₀ / 32) ^ 2 :=
    calc _ = 16 * (n : ℝ) * (eta0 n τ s₀ r₀ gc ε γ * (16 * cT s₀ r₀ B h * Lplus Lh)) := by ring
      _ ≤ 16 * n * (stripWidth s₀ / 32) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  have e2 : (n : ℝ) * stripWidth s₀ * stripWidth s₀ ≤
      cT s₀ r₀ B h * Lplus Lh * stripWidth s₀ := mul_le_mul_of_nonneg_right hns hs.le
  have e3 : 0 ≤ cT s₀ r₀ B h * Lplus Lh * stripWidth s₀ := by positivity
  linarith

theorem smallness_s4 (hD : Data τ s₀ r₀ B h Lh) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    gc.C12 * (A1 τ s₀ r₀ B h Lh gc * lamStar Lh s₀ r₀ * ε) /
      (γ ^ 4 * (3 * stripWidth s₀ / 32) ^ (4 * τ)) ≤ 1 / 2 := by
  obtain ⟨hn, -, hs₀, hr₀, -⟩ := hD
  have hs := stripWidth_pos hs₀
  have hγ := hSA.gamma_pos
  have hr : 0 < (3 * stripWidth s₀ / 32) ^ (4 * τ) := Real.rpow_pos_of_pos (by positivity) _
  have hQ : 0 < 2 * gc.C12 * A1 τ s₀ r₀ B h Lh gc * lamStar Lh s₀ r₀ :=
    mul_pos (mul_pos (mul_pos two_pos hgc.C12_pos) (A1_pos hs₀ hr₀ hgc)) (lamStar_pos hs₀ hr₀)
  have := mul_le_of_le_cStar hQ (pow_pos hγ 4).le hSA.eps_le
    (cStar_le_5 (τ := τ) (B := B) (h := h) (Lh := Lh) (gc := gc))
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem smallness_s5 (hD : Data τ s₀ r₀ B h Lh) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    (2 * A0 n τ s₀ r₀ gc +
        gc.C22 * A1 τ s₀ r₀ B h Lh gc * lamStar Lh s₀ r₀ / (3 * stripWidth s₀ / 32) ^ (2 * τ)) *
      (ε / γ ^ 2) ≤ gc.cG * γ ^ 2 * (stripWidth s₀ / 16) ^ (2 * τ) := by
  obtain ⟨hn, -, hs₀, hr₀, -⟩ := hD
  have hs := stripWidth_pos hs₀
  have hγ := hSA.gamma_pos
  have hγ2 : 0 < γ ^ 2 := pow_pos hγ 2
  have hr : 0 < (3 * stripWidth s₀ / 32) ^ (2 * τ) := Real.rpow_pos_of_pos (by positivity) _
  have hQ : 0 < 2 * A0 n τ s₀ r₀ gc +
      gc.C22 * A1 τ s₀ r₀ B h Lh gc * lamStar Lh s₀ r₀ / (3 * stripWidth s₀ / 32) ^ (2 * τ) :=
    add_pos (mul_pos two_pos (A0_pos hs₀ hr₀ hgc))
      (div_pos (mul_pos (mul_pos hgc.C22_pos (A1_pos hs₀ hr₀ hgc)) (lamStar_pos hs₀ hr₀)) hr)
  have hε : ε / γ ^ 2 ≤ cStar τ s₀ r₀ B h Lh gc * γ ^ 2 := by
    rw [div_le_iff₀ hγ2]
    calc ε ≤ cStar τ s₀ r₀ B h Lh gc * γ ^ 4 := hSA.eps_le
      _ = cStar τ s₀ r₀ B h Lh gc * γ ^ 2 * γ ^ 2 := by ring
  have := mul_le_of_le_cStar hQ hγ2.le hε
    (cStar_le_6 (τ := τ) (B := B) (h := h) (Lh := Lh) (gc := gc))
  linarith

theorem smallness_s6 (hD : Data τ s₀ r₀ B h Lh) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    (A3 τ s₀ r₀ B h Lh gc * LambdaG s₀ r₀ B h + A4 n τ s₀ r₀ gc) * (ε / γ ^ 4) ≤ 1 / 4 := by
  obtain ⟨hn, -, hs₀, hr₀, -⟩ := hD
  have hγ4 : 0 < γ ^ 4 := pow_pos hSA.gamma_pos 4
  have hQ : 0 < 4 * (A3 τ s₀ r₀ B h Lh gc * LambdaG s₀ r₀ B h + A4 n τ s₀ r₀ gc) :=
    mul_pos four_pos (add_pos_of_nonneg_of_pos
      (mul_nonneg (A3_pos hs₀ hr₀ hgc).le (LambdaG_nonneg hs₀ hr₀)) (A4_pos hs₀ hr₀ hn hgc))
  have hε : ε / γ ^ 4 ≤ cStar τ s₀ r₀ B h Lh gc * 1 := by
    rw [div_le_iff₀ hγ4, mul_one]
    exact hSA.eps_le
  have := mul_le_of_le_cStar hQ zero_le_one hε
    (cStar_le_7 (τ := τ) (B := B) (h := h) (Lh := Lh) (gc := gc))
  linarith

theorem smallness_s7 (hD : Data τ s₀ r₀ B h Lh) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    eta0 n τ s₀ r₀ gc ε γ ≤ γ ^ 2 / 2 ∧ γ ^ 2 / 2 ≤ min γ 1 / 2 := by
  obtain ⟨hn, -, hs₀, hr₀, -⟩ := hD
  have hγ := hSA.gamma_pos
  refine ⟨?_, ?_⟩
  · have := eta0_le_of hs₀ hr₀ hgc hSA (A0_mul_cStar_le_half hs₀ hr₀ hgc)
    linarith
  · have : γ ^ 2 ≤ min γ 1 := le_min (pow_le_of_le_one hγ.le hSA.gamma_le two_ne_zero)
      (pow_le_one₀ hγ.le hSA.gamma_le)
    linarith

end Smallness

end Parameters

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ} {ε γ : ℝ}
  {gc : GConsts}

/-- Blueprint `bp:p4:parameters` (claims): the side conditions of the three frozen applications,
`σ - μ` values, the second entry of `c_*`, and positivity of the derived constants. -/
theorem parameters (hD : Data τ s₀ r₀ B h Lh) :
    ((2 ≤ n ∧ (n : ℝ) - 1 ≤ τ) ∧
      (0 < stripWidth s₀ / 8 ∧ stripWidth s₀ / 8 < stripWidth s₀ / 4) ∧
      (0 < stripWidth s₀ / 16 ∧ stripWidth s₀ / 16 < 3 * stripWidth s₀ / 32) ∧
      0 < Mconst s₀ r₀ B h ∧ 0 < sigmaK s₀ r₀ ∧ 0 < sigmaB s₀ r₀ ∧ 0 < sigmaT Lh s₀ r₀ ∧
      0 < muParam s₀ r₀) ∧
    (sigmaK s₀ r₀ - muParam s₀ r₀ = 2 ∧ sigmaB s₀ r₀ - muParam s₀ r₀ = 2 ∧
      sigmaT Lh s₀ r₀ - muParam s₀ r₀ = 4 * Lplus Lh) ∧
    deltaStar s₀ r₀ ^ 2 / (2 * Lplus Lh * cbar n) = 1 / (2 * Lplus Lh * Fconst n s₀ r₀ 2) ∧
    0 < lamStar Lh s₀ r₀ ∧ 0 < cT s₀ r₀ B h ∧ (∀ δ : ℝ, 0 < δ → 0 < etaStar s₀ r₀ B h Lh δ) ∧
    ∀ gc : GConsts, gc.Pos →
      0 < A0 n τ s₀ r₀ gc ∧ 0 < A1 τ s₀ r₀ B h Lh gc ∧ 0 < A2 τ s₀ r₀ B h Lh gc ∧
      0 < A3 τ s₀ r₀ B h Lh gc ∧ 0 < A4 n τ s₀ r₀ gc ∧ 0 < cStar τ s₀ r₀ B h Lh gc := by
  obtain ⟨hn, hτ, hs₀, hr₀, -⟩ := hD
  have hs := stripWidth_pos hs₀
  refine ⟨⟨⟨hn, hτ.le⟩, ⟨by positivity, by linarith⟩, ⟨by positivity, by linarith⟩,
    Parameters.Mconst_pos hs₀ hr₀, Parameters.sigmaK_pos hs₀ hr₀, Parameters.sigmaB_pos hs₀ hr₀,
    Parameters.sigmaT_pos hs₀ hr₀, muParam_pos hs₀ hr₀⟩,
    ⟨by unfold sigmaK; ring, by unfold sigmaB; ring, by unfold sigmaT; ring⟩,
    Parameters.deltaStar_sq_div_eq hs₀ hr₀, Parameters.lamStar_pos hs₀ hr₀,
    Parameters.cT_pos hn hs₀ hr₀, fun δ hδ => Parameters.etaStar_pos hn hs₀ hr₀ hδ,
    fun gc hgc => ⟨Parameters.A0_pos hs₀ hr₀ hgc, Parameters.A1_pos hs₀ hr₀ hgc,
      Parameters.A2_pos hs₀ hr₀ hgc, Parameters.A3_pos hs₀ hr₀ hgc,
      Parameters.A4_pos hs₀ hr₀ hn hgc, Parameters.cStar_pos hn hs₀ hr₀ hgc⟩⟩

/-- Blueprint `bp:p4:smallness`, items (s1)–(s7). -/
theorem smallness (hD : Data τ s₀ r₀ B h Lh) (hgc : gc.Pos)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    -- (s1)
    (ε ≤ 1 ∧ Lplus Lh * Fconst n s₀ r₀ 2 * ε ≤ 1 / 2) ∧
    -- (s2)
    gc.C11 * (Fconst n s₀ r₀ 1 * ε) / (γ ^ 4 * (stripWidth s₀ / 4) ^ (4 * τ)) ≤ 1 / 2 ∧
    -- (s3)
    (eta0 n τ s₀ r₀ gc ε γ ≤ etaStar s₀ r₀ B h Lh (stripWidth s₀ / 32) ∧
      etaStar s₀ r₀ B h Lh (stripWidth s₀ / 32) ≤ etaStar s₀ r₀ B h Lh (stripWidth s₀ / 16) ∧
      eta0 n τ s₀ r₀ gc ε γ ≤ muParam s₀ r₀ ∧
      16 * n * eta0 n τ s₀ r₀ gc ε γ / stripWidth s₀ ≤ 1 / 2) ∧
    -- (s4)
    gc.C12 * (A1 τ s₀ r₀ B h Lh gc * lamStar Lh s₀ r₀ * ε) /
      (γ ^ 4 * (3 * stripWidth s₀ / 32) ^ (4 * τ)) ≤ 1 / 2 ∧
    -- (s5)
    (2 * A0 n τ s₀ r₀ gc +
        gc.C22 * A1 τ s₀ r₀ B h Lh gc * lamStar Lh s₀ r₀ / (3 * stripWidth s₀ / 32) ^ (2 * τ)) *
      (ε / γ ^ 2) ≤ gc.cG * γ ^ 2 * (stripWidth s₀ / 16) ^ (2 * τ) ∧
    -- (s6)
    (A3 τ s₀ r₀ B h Lh gc * LambdaG s₀ r₀ B h + A4 n τ s₀ r₀ gc) * (ε / γ ^ 4) ≤ 1 / 4 ∧
    -- (s7)
    (eta0 n τ s₀ r₀ gc ε γ ≤ γ ^ 2 / 2 ∧ γ ^ 2 / 2 ≤ min γ 1 / 2) :=
  ⟨Parameters.smallness_s1 hD hgc hSA, Parameters.smallness_s2 hD hgc hSA,
    Parameters.smallness_s3 hD hgc hSA, Parameters.smallness_s4 hD hgc hSA,
    Parameters.smallness_s5 hD hgc hSA, Parameters.smallness_s6 hD hgc hSA,
    Parameters.smallness_s7 hD hgc hSA⟩

end KAM.Head
