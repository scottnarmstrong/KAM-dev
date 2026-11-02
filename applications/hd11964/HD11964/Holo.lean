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
# HD 11964: the complex extension of `P` — definitions and the Kepler contraction (HD11964-HOLO)

* `planetChartC`, `chartQPC`, `distSqC`, `chartPertC`: LP's chart continued to complex mean
  longitudes with the Kepler strip `y₀` (`keplerSol y₀` in place of `keplerLongC`), the complexified
  mutual distance squared (bilinear) and the complexified perturbation
  `P_C = μ((p_c + p_b)·(p_c + p_b)/2 − ν_c ν_b (d²)^{−1/2})`.
* `holoDomHD`: `R(1/500)` with planet `c` rotation-reduced (`|η_c| ≤ 1/500`); the strip
  `rhoHolo = (1/40, 3/20)`, the Kepler strips `yHolo = (4/5, 13/10)`, `kappaHolo = (19/20, 1/2)`.
* `eccL1_le_eBar`: on `holoDomHD` the ℓ¹ eccentricity vectors `β(|ξ| + |η|)` are at most
  `ē = (0.69, 0.18)`.
* `keplerData_HD` (1a): the Kepler contraction (`KAM.Kepler.KeplerData`) on `|Im λ| < 2πρ_j` for
  both planets.
* `noCollision_of_enclosure`: (1b) from a certified enclosure of `d²` (the layer's data).
* `abs_pb_le` (2a): the bracket bounded by coordinates.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real ContDiff

namespace HD11964.Cover

/-! ### Definitions -/

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

/-- **The complexified mutual distance squared** (bilinear): `d² = (q_c - q_b)·(q_c - q_b)`. -/
def distSqC (y : Fin 2 → ℝ) (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) : ℂ :=
  ((chartQPC y w θ 0).1 0 - (chartQPC y w θ 1).1 0) ^ 2 +
    ((chartQPC y w θ 0).1 1 - (chartQPC y w θ 1).1 1) ^ 2

/-- **The complexified perturbation** `P_C = μ (|p_c + p_b|²/2 - ν_c ν_b (d²)^{-1/2})`. -/
def chartPertC (y : Fin 2 → ℝ) (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) : ℂ :=
  (mu : ℂ) * ((((chartQPC y w θ 0).2 0 + (chartQPC y w θ 1).2 0) ^ 2 +
    ((chartQPC y w θ 0).2 1 + (chartQPC y w θ 1).2 1) ^ 2) / 2 -
    (nu 0 : ℂ) * (nu 1 : ℂ) * distSqC y w θ ^ (-(1 / 2 : ℂ)))

/-- The strip widths (`θ = λ/2π`): `ρ = (1/40, 3/20)`. -/
def rhoHolo : Fin 2 → ℝ := ![1 / 40, 3 / 20]

/-- The Kepler strips `y₀ = (4/5, 13/10)`. -/
def yHolo : Fin 2 → ℝ := ![4 / 5, 13 / 10]

/-- The contraction constants `κ = (19/20, 1/2)`. -/
def kappaHolo : Fin 2 → ℝ := ![19 / 20, 1 / 2]

/-- The bounds on the ℓ¹ eccentricity vectors: `ē = (0.69, 0.18)`. -/
def eBar : Fin 2 → ℝ := ![69 / 100, 9 / 50]

/-- **The real chart states of the claim**: `R(1/500)` with planet `c` rotation-reduced
(`|η_c| ≤ 1/500`). -/
def holoDomHD : Set (Phase (2 + 2)) := {w | w ∈ region (1 / 500) ∧ |slow w.2 0| ≤ 1 / 500}

/-! ### The ℓ¹ eccentricity vectors on `holoDomHD` -/

theorem lpGamma_le_chartAMD (w : Phase (2 + 2)) (i : Fin 2) : lpGamma w i ≤ chartAMD w := by
  rw [chartAMD_eq_sum_lpGamma]
  exact Finset.single_le_sum (f := lpGamma w) (fun j _ => by unfold lpGamma; positivity)
    (Finset.mem_univ i)

/-- The ℓ¹ eccentricity of one planet from its action `Λ` and slow pair `(ξ, η)`: if
`β²(|ξ| + |η|)² ≤ e²` with `β² = (1 - Γ/(2Λ))/Λ`, then `β(|ξ| + |η|) ≤ e`. -/
theorem eccL1_le_of_sq {Λ ξ η e : ℝ} (_hΛ : 0 < Λ) (he : 0 ≤ e)
    (h : (1 - (ξ ^ 2 + η ^ 2) / 2 / (2 * Λ)) / Λ * (|ξ| + |η|) ^ 2 ≤ e ^ 2) :
    lpEccScale Λ ((ξ ^ 2 + η ^ 2) / 2) * (|ξ| + |η|) ≤ e := by
  unfold lpEccScale
  rw [← Real.sqrt_sq (add_nonneg (abs_nonneg ξ) (abs_nonneg η)), ← Real.sqrt_mul' _ (sq_nonneg _),
    ← Real.sqrt_sq he]
  exact Real.sqrt_le_sqrt h

/-- **On `holoDomHD`, the ℓ¹ eccentricity vectors are at most `ē`.** -/
theorem eccL1_le_eBar {w : Phase (2 + 2)} (hw : w ∈ holoDomHD) (i : Fin 2) :
    lpEccScale (fast w.2 i) (lpGamma w i) * (|slow w.1 i| + |slow w.2 i|) ≤ eBar i := by
  obtain ⟨⟨-, hΛ, hA⟩, hη⟩ := hw
  have hG : lpGamma w i ≤ 7 / 500 :=
    (lpGamma_le_chartAMD w i).trans (by norm_num [cBar] at hA ⊢; linarith)
  have hΓ : lpGamma w i = ((slow w.1 i) ^ 2 + (slow w.2 i) ^ 2) / 2 := rfl
  have hΛlo := (hΛ i).1
  rw [hΓ] at hG ⊢
  refine eccL1_le_of_sq (by fin_cases i <;> simp [lamLo] at hΛlo ⊢ <;> norm_num at hΛlo ⊢ <;>
    linarith) (by fin_cases i <;> norm_num [eBar]) ?_
  set ξ := slow w.1 i
  set η := slow w.2 i
  set Λ := fast w.2 i
  have hs : (|ξ| + |η|) ^ 2 = ξ ^ 2 + η ^ 2 + 2 * |ξ| * |η| := by
    rw [add_sq, sq_abs, sq_abs]; ring
  fin_cases i
  · -- planet c: `|η_c| ≤ 1/500`, `Λ_c ≥ 0.0563`
    simp only [lamLo, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hΛlo
    simp only [eBar, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    have hΛ0 : (563 : ℝ) / 10000 ≤ Λ := by norm_num at hΛlo; linarith
    have hηa : |η| ≤ 1 / 500 := hη
    have hξa : |ξ| ≤ 17 / 100 := by
      rw [← Real.sqrt_sq (abs_nonneg ξ)]
      calc √(|ξ| ^ 2) ≤ √((17 / 100) ^ 2) :=
            Real.sqrt_le_sqrt (by rw [sq_abs]; nlinarith [sq_nonneg η])
        _ = 17 / 100 := Real.sqrt_sq (by norm_num)
    have hcross : 2 * |ξ| * |η| ≤ 17 / 25000 := by
      nlinarith [abs_nonneg ξ, abs_nonneg η]
    set Γ := (ξ ^ 2 + η ^ 2) / 2 with hΓdef
    have hΓ0 : 0 ≤ Γ := by positivity
    rw [hs, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have h1 : 0 ≤ 1 - Γ / (2 * Λ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have h2 : (1 - Γ / (2 * Λ)) * (ξ ^ 2 + η ^ 2 + 2 * |ξ| * |η|) ≤
        (1 - Γ / (2 * Λ)) * (2 * Γ + 17 / 25000) :=
      mul_le_mul_of_nonneg_left (by rw [hΓdef]; linarith) h1
    refine h2.trans ?_
    have e : (1 - Γ / (2 * Λ)) * (2 * Γ + 17 / 25000) =
        (2 * Γ + 17 / 25000) - Γ * (2 * Γ + 17 / 25000) / (2 * Λ) := by ring
    rw [e]
    have h3 : Γ * (2 * Γ + 17 / 25000) / (2 * Λ) ≥ Γ * (2 * Γ) / (2 * Λ) := by
      apply div_le_div_of_nonneg_right _ (by linarith); nlinarith
    have h4 : Γ * (2 * Γ) / (2 * Λ) = Γ ^ 2 / Λ := by field_simp
    rw [h4] at h3
    have h5 : 2 * Γ - Γ ^ 2 / Λ ≤ 7 / 250 - (7 / 500) ^ 2 / Λ := by
      have hΛp : 0 < Λ := by linarith
      rw [show 2 * Γ - Γ ^ 2 / Λ = (2 * Γ * Λ - Γ ^ 2) / Λ by field_simp,
        show (7 : ℝ) / 250 - (7 / 500) ^ 2 / Λ = (7 / 250 * Λ - (7 / 500) ^ 2) / Λ by field_simp]
      apply div_le_div_of_nonneg_right _ hΛp.le
      nlinarith [mul_nonneg (sub_nonneg.2 hG) (by linarith : (0 : ℝ) ≤ 2 * Λ - Γ - 7 / 500)]
    have h6 : 7 / 250 - (7 / 500) ^ 2 / Λ + 17 / 25000 ≤ (69 / 100) ^ 2 * Λ := by
      have hΛp : 0 < Λ := by linarith
      rw [← sub_nonneg]
      have : (69 / 100) ^ 2 * Λ - (7 / 250 - (7 / 500) ^ 2 / Λ + 17 / 25000) =
          ((69 / 100) ^ 2 * Λ ^ 2 - (7 / 250 + 17 / 25000) * Λ + (7 / 500) ^ 2) / Λ := by
        field_simp; ring
      rw [this]
      apply div_nonneg _ hΛp.le
      nlinarith [mul_nonneg (sub_nonneg.2 hΛ0) (sub_nonneg.2 hΛ0)]
    linarith
  · -- planet b: `β² ≤ 1/Λ_b`, `(|ξ| + |η|)² ≤ 4Γ`, `Λ_b ≥ 1.7797`
    simp only [lamLo, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hΛlo
    simp only [eBar, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hΛ0 : (17796 : ℝ) / 10000 ≤ Λ := by norm_num at hΛlo; linarith
    have hΛp : 0 < Λ := by linarith
    have h1 : (1 - (ξ ^ 2 + η ^ 2) / 2 / (2 * Λ)) / Λ ≤ 1 / Λ := by
      apply div_le_div_of_nonneg_right _ hΛp.le
      have : 0 ≤ (ξ ^ 2 + η ^ 2) / 2 / (2 * Λ) := by positivity
      linarith
    have h2 : (|ξ| + |η|) ^ 2 ≤ 2 * (ξ ^ 2 + η ^ 2) := by
      rw [hs]; nlinarith [sq_nonneg (|ξ| - |η|), sq_abs ξ, sq_abs η]
    have h0 : 0 ≤ (1 - (ξ ^ 2 + η ^ 2) / 2 / (2 * Λ)) / Λ := by
      apply div_nonneg _ hΛp.le
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    calc (1 - (ξ ^ 2 + η ^ 2) / 2 / (2 * Λ)) / Λ * (|ξ| + |η|) ^ 2
        ≤ 1 / Λ * (2 * (ξ ^ 2 + η ^ 2)) := mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ ≤ (9 / 50) ^ 2 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hΛp]; nlinarith

/-! ### Numerical bounds on `sinh`, `cosh` -/

theorem exp_bound_aux {x lo hi : ℝ} (hx : |x| ≤ 1)
    (h : ∑ i ∈ Finset.range 7, x ^ i / (Nat.factorial i : ℝ) - |x| ^ 7 * (8 / (5040 * 7)) ≥ lo ∧
      ∑ i ∈ Finset.range 7, x ^ i / (Nat.factorial i : ℝ) + |x| ^ 7 * (8 / (5040 * 7)) ≤ hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  have hb := Real.exp_bound hx (n := 7) (by norm_num)
  norm_num [Nat.factorial] at hb h ⊢
  rw [abs_le] at hb
  constructor <;> linarith [hb.1, hb.2, h.1, h.2]

theorem exp_four_fifths : 2.2254 ≤ Real.exp (4 / 5) ∧ Real.exp (4 / 5) ≤ 2.2256 :=
  exp_bound_aux (by norm_num [abs_of_pos]) (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem exp_neg_four_fifths : 0.4493 ≤ Real.exp (-(4 / 5)) ∧ Real.exp (-(4 / 5)) ≤ 0.4495 :=
  exp_bound_aux (by norm_num [abs_of_neg]) (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem exp_three_tenths : Real.exp (3 / 10) ≤ 1.3499 :=
  (exp_bound_aux (lo := 1.3498) (by norm_num [abs_of_pos])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])).2

theorem sinh_four_fifths_le : Real.sinh (4 / 5) ≤ 0.8882 := by
  rw [Real.sinh_eq]; linarith [exp_four_fifths.2, exp_neg_four_fifths.1]

theorem cosh_four_fifths_le : Real.cosh (4 / 5) ≤ 1.3376 := by
  rw [Real.cosh_eq]; linarith [exp_four_fifths.2, exp_neg_four_fifths.2]

theorem exp_thirteen_tenths_le : Real.exp (13 / 10) ≤ 3.6695 := by
  rw [show (13 / 10 : ℝ) = 1 + 3 / 10 by norm_num, Real.exp_add]
  have h1 := Real.exp_one_lt_d9
  have h2 := exp_three_tenths
  have h0 := Real.exp_pos (3 / 10)
  have h1' : Real.exp 1 ≤ 2.7182818286 := h1.le
  calc Real.exp 1 * Real.exp (3 / 10) ≤ 2.7182818286 * 1.3499 :=
        mul_le_mul h1' h2 h0.le (by norm_num)
    _ ≤ 3.6695 := by norm_num

theorem sinh_thirteen_tenths_le : Real.sinh (13 / 10) ≤ 1.8348 := by
  rw [Real.sinh_eq]; linarith [exp_thirteen_tenths_le, Real.exp_pos (-(13 / 10))]

theorem cosh_thirteen_tenths_le : Real.cosh (13 / 10) ≤ 2.3348 := by
  rw [Real.cosh_eq]
  have : Real.exp (-(13 / 10)) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  linarith [exp_thirteen_tenths_le]

/-! ### (1a) The Kepler contraction on the strip -/

/-- **(1a) The Kepler contraction on the strip** for both planets on `holoDomHD`
(`KAM.Kepler.KeplerData` with coefficients constant in `λ`, strip `y_j`, constant `κ_j`). -/
theorem keplerData_HD (j : Fin 2) {w : Phase (2 + 2)} (hw : w ∈ holoDomHD) :
    KAM.Kepler.KeplerData {lam : ℂ | |lam.im| < 2 * π * rhoHolo j}
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.1 j : ℝ) : ℂ))
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.2 j : ℝ) : ℂ))
      (fun lam => lam) (yHolo j) (kappaHolo j) := by
  have he := eccL1_le_eBar hw j
  set β := lpEccScale (fast w.2 j) (lpGamma w j)
  have hβ : 0 ≤ β := Real.sqrt_nonneg _
  have hsum : |β * slow w.1 j| + |β * slow w.2 j| ≤ eBar j := by
    rw [abs_mul, abs_mul, abs_of_nonneg hβ, ← mul_add]; exact he
  have hpi := Real.pi_lt_d2
  refine ⟨isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const,
    analyticOnNhd_const, analyticOnNhd_const, analyticOnNhd_id, ?_, ?_, ?_, ?_⟩
  · fin_cases j <;> norm_num [yHolo]
  · fin_cases j <;> norm_num [kappaHolo]
  · intro lam hlam
    simp only [Set.mem_ofPred_eq] at hlam
    simp only [Complex.ofReal_re, Complex.ofReal_im, abs_zero, add_zero, zero_mul]
    have hs0 : 0 ≤ Real.sinh (yHolo j) :=
      Real.sinh_nonneg_iff.2 (by fin_cases j <;> norm_num [yHolo])
    have hmono := mul_le_mul_of_nonneg_right hsum hs0
    fin_cases j
    · simp only [rhoHolo, yHolo, eBar, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        at hlam hmono ⊢
      nlinarith [sinh_four_fifths_le]
    · simp only [rhoHolo, yHolo, eBar, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hlam hmono ⊢
      nlinarith [sinh_thirteen_tenths_le]
  · intro lam _
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have hc0 : 0 ≤ Real.cosh (yHolo j) := (Real.cosh_pos _).le
    have hmono := mul_le_mul_of_nonneg_right hsum hc0
    fin_cases j
    · simp only [yHolo, eBar, kappaHolo, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hmono ⊢
      nlinarith [cosh_four_fifths_le]
    · simp only [yHolo, eBar, kappaHolo, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hmono ⊢
      nlinarith [cosh_thirteen_tenths_le]

/-! ### (1b) from a certified enclosure; (2a) the bracket by coordinates -/

/-- **(1b) from a certified enclosure of `d²`** (the layer's data): if `|d² - D| ≤ r < Re D` on the
strip, then `Re d² > 0` there. -/
theorem noCollision_of_enclosure {w : Phase (2 + 2)} {D : (Fin 2 → ℂ) → ℂ} {r : (Fin 2 → ℂ) → ℝ}
    (hD : ∀ θ ∈ stripA rhoHolo, ‖distSqC yHolo w θ - D θ‖ ≤ r θ)
    (hr : ∀ θ ∈ stripA rhoHolo, r θ < (D θ).re) :
    ∀ θ ∈ stripA rhoHolo, 0 < (distSqC yHolo w θ).re := by
  intro θ hθ
  have h1 := (Complex.abs_re_le_norm _).trans (hD θ hθ)
  rw [Complex.sub_re, abs_le] at h1
  linarith [hr θ hθ, h1.1]

/-- **(2a) The bracket by coordinates**:
`|{a, b}| ≤ Σ_k |∂_{x_k} a| |∂_{y_k} b| + |∂_{y_k} a| |∂_{x_k} b|`. -/
theorem abs_pb_le {d : ℕ} (a b : Phase d → ℝ) (w : Phase d) :
    |pb a b w| ≤ ∑ k, (|fderiv ℝ a w (Pi.single k 1, 0)| * |fderiv ℝ b w (0, Pi.single k 1)| +
      |fderiv ℝ a w (0, Pi.single k 1)| * |fderiv ℝ b w (Pi.single k 1, 0)|) := by
  rw [pb_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← abs_mul, ← abs_mul]
  exact abs_sub _ _

end HD11964.Cover

end
