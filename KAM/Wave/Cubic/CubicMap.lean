/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.TriProps
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Analyticity and Lipschitz bounds of the cubic map (blueprint `bpW:w1:cubic-analytic`)

`KAM.Wave.waveCubicNL a p y = 𝒯^{a,p}(y,y,y)` on `ℓ²_𝕜` is
(i) `𝕜`-analytic on all of `ℓ²_𝕜` with `‖𝒩(y)‖ ≤ C_* ‖y‖³` (`waveCubicNL_analyticOnNhd`,
`waveCubicNL_norm_le`); (ii) `D𝒩(y) h = 3 𝒯(y,y,h)` with `‖D𝒩(y)‖ ≤ 3 C_* ‖y‖²`
(`waveCubicNL_hasFDerivAt`, `norm_fderiv_waveCubicNL_le`); (iii) the Lipschitz bound
`‖𝒩(y) - 𝒩(y')‖ ≤ 3 C_* ‖y - y'‖ max(‖y‖,‖y'‖)²` (`waveCubicNL_sub_le`); (iv) the frozen form
`𝒢^w(y) = ω_{1,2} · cubicGrad y = 𝒩(y)` for `𝕜 = ℝ`, `(a,p) = (1,1)` (`waveGw`, `waveGw_apply`,
`waveGw_norm_le` with `C_m = waveCubicHeadlineConst = waveCubicConst 1`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {K : Type*} [RCLike K] (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- `𝒩(y) = 𝒯^{a,p}_𝕜(y,y,y)` (blueprint `bpW:w1:cubic-analytic`). -/
def waveCubicNL (y : lp (fun _ : ℕ+ => K) 2) : lp (fun _ : ℕ+ => K) 2 :=
  waveTriML (K := K) m hm ha hp fun _ => y

lemma waveCubicNL_eq (y : lp (fun _ : ℕ+ => K) 2) :
    waveCubicNL m hm ha hp y = waveTriML (K := K) m hm ha hp ![y, y, y] := by
  unfold waveCubicNL
  congr 1
  ext i; fin_cases i <;> rfl

/-- (i) `‖𝒩(y)‖ ≤ C_* ‖y‖³`. -/
theorem waveCubicNL_norm_le (y : lp (fun _ : ℕ+ => K) 2) :
    ‖waveCubicNL m hm ha hp y‖ ≤ waveCubicConst p * ‖y‖ ^ 3 := by
  have := waveTriAux_norm_le m hm ha hp y y y
  simpa [waveCubicNL, waveTriML_apply, pow_succ, mul_assoc] using this

/-- (i) `𝒩` is `𝕜`-analytic on all of `ℓ²_𝕜`. -/
theorem waveCubicNL_analyticOnNhd :
    AnalyticOnNhd K (waveCubicNL (K := K) m hm ha hp) Set.univ := by
  intro y _
  have hdiag : AnalyticAt K (fun y : lp (fun _ : ℕ+ => K) 2 => fun _ : Fin 3 => y) y :=
    (ContinuousLinearMap.pi fun _ : Fin 3 =>
      ContinuousLinearMap.id K (lp (fun _ : ℕ+ => K) 2)).analyticAt y
  have hM := ((waveTriML (K := K) m hm ha hp).cpolynomialAt (x := fun _ : Fin 3 => y)).analyticAt
  exact hM.comp hdiag

lemma wave_update_const_zero (y h : lp (fun _ : ℕ+ => K) 2) :
    Function.update (fun _ : Fin 3 => y) 0 h = ![h, y, y] := by
  ext i; fin_cases i <;> simp [Function.update]

lemma wave_update_const_one (y h : lp (fun _ : ℕ+ => K) 2) :
    Function.update (fun _ : Fin 3 => y) 1 h = ![y, h, y] := by
  ext i; fin_cases i <;> simp [Function.update]

lemma wave_update_const_two (y h : lp (fun _ : ℕ+ => K) 2) :
    Function.update (fun _ : Fin 3 => y) 2 h = ![y, y, h] := by
  ext i; fin_cases i <;> simp [Function.update]

/-- The derivative `h ↦ 3 𝒯(y,y,h)` of `𝒩` at `y`, as a continuous linear map. -/
def waveCubicDeriv (y : lp (fun _ : ℕ+ => K) 2) :
    lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2 :=
  (3 : K) • (waveTriML (K := K) m hm ha hp).toContinuousLinearMap (fun _ => y) 2

lemma waveCubicDeriv_apply (y h : lp (fun _ : ℕ+ => K) 2) :
    waveCubicDeriv m hm ha hp y h = (3 : K) • waveTriML (K := K) m hm ha hp ![y, y, h] := by
  simp [waveCubicDeriv, wave_update_const_two]

/-- (ii) `D𝒩(y) h = 3 𝒯(y,y,h)`. -/
theorem waveCubicNL_hasFDerivAt (y : lp (fun _ : ℕ+ => K) 2) :
    HasFDerivAt (waveCubicNL (K := K) m hm ha hp) (waveCubicDeriv m hm ha hp y) y := by
  classical
  let diag : lp (fun _ : ℕ+ => K) 2 →L[K] (Fin 3 → lp (fun _ : ℕ+ => K) 2) :=
    ContinuousLinearMap.pi fun _ : Fin 3 => ContinuousLinearMap.id K (lp (fun _ : ℕ+ => K) 2)
  have h1 := ((waveTriML (K := K) m hm ha hp).hasFDerivAt (x := fun _ : Fin 3 => y)).comp y
    (diag.hasFDerivAt (x := y))
  have hfun : waveCubicNL (K := K) m hm ha hp = ⇑(waveTriML (K := K) m hm ha hp) ∘ ⇑diag := rfl
  have hD : waveCubicDeriv m hm ha hp y =
      ((waveTriML (K := K) m hm ha hp).linearDeriv fun _ : Fin 3 => y).comp diag := by
    ext h : 1
    simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
      Fin.sum_univ_three, wave_update_const_zero, wave_update_const_one, wave_update_const_two,
      waveCubicDeriv_apply]
    have e1 := waveTriML_swap_left_right (K := K) m hm ha hp h y y
    have e2 := waveTriML_swap_mid_right (K := K) m hm ha hp y h y
    simp only [diag, ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply]
    have e5 : waveTriML (K := K) m hm ha hp ![h, y, y] = waveTriML (K := K) m hm ha hp ![y, y, h] :=
      e1
    have e6 : waveTriML (K := K) m hm ha hp ![y, h, y] = waveTriML (K := K) m hm ha hp ![y, y, h] :=
      e2
    rw [e5, e6]
    module
  rw [hfun, hD]
  exact h1

theorem waveCubicNL_fderiv (y h : lp (fun _ : ℕ+ => K) 2) :
    fderiv K (waveCubicNL (K := K) m hm ha hp) y h =
      (3 : K) • waveTriML (K := K) m hm ha hp ![y, y, h] := by
  rw [(waveCubicNL_hasFDerivAt m hm ha hp y).fderiv, waveCubicDeriv_apply]

/-- (ii) `‖D𝒩(y)‖ ≤ 3 C_* ‖y‖²`. -/
theorem norm_waveCubicDeriv_le (y : lp (fun _ : ℕ+ => K) 2) :
    ‖waveCubicDeriv m hm ha hp y‖ ≤ 3 * waveCubicConst p * ‖y‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := waveCubicConst_nonneg p; positivity)
    fun h => ?_
  rw [waveCubicDeriv_apply, norm_smul]
  have := waveTriAux_norm_le m hm ha hp y y h
  have h3 : ‖(3 : K)‖ = 3 := by simp
  rw [h3]
  have e : waveTriML (K := K) m hm ha hp ![y, y, h] = waveTriAux m hm ha hp y y h := rfl
  rw [e]
  calc 3 * ‖waveTriAux m hm ha hp y y h‖ ≤ 3 * (waveCubicConst p * (‖y‖ * ‖y‖ * ‖h‖)) := by
        gcongr
    _ = _ := by ring

theorem norm_fderiv_waveCubicNL_le (y : lp (fun _ : ℕ+ => K) 2) :
    ‖fderiv K (waveCubicNL (K := K) m hm ha hp) y‖ ≤ 3 * waveCubicConst p * ‖y‖ ^ 2 := by
  rw [(waveCubicNL_hasFDerivAt m hm ha hp y).fderiv]
  exact norm_waveCubicDeriv_le m hm ha hp y

/-- (iii) `‖𝒩(y) - 𝒩(y')‖ ≤ 3 C_* ‖y - y'‖ max(‖y‖,‖y'‖)²`. -/
theorem waveCubicNL_sub_le (y y' : lp (fun _ : ℕ+ => K) 2) :
    ‖waveCubicNL m hm ha hp y - waveCubicNL m hm ha hp y'‖ ≤
      3 * waveCubicConst p * ‖y - y'‖ * (max ‖y‖ ‖y'‖) ^ 2 := by
  have hC := waveCubicConst_nonneg p
  have h := (waveTriML (K := K) m hm ha hp).toMultilinearMap.norm_image_sub_le_of_bound hC
    (fun v => by
      have := waveTriAux_norm_le m hm ha hp (v 0) (v 1) (v 2)
      simpa [Fin.prod_univ_three, mul_assoc, waveTriML_apply] using this)
    (fun _ => y) (fun _ => y')
  simp only [Fintype.card_fin, pi_norm_const] at h
  have e : ‖(fun _ : Fin 3 => y) - fun _ => y'‖ = ‖y - y'‖ := by
    have : ((fun _ : Fin 3 => y) - fun _ => y') = fun _ => y - y' := rfl
    rw [this, pi_norm_const]
  rw [e] at h
  unfold waveCubicNL
  calc _ ≤ _ := h
    _ = _ := by push_cast; ring

end KAM.Wave

end
