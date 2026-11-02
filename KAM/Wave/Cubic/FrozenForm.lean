/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.CubicMap
public import KAM.Wave.Seq.Coordinatewise
public import KAM.Wave.Seq.Diag

/-!
# The frozen forms `𝒢^w` and `X^w` (blueprint `bpW:w1:cubic-analytic` (iv),
`bpW:w1:hamfield` (v), `bpW:w1:coordinatewise`)

* `KAM.Wave.waveGw m hm = 𝒩` for `𝕜 = ℝ`, `(a,p) = (1,1)`: `𝒢^w(y)_l = ω_{1,2}(l) cubicGrad y l`
  (`waveGw_apply`), real analytic, `‖𝒢^w(y)‖ ≤ C_m ‖y‖³` (`waveGw_norm_le`), with the weighted
  coordinates of `𝒢(κ_{1,1} y)` at weights `(1,2)`, `(1,1)`, `(1,0)` (`coeffW_one_two_waveGw`,
  `waveGw_weighted_one_one`, `waveGw_weighted_one_zero`);
* `KAM.Wave.waveXw`: `X^w(y,y') = (D y', -D y - S² 𝒢^w(y))` on `WaveSpace`, real analytic
  (`waveXw_analyticOnNhd`), with coordinates `ω_{1,0}(j) (λ_j coeff y' j, -λ_j coeff y j -
  cubicGrad y j)` (`coeffW_one_zero_waveXw_fst`, `coeffW_one_zero_waveXw_snd`);
* `KAM.Wave.frozen_invariance_iff_waveXw`: the full specialization of `bpW:w1:coordinatewise` to
  `v := X^w(K θ)`: the coordinatewise form of clause (4) of the frozen `nlw2` holds iff
  `ι̂ (DK(θ) ν) = X^w(K θ)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

lemma ellWeight_one_zero (l : ℕ+) : ellWeight 1 0 l = Real.exp (l : ℝ) := by
  simp [ellWeight]

lemma ellWeight_one_one (l : ℕ+) : ellWeight 1 1 l = (l : ℝ) * Real.exp (l : ℝ) := by
  simp [ellWeight]

lemma ellWeight_one_two (l : ℕ+) : ellWeight 1 2 l = (l : ℝ) ^ 2 * Real.exp (l : ℝ) := by
  unfold ellWeight
  rw [Real.rpow_two]; simp

/-- `𝒢^w`: the cubic gradient in the frozen weighted coordinates, `𝒩` for `𝕜 = ℝ`, `(a,p)=(1,1)`
(blueprint `bpW:w1:cubic-analytic` (iv)). -/
def waveGw (y : lp (fun _ : ℕ+ => ℝ) 2) : lp (fun _ : ℕ+ => ℝ) 2 :=
  waveCubicNL (K := ℝ) m hm zero_le_one (by norm_num : (1 / 2 : ℝ) ≤ 1) y

/-- `𝒢^w(y)_l = ω_{1,2}(l) · cubicGrad y l`. -/
theorem waveGw_apply (y : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) :
    waveGw m hm y l = ellWeight 1 2 l * cubicGrad m hm y l := by
  rw [cubicGrad_eq_triML_div, waveGw, waveCubicNL_eq]
  have := ellWeight_pos 1 2 l
  field_simp

/-- `bpW:w1:cubic-analytic` (iv): `‖𝒢^w(y)‖ ≤ C_m ‖y‖³`, `C_m = 8(1 + 2ζ(3))/π`. -/
theorem waveGw_norm_le (y : lp (fun _ : ℕ+ => ℝ) 2) :
    ‖waveGw m hm y‖ ≤ waveCubicHeadlineConst * ‖y‖ ^ 3 := by
  rw [← waveCubicConst_one]
  exact waveCubicNL_norm_le m hm _ _ y

/-- `bpW:w1:cubic-analytic` (iv): `𝒢^w` is real analytic on all of `ℓ²_ℝ`. -/
theorem waveGw_analyticOnNhd : AnalyticOnNhd ℝ (waveGw m hm) Set.univ :=
  waveCubicNL_analyticOnNhd m hm _ _

/-- The coefficient sequence `𝒢(κ_{1,1} y) = cubicGrad y` has weighted coordinates `𝒢^w(y)` at
weight `(1,2)`. -/
theorem coeffW_one_two_waveGw (y : lp (fun _ : ℕ+ => ℝ) 2) :
    coeffW 1 2 (waveGw m hm y) = cubicGrad m hm y := by
  funext l
  rw [coeffW_apply, waveGw_apply]
  have := ellWeight_pos 1 2 l
  simp only [RCLike.ofReal_real_eq_id, id]
  field_simp

/-- Weighted coordinates at weight `(1,1)`: `ω_{1,1}(l) cubicGrad y l = l⁻¹ 𝒢^w(y)_l`. -/
theorem waveGw_weighted_one_one (y : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) :
    ellWeight 1 1 l * cubicGrad m hm y l = (l : ℝ)⁻¹ * waveGw m hm y l := by
  rw [waveGw_apply, ellWeight_one_two, ellWeight_one_one]
  have : (0 : ℝ) < l := by positivity
  field_simp

/-- Weighted coordinates at weight `(1,0)`: `ω_{1,0}(l) cubicGrad y l = l⁻² 𝒢^w(y)_l`. -/
theorem waveGw_weighted_one_zero (y : lp (fun _ : ℕ+ => ℝ) 2) (l : ℕ+) :
    ellWeight 1 0 l * cubicGrad m hm y l = ((l : ℝ) ^ 2)⁻¹ * waveGw m hm y l := by
  rw [waveGw_apply, ellWeight_one_two, ellWeight_one_zero]
  have : (0 : ℝ) < l := by positivity
  field_simp

/-- The diagonal multiplier `S = D_{(1/j)}`. -/
def waveShift : lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℝ) 2 :=
  weightedDiagCLM (fun j : ℕ+ => 1 / (j : ℝ)) (M := 1) (fun j => by
    have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_le_one (by positivity)).2 hj)

@[simp] lemma waveShift_apply (y : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) :
    waveShift y j = 1 / (j : ℝ) * y j := rfl

/-- `X^w(y,y') = (D y', -D y - S² 𝒢^w(y))` on `WaveSpace`, `D = D_μ`, `μ_j = λ_j / j`
(blueprint `bpW:w1:hamfield` (v)). -/
def waveXw (z : WaveSpace) : WaveSpace :=
  (lamMul (K := ℝ) m hm 1 z.2,
    -(lamMul (K := ℝ) m hm 1 z.1) - waveShift (waveShift (waveGw m hm z.1)))

lemma lamRatio_one (j : ℕ+) : lamRatio m hm 1 j = lam m hm j / (j : ℝ) := by
  simp [lamRatio]

/-- `κ_{1,0} (X^w z).1 = λ · coeff z.2`. -/
theorem coeffW_one_zero_waveXw_fst (z : WaveSpace) :
    coeffW 1 0 (waveXw m hm z).1 = fun j => lam m hm j * coeff z.2 j := by
  funext j
  simp only [waveXw, coeffW_apply, lamMul_apply, lamRatio_one, RCLike.ofReal_real_eq_id, id]
  rw [ellWeight_one_zero]
  unfold coeff
  rw [ellWeight_one_one]
  have h1 : (0 : ℝ) < j := by positivity
  have h2 := Real.exp_pos (j : ℝ)
  field_simp

/-- `κ_{1,0} (X^w z).2 = -λ · coeff z.1 - cubicGrad z.1`. -/
theorem coeffW_one_zero_waveXw_snd (z : WaveSpace) :
    coeffW 1 0 (waveXw m hm z).2 =
      fun j => -(lam m hm j * coeff z.1 j) - cubicGrad m hm z.1 j := by
  funext j
  have hG := waveGw_apply m hm z.1 j
  simp only [waveXw, coeffW_apply, lamMul_apply, lamRatio_one, RCLike.ofReal_real_eq_id, id,
    lp.coeFn_sub, lp.coeFn_neg, Pi.sub_apply, Pi.neg_apply, waveShift_apply]
  rw [hG, ellWeight_one_zero]
  unfold coeff
  rw [ellWeight_one_one, ellWeight_one_two]
  have h1 : (0 : ℝ) < j := by positivity
  have h2 := Real.exp_pos (j : ℝ)
  field_simp

/-- `bpW:w1:hamfield` (v): `X^w` is real analytic on all of `WaveSpace`. -/
theorem waveXw_analyticOnNhd : AnalyticOnNhd ℝ (waveXw m hm) Set.univ := by
  intro z _
  have hfst : AnalyticAt ℝ (fun z : WaveSpace => z.1) z :=
    (ContinuousLinearMap.fst ℝ (lp (fun _ : ℕ+ => ℝ) 2) (lp (fun _ : ℕ+ => ℝ) 2)).analyticAt z
  have hsnd : AnalyticAt ℝ (fun z : WaveSpace => z.2) z :=
    (ContinuousLinearMap.snd ℝ (lp (fun _ : ℕ+ => ℝ) 2) (lp (fun _ : ℕ+ => ℝ) 2)).analyticAt z
  have hD : ∀ w : WaveSpace → lp (fun _ : ℕ+ => ℝ) 2, AnalyticAt ℝ w z →
      AnalyticAt ℝ (fun z => lamMul (K := ℝ) m hm 1 (w z)) z := fun w hw =>
    ((lamMul (K := ℝ) m hm 1).analyticAt _).comp hw
  have hG : AnalyticAt ℝ (fun z : WaveSpace => waveGw m hm z.1) z :=
    (waveGw_analyticOnNhd m hm z.1 trivial).comp hfst
  have hS : ∀ w : WaveSpace → lp (fun _ : ℕ+ => ℝ) 2, AnalyticAt ℝ w z →
      AnalyticAt ℝ (fun z => waveShift (w z)) z := fun w hw => (waveShift.analyticAt _).comp hw
  exact AnalyticAt.prod (hD _ hsnd) (AnalyticAt.sub (AnalyticAt.neg (hD _ hfst))
    (hS _ (hS _ hG)))

/-- **Full specialization of `bpW:w1:coordinatewise`** (`bpW:w1:hamfield` (v)): for `Kmap`
differentiable at `θ`, the coordinatewise form of clause (4) of the frozen `nlw2` is equivalent to
`ι̂ (DK(θ) ν) = X^w(K θ)` (with `ι̂ : E_{1,1} → E_{1,0}` the representative of the inclusion,
applied componentwise). -/
theorem frozen_invariance_iff_waveXw {Kmap : (Fin 2 → ℝ) → WaveSpace}
    {θ ν : Fin 2 → ℝ} (hK : DifferentiableAt ℝ Kmap θ) :
    (∀ j : ℕ+,
        HasDerivAt (fun t : ℝ => coeff (Kmap (θ + t • ν)).1 j) (lam m hm j * coeff (Kmap θ).2 j) 0 ∧
        HasDerivAt (fun t : ℝ => coeff (Kmap (θ + t • ν)).2 j)
          (-(lam m hm j * coeff (Kmap θ).1 j) - cubicGrad m hm (Kmap θ).1 j) 0) ↔
      (embedCLM 1 1 1 0 le_rfl zero_le_one (fderiv ℝ Kmap θ ν).1,
        embedCLM 1 1 1 0 le_rfl zero_le_one (fderiv ℝ Kmap θ ν).2) = waveXw m hm (Kmap θ) := by
  rw [Prod.ext_iff]
  exact frozen_invariance_iff hm hK (waveXw m hm (Kmap θ))
    (coeffW_one_zero_waveXw_fst m hm (Kmap θ)) (coeffW_one_zero_waveXw_snd m hm (Kmap θ))

end KAM.Wave

end
