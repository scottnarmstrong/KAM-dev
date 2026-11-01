/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainK2f

/-!
# The class `𝒜(B_{ρ₁})` for `K` (blueprint-W `bpW:w3:main` (i), (ii))

Package W3-MAIN, blueprint label `bpW:w3:main`.

`birkXKExt = X_{K₁} + X_{K₂}` is the Hamiltonian field of `K` on `B_{ρ₁}` (`birkKExt_field`),
analytic
into `𝔚⁺`, real, with `‖X_K(w)‖₊ ≤ 66 C_* C_F ‖w‖⁵` (`norm_birkXKExt_le`); `birkKExt_isClassA`:
`K ∈ 𝒜(B_{ρ₁})` with `B_{ρ₁} = {w | 160 C_F ‖w‖² < 1}`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- Internal totalized helper (meaningful on `B_{ρ₁}`; public object `birkXK`):
`X_K = X_{K₁} + X_{K₂}`. -/
def birkXKExt (w : BirkSpace) : BirkSpace := birkXK1Ext m hm ha hp w + birkXK2Ext m hm ha hp w

variable {m hm ha hp}

include hm hp in
theorem birkKExt_field (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) (v : BirkSpace) :
    fderiv ℂ (birkKExt m hm ha hp) w v =
      birkOmegaPlus a p ha (by linarith) (birkXKExt m hm ha hp w) v := by
  have hw40 : 40 * birkCF m p * ‖w‖ ^ 2 < 1 := by
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  have hΓa : AnalyticAt ℂ (birkGamma m hm ha hp 1) w :=
    birkGamma_analyticOnNhd (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w hw40
  have hΛa : ∀ y, AnalyticAt ℂ (birkLambda m hm ha hp) y := fun y =>
    (birkLambda_analyticOnNhd (m := m) (hm := hm) (ha := ha) (hp := hp)) y (Set.mem_univ _)
  have hGa : ∀ y, AnalyticAt ℂ (birkHamG m hm ha hp) y := fun y =>
    (birkHamG_isClassA m hm ha hp).analytic y (Set.mem_univ _)
  have hZa : ∀ y, AnalyticAt ℂ (birkHamZ m hm ha hp) y := fun y =>
    (birkHamZ_isClassA m hm ha hp).analytic y (Set.mem_univ _)
  have hK1 : AnalyticAt ℂ (birkK1Ext m hm ha hp) w := by
    unfold birkK1Ext; exact ((hGa _).comp hΓa).sub (hGa w)
  have hK2 : AnalyticAt ℂ (birkK2Ext m hm ha hp) w := by
    unfold birkK2Ext; exact ((((hΛa _).comp hΓa).sub (hΛa w)).sub (hZa w))
  have e : birkKExt m hm ha hp = fun y => birkK1Ext m hm ha hp y + birkK2Ext m hm ha hp y :=
    funext fun y => birkKExt_eq m hm ha hp y
  rw [e, fderiv_fun_add hK1.differentiableAt hK2.differentiableAt]
  simp only [ContinuousLinearMap.add_apply]
  rw [birkK1Ext_field (ha := ha) (hm := hm) (hp := hp) w hw v,
    birkK2Ext_field (ha := ha) (hm := hm) (hp := hp) w hw v]
  unfold birkXKExt birkOmegaPlus
  rw [map_add, map_add, ContinuousLinearMap.add_apply]

include hm hp in
theorem norm_birkXKExt_le (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    ‖birkXKExt m hm ha hp w‖ ≤ 66 * waveCubicConst p * birkCF m p * ‖w‖ ^ 5 := by
  unfold birkXKExt
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_birkXK1Ext_le (ha := ha) (hm := hm) (hp := hp) w hw
  have h2 := norm_birkXK2Ext_le (ha := ha) (hm := hm) (hp := hp) w hw
  linarith

include hm hp in
theorem birkXKExt_analyticAt (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    AnalyticAt ℂ (birkXKExt m hm ha hp) w :=
  (birkXK1Ext_analyticAt (ha := ha) (hm := hm) (hp := hp) w hw).add
    (birkXK2Ext_analyticAt (ha := ha) (hm := hm) (hp := hp) w hw)

include hm hp in
/-- (`bpW:w3:main` (i), (ii)) `K ∈ 𝒜(B_{ρ₁})` with field `X_K`. -/
theorem birkKExt_isClassA :
    IsBirkClassA a p ha (by linarith) {w : BirkSpace | 160 * birkCF m p * ‖w‖ ^ 2 < 1}
      (birkKExt m hm ha hp) (birkXKExt m hm ha hp) where
  isOpen := isOpen_lt (by fun_prop) continuous_const
  rho_mem w hw := by
    show 160 * birkCF m p * ‖birkRho w‖ ^ 2 < 1
    rw [birkRho.norm_map]; exact hw
  real w hw := birkKExt_rho (ha := ha) (hm := hm) (hp := hp) w hw
  analytic w hw := birkKExt_analyticOnNhd (ha := ha) (hm := hm) (hp := hp) w (by
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    show 40 * birkCF m p * ‖w‖ ^ 2 < 1
    have hw' : 160 * birkCF m p * ‖w‖ ^ 2 < 1 := hw
    nlinarith)
  field w hw v := birkKExt_field (ha := ha) (hm := hm) (hp := hp) w hw v
  analytic_field w hw := birkXKExt_analyticAt (ha := ha) (hm := hm) (hp := hp) w hw

end KAM.Wave

end
