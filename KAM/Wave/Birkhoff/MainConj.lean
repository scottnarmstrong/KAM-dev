/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainK3

/-!
# The conjugacy identity (blueprint-W `bpW:w3:main` (iv))

Package W3-MAIN, blueprint label `bpW:w3:main`.

For `w = ι y ∈ B_{ρ₁} ∩ 𝔚⁺` (`y` read at weight `p+1`): `Γ(w) = ι z` with `z = y + ψ(w) ∈ 𝔚⁺`
and
`DΓ(w)[X_Λ(y) + X_Ḡ(w) + X_{G^{nor}}(w) + X_K(w)] = X_Λ(z) + X_G(Γ w)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
/-- The chain rule for an analytic function composed with `Γ`. -/
theorem fderiv_comp_birkGamma {P : BirkSpace → ℂ} (w : BirkSpace)
    (hw40 : 40 * birkCF m p * ‖w‖ ^ 2 < 1) (hP : AnalyticAt ℂ P (birkGamma m hm ha hp 1 w))
    (η : BirkSpace) :
    fderiv ℂ (fun w' => P (birkGamma m hm ha hp 1 w')) w η =
      fderiv ℂ P (birkGamma m hm ha hp 1 w) (birkGammaD m hm ha hp 1 w η) := by
  have hΓa : AnalyticAt ℂ (birkGamma m hm ha hp 1) w :=
    birkGamma_analyticOnNhd (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w hw40
  have hcomp : AnalyticAt ℂ (fun w' => P (birkGamma m hm ha hp 1 w')) w := hP.comp hΓa
  have hR := (hP.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp w
    (birkGamma_hasFDerivAt (ha := ha) (hm := hm) (hp := hp) 1 w (by norm_num) hw40)
  have h3 := (hcomp.differentiableAt.hasFDerivAt.restrictScalars ℝ).unique hR
  have := DFunLike.congr_fun h3 η
  simpa using this

include hm hp in
/-- (`bpW:w3:main` (iv)) The conjugacy identity. -/
theorem birk_conjugacy_aux (y : BirkSpace)
    (hy : 160 * birkCF m p * ‖birkEmbed a (p + 1) p (by linarith) y‖ ^ 2 < 1) :
    ∃ z : BirkSpace, birkEmbed a (p + 1) p (by linarith) z =
        birkGamma m hm ha hp 1 (birkEmbed a (p + 1) p (by linarith) y) ∧
      birkGammaD m hm ha hp 1 (birkEmbed a (p + 1) p (by linarith) y)
        (birkXLam m hm y + birkEmbed a (p + 1) p (by linarith)
            (birkHamBarX m hm ha hp (birkEmbed a (p + 1) p (by linarith) y)) +
          birkEmbed a (p + 1) p (by linarith)
            (birkHamNorX m hm ha hp (birkEmbed a (p + 1) p (by linarith) y)) +
          birkEmbed a (p + 1) p (by linarith)
            (birkXKExt m hm ha hp (birkEmbed a (p + 1) p (by linarith) y))) =
        birkXLam m hm z + birkEmbed a (p + 1) p (by linarith)
          (birkHamGX m hm ha hp
            (birkGamma m hm ha hp 1 (birkEmbed a (p + 1) p (by linarith) y))) := by
  set ι := birkEmbed a (p + 1) p (by linarith) with hι
  set w := ι y with hw
  have hw40 : 40 * birkCF m p * ‖w‖ ^ 2 < 1 := by
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  have hzz : ι (y + birkPsiExt m hm ha hp w) = birkGamma m hm ha hp 1 w := by
    rw [map_add, birkPsiExt_embed (ha := ha) (hm := hm) (hp := hp) w hw40]; abel
  refine ⟨y + birkPsiExt m hm ha hp w, hzz, ?_⟩
  set z := y + birkPsiExt m hm ha hp w with hz
  set Γw := birkGamma m hm ha hp 1 w with hΓw
  set A := birkGammaD m hm ha hp 1 w with hA
  obtain ⟨B, hAB, hBA, -⟩ := birkInvDataExt (ha := ha) (hm := hm) (hp := hp) w hw40
  set Ω := birkOmega ha (by linarith : (0 : ℝ) ≤ p) with hΩ
  have hsymp := fun ξ η' => birkGammaD_symplectic (ha := ha) (hm := hm) (hp := hp) 1 w ξ η'
    (by norm_num) hw40
  -- analytic pieces
  have hΓa : AnalyticAt ℂ (birkGamma m hm ha hp 1) w :=
    birkGamma_analyticOnNhd (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w hw40
  have hΛa : ∀ y', AnalyticAt ℂ (birkLambda m hm ha hp) y' := fun y' =>
    (birkLambda_analyticOnNhd (m := m) (hm := hm) (ha := ha) (hp := hp)) y' (Set.mem_univ _)
  have hGa : ∀ y', AnalyticAt ℂ (birkHamG m hm ha hp) y' := fun y' =>
    (birkHamG_isClassA m hm ha hp).analytic y' (Set.mem_univ _)
  have hBa : ∀ y', AnalyticAt ℂ (birkHamBar m hm ha hp) y' := fun y' =>
    (birkQuart_isClassA m hm ha hp (birkCoefBar_isCoef m hm)).analytic y' (Set.mem_univ _)
  have hNa : ∀ y', AnalyticAt ℂ (birkHamNor m hm ha hp) y' := fun y' =>
    (birkQuart_isClassA m hm ha hp (birkCoefNor_isCoef m hm)).analytic y' (Set.mem_univ _)
  -- the derivative of `K`
  have hDK : ∀ η' : BirkSpace, fderiv ℂ (birkKExt m hm ha hp) w η' =
      fderiv ℂ (birkLambda m hm ha hp) Γw (A η') + fderiv ℂ (birkHamG m hm ha hp) Γw (A η') -
        fderiv ℂ (birkLambda m hm ha hp) w η' - fderiv ℂ (birkHamBar m hm ha hp) w η' -
          fderiv ℂ (birkHamNor m hm ha hp) w η' := fun η' => by
    have c1 := fderiv_comp_birkGamma (ha := ha) (hm := hm) (hp := hp) (P := birkLambda m hm ha hp)
      w hw40 (hΛa _) η'
    have c2 := fderiv_comp_birkGamma (ha := ha) (hm := hm) (hp := hp) (P := birkHamG m hm ha hp)
      w hw40 (hGa _) η'
    have d1 : AnalyticAt ℂ (fun w' => birkLambda m hm ha hp (birkGamma m hm ha hp 1 w')) w :=
      (hΛa _).comp hΓa
    have d2 : AnalyticAt ℂ (fun w' => birkHamG m hm ha hp (birkGamma m hm ha hp 1 w')) w :=
      (hGa _).comp hΓa
    unfold birkKExt
    rw [fderiv_fun_sub (f := fun y' => birkLambda m hm ha hp (birkGamma m hm ha hp 1 y') +
        birkHamG m hm ha hp (birkGamma m hm ha hp 1 y') - birkLambda m hm ha hp y' -
        birkHamBar m hm ha hp y') (g := birkHamNor m hm ha hp)
      (((d1.add d2).sub (hΛa w)).sub (hBa w)).differentiableAt (hNa w).differentiableAt,
      fderiv_fun_sub (f := fun y' => birkLambda m hm ha hp (birkGamma m hm ha hp 1 y') +
        birkHamG m hm ha hp (birkGamma m hm ha hp 1 y') - birkLambda m hm ha hp y')
        (g := birkHamBar m hm ha hp) ((d1.add d2).sub (hΛa w)).differentiableAt
        (hBa w).differentiableAt,
      fderiv_fun_sub (f := fun y' => birkLambda m hm ha hp (birkGamma m hm ha hp 1 y') +
        birkHamG m hm ha hp (birkGamma m hm ha hp 1 y')) (g := birkLambda m hm ha hp)
        (d1.add d2).differentiableAt (hΛa w).differentiableAt,
      fderiv_fun_add d1.differentiableAt d2.differentiableAt]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
    rw [c1, c2]
  -- the fields
  have fΛ : ∀ η', fderiv ℂ (birkLambda m hm ha hp) w η' = Ω (birkXLam m hm y) η' := fun η' =>
    birkLambda_field m hm ha hp y η'
  have fΛz : ∀ η', fderiv ℂ (birkLambda m hm ha hp) Γw η' = Ω (birkXLam m hm z) η' := fun η' => by
    rw [← hzz]; exact birkLambda_field m hm ha hp z η'
  have fG : ∀ η', fderiv ℂ (birkHamG m hm ha hp) Γw η' = Ω (ι (birkHamGX m hm ha hp Γw)) η' :=
    fun η' => (birkHamG_isClassA m hm ha hp).field Γw (Set.mem_univ _) η'
  have fB : ∀ η', fderiv ℂ (birkHamBar m hm ha hp) w η' = Ω (ι (birkHamBarX m hm ha hp w)) η' :=
    fun η' => (birkQuart_isClassA m hm ha hp (birkCoefBar_isCoef m hm)).field w
      (Set.mem_univ _) η'
  have fN : ∀ η', fderiv ℂ (birkHamNor m hm ha hp) w η' = Ω (ι (birkHamNorX m hm ha hp w)) η' :=
    fun η' => (birkQuart_isClassA m hm ha hp (birkCoefNor_isCoef m hm)).field w
      (Set.mem_univ _) η'
  have fK : ∀ η', fderiv ℂ (birkKExt m hm ha hp) w η' =
      Ω (ι (birkXKExt m hm ha hp w)) η' := fun η' =>
    birkKExt_field (ha := ha) (hm := hm) (hp := hp) w (by
      have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
      exact hy) η'
  -- nondegeneracy
  set Xtot := birkXLam m hm y + ι (birkHamBarX m hm ha hp w) + ι (birkHamNorX m hm ha hp w) +
    ι (birkXKExt m hm ha hp w) with hXtot
  have key : ∀ η', Ω (A Xtot) (A η') =
      Ω (birkXLam m hm z + ι (birkHamGX m hm ha hp Γw)) (A η') := by
    intro η'
    rw [hsymp]
    have h1 := hDK η'
    rw [fK η', fΛz, fG, fΛ, fB, fN] at h1
    simp only [hXtot, map_add, ContinuousLinearMap.add_apply]
    linear_combination h1
  refine sub_eq_zero.1 (birkOmega_nondegenerate ha (by linarith : (0 : ℝ) ≤ p) (fun v => ?_))
  have hv : v = A (B v) := by
    have := DFunLike.congr_fun hAB v
    simpa using this.symm
  rw [map_sub, ContinuousLinearMap.sub_apply, hv, key, sub_self]

end KAM.Wave

end
