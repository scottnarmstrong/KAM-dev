/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainK

/-!
# The `𝔚⁺`-inverse of `DΓ` as an analytic family (blueprint-W `bpW:w3:main`, Step XK1)

Package W3-MAIN, blueprint label `bpW:w3:main`.

`birkPsiExt = liePsiSum` with `ι ψ(w) = Γ(w) - w`; `birkXiExt w = Dψ(w) : 𝔚 → 𝔚⁺` (so
`ι ∘ Ξ = DΓ - I`), `birkAFExt w = I + Ξ ι` (`DΓ` on `𝔚⁺`) and
`birkBFExt w = (birkAFExt w)⁻¹`, all analytic
in `w`. `birkInvDataExt`: `birkBFExt` is the two-sided inverse, with norm `≤ 2` and
`‖(birkBFExt - 1) f‖ ≤ 20 C_F ‖w‖² ‖f‖`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- Internal totalized helper (meaningful on `B_{ρ₀}`; public object `birkPsi`, `MainBall`):
`ψ = Γ - id` as a `𝔚⁺`-valued map (`ι ψ = Γ - id`). -/
def birkPsiExt : BirkSpace → BirkSpace :=
  liePsiSum (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) 1

/-- Internal totalized helper (meaningful on `B_{ρ₀}`; public object `birkXi`): `Ξ(w) = Dψ(w)`. -/
def birkXiExt (w : BirkSpace) : BirkSpace →L[ℂ] BirkSpace := fderiv ℂ (birkPsiExt m hm ha hp) w

/-- Internal totalized helper (meaningful on `B_{ρ₀}`; public object `birkAF`): `DΓ(w)` on `𝔚⁺`:
`I + Ξ(w) ι`. -/
def birkAFExt (w : BirkSpace) : BirkSpace →L[ℂ] BirkSpace :=
  1 + (birkXiExt m hm ha hp w).comp (birkEmbed a (p + 1) p (by linarith))

/-- Internal totalized helper (`Ring.inverse`; a two-sided inverse only on `B_{ρ₀}`,
`birkInvDataExt`; public object `birkBF`): `DΓ(w)⁻¹` on `𝔚⁺`. -/
def birkBFExt (w : BirkSpace) : BirkSpace →L[ℂ] BirkSpace := Ring.inverse (birkAFExt m hm ha hp w)

variable {m hm ha hp}

include hm hp in
theorem birkPsiExt_embed (w : BirkSpace) (hw : 40 * birkCF m p * ‖w‖ ^ 2 < 1) :
    birkEmbed a (p + 1) p (by linarith) (birkPsiExt m hm ha hp w) =
      birkGamma m hm ha hp 1 w - w := by
  have hCp := birkCF_pos m hm hp
  have hSn : ‖birkS m hm ha hp‖ ≤ birkCF m p :=
    ContinuousMultilinearMap.opNorm_le_bound hCp.le (norm_birkS_le m hm ha hp)
  exact map_liePsiSum (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) hCp.le
    (norm_birkEmbed_le _ _ _ _) hSn 1 w (birk_q_le (hm := hm) (hp := hp) 1 w (by norm_num) hw)

include hm hp in
theorem birkPsiExt_analyticAt (w : BirkSpace) (hw : 40 * birkCF m p * ‖w‖ ^ 2 < 1) :
    AnalyticAt ℂ (birkPsiExt m hm ha hp) w := by
  have hCp := birkCF_pos m hm hp
  have hSn : ‖birkS m hm ha hp‖ ≤ birkCF m p :=
    ContinuousMultilinearMap.opNorm_le_bound hCp.le (norm_birkS_le m hm ha hp)
  exact analyticAt_liePsiSum (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) hCp.le
    (norm_birkEmbed_le _ _ _ _) hSn hCp 1 w (by norm_num) hw

include hm hp in
/-- `ι ∘ Ξ(w) = DΓ(w) - I`. -/
theorem birkXiExt_embed (w : BirkSpace) (hw : 40 * birkCF m p * ‖w‖ ^ 2 < 1) :
    (birkEmbed a (p + 1) p (by linarith)).comp (birkXiExt m hm ha hp w) =
      birkGammaD m hm ha hp 1 w - 1 := by
  have hψ : HasFDerivAt (birkPsiExt m hm ha hp) (birkXiExt m hm ha hp w) w :=
    (birkPsiExt_analyticAt (ha := ha) (hm := hm) (hp := hp) w hw).differentiableAt.hasFDerivAt
  have h1 : HasFDerivAt (fun w' => birkEmbed a (p + 1) p (by linarith) (birkPsiExt m hm ha hp w'))
      (((birkEmbed a (p + 1) p (by linarith)).restrictScalars ℝ).comp
        ((birkXiExt m hm ha hp w).restrictScalars ℝ)) w :=
    ((birkEmbed a (p + 1) p (by linarith)).restrictScalars ℝ).hasFDerivAt.comp w
      (hψ.restrictScalars ℝ)
  have h2 : HasFDerivAt (fun w' => birkGamma m hm ha hp 1 w' - w')
      ((birkGammaD m hm ha hp 1 w).restrictScalars ℝ - ContinuousLinearMap.id ℝ BirkSpace) w :=
    (birkGamma_hasFDerivAt (ha := ha) (hm := hm) (hp := hp) 1 w (by norm_num) hw).sub
      (hasFDerivAt_id w)
  have hev : (fun w' => birkEmbed a (p + 1) p (by linarith) (birkPsiExt m hm ha hp w')) =ᶠ[nhds w]
      fun w' => birkGamma m hm ha hp 1 w' - w' := by
    have hopen : IsOpen {w' : BirkSpace | 40 * birkCF m p * ‖w'‖ ^ 2 < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hw] with w' hw' using birkPsiExt_embed (ha := ha) (hm := hm)
      (hp := hp) w' hw'
  have := (h1.congr_of_eventuallyEq hev.symm).unique h2
  refine ContinuousLinearMap.ext fun v => ?_
  have := DFunLike.congr_fun this v
  simpa using this

include hm hp in
/-- The inverse data of `DΓ(w)` on `𝔚` and on `𝔚⁺`, with `birkBFExt` the inverse on `𝔚⁺`. -/
theorem birkInvDataExt (w : BirkSpace) (hw : 40 * birkCF m p * ‖w‖ ^ 2 < 1) :
    ∃ B : BirkSpace →L[ℂ] BirkSpace, birkGammaD m hm ha hp 1 w * B = 1 ∧
      B * birkGammaD m hm ha hp 1 w = 1 ∧
      (birkEmbed a (p + 1) p (by linarith)).comp (birkBFExt m hm ha hp w) =
        B.comp (birkEmbed a (p + 1) p (by linarith)) ∧
      ‖birkBFExt m hm ha hp w‖ ≤ 2 ∧ birkAFExt m hm ha hp w * birkBFExt m hm ha hp w = 1 ∧
      birkBFExt m hm ha hp w * birkAFExt m hm ha hp w = 1 ∧
      ∀ f, ‖birkBFExt m hm ha hp w f - f‖ ≤ 20 * birkCF m p * ‖w‖ ^ 2 * ‖f‖ := by
  have hq := birk_q_le (hm := hm) (hp := hp) 1 w (by norm_num) hw
  obtain ⟨Ξ, B, BF, Ξ', hAB, hBA, hB2, hΞ, hΞn, hAι, hF1, hF2, hF3, hιB, hΞ'e, hΞ'n⟩ :=
    birkGammaD_inverse_plus (ha := ha) (hm := hm) (hp := hp) 1 w hq
  have hinj := birkEmbed_injective a (p + 1) p (by linarith)
  have hΞeq : Ξ = birkXiExt m hm ha hp w := by
    refine ContinuousLinearMap.ext fun v => hinj ?_
    have h1 := DFunLike.congr_fun hΞ v
    have h2 := DFunLike.congr_fun (birkXiExt_embed (ha := ha) (hm := hm) (hp := hp) w hw) v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at h1 h2
    rw [h1, h2]
  have hAF : birkAFExt m hm ha hp w = 1 + Ξ.comp (birkEmbed a (p + 1) p (by linarith)) := by
    rw [hΞeq]; rfl
  have hF1' : birkAFExt m hm ha hp w * BF = 1 := by rw [hAF]; exact hF1
  have hF2' : BF * birkAFExt m hm ha hp w = 1 := by rw [hAF]; exact hF2
  have hu : IsUnit (birkAFExt m hm ha hp w) := ⟨⟨birkAFExt m hm ha hp w, BF, hF1', hF2'⟩, rfl⟩
  have hBFeq : birkBFExt m hm ha hp w = BF := by
    unfold birkBFExt
    calc Ring.inverse (birkAFExt m hm ha hp w)
        = Ring.inverse (birkAFExt m hm ha hp w) * (birkAFExt m hm ha hp w * BF) := by
          rw [hF1', mul_one]
      _ = (Ring.inverse (birkAFExt m hm ha hp w) * birkAFExt m hm ha hp w) * BF := by rw [mul_assoc]
      _ = BF := by rw [Ring.inverse_mul_cancel _ hu, one_mul]
  rw [hBFeq]
  refine ⟨B, hAB, hBA, hιB, hF3, hF1', hF2', fun f => ?_⟩
  have hξ : BF f - f = Ξ' (birkEmbed a (p + 1) p (by linarith) f) := by
    refine hinj ?_
    have h1 := DFunLike.congr_fun hιB f
    have h2 := DFunLike.congr_fun hΞ'e (birkEmbed a (p + 1) p (by linarith) f)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at h1 h2
    rw [map_sub, h1, h2]
  rw [hξ]
  refine (Ξ'.le_opNorm _).trans ?_
  have hι0 := norm_birkEmbed_le a (p + 1) p (by linarith)
  have hι : ‖birkEmbed a (p + 1) p (by linarith) f‖ ≤ ‖f‖ := by
    refine ((birkEmbed a (p + 1) p (by linarith)).le_opNorm f).trans ?_
    calc ‖birkEmbed a (p + 1) p (by linarith)‖ * ‖f‖ ≤ 1 * ‖f‖ :=
          mul_le_mul_of_nonneg_right hι0 (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  calc ‖Ξ'‖ * ‖birkEmbed a (p + 1) p (by linarith) f‖ ≤ (20 * |(1 : ℝ)| * birkCF m p * ‖w‖ ^ 2) *
      ‖f‖ := mul_le_mul hΞ'n hι (norm_nonneg _)
        (by have := (birkCF_pos m hm hp).le; positivity)
    _ = 20 * birkCF m p * ‖w‖ ^ 2 * ‖f‖ := by rw [abs_one]; ring

variable (m hm ha hp) in
/-- Internal totalized helper (meaningful on `B_{ρ₁}`; public object `birkXK1`):
`X_{K₁}(w) = DΓ(w)⁻¹ X_G(Γ w) - X_G(w)`, `𝔚⁺`-valued. -/
def birkXK1Ext (w : BirkSpace) : BirkSpace :=
  birkBFExt m hm ha hp w (birkHamGX m hm ha hp (birkGamma m hm ha hp 1 w)) - birkHamGX m hm ha hp w

include hm hp in
/-- (`bpW:w3:main`, Step XK1) `DK₁(w) v = Ω(X_{K₁}(w), v)`. -/
theorem birkK1Ext_field (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) (v : BirkSpace) :
    fderiv ℂ (birkK1Ext m hm ha hp) w v =
      birkOmegaPlus a p ha (by linarith) (birkXK1Ext m hm ha hp w) v := by
  have hw40 : 40 * birkCF m p * ‖w‖ ^ 2 < 1 := by
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  obtain ⟨B, hAB, hBA, hιB, hBF2, hAF1, hAF2, hBFn⟩ :=
    birkInvDataExt (ha := ha) (hm := hm) (hp := hp) w hw40
  have hΓa : AnalyticAt ℂ (birkGamma m hm ha hp 1) w :=
    birkGamma_analyticOnNhd (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w hw40
  have hGa : ∀ y, AnalyticAt ℂ (birkHamG m hm ha hp) y := fun y =>
    (birkHamG_isClassA m hm ha hp).analytic y (Set.mem_univ _)
  have hcomp : AnalyticAt ℂ (fun w' => birkHamG m hm ha hp (birkGamma m hm ha hp 1 w')) w :=
    (hGa _).comp hΓa
  set y := birkGamma m hm ha hp 1 w with hy
  set dP := fderiv ℂ (birkHamG m hm ha hp) y with hdP
  have hP : HasFDerivAt (birkHamG m hm ha hp) dP y := (hGa y).differentiableAt.hasFDerivAt
  have hX : ∀ u, dP u = birkOmega ha (by linarith : 0 ≤ p)
      (birkEmbed a (p + 1) p (by linarith) (birkHamGX m hm ha hp y)) u := fun u =>
    (birkHamG_isClassA m hm ha hp).field y (Set.mem_univ _) u
  obtain ⟨h1, h2, -⟩ := birk_gradient_transport (ha := ha) (hm := hm) (hp := hp) 1 w
    (by norm_num) hw40 _ dP hP _ hX B hAB
  have hD : fderiv ℂ (fun w' => birkHamG m hm ha hp (birkGamma m hm ha hp 1 w')) w v =
      dP (birkGammaD m hm ha hp 1 w v) := by
    have h3 := (hcomp.differentiableAt.hasFDerivAt.restrictScalars ℝ).unique h1
    have := DFunLike.congr_fun h3 v
    simpa using this
  have hG : fderiv ℂ (birkHamG m hm ha hp) w v =
      birkOmegaPlus a p ha (by linarith) (birkHamGX m hm ha hp w) v :=
    (birkHamG_isClassA m hm ha hp).field w (Set.mem_univ _) v
  have hsub : fderiv ℂ (birkK1Ext m hm ha hp) w v =
      fderiv ℂ (fun w' => birkHamG m hm ha hp (birkGamma m hm ha hp 1 w')) w v -
        fderiv ℂ (birkHamG m hm ha hp) w v := by
    unfold birkK1Ext
    rw [fderiv_fun_sub hcomp.differentiableAt (hGa w).differentiableAt]
    rfl
  have hι' : birkEmbed a (p + 1) p (by linarith) (birkBFExt m hm ha hp w (birkHamGX m hm ha hp y)) =
      B (birkEmbed a (p + 1) p (by linarith) (birkHamGX m hm ha hp y)) := by
    have := DFunLike.congr_fun hιB (birkHamGX m hm ha hp y)
    simpa using this
  rw [hsub, hD, hG, h2 v]
  unfold birkXK1Ext birkOmegaPlus
  rw [map_sub, hι', map_sub, ContinuousLinearMap.sub_apply]

include hm hp in
/-- (`bpW:w3:main`, Step XK1) `‖X_{K₁}(w)‖₊ ≤ 44 C_* C_F ‖w‖⁵`. -/
theorem norm_birkXK1Ext_le (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    ‖birkXK1Ext m hm ha hp w‖ ≤ 44 * waveCubicConst p * birkCF m p * ‖w‖ ^ 5 := by
  have hw40 : 40 * birkCF m p * ‖w‖ ^ 2 < 1 := by
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  have hCs := waveCubicConst_nonneg p
  have hCF := (birkCF_pos m hm hp).le
  have hw0 := norm_nonneg w
  obtain ⟨B, hAB, hBA, hιB, hBF2, hAF1, hAF2, hBFn⟩ :=
    birkInvDataExt (ha := ha) (hm := hm) (hp := hp) w hw40
  have hq : 2 * |(1 : ℝ)| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10 := by
    rw [abs_one]
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg hCF (sq_nonneg _)
    nlinarith
  have hΓ := norm_birkGamma_le (ha := ha) (hm := hm) (hp := hp) 1 w hq
  have hd := norm_birkGamma_sub_le (ha := ha) (hm := hm) (hp := hp) 1 w hq
  rw [abs_one] at hd
  set y := birkGamma m hm ha hp 1 w with hy
  have hX1 := norm_birkQuartX_sub_le m hm ha hp (birkCoefAll_isCoef m hm) y w
  have hX2 := norm_birkHamGX_le m hm ha hp w
  have hmax : max ‖y‖ ‖w‖ ≤ 10 / 9 * ‖w‖ := max_le hΓ (by linarith)
  have hmax2 : (max ‖y‖ ‖w‖) ^ 2 ≤ (10 / 9 * ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (le_trans (norm_nonneg _) (le_max_left _ _)) hmax 2
  have hdiff : ‖birkHamGX m hm ha hp y - birkHamGX m hm ha hp w‖ ≤
      3 * waveCubicConst p * (10 / 9 * ‖w‖) ^ 2 * (3 * birkCF m p * ‖w‖ ^ 3) := by
    calc _ ≤ 3 * waveCubicConst p * (max ‖y‖ ‖w‖) ^ 2 * ‖y - w‖ := hX1
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hmax2 (by positivity))
          (by linarith [hd]) (norm_nonneg _) (by positivity)
  have hsplit : birkXK1Ext m hm ha hp w = birkBFExt m hm ha hp w
      (birkHamGX m hm ha hp y - birkHamGX m hm ha hp w) +
      (birkBFExt m hm ha hp w (birkHamGX m hm ha hp w) - birkHamGX m hm ha hp w) := by
    unfold birkXK1Ext; rw [map_sub]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have t1 : ‖birkBFExt m hm ha hp w (birkHamGX m hm ha hp y - birkHamGX m hm ha hp w)‖ ≤
      2 * (3 * waveCubicConst p * (10 / 9 * ‖w‖) ^ 2 * (3 * birkCF m p * ‖w‖ ^ 3)) :=
    ((birkBFExt m hm ha hp w).le_opNorm _).trans
      (mul_le_mul hBF2 hdiff (norm_nonneg _) (by norm_num))
  have t2 : ‖birkBFExt m hm ha hp w (birkHamGX m hm ha hp w) - birkHamGX m hm ha hp w‖ ≤
      20 * birkCF m p * ‖w‖ ^ 2 * (waveCubicConst p * ‖w‖ ^ 3) :=
    (hBFn _).trans (mul_le_mul_of_nonneg_left hX2 (by positivity))
  have hnn : 0 ≤ waveCubicConst p * birkCF m p * ‖w‖ ^ 5 := by positivity
  nlinarith [t1, t2]

include hm hp in
/-- `X_{K₁}` is analytic into `𝔚⁺` on `B_{ρ₁}`. -/
theorem birkXK1Ext_analyticAt (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    AnalyticAt ℂ (birkXK1Ext m hm ha hp) w := by
  have hw40 : 40 * birkCF m p * ‖w‖ ^ 2 < 1 := by
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  obtain ⟨B, hAB, hBA, hιB, hBF2, hAF1, hAF2, hBFn⟩ :=
    birkInvDataExt (ha := ha) (hm := hm) (hp := hp) w hw40
  have hψ : AnalyticAt ℂ (birkPsiExt m hm ha hp) w :=
    birkPsiExt_analyticAt (ha := ha) (hm := hm) (hp := hp) w hw40
  have hΞ : AnalyticAt ℂ (birkXiExt m hm ha hp) w := hψ.fderiv
  have hAF : AnalyticAt ℂ (birkAFExt m hm ha hp) w := by
    unfold birkAFExt
    exact analyticAt_const.add
      (((ContinuousLinearMap.compL ℂ BirkSpace BirkSpace BirkSpace).flip
        (birkEmbed a (p + 1) p (by linarith))).analyticAt _ |>.comp hΞ)
  have hu : IsUnit (birkAFExt m hm ha hp w) := ⟨⟨_, _, hAF1, hAF2⟩, rfl⟩
  have hBF : AnalyticAt ℂ (birkBFExt m hm ha hp) w :=
    (analyticOnNhd_inverse (𝕜 := ℂ) (birkAFExt m hm ha hp w) hu).comp hAF
  have hΓ : AnalyticAt ℂ (birkGamma m hm ha hp 1) w :=
    birkGamma_analyticOnNhd (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w hw40
  have hXG : ∀ y, AnalyticAt ℂ (birkHamGX m hm ha hp) y := fun y =>
    (birkHamG_isClassA m hm ha hp).analytic_field y (Set.mem_univ _)
  unfold birkXK1Ext
  have hap : AnalyticAt ℂ (fun z : (BirkSpace →L[ℂ] BirkSpace) × BirkSpace => z.1 z.2)
      (birkBFExt m hm ha hp w, birkHamGX m hm ha hp (birkGamma m hm ha hp 1 w)) :=
    (ContinuousLinearMap.id ℂ (BirkSpace →L[ℂ] BirkSpace)).analyticAt_bilinear _
  exact (AnalyticAt.comp (g := fun z : (BirkSpace →L[ℂ] BirkSpace) × BirkSpace => z.1 z.2)
    (f := fun x => (birkBFExt m hm ha hp x,
      birkHamGX m hm ha hp (birkGamma m hm ha hp 1 x))) hap
    (hBF.prod ((hXG _).comp hΓ))).sub (hXG w)

end KAM.Wave

end
