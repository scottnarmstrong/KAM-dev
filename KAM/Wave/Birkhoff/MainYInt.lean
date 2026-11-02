/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainK3

/-!
# The integrand `Y(t,w)` of the remainder field (blueprint-W `bpW:w3:Yseries`, eq. `bpW:w3:Ydef`)

Package W3-MAIN, blueprint label `bpW:w3:Yseries` (definition `bpW:w3:Ydef`).

Domains (public carriers are restricted to them):
* `birkBall0 m p = B_{ρ₀} = {w | 40 C_F ‖w‖² < 1}`,
  `birkBall1 m p = B_{ρ₁} = {w | 160 C_F ‖w‖² < 1}`;
* `birkGammaDPlus t w` (`t ∈ (-2,2)`, `w ∈ B_{ρ₀}`): `DΓ_t(w)` as an operator on `𝔚⁺`, characterized
  by `ι ∘ DΓ_t(w)|_{𝔚⁺} = DΓ_t(w) ∘ ι` (`birkGammaDPlus_embed`), invertible
  (`birkGammaDPlus_mul_inv`, `birkGammaDPlusInv_mul`) with inverse `birkGammaDPlusInv t w` of
  norm `≤ 2`;
* `birkY t w` (`t ∈ [0,1]`, `w ∈ B_{ρ₁}`): the integrand
  `Y(t,w) = DΓ_t(w)⁻¹ X_{Z'}(Γ_t w) - X_{Z'}(w) ∈ 𝔚⁺`, with `birkY_eq_tsum`:
  `Y(t,w) = Σ_n t^n V_n(w,…,w) - V_0(w,…,w)`.

The totalized helpers `birkPsiTExt`, `birkXiTExt`, `birkAFTExt` (internal; meaningful only for
`|t| < 2`, `w ∈ B_{ρ₀}`) carry the series construction of `ψ_t = Γ_t - id` and its derivative.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- The ball `B_{ρ₀} = {w | 40 C_F ‖w‖² < 1}` (`ρ₀ = (40 C_F)^{-1/2}`). -/
def birkBall0 (m p : ℝ) : Set BirkSpace := {w | 40 * birkCF m p * ‖w‖ ^ 2 < 1}

/-- The ball `B_{ρ₁} = {w | 160 C_F ‖w‖² < 1}` (`ρ₁ = ρ₀ / 2`). -/
def birkBall1 (m p : ℝ) : Set BirkSpace := {w | 160 * birkCF m p * ‖w‖ ^ 2 < 1}

theorem birkBall1_subset_birkBall0 (m : ℝ) (hm : 0 < m) {p : ℝ} (hp : 1 / 2 ≤ p) :
    birkBall1 m p ⊆ birkBall0 m p := fun w hw => by
  have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
  have hw' : 160 * birkCF m p * ‖w‖ ^ 2 < 1 := hw
  show 40 * birkCF m p * ‖w‖ ^ 2 < 1
  nlinarith

theorem isOpen_birkBall0 (m p : ℝ) : IsOpen (birkBall0 m p) :=
  isOpen_lt (by fun_prop) continuous_const

theorem isOpen_birkBall1 (m p : ℝ) : IsOpen (birkBall1 m p) :=
  isOpen_lt (by fun_prop) continuous_const

theorem birkRho_mem_birkBall1 {w : BirkSpace} (hw : w ∈ birkBall1 m p) :
    birkRho w ∈ birkBall1 m p := by
  show 160 * birkCF m p * ‖birkRho w‖ ^ 2 < 1
  rw [birkRho.norm_map]; exact hw

/-- Internal (totalized; meaningful for `|t| < 2`, `w ∈ B_{ρ₀}`): `ψ_t = Γ_t - id` as a
`𝔚⁺`-valued series. -/
def birkPsiTExt (t : ℝ) : BirkSpace → BirkSpace :=
  liePsiSum (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) t

/-- Internal: `Ξ_t(w) = Dψ_t(w) : 𝔚 → 𝔚⁺`. -/
def birkXiTExt (t : ℝ) (w : BirkSpace) : BirkSpace →L[ℂ] BirkSpace :=
  fderiv ℂ (birkPsiTExt m hm ha hp t) w

/-- Internal: `I + Ξ_t(w) ι`, i.e. `DΓ_t(w)` on `𝔚⁺`. -/
def birkAFTExt (t : ℝ) (w : BirkSpace) : BirkSpace →L[ℂ] BirkSpace :=
  1 + (birkXiTExt m hm ha hp t w).comp (birkEmbed a (p + 1) p (by linarith))

variable {m hm ha hp}

section Ext

variable (t : ℝ) (ht : |t| < 2) (w : BirkSpace) (hw : w ∈ birkBall0 m p)

include hm hp ht hw in
theorem birkPsiTExt_embed :
    birkEmbed a (p + 1) p (by linarith) (birkPsiTExt m hm ha hp t w) =
      birkGamma m hm ha hp t w - w := by
  have hCp := birkCF_pos m hm hp
  have hSn : ‖birkS m hm ha hp‖ ≤ birkCF m p :=
    ContinuousMultilinearMap.opNorm_le_bound hCp.le (norm_birkS_le m hm ha hp)
  exact map_liePsiSum (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) hCp.le
    (norm_birkEmbed_le _ _ _ _) hSn t w (birk_q_le (hm := hm) (hp := hp) t w ht hw)

include hm hp ht hw in
theorem birkPsiTExt_analyticAt : AnalyticAt ℂ (birkPsiTExt m hm ha hp t) w := by
  have hCp := birkCF_pos m hm hp
  have hSn : ‖birkS m hm ha hp‖ ≤ birkCF m p :=
    ContinuousMultilinearMap.opNorm_le_bound hCp.le (norm_birkS_le m hm ha hp)
  exact analyticAt_liePsiSum (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) hCp.le
    (norm_birkEmbed_le _ _ _ _) hSn hCp t w ht hw

include hm hp ht hw in
/-- `ι ∘ Ξ_t(w) = DΓ_t(w) - I`. -/
theorem birkXiTExt_embed :
    (birkEmbed a (p + 1) p (by linarith)).comp (birkXiTExt m hm ha hp t w) =
      birkGammaD m hm ha hp t w - 1 := by
  have hψ : HasFDerivAt (birkPsiTExt m hm ha hp t) (birkXiTExt m hm ha hp t w) w :=
    (birkPsiTExt_analyticAt (hm := hm) (hp := hp) (ha := ha) t ht w hw).differentiableAt.hasFDerivAt
  have h1 : HasFDerivAt (fun w' => birkEmbed a (p + 1) p (by linarith)
        (birkPsiTExt m hm ha hp t w'))
      (((birkEmbed a (p + 1) p (by linarith)).restrictScalars ℝ).comp
        ((birkXiTExt m hm ha hp t w).restrictScalars ℝ)) w :=
    ((birkEmbed a (p + 1) p (by linarith)).restrictScalars ℝ).hasFDerivAt.comp w
      (hψ.restrictScalars ℝ)
  have h2 : HasFDerivAt (fun w' => birkGamma m hm ha hp t w' - w')
      ((birkGammaD m hm ha hp t w).restrictScalars ℝ - ContinuousLinearMap.id ℝ BirkSpace) w :=
    (birkGamma_hasFDerivAt (ha := ha) (hm := hm) (hp := hp) t w ht hw).sub (hasFDerivAt_id w)
  have hev : (fun w' => birkEmbed a (p + 1) p (by linarith) (birkPsiTExt m hm ha hp t w'))
      =ᶠ[nhds w] fun w' => birkGamma m hm ha hp t w' - w' := by
    filter_upwards [(isOpen_birkBall0 m p).mem_nhds hw] with w' hw' using
      birkPsiTExt_embed (hm := hm) (hp := hp) (ha := ha) t ht w' hw'
  have := (h1.congr_of_eventuallyEq hev.symm).unique h2
  refine ContinuousLinearMap.ext fun v => ?_
  have := DFunLike.congr_fun this v
  simpa using this

include hm hp ht hw in
/-- `ι ∘ (I + Ξ_t(w) ι) = DΓ_t(w) ∘ ι`. -/
theorem birkAFTExt_embed :
    (birkEmbed a (p + 1) p (by linarith)).comp (birkAFTExt m hm ha hp t w) =
      (birkGammaD m hm ha hp t w).comp (birkEmbed a (p + 1) p (by linarith)) := by
  refine ContinuousLinearMap.ext fun f => ?_
  have h := DFunLike.congr_fun (birkXiTExt_embed (hm := hm) (hp := hp) (ha := ha) t ht w hw)
    (birkEmbed a (p + 1) p (by linarith) f)
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    one_apply_eq_self] at h
  simp only [birkAFTExt, ContinuousLinearMap.comp_apply, add_apply,
    one_apply_eq_self, map_add, h]
  abel

include hm hp ht hw in
/-- `I + Ξ_t(w) ι` is invertible on `𝔚⁺`, with inverse of norm `≤ 2`. -/
theorem birkAFTExt_inverse :
    ∃ BF : BirkSpace →L[ℂ] BirkSpace, birkAFTExt m hm ha hp t w * BF = 1 ∧
      BF * birkAFTExt m hm ha hp t w = 1 ∧ ‖BF‖ ≤ 2 := by
  have hq := birk_q_le (hm := hm) (hp := hp) t w ht hw
  obtain ⟨Ξ, B, BF, Ξ', -, -, -, hΞ, -, -, hF1, hF2, hF3, -⟩ :=
    birkGammaD_inverse_plus (ha := ha) (hm := hm) (hp := hp) t w hq
  have hinj := birkEmbed_injective a (p + 1) p (by linarith)
  have hΞeq : Ξ = birkXiTExt m hm ha hp t w := by
    refine ContinuousLinearMap.ext fun v => hinj ?_
    have h1 := DFunLike.congr_fun hΞ v
    have h2 := DFunLike.congr_fun (birkXiTExt_embed (hm := hm) (hp := hp) (ha := ha) t ht w hw) v
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [h1, h2]
  have hAF : birkAFTExt m hm ha hp t w = 1 + Ξ.comp (birkEmbed a (p + 1) p (by linarith)) := by
    rw [hΞeq]; rfl
  exact ⟨BF, by rw [hAF]; exact hF1, by rw [hAF]; exact hF2, hF3⟩

end Ext

/-! ### Public, domain-restricted objects -/

theorem abs_lt_two_of_mem_Ioo (t : Set.Ioo (-2 : ℝ) 2) : |(t : ℝ)| < 2 :=
  abs_lt.2 ⟨t.2.1, t.2.2⟩

/-- `[0, 1] ⊂ (-2, 2)`. -/
theorem mem_Ioo_of_mem_Icc01 (t : Set.Icc (0 : ℝ) 1) : (t : ℝ) ∈ Set.Ioo (-2 : ℝ) 2 :=
  ⟨by linarith [t.2.1], by linarith [t.2.2]⟩

variable (m hm ha hp) in
/-- (`bpW:w3:flow` (iii)) `DΓ_t(w)` as an operator on `𝔚⁺`, for `|t| < 2` and `w ∈ B_{ρ₀}`
(characterized by `birkGammaDPlus_embed`). -/
def birkGammaDPlus (t : Set.Ioo (-2 : ℝ) 2) (w : birkBall0 m p) : BirkSpace →L[ℂ] BirkSpace :=
  birkAFTExt m hm ha hp t w

variable (m hm ha hp) in
/-- (`bpW:w3:flow` (iii)) `DΓ_t(w)⁻¹` on `𝔚⁺`, for `|t| < 2` and `w ∈ B_{ρ₀}`; it is a two-sided
inverse (`birkGammaDPlus_mul_inv`, `birkGammaDPlusInv_mul`). -/
def birkGammaDPlusInv (t : Set.Ioo (-2 : ℝ) 2) (w : birkBall0 m p) : BirkSpace →L[ℂ] BirkSpace :=
  Ring.inverse (birkGammaDPlus m hm ha hp t w)

section Restricted

variable (t : Set.Ioo (-2 : ℝ) 2) (w : birkBall0 m p)

/-- (`bpW:w3:flow` (iii)) `ι ∘ DΓ_t(w)|_{𝔚⁺} = DΓ_t(w) ∘ ι` (this determines the operator, as
`ι` is injective). -/
theorem birkGammaDPlus_embed :
    (birkEmbed a (p + 1) p (by linarith)).comp (birkGammaDPlus m hm ha hp t w) =
      (birkGammaD m hm ha hp t w).comp (birkEmbed a (p + 1) p (by linarith)) :=
  birkAFTExt_embed (hm := hm) (hp := hp) t (abs_lt_two_of_mem_Ioo t) w w.2

theorem isUnit_birkGammaDPlus : IsUnit (birkGammaDPlus m hm ha hp t w) := by
  obtain ⟨BF, h1, h2, -⟩ :=
    birkAFTExt_inverse (hm := hm) (hp := hp) (ha := ha) t (abs_lt_two_of_mem_Ioo t) w w.2
  exact ⟨⟨_, BF, h1, h2⟩, rfl⟩

theorem birkGammaDPlus_mul_inv :
    birkGammaDPlus m hm ha hp t w * birkGammaDPlusInv m hm ha hp t w = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_birkGammaDPlus t w)

theorem birkGammaDPlusInv_mul :
    birkGammaDPlusInv m hm ha hp t w * birkGammaDPlus m hm ha hp t w = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_birkGammaDPlus t w)

end Restricted

variable (m hm ha hp) in
/-- (`bpW:w3:Yseries`, eq. `bpW:w3:Ydef`) The integrand
`Y(t,w) = DΓ_t(w)⁻¹ X_{Z'}(Γ_t w) - X_{Z'}(w) ∈ 𝔚⁺` for `0 ≤ t ≤ 1`, `w ∈ B_{ρ₁}`, with
`DΓ_t(w)⁻¹` the inverse on `𝔚⁺`. -/
def birkY (t : Set.Icc (0 : ℝ) 1) (w : birkBall1 m p) : BirkSpace :=
  birkGammaDPlusInv m hm ha hp ⟨t, mem_Ioo_of_mem_Icc01 t⟩
      ⟨w, birkBall1_subset_birkBall0 m hm hp w.2⟩
      (birkHamZX m hm ha hp (birkGamma m hm ha hp t w)) -
    birkHamZX m hm ha hp w

/-- `Y(t,w) = V_t - V_0`, `V_t = Σ_n t^n V_n(w,…,w)` (the pullback `DΓ_t(w)⁻¹ X_{Z'}(Γ_t w)`). -/
theorem birkY_eq_tsum (t : Set.Icc (0 : ℝ) 1) (w : birkBall1 m p) :
    birkY m hm ha hp t w = ∑' n : ℕ, ((t : ℝ) ^ n) • birkVn m hm ha hp n (fun _ => (w : BirkSpace))
      - birkVn m hm ha hp 0 (fun _ => (w : BirkSpace)) := by
  set t' : Set.Ioo (-2 : ℝ) 2 := ⟨t, mem_Ioo_of_mem_Icc01 t⟩
  set w' : birkBall0 m p := ⟨w, birkBall1_subset_birkBall0 m hm hp w.2⟩
  set V := ∑' n : ℕ, ((t : ℝ) ^ n) • birkVn m hm ha hp n (fun _ => (w : BirkSpace)) with hV
  have hid := birkV_identity (ha := ha) (hm := hm) (hp := hp) t
    (abs_lt_two_of_mem_Ioo t') w w.2
  have hA : birkGammaDPlus m hm ha hp t' w' V =
      birkHamZX m hm ha hp (birkGamma m hm ha hp t w) := by
    refine birkEmbed_injective a (p + 1) p (by linarith) ?_
    have h := DFunLike.congr_fun (birkGammaDPlus_embed (hm := hm) (ha := ha) (hp := hp) t' w') V
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h]; exact hid
  unfold birkY
  rw [birkVn_zero_const]
  congr 1
  show birkGammaDPlusInv m hm ha hp t' w' _ = V
  have h2 : birkGammaDPlusInv m hm ha hp t' w' (birkGammaDPlus m hm ha hp t' w' V) = V :=
    DFunLike.congr_fun (birkGammaDPlusInv_mul (hm := hm) (ha := ha) (hp := hp) t' w') V
  rw [← hA, h2]

end KAM.Wave

end
