/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieBirk
public import KAM.Wave.Birkhoff.LiePlusInv

/-!
# The flow of `X_F`: `𝔚⁺`-estimates, images and gradient transport
(blueprint-W `bpW:w3:flow` (iii), (vi), `bpW:w3:symplectic`)

Package W3-FLOW, blueprint labels `bpW:w3:flow`, `bpW:w3:symplectic`.

With `ι = birkEmbed a (p+1) p` (the inclusion `𝔚⁺ ⊂ 𝔚`, a map into `𝔚⁺` being a point of
`BirkSpace` read at weight `p + 1`) and `r = 2|t|C_F‖w‖² ≤ 1/10` (true on `|t| < 2`,
`‖w‖ < ρ₀`, `birk_q_le`): `birkGamma_sub_plus` (`Γ_t w - w = ι ψ`, `‖ψ‖₊ ≤ 3|t|C_F‖w‖³`),
`birkGammaD_sub_plus` (`DΓ_t - I = ι Ξ`, `‖Ξ‖_{𝔚→𝔚⁺} ≤ 10|t|C_F‖w‖²`),
`birkGammaD_inverse_plus` (invertibility on `𝔚⁺`, `‖DΓ⁻¹ - I‖_{𝔚→𝔚⁺} ≤ 20|t|C_F‖w‖²`),
`birkGamma_image_subset`, `birkGamma_image_superset`, `birkGamma_injOn` (images of balls),
`birk_gradient_transport` (`X_{P∘Γ_t} = DΓ_t⁻¹ X_P(Γ_t)`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

theorem lieT_birk :
    lieT (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) = birkT m hm ha hp := rfl

variable {m hm ha hp}

include hm hp in
/-- On `|t| < 2`, `40 C_F ‖w‖² < 1` (that is `‖w‖ < ρ₀`): `2|t|C_F‖w‖² ≤ 1/10`. -/
theorem birk_q_le (t : ℝ) (w : BirkSpace) (ht : |t| < 2) (hw : 40 * birkCF m p * ‖w‖ ^ 2 < 1) :
    2 * |t| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10 :=
  q_le_of_dom (birkCF_pos m hm hp) t w ht hw

section
variable (t : ℝ) (w : BirkSpace) (hq : 2 * |t| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10)

include hm hp hq in
/-- (`bpW:w3:flow` (iii)) `Γ_t(w) - w = ι ψ` with `‖ψ‖₊ ≤ 3 |t| C_F ‖w‖³`. -/
theorem birkGamma_sub_plus :
    ∃ ψ : BirkSpace, birkEmbed a (p + 1) p (by linarith) ψ = birkGamma m hm ha hp t w - w ∧
      ‖ψ‖ ≤ 3 * |t| * birkCF m p * ‖w‖ ^ 3 :=
  exists_lieGamma_sub (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp)
    (birkCF_pos m hm hp).le (norm_birkEmbed_le _ _ _ _) (norm_birkS_le m hm ha hp) t w hq

include hm hp hq in
/-- (`bpW:w3:flow` (iii)) `DΓ_t(w) - I = ι ∘ Ξ` with `‖Ξ‖_{𝔚→𝔚⁺} ≤ 10 |t| C_F ‖w‖²`. -/
theorem birkGammaD_sub_plus :
    ∃ Ξ : BirkSpace →L[ℂ] BirkSpace,
      (birkEmbed a (p + 1) p (by linarith)).comp Ξ =
        birkGammaD m hm ha hp t w - ContinuousLinearMap.id ℂ BirkSpace ∧
      ‖Ξ‖ ≤ 10 * |t| * birkCF m p * ‖w‖ ^ 2 :=
  exists_lieGammaD_sub (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp)
    (birkCF_pos m hm hp).le (norm_birkEmbed_le _ _ _ _) (norm_birkS_le m hm ha hp) t w hq

include hm hp hq in
/-- (`bpW:w3:flow` (iii)) `DΓ_t(w)` maps `𝔚⁺` into itself, is invertible on `𝔚` and on `𝔚⁺`
(inverses of norm `≤ 2`, compatible with `ι`), and `DΓ_t(w)⁻¹ - I = ι ∘ Ξ'` with
`‖Ξ'‖_{𝔚→𝔚⁺} ≤ 20 |t| C_F ‖w‖²`. -/
theorem birkGammaD_inverse_plus :
    ∃ (Ξ : BirkSpace →L[ℂ] BirkSpace) (B BF Ξ' : BirkSpace →L[ℂ] BirkSpace),
      birkGammaD m hm ha hp t w * B = 1 ∧ B * birkGammaD m hm ha hp t w = 1 ∧ ‖B‖ ≤ 2 ∧
      (birkEmbed a (p + 1) p (by linarith)).comp Ξ = birkGammaD m hm ha hp t w - 1 ∧
      ‖Ξ‖ ≤ 10 * |t| * birkCF m p * ‖w‖ ^ 2 ∧
      (birkGammaD m hm ha hp t w).comp (birkEmbed a (p + 1) p (by linarith)) =
        (birkEmbed a (p + 1) p (by linarith)).comp (1 + Ξ.comp (birkEmbed a (p + 1) p
          (by linarith))) ∧
      (1 + Ξ.comp (birkEmbed a (p + 1) p (by linarith))) * BF = 1 ∧
      BF * (1 + Ξ.comp (birkEmbed a (p + 1) p (by linarith))) = 1 ∧ ‖BF‖ ≤ 2 ∧
      (birkEmbed a (p + 1) p (by linarith)).comp BF =
        B.comp (birkEmbed a (p + 1) p (by linarith)) ∧
      (birkEmbed a (p + 1) p (by linarith)).comp Ξ' = B - 1 ∧
      ‖Ξ'‖ ≤ 20 * |t| * birkCF m p * ‖w‖ ^ 2 :=
  lie_plus_inverse (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp)
    (birkCF_pos m hm hp).le (norm_birkEmbed_le _ _ _ _) (norm_birkS_le m hm ha hp) t w hq

end

section
variable {ρ : ℝ} (hρ : 160 * birkCF m p * ρ ^ 2 ≤ 1)

include hm hp hρ in
/-- (`bpW:w3:flow` (vi)) `Γ_1(B_ρ) ⊂ B_{10ρ/9}` for `160 C_F ρ² ≤ 1` (`ρ = ρ₁`). -/
theorem birkGamma_image_subset (w : BirkSpace) (hw : ‖w‖ < ρ) :
    ‖birkGamma m hm ha hp 1 w‖ < 10 / 9 * ρ := by
  have hC := (birkCF_pos m hm hp).le
  have hq : 2 * |(1 : ℝ)| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10 := by
    have h1 : ‖w‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw.le 2
    rw [abs_one]
    nlinarith [mul_le_mul_of_nonneg_left h1 hC]
  have := norm_birkGamma_le (ha := ha) (hm := hm) (hp := hp) 1 w hq
  linarith

include hm hp hρ in
/-- (`bpW:w3:flow` (vi)) `Γ_1` is injective on `B_ρ` (`Γ_{-1} Γ_1 = id`). -/
theorem birkGamma_injOn : Set.InjOn (birkGamma m hm ha hp 1) {w | ‖w‖ < ρ} := by
  intro w hw w' hw' h
  have hCp := birkCF_pos m hm hp
  have key : ∀ v : BirkSpace, ‖v‖ < ρ → birkGamma m hm ha hp (-1) (birkGamma m hm ha hp 1 v) = v :=
    fun v hv => by
      refine birkGamma_neg_birkGamma 1 v (by norm_num) ?_
      have h1 : ‖v‖ ^ 2 < ρ ^ 2 := pow_lt_pow_left₀ hv (norm_nonneg _) (by norm_num)
      nlinarith [mul_lt_mul_of_pos_left h1 hCp]
  rw [← key w hw, ← key w' hw', h]

include hm hp hρ in
/-- (`bpW:w3:flow` (vi)) `Γ_1(B_ρ) ⊃ B_{9ρ/10}` for `160 C_F ρ² ≤ 1`. -/
theorem birkGamma_image_superset (y : BirkSpace) (hy : ‖y‖ < 9 / 10 * ρ) :
    ∃ w : BirkSpace, ‖w‖ < ρ ∧ birkGamma m hm ha hp 1 w = y := by
  have hCp := birkCF_pos m hm hp
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) (lt_of_lt_of_le hy (by
    have : 0 ≤ ρ := by
      by_contra hneg; push_neg at hneg
      have := norm_nonneg y
      linarith
    linarith))
  have hy2 : 160 * birkCF m p * ‖y‖ ^ 2 < 1 := by
    have h1 : ‖y‖ ^ 2 < (9 / 10 * ρ) ^ 2 :=
      pow_lt_pow_left₀ hy (norm_nonneg _) (by norm_num)
    nlinarith [mul_lt_mul_of_pos_left h1 hCp, sq_nonneg ρ, mul_nonneg hCp.le (sq_nonneg ρ)]
  have hq : 2 * |(-1 : ℝ)| * birkCF m p * ‖y‖ ^ 2 ≤ 1 / 10 := by
    rw [abs_neg, abs_one]; nlinarith [sq_nonneg ‖y‖, mul_nonneg hCp.le (sq_nonneg ‖y‖)]
  refine ⟨birkGamma m hm ha hp (-1) y, ?_, ?_⟩
  · have := norm_birkGamma_le (ha := ha) (hm := hm) (hp := hp) (-1) y hq
    linarith
  · have := birkGamma_neg_birkGamma (ha := ha) (hm := hm) (hp := hp) (-1) y
      (by norm_num) hy2
    simpa using this

end

include hm hp in
/-- (`bpW:w3:symplectic`, Step Gradient transport) If `P` is complex differentiable at
`Γ_t(w)` with `DP(Γ_t w) u = Ω(X, u)` (`X = X_P(Γ_t w)`), then
`D(P ∘ Γ_t)(w) v = DP(Γ_t w)(DΓ_t(w) v)` (real Fréchet derivative), this equals
`Ω(B X, v)` with `B = DΓ_t(w)⁻¹`, and `B X` is the only vector with this property:
`X_{P∘Γ_t}(w) = DΓ_t(w)⁻¹ X_P(Γ_t w)`. -/
theorem birk_gradient_transport (t : ℝ) (w : BirkSpace) (ht : |t| < 2)
    (hw : 40 * birkCF m p * ‖w‖ ^ 2 < 1) (P : BirkSpace → ℂ) (dP : BirkSpace →L[ℂ] ℂ)
    (hP : HasFDerivAt P dP (birkGamma m hm ha hp t w)) (X : BirkSpace)
    (hX : ∀ u, dP u = birkOmega ha (by linarith : 0 ≤ p) X u) (B : BirkSpace →L[ℂ] BirkSpace)
    (hAB : birkGammaD m hm ha hp t w * B = 1) :
    HasFDerivAt (fun w' => P (birkGamma m hm ha hp t w'))
        ((dP.restrictScalars ℝ).comp ((birkGammaD m hm ha hp t w).restrictScalars ℝ)) w ∧
      (∀ v, dP (birkGammaD m hm ha hp t w v) =
        birkOmega ha (by linarith : 0 ≤ p) (B X) v) ∧
      ∀ Y, (∀ v, dP (birkGammaD m hm ha hp t w v) = birkOmega ha (by linarith : 0 ≤ p) Y v) →
        Y = B X := by
  have hsymp := fun ξ η => birkGammaD_symplectic (ha := ha) (hm := hm) (hp := hp) t w ξ η ht hw
  have hAB' : birkGammaD m hm ha hp t w (B X) = X := by
    simpa using DFunLike.congr_fun hAB X
  refine ⟨(hP.restrictScalars ℝ).comp w (birkGamma_hasFDerivAt t w ht hw), fun v => ?_, ?_⟩
  · rw [hX, ← hsymp (B X) v, hAB']
  · intro Y hY
    exact lie_gradient_transport (birkOmega ha (by linarith : 0 ≤ p))
      (fun ζ h => birkOmega_nondegenerate ha (by linarith : 0 ≤ p) h) _ B hAB hsymp dP X Y hX hY

end KAM.Wave

end
