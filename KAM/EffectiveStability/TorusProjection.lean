/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Cauchy
public import KAM.EffectiveStability.TorusRealSlice

/-!
# The projection bound `‖Du‖ ≤ κc + disp/δ` (track B, package B5-LAG, item 4)

* `norm_fderiv_real_le_of_strip_bound`: Cauchy estimate on the strip for a vector-valued
  holomorphic map bounded by `d` on `T_ρ`: `‖DF(ι φ)‖ ≤ d/δ` for `0 < δ < ρ`.
* `torusRealU_fderiv_le`: if the angle component `K_c^θ - id` of a holomorphic reference
  embedding has `‖D(K_c^θ - id)(ι φ)‖ ≤ κc` and `‖K - K_c‖ ≤ disp` on `T_ρ`, then the real
  displacement `u` of the real-on-reals `K` has `‖Du φ‖ ≤ κc + disp/δ`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open KAM KAM.Torus

variable {n : ℕ} {ρ δ : ℝ}

/-- Cauchy estimate for a vector-valued map on the strip at a real point. -/
theorem norm_fderiv_real_le_of_strip_bound {F : (Fin n → ℂ) → (Fin n → ℂ)} {d : ℝ}
    (hρ : 0 < ρ) (hF : DifferentiableOn ℂ F (complexStrip n ρ)) (hδ : 0 < δ) (hδρ : δ < ρ)
    (hd : ∀ θ ∈ complexStrip n ρ, ‖F θ‖ ≤ d) (x : Fin n → ℝ) :
    ‖fderiv ℂ F (realInclusion n x)‖ ≤ d / δ := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd _ (realInclusion_mem_complexStrip hρ x))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
  rcases eq_or_ne e 0 with rfl | he
  · simp
  have hte : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hz := realInclusion_mem_complexStrip hρ x
  have hFd : DifferentiableAt ℂ F (realInclusion n x) :=
    hF.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hz)
  have hmem : ∀ ζ : ℂ, ‖ζ‖ ≤ δ / ‖e‖ → realInclusion n x + ζ • e ∈ complexStrip n ρ := by
    intro ζ hζ i
    have h1 : ‖ζ‖ * ‖e‖ ≤ δ := by
      calc ‖ζ‖ * ‖e‖ ≤ δ / ‖e‖ * ‖e‖ := by gcongr
        _ = δ := by field_simp
    have h2 : ‖ζ * e i‖ ≤ ‖ζ‖ * ‖e‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm e i) (norm_nonneg _)
    have h3 : |((realInclusion n x + ζ • e) i).im| ≤ ‖ζ * e i‖ := by
      have : ((realInclusion n x + ζ • e) i).im = (ζ * e i).im := by simp
      rw [this]
      exact Complex.abs_im_le_norm _
    exact lt_of_le_of_lt (h3.trans (h2.trans h1)) hδρ
  have hcoord : ∀ i, ‖fderiv ℂ F (realInclusion n x) e i‖ ≤ d * ‖e‖ / δ := by
    intro i
    have hfi : DifferentiableOn ℂ (fun θ => F θ i) (complexStrip n ρ) :=
      (differentiableOn_pi.mp hF) i
    have hder : fderiv ℂ (fun θ => F θ i) (realInclusion n x) e =
        fderiv ℂ F (realInclusion n x) e i := by
      rw [(hasFDerivAt_pi'.mp hFd.hasFDerivAt i).fderiv]
      rfl
    have := norm_fderiv_le_of_closedDisc (isOpen_complexStrip n ρ) hfi (z := realInclusion n x)
      e (δ := δ / ‖e‖) (M := d) (by positivity) hmem
      (fun ζ hζ => (norm_le_pi_norm _ i).trans (hd _ (hmem ζ hζ)))
    rw [hder] at this
    calc _ ≤ d / (δ / ‖e‖) := this
      _ = d * ‖e‖ / δ := by field_simp
  have : ‖fderiv ℂ F (realInclusion n x) e‖ ≤ d * ‖e‖ / δ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 hcoord
  calc _ ≤ d * ‖e‖ / δ := this
    _ = d / δ * ‖e‖ := by ring

variable {K Kc : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- **Projection bound** (item 4). `K` holomorphic and real on reals, `Kc` holomorphic on `T_ρ`,
`‖D(Kc^θ - id)(ι φ)‖ ≤ κc` at real points and `‖K - Kc‖ ≤ disp` on `T_ρ`; then for `0 < δ < ρ`
the real displacement `u = x - id` of `K` satisfies `‖Du φ‖ ≤ κc + disp/δ`. -/
theorem torusRealU_fderiv_le (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hKc : DifferentiableOn ℂ Kc (complexStrip n ρ)) (hreal : IsRealOnReals K)
    (hδ : 0 < δ) (hδρ : δ < ρ) {κc disp : ℝ}
    (hκ : ∀ φ : Fin n → ℝ, ‖fderiv ℂ (fun θ => (Kc θ).1 - θ) (realInclusion n φ)‖ ≤ κc)
    (hdisp : ∀ θ ∈ complexStrip n ρ, ‖K θ - Kc θ‖ ≤ disp) (φ : Fin n → ℝ) :
    ‖fderiv ℝ (torusRealU K) φ‖ ≤ κc + disp / δ := by
  set z := realInclusion n φ with hzdef
  have hz : z ∈ complexStrip n ρ := realInclusion_mem_complexStrip hρ φ
  have hnb := (isOpen_complexStrip n ρ).mem_nhds hz
  have hKd : DifferentiableAt ℂ K z := hK.differentiableAt hnb
  have hKcd : DifferentiableAt ℂ Kc z := hKc.differentiableAt hnb
  have hK1 : DifferentiableAt ℂ (fun θ => (K θ).1) z := hKd.fst
  have hKc1 : DifferentiableAt ℂ (fun θ => (Kc θ).1) z := hKcd.fst
  set G : (Fin n → ℂ) → (Fin n → ℂ) := fun θ => (Kc θ).1 - θ with hG
  set F : (Fin n → ℂ) → (Fin n → ℂ) := fun θ => (K θ).1 - θ with hF
  have hFd : DifferentiableAt ℂ F z := hK1.sub differentiableAt_id
  have hGd : DifferentiableAt ℂ G z := hKc1.sub differentiableAt_id
  have hdiffF : DifferentiableOn ℂ (fun θ => F θ - G θ) (complexStrip n ρ) := by
    intro θ hθ
    have h1 : DifferentiableAt ℂ K θ := hK.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ)
    have h2 : DifferentiableAt ℂ Kc θ :=
      hKc.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ)
    exact ((h1.fst.sub differentiableAt_id).sub
      (h2.fst.sub differentiableAt_id)).differentiableWithinAt
  have hcau := norm_fderiv_real_le_of_strip_bound hρ hdiffF hδ hδρ (d := disp) (fun θ hθ => by
    have : F θ - G θ = (K θ - Kc θ).1 := by simp [hF, hG]
    rw [this]
    exact (norm_fst_le _).trans (hdisp θ hθ)) φ
  have hdisp0 : 0 ≤ disp := (norm_nonneg _).trans (hdisp _ hz)
  have hκ0 : 0 ≤ κc := (norm_nonneg _).trans (hκ 0)
  have hsplit : fderiv ℂ F z = fderiv ℂ G z + fderiv ℂ (fun θ => F θ - G θ) z := by
    rw [fderiv_fun_sub hFd hGd]
    abel
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    fun e => ?_
  have hu : realInclusion n (fderiv ℝ (torusRealU K) φ e) = fderiv ℂ F z (realInclusion n e) := by
    have hX := fderiv_torusRealX_incl hρ hK hreal φ e
    have hU : fderiv ℝ (torusRealU K) φ e = fderiv ℝ (torusRealX K) φ e - e := by
      have : DifferentiableAt ℝ (torusRealX K) φ :=
        (realRestriction_fderiv hρ hK hreal φ).1.fst
      have h2 := fderiv_fun_sub (f := torusRealX K) (g := fun y => y) this
        (differentiableAt_id (𝕜 := ℝ) (x := φ))
      show fderiv ℝ (fun y => torusRealX K y - y) φ e = _
      rw [h2]
      simp
    have hF' : fderiv ℂ F z (realInclusion n e) =
        (fderiv ℂ K z (realInclusion n e)).1 - realInclusion n e := by
      have h3 := fderiv_fun_sub (f := fun θ => (K θ).1) (g := fun θ => θ) hK1
        differentiableAt_id
      have h4 : fderiv ℂ (fun θ => (K θ).1) z (realInclusion n e) =
          (fderiv ℂ K z (realInclusion n e)).1 := by
        have := (hKd.hasFDerivAt.fst).fderiv
        rw [this]
        rfl
      simp only [hF]
      rw [h3]
      simp [h4]
    rw [hF', hU, map_sub, hX]
  calc ‖fderiv ℝ (torusRealU K) φ e‖ = ‖realInclusion n (fderiv ℝ (torusRealU K) φ e)‖ :=
        (norm_realInclusion _).symm
    _ = ‖fderiv ℂ F z (realInclusion n e)‖ := by rw [hu]
    _ = ‖fderiv ℂ G z (realInclusion n e) +
          fderiv ℂ (fun θ => F θ - G θ) z (realInclusion n e)‖ := by
        rw [hsplit]; rfl
    _ ≤ ‖fderiv ℂ G z‖ * ‖realInclusion n e‖ + disp / δ * ‖realInclusion n e‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact (fderiv ℂ G z).le_opNorm _
        · exact (fderiv ℂ (fun θ => F θ - G θ) z).le_opNorm _ |>.trans
            (mul_le_mul_of_nonneg_right hcau (norm_nonneg _))
    _ ≤ (κc + disp / δ) * ‖e‖ := by
        rw [norm_realInclusion, ← add_mul]
        exact mul_le_mul_of_nonneg_right (add_le_add (hκ φ) le_rfl) (norm_nonneg _)

end KAM.EffectiveStability

end
