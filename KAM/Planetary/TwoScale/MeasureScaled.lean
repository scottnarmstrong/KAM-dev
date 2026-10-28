/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.Cover
public import KAM.Planetary.TwoScale.LimitMapScale
public import KAM.Measure.Lipschitz

/-!
# Two-scale KAM: rescaled cover and rescaled Lipschitz image (`stepP:p3:mt-ext`, `stepP:p3:mt-meas`)

In the rescaled coordinates `(θ, I) ↦ (2π θ / s, I / R)` the norm `limitmap_data R s` is the max
norm. `scaled_cover` transports `cover` through `sc`/`unsc`; `lip_image_scaled` transports the
Lipschitz image bound through the linear rescaling `e`, whose Jacobian determinant is a nonzero
constant that cancels on both sides.
-/

@[expose] public noncomputable section

open Set MeasureTheory Real

namespace KAM.Planetary

variable {n : ℕ}

/-- `stepP:p3:mt-ext`: the bi-Lipschitz extension of a rescaled-Lipschitz perturbation of the
identity from `X ⊆ ℝⁿ × ℝⁿ`; points of `X` have an inverse image within `η / (1 - λ)`. -/
theorem scaled_cover {R s lam eta : ℝ} (hR : 0 < R) (hs : 0 < s) (hlam : 0 ≤ lam ∧ lam < 1)
    (heta : 0 ≤ eta) {X : Set (Phase n)} {Φ : Phase n → Phase n}
    (hlip : ∀ x ∈ X, ∀ y ∈ X,
      limitmap_data R s ((Φ x - x) - (Φ y - y)) ≤ lam * limitmap_data R s (x - y))
    (hsup : ∀ x ∈ X, limitmap_data R s (Φ x - x) ≤ eta) :
    ∃ Ψ : Phase n → Phase n, (∀ x ∈ X, Ψ x = Φ x) ∧
      (∀ x y, limitmap_data R s (Ψ x - Ψ y) ≤ (1 + lam) * limitmap_data R s (x - y)) ∧
      ∀ y ∈ X, ∃ x, Ψ x = y ∧ limitmap_data R s (x - y) ≤ eta / (1 - lam) := by
  have hRne := hR.ne'
  have hsne := hs.ne'
  have hsu := fun z : Fin (n + n) → ℝ => sc_unsc (𝕜 := ℝ) hRne hsne z
  have hus := fun w : Phase n => unsc_sc (𝕜 := ℝ) hRne hsne w
  have hnorm := fun w : Phase n => limitmap_data_eq_norm_sc hR hs w
  obtain ⟨F, hFX, hFbi, hFloc⟩ := cover (N := n + n)
    (X := {z | unsc R s z ∈ X})
    (g := fun z => sc R s (Φ (unsc R s z) - unsc R s z)) (lam := lam) (η := eta) hlam heta
    (fun z hz w hw => by
      have h := hlip _ hz _ hw
      rw [hnorm, hnorm, ← sc_sub, ← sc_sub] at h
      rw [← sc_sub]
      have e : sc R s (unsc R s z - unsc R s w) = z - w := by rw [sc_sub, hsu, hsu]
      rw [e] at h
      exact h)
    (fun z hz => by rw [← hnorm]; exact hsup _ hz)
  refine ⟨fun x => unsc R s (F (sc R s x)), fun x hx => ?_, fun x y => ?_, fun y hy => ?_⟩
  · have hz : sc R s x ∈ {z | unsc R s z ∈ X} := by simpa [hus] using hx
    have e : sc R s x + sc R s (Φ x - x) = sc R s (Φ x) := by rw [sc_sub]; abel
    simp only [hFX _ hz, hus, e]
  · simp only [hnorm (_ - _), ← unsc_sub, hsu]
    rw [hnorm (x - y), sc_sub]
    exact (hFbi _ _).2
  · have hz : sc R s y ∈ {z | unsc R s z ∈ X} := by simpa [hus] using hy
    refine ⟨unsc R s (F.symm (sc R s y)), ?_, ?_⟩
    · simp only [hsu, Equiv.apply_symm_apply, hus]
    · rw [hnorm, sc_sub, hsu]
      exact hFloc _ hz

/-- The rescaling `(θ, I) ↦ (2π θ / s, I / R)` as a linear equivalence of `ℝⁿ × ℝⁿ`. -/
def scaleEquiv (R s : ℝ) (hR : 0 < R) (hs : 0 < s) : Phase n ≃ₗ[ℝ] Phase n :=
  LinearEquiv.prodCongr (LinearEquiv.smulOfNeZero ℝ (Fin n → ℝ) (2 * π / s) (by positivity))
    (LinearEquiv.smulOfNeZero ℝ (Fin n → ℝ) (1 / R) (by positivity))

theorem norm_scaleEquiv {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (w : Phase n) :
    ‖scaleEquiv R s hR hs w‖ = limitmap_data R s w := by
  have h1 : 0 ≤ 2 * π / s := by positivity
  have h2 : 0 ≤ 1 / R := by positivity
  simp only [scaleEquiv, Prod.norm_def, limitmap_data]
  change max ‖(2 * π / s) • w.1‖ ‖(1 / R) • w.2‖ = _
  rw [norm_smul, norm_smul, Real.norm_of_nonneg h1, Real.norm_of_nonneg h2, mul_comm,
    one_div, ← div_eq_inv_mul, mul_comm (2 * π / s)]

/-- `stepP:p3:mt-meas`: Lipschitz image bound for the rescaled norm on `ℝⁿ × ℝⁿ`; the Jacobian of
the rescaling cancels. -/
theorem lip_image_scaled {R s Λ : ℝ} (hR : 0 < R) (hs : 0 < s) {S : Set (Phase n)}
    {F : Phase n → Phase n}
    (hF : ∀ x ∈ S, ∀ y ∈ S,
      limitmap_data R s (F x - F y) ≤ Λ * limitmap_data R s (x - y)) :
    volume (F '' S) ≤ ENNReal.ofReal (Λ ^ (2 * n)) * volume S := by
  set e := scaleEquiv (n := n) R s hR hs with he
  have hlip : ∀ u ∈ e '' S, ∀ v ∈ e '' S,
      ‖(e ∘ F ∘ e.symm) u - (e ∘ F ∘ e.symm) v‖ ≤ Λ * ‖u - v‖ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp, LinearEquiv.symm_apply_apply]
    rw [← map_sub, ← map_sub, he, norm_scaleEquiv, norm_scaleEquiv]
    exact hF x hx y hy
  have h1 := KAM.lip_image_prod hlip
  have himg : (e ∘ F ∘ e.symm) '' (e '' S) = e '' (F '' S) := by
    simp only [Set.image_image, Function.comp, LinearEquiv.symm_apply_apply]
  rw [himg] at h1
  have hdet : (LinearMap.det (e : Phase n →ₗ[ℝ] Phase n)) ≠ 0 :=
    (LinearEquiv.isUnit_det' e).ne_zero
  have hc : ENNReal.ofReal |LinearMap.det (e : Phase n →ₗ[ℝ] Phase n)| ≠ 0 := by
    simpa using hdet
  rw [Measure.addHaar_image_linearMap, Measure.addHaar_image_linearMap, ← mul_assoc,
    mul_comm _ (ENNReal.ofReal (Λ ^ (2 * n))), mul_assoc] at h1
  exact (ENNReal.mul_le_mul_iff_right hc ENNReal.ofReal_ne_top).1 (by simpa [mul_comm] using h1)

end KAM.Planetary

end
