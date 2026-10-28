/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepInj

/-!
# Two-scale KAM step: the map `ĩ₊ = ω₊⁻¹ ∘ ω₀` (`stepP:p3:st-ihat`)

Existence of the holomorphic map `ĩ₊` on `D_{R/16}` with `ω₊ ∘ ĩ₊ = ω₀`, its values in the ball
`B(I, R/16)` and the coordinatewise (block) displacement bounds `10 M̄ᵢ E / R`. The coordinate bounds
come from the mean value inequality for the inverse `G` of `ω₊` on a ball of the image, whose
derivative is the inverse of the Hessian (rows bounded by `2 M̄ᵢ`). Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

/-- Coordinate bound for the displacement of an inverse along a ball in the image. -/
theorem inv_coord {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {F : (Fin n → ℂ) → (Fin n → ℂ)} (hF : DifferentiableOn ℂ F Ω) (hinj : Set.InjOn F Ω)
    {m δ : ℝ} (hm : 0 < m) (hδ : 0 < δ)
    (hder : ∀ x ∈ Ω, ∃ A : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      (A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F x ∧
        ‖(A.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖ ≤ m)
    {x₀ : Fin n → ℂ} (hx : Metric.ball x₀ δ ⊆ Ω)
    {G : (Fin n → ℂ) → (Fin n → ℂ)} (hopen : IsOpen (F '' Ω)) (hG : DifferentiableOn ℂ G (F '' Ω))
    (hGF : ∀ x ∈ Ω, G (F x) = x)
    (hGd : ∀ y ∈ F '' Ω, ∀ v, fderiv ℂ G y (fderiv ℂ F (G y) v) = v)
    (j : Fin n) {c : ℝ} (hc : 0 ≤ c)
    (hrow : ∀ x ∈ Ω, ∃ A : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      (A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F x ∧ ∀ w, ‖A.symm w j‖ ≤ c * ‖w‖)
    {w : Fin n → ℂ} (hw : w ∈ Metric.ball (F x₀) (δ / m)) :
    ‖G w j - x₀ j‖ ≤ c * ‖w - F x₀‖ := by
  obtain ⟨hb1, -⟩ := KAM.Planetary.ball hΩ hF hinj hm hδ hder hx
  have hsub : Metric.ball (F x₀) (δ / m) ⊆ F '' Ω := fun z hz => by
    obtain ⟨x, hxb, rfl⟩ := hb1 hz
    exact ⟨x, hx hxb, rfl⟩
  have hx₀ : x₀ ∈ Ω := hx (mem_ball_self hδ)
  have hGd' : ∀ z ∈ Metric.ball (F x₀) (δ / m), DifferentiableAt ℂ G z := fun z hz =>
    (hG.differentiableAt (hopen.mem_nhds (hsub hz)))
  have hrow' : ∀ z ∈ Metric.ball (F x₀) (δ / m), ∀ v, ‖fderiv ℂ G z v j‖ ≤ c * ‖v‖ := by
    intro z hz v
    obtain ⟨x, hxΩ, rfl⟩ := hsub hz
    obtain ⟨A, hA, hAr⟩ := hrow x hxΩ
    have hGx := hGF x hxΩ
    have h1 := hGd (F x) ⟨x, hxΩ, rfl⟩ (A.symm v)
    rw [hGx, ← hA] at h1
    have h2 : (A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (A.symm v) = v := A.apply_symm_apply v
    rw [h2] at h1
    rw [h1]; exact hAr v
  have := coord_mvt (convex_ball _ _) hc j hGd' hrow' hw (mem_ball_self (by positivity))
  rwa [hGF x₀ hx₀] at this

namespace KamHyp

variable {g : (Fin (a + b) → ℂ) → ℂ}

theorem ihat_exists (H : KamHyp D sbar p h f)
    (hg : DifferentiableOn ℂ g (KAM.actionNbhd D (rhoHat p / 2)))
    (hgb : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 2), ‖g I‖ ≤ 5 / 4 * p.E) :
    ∃ ihat : (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ),
      DifferentiableOn ℂ ihat (KAM.actionNbhd D (rhoHat p / 16)) ∧
      ∀ I ∈ KAM.actionNbhd D (rhoHat p / 16),
        ihat I ∈ Metric.ball I (rhoHat p / 16) ∧
        freq (fun J => h J + g J) (ihat I) = freq h I ∧
        (∀ j, ‖(ihat I - I) j‖ ≤ 10 * p.Mbar * p.E / rhoHat p) ∧
        (∀ i : Fin a, ‖(ihat I - I) (Fin.castAdd b i)‖ ≤ 10 * p.Mbar₁ * p.E / rhoHat p) ∧
        (∀ i : Fin b, ‖(ihat I - I) (Fin.natAdd a i)‖ ≤ 10 * p.Mbar₂ * p.E / rhoHat p) := by
  have hR := H.R_pos
  have hE := H.positive.2.2.2.1
  have hMb := H.positive.2.2.2.2.2.2.1
  have hMb₁ := H.positive.2.2.2.2.2.2.2.1
  have hMb₂ := H.positive.2.2.2.2.2.2.2.2
  obtain ⟨-, -, hb3⟩ := H.beta_facts
  have hRρ := H.R_le_ρ
  set F : (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ) := freq (fun J => h J + g J) with hFdef
  set Ω : Set (Fin (a + b) → ℂ) := KAM.actionNbhd D (rhoHat p / 8) with hΩdef
  have hΩ : IsOpen Ω := isOpen_actionNbhd' D _
  have hU2 := isOpen_actionNbhd' D (rhoHat p / 2)
  have hhU : DifferentiableOn ℂ h (KAM.actionNbhd D (rhoHat p / 2)) :=
    H.holo.mono (actionNbhd_mono (by linarith))
  have hpd : DifferentiableOn ℂ (fun J => h J + g J) (KAM.actionNbhd D (rhoHat p / 2)) :=
    hhU.add hg
  have hΩ2 : Ω ⊆ KAM.actionNbhd D (rhoHat p / 2) := actionNbhd_mono (by linarith)
  have hF : DifferentiableOn ℂ F Ω := fun z hz =>
    (differentiableAt_freq hU2 hpd (hΩ2 hz)).differentiableWithinAt
  have hinj : Set.InjOn F Ω := H.freq_inj hg hgb
  have hess := H.hessian_next hg hgb
  have hder : ∀ x ∈ Ω, ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
      (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) = fderiv ℂ F x ∧
        ‖(A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ))‖ ≤ 2 * p.Mbar := by
    intro x hx
    obtain ⟨-, -, A, hA, hA1, -⟩ := hess x (actionNbhd_mono (by linarith) hx)
    exact ⟨A, hA, hA1⟩
  have hbij : ∀ x ∈ Ω, Function.Bijective (fderiv ℂ F x) := by
    intro x hx
    obtain ⟨A, hA, -⟩ := hder x hx
    rw [← hA]; exact A.bijective
  obtain ⟨hopen, G, hGd, -, hGF, hFG, hGder⟩ := ext_ift hΩ hF hinj hbij
  have hballsub : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 16), Metric.ball I (rhoHat p / 16) ⊆ Ω := by
    intro I hI
    refine (ball_subset_actionNbhd hI).trans (actionNbhd_mono ?_)
    linarith
  have hgsmall : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 16),
      ‖freq g I‖ < rhoHat p / 16 / (2 * p.Mbar) := by
    intro I hI
    have h1 := H.freq_g_le hg hgb (actionNbhd_mono (by linarith) hI)
    refine lt_of_le_of_lt h1 ?_
    rw [div_lt_div_iff₀ hR (by positivity)]
    have h5 : p.Mbar * (80 * p.E) / rhoHat p ^ 2 ≤ 1 / 100 := by
      rw [mul_div_assoc]; exact hb3
    have h6 := (div_le_iff₀ (by positivity)).1 h5
    nlinarith [sq_nonneg (rhoHat p)]
  have hFh : DifferentiableOn ℂ (freq h) (KAM.actionNbhd D p.ρ) := fun z hz =>
    (differentiableAt_freq (isOpen_actionNbhd' D p.ρ) H.holo hz).differentiableWithinAt
  -- membership of `ω₀ I` in the image ball
  have hmem : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 16),
      freq h I ∈ Metric.ball (F I) (rhoHat p / 16 / (2 * p.Mbar)) := by
    intro I hI
    have hI2 : I ∈ KAM.actionNbhd D (rhoHat p / 2) := actionNbhd_mono (by linarith) hI
    have e : freq h I - F I = - freq g I := by
      rw [hFdef, freq_add (hhU.differentiableAt (hU2.mem_nhds hI2))
        (hg.differentiableAt (hU2.mem_nhds hI2))]
      abel
    rw [mem_ball, dist_eq_norm, e, norm_neg]
    exact hgsmall I hI
  have hpre : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 16),
      ∃ x ∈ Metric.ball I (rhoHat p / 16), F x = freq h I := by
    intro I hI
    obtain ⟨hb1, -⟩ := KAM.Planetary.ball hΩ hF hinj (by positivity : 0 < 2 * p.Mbar)
      (by positivity : 0 < rhoHat p / 16) hder (hballsub I hI)
    exact hb1 (hmem I hI)
  have hN : KAM.actionNbhd D (rhoHat p / 16) ⊆ KAM.actionNbhd D p.ρ :=
    actionNbhd_mono (by linarith)
  refine ⟨fun I => G (freq h I), ?_, fun I hI => ?_⟩
  · refine hGd.comp (hFh.mono hN) fun I hI => ?_
    obtain ⟨x, hx, hxe⟩ := hpre I hI
    exact ⟨x, hballsub I hI hx, hxe⟩
  obtain ⟨x, hx, hxe⟩ := hpre I hI
  have hxΩ : x ∈ Ω := hballsub I hI hx
  have hGx : G (freq h I) = x := by rw [← hxe]; exact hGF x hxΩ
  have hfg := H.freq_g_le hg hgb (actionNbhd_mono (by linarith) hI)
  have hw := hmem I hI
  have hdisp : ∀ j (c : ℝ), 0 ≤ c →
      (∀ y ∈ Ω, ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
        (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) = fderiv ℂ F y ∧
          ∀ w, ‖A.symm w j‖ ≤ c * ‖w‖) → ‖(x - I) j‖ ≤ c * (5 * p.E / rhoHat p) := by
    intro j c hc hrow
    have := inv_coord hΩ hF hinj (by positivity : 0 < 2 * p.Mbar)
      (by positivity : 0 < rhoHat p / 16) hder (hballsub I hI) hopen hGd hGF hGder j hc hrow hw
    rw [hGx] at this
    have e : ‖freq h I - F I‖ = ‖freq g I‖ := by
      have hI2 : I ∈ KAM.actionNbhd D (rhoHat p / 2) := actionNbhd_mono (by linarith) hI
      rw [hFdef, freq_add (hhU.differentiableAt (hU2.mem_nhds hI2))
        (hg.differentiableAt (hU2.mem_nhds hI2))]
      rw [show freq h I - (freq h I + freq g I) = - freq g I by abel, norm_neg]
    rw [e] at this
    simpa using this.trans (mul_le_mul_of_nonneg_left hfg hc)
  have hrow_all : ∀ j, ∀ y ∈ Ω, ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
      (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) = fderiv ℂ F y ∧
        ∀ w, ‖A.symm w j‖ ≤ 2 * p.Mbar * ‖w‖ := by
    intro j y hy
    obtain ⟨-, -, A, hA, hA1, -⟩ := hess y (actionNbhd_mono (by linarith) hy)
    refine ⟨A, hA, fun w => (norm_le_pi_norm _ j).trans ?_⟩
    exact ((A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hA1 (norm_nonneg _))
  have hrow_first : ∀ i : Fin a, ∀ y ∈ Ω, ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
      (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) = fderiv ℂ F y ∧
        ∀ w, ‖A.symm w (Fin.castAdd b i)‖ ≤ 2 * p.Mbar₁ * ‖w‖ := by
    intro i y hy
    obtain ⟨-, -, A, hA, -, hA2, -⟩ := hess y (actionNbhd_mono (by linarith) hy)
    exact ⟨A, hA, fun w => (norm_le_pi_norm (firstBlock (b := b) (A.symm w)) i).trans (hA2 w)⟩
  have hrow_last : ∀ i : Fin b, ∀ y ∈ Ω, ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
      (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) = fderiv ℂ F y ∧
        ∀ w, ‖A.symm w (Fin.natAdd a i)‖ ≤ 2 * p.Mbar₂ * ‖w‖ := by
    intro i y hy
    obtain ⟨-, -, A, hA, -, -, hA3⟩ := hess y (actionNbhd_mono (by linarith) hy)
    exact ⟨A, hA, fun w => (norm_le_pi_norm (lastBlock (a := a) (A.symm w)) i).trans (hA3 w)⟩
  beta_reduce
  rw [hGx]
  refine ⟨hx, hxe, ?_, ?_, ?_⟩
  · intro j
    have := hdisp j (2 * p.Mbar) (by positivity) (hrow_all j)
    simpa [mul_div_assoc, mul_assoc, mul_comm, mul_left_comm] using
      this.trans_eq (by ring)
  · intro i
    have := hdisp _ (2 * p.Mbar₁) (by positivity) (hrow_first i)
    exact this.trans_eq (by ring)
  · intro i
    have := hdisp _ (2 * p.Mbar₂) (by positivity) (hrow_last i)
    exact this.trans_eq (by ring)

end KamHyp

end KAM.Planetary

end
