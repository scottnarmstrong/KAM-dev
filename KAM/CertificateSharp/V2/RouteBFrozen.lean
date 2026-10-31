/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBRefined

/-!
# Route B at the frozen data

`frozenBCore_sound` concludes `CertifiedTorus` through the literal frozen-form theorem
`KAM.Iso.Sharp2.RouteB.iso_g1_v2B_frozen`: no refined hypothesis, `M₁ = M₂ = M_h2 = M`,
`c_Th = c_DTh = 2M`, the default initial values `defaultInitB`, classical small-divisor constants
at every site (certificates on the Diophantine set at every scale). Its constants are
`min {C₁♯, c1B}`, `max {C₂♯, c2B}`, `max {C₃♯, c3B}`; `finalBF` bounds `C₂♯`, `C₃♯` by their
rational majorants (`sharp_disp_le`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB
  KAM.Iso.Sharp2.RouteB KAM.Iso.Sharp

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

theorem max_mul_div_le_of {x y e g D : ℝ} (hx : x * e / g ≤ D) (hy : y * e / g ≤ D) :
    max x y * e / g ≤ D := by
  rcases max_choice x y with h | h <;> rw [h] <;> assumption

/-- **`finalBF` gives `Admissible` at the constants of `iso_g1_v2B_frozen`, and the room of the
ray.** -/
theorem finalBF_sound {c : TorusCertificate n α} {Q : NumBQ} {iLt iN iNt Xs : ℚ}
    (hs : checkStatic c = true) (hτ : Q.τ = c.params.tau) (hρ : Q.ρ = c.params.rho)
    (hXs : 0 < Xs) (h : finalBF Q n c.params c.freqBox iLt iNt Xs = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) :
    Admissible c.params
      (min (sharpIsoC1 n (c.params.tau : ℝ) (cohConstR n (c.params.tau : ℝ)) c.params.M c.params.σK
        c.params.σB c.params.σT c.params.γbar c.params.μ c.params.nuRay (c.params.tau : ℝ)
        c.params.rho c.params.rhoInf) (c1B (Q.toNum n) ⟨iLt, iN, iNt⟩ Xs))
      (max (sharpIsoC2 n (c.params.tau : ℝ) (cohConstR n (c.params.tau : ℝ)) c.params.M c.params.σK
        c.params.σB c.params.σT c.params.γbar (c.params.tau : ℝ) c.params.rho c.params.rhoInf)
        (c2B (Q.toNum n) ⟨iLt, iN, iNt⟩ Xs))
      (max (sharpIsoC3 n (c.params.tau : ℝ) (cohConstR n (c.params.tau : ℝ)) c.params.M c.params.σK
        c.params.σB c.params.σT c.params.γbar (c.params.tau : ℝ) c.params.rho c.params.rhoInf)
        (c3B (Q.toNum n) ⟨iLt, iN, iNt⟩ Xs)) ∧
      (c.params.disp : ℝ) < ((c.params.σω : ℝ) - c.params.s) * ‖ωstar‖ := by
  have S := checkStatic_sound hs
  simp only [finalBF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hB, hsh⟩ := h
  obtain ⟨hsm, hd2, hd3, hroom⟩ := finalB_sound (iN := iN) hs hτ hρ hXs hB hω
  have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
  have hτQ : (Q.toNum n).τ = (c.params.tau : ℝ) := by rw [NumBQ.cast_τ, hτ]
  have hρQ : (Q.toNum n).ρ = (c.params.rho : ℝ) := by
    show ((Q.ρ : ℚ) : ℝ) = _; rw [hρ]
  rw [hτQ, hρQ] at hsm hd2 hd3
  have e2 : (2 * (c.params.tau : ℝ)) = ((2 * c.params.tau : ℕ) : ℝ) := by push_cast; ring
  have hg : (0 : ℝ) < (c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ)) := by
    have := Real.rpow_pos_of_pos hρ0 (2 * (c.params.tau : ℝ))
    have := S.hγ
    positivity
  have h4 : (0 : ℝ) < (c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ)) := by
    have := Real.rpow_pos_of_pos hρ0 (4 * (c.params.tau : ℝ))
    have := S.hγ
    positivity
  have hS := sharp_disp_le hs
  have hsh' : ((max (sharpIsoC2Q n c.params.tau (cRRQ n c.params.tau) c.params.M c.params.σK
      c.params.σB c.params.σT c.params.γbar c.params.rho c.params.rhoInf)
      (sharpIsoC3Q n c.params.tau (cRRQ n c.params.tau) c.params.M c.params.σK c.params.σB
        c.params.σT c.params.γbar c.params.rho c.params.rhoInf) : ℚ) : ℝ) * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp := by
    rw [div_le_iff₀ hg, e2, Real.rpow_natCast]
    have := (Rat.cast_le (K := ℝ)).mpr hsh
    push_cast at this ⊢
    exact this
  have hsharp : ∀ {C : ℝ}, C ≤ _ → C * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp :=
    fun {C} hC => (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC S.he0) hg.le).trans
      hsh'
  refine ⟨⟨?_, ?_⟩, hroom⟩
  · exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) S.he0)
      h4.le).trans_lt hsm
  · exact max_mul_div_le_of
      (max_mul_div_le_of (hsharp ((le_max_left _ _).trans hS)) hd2)
      (max_mul_div_le_of (hsharp ((le_max_right _ _).trans hS)) hd3)

/-- The default initial values at rational data. -/
theorem cast_defaultInitB (p : CertParams) :
    defaultInitB n (p.σK : ℝ) p.σB p.μ =
      ⟨((defaultIB n p).1 : ℝ), ((defaultIB n p).2.1 : ℝ), ((defaultIB n p).2.2 : ℝ)⟩ := by
  simp only [defaultInitB, defaultIB]
  push_cast
  rfl

/-- **Soundness of route B at the frozen data**, through `iso_g1_v2B_frozen`. -/
theorem frozenBCore_sound (c : TorusCertificate n α) (w : RunBWit) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (h : frozenBCore n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, -, -⟩ := checkStatic_freq B.hs hω
  simp only [frozenBCore, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hX, hσK⟩, hσB⟩, hsB⟩, hwf⟩, hfit⟩, hini⟩, hok⟩, hsites⟩, htail⟩, hfin⟩ := h
  set Q := w.num c.params c.freqBox c.params.M c.params.M c.params.M with hQ
  have hN : (Q.toNum n).Wf := NumBQ.wfOk_sound hwf
  have hX' : (0 : ℝ) < w.Xs := by exact_mod_cast hX
  obtain ⟨hA, hroom⟩ := finalBF_sound (Q := Q) (iN := (defaultIB n c.params).2.1) B.hs rfl rfl hX
    hfin hω
  have hσ0 : (0 : ℝ) ≤ c.params.σω := by linarith [S.hσω]
  obtain ⟨hσ, hΘ⟩ := rayBound (σ := c.params.σω) (Θ := c.params.σω * boxNormUp c.freqBox)
    hσ0 (by push_cast; exact le_rfl) hω hω0
  have hOk := NumBQ.okB_sound hN hok
  rw [← NumBQ.cast_capB, ← NumBQ.cast_initB] at hOk
  have hμ2 : (((c.params.μ / 2 : ℚ)) : ℝ) = (c.params.μ : ℝ) / 2 := by push_cast; ring
  rw [hμ2] at hOk
  have hDI := cast_defaultInitB (n := n) c.params
  have hI := NumBQ.initOk_sound (n := n) hini
  have hF := NumBQ.fitsOk_sound (n := n) (iN := (defaultIB n c.params).2.1) hfit
  rw [← hDI] at hOk hI hF
  rw [← hDI] at hA
  obtain ⟨-, -, -, hbody⟩ := iso_g1_v2B_frozen (N := Q.toNum n) (M := c.params.M)
    (σK := c.params.σK) (σB := c.params.σB) (σT := c.params.σT) (μ := c.params.μ)
    (γbar := c.params.γbar) (σω := ((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖)
    (ν := c.params.nuRay) (Xs := w.Xs) hN rfl S.hτ S.hM (by exact_mod_cast hσK)
    (by exact_mod_cast hσB) S.hσT S.hμ (S.hσω.trans_le hσ) S.hν ωstar hω0 rfl
    (by show ((c.params.σK - c.params.μ / 2 : ℚ) : ℝ) = _; push_cast; ring)
    (by show (c.params.σB : ℝ) - c.params.μ < (w.sB : ℝ); exact_mod_cast hsB) hΘ
    (by show ((c.params.M * w.sN : ℚ) : ℝ) = _; push_cast; rfl) rfl rfl rfl
    (by show (2 : ℝ) * c.params.M ≤ ((2 * c.params.M : ℚ) : ℝ); push_cast; exact le_rfl)
    (by show (2 : ℝ) * c.params.M ≤ ((2 * c.params.M : ℚ) : ℝ); push_cast; exact le_rfl)
    hI hF hOk hX' (fun _ hγ _ => NumBQ.cert_classical hN hsites htail hγ)
  exact certifiedTorus_of_ray hω hdio B hσ hA (fun _ _ ht => ray_lt_of_disp hroom ht) hbody

/-- **The engine of route B at the frozen data.** -/
def routeBFrozen : EngineV2 where
  Wit := RunBWit
  test := fun {n} _ _ c w => frozenBCore n c.params c.freqBox w
  sound := fun c w _ hω hdio B h => frozenBCore_sound c w hω hdio B h

end KAM.CertificateSharp.V2

end
