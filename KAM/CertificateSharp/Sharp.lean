/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.ConstantsDom
public import KAM.CertificateSharp.Engine
public import KAM.CertificateSharp.Constants
public import KAM.Sharp.CohData

/-!
# The sharp threshold test

`sharpTest` is the engine test of the sharp isoenergetic theorem: `C₁♯ e < γ⁴ ρ^{4τ}` and
`max {C₂♯, C₃♯} e ≤ disp γ² ρ^{2τ}`, through the rational mirrors `sharpIsoC*Q` at
`c_R := cRRQ n τ` (`cohConstR_le_cRRQ`). `sharpTest_arith` is its arithmetic soundness: a passing
test gives the real inequalities for `sharpIsoC1`, `sharpIsoC2`, `sharpIsoC3` at
`c_R = cohConstR n τ`.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Sharp KAM.Iso.Sharp KAM.Certificate CertArith

section Compare

variable {n τ : ℕ} {cR : ℝ} {cRq Mq σKq σBq σTq γbq μq νq : ℚ} {ρq ρinfq : ℚ}

theorem delta0s_cast (ρq ρinfq : ℚ) : delta0s (ρq : ℝ) (ρinfq : ℝ) = (delta0sQ ρq ρinfq : ℝ) := by
  unfold delta0s delta0sQ
  push_cast
  rfl

theorem delta0s_rpow_neg (hρ : ρinfq < ρq) (m : ℕ) :
    delta0s (ρq : ℝ) (ρinfq : ℝ) ^ (-(m : ℝ)) = ((delta0sQ ρq ρinfq : ℝ) ^ m)⁻¹ := by
  have hd : 0 < delta0s (ρq : ℝ) (ρinfq : ℝ) := by
    rw [delta0s_cast]
    unfold delta0sQ
    push_cast
    refine lt_min one_pos ?_
    have : (ρinfq : ℝ) < ρq := by exact_mod_cast hρ
    positivity
  rw [Real.rpow_neg hd.le, Real.rpow_natCast, delta0s_cast]

theorem delta0sQ_pos (hρ : ρinfq < ρq) : 0 < delta0sQ ρq ρinfq := by
  unfold delta0sQ
  exact lt_min one_pos (by have : 0 < ρq - ρinfq := by linarith
                           positivity)

theorem sharpIsoC1_le (D : Data n cR cRq Mq σKq σBq σTq γbq μq νq)
    (P : Pos n τ cR Mq σKq σBq σTq γbq μq νq)
    (dC : DomC n τ cR cRq Mq σKq σBq σTq γbq μq νq) (hρinf : 0 < ρinfq) (hρ : ρinfq < ρq) :
    sharpIsoC1 n (τ : ℝ) cR (Mq : ℝ) σKq σBq σTq γbq μq νq (τ : ℝ) (ρq : ℝ) (ρinfq : ℝ) ≤
      (sharpIsoC1Q n τ cRq Mq σKq σBq σTq γbq μq νq ρq ρinfq : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, h_iCStar⟩ := dC
  have hρ0 : (0 : ℝ) < ρq := by exact_mod_cast hρinf.trans hρ
  have hγb' : (0 : ℝ) < γbq := by exact_mod_cast D.hγb
  have hneg := delta0s_rpow_neg hρ (2 * (2 * τ))
  have h2 : -(2 * (2 * (τ : ℝ))) = -((2 * (2 * τ) : ℕ) : ℝ) := by push_cast; ring
  have h4 : (4 * (τ : ℝ)) = ((4 * τ : ℕ) : ℝ) := by push_cast; ring
  have hs : 0 ≤ iCStar n (τ : ℝ) cR (Mq : ℝ) σKq σBq σTq γbq μq νq := P.p_iCStar.le
  have hd : (0 : ℝ) < (delta0sQ ρq ρinfq : ℝ) := by exact_mod_cast delta0sQ_pos hρ
  unfold sharpIsoC1 sharpIsoC1Q
  rw [h2, hneg, h4, Real.rpow_natCast]
  push_cast
  gcongr

theorem sharpIsoC2_le (D : Data n cR cRq Mq σKq σBq σTq γbq μq νq)
    (P : Pos n τ cR Mq σKq σBq σTq γbq μq νq)
    (dB : DomB n τ cR cRq Mq σKq σBq σTq γbq μq νq) (hρinf : 0 < ρinfq) (hρ : ρinfq < ρq) :
    sharpIsoC2 n (τ : ℝ) cR (Mq : ℝ) σKq σBq σTq γbq (τ : ℝ) (ρq : ℝ) (ρinfq : ℝ) ≤
      (sharpIsoC2Q n τ cRq Mq σKq σBq σTq γbq ρq ρinfq : ℝ) := by
  obtain ⟨-, -, -, -, -, -, h_iCDK, -⟩ := dB
  have hρ0 : (0 : ℝ) < ρq := by exact_mod_cast hρinf.trans hρ
  have hneg := delta0s_rpow_neg hρ (2 * τ)
  have h2 : -(2 * (τ : ℝ)) = -((2 * τ : ℕ) : ℝ) := by push_cast; ring
  have h4 : (2 * (τ : ℝ)) = ((2 * τ : ℕ) : ℝ) := by push_cast; ring
  have hs : 0 ≤ iCDK n cR (Mq : ℝ) σKq σBq σTq γbq := P.p_iCDK.le
  have hd : (0 : ℝ) < (delta0sQ ρq ρinfq : ℝ) := by exact_mod_cast delta0sQ_pos hρ
  unfold sharpIsoC2 sharpIsoC2Q
  rw [h2, hneg, h4, Real.rpow_natCast]
  push_cast
  gcongr

theorem sharpIsoC3_le (D : Data n cR cRq Mq σKq σBq σTq γbq μq νq)
    (P : Pos n τ cR Mq σKq σBq σTq γbq μq νq)
    (dB : DomB n τ cR cRq Mq σKq σBq σTq γbq μq νq) (hρinf : 0 < ρinfq) (hρ : ρinfq < ρq) :
    sharpIsoC3 n (τ : ℝ) cR (Mq : ℝ) σKq σBq σTq γbq (τ : ℝ) (ρq : ℝ) (ρinfq : ℝ) ≤
      (sharpIsoC3Q n τ cRq Mq σKq σBq σTq γbq ρq ρinfq : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, h_iCDw, -⟩ := dB
  have hρ0 : (0 : ℝ) < ρq := by exact_mod_cast hρinf.trans hρ
  have hneg := delta0s_rpow_neg hρ (2 * τ)
  have h2 : -(2 * (τ : ℝ)) = -((2 * τ : ℕ) : ℝ) := by push_cast; ring
  have h4 : (2 * (τ : ℝ)) = ((2 * τ : ℕ) : ℝ) := by push_cast; ring
  have hs : 0 ≤ iCDw n cR (Mq : ℝ) σKq σBq σTq γbq := P.p_iCDw.le
  have hd : (0 : ℝ) < (delta0sQ ρq ρinfq : ℝ) := by exact_mod_cast delta0sQ_pos hρ
  unfold sharpIsoC3 sharpIsoC3Q
  rw [h2, hneg, h4, Real.rpow_natCast]
  push_cast
  gcongr

end Compare


/-! ### The test and its arithmetic soundness -/

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

omit [LawfulCertArith α] in
/-- `C₁♯ e < γ⁴ ρ^{4τ}` and `max {C₂♯, C₃♯} e ≤ disp γ² ρ^{2τ}`, in exact rational arithmetic
(`c_R := cRRQ n τ`). -/
def sharpTest (c : TorusCertificate n α) : Bool :=
  let p := c.params
  decide (sharpIsoC1Q n p.tau (cRRQ n p.tau) p.M p.σK p.σB p.σT p.γbar p.μ p.nuRay p.rho p.rhoInf *
      p.err < p.γ ^ 4 * p.rho ^ (4 * p.tau)) &&
    decide (max (sharpIsoC2Q n p.tau (cRRQ n p.tau) p.M p.σK p.σB p.σT p.γbar p.rho p.rhoInf)
      (sharpIsoC3Q n p.tau (cRRQ n p.tau) p.M p.σK p.σB p.σT p.γbar p.rho p.rhoInf) * p.err ≤
        p.disp * (p.γ ^ 2 * p.rho ^ (2 * p.tau)))

theorem sharpTest_arith {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : sharpTest c = true) :
    sharpIsoC1 n (c.params.tau : ℝ) (cohConstR n (c.params.tau : ℝ)) c.params.M c.params.σK
      c.params.σB c.params.σT c.params.γbar c.params.μ c.params.nuRay (c.params.tau : ℝ)
      c.params.rho c.params.rhoInf * c.params.err /
        ((c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ))) < 1 ∧
    max (sharpIsoC2 n (c.params.tau : ℝ) (cohConstR n (c.params.tau : ℝ)) c.params.M c.params.σK
        c.params.σB c.params.σT c.params.γbar (c.params.tau : ℝ) c.params.rho c.params.rhoInf)
      (sharpIsoC3 n (c.params.tau : ℝ) (cohConstR n (c.params.tau : ℝ)) c.params.M c.params.σK
        c.params.σB c.params.σT c.params.γbar (c.params.tau : ℝ) c.params.rho c.params.rhoInf) *
      c.params.err /
        ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤
      c.params.disp := by
  have S := checkStatic_sound hs
  simp only [sharpTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hτ1 : (1 : ℝ) ≤ (c.params.tau : ℝ) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast S.hn
    linarith [S.hτ]
  have hD : Data n (cohConstR n (c.params.tau : ℝ)) (cRRQ n c.params.tau) c.params.M c.params.σK
      c.params.σB c.params.σT c.params.γbar c.params.μ c.params.nuRay :=
    { hn := by have := S.hn; omega
      hcR0 := (cohData_russmann (n := n) hτ1).cR_pos
      hcR := cohConstR_le_cRRQ n c.params.tau
      hM := by exact_mod_cast S.hM
      hσK := by exact_mod_cast S.hσK
      hσB := by exact_mod_cast S.hσB
      hσT := by exact_mod_cast S.hσT
      hγb := by exact_mod_cast S.hγbar
      hμ := by exact_mod_cast S.hμ
      hν := by exact_mod_cast S.hν }
  have hρinf : (0 : ℚ) < c.params.rhoInf := by exact_mod_cast S.hρinf
  have hρρ : c.params.rhoInf < c.params.rho := by exact_mod_cast S.hρinfρ
  have P := pos_of c.params.tau hD
  have dA := domA hD P
  have dB := domB hD P dA
  have dC := domC hD P dA dB
  have c1 := sharpIsoC1_le hD P dC hρinf hρρ
  have c2 := sharpIsoC2_le hD P dB hρinf hρρ
  have c3 := sharpIsoC3_le hD P dB hρinf hρρ
  have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
  have h4 : (4 : ℝ) * (c.params.tau : ℝ) = ((4 * c.params.tau : ℕ) : ℝ) := by push_cast; ring
  have h2' : (2 : ℝ) * (c.params.tau : ℝ) = ((2 * c.params.tau : ℕ) : ℝ) := by push_cast; ring
  rw [h4, h2', Real.rpow_natCast, Real.rpow_natCast]
  have hd4 : (0 : ℝ) < (c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * c.params.tau) := by
    positivity [S.hγ]
  have hd2 : (0 : ℝ) < (c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * c.params.tau) := by
    positivity [S.hγ]
  have h1' : ((sharpIsoC1Q n c.params.tau (cRRQ n c.params.tau) c.params.M c.params.σK
      c.params.σB c.params.σT c.params.γbar c.params.μ c.params.nuRay c.params.rho
      c.params.rhoInf : ℚ) : ℝ) * c.params.err <
      (c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * c.params.tau) := by exact_mod_cast h1
  have h2'' : ((max (sharpIsoC2Q n c.params.tau (cRRQ n c.params.tau) c.params.M c.params.σK
      c.params.σB c.params.σT c.params.γbar c.params.rho c.params.rhoInf)
      (sharpIsoC3Q n c.params.tau (cRRQ n c.params.tau) c.params.M c.params.σK
      c.params.σB c.params.σT c.params.γbar c.params.rho c.params.rhoInf) : ℚ) : ℝ) *
      c.params.err ≤
      (c.params.disp : ℝ) * ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * c.params.tau)) := by
    exact_mod_cast h2
  constructor
  · rw [div_lt_one hd4]
    exact (mul_le_mul_of_nonneg_right c1 S.he0).trans_lt h1'
  · rw [div_le_iff₀ hd2]
    refine (mul_le_mul_of_nonneg_right ?_ S.he0).trans h2''
    push_cast
    exact max_le_max c2 c3

end KAM.CertificateSharp
