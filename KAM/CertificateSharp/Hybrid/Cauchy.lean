/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.Ops
public import KAM.Strip.Bridges
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The derivative of a model with a remainder (package C8c)

A model `m = ⟨d, P, rad⟩` enclosing a holomorphic `f` in sup on `T_ρ` gives a model of `∂_j f` on
`T_{ρ-δ}`: the exact derivative of the polynomial part (`CertModel.ofDeriv`, at degree `d + 1`) and,
for the remainder `R = f - (2π)^d P`, the Cauchy estimate `|∂_j R| ≤ δ⁻¹ sup_{T_ρ} |R|`
(`KAM.cauchy_strip`), that is the extra radius `rad/(2πδ) ≤ rad/(2 · 3.14 δ)` in units of
`(2π)^{d+1}`.

* `CertModel.derivC`, `CertModel.Encloses.derivC`.
-/

@[expose] public section

namespace KAM.CertificateSharp.Hybrid

open KAM KAM.Certificate CertArith

variable {α : Type} [CertArith α]

/-- The Cauchy factor `1/(2πδ) ≤ 1/(2 · piLoQ · δ)`. -/
def cauchyFactor (δ : ℚ) : ℚ := 1 / (2 * piLoQ * δ)

/-- The model of `∂_j f` on `T_{ρ-δ}` from a model of `f` on `T_ρ`; the weight `W'` is that of
`T_{ρ-δ}`. -/
def CertModel.derivC (W' : CertWeight) (j : ℕ) (δ : ℚ) (m : CertModel α) : CertModel α :=
  let D := CertModel.ofDeriv W' j m.deg m.poly
  ⟨D.deg, D.poly, upAdd D.rad (upMul m.rad (ofRatUp (cauchyFactor δ)))⟩

variable [LawfulCertArith α] {n : ℕ}

/-- **The derivative of a model.** -/
theorem CertModel.Encloses.derivC {W' : CertWeight} {s N : ℕ} (hW' : checkWeight W' s N = true)
    {ρ : ℚ} (hρ : W'.rho < ρ) {m : CertModel α} {f : (Fin n → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (complexStrip n ρ)) (hm : m.Encloses n ρ f) (j : Fin n) :
    (CertModel.derivC W' j.val (ρ - W'.rho) m).Encloses n W'.rho
      (fun θ => fderiv ℂ f θ (Pi.single j 1)) := by
  intro θ hθ
  have hρ' := CertWeight.rho_pos hW'
  have hρ0 : (0 : ℝ) < ρ := by
    have : (W'.rho : ℝ) < ρ := by exact_mod_cast hρ
    linarith
  have hδ : (0 : ℝ) < ((ρ - W'.rho : ℚ) : ℝ) := by
    have : (0 : ℚ) < ρ - W'.rho := by linarith
    exact_mod_cast this
  have hrad := CertModel.Encloses.rad_nonneg hρ0 hm
  set c : ℂ := (2 * (Real.pi : ℂ)) ^ m.deg with hc
  set R : (Fin n → ℂ) → ℂ := fun θ => f θ - c * m.poly.eval n θ with hR
  have hRd : DifferentiableOn ℂ R (complexStrip n ρ) :=
    hf.sub ((m.poly.differentiable_eval n).const_mul _).differentiableOn
  have hRb : ∀ θ ∈ complexStrip n ρ, ‖R θ‖ ≤ (2 * Real.pi) ^ m.deg * val m.rad := hm
  have hcs := (cauchy_strip hRd hRb hδ).1 j θ (by
    have e : (ρ : ℝ) - ((ρ - W'.rho : ℚ) : ℝ) = W'.rho := by push_cast; ring
    rw [e]; exact hθ)
  -- the polynomial part
  have hD := CertModel.Encloses.ofDeriv hW' j m.deg m.poly θ hθ
  -- `∂_j R = ∂_j f - c ∂_j P` at `θ`
  have hθρ : θ ∈ complexStrip n ρ := fun i => (hθ i).trans (by exact_mod_cast hρ)
  have hfd : DifferentiableAt ℂ f θ := hf.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθρ)
  have hPd : DifferentiableAt ℂ (fun θ => c * m.poly.eval n θ) θ :=
    ((m.poly.differentiable_eval n).const_mul _) θ
  have hRe : fderiv ℂ R θ (Pi.single j 1) =
      fderiv ℂ f θ (Pi.single j 1) - c * fderiv ℂ (m.poly.eval n) θ (Pi.single j 1) := by
    have h1 : fderiv ℂ R θ = fderiv ℂ f θ - fderiv ℂ (fun θ => c * m.poly.eval n θ) θ :=
      fderiv_sub hfd hPd
    have h2 : fderiv ℂ (fun θ => c * m.poly.eval n θ) θ = c • fderiv ℂ (m.poly.eval n) θ :=
      fderiv_const_mul ((m.poly.differentiable_eval n) θ) c
    rw [h1, h2]
    simp
  -- assemble
  have hcf := LawfulCertArith.ofRatUp_ge (α := α) (cauchyFactor (ρ - W'.rho))
  have hpi : (piLoQ : ℝ) < Real.pi := piLoQ_lt_pi
  have hpilo : (0 : ℝ) < piLoQ := by norm_num [piLoQ]
  have hcf0 : (0 : ℝ) ≤ cauchyFactor (ρ - W'.rho) := by
    simp only [cauchyFactor]
    have : (0 : ℚ) < ρ - W'.rho := by linarith
    have : (0 : ℚ) < piLoQ := by exact_mod_cast hpilo
    positivity
  have hmul := LawfulCertArith.upMul_ge m.rad (ofRatUp (cauchyFactor (ρ - W'.rho))) hrad
    (hcf0.trans hcf)
  have hDrad : 0 ≤ val (CertModel.ofDeriv W' j.val m.deg m.poly).rad :=
    CertModel.Encloses.rad_nonneg hρ' (CertModel.Encloses.ofDeriv hW' j m.deg m.poly)
  have hadd := LawfulCertArith.upAdd_ge (CertModel.ofDeriv W' j.val m.deg m.poly).rad
    (upMul m.rad (ofRatUp (cauchyFactor (ρ - W'.rho))))
  have hdeg : (CertModel.ofDeriv W' j.val m.deg m.poly).deg = m.deg + 1 := rfl
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ m.deg := by positivity
  have hzpow : (2 * Real.pi) ^ (m.deg + 1) = (2 * Real.pi) ^ m.deg * (2 * Real.pi) :=
    zpow_add_one₀ (by positivity) _
  -- the Cauchy term in units of `(2π)^{d+1}`
  have hcau : ((ρ - W'.rho : ℚ) : ℝ)⁻¹ * ((2 * Real.pi) ^ m.deg * val m.rad) ≤
      (2 * Real.pi) ^ (m.deg + 1) *
        val (upMul m.rad (ofRatUp (cauchyFactor (ρ - W'.rho))) : α) := by
    rw [hzpow]
    have e1 : ((ρ - W'.rho : ℚ) : ℝ)⁻¹ * ((2 * Real.pi) ^ m.deg * val m.rad) =
        (2 * Real.pi) ^ m.deg * (2 * Real.pi) * (val m.rad * (1 / (2 * Real.pi *
          ((ρ - W'.rho : ℚ) : ℝ)))) := by
      field_simp
    rw [e1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans ?_ hmul
    refine mul_le_mul_of_nonneg_left ?_ hrad
    refine le_trans ?_ hcf
    have hδ' : (0 : ℝ) < (ρ : ℝ) - (W'.rho : ℝ) := by
      have := hδ; push_cast at this; linarith
    simp only [cauchyFactor]
    push_cast
    exact one_div_le_one_div_of_le (mul_pos (mul_pos two_pos hpilo) hδ')
      (mul_le_mul_of_nonneg_right (by linarith) hδ'.le)
  simp only [CertModel.derivC]
  rw [hdeg]
  calc ‖fderiv ℂ f θ (Pi.single j 1) -
        (2 * (Real.pi : ℂ)) ^ (m.deg + 1) *
          (CertModel.ofDeriv W' j.val m.deg m.poly).poly.eval n θ‖
      ≤ ‖fderiv ℂ R θ (Pi.single j 1)‖ +
          ‖c * fderiv ℂ (m.poly.eval n) θ (Pi.single j 1) -
            (2 * (Real.pi : ℂ)) ^ (m.deg + 1) *
              (CertModel.ofDeriv W' j.val m.deg m.poly).poly.eval n θ‖ := by
        rw [hRe]
        have e : fderiv ℂ f θ (Pi.single j 1) -
            (2 * (Real.pi : ℂ)) ^ (m.deg + 1) *
              (CertModel.ofDeriv W' j.val m.deg m.poly).poly.eval n θ =
            (fderiv ℂ f θ (Pi.single j 1) - c * fderiv ℂ (m.poly.eval n) θ (Pi.single j 1)) +
            (c * fderiv ℂ (m.poly.eval n) θ (Pi.single j 1) -
              (2 * (Real.pi : ℂ)) ^ (m.deg + 1) *
                (CertModel.ofDeriv W' j.val m.deg m.poly).poly.eval n θ) := by ring
        rw [e]
        exact norm_add_le _ _
    _ ≤ ((ρ - W'.rho : ℚ) : ℝ)⁻¹ * ((2 * Real.pi) ^ m.deg * val m.rad) +
          (2 * Real.pi) ^ (m.deg + 1) * val (CertModel.ofDeriv W' j.val m.deg m.poly).rad := by
        refine add_le_add hcs ?_
        have := hD
        rw [hdeg] at this
        exact this
    _ ≤ (2 * Real.pi) ^ (m.deg + 1) *
          val (upAdd (CertModel.ofDeriv W' j.val m.deg m.poly).rad
            (upMul m.rad (ofRatUp (cauchyFactor (ρ - W'.rho))))) := by
        have h2 : (0 : ℝ) < (2 * Real.pi) ^ (m.deg + 1) := by positivity
        nlinarith

end KAM.CertificateSharp.Hybrid

end
