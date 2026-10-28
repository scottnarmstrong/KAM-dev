/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.KAMInputs

/-!
# P Part 5: the frequency bounds of the torus family (`bpP:p5:torus-conv`, `stepP:p5:tc-freq`)

`frequency_bounds` bounds the fast frequency by a constant and the slow frequency by that
constant times `mu` on the parameter set `pgD0`, from the jet bounds of `FrequencyLip`,
the bound `M0` of the complexified fast Hamiltonian, and the real/complex frequency bridge.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FAM.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Planetary

variable {a b : ℕ}

theorem frequency_bounds (d : PGData a b) : ∃ Cw : ℝ, 0 < Cw ∧ ∀ r mu : ℝ,
    admissible d (pgRstar d) r mu → ∀ J ∈ pgD0 d r mu,
      ‖(blockFast ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) : Fin a → ℝ)‖ ≤ Cw ∧
      ‖(blockSlow ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) : Fin b → ℝ)‖ ≤ Cw*mu := by
  have hpi := Real.pi_pos
  have hM0 := (pgExtension d).M0_pos
  have hjp := jpBound_ge_one d
  have hk2 := jetK2_nonneg d
  have hk4 := jetK4_nonneg d
  have hδ := (pgExtension d).delta_pos
  refine ⟨(2*Real.pi)⁻¹*((pgExtension d).M0 + jpBound d + jetK2 d + b*jetK4 d), by positivity,
    fun r mu h J hJ => ?_⟩
  obtain ⟨hJ', hJd⟩ := hJ
  have hmu : mu ∈ Icc 0 d.mu0 := mu_mem_Icc h
  have hmu0 : 0 < mu := h.2.2.1
  have hmu1 : mu < 1 := mu_lt_one_of_admissible h
  have hJV : blockFast J ∈ d.V := hJ'.1.1.1
  obtain ⟨hr1, -, -, hl1, -⟩ := kh_dyn h
  have hxi : ‖KAM.realInclusion b (blockSlow J)‖ ≤ 1 := by
    rw [KAM.norm_realInclusion]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    obtain ⟨hj1, hj2⟩ := hJ'.2 j (mem_univ j)
    have := params_l2top d r mu
    have hr2 : r^2 < 1 := by nlinarith [h.1]
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hI2 : blockFast (KAM.realInclusion (a+b) J) ∈
      KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2) :=
    realInclusion_mem_actionNbhd (by linarith) (subset_closure hJV)
  have hI16 : blockFast (KAM.realInclusion (a+b) J) ∈
      KAM.actionNbhd (closure d.V) ((pgExtension d).delta/16) :=
    realInclusion_mem_actionNbhd (by linarith) (subset_closure hJV)
  have hbr := complexFrequency_realSlice d hmu hJV
  have hfast := blockFast_complexFrequency d hmu hI2
  have hslow := blockSlow_complexFrequency d hmu hI2
  rw [hbr] at hfast hslow
  have hbf : ‖(blockFast (freq d.H0 d.P0 d.Omega d.beta mu J) : Fin a → ℝ)‖ ≤
      (pgExtension d).M0 + jpBound d := by
    have e1 : ‖blockFast (KAM.realInclusion (a+b) (freq d.H0 d.P0 d.Omega d.beta mu J))‖ =
        ‖(blockFast (freq d.H0 d.P0 d.Omega d.beta mu J) : Fin a → ℝ)‖ :=
      KAM.norm_realInclusion _
    rw [← e1, hfast]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (pi_norm_le_iff_of_nonneg hM0.le).2 fun i => ?_
      have hb := ((pgExtension d).h0bounds _ (mem_actionNbhd_mono (by linarith) hI2)).2.1
      have hs1 : ‖(Pi.single i (1:ℂ) : Fin a → ℂ)‖ ≤ 1 :=
        (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
          by_cases hj : j = i <;> simp [hj]
      have hop := (fderiv ℂ (pgExtension d).H0
        (blockFast (KAM.realInclusion (a+b) J))).le_opNorm (Pi.single i (1:ℂ))
      show ‖fderiv ℂ (pgExtension d).H0 (blockFast (KAM.realInclusion (a+b) J))
        (Pi.single i 1)‖ ≤ _
      calc _ ≤ _ := hop
        _ ≤ ‖fderiv ℂ (pgExtension d).H0 (blockFast (KAM.realInclusion (a+b) J))‖ * 1 := by
            gcongr
        _ ≤ _ := by linarith
    · rw [norm_smul]
      have := norm_jpGrad_le d hmu hxi hI16
      have e : ‖(mu : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmu0]; exact hmu1.le
      calc _ ≤ 1 * jpBound d := mul_le_mul e this (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  have hbs : ‖(blockSlow (freq d.H0 d.P0 d.Omega d.beta mu J) : Fin b → ℝ)‖ ≤
      mu*(jetK2 d + b*jetK4 d) := by
    have e1 : ‖blockSlow (KAM.realInclusion (a+b) (freq d.H0 d.P0 d.Omega d.beta mu J))‖ =
        ‖(blockSlow (freq d.H0 d.P0 d.Omega d.beta mu J) : Fin b → ℝ)‖ :=
      KAM.norm_realInclusion _
    rw [← e1, hslow, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmu0]
    exact mul_le_mul_of_nonneg_left (norm_jpTheta_le d hmu hxi
      (mem_actionNbhd_mono (by linarith) hI16)) hmu0.le
  have hc : 0 ≤ (2*Real.pi)⁻¹ := by positivity
  have bf : blockFast ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) =
      (2*Real.pi)⁻¹ • blockFast (freq d.H0 d.P0 d.Omega d.beta mu J) := rfl
  have bs : blockSlow ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) =
      (2*Real.pi)⁻¹ • blockSlow (freq d.H0 d.P0 d.Omega d.beta mu J) := rfl
  constructor
  · rw [bf, norm_smul, Real.norm_of_nonneg hc]
    calc _ ≤ (2*Real.pi)⁻¹ * ((pgExtension d).M0 + jpBound d) :=
          mul_le_mul_of_nonneg_left hbf hc
      _ ≤ _ := by
          have : 0 ≤ (b:ℝ)*jetK4 d := by positivity
          exact mul_le_mul_of_nonneg_left (by linarith) hc
  · rw [bs, norm_smul, Real.norm_of_nonneg hc]
    calc _ ≤ (2*Real.pi)⁻¹ * (mu*(jetK2 d + b*jetK4 d)) :=
          mul_le_mul_of_nonneg_left hbs hc
      _ ≤ _ := by
          have : 0 ≤ (b:ℝ)*jetK4 d := by positivity
          nlinarith [mul_nonneg hc hmu0.le, mul_nonneg (mul_nonneg hc hmu0.le) hM0.le,
            mul_nonneg (mul_nonneg hc hmu0.le) (by linarith : (0:ℝ) ≤ jpBound d)]

end KAM.Planetary

end
