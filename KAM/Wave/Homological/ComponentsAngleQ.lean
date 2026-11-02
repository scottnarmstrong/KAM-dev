/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ComponentsAngle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Component bounds, part D: the mixed term and the statement (blueprint-W `bpW:w4:components` (ii))

`homComp_angle_gen`: if `|X_R|_r ≤ ε` on `D(s,r)` then for `θ ∈ T_s`, `i ∈ {1,2}`:
`|∂_i a| ≤ 2π r² ε`, `|∂_i b|₁ ≤ 2π ε`, `‖∂_i c^±‖_* ≤ 2√2 π r ε`,
`‖Λ∂_i P‖_bil, ‖Λ∂_i P'‖_bil ≤ 4π ε`, `‖Λ∂_i Q‖_bil ≤ 16π ε`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

theorem homRtheta_zzb_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen
    a p pb
    s) (i : Fin 2)
    (θ : Fin 2 → ℂ) (ζ η : ℂ) (z0 z1 : HomL2) :
    homRtheta_gen ha hp hpb T i θ 0 (ζ • z0) (η • z1) = homPartial i T.a0 θ
      + ζ * homPairRep_gen ha (homPP hp hpb) (homPartial i T.cp θ) z0
      + η * homPairRep_gen ha (homPP hp hpb) (homPartial i T.cm θ) z1
      + ζ ^ 2 * homPairRep_gen ha (homPP hp hpb) (homPartial i T.P θ z0) z0
      + ζ * η * homPairRep_gen ha (homPP hp hpb) (homPartial i T.Q θ z0) z1
      + η ^ 2 * homPairRep_gen ha (homPP hp hpb) (homPartial i T.P' θ z1) z1 := by
  simp [homRtheta_gen, homPairRep_eq_gen, map_smul]
  ring

/-- The mixed coefficient: `|⟨∂_{θ_i}Q z₀, z₁⟩₀| ≤ 16π ε` for `‖z₀‖, ‖z₁‖ ≤ 1`. -/
theorem homAngle_Q_gen {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0 <
    r)
    (T : HomTaylor_gen a p pb s) (hX : HomFieldBound_gen ha hp hpb r ε T) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (i : Fin 2) (z0 z1 : HomL2) (h0 : ‖z0‖ ≤ 1) (h1 : ‖z1‖ ≤ 1) :
    ‖homPairRep_gen ha (homPP hp hpb) (homPartial i T.Q θ z0) z1‖ ≤ 16 * Real.pi * ε := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hρ : 0 < r / (2 * Real.sqrt 2) := by positivity
  set c : Fin 3 → Fin 3 → ℂ :=
    ![![homPartial i T.a0 θ, homPairRep_gen ha (homPP hp hpb) (homPartial i T.cm θ) z1,
        homPairRep_gen ha (homPP hp hpb) (homPartial i T.P' θ z1) z1],
      ![homPairRep_gen ha (homPP hp hpb) (homPartial i T.cp θ) z0, homPairRep_gen ha (homPP hp hpb)
          (homPartial i T.Q θ z0) z1, 0],
      ![homPairRep_gen ha (homPP hp hpb) (homPartial i T.P θ z0) z0, 0, 0]] with hc
  have hz : ∀ (z : HomL2) (ζ : ℂ), ‖z‖ ≤ 1 → ‖ζ‖ < r / (2 * Real.sqrt 2) →
      ‖ζ • z‖ < r / (2 * Real.sqrt 2) := fun z ζ hz hζ => by
    rw [norm_smul]
    calc ‖ζ‖ * ‖z‖ ≤ ‖ζ‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ < _ := by linarith
  have h := polyExtract hρ hρ (c := c) (K := 2 * Real.pi * r ^ 2 * ε)
    (fun p q hpq => by
      fin_cases p <;> fin_cases q <;> simp_all)
    (fun ζ η hζ hη => by
      have hd := homXnorm_parts_gen ha hp hpb hr T
        (hX θ 0 (ζ • z0) (η • z1) (homDomain_zzb hθ hr (hz z0 ζ h0 hζ) (hz z1 η h1 hη)))
      have h2 := (norm_le_pi_norm (fun i => homRtheta_gen ha hp hpb T i θ 0 (ζ • z0) (η • z1))
          i).trans
          hd.2.1
      rw [homRtheta_zzb_gen] at h2
      have : polyEval2 c ζ η = homPartial i T.a0 θ
          + ζ * homPairRep_gen ha (homPP hp hpb) (homPartial i T.cp θ) z0
          + η * homPairRep_gen ha (homPP hp hpb) (homPartial i T.cm θ) z1
          + ζ ^ 2 * homPairRep_gen ha (homPP hp hpb) (homPartial i T.P θ z0) z0
          + ζ * η * homPairRep_gen ha (homPP hp hpb) (homPartial i T.Q θ z0) z1
          + η ^ 2 * homPairRep_gen ha (homPP hp hpb) (homPartial i T.P' θ z1) z1 := by
        simp [polyEval2, Fin.sum_univ_three, hc]
        ring
      rw [this]; exact h2) 1 1 (by simp)
  simp only [hc, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.val_one, pow_one] at h
  refine h.trans_eq ?_
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  simp only [h22]
  ring

/-- **Component bounds, (ii)** (blueprint `bpW:w4:components` (ii)). -/
theorem homComp_angle_gen {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0
    < r)
    (T : HomTaylor_gen a p pb s) (hX : HomFieldBound_gen ha hp hpb r ε T) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (i : Fin 2) :
    ‖homPartial i T.a0 θ‖ ≤ 2 * Real.pi * r ^ 2 * ε ∧
      ∑ k, ‖homPartial i T.b θ k‖ ≤ 2 * Real.pi * ε ∧
      homDualNorm_gen ha (homPP hp hpb) (homPartial i T.cp θ) ≤ 2 * Real.sqrt 2 * Real.pi * r * ε ∧
      homDualNorm_gen ha (homPP hp hpb) (homPartial i T.cm θ) ≤ 2 * Real.sqrt 2 * Real.pi * r * ε ∧
      ‖homLamCLM_gen ha (homPP hp hpb) (homPartial i T.P θ)‖ ≤ 4 * Real.pi * ε ∧
      ‖homLamCLM_gen ha (homPP hp hpb) (homPartial i T.P' θ)‖ ≤ 4 * Real.pi * ε ∧
      ‖homLamCLM_gen ha (homPP hp hpb) (homPartial i T.Q θ)‖ ≤ 16 * Real.pi * ε := by
  have hopen := isOpen_complexStrip 2 s
  have hε : 0 ≤ ε := (homXnorm_nonneg_gen ha hp hpb hr T θ 0 0 0).trans
    (hX θ 0 0 0 (homDomain_y hθ hr (by simpa using pow_pos hr 2)))
  have hdP : DifferentiableAt ℂ T.P θ := T.comp_P.1.differentiableAt (hopen.mem_nhds hθ)
  have hdP' : DifferentiableAt ℂ T.P' θ := T.comp_P'.1.differentiableAt (hopen.mem_nhds hθ)
  refine ⟨homAngle_a_gen ha hp hpb hr T hX hθ i, homAngle_b_gen ha hp hpb hr T hX hθ i, ?_, ?_, ?_,
      ?_, ?_⟩
  · exact norm_le_of_pairing_le fun y hy => (homAngle_z_gen ha hp hpb hr T hX hθ i y hy).1
  · exact norm_le_of_pairing_le fun y hy => (homAngle_zb_gen ha hp hpb hr T hX hθ i y hy).1
  · refine norm_le_of_quadratic (homLam_entry_symm_gen ha hp hpb
      (homNormalEntry_partial_symm_gen hdP (hopen.mem_nhds hθ) T.symP i)) fun z => homQuad_of_unit
          (fun
          z hz => ?_) z
    exact (homAngle_z_gen ha hp hpb hr T hX hθ i z hz).2
  · refine norm_le_of_quadratic (homLam_entry_symm_gen ha hp hpb
      (homNormalEntry_partial_symm_gen hdP' (hopen.mem_nhds hθ) T.symP' i)) fun z => homQuad_of_unit
          (fun z hz => ?_) z
    exact (homAngle_zb_gen ha hp hpb hr T hX hθ i z hz).2
  · refine ContinuousLinearMap.opNorm_le_of_unit_norm (by have := Real.pi_pos; positivity) fun z0
      hz0 => ?_
    refine norm_le_of_pairing_le fun z1 hz1 => ?_
    exact homAngle_Q_gen ha hp hpb hr T hX hθ i z0 z1 hz0.le hz1

end KAM.Wave
