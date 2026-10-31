/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ComponentsFirst
public import KAM.Wave.Homological.AngleSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Component bounds, part C: the angle derivatives (blueprint-W `bpW:w4:components` (ii))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

Evaluation of `∂_{θ_i} R` at the test points and extraction of the coefficients
(`bpW:w4:extract`). This file proves the scalar, linear and `z`-quadratic bounds; the mixed
`Q` bound and the final statement `homComp_angle_gen` are in `ComponentsAngleQ.lean`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

theorem homRtheta_y_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a
    p pb s)
    (i : Fin 2)
    (θ y : Fin 2 → ℂ) :
    homRtheta_gen ha hp hpb T i θ y 0 0 = homPartial i T.a0 θ + ∑ k, homPartial i T.b θ k * y k :=
        by
  simp [homRtheta_gen, homPairRep_eq_gen]

theorem homRtheta_z_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a
    p pb s)
    (i : Fin 2)
    (θ : Fin 2 → ℂ) (ζ : ℂ) (z0 : HomL2) :
    homRtheta_gen ha hp hpb T i θ 0 (ζ • z0) 0 = homPartial i T.a0 θ
      + ζ * homPairRep_gen ha (homPP hp hpb) (homPartial i T.cp θ) z0
      + ζ ^ 2 * homPairRep_gen ha (homPP hp hpb) (homPartial i T.P θ z0) z0 := by
  simp [homRtheta_gen, homPairRep_eq_gen, map_smul]
  ring

theorem homRtheta_zb_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a
    p pb s)
    (i : Fin 2)
    (θ : Fin 2 → ℂ) (ζ : ℂ) (z0 : HomL2) :
    homRtheta_gen ha hp hpb T i θ 0 0 (ζ • z0) = homPartial i T.a0 θ
      + ζ * homPairRep_gen ha (homPP hp hpb) (homPartial i T.cm θ) z0
      + ζ ^ 2 * homPairRep_gen ha (homPP hp hpb) (homPartial i T.P' θ z0) z0 := by
  simp [homRtheta_gen, homPairRep_eq_gen, map_smul]
  ring

/-- **Zeroth order**: `|∂_{θ_i} a| ≤ 2π r² ε`. -/
theorem homAngle_a_gen {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0 <
    r)
    (T : HomTaylor_gen a p pb s) (hX : HomFieldBound_gen ha hp hpb r ε T) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (i : Fin 2) :
    ‖homPartial i T.a0 θ‖ ≤ 2 * Real.pi * r ^ 2 * ε := by
  have h := (homXnorm_parts_gen ha hp hpb hr T
    (hX θ 0 0 0 (homDomain_y hθ hr (by simpa using pow_pos hr 2)))).2.1
  have := (norm_le_pi_norm (fun i => homRtheta_gen ha hp hpb T i θ 0 0 0) i).trans h
  rw [homRtheta_y_gen] at this
  simpa using this


/-- **Linear order in `y`**: `∑_k |∂_{θ_i} b_k| ≤ 2π ε` (the dual of the max norm). -/
theorem homAngle_b_gen {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0 <
    r)
    (T : HomTaylor_gen a p pb s) (hX : HomFieldBound_gen ha hp hpb r ε T) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (i : Fin 2) :
    ∑ k, ‖homPartial i T.b θ k‖ ≤ 2 * Real.pi * ε := by
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  set β : Fin 2 → ℂ := homPartial i T.b θ with hβ
  let L : (Fin 2 → ℂ) →L[ℂ] ℂ := ∑ k, (β k) • ContinuousLinearMap.proj k
  have hLy : ∀ y : Fin 2 → ℂ, L y = ∑ k, β k * y k := fun y => by simp [L]
  have hL := homAffine_bound hr2 (homPartial i T.a0 θ) L (K := 2 * Real.pi * r ^ 2 * ε)
    (fun y0 hy0 ζ hζ => by
      have hd : ‖ζ • y0‖ < r ^ 2 := by
        rw [norm_smul]
        calc ‖ζ‖ * ‖y0‖ ≤ ‖ζ‖ * 1 := mul_le_mul_of_nonneg_left hy0 (norm_nonneg _)
          _ < _ := by linarith
      have h := (homXnorm_parts_gen ha hp hpb hr T (hX θ (ζ • y0) 0 0 (homDomain_y hθ hr hd))).2.1
      have h2 := (norm_le_pi_norm (fun i => homRtheta_gen ha hp hpb T i θ (ζ • y0) 0 0) i).trans h
      rw [homRtheta_y_gen] at h2
      have e : homPartial i T.a0 θ + ∑ k, homPartial i T.b θ k * (ζ • y0) k =
          homPartial i T.a0 θ + ζ • L y0 := by
        rw [hLy, smul_eq_mul, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [e] at h2
      exact h2)
  have hK : 2 * Real.pi * r ^ 2 * ε / r ^ 2 = 2 * Real.pi * ε := by field_simp
  rw [hK] at hL
  -- the extremal `y0`
  let y0 : Fin 2 → ℂ := fun k => if β k = 0 then 0 else (starRingEnd ℂ (β k)) / (‖β k‖ : ℂ)
  have hy0 : ‖y0‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
    by_cases h : β k = 0
    · simp [y0, h]
    · have hn : 0 < ‖β k‖ := norm_pos_iff.mpr h
      simp only [y0, h, ite_false, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm]
      rw [div_self hn.ne']
  have hLy0 : L y0 = ((∑ k, ‖β k‖ : ℝ) : ℂ) := by
    rw [hLy]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : β k = 0
    · simp [y0, h]
    · have hn : (‖β k‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr h).ne'
      simp only [y0, h, ite_false]
      rw [mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      field_simp
  have := (L.le_opNorm y0).trans (mul_le_of_le_one_right (norm_nonneg L) hy0)
  rw [hLy0] at this
  have hs : 0 ≤ ∑ k, ‖β k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] at this
  exact this.trans hL


theorem homQuad_of_unit {B : HomOp} {M : ℝ} (h : ∀ z : HomL2, ‖z‖ ≤ 1 → ‖homPairL2 (B z) z‖ ≤ M)
    (z : HomL2) : ‖homPairL2 (B z) z‖ ≤ M * ‖z‖ ^ 2 := by
  by_cases hz : z = 0
  · subst hz; simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set z0 : HomL2 := ((‖z‖⁻¹ : ℝ) : ℂ) • z with hz0
  have h1 : ‖z0‖ ≤ 1 := by
    rw [hz0, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']
  have e : z = ((‖z‖ : ℝ) : ℂ) • z0 := by
    rw [hz0, smul_smul]
    have : ((‖z‖ : ℝ) : ℂ) * ((‖z‖⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne']; simp
    rw [this, one_smul]
  have h2 := h z0 h1
  conv_lhs => rw [e]
  simp only [map_smul, smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hn]
  nlinarith [h2, hn]

/-- **First and second order in `z`**: `‖⟨∂_{θ_i}c^+, z₀⟩₀‖ ≤ 2√2π r ε` and
`|⟨∂_{θ_i}P z₀, z₀⟩₀| ≤ 4πε` for `‖z₀‖ ≤ 1`. -/
theorem homAngle_z_gen {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0 <
    r)
    (T : HomTaylor_gen a p pb s) (hX : HomFieldBound_gen ha hp hpb r ε T) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (i : Fin 2) (z0 : HomL2) (hz0 : ‖z0‖ ≤ 1) :
    ‖homPairRep_gen ha (homPP hp hpb) (homPartial i T.cp θ) z0‖ ≤ 2 * Real.sqrt 2 * Real.pi * r * ε
        ∧
      ‖homPairRep_gen ha (homPP hp hpb) (homPartial i T.P θ z0) z0‖ ≤ 4 * Real.pi * ε := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hρ : 0 < r / Real.sqrt 2 := by positivity
  have h := polyExtract_one
    (![homPartial i T.a0 θ, homPairRep_gen ha (homPP hp hpb) (homPartial i T.cp θ) z0,
      homPairRep_gen ha (homPP hp hpb) (homPartial i T.P θ z0) z0] : Fin 3 → ℂ) hρ
    (K := 2 * Real.pi * r ^ 2 * ε) (fun ζ hζ => by
      have hd : ‖ζ • z0‖ < r / Real.sqrt 2 := by
        rw [norm_smul]
        calc ‖ζ‖ * ‖z0‖ ≤ ‖ζ‖ * 1 := mul_le_mul_of_nonneg_left hz0 (norm_nonneg _)
          _ < _ := by linarith
      have h1 := (homXnorm_parts_gen ha hp hpb hr T (hX θ 0 (ζ • z0) 0 (homDomain_z hθ hr hd))).2.1
      have h2 := (norm_le_pi_norm (fun i => homRtheta_gen ha hp hpb T i θ 0 (ζ • z0) 0) i).trans h1
      rw [homRtheta_z_gen] at h2
      have : ∑ q : Fin 3, ζ ^ (q : ℕ) • (![homPartial i T.a0 θ,
          homPairRep_gen ha (homPP hp hpb) (homPartial i T.cp θ) z0,
          homPairRep_gen ha (homPP hp hpb) (homPartial i T.P θ z0) z0] : Fin 3 → ℂ) q =
          homPartial i T.a0 θ + ζ * homPairRep_gen ha (homPP hp hpb) (homPartial i T.cp θ) z0
            + ζ ^ 2 * homPairRep_gen ha (homPP hp hpb) (homPartial i T.P θ z0) z0 := by
        simp [Fin.sum_univ_three]
      rw [this]; exact h2)
  have h1 := h 1
  have h2 := h 2
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.val_one, pow_one,
    Fin.val_two] at h1 h2
  refine ⟨h1.trans_eq ?_, h2.trans_eq ?_⟩
  · field_simp
  · have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    simp only [h22]
    ring

/-- The same for `c^-` and `P'`. -/
theorem homAngle_zb_gen {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0 <
    r)
    (T : HomTaylor_gen a p pb s) (hX : HomFieldBound_gen ha hp hpb r ε T) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (i : Fin 2) (z0 : HomL2) (hz0 : ‖z0‖ ≤ 1) :
    ‖homPairRep_gen ha (homPP hp hpb) (homPartial i T.cm θ) z0‖ ≤ 2 * Real.sqrt 2 * Real.pi * r * ε
        ∧
      ‖homPairRep_gen ha (homPP hp hpb) (homPartial i T.P' θ z0) z0‖ ≤ 4 * Real.pi * ε := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hρ : 0 < r / Real.sqrt 2 := by positivity
  have h := polyExtract_one
    (![homPartial i T.a0 θ, homPairRep_gen ha (homPP hp hpb) (homPartial i T.cm θ) z0,
      homPairRep_gen ha (homPP hp hpb) (homPartial i T.P' θ z0) z0] : Fin 3 → ℂ) hρ
    (K := 2 * Real.pi * r ^ 2 * ε) (fun ζ hζ => by
      have hd : ‖ζ • z0‖ < r / Real.sqrt 2 := by
        rw [norm_smul]
        calc ‖ζ‖ * ‖z0‖ ≤ ‖ζ‖ * 1 := mul_le_mul_of_nonneg_left hz0 (norm_nonneg _)
          _ < _ := by linarith
      have h1 := (homXnorm_parts_gen ha hp hpb hr T (hX θ 0 0 (ζ • z0) (homDomain_zb hθ hr hd))).2.1
      have h2 := (norm_le_pi_norm (fun i => homRtheta_gen ha hp hpb T i θ 0 0 (ζ • z0)) i).trans h1
      rw [homRtheta_zb_gen] at h2
      have : ∑ q : Fin 3, ζ ^ (q : ℕ) • (![homPartial i T.a0 θ,
          homPairRep_gen ha (homPP hp hpb) (homPartial i T.cm θ) z0,
          homPairRep_gen ha (homPP hp hpb) (homPartial i T.P' θ z0) z0] : Fin 3 → ℂ) q =
          homPartial i T.a0 θ + ζ * homPairRep_gen ha (homPP hp hpb) (homPartial i T.cm θ) z0
            + ζ ^ 2 * homPairRep_gen ha (homPP hp hpb) (homPartial i T.P' θ z0) z0 := by
        simp [Fin.sum_univ_three]
      rw [this]; exact h2)
  have h1 := h 1
  have h2 := h 2
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.val_one, pow_one,
    Fin.val_two] at h1 h2
  refine ⟨h1.trans_eq ?_, h2.trans_eq ?_⟩
  · field_simp
  · have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    simp only [h22]
    ring

end KAM.Wave
