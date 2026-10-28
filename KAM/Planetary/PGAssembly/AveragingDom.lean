/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingFacts

/-!
# P Part 5: positivity and the transformed domain (`stepP:p5:av-dict`)

`pg_osc_positive` and `pg_osc_domain`: the image of the P2 half-domain under the normalization is
exactly `averagingDomain`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ}

theorem sqrt_two_pi_pos : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.2 (by positivity)

theorem blockFast_normalize_fst (z : CPhase (a+b)) :
    blockFast (pgOscNormalize z).1 = (2*Real.pi:ℂ) • blockFast z.1 := blockFast_append _ _

theorem blockSlow_normalize_fst (z : CPhase (a+b)) :
    blockSlow (pgOscNormalize z).1 = (Real.sqrt (2*Real.pi):ℂ) • blockSlow z.1 :=
  blockSlow_append _ _

theorem blockFast_normalize_snd (z : CPhase (a+b)) :
    blockFast (pgOscNormalize z).2 = blockFast z.2 := blockFast_append _ _

theorem blockSlow_normalize_snd (z : CPhase (a+b)) :
    blockSlow (pgOscNormalize z).2 = (Real.sqrt (2*Real.pi):ℂ) • blockSlow z.2 :=
  blockSlow_append _ _

theorem norm_real_smul_lt_iff {N : ℕ} {s t : ℝ} (hs : 0 < s) (v : Fin N → ℂ) :
    ‖(s:ℂ) • v‖ < t ↔ ‖v‖ < t/s := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, lt_div_iff₀ hs, mul_comm]

theorem strip_smul_iff {N : ℕ} {s S : ℝ} (hs : 0 < s) (θ : Fin N → ℂ) :
    (s:ℂ) • θ ∈ KAM.complexStrip N (s*S) ↔ θ ∈ KAM.complexStrip N S := by
  simp only [KAM.complexStrip, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
  refine forall_congr' fun i => ?_
  rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos hs]
  exact mul_lt_mul_iff_right₀ hs

theorem pg_osc_positive (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    (0 < r ∧ r < Real.exp (-1/5)) ∧ 0 < pgOscE d mu := by
  refine ⟨⟨h.1, av_r_lt_exp_fifth h⟩, ?_⟩
  unfold pgOscE
  have := pgAnalytic_LP_ge_one d
  have := h.2.2.1
  positivity

theorem pg_osc_domain (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    pgOscNormalize '' oscDom (checkedCore d r mu) ((params d r mu).rhoBar/2)
      (pgOscEpsilon d/2) (pgOscEpsilon d/2) (pgOscWidth d/6) = averagingDomain d r mu := by
  have hpi := Real.pi_pos
  have hs := sqrt_two_pi_pos
  have h2 : 0 < 2*Real.pi := by positivity
  have hwid : pgOscWidth d/6 = ((pgWidth d/6)) / (2*Real.pi) := by
    unfold pgOscWidth; ring
  have hstrip : ∀ θ : Fin a → ℂ, (2*Real.pi:ℂ) • θ ∈ KAM.complexStrip a (pgWidth d/6) ↔
      θ ∈ KAM.complexStrip a (pgOscWidth d/6) := by
    intro θ
    have := strip_smul_iff (N := a) h2 (S := pgOscWidth d/6) θ
    rw [← this]
    have e : 2*Real.pi*(pgOscWidth d/6) = pgWidth d/6 := by unfold pgOscWidth; field_simp
    rw [e]
    push_cast; rfl
  have hrad : ∀ v : Fin b → ℂ, ‖(Real.sqrt (2*Real.pi):ℂ) • v‖ < pgOscRadius d/2 ↔
      ‖v‖ < pgOscEpsilon d/2 := by
    intro v
    rw [norm_real_smul_lt_iff hs]
    unfold pgOscEpsilon
    rw [div_div, div_div, mul_comm]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y1, y2, y3, y4⟩ := mem_oscDom_pg.1 hy
    refine ⟨?_, ?_, ?_⟩
    · rw [blockFast_normalize_snd]; exact y2
    · rw [blockFast_normalize_fst]; exact (hstrip _).2 y1
    · rw [Prod.norm_def, blockSlow_normalize_snd, blockSlow_normalize_fst]
      exact max_lt ((hrad _).2 y3) ((hrad _).2 y4)
  · rintro ⟨z1, z2, z3⟩
    refine ⟨pgOscUnnormalize z, ?_, pgOscNormalize_unnormalize z⟩
    rw [Prod.norm_def, max_lt_iff] at z3
    refine mem_oscDom_pg.2 ⟨?_, ?_, ?_, ?_⟩
    · have : blockFast (pgOscUnnormalize z).1 = (2*Real.pi:ℂ)⁻¹ • blockFast z.1 :=
        blockFast_append _ _
      rw [this, ← hstrip, smul_smul, mul_inv_cancel₀ (by exact_mod_cast h2.ne'), one_smul]
      exact z2
    · have : blockFast (pgOscUnnormalize z).2 = blockFast z.2 := blockFast_append _ _
      rw [this]; exact z1
    · have : blockSlow (pgOscUnnormalize z).2 = (Real.sqrt (2*Real.pi):ℂ)⁻¹ • blockSlow z.2 :=
        blockSlow_append _ _
      rw [this, ← hrad, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hs.ne'), one_smul]
      exact z3.1
    · have : blockSlow (pgOscUnnormalize z).1 = (Real.sqrt (2*Real.pi):ℂ)⁻¹ • blockSlow z.1 :=
        blockSlow_append _ _
      rw [this, ← hrad, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hs.ne'), one_smul]
      exact z3.2

end KAM.Planetary

end
