/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ModifiedBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Lipschitz bounds of the components with modified divisors (`bpW:w5:w4-modified` (ii))

Off-frontier, source-faithful infrastructure (W5-MODIFIED, blueprint `bpW:w5:w4-modified`); the
dependency graph is still being built.

The two-parameter bounds of the components of `F(ξ) - F(ζ)` (W4's step *Lipschitz*, with the
multipliers of `HomModMultBounds` and their Lipschitz bounds `HomModMultLip`, step `m-lip`), with
the scale `E^W = B^W_σ(ε^L + 2Mε/α)d/α`:
* `homModLip_b`, `homModLip_cp`, `homModLip_cm`, `homModLip_P`, `homModLip_P'`, `homModLip_da`,
  `homModLip_db`: for any data `R₁, R₂ ∈ 𝒯_s` with the field bounds `ε`, `ε^L d` (applied to the
  reweighted data `homReweight R`, in `ModifiedLipDeriv.lean`);
* `homModLip_Q`, `homModLip_Qt`: the twisted `Q`-solves of `R₁.Q, R₂.Q` (weights `(p,p+1)`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

section lip

variable {a p pb s σ τ α M d : ℝ} {w₁ w₂ : Fin 2 → ℝ} {W₁ W₂ : ℕ+ → ℝ}
  (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε εL : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α)
  (hM : 0 ≤ M) (hd : 0 ≤ d) (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s)
  (hm₁ : HomModMultBounds a p pb τ α w₁ W₁) (hm₂ : HomModMultBounds a p pb τ α w₂ W₂)
  (hL : HomModMultLip a p pb τ α M d w₁ W₁ w₂ W₂) {θ : Fin 2 → ℂ}
  (hθ : θ ∈ complexStrip 2 (s - σ))
include ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hθ

theorem homModLip_b (R₁ R₂ : HomTaylor_gen a p pb s) (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂) :
    ‖homSolve (homTvec w₁) R₁.b θ - homSolve (homTvec w₂) R₂.b θ‖ ≤
      2 * Real.pi * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp hpb hr (R₁.homSub R₂) hXL hz
  have := homSolve_sub_le (m := 2 * Real.pi * ε) (mL := 2 * Real.pi * εL) (κ := 1) hτ hα le_rfl
    hM hd hσ hσs (norm_homModTvec_le hm₁) (norm_homModTvec_le hm₂)
    (norm_homModTvec_sub_le hL)
    R₁.comp_b.1 R₂.comp_b.1 R₁.comp_b.2.1 R₂.comp_b.2.1
    (fun z hz => (hf₁ z hz).1) (fun z hz => (hf₂ z hz).1)
    (fun z hz => by
      have h := (hfL z hz).1
      show ‖R₁.b z - R₂.b z‖ ≤ _
      calc _ ≤ _ := h
        _ = _ := by ring)
    (by positivity) θ hθ
  exact this.trans (le_of_eq (by ring))

theorem homModLip_cp (R₁ R₂ : HomTaylor_gen a p pb s) (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂) :
    ‖homSolve (homModTdp hm₁) R₁.cp θ - homSolve (homModTdp hm₂) R₂.cp θ‖ ≤
      r * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) / Real.sqrt 2 := by
  have hs : 0 < s := hσ.trans hσs
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp hpb hr (R₁.homSub R₂) hXL hz
  have := homSolve_sub_le (m := r * ε / Real.sqrt 2) (mL := r * εL / Real.sqrt 2) (κ := 1) hτ hα
    le_rfl hM hd hσ hσs (norm_homModTdp_le hm₁) (norm_homModTdp_le hm₂)
    (norm_homModTdp_sub_le hm₁ hm₂ hL)
    R₁.comp_cp.1 R₂.comp_cp.1 R₁.comp_cp.2.1 R₂.comp_cp.2.1
    (fun z hz => (hf₁ z hz).2.1) (fun z hz => (hf₂ z hz).2.1)
    (fun z hz => by
      have h := (hfL z hz).2.1
      show ‖R₁.cp z - R₂.cp z‖ ≤ _
      calc _ ≤ _ := h
        _ = _ := by ring)
    (by positivity) θ hθ
  exact this.trans (le_of_eq (by ring))

theorem homModLip_cm (R₁ R₂ : HomTaylor_gen a p pb s) (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂) :
    ‖homSolve (homModTdm hm₁) R₁.cm θ - homSolve (homModTdm hm₂) R₂.cm θ‖ ≤
      r * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) / Real.sqrt 2 := by
  have hs : 0 < s := hσ.trans hσs
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp hpb hr (R₁.homSub R₂) hXL hz
  have := homSolve_sub_le (m := r * ε / Real.sqrt 2) (mL := r * εL / Real.sqrt 2) (κ := 1) hτ hα
    le_rfl hM hd hσ hσs (norm_homModTdm_le hm₁) (norm_homModTdm_le hm₂)
    (norm_homModTdm_sub_le hm₁ hm₂ hL)
    R₁.comp_cm.1 R₂.comp_cm.1 R₁.comp_cm.2.1 R₂.comp_cm.2.1
    (fun z hz => (hf₁ z hz).2.2.1) (fun z hz => (hf₂ z hz).2.2.1)
    (fun z hz => by
      have h := (hfL z hz).2.2.1
      show ‖R₁.cm z - R₂.cm z‖ ≤ _
      calc _ ≤ _ := h
        _ = _ := by ring)
    (by positivity) θ hθ
  exact this.trans (le_of_eq (by ring))

theorem homModLip_P (R₁ R₂ : HomTaylor_gen a p pb s) (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂) :
    ‖(2 : ℂ) • (homSolve (homModTP hm₁) R₁.P θ - homSolve (homModTP hm₂) R₂.P θ)‖ ≤
      homKS * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX₁
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp hpb hr (R₁.homSub R₂) hXL hz
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hP₁ : ∀ z ∈ complexStrip 2 s, ‖R₁.P z‖ ≤ ε / 2 := fun z hz => by
    have := (hf₁ z hz).2.2.2.1
    rw [norm_smul, h2] at this; linarith
  have hP₂ : ∀ z ∈ complexStrip 2 s, ‖R₂.P z‖ ≤ ε / 2 := fun z hz => by
    have := (hf₂ z hz).2.2.2.1
    rw [norm_smul, h2] at this; linarith
  have hPL : ∀ z ∈ complexStrip 2 s, ‖R₁.P z - R₂.P z‖ ≤ (εL / 2) * d := fun z hz => by
    have this : ‖(2 : ℂ) • (R₁.P z - R₂.P z)‖ ≤ εL * d := (hfL z hz).2.2.2.1
    rw [norm_smul, h2] at this; linarith
  have := homSolve_sub_le (m := ε / 2) (mL := εL / 2) (κ := homKS) hτ hα one_le_homKS
    hM hd hσ hσs (norm_homModTP_le hm₁) (norm_homModTP_le hm₂)
    (norm_homModTP_sub_le hm₁ hm₂ hL)
    R₁.comp_P.1 R₂.comp_P.1 R₁.comp_P.2.1 R₂.comp_P.2.1 hP₁ hP₂ hPL (by positivity) θ hθ
  rw [norm_smul, h2]
  calc 2 * ‖homSolve (homModTP hm₁) R₁.P θ - homSolve (homModTP hm₂) R₂.P θ‖
      ≤ 2 * (homKS * waveBW τ σ / α * (εL / 2 + 2 * M * (ε / 2) / α) * d) := by gcongr
    _ = _ := by ring

theorem homModLip_P' (R₁ R₂ : HomTaylor_gen a p pb s) (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂) :
    ‖(2 : ℂ) • (homSolve (homModTP' hm₁) R₁.P' θ - homSolve (homModTP' hm₂) R₂.P' θ)‖ ≤
      homKS * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX₁
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp hpb hr (R₁.homSub R₂) hXL hz
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hP₁ : ∀ z ∈ complexStrip 2 s, ‖R₁.P' z‖ ≤ ε / 2 := fun z hz => by
    have := (hf₁ z hz).2.2.2.2.2.2
    rw [norm_smul, h2] at this; linarith
  have hP₂ : ∀ z ∈ complexStrip 2 s, ‖R₂.P' z‖ ≤ ε / 2 := fun z hz => by
    have := (hf₂ z hz).2.2.2.2.2.2
    rw [norm_smul, h2] at this; linarith
  have hPL : ∀ z ∈ complexStrip 2 s, ‖R₁.P' z - R₂.P' z‖ ≤ (εL / 2) * d := fun z hz => by
    have this : ‖(2 : ℂ) • (R₁.P' z - R₂.P' z)‖ ≤ εL * d := (hfL z hz).2.2.2.2.2.2
    rw [norm_smul, h2] at this; linarith
  have := homSolve_sub_le (m := ε / 2) (mL := εL / 2) (κ := homKS) hτ hα one_le_homKS
    hM hd hσ hσs (norm_homModTP'_le hm₁) (norm_homModTP'_le hm₂)
    (norm_homModTP'_sub_le hm₁ hm₂ hL)
    R₁.comp_P'.1 R₂.comp_P'.1 R₁.comp_P'.2.1 R₂.comp_P'.2.1 hP₁ hP₂ hPL (by positivity) θ hθ
  rw [norm_smul, h2]
  calc 2 * ‖homSolve (homModTP' hm₁) R₁.P' θ - homSolve (homModTP' hm₂) R₂.P' θ‖
      ≤ 2 * (homKS * waveBW τ σ / α * (εL / 2 + 2 * M * (ε / 2) / α) * d) := by gcongr
    _ = _ := by ring

/-- The twisted `Q`-solve (step `m-lip`, from the `p+1` bounds of `R.Q`). -/
theorem homModLip_Q (R₁ R₂ : HomTaylor_gen a p (p + 1) s)
    (hX₁ : HomFieldBound_gen ha hp (by linarith : p ≤ p + 1) r ε R₁)
    (hXL : HomFieldBound_gen ha hp (by linarith : p ≤ p + 1) r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp (by linarith : p ≤ p + 1) r ε R₂) :
    ‖homSolve (homModTQ hm₁) R₁.Q θ - homSolve (homModTQ hm₂) R₂.Q θ‖ ≤
      homKS * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp (by linarith : p ≤ p + 1) hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp (by linarith : p ≤ p + 1) hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp (by linarith : p ≤ p + 1) hr (R₁.homSub R₂) hXL hz
  have := homSolve_sub_le (m := ε) (mL := εL) (κ := homKS) hτ hα one_le_homKS
    hM hd hσ hσs (norm_homModTQ_le hm₁) (norm_homModTQ_le hm₂) (norm_homModTQ_sub_le hm₁ hm₂ hL)
    R₁.comp_Q.1 R₂.comp_Q.1 R₁.comp_Q.2.1 R₂.comp_Q.2.1
    (fun z hz => (hf₁ z hz).2.2.2.2.1) (fun z hz => (hf₂ z hz).2.2.2.2.1)
    (fun z hz => by
      have h := (hfL z hz).2.2.2.2.1
      show ‖R₁.Q z - R₂.Q z‖ ≤ _
      calc _ ≤ _ := h
        _ = _ := by ring)
    hεL θ hθ
  exact this.trans (le_of_eq (by ring))

theorem homModLip_Qt (R₁ R₂ : HomTaylor_gen a p (p + 1) s)
    (hX₁ : HomFieldBound_gen ha hp (by linarith : p ≤ p + 1) r ε R₁)
    (hXL : HomFieldBound_gen ha hp (by linarith : p ≤ p + 1) r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp (by linarith : p ≤ p + 1) r ε R₂) :
    ‖homSolve (homModTQt hm₁) R₁.Qt θ - homSolve (homModTQt hm₂) R₂.Qt θ‖ ≤
      homKS * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp (by linarith : p ≤ p + 1) hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp (by linarith : p ≤ p + 1) hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp (by linarith : p ≤ p + 1) hr (R₁.homSub R₂) hXL hz
  have := homSolve_sub_le (m := ε) (mL := εL) (κ := homKS) hτ hα one_le_homKS
    hM hd hσ hσs (norm_homModTQt_le hm₁) (norm_homModTQt_le hm₂)
    (norm_homModTQt_sub_le hm₁ hm₂ hL)
    R₁.comp_Qt.1 R₂.comp_Qt.1 R₁.comp_Qt.2.1 R₂.comp_Qt.2.1
    (fun z hz => (hf₁ z hz).2.2.2.2.2.1) (fun z hz => (hf₂ z hz).2.2.2.2.2.1)
    (fun z hz => by
      have h := (hfL z hz).2.2.2.2.2.1
      show ‖R₁.Qt z - R₂.Qt z‖ ≤ _
      calc _ ≤ _ := h
        _ = _ := by ring)
    hεL θ hθ
  exact this.trans (le_of_eq (by ring))

theorem homModLip_da (R₁ R₂ : HomTaylor_gen a p pb s) (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂) (i : Fin 2) :
    ‖homPartial i (homSolve (homTscal w₁) R₁.a0) θ -
        homPartial i (homSolve (homTscal w₂) R₂.a0) θ‖ ≤
      2 * Real.pi * r ^ 2 * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX₁
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i =>
    homComp_angle_gen ha hp hpb hr (R₁.homSub R₂) hXL hz i
  obtain ⟨C₁, hC₁⟩ := R₁.comp_a0.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_a0.2.2
  have hopen := isOpen_complexStrip 2 s
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂) (mΛ := max C₁ C₂)
    (mΛ' := 2 * Real.pi * r ^ 2 * ε) (mL' := 2 * Real.pi * r ^ 2 * εL) (κ := 1) (κ' := 1)
    hτ hα le_rfl le_rfl hM hd (by positivity) hσ hσs (T₁ := homTscal w₁) (T₂ := homTscal w₂)
    (T₁' := homTscal w₁) (T₂' := homTscal w₂)
    (norm_homModTscal_le hm₁) (norm_homModTscal_le hm₂) (norm_homModTscal_le hm₁)
    (norm_homModTscal_le hm₂) (norm_homModTscal_sub_le hL) (ContinuousLinearMap.id ℂ ℂ)
    (fun k => by simp) (fun k => by simp)
    R₁.comp_a0.1 R₂.comp_a0.1 R₁.comp_a0.2.1 R₂.comp_a0.2.1 hC₁ hC₂
    (fun z hz => by simpa using (hC₁ z hz).trans (le_max_left _ _))
    (fun z hz => by simpa using (hC₂ z hz).trans (le_max_right _ _)) i
    (fun z hz => by simpa using (ha₁ z hz i).1) (fun z hz => by simpa using (ha₂ z hz i).1)
    (fun z hz => by
      rw [homPartial_clm_sub (ContinuousLinearMap.id ℂ ℂ)
        (R₁.comp_a0.1.differentiableAt (hopen.mem_nhds hz))
        (R₂.comp_a0.1.differentiableAt (hopen.mem_nhds hz)) i]
      have h := (haL z hz i).1
      simp only [ContinuousLinearMap.id_apply]
      calc _ ≤ _ := h
        _ = _ := by ring)
    hθ
  simp only [ContinuousLinearMap.id_apply] at this
  exact this.trans (le_of_eq (by ring))

theorem homModLip_db (R₁ R₂ : HomTaylor_gen a p pb s) (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂) (i : Fin 2) (y : Fin 2 → ℂ) :
    ‖∑ k, (homPartial i (homSolve (homTvec w₁) R₁.b) θ k -
        homPartial i (homSolve (homTvec w₂) R₂.b) θ k) * y k‖ ≤
      2 * Real.pi * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) * ‖y‖ := by
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX₁
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i =>
    homComp_angle_gen ha hp hpb hr (R₁.homSub R₂) hXL hz i
  obtain ⟨C₁, hC₁⟩ := R₁.comp_b.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_b.2.2
  have hopen := isOpen_complexStrip 2 s
  have d1 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₁.b z := fun z hz =>
    R₁.comp_b.1.differentiableAt (hopen.mem_nhds hz)
  have d2 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₂.b z := fun z hz =>
    R₂.comp_b.1.differentiableAt (hopen.mem_nhds hz)
  set Λy : (Fin 2 → ℂ) →L[ℂ] ℂ := ∑ k, (y k) • ContinuousLinearMap.proj k with hΛydef
  have hΛy : ∀ b : Fin 2 → ℂ, Λy b = ∑ k, b k * y k := fun b => by
    simp [hΛydef, mul_comm]
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hcomm : ∀ (w : Fin 2 → ℝ) (k : Fin 2 → ℤ),
      Λy.comp (homTvec w k) = (homTscal w k).comp Λy := fun w k => by
    refine ContinuousLinearMap.ext fun b => ?_
    simp [homTvec, homTscal, map_smul]
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂) (mΛ := ‖Λy‖ * max C₁ C₂)
    (mΛ' := 2 * Real.pi * ε * ‖y‖) (mL' := 2 * Real.pi * εL * ‖y‖) (κ := 1) (κ' := 1)
    hτ hα le_rfl le_rfl hM hd (by positivity) hσ hσs (T₁ := homTvec w₁) (T₂ := homTvec w₂)
    (T₁' := homTscal w₁) (T₂' := homTscal w₂)
    (norm_homModTvec_le hm₁) (norm_homModTvec_le hm₂) (norm_homModTscal_le hm₁)
    (norm_homModTscal_le hm₂) (norm_homModTscal_sub_le hL) Λy (hcomm w₁) (hcomm w₂)
    R₁.comp_b.1 R₂.comp_b.1 R₁.comp_b.2.1 R₂.comp_b.2.1 hC₁ hC₂
    (fun z hz => (Λy.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₁ z hz).trans (le_max_left _ _)) (norm_nonneg _)))
    (fun z hz => (Λy.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₂ z hz).trans (le_max_right _ _)) (norm_nonneg _))) i
    (fun z hz => by
      rw [homPartial_clm _ (d1 z hz) i, hΛy]
      exact (norm_sum_mul_le_of_sum_norm _ _).trans
        (mul_le_mul_of_nonneg_right (ha₁ z hz i).2.1 hy0))
    (fun z hz => by
      rw [homPartial_clm _ (d2 z hz) i, hΛy]
      exact (norm_sum_mul_le_of_sum_norm _ _).trans
        (mul_le_mul_of_nonneg_right (ha₂ z hz i).2.1 hy0))
    (fun z hz => by
      rw [homPartial_clm_sub _ (d1 z hz) (d2 z hz) i, hΛy]
      have h := (haL z hz i).2.1
      refine (norm_sum_mul_le_of_sum_norm _ _).trans ?_
      calc _ ≤ (2 * Real.pi * (εL * d)) * ‖y‖ := mul_le_mul_of_nonneg_right h hy0
        _ = _ := by ring)
    hθ
  have e2 : ∑ k, (homPartial i (homSolve (homTvec w₁) R₁.b) θ k -
      homPartial i (homSolve (homTvec w₂) R₂.b) θ k) * y k =
      Λy (homPartial i (homSolve (homTvec w₁) R₁.b) θ) -
        Λy (homPartial i (homSolve (homTvec w₂) R₂.b) θ) := by
    rw [hΛy, hΛy, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e2]
  exact this.trans (le_of_eq (by ring))

end lip

end KAM.Wave
