/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ModifiedLip
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The Lipschitz bound with modified divisors (`bpW:w5:w4-modified` (ii))

Off-frontier, source-faithful infrastructure (W5-MODIFIED, blueprint `bpW:w5:w4-modified`); the
dependency graph is still being built.

* `homModLip_dcp`, `homModLip_dcm`, `homModLip_dP`, `homModLip_dP'`: the angle derivatives of the
  components `c^±, P, P'` (W4's route, scale `E^W = B^W_σ(ε^L + 2Mε/α)d/α`);
* `homModLip_dQ`: step `m-act` for differences, scale `E^♮ = B^♮_σ(ε^L + 2Mε/α)d/α`;
* `homModF_sub_compBounds`: the component bounds of `F(ξ) - F(ζ)` at scale `E^♮`
  (`E^W ≤ E^♮` since `B^W_σ ≤ B^♮_σ`, step `m-ass`);
* `homModLemma_lipschitz`: **`|X_{F(ξ)} - X_{F(ζ)}|_{p₊,r} ≤ (C₁B^♮_σ/α)(ε^L + 2Mε/α)|ξ-ζ|`** on
  `D(s-σ,r)` when `2β ≤ p+1-p₊`, from the source premises.
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

theorem homModLip_dcp (R₁ R₂ : HomTaylor_gen a p pb s) (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂) (i : Fin 2) :
    homDualNorm_gen ha (homPP hp hpb) (homPartial i (homSolve (homModTdp hm₁) R₁.cp) θ -
        homPartial i (homSolve (homModTdp hm₂) R₂.cp) θ) ≤
      2 * Real.sqrt 2 * Real.pi * r * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX₁
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i =>
    homComp_angle_gen ha hp hpb hr (R₁.homSub R₂) hXL hz i
  obtain ⟨C₁, hC₁⟩ := R₁.comp_cp.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_cp.2.2
  have hopen := isOpen_complexStrip 2 s
  have d1 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₁.cp z := fun z hz =>
    R₁.comp_cp.1.differentiableAt (hopen.mem_nhds hz)
  have d2 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₂.cp z := fun z hz =>
    R₂.comp_cp.1.differentiableAt (hopen.mem_nhds hz)
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂)
    (mΛ := ‖homLamDiag_gen ha (homPP hp hpb)‖ * max C₁ C₂)
    (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε) (mL' := 2 * Real.sqrt 2 * Real.pi * r * εL)
    (κ := 1) (κ' := 1)
    hτ hα le_rfl le_rfl hM hd (by positivity) hσ hσs (T₁ := homModTdp hm₁) (T₂ := homModTdp hm₂)
    (T₁' := homModTdp hm₁) (T₂' := homModTdp hm₂)
    (norm_homModTdp_le hm₁) (norm_homModTdp_le hm₂) (norm_homModTdp_le hm₁)
    (norm_homModTdp_le hm₂) (norm_homModTdp_sub_le hm₁ hm₂ hL) (homLamDiag_gen ha (homPP hp hpb))
    (homLamDiag_comm_homModTdp ha hp hpb hm₁) (homLamDiag_comm_homModTdp ha hp hpb hm₂)
    R₁.comp_cp.1 R₂.comp_cp.1 R₁.comp_cp.2.1 R₂.comp_cp.2.1 hC₁ hC₂
    (fun z hz => ((homLamDiag_gen ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₁ z hz).trans (le_max_left _ _)) (norm_nonneg _)))
    (fun z hz => ((homLamDiag_gen ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₂ z hz).trans (le_max_right _ _)) (norm_nonneg _))) i
    (fun z hz => by rw [homPartial_clm _ (d1 z hz) i]; exact (ha₁ z hz i).2.2.1)
    (fun z hz => by rw [homPartial_clm _ (d2 z hz) i]; exact (ha₂ z hz i).2.2.1)
    (fun z hz => by
      rw [homPartial_clm_sub _ (d1 z hz) (d2 z hz) i]
      have h := (haL z hz i).2.2.1
      calc _ ≤ _ := h
        _ = _ := by ring) hθ
  unfold homDualNorm_gen
  rw [map_sub]
  exact this.trans (le_of_eq (by ring))

theorem homModLip_dcm (R₁ R₂ : HomTaylor_gen a p pb s) (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂) (i : Fin 2) :
    homDualNorm_gen ha (homPP hp hpb) (homPartial i (homSolve (homModTdm hm₁) R₁.cm) θ -
        homPartial i (homSolve (homModTdm hm₂) R₂.cm) θ) ≤
      2 * Real.sqrt 2 * Real.pi * r * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX₁
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i =>
    homComp_angle_gen ha hp hpb hr (R₁.homSub R₂) hXL hz i
  obtain ⟨C₁, hC₁⟩ := R₁.comp_cm.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_cm.2.2
  have hopen := isOpen_complexStrip 2 s
  have d1 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₁.cm z := fun z hz =>
    R₁.comp_cm.1.differentiableAt (hopen.mem_nhds hz)
  have d2 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₂.cm z := fun z hz =>
    R₂.comp_cm.1.differentiableAt (hopen.mem_nhds hz)
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂)
    (mΛ := ‖homLamDiag_gen ha (homPP hp hpb)‖ * max C₁ C₂)
    (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε) (mL' := 2 * Real.sqrt 2 * Real.pi * r * εL)
    (κ := 1) (κ' := 1)
    hτ hα le_rfl le_rfl hM hd (by positivity) hσ hσs (T₁ := homModTdm hm₁) (T₂ := homModTdm hm₂)
    (T₁' := homModTdm hm₁) (T₂' := homModTdm hm₂)
    (norm_homModTdm_le hm₁) (norm_homModTdm_le hm₂) (norm_homModTdm_le hm₁)
    (norm_homModTdm_le hm₂) (norm_homModTdm_sub_le hm₁ hm₂ hL) (homLamDiag_gen ha (homPP hp hpb))
    (homLamDiag_comm_homModTdm ha hp hpb hm₁) (homLamDiag_comm_homModTdm ha hp hpb hm₂)
    R₁.comp_cm.1 R₂.comp_cm.1 R₁.comp_cm.2.1 R₂.comp_cm.2.1 hC₁ hC₂
    (fun z hz => ((homLamDiag_gen ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₁ z hz).trans (le_max_left _ _)) (norm_nonneg _)))
    (fun z hz => ((homLamDiag_gen ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₂ z hz).trans (le_max_right _ _)) (norm_nonneg _))) i
    (fun z hz => by rw [homPartial_clm _ (d1 z hz) i]; exact (ha₁ z hz i).2.2.2.1)
    (fun z hz => by rw [homPartial_clm _ (d2 z hz) i]; exact (ha₂ z hz i).2.2.2.1)
    (fun z hz => by
      rw [homPartial_clm_sub _ (d1 z hz) (d2 z hz) i]
      have h := (haL z hz i).2.2.2.1
      calc _ ≤ _ := h
        _ = _ := by ring) hθ
  unfold homDualNorm_gen
  rw [map_sub]
  exact this.trans (le_of_eq (by ring))

theorem homModLip_dP (R₁ R₂ : HomTaylor_gen a p pb s) (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂) (i : Fin 2) :
    ‖homLamCLM_gen ha (homPP hp hpb) (homPartial i (homSolve (homModTP hm₁) R₁.P) θ -
        homPartial i (homSolve (homModTP hm₂) R₂.P) θ)‖ ≤
      homKS * (4 * Real.pi * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d)) := by
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX₁
  have hK1 := one_le_homKS
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i =>
    homComp_angle_gen ha hp hpb hr (R₁.homSub R₂) hXL hz i
  obtain ⟨C₁, hC₁⟩ := R₁.comp_P.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_P.2.2
  have hopen := isOpen_complexStrip 2 s
  have d1 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₁.P z := fun z hz =>
    R₁.comp_P.1.differentiableAt (hopen.mem_nhds hz)
  have d2 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₂.P z := fun z hz =>
    R₂.comp_P.1.differentiableAt (hopen.mem_nhds hz)
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂)
    (mΛ := ‖homLamCLM_gen ha (homPP hp hpb)‖ * max C₁ C₂)
    (mΛ' := 4 * Real.pi * ε) (mL' := 4 * Real.pi * εL) (κ := homKS) (κ' := homKS)
    hτ hα one_le_homKS one_le_homKS hM hd (by positivity) hσ hσs (T₁ := homModTP hm₁)
    (T₂ := homModTP hm₂) (T₁' := homModTP hm₁) (T₂' := homModTP hm₂)
    (norm_homModTP_le hm₁) (norm_homModTP_le hm₂) (norm_homModTP_le hm₁) (norm_homModTP_le hm₂)
    (norm_homModTP_sub_le hm₁ hm₂ hL) (homLamCLM_gen ha (homPP hp hpb))
    (fun k => homLam_comm_hadamard_gen ha hp hpb (hm₁.P k))
    (fun k => homLam_comm_hadamard_gen ha hp hpb (hm₂.P k))
    R₁.comp_P.1 R₂.comp_P.1 R₁.comp_P.2.1 R₂.comp_P.2.1 hC₁ hC₂
    (fun z hz => ((homLamCLM_gen ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₁ z hz).trans (le_max_left _ _)) (norm_nonneg _)))
    (fun z hz => ((homLamCLM_gen ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₂ z hz).trans (le_max_right _ _)) (norm_nonneg _))) i
    (fun z hz => by rw [homPartial_clm _ (d1 z hz) i]; exact (ha₁ z hz i).2.2.2.2.1)
    (fun z hz => by rw [homPartial_clm _ (d2 z hz) i]; exact (ha₂ z hz i).2.2.2.2.1)
    (fun z hz => by
      rw [homPartial_clm_sub _ (d1 z hz) (d2 z hz) i]
      have h := (haL z hz i).2.2.2.2.1
      calc _ ≤ _ := h
        _ = _ := by ring) hθ
  rw [map_sub]
  exact this.trans (le_of_eq (by ring))

theorem homModLip_dP' (R₁ R₂ : HomTaylor_gen a p pb s) (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂) (i : Fin 2) :
    ‖homLamCLM_gen ha (homPP hp hpb) (homPartial i (homSolve (homModTP' hm₁) R₁.P') θ -
        homPartial i (homSolve (homModTP' hm₂) R₂.P') θ)‖ ≤
      homKS * (4 * Real.pi * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d)) := by
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX₁
  have hK1 := one_le_homKS
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i =>
    homComp_angle_gen ha hp hpb hr (R₁.homSub R₂) hXL hz i
  obtain ⟨C₁, hC₁⟩ := R₁.comp_P'.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_P'.2.2
  have hopen := isOpen_complexStrip 2 s
  have d1 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₁.P' z := fun z hz =>
    R₁.comp_P'.1.differentiableAt (hopen.mem_nhds hz)
  have d2 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₂.P' z := fun z hz =>
    R₂.comp_P'.1.differentiableAt (hopen.mem_nhds hz)
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂)
    (mΛ := ‖homLamCLM_gen ha (homPP hp hpb)‖ * max C₁ C₂)
    (mΛ' := 4 * Real.pi * ε) (mL' := 4 * Real.pi * εL) (κ := homKS) (κ' := homKS)
    hτ hα one_le_homKS one_le_homKS hM hd (by positivity) hσ hσs (T₁ := homModTP' hm₁)
    (T₂ := homModTP' hm₂) (T₁' := homModTP' hm₁) (T₂' := homModTP' hm₂)
    (norm_homModTP'_le hm₁) (norm_homModTP'_le hm₂) (norm_homModTP'_le hm₁)
    (norm_homModTP'_le hm₂) (norm_homModTP'_sub_le hm₁ hm₂ hL) (homLamCLM_gen ha (homPP hp hpb))
    (fun k => homLam_comm_hadamard_gen ha hp hpb (hm₁.P' k))
    (fun k => homLam_comm_hadamard_gen ha hp hpb (hm₂.P' k))
    R₁.comp_P'.1 R₂.comp_P'.1 R₁.comp_P'.2.1 R₂.comp_P'.2.1 hC₁ hC₂
    (fun z hz => ((homLamCLM_gen ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₁ z hz).trans (le_max_left _ _)) (norm_nonneg _)))
    (fun z hz => ((homLamCLM_gen ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₂ z hz).trans (le_max_right _ _)) (norm_nonneg _))) i
    (fun z hz => by rw [homPartial_clm _ (d1 z hz) i]; exact (ha₁ z hz i).2.2.2.2.2.1)
    (fun z hz => by rw [homPartial_clm _ (d2 z hz) i]; exact (ha₂ z hz i).2.2.2.2.2.1)
    (fun z hz => by
      rw [homPartial_clm_sub _ (d1 z hz) (d2 z hz) i]
      have h := (haL z hz i).2.2.2.2.2.1
      calc _ ≤ _ := h
        _ = _ := by ring) hθ
  rw [map_sub]
  exact this.trans (le_of_eq (by ring))

/-- **Step `m-act`, differences**: `‖Λ ∂_{θ_i}(Q_{F(ξ)} - Q_{F(ζ)})‖ ≤ 16πK_S E^♮`. -/
theorem homModLip_dQ (R₁ R₂ : HomTaylor_gen a p (p + 1) s)
    (hX₁ : HomFieldBound_gen ha hp (by linarith : p ≤ p + 1) r ε R₁)
    (hXL : HomFieldBound_gen ha hp (by linarith : p ≤ p + 1) r (εL * d) (R₁.homSub R₂))
    (hX₂ : HomFieldBound_gen ha hp (by linarith : p ≤ p + 1) r ε R₂) (i : Fin 2) :
    ‖homLamCLM_gen ha (homPP hp hpb) (homPartial i (homSolve (homModTQ hm₁) R₁.Q) θ -
        homPartial i (homSolve (homModTQ hm₂) R₂.Q) θ)‖ ≤
      homKS * (16 * Real.pi * (waveBN τ σ / α * (εL + 2 * M * ε / α) * d)) := by
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX₁
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp (by linarith : p ≤ p + 1) hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp (by linarith : p ≤ p + 1) hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp (by linarith : p ≤ p + 1) hr (R₁.homSub R₂) hXL hz
  have h1 := norm_homPartial_homSolve_sub_le (m := ε) (mL := εL) hτ hα one_le_homKS hM hd hσ hσs
    (norm_homModTQ_le hm₁) (norm_homModTQ_le hm₂) (norm_homModTQ_sub_le hm₁ hm₂ hL)
    R₁.comp_Q.1 R₂.comp_Q.1 R₁.comp_Q.2.1 R₂.comp_Q.2.1
    (fun z hz => (hf₁ z hz).2.2.2.2.1) (fun z hz => (hf₂ z hz).2.2.2.2.1)
    (fun z hz => by
      have h := (hfL z hz).2.2.2.2.1
      show ‖R₁.Q z - R₂.Q z‖ ≤ _
      calc _ ≤ _ := h
        _ = _ := by ring) hεL i hθ
  refine (norm_homLamCLM_apply_le_gen ha (homPP hp hpb) _).trans (h1.trans ?_)
  have hB : 0 ≤ waveBN τ σ := (waveBW_nonneg τ σ).trans (waveBW_le_waveBN hτ hσ)
  have hK1 := one_le_homKS
  have hπ := Real.pi_pos
  have hX : 0 ≤ homKS * (waveBN τ σ / α * (εL + 2 * M * ε / α) * d) := by positivity
  calc 2 * Real.pi * homKS * waveBN τ σ / α * (εL + 2 * M * ε / α) * d
      = 2 * Real.pi * (homKS * (waveBN τ σ / α * (εL + 2 * M * ε / α) * d)) := by ring
    _ ≤ 16 * Real.pi * (homKS * (waveBN τ σ / α * (εL + 2 * M * ε / α) * d)) := by nlinarith
    _ = _ := by ring

end lip

/-- Monotonicity of the component bounds in the scale `E₀`. -/
theorem HomCompBounds_gen.mono_scale {a p pb s : ℝ} {ha : 0 ≤ a} {hp : 0 ≤ p} {hpb : p ≤ pb}
    {r K E0 E0' : ℝ} {T : HomTaylor_gen a p pb s} {θ : Fin 2 → ℂ} (hr : 0 < r) (hK : 0 ≤ K)
    (h : HomCompBounds_gen ha hp hpb r K E0 T θ) (hE : E0 ≤ E0') :
    HomCompBounds_gen ha hp hpb r K E0' T θ := by
  have hπ := Real.pi_pos
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨h.b.trans (by gcongr), h.cp.trans (by gcongr), h.cm.trans (by gcongr),
    h.P.trans (by gcongr), h.Q.trans (by gcongr), h.Qt.trans (by gcongr), h.P'.trans (by gcongr),
    fun i => (h.da i).trans (by gcongr), fun i y => (h.db i y).trans (by gcongr),
    fun i => (h.dcp i).trans (by gcongr), fun i => (h.dcm i).trans (by gcongr),
    fun i => (h.dP i).trans (by gcongr), fun i => (h.dP' i).trans (by gcongr),
    fun i => (h.dQ i).trans (by gcongr)⟩

end KAM.Wave
