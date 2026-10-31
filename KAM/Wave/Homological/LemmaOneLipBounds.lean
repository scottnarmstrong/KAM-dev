/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneLipDiff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Lipschitz bounds for the components of `F` (`bpW:w4:lemma1` (iii), step *Lipschitz*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

`homF_sub_compBounds`: the difference `F(ξ) - F(ζ)` of the solutions for the data `R₁ = R(ξ)`,
`R₂ = R(ζ)` satisfies `HomCompBounds` on `T_{s-σ}` with the scale
`E₀' = B^W_σ(ε^L + 2Mε/α)d/α` and `K = K_S` (`d = |ξ-ζ|`), by `bpW:w4:solve` (ii) in the image
spaces and `bpW:w4:components` for `R₁`, `R₂` and `R₁ - R₂`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

theorem homSolveTaylor_Q {a p pb s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ} (hτ : 0 ≤ τ)
    (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hm : HomMultBounds τ α w W) (R : HomTaylor a p pb s) :
    (homSolveTaylor hτ hα hσ hσs hm R).Q = homSolve (homTQ hm) R.Q := rfl

theorem homLam_comm_homTP {a p pb τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p)
    (hpb
    : p ≤ pb)
    (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    (homLamCLM ha (homPP hp hpb)).comp (homTP hm k) = (homTP hm k).comp (homLamCLM ha (homPP hp
        hpb)) :=
  homLam_comm_hadamard ha hp hpb (hm.P k)

theorem homLam_comm_homTP' {a p pb τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p)
    (hpb : p ≤ pb)
    (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    (homLamCLM ha (homPP hp hpb)).comp (homTP' hm k) = (homTP' hm k).comp (homLamCLM ha (homPP hp
        hpb)) :=
  homLam_comm_hadamard ha hp hpb (hm.P' k)

theorem homLam_comm_homTQ {a p pb τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p)
    (hpb
    : p ≤ pb)
    (hm : HomMultBounds τ α w W) (k : Fin 2 → ℤ) :
    (homLamCLM ha (homPP hp hpb)).comp (homTQ hm k) = (homTQ hm k).comp (homLamCLM ha (homPP hp
        hpb)) :=
  homLam_comm_hadamard ha hp hpb (hm.Q k)

theorem homPartial_sub_comp {s σ : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : (Fin 2 → ℂ) → E} (hf : IsHomComp (s - σ) f) (hg : IsHomComp (s - σ) g)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) (i : Fin 2) :
    homPartial i (fun z => f z - g z) θ = homPartial i f θ - homPartial i g θ :=
  homPartial_sub (hf.1.differentiableAt ((isOpen_complexStrip 2 _).mem_nhds hθ))
    (hg.1.differentiableAt ((isOpen_complexStrip 2 _).mem_nhds hθ)) i


theorem homPartial_clm_sub {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (Λ : E →L[ℂ] G) {u v : (Fin 2 → ℂ) → E}
    {z : Fin 2 → ℂ} (hu : DifferentiableAt ℂ u z) (hv : DifferentiableAt ℂ v z) (i : Fin 2) :
    homPartial i (fun z => Λ (u z)) z - homPartial i (fun z => Λ (v z)) z =
      Λ (homPartial i (fun z => u z - v z) z) := by
  rw [homPartial_clm Λ hu i, homPartial_clm Λ hv i, homPartial_sub hu hv i, map_sub]

section lip

variable {a p pb s σ τ α M d : ℝ} {w₁ w₂ : Fin 2 → ℝ} {W₁ W₂ : ℕ+ → ℝ}
  (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε εL : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hM
      : 0 ≤ M)
  (hd : 0 ≤ d) (hεL : 0 ≤ εL) (hσ : 0 < σ) (hσs : σ < s)
  (hm₁ : HomMultBounds τ α w₁ W₁) (hm₂ : HomMultBounds τ α w₂ W₂)
  (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (R₁ R₂ : HomTaylor a p pb s)
  (hX₁ : HomFieldBound ha hp hpb r ε R₁) (hX₂ : HomFieldBound ha hp hpb r ε R₂)
  (hXL : HomFieldBound ha hp hpb r (εL * d) (R₁.sub R₂)) {θ : Fin 2 → ℂ}
  (hθ : θ ∈ complexStrip 2 (s - σ))
include ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL hX₁ hX₂ hXL hθ

theorem homLipField_b :
    ‖((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ hσs hm₂ R₂)).b θ‖ ≤ 2 *
        Real.pi * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  obtain ⟨C₁, hC₁⟩ := R₁.comp_b.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_b.2.2
  have := homSolve_sub_le (m := 2 * Real.pi * ε) (mL := 2 * Real.pi * εL) (κ := 1) hτ hα le_rfl
    hM hd hσ hσs (norm_homTvec_le hm₁) (norm_homTvec_le hm₂) (norm_homTvec_sub_le hL)
    R₁.comp_b.1 R₂.comp_b.1 R₁.comp_b.2.1 R₂.comp_b.2.1
    (fun z hz => (hf₁ z hz).1) (fun z hz => (hf₂ z hz).1)
    (fun z hz => by
      have h := (hfL z hz).1
      show ‖R₁.b z - R₂.b z‖ ≤ _
      calc _ ≤ _ := h
        _ = _ := by ring)
    (by positivity) θ hθ
  exact (le_of_eq rfl).trans (this.trans (le_of_eq (by ring)))

theorem homLipField_cp :
    ‖((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ hσs hm₂ R₂)).cp θ‖ ≤ r *
        (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) / Real.sqrt 2 := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  obtain ⟨C₁, hC₁⟩ := R₁.comp_cp.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_cp.2.2
  have := homSolve_sub_le (m := r * ε / Real.sqrt 2) (mL := r * εL / Real.sqrt 2) (κ := 1) hτ hα
      le_rfl
    hM hd hσ hσs (norm_homTdp_le hm₁) (norm_homTdp_le hm₂) (norm_homTdp_sub_le hm₁ hm₂ hL)
    R₁.comp_cp.1 R₂.comp_cp.1 R₁.comp_cp.2.1 R₂.comp_cp.2.1
    (fun z hz => (hf₁ z hz).2.1) (fun z hz => (hf₂ z hz).2.1)
    (fun z hz => by
      have h := (hfL z hz).2.1
      show ‖R₁.cp z - R₂.cp z‖ ≤ _
      calc _ ≤ _ := h
        _ = _ := by ring)
    (by positivity) θ hθ
  exact (le_of_eq rfl).trans (this.trans (le_of_eq (by ring)))

theorem homLipField_cm :
    ‖((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ hσs hm₂ R₂)).cm θ‖ ≤ r *
        (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) / Real.sqrt 2 := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  obtain ⟨C₁, hC₁⟩ := R₁.comp_cm.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_cm.2.2
  have := homSolve_sub_le (m := r * ε / Real.sqrt 2) (mL := r * εL / Real.sqrt 2) (κ := 1) hτ hα
      le_rfl
    hM hd hσ hσs (norm_homTdm_le hm₁) (norm_homTdm_le hm₂) (norm_homTdm_sub_le hm₁ hm₂ hL)
    R₁.comp_cm.1 R₂.comp_cm.1 R₁.comp_cm.2.1 R₂.comp_cm.2.1
    (fun z hz => (hf₁ z hz).2.2.1) (fun z hz => (hf₂ z hz).2.2.1)
    (fun z hz => by
      have h := (hfL z hz).2.2.1
      show ‖R₁.cm z - R₂.cm z‖ ≤ _
      calc _ ≤ _ := h
        _ = _ := by ring)
    (by positivity) θ hθ
  exact (le_of_eq rfl).trans (this.trans (le_of_eq (by ring)))

theorem homLipField_P :
    ‖(2 : ℂ) • ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ hσs hm₂ R₂)).P θ‖
        ≤ homKS * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
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
    hM hd hσ hσs (norm_homTP_le hm₁) (norm_homTP_le hm₂) (norm_homTP_sub_le hm₁ hm₂ hL)
    R₁.comp_P.1 R₂.comp_P.1 R₁.comp_P.2.1 R₂.comp_P.2.1 hP₁ hP₂ hPL
    (by positivity) θ hθ
  show ‖(2 : ℂ) • (homSolve (homTP hm₁) R₁.P θ - homSolve (homTP hm₂) R₂.P θ)‖ ≤ _
  rw [norm_smul, h2]
  calc 2 * ‖homSolve (homTP hm₁) R₁.P θ - homSolve (homTP hm₂) R₂.P θ‖
      ≤ 2 * (homKS * waveBW τ σ / α * (εL / 2 + 2 * M * (ε / 2) / α) * d) := by gcongr
    _ = _ := by ring

theorem homLipField_Q :
    ‖((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ hσs hm₂ R₂)).Q θ‖ ≤ homKS *
        (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  obtain ⟨C₁, hC₁⟩ := R₁.comp_Q.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_Q.2.2
  have := homSolve_sub_le (m := ε) (mL := εL) (κ := homKS) hτ hα one_le_homKS
    hM hd hσ hσs (norm_homTQ_le hm₁) (norm_homTQ_le hm₂) (norm_homTQ_sub_le hm₁ hm₂ hL)
    R₁.comp_Q.1 R₂.comp_Q.1 R₁.comp_Q.2.1 R₂.comp_Q.2.1
    (fun z hz => (hf₁ z hz).2.2.2.2.1) (fun z hz => (hf₂ z hz).2.2.2.2.1)
    (fun z hz => by
      have h := (hfL z hz).2.2.2.2.1
      show ‖R₁.Q z - R₂.Q z‖ ≤ _
      calc _ ≤ _ := h
        _ = _ := by ring)
    (by positivity) θ hθ
  exact (le_of_eq rfl).trans (this.trans (le_of_eq (by ring)))

theorem homLipField_Qt :
    ‖((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ hσs hm₂ R₂)).Qt θ‖ ≤ homKS
        * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  obtain ⟨C₁, hC₁⟩ := R₁.comp_Qt.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_Qt.2.2
  have := homSolve_sub_le (m := ε) (mL := εL) (κ := homKS) hτ hα one_le_homKS
    hM hd hσ hσs (norm_homTQt_le hm₁) (norm_homTQt_le hm₂) (norm_homTQt_sub_le hm₁ hm₂ hL)
    R₁.comp_Qt.1 R₂.comp_Qt.1 R₁.comp_Qt.2.1 R₂.comp_Qt.2.1
    (fun z hz => (hf₁ z hz).2.2.2.2.2.1) (fun z hz => (hf₂ z hz).2.2.2.2.2.1)
    (fun z hz => by
      have h := (hfL z hz).2.2.2.2.2.1
      show ‖R₁.Qt z - R₂.Qt z‖ ≤ _
      calc _ ≤ _ := h
        _ = _ := by ring)
    (by positivity) θ hθ
  exact (le_of_eq rfl).trans (this.trans (le_of_eq (by ring)))

theorem homLipField_P' :
    ‖(2 : ℂ) • ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ hσs hm₂ R₂)).P'
        θ‖ ≤ homKS * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
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
    hM hd hσ hσs (norm_homTP'_le hm₁) (norm_homTP'_le hm₂) (norm_homTP'_sub_le hm₁ hm₂ hL)
    R₁.comp_P'.1 R₂.comp_P'.1 R₁.comp_P'.2.1 R₂.comp_P'.2.1 hP₁ hP₂ hPL
    (by positivity) θ hθ
  show ‖(2 : ℂ) • (homSolve (homTP' hm₁) R₁.P' θ - homSolve (homTP' hm₂) R₂.P' θ)‖ ≤ _
  rw [norm_smul, h2]
  calc 2 * ‖homSolve (homTP' hm₁) R₁.P' θ - homSolve (homTP' hm₂) R₂.P' θ‖
      ≤ 2 * (homKS * waveBW τ σ / α * (εL / 2 + 2 * M * (ε / 2) / α) * d) := by gcongr
    _ = _ := by ring

theorem homLipField_dcp (i : Fin 2) :
    homDualNorm ha (homPP hp hpb) (homPartial i ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub
        (homSolveTaylor hτ hα
        hσ hσs hm₂ R₂)).cp θ) ≤ 2 * Real.sqrt 2 * Real.pi * r * (waveBW τ σ / α * (εL + 2 * M * ε /
        α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  obtain ⟨C₁, hC₁⟩ := R₁.comp_cp.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_cp.2.2
  have hopen := isOpen_complexStrip 2 s
  have d1 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₁.cp z := fun z hz =>
    R₁.comp_cp.1.differentiableAt (hopen.mem_nhds hz)
  have d2 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₂.cp z := fun z hz =>
    R₂.comp_cp.1.differentiableAt (hopen.mem_nhds hz)
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂) (mΛ := ‖homLamDiag ha (homPP hp
      hpb)‖ * max C₁
      C₂)
    (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε) (mL' := 2 * Real.sqrt 2 * Real.pi * r * εL) (κ := 1)
        (κ' := 1)
    hτ hα le_rfl le_rfl hM hd (by positivity) hσ hσs (T₁ := homTdp hm₁) (T₂ := homTdp hm₂)
    (T₁' := homTdp hm₁) (T₂' := homTdp hm₂)
    (norm_homTdp_le hm₁) (norm_homTdp_le hm₂) (norm_homTdp_le hm₁) (norm_homTdp_le hm₂)
    (norm_homTdp_sub_le hm₁ hm₂ hL) (homLamDiag ha (homPP hp hpb))
    (homLamDiag_comm_homTdp ha hp hpb hm₁) (homLamDiag_comm_homTdp ha hp hpb hm₂)
    R₁.comp_cp.1 R₂.comp_cp.1 R₁.comp_cp.2.1 R₂.comp_cp.2.1 hC₁ hC₂
    (fun z hz => ((homLamDiag ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₁ z hz).trans (le_max_left _ _)) (norm_nonneg _)))
    (fun z hz => ((homLamDiag ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₂ z hz).trans (le_max_right _ _)) (norm_nonneg _))) i
    (fun z hz => by rw [homPartial_clm _ (d1 z hz) i]; exact (ha₁ z hz i).2.2.1)
    (fun z hz => by rw [homPartial_clm _ (d2 z hz) i]; exact (ha₂ z hz i).2.2.1)
    (fun z hz => by
      rw [homPartial_clm_sub _ (d1 z hz) (d2 z hz) i]
      have h := (haL z hz i).2.2.1
      calc _ ≤ _ := h
        _ = _ := by ring) hθ
  have e := homPartial_sub_comp (s := s) (σ := σ)
    (homSolveTaylor hτ hα hσ hσs hm₁ R₁).comp_cp (homSolveTaylor hτ hα hσ hσs hm₂ R₂).comp_cp hθ i
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · show ‖homLamDiag ha (homPP hp hpb) (homPartial i (fun z => (homSolveTaylor hτ hα hσ hσs hm₁
      R₁).cp z -
      (homSolveTaylor hτ hα hσ hσs hm₂ R₂).cp z) θ)‖ = _
    rw [e, map_sub]
    rfl
  · ring

theorem homLipField_dcm (i : Fin 2) :
    homDualNorm ha (homPP hp hpb) (homPartial i ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub
        (homSolveTaylor hτ hα
        hσ hσs hm₂ R₂)).cm θ) ≤ 2 * Real.sqrt 2 * Real.pi * r * (waveBW τ σ / α * (εL + 2 * M * ε /
        α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  obtain ⟨C₁, hC₁⟩ := R₁.comp_cm.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_cm.2.2
  have hopen := isOpen_complexStrip 2 s
  have d1 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₁.cm z := fun z hz =>
    R₁.comp_cm.1.differentiableAt (hopen.mem_nhds hz)
  have d2 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₂.cm z := fun z hz =>
    R₂.comp_cm.1.differentiableAt (hopen.mem_nhds hz)
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂) (mΛ := ‖homLamDiag ha (homPP hp
      hpb)‖ * max C₁
      C₂)
    (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε) (mL' := 2 * Real.sqrt 2 * Real.pi * r * εL) (κ := 1)
        (κ' := 1)
    hτ hα le_rfl le_rfl hM hd (by positivity) hσ hσs (T₁ := homTdm hm₁) (T₂ := homTdm hm₂)
    (T₁' := homTdm hm₁) (T₂' := homTdm hm₂)
    (norm_homTdm_le hm₁) (norm_homTdm_le hm₂) (norm_homTdm_le hm₁) (norm_homTdm_le hm₂)
    (norm_homTdm_sub_le hm₁ hm₂ hL) (homLamDiag ha (homPP hp hpb))
    (homLamDiag_comm_homTdm ha hp hpb hm₁) (homLamDiag_comm_homTdm ha hp hpb hm₂)
    R₁.comp_cm.1 R₂.comp_cm.1 R₁.comp_cm.2.1 R₂.comp_cm.2.1 hC₁ hC₂
    (fun z hz => ((homLamDiag ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₁ z hz).trans (le_max_left _ _)) (norm_nonneg _)))
    (fun z hz => ((homLamDiag ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₂ z hz).trans (le_max_right _ _)) (norm_nonneg _))) i
    (fun z hz => by rw [homPartial_clm _ (d1 z hz) i]; exact (ha₁ z hz i).2.2.2.1)
    (fun z hz => by rw [homPartial_clm _ (d2 z hz) i]; exact (ha₂ z hz i).2.2.2.1)
    (fun z hz => by
      rw [homPartial_clm_sub _ (d1 z hz) (d2 z hz) i]
      have h := (haL z hz i).2.2.2.1
      calc _ ≤ _ := h
        _ = _ := by ring) hθ
  have e := homPartial_sub_comp (s := s) (σ := σ)
    (homSolveTaylor hτ hα hσ hσs hm₁ R₁).comp_cm (homSolveTaylor hτ hα hσ hσs hm₂ R₂).comp_cm hθ i
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · show ‖homLamDiag ha (homPP hp hpb) (homPartial i (fun z => (homSolveTaylor hτ hα hσ hσs hm₁
      R₁).cm z -
      (homSolveTaylor hτ hα hσ hσs hm₂ R₂).cm z) θ)‖ = _
    rw [e, map_sub]
    rfl
  · ring

theorem homLipField_dP (i : Fin 2) :
    ‖homLamCLM ha (homPP hp hpb) (homPartial i ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub
        (homSolveTaylor hτ hα
        hσ hσs hm₂ R₂)).P θ)‖ ≤ homKS * (4 * Real.pi * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d))
        := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  obtain ⟨C₁, hC₁⟩ := R₁.comp_P.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_P.2.2
  have hopen := isOpen_complexStrip 2 s
  have d1 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₁.P z := fun z hz =>
    R₁.comp_P.1.differentiableAt (hopen.mem_nhds hz)
  have d2 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₂.P z := fun z hz =>
    R₂.comp_P.1.differentiableAt (hopen.mem_nhds hz)
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂) (mΛ := ‖homLamCLM ha (homPP hp
      hpb)‖ * max C₁
      C₂)
    (mΛ' := 4 * Real.pi * ε) (mL' := 4 * Real.pi * εL) (κ := homKS) (κ' := homKS)
    hτ hα one_le_homKS one_le_homKS hM hd (by positivity) hσ hσs (T₁ := homTP hm₁) (T₂ := homTP hm₂)
    (T₁' := homTP hm₁) (T₂' := homTP hm₂)
    (norm_homTP_le hm₁) (norm_homTP_le hm₂) (norm_homTP_le hm₁) (norm_homTP_le hm₂)
    (norm_homTP_sub_le hm₁ hm₂ hL) (homLamCLM ha (homPP hp hpb))
    (homLam_comm_homTP ha hp hpb hm₁) (homLam_comm_homTP ha hp hpb hm₂)
    R₁.comp_P.1 R₂.comp_P.1 R₁.comp_P.2.1 R₂.comp_P.2.1 hC₁ hC₂
    (fun z hz => ((homLamCLM ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₁ z hz).trans (le_max_left _ _)) (norm_nonneg _)))
    (fun z hz => ((homLamCLM ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₂ z hz).trans (le_max_right _ _)) (norm_nonneg _))) i
    (fun z hz => by rw [homPartial_clm _ (d1 z hz) i]; exact (ha₁ z hz i).2.2.2.2.1)
    (fun z hz => by rw [homPartial_clm _ (d2 z hz) i]; exact (ha₂ z hz i).2.2.2.2.1)
    (fun z hz => by
      rw [homPartial_clm_sub _ (d1 z hz) (d2 z hz) i]
      have h := (haL z hz i).2.2.2.2.1
      calc _ ≤ _ := h
        _ = _ := by ring) hθ
  have e := homPartial_sub_comp (s := s) (σ := σ)
    (homSolveTaylor hτ hα hσ hσs hm₁ R₁).comp_P (homSolveTaylor hτ hα hσ hσs hm₂ R₂).comp_P hθ i
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · show ‖homLamCLM ha (homPP hp hpb) (homPartial i (fun z => (homSolveTaylor hτ hα hσ hσs hm₁
      R₁).P z -
      (homSolveTaylor hτ hα hσ hσs hm₂ R₂).P z) θ)‖ = _
    rw [e, map_sub]
    rfl
  · ring

theorem homLipField_dP' (i : Fin 2) :
    ‖homLamCLM ha (homPP hp hpb) (homPartial i ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub
        (homSolveTaylor hτ hα
        hσ hσs hm₂ R₂)).P' θ)‖ ≤ homKS * (4 * Real.pi * (waveBW τ σ / α * (εL + 2 * M * ε / α) *
        d)) := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  obtain ⟨C₁, hC₁⟩ := R₁.comp_P'.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_P'.2.2
  have hopen := isOpen_complexStrip 2 s
  have d1 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₁.P' z := fun z hz =>
    R₁.comp_P'.1.differentiableAt (hopen.mem_nhds hz)
  have d2 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₂.P' z := fun z hz =>
    R₂.comp_P'.1.differentiableAt (hopen.mem_nhds hz)
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂) (mΛ := ‖homLamCLM ha (homPP hp
      hpb)‖ * max C₁
      C₂)
    (mΛ' := 4 * Real.pi * ε) (mL' := 4 * Real.pi * εL) (κ := homKS) (κ' := homKS)
    hτ hα one_le_homKS one_le_homKS hM hd (by positivity) hσ hσs (T₁ := homTP' hm₁) (T₂ := homTP'
        hm₂)
    (T₁' := homTP' hm₁) (T₂' := homTP' hm₂)
    (norm_homTP'_le hm₁) (norm_homTP'_le hm₂) (norm_homTP'_le hm₁) (norm_homTP'_le hm₂)
    (norm_homTP'_sub_le hm₁ hm₂ hL) (homLamCLM ha (homPP hp hpb))
    (homLam_comm_homTP' ha hp hpb hm₁) (homLam_comm_homTP' ha hp hpb hm₂)
    R₁.comp_P'.1 R₂.comp_P'.1 R₁.comp_P'.2.1 R₂.comp_P'.2.1 hC₁ hC₂
    (fun z hz => ((homLamCLM ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₁ z hz).trans (le_max_left _ _)) (norm_nonneg _)))
    (fun z hz => ((homLamCLM ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₂ z hz).trans (le_max_right _ _)) (norm_nonneg _))) i
    (fun z hz => by rw [homPartial_clm _ (d1 z hz) i]; exact (ha₁ z hz i).2.2.2.2.2.1)
    (fun z hz => by rw [homPartial_clm _ (d2 z hz) i]; exact (ha₂ z hz i).2.2.2.2.2.1)
    (fun z hz => by
      rw [homPartial_clm_sub _ (d1 z hz) (d2 z hz) i]
      have h := (haL z hz i).2.2.2.2.2.1
      calc _ ≤ _ := h
        _ = _ := by ring) hθ
  have e := homPartial_sub_comp (s := s) (σ := σ)
    (homSolveTaylor hτ hα hσ hσs hm₁ R₁).comp_P' (homSolveTaylor hτ hα hσ hσs hm₂ R₂).comp_P' hθ i
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · show ‖homLamCLM ha (homPP hp hpb) (homPartial i (fun z => (homSolveTaylor hτ hα hσ hσs hm₁
      R₁).P' z -
      (homSolveTaylor hτ hα hσ hσs hm₂ R₂).P' z) θ)‖ = _
    rw [e, map_sub]
    rfl
  · ring

theorem homLipField_dQ (i : Fin 2) :
    ‖homLamCLM ha (homPP hp hpb) (homPartial i ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub
        (homSolveTaylor hτ hα
        hσ hσs hm₂ R₂)).Q θ)‖ ≤ homKS * (16 * Real.pi * (waveBW τ σ / α * (εL + 2 * M * ε / α) *
        d)) := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  obtain ⟨C₁, hC₁⟩ := R₁.comp_Q.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_Q.2.2
  have hopen := isOpen_complexStrip 2 s
  have d1 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₁.Q z := fun z hz =>
    R₁.comp_Q.1.differentiableAt (hopen.mem_nhds hz)
  have d2 : ∀ z ∈ complexStrip 2 s, DifferentiableAt ℂ R₂.Q z := fun z hz =>
    R₂.comp_Q.1.differentiableAt (hopen.mem_nhds hz)
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂) (mΛ := ‖homLamCLM ha (homPP hp
      hpb)‖ * max C₁
      C₂)
    (mΛ' := 16 * Real.pi * ε) (mL' := 16 * Real.pi * εL) (κ := homKS) (κ' := homKS)
    hτ hα one_le_homKS one_le_homKS hM hd (by positivity) hσ hσs (T₁ := homTQ hm₁) (T₂ := homTQ hm₂)
    (T₁' := homTQ hm₁) (T₂' := homTQ hm₂)
    (norm_homTQ_le hm₁) (norm_homTQ_le hm₂) (norm_homTQ_le hm₁) (norm_homTQ_le hm₂)
    (norm_homTQ_sub_le hm₁ hm₂ hL) (homLamCLM ha (homPP hp hpb))
    (homLam_comm_homTQ ha hp hpb hm₁) (homLam_comm_homTQ ha hp hpb hm₂)
    R₁.comp_Q.1 R₂.comp_Q.1 R₁.comp_Q.2.1 R₂.comp_Q.2.1 hC₁ hC₂
    (fun z hz => ((homLamCLM ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₁ z hz).trans (le_max_left _ _)) (norm_nonneg _)))
    (fun z hz => ((homLamCLM ha (homPP hp hpb)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hC₂ z hz).trans (le_max_right _ _)) (norm_nonneg _))) i
    (fun z hz => by rw [homPartial_clm _ (d1 z hz) i]; exact (ha₁ z hz i).2.2.2.2.2.2)
    (fun z hz => by rw [homPartial_clm _ (d2 z hz) i]; exact (ha₂ z hz i).2.2.2.2.2.2)
    (fun z hz => by
      rw [homPartial_clm_sub _ (d1 z hz) (d2 z hz) i]
      have h := (haL z hz i).2.2.2.2.2.2
      calc _ ≤ _ := h
        _ = _ := by ring) hθ
  have e := homPartial_sub_comp (s := s) (σ := σ)
    (homSolveTaylor hτ hα hσ hσs hm₁ R₁).comp_Q (homSolveTaylor hτ hα hσ hσs hm₂ R₂).comp_Q hθ i
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · show ‖homLamCLM ha (homPP hp hpb) (homPartial i (fun z => (homSolveTaylor hτ hα hσ hσs hm₁
      R₁).Q z -
      (homSolveTaylor hτ hα hσ hσs hm₂ R₂).Q z) θ)‖ = _
    rw [e, map_sub, homSolveTaylor_Q, homSolveTaylor_Q]
  · ring

theorem homLipField_da (i : Fin 2) :
    ‖homPartial i ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ hσs hm₂
        R₂)).a0 θ‖ ≤ 2 * Real.pi * r ^ 2 * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  obtain ⟨C₁, hC₁⟩ := R₁.comp_a0.2.2
  obtain ⟨C₂, hC₂⟩ := R₂.comp_a0.2.2
  have hopen := isOpen_complexStrip 2 s
  have := homSolve_image_partial_sub_bound (m₁ := C₁) (m₂ := C₂) (mΛ := max C₁ C₂)
    (mΛ' := 2 * Real.pi * r ^ 2 * ε) (mL' := 2 * Real.pi * r ^ 2 * εL) (κ := 1) (κ' := 1)
    hτ hα le_rfl le_rfl hM hd (by positivity) hσ hσs (T₁ := homTscal w₁) (T₂ := homTscal w₂)
    (T₁' := homTscal w₁) (T₂' := homTscal w₂)
    (norm_homTscal_le hm₁) (norm_homTscal_le hm₂) (norm_homTscal_le hm₁) (norm_homTscal_le hm₂)
    (norm_homTscal_sub_le hL) (ContinuousLinearMap.id ℂ ℂ) (fun k => by simp) (fun k => by simp)
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
  have e := homPartial_sub_comp (s := s) (σ := σ)
    (homSolveTaylor hτ hα hσ hσs hm₁ R₁).comp_a0 (homSolveTaylor hτ hα hσ hσs hm₂ R₂).comp_a0 hθ i
  show ‖homPartial i (fun z => (homSolveTaylor hτ hα hσ hσs hm₁ R₁).a0 z -
    (homSolveTaylor hτ hα hσ hσs hm₂ R₂).a0 z) θ‖ ≤ _
  rw [e]
  exact this.trans (le_of_eq (by ring))

theorem homLipField_db (i : Fin 2) (y : Fin 2 → ℂ) :
    ‖∑ k, homPartial i ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ hσs hm₂
        R₂)).b θ k * y k‖ ≤ 2 * Real.pi * (waveBW τ σ / α * (εL + 2 * M * ε / α) * d) * ‖y‖ := by
  have hs : 0 < s := hσ.trans hσs
  have hB := waveBW_nonneg τ σ
  have hK1 := one_le_homKS
  have hf₁ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₁ hX₁ hz
  have hf₂ := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R₂ hX₂ hz
  have hfL := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr (R₁.sub R₂) hXL hz
  have ha₁ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₁ hX₁ hz i
  have ha₂ := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr R₂ hX₂ hz i
  have haL := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle ha hp hpb hr (R₁.sub R₂) hXL hz i
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := fun j => by have := hθ j; linarith
    exact (homXnorm_nonneg ha hp hpb hr R₁ θ 0 0 0).trans
      (hX₁ θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
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
    (norm_homTvec_le hm₁) (norm_homTvec_le hm₂) (norm_homTscal_le hm₁) (norm_homTscal_le hm₂)
    (norm_homTscal_sub_le hL) Λy (hcomm w₁) (hcomm w₂)
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
  have e := homPartial_sub_comp (s := s) (σ := σ)
    (homSolveTaylor hτ hα hσ hσs hm₁ R₁).comp_b (homSolveTaylor hτ hα hσ hσs hm₂ R₂).comp_b hθ i
  have e2 : ∑ k, homPartial i ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ
      hσs hm₂ R₂)).b θ k * y k =
      Λy (homPartial i (homSolveTaylor hτ hα hσ hσs hm₁ R₁).b θ) -
        Λy (homPartial i (homSolveTaylor hτ hα hσ hσs hm₂ R₂).b θ) := by
    rw [hΛy, hΛy, ← Finset.sum_sub_distrib]
    show ∑ k, homPartial i (fun z => (homSolveTaylor hτ hα hσ hσs hm₁ R₁).b z -
      (homSolveTaylor hτ hα hσ hσs hm₂ R₂).b z) θ k * y k = _
    rw [e]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [sub_mul]
  rw [e2]
  exact this.trans (le_of_eq (by ring))

/-- **Lipschitz component bounds of `F`** (`bpW:w4:lemma1` (iii), step *Lipschitz*). -/
theorem homF_sub_compBounds :
    HomCompBounds ha hp hpb r homKS (waveBW τ σ / α * (εL + 2 * M * ε / α) * d)
      ((homSolveTaylor hτ hα hσ hσs hm₁ R₁).sub (homSolveTaylor hτ hα hσ hσs hm₂ R₂)) θ :=
  ⟨homLipField_b ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_cp ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_cm ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_P ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_Q ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_Qt ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_P' ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_da ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_db ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_dcp ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_dcm ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_dP ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_dP' ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ,
   homLipField_dQ ha hp hpb hr hτ hα hM hd hεL hσ hσs hm₁ hm₂ hL R₁ R₂ hX₁ hX₂ hXL hθ⟩

end lip

end KAM.Wave
