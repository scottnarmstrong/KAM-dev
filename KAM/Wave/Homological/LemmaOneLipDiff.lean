/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneLip
public import KAM.Wave.Homological.LemmaOneBounds
public import KAM.Wave.Homological.SolveImageSub
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Differences of the division operators as operators (`bpW:w4:lemma1`, step *Lipschitz*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

The operator norms of `T_k(ξ) - T_k(ζ)` for the seven families, from `HomMultLip`:
`norm_homTscal_sub_le`, `norm_homTvec_sub_le`, `norm_homTdp_sub_le`, `norm_homTdm_sub_le`,
`norm_homTP_sub_le`, `norm_homTP'_sub_le`, `norm_homTQ_sub_le`, `norm_homTQt_sub_le`
(each `≤ κ · homLipC`, `κ = 1` or `K_S`, the form required by `homSolve_sub_le`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

theorem kamEntry_sub' (A B : HomOp) (i j : ℕ+) :
    kamEntry (A - B) i j = kamEntry A i j - kamEntry B i j := by simp [kamEntry]

variable {τ α M d : ℝ} {w₁ w₂ : Fin 2 → ℝ} {W₁ W₂ : ℕ+ → ℝ}

theorem norm_homTscal_sub_le (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (k : Fin 2 → ℤ) :
    ‖homTscal w₁ k - homTscal w₂ k‖ ≤ 2 * 1 * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  have : homTscal w₁ k - homTscal w₂ k =
      (homMultA0 w₁ k - homMultA0 w₂ k) • ContinuousLinearMap.id ℂ ℂ := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [homTscal, sub_mul]
  rw [this]
  refine ((norm_smul _ _).le.trans (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
    (norm_nonneg _))).trans ?_
  have := hL.a0 k
  unfold homLipC at this
  linarith

theorem norm_homTvec_sub_le (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (k : Fin 2 → ℤ) :
    ‖homTvec w₁ k - homTvec w₂ k‖ ≤ 2 * 1 * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  have : homTvec w₁ k - homTvec w₂ k =
      (homMultA0 w₁ k - homMultA0 w₂ k) • ContinuousLinearMap.id ℂ (Fin 2 → ℂ) := by
    refine ContinuousLinearMap.ext fun v => ?_
    ext j
    simp [homTvec, sub_mul]
  rw [this]
  refine ((norm_smul _ _).le.trans (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
    (norm_nonneg _))).trans ?_
  have := hL.a0 k
  unfold homLipC at this
  linarith

variable {w₁' : Fin 2 → ℝ}

theorem norm_homTdp_sub_le (hm₁ : HomMultBounds τ α w₁ W₁) (hm₂ : HomMultBounds τ α w₂ W₂)
    (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (k : Fin 2 → ℤ) :
    ‖homTdp hm₁ k - homTdp hm₂ k‖ ≤ 2 * 1 * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  have hb : ∀ j, ‖homMultDp w₁ W₁ k j - homMultDp w₂ W₂ k j‖ ≤ homLipC τ α M d k :=
    fun j => hL.dp k j
  have : homTdp hm₁ k - homTdp hm₂ k =
      weightedDiagCLM (fun j => homMultDp w₁ W₁ k j - homMultDp w₂ W₂ k j) hb := by
    refine ContinuousLinearMap.ext fun v => ?_
    ext j
    simp [homTdp, weightedDiagCLM_apply, sub_mul]
  rw [this]
  refine (norm_diagCLM_le _ hb).trans ?_
  unfold homLipC; linarith

theorem norm_homTdm_sub_le (hm₁ : HomMultBounds τ α w₁ W₁) (hm₂ : HomMultBounds τ α w₂ W₂)
    (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (k : Fin 2 → ℤ) :
    ‖homTdm hm₁ k - homTdm hm₂ k‖ ≤ 2 * 1 * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  have hb : ∀ j, ‖homMultDm w₁ W₁ k j - homMultDm w₂ W₂ k j‖ ≤ homLipC τ α M d k :=
    fun j => hL.dm k j
  have : homTdm hm₁ k - homTdm hm₂ k =
      weightedDiagCLM (fun j => homMultDm w₁ W₁ k j - homMultDm w₂ W₂ k j) hb := by
    refine ContinuousLinearMap.ext fun v => ?_
    ext j
    simp [homTdm, weightedDiagCLM_apply, sub_mul]
  rw [this]
  refine (norm_diagCLM_le _ hb).trans ?_
  unfold homLipC; linarith

theorem homHadamardCLM_sub {d₁ d₂ d₃ : ℕ+ → ℕ+ → ℂ} {c₁ c₂ c₃ : ℝ} (h₁ : HomHadamardBound d₁ c₁)
    (h₂ : HomHadamardBound d₂ c₂) (h₃ : HomHadamardBound d₃ c₃)
    (h : ∀ i j, d₃ i j = d₁ i j - d₂ i j) :
    homHadamardCLM h₁ - homHadamardCLM h₂ = homHadamardCLM h₃ := by
  refine ContinuousLinearMap.ext fun A => ?_
  refine homOp_ext_entries fun i j => ?_
  simp only [sub_apply, homHadamardCLM_apply, kamEntry_sub', homHadamard_entry, h i j]
  ring


theorem norm_hadSub_le {d₁ d₂ : ℕ+ → ℕ+ → ℂ} {c₁ c₂ c₃ : ℝ} (h₁ : HomHadamardBound d₁ c₁)
    (h₂ : HomHadamardBound d₂ c₂) (h₃ : HomHadamardBound (fun i j => d₁ i j - d₂ i j) c₃) :
    ‖homHadamardCLM h₁ - homHadamardCLM h₂‖ ≤ c₃ * homKS := by
  rw [homHadamardCLM_sub h₁ h₂ h₃ (fun i j => rfl)]
  exact norm_homHadamardCLM_le h₃

theorem norm_homTP_sub_le (hm₁ : HomMultBounds τ α w₁ W₁) (hm₂ : HomMultBounds τ α w₂ W₂)
    (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (k : Fin 2 → ℤ) :
    ‖homTP hm₁ k - homTP hm₂ k‖ ≤
      2 * homKS * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  refine (norm_hadSub_le (hm₁.P k) (hm₂.P k) (hL.P k)).trans (le_of_eq ?_)
  unfold homLipC; ring

theorem norm_homTP'_sub_le (hm₁ : HomMultBounds τ α w₁ W₁) (hm₂ : HomMultBounds τ α w₂ W₂)
    (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (k : Fin 2 → ℤ) :
    ‖homTP' hm₁ k - homTP' hm₂ k‖ ≤
      2 * homKS * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  refine (norm_hadSub_le (hm₁.P' k) (hm₂.P' k) (hL.P' k)).trans (le_of_eq ?_)
  unfold homLipC; ring

theorem norm_homTQ_sub_le (hm₁ : HomMultBounds τ α w₁ W₁) (hm₂ : HomMultBounds τ α w₂ W₂)
    (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (k : Fin 2 → ℤ) :
    ‖homTQ hm₁ k - homTQ hm₂ k‖ ≤
      2 * homKS * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  refine (norm_hadSub_le (hm₁.Q k) (hm₂.Q k) (hL.Q k)).trans (le_of_eq ?_)
  unfold homLipC; ring

theorem norm_homTQt_sub_le (hm₁ : HomMultBounds τ α w₁ W₁) (hm₂ : HomMultBounds τ α w₂ W₂)
    (hL : HomMultLip τ α M d w₁ W₁ w₂ W₂) (k : Fin 2 → ℤ) :
    ‖homTQt hm₁ k - homTQt hm₂ k‖ ≤
      2 * homKS * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  refine (norm_hadSub_le (hm₁.Qt k) (hm₂.Qt k) (hL.Qt k)).trans (le_of_eq ?_)
  unfold homLipC; ring

end KAM.Wave
