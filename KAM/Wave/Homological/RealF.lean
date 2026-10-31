/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.RealSolve
public import KAM.Wave.Homological.SolveImage
public import KAM.Wave.Homological.NhatTaylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Reality of `F` and `N̂` (`bpW:w4:lemma1` (i), step *Reality*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

`HomTaylor.IsReal R`: at real `θ`, `a, b` are real, `c^- = \\overline{c^+}`,
`P' = \\overline P`, `Q^T = \\overline Q` (entrywise, in the entries of the represented operators;
    the
weights are real so this is the same on representatives). Theorem `homSolveTaylor_isReal`:
if `R` is real, so is `F = homSolveTaylor … R` (the divisors are real,
`δ⁰_{-k} = -δ⁰_k`, `δ^+_{-k,j} = -δ^-_{k,j}`, `δ^P_{-k} = -δ^{P'}_k`, `δ^Q_{-k,ij} = -δ^Q_{k,ji}`);
`homNhatTaylor_isReal`: so is `N̂` (`\\hat ω ∈ ℝ²`, `\\hat Ω_j ∈ ℝ`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM
open scoped ComplexConjugate

variable {a p pb s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

/-- **Reality** of a Taylor Hamiltonian (`bpW:w4:taylor`), at real `θ`. -/
def HomTaylor.IsReal (R : HomTaylor a p pb s) : Prop :=
  ∀ x : Fin 2 → ℝ, (R.a0 fun j => (x j : ℂ)).im = 0 ∧
    (∀ k, (R.b (fun j => (x j : ℂ)) k).im = 0) ∧
    (∀ j, R.cm (fun j => (x j : ℂ)) j = conj (R.cp (fun j => (x j : ℂ)) j)) ∧
    (∀ i j, homNormalEntry a p pb (R.P' fun j => (x j : ℂ)) i j =
      conj (homNormalEntry a p pb (R.P fun j => (x j : ℂ)) i j)) ∧
    (∀ i j, homNormalEntry a p pb (R.Qt fun j => (x j : ℂ)) i j =
      conj (homNormalEntry a p pb (R.Q fun j => (x j : ℂ)) i j))

theorem homSolveTaylor_isReal (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hm : HomMultBounds τ α w W) (R : HomTaylor a p pb s) (hR : R.IsReal) :
    (homSolveTaylor hτ hα hσ hσs hm R).IsReal := by
  have hs : 0 < s := hσ.trans hσs
  intro x
  set θ : Fin 2 → ℂ := fun j => (x j : ℂ) with hθdef
  have hθs : θ ∈ complexStrip 2 (s - σ) := ofReal_mem_complexStrip (by linarith) x
  have hθs' : θ ∈ complexStrip 2 s := ofReal_mem_complexStrip hs x
  obtain ⟨hra, hrb, hrc, hrp, hrq⟩ := hR x
  have hrealpt : ∀ (y : Fin 2 → ℝ), True := fun _ => trivial
  refine ⟨?_, fun k => ?_, fun j => ?_, fun i j => ?_, fun i j => ?_⟩
  · -- a0
    have h := homSolve_conj_real (u := R.a0) (v := R.a0)
      (fun y => by
        have := (hR y).1
        exact ((Complex.conj_eq_iff_im).mpr this).symm) (homMultA0 w) (homMultA0 w)
      (fun k => (homMultA0_conj w k).symm) x
    have h2 : conj ((homSolveTaylor hτ hα hσ hσs hm R).a0 θ) =
        (homSolveTaylor hτ hα hσ hσs hm R).a0 θ := h
    exact (Complex.conj_eq_iff_im).mp h2
  · -- b
    have e : ∀ z ∈ complexStrip 2 (s - σ), (homSolveTaylor hτ hα hσ hσs hm R).b z k =
        homSolve (fun k' => homMultA0 w k' • ContinuousLinearMap.id ℂ ℂ)
          (fun z => R.b z k) z := fun z hz => by
      have := homSolve_image_eq (T' := fun k' => homMultA0 w k' • ContinuousLinearMap.id ℂ ℂ)
        hτ hα le_rfl hσ hσs (norm_homTvec_le hm) (ContinuousLinearMap.proj k)
        (fun k' => by
          refine ContinuousLinearMap.ext fun v => ?_
          simp [homTvec]) R.comp_b.1 R.comp_b.2.1 R.comp_b.2.2.choose_spec hz
      exact this
    rw [e θ hθs]
    have h := homSolve_conj_real (u := fun z => R.b z k) (v := fun z => R.b z k)
      (fun y => ((Complex.conj_eq_iff_im).mpr ((hR y).2.1 k)).symm) (homMultA0 w) (homMultA0 w)
      (fun k' => (homMultA0_conj w k').symm) x
    exact (Complex.conj_eq_iff_im).mp h
  · -- c
    have ecp : ∀ z ∈ complexStrip 2 (s - σ), (homSolveTaylor hτ hα hσ hσs hm R).cp z j =
        homSolve (fun k => homMultDp w W k j • ContinuousLinearMap.id ℂ ℂ) (fun z => R.cp z j) z :=
      fun z hz => by
        have := homSolve_image_eq (T' := fun k => homMultDp w W k j • ContinuousLinearMap.id ℂ ℂ)
          hτ hα le_rfl hσ hσs (norm_homTdp_le hm) (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j)
          (fun k => by
            refine ContinuousLinearMap.ext fun v => ?_
            simp [homTdp]; rfl) R.comp_cp.1 R.comp_cp.2.1
          R.comp_cp.2.2.choose_spec hz
        exact this
    have ecm : ∀ z ∈ complexStrip 2 (s - σ), (homSolveTaylor hτ hα hσ hσs hm R).cm z j =
        homSolve (fun k => homMultDm w W k j • ContinuousLinearMap.id ℂ ℂ) (fun z => R.cm z j) z :=
      fun z hz => by
        have := homSolve_image_eq (T' := fun k => homMultDm w W k j • ContinuousLinearMap.id ℂ ℂ)
          hτ hα le_rfl hσ hσs (norm_homTdm_le hm) (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j)
          (fun k => by
            refine ContinuousLinearMap.ext fun v => ?_
            simp [homTdm]; rfl) R.comp_cm.1 R.comp_cm.2.1
          R.comp_cm.2.2.choose_spec hz
        exact this
    have h := homSolve_conj_real (u := fun z => R.cp z j) (v := fun z => R.cm z j)
      (fun y => (hR y).2.2.1 j) (fun k => homMultDp w W k j) (fun k => homMultDm w W k j)
      (fun k => (homMultDp_conj w W k j).symm) x
    rw [ecm θ hθs, ecp θ hθs]
    exact h.symm
  · -- P'
    have eP : ∀ z ∈ complexStrip 2 (s - σ), homNormalEntry a p pb
        ((homSolveTaylor hτ hα hσ hσs hm R).P z) i j =
        homSolve (fun k => homDP w W k i j • ContinuousLinearMap.id ℂ ℂ)
          (fun z => homNormalEntry a p pb (R.P z) i j) z := fun z hz =>
      homSolve_hadamard_entry a p pb hτ hα one_le_homKS hσ hσs hm.P (norm_homTP_le hm)
        R.comp_P.1 R.comp_P.2.1 R.comp_P.2.2.choose_spec i j hz
    have eP' : ∀ z ∈ complexStrip 2 (s - σ), homNormalEntry a p pb
        ((homSolveTaylor hτ hα hσ hσs hm R).P' z) i j =
        homSolve (fun k => homDP' w W k i j • ContinuousLinearMap.id ℂ ℂ)
          (fun z => homNormalEntry a p pb (R.P' z) i j) z := fun z hz =>
      homSolve_hadamard_entry a p pb hτ hα one_le_homKS hσ hσs hm.P' (norm_homTP'_le hm)
        R.comp_P'.1 R.comp_P'.2.1 R.comp_P'.2.2.choose_spec i j hz
    have h := homSolve_conj_real (u := fun z => homNormalEntry a p pb (R.P z) i j)
      (v := fun z => homNormalEntry a p pb (R.P' z) i j)
      (fun y => (hR y).2.2.2.1 i j) (fun k => homDP w W k i j) (fun k => homDP' w W k i j)
      (fun k => (homDP_conj w W k i j).symm) x
    rw [eP' θ hθs, eP θ hθs]
    exact h.symm
  · -- Qt
    have eQ : ∀ i j : ℕ+, ∀ z ∈ complexStrip 2 (s - σ), homNormalEntry a p pb
        ((homSolveTaylor hτ hα hσ hσs hm R).Q z) i j =
        homSolve (fun k => homDQ w W k i j • ContinuousLinearMap.id ℂ ℂ)
          (fun z => homNormalEntry a p pb (R.Q z) i j) z := fun i j z hz =>
      homSolve_hadamard_entry a p pb hτ hα one_le_homKS hσ hσs hm.Q (norm_homTQ_le hm)
        R.comp_Q.1 R.comp_Q.2.1 R.comp_Q.2.2.choose_spec i j hz
    have h := homSolve_conj_real (u := fun z => homNormalEntry a p pb (R.Q z) i j)
      (v := fun z => homNormalEntry a p pb (R.Q z) j i)
      (fun y => by
        have h1 := (hR y).2.2.2.2 i j
        rw [R.transQ _ (ofReal_mem_complexStrip hs y) i j] at h1
        exact h1)
      (fun k => homDQ w W k i j) (fun k => homDQ w W k j i)
      (fun k => (homDQ_conj w W k i j).symm) x
    rw [(homSolveTaylor hτ hα hσ hσs hm R).transQ θ hθs i j, eQ j i θ hθs, eQ i j θ hθs]
    exact h.symm


/-- The mean of a function that is real at real points is real. -/
theorem homCoeff_zero_im {s : ℝ} {u : (Fin 2 → ℂ) → ℂ}
    (hu : ∀ x : Fin 2 → ℝ, (u fun j => (x j : ℂ)).im = 0) : (homCoeff u 0).im = 0 := by
  have h := homCoeff_conj (u := u) (v := u)
    (fun x => ((Complex.conj_eq_iff_im).mpr (hu x)).symm) 0
  rw [neg_zero] at h
  exact (Complex.conj_eq_iff_im).mp h.symm

/-- **`N̂` is real** if `R` is (`\hat ω ∈ ℝ²`, `\hat Ω_j ∈ ℝ`). -/
theorem homNhatTaylor_isReal (hs : 0 < s) (R : HomTaylor a p pb s) (hR : R.IsReal) :
    (homNhatTaylor R).IsReal := by
  intro x
  refine ⟨by simp [homNhatTaylor], fun k => ?_, fun j => by simp [homNhatTaylor],
    fun i j => by simp [homNhatTaylor, homNormalEntry, kamEntry], fun i j => ?_⟩
  · have := homCoeff_zero_im (u := fun z => R.b z k) (s := s) (fun y => (hR y).2.1 k)
    have hc : homCoeff (fun z => R.b z k) 0 = homCoeff R.b 0 k := by
      simpa using homCoeff_clm hs R.comp_b.1 (ContinuousLinearMap.proj k) 0
    simpa [homNhatTaylor, hc] using this
  · by_cases hij : i = j
    · subst hij
      have hre : ∀ y : Fin 2 → ℝ,
          (homNormalEntry a p pb (R.Q fun j => (y j : ℂ)) i i).im = 0 := fun y => by
        have h1 := (hR y).2.2.2.2 i i
        rw [R.transQ _ (ofReal_mem_complexStrip hs y) i i] at h1
        exact (Complex.conj_eq_iff_im).mp h1.symm
      have h2 := homCoeff_zero_im (u := fun z => homNormalEntry a p pb (R.Q z) i i) (s := s) hre
      have hc : homCoeff (fun z => homNormalEntry a p pb (R.Q z) i i) 0 =
          homNormalEntry a p pb (homCoeff R.Q 0) i i := by
        have := homCoeff_clm hs R.comp_Q.1 (homNormEntryCLM a p pb i i) 0
        simpa [homNormEntryCLM_apply] using this
      rw [hc] at h2
      show (homNormalEntry a p pb (kamEntryDiagCLM (homCoeff R.Q 0)) i i) =
        conj (homNormalEntry a p pb (kamEntryDiagCLM (homCoeff R.Q 0)) i i)
      have e : homNormalEntry a p pb (kamEntryDiagCLM (homCoeff R.Q 0)) i i =
          homNormalEntry a p pb (homCoeff R.Q 0) i i := by
        simp [homNormalEntry, kamEntry_diagCLM]
      rw [e]
      exact ((Complex.conj_eq_iff_im).mpr h2).symm
    · simp [homNhatTaylor, homNormalEntry, kamEntry_diagCLM, hij]

end KAM.Wave
