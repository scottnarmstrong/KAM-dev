/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.PNat.Basic

/-!
# Sup-weighted sequences (blueprint-W `bpW:w1:linfty`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

`ℓ^p_∞` is realized as `lp (fun _ : ℕ+ => ℝ) ∞` through `w ↦ (j^p w_j)`:
`IsLinfty`, `tauInfty`, `norm_tauInfty` (`‖τ w‖ = sup_j |w_j| j^p`), and the `L`-Lipschitz predicate
`IsLinftyLipschitz`, with the pointwise characterization `isLinftyLipschitz_iff`.
-/

@[expose] public noncomputable section

open ENNReal

namespace KAM.Wave

/-- Membership in `ℓ^p_∞`: `(j^p w_j)_j` is bounded. -/
def IsLinfty (p : ℝ) (w : ℕ+ → ℝ) : Prop :=
  Memℓp (fun j : ℕ+ => (j : ℝ) ^ p * w j) ∞

/-- The transport `τ : ℓ^p_∞ → lp ∞`, `w ↦ (j^p w_j)` (blueprint `bpW:w1:linfty`). -/
def tauInfty (p : ℝ) (w : ℕ+ → ℝ) (h : IsLinfty p w) : lp (fun _ : ℕ+ => ℝ) ∞ :=
  ⟨fun j => (j : ℝ) ^ p * w j, h⟩

@[simp] theorem tauInfty_apply (p : ℝ) (w : ℕ+ → ℝ) (h : IsLinfty p w) (j : ℕ+) :
    tauInfty p w h j = (j : ℝ) ^ p * w j := rfl

theorem rpow_pnat_pos (p : ℝ) (j : ℕ+) : 0 < (j : ℝ) ^ p :=
  Real.rpow_pos_of_pos (by exact_mod_cast j.pos) p

/-- `bpW:w1:linfty`: the norm of `lp ∞` is the sup `sup_j |w_j| j^p`. -/
theorem norm_tauInfty_le_iff (p : ℝ) (w : ℕ+ → ℝ) (h : IsLinfty p w) {C : ℝ} (hC : 0 ≤ C) :
    ‖tauInfty p w h‖ ≤ C ↔ ∀ j : ℕ+, |w j| * (j : ℝ) ^ p ≤ C := by
  constructor
  · intro hn j
    have := lp.norm_apply_le_norm (by simp) (tauInfty p w h) j
    simp only [tauInfty_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pnat_pos p j)] at this
    linarith [this.trans hn]
  · intro hj
    refine lp.norm_le_of_forall_le hC fun j => ?_
    simp only [tauInfty_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pnat_pos p j)]
    linarith [hj j, mul_comm |w j| ((j : ℝ) ^ p)]

/-- `ℓ^p_∞`-membership from a pointwise sup bound. -/
theorem isLinfty_of_bound (p : ℝ) (w : ℕ+ → ℝ) {C : ℝ} (hC : ∀ j : ℕ+, |w j| * (j : ℝ) ^ p ≤ C) :
    IsLinfty p w := by
  refine memℓp_infty ⟨C, ?_⟩
  rintro _ ⟨j, rfl⟩
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pnat_pos p j)]
  linarith [hC j, mul_comm |w j| ((j : ℝ) ^ p)]

/-- The pure difference condition `|Ω(ξ) - Ω(ζ)|_p ≤ L |ξ - ζ|` for all `ξ, ζ ∈ Π` (max norm on
`ℝ²`), through the transport `tauInfty`. It does not assert that the values lie in `ℓ^p_∞`; the
source-facing predicate is `IsLinftyLipschitz`. -/
def IsLinftyDiffLipschitz (p L : ℝ) (Dom : Set (Fin 2 → ℝ)) (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) : Prop :=
  ∀ ξ ∈ Dom, ∀ ζ ∈ Dom, ∃ h : IsLinfty p (fun j => Ω ξ j - Ω ζ j),
    ‖tauInfty p _ h‖ ≤ L * ‖ξ - ζ‖

/-- `Ω̃ : Π → ℓ^p_∞` is `L`-Lipschitz (`L ≥ 0`; blueprint `bpW:w1:linfty`): every value lies in
`ℓ^p_∞` and `|Ω̃(ξ) - Ω̃(ζ)|_p ≤ L |ξ - ζ|` for all `ξ, ζ ∈ Π`. -/
def IsLinftyLipschitz (p L : ℝ) (Dom : Set (Fin 2 → ℝ)) (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) : Prop :=
  0 ≤ L ∧ (∀ ξ ∈ Dom, IsLinfty p (Ω ξ)) ∧ IsLinftyDiffLipschitz p L Dom Ω

/-- `bpW:w1:linfty`: pointwise characterization of the difference condition (`L ≥ 0`). -/
theorem isLinftyDiffLipschitz_iff {p L : ℝ} (hL : 0 ≤ L) {Dom : Set (Fin 2 → ℝ)}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} :
    IsLinftyDiffLipschitz p L Dom Ω ↔
      ∀ ξ ∈ Dom, ∀ ζ ∈ Dom, ∀ j : ℕ+, |Ω ξ j - Ω ζ j| * (j : ℝ) ^ p ≤ L * ‖ξ - ζ‖ := by
  constructor
  · intro h ξ hξ ζ hζ j
    obtain ⟨hi, hn⟩ := h ξ hξ ζ hζ
    exact (norm_tauInfty_le_iff p _ hi (by positivity)).1 hn j
  · intro h ξ hξ ζ hζ
    have hb := h ξ hξ ζ hζ
    have hi := isLinfty_of_bound p _ hb
    exact ⟨hi, (norm_tauInfty_le_iff p _ hi (by positivity)).2 hb⟩

/-- `bpW:w1:linfty`: pointwise characterization of the source-facing Lipschitz predicate. -/
theorem isLinftyLipschitz_iff {p L : ℝ} {Dom : Set (Fin 2 → ℝ)} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} :
    IsLinftyLipschitz p L Dom Ω ↔ 0 ≤ L ∧ (∀ ξ ∈ Dom, IsLinfty p (Ω ξ)) ∧
      ∀ ξ ∈ Dom, ∀ ζ ∈ Dom, ∀ j : ℕ+, |Ω ξ j - Ω ζ j| * (j : ℝ) ^ p ≤ L * ‖ξ - ζ‖ := by
  unfold IsLinftyLipschitz
  constructor
  · rintro ⟨hL, hm, hd⟩
    exact ⟨hL, hm, (isLinftyDiffLipschitz_iff hL).1 hd⟩
  · rintro ⟨hL, hm, hd⟩
    exact ⟨hL, hm, (isLinftyDiffLipschitz_iff hL).2 hd⟩

end KAM.Wave

end
