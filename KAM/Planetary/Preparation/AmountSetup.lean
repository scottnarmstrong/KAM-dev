/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Prepared
public import KAM.Planetary.Preparation.AmountCore

/-!
# Setup lemmas for `amount` (P11A-P8e)

A compactness jet bound in the diagonal gauge, smoothness of `checkW` on the ball of radius
`5/4` from the prepared specification, and the geometry of the box `J₀ + eps R`.
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

section Setup

variable {n : ℕ}

/-- Compactness bound for the operator gauge of the jets of a smooth map. -/
theorem p11_amt_op_bound {m : ℕ} {V A : Set (P11Vec n)} (hV : IsOpen V) (hA : IsCompact A)
    (hAV : A ⊆ V) {w : P11Vec n → P11Vec m} {k : ℕ} (hw : ContDiffOn ℝ k w V) (j : ℕ)
    (hj : j ≤ k) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ A, p11op w j y ≤ B := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ j w) V :=
    ContinuousOn.continuousOn_iteratedFDeriv hw hV (by exact_mod_cast hj)
  have hBc : IsCompact
      (Set.pi (Set.univ : Set (Fin j)) fun _ => {a : P11Vec n | p11euclid a ≤ 1}) :=
    isCompact_univ_pi fun _ => p11ball_isCompact
  have hF : ContinuousOn (fun p : P11Vec n × (Fin j → P11Vec n) =>
      p11euclid (iteratedFDeriv ℝ j w p.1 p.2))
      (A ×ˢ Set.pi (Set.univ : Set (Fin j)) fun _ => {a : P11Vec n | p11euclid a ≤ 1}) := by
    refine p11euclid_continuous.comp_continuousOn ?_
    refine ContinuousOn.eval ?_ continuousOn_snd
    exact (hcont.mono hAV).comp continuousOn_fst (fun p hp => hp.1)
  obtain ⟨C, hC⟩ := (hA.prod hBc).exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
  unfold p11op
  refine Real.sSup_le ?_ (le_max_right _ _)
  rintro v ⟨a, ha, rfl⟩
  have := hC (y, a) ⟨hy, fun i _ => ha i⟩
  rw [Real.norm_of_nonneg (p11euclid_nonneg _)] at this
  exact this.trans (le_max_left _ _)

/-- A diagonal jet bound on a compact subset of an open set of smoothness. -/
theorem p11_amt_jet_bound {m : ℕ} (hn : 1 ≤ n) {V A : Set (P11Vec n)} (hV : IsOpen V)
    (hA : IsCompact A) (hAV : A ⊆ V) {w : P11Vec n → P11Vec m} {k : ℕ}
    (hw : ContDiffOn ℝ k w V) : ∃ M : ℝ, 0 ≤ M ∧ p11JetBound true k A w M := by
  have : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ (j ≤ k → ∀ y ∈ A, p11op w j y ≤ B) := fun j => by
    by_cases hj : j ≤ k
    · obtain ⟨B, hB, h⟩ := p11_amt_op_bound hV hA hAV hw j hj
      exact ⟨B, hB, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose B hB0 hB using this
  refine ⟨∑ j ∈ Finset.range (k + 1), B j, Finset.sum_nonneg fun j _ => hB0 j,
    fun j hj y hy => ?_⟩
  rw [if_pos rfl]
  exact (p11dg_le_p11op w j y hn).trans ((hB j hj y hy).trans (Finset.single_le_sum (f := B)
    (fun j _ => hB0 j) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))))

/-- Monotonicity of a jet bound in the set. -/
theorem p11_amt_jet_mono {m mu : ℕ} {A B : Set (P11Vec n)} (hAB : A ⊆ B) {f : P11Vec n → P11Vec m}
    {M : ℝ} {d : Bool} (h : p11JetBound d mu B f M) : p11JetBound d mu A f M :=
  fun j hj y hy => h j hj y (hAB hy)

/-- The half-unit cube in `P11Vec n`. -/
def p11HalfCube (n : ℕ) : Set (P11Vec n) :=
  Set.pi univ (fun _ => Icc (-1 / 2 : ℝ) (1 / 2))

theorem p11HalfCube_compact : IsCompact (p11HalfCube n) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem p11HalfCube_nonempty : (p11HalfCube n).Nonempty :=
  ⟨0, fun _ _ => ⟨by norm_num, by norm_num⟩⟩

theorem p11HalfCube_norm {r : P11Vec n} (hr : r ∈ p11HalfCube n) : ‖r‖ ≤ 1 / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  have := hr i (Set.mem_univ i)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [this.1, this.2]

theorem p11_amt_append_norm {r ρ : P11Vec n} (hr : r ∈ p11HalfCube n) (hρ : ρ ∈ p11HalfCube n) :
    ‖(Fin.append r ρ : P11Vec (n + n))‖ ≤ 1 / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; exact (norm_le_pi_norm r j).trans (p11HalfCube_norm hr)
  · rw [Fin.append_right]; exact (norm_le_pi_norm ρ j).trans (p11HalfCube_norm hρ)

theorem p11_amt_box_halfCube {y : P11Vec (n + n)} (hy : y ∈ p11PreparedBox n) :
    (fun i : Fin n => y (Fin.castAdd n i)) ∈ p11HalfCube n ∧
      (fun i : Fin n => y (Fin.natAdd n i)) ∈ p11HalfCube n :=
  ⟨fun _ _ => hy _ (Set.mem_univ _), fun _ _ => hy _ (Set.mem_univ _)⟩

end Setup

end KAM.Planetary

end
