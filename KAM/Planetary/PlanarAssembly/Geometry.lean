/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Planetary.Poincare.Tube
public import KAM.Frozen.Planetary.Defs.CircularTube
public import KAM.Frozen.Planetary.Defs.FastShift

/-!
# Planar assembly geometry (Part 12)

Blueprint P, Part 12 (`bpP:p12:sec-set#data`, `stepP:p12:ft-cpt`, `bpP:p12:forward-tube`): the
action-only Kepler Hamiltonian `kepler_h`, the action centre `action_center`, the compact cell
`compact_cell` of the fast angles in `[0, 2π]`, the actions within `δ` of the centre and the
secular radii `Γ_i ≤ δ`, and the forward tube statement: chart points near the circular torus in
the coordinates `(Λ, Γ)` are mapped by the product chart into the physical tube `circularTube ζ`.
The proof is uniform continuity of the product chart on the compact cell, transported to all fast
angles by the fast-lattice periodicity of the chart and of the circular torus.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function
open scoped BigOperators

namespace KAM.Planetary
open KAM KAM.Kepler

namespace PlanarAssembly

/-- The action-only Kepler Hamiltonian, reusing hProd rather than a second formula. -/
def kepler_h {n : ℕ} (κ : ℝ) (m : Fin n → ℝ) (I : Fin n → ℝ) : ℝ :=
  hProd κ m (assemble I (0 : Fin n → ℝ) (0 : Fin n → ℝ) (0 : Fin n → ℝ))

def action_center (G m0 : ℝ) (m a : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => m i * √(G * m0 * a i)

/-- The compact set used in the proof of forward_tube. -/
def compact_cell (G m0 : ℝ) (m a : Fin 2 → ℝ) (δ : ℝ) : Set (Phase 4) :=
  {w | (∀ i, fast (a := 2) (b := 2) w.1 i ∈ Icc (0 : ℝ) (2 * π)) ∧
    (∀ i, |fast (a := 2) (b := 2) w.2 i - action_center G m0 m a i| ≤ δ) ∧
    (∀ i, poincareGamma (planetBlock (n := 2) w i) ≤ δ)}

private theorem gamma_planetBlock (w : Phase 4) (i : Fin 2) :
    poincareGamma (planetBlock (n := 2) w i) =
      (slow (a := 2) (b := 2) w.1 i ^ 2 + slow (a := 2) (b := 2) w.2 i ^ 2) / 2 := rfl

private theorem continuous_fast_fst (i : Fin 2) :
    Continuous fun w : Phase 4 => fast (a := 2) (b := 2) w.1 i :=
  (continuous_apply _).comp continuous_fst

private theorem continuous_fast_snd (i : Fin 2) :
    Continuous fun w : Phase 4 => fast (a := 2) (b := 2) w.2 i :=
  (continuous_apply _).comp continuous_snd

private theorem continuous_slow_fst (i : Fin 2) :
    Continuous fun w : Phase 4 => slow (a := 2) (b := 2) w.1 i :=
  (continuous_apply _).comp continuous_fst

private theorem continuous_slow_snd (i : Fin 2) :
    Continuous fun w : Phase 4 => slow (a := 2) (b := 2) w.2 i :=
  (continuous_apply _).comp continuous_snd

private theorem continuous_gamma (i : Fin 2) :
    Continuous fun w : Phase 4 => poincareGamma (planetBlock (n := 2) w i) := by
  simp only [gamma_planetBlock]
  exact (((continuous_slow_fst i).pow 2).add ((continuous_slow_snd i).pow 2)).div_const _

private theorem isClosed_compact_cell (G m0 : ℝ) (m a : Fin 2 → ℝ) (δ : ℝ) :
    IsClosed (compact_cell G m0 m a δ) := by
  unfold compact_cell
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter (isClosed_iInter fun i => ?_)
    (IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun i => ?_))
  · exact isClosed_Icc.preimage (continuous_fast_fst i)
  · exact isClosed_le (((continuous_fast_snd i).sub continuous_const).abs) continuous_const
  · exact isClosed_le (continuous_gamma i) continuous_const

private theorem coord_bound_of_gamma {x y δ : ℝ} (h : (x ^ 2 + y ^ 2) / 2 ≤ δ) :
    |x| ≤ 1 + δ ∧ |y| ≤ 1 + δ := by
  have hδ : 0 ≤ δ := le_trans (by positivity) h
  have h1 : x ^ 2 ≤ (1 + δ) ^ 2 := by nlinarith [sq_nonneg y, sq_nonneg δ]
  have h2 : y ^ 2 ≤ (1 + δ) ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg δ]
  exact ⟨abs_le_of_sq_le_sq h1 (by linarith), abs_le_of_sq_le_sq h2 (by linarith)⟩

theorem compact_cell_isCompact (G m0 : ℝ) (m a : Fin 2 → ℝ) (δ : ℝ) :
    IsCompact (compact_cell G m0 m a δ) := by
  set R : ℝ := 2 * π + 1 + δ + ∑ i, |action_center G m0 m a i| + δ with hR
  have hcell : compact_cell G m0 m a δ ⊆
      Set.pi univ (fun _ : Fin (2 + 2) => Icc (-R) R) ×ˢ Set.pi univ (fun _ : Fin (2 + 2) => Icc (-R) R) := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hw
    have hδ : 0 ≤ δ := by
      have := h3 0
      rw [gamma_planetBlock] at this
      exact le_trans (by positivity) this
    have hsum : ∀ i, |action_center G m0 m a i| ≤ ∑ j, |action_center G m0 m a j| := fun i =>
      Finset.single_le_sum (f := fun j => |action_center G m0 m a j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    have hpi : 0 < π := Real.pi_pos
    refine ⟨fun j _ => ?_, fun j _ => ?_⟩
    · induction j using Fin.addCases with
      | left i =>
        have := h1 i
        have e : w.1 (Fin.castAdd 2 i) = fast (a := 2) (b := 2) w.1 i := rfl
        rw [e]; constructor <;> linarith [this.1, this.2, hsum i, abs_nonneg (action_center G m0 m a i)]
      | right i =>
        have := (coord_bound_of_gamma (δ := δ) (by rw [← gamma_planetBlock w i]; exact h3 i)).1
        have e : w.1 (Fin.natAdd 2 i) = slow (a := 2) (b := 2) w.1 i := rfl
        rw [e]
        have := abs_le.1 this
        constructor <;> linarith [hsum i, abs_nonneg (action_center G m0 m a i)]
    · induction j using Fin.addCases with
      | left i =>
        have := abs_le.1 (h2 i)
        have e : w.2 (Fin.castAdd 2 i) = fast (a := 2) (b := 2) w.2 i := rfl
        rw [e]
        constructor <;> linarith [hsum i, abs_nonneg (action_center G m0 m a i), this.1, this.2,
          neg_abs_le (action_center G m0 m a i), le_abs_self (action_center G m0 m a i)]
      | right i =>
        have := (coord_bound_of_gamma (δ := δ) (by rw [← gamma_planetBlock w i]; exact h3 i)).2
        have e : w.2 (Fin.natAdd 2 i) = slow (a := 2) (b := 2) w.2 i := rfl
        rw [e]
        have := abs_le.1 this
        constructor <;> linarith [hsum i, abs_nonneg (action_center G m0 m a i)]
  exact ((isCompact_univ_pi fun _ => isCompact_Icc).prod
    (isCompact_univ_pi fun _ => isCompact_Icc)).of_isClosed_subset
      (isClosed_compact_cell G m0 m a δ) hcell

end PlanarAssembly

end KAM.Planetary

end
