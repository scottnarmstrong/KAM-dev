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

/-! ### Forward tube -/

private theorem mem_dom_of_close {G m0 : ℝ} {m a : Fin 2 → ℝ} {δ : ℝ} {w : Phase 4}
    (hΛ : ∀ i, 0 < action_center G m0 m a i) (hδ : ∀ i, δ ≤ action_center G m0 m a i / 4)
    (h2 : ∀ i, |fast (a := 2) (b := 2) w.2 i - action_center G m0 m a i| ≤ δ)
    (h3 : ∀ i, poincareGamma (planetBlock (n := 2) w i) ≤ δ) : w ∈ poincareProdDom 2 := by
  intro i
  have h := abs_le.1 (h2 i)
  have hd := hδ i
  have hΓ := h3 i
  have hf : (planetBlock (n := 2) w i).2 0 = fast (a := 2) (b := 2) w.2 i := rfl
  refine ⟨?_, ?_⟩
  · show 0 < (planetBlock (n := 2) w i).2 0
    rw [hf]
    linarith [h.1, hΛ i]
  · show poincareGamma (planetBlock (n := 2) w i) < (planetBlock (n := 2) w i).2 0
    rw [hf]
    linarith [h.1, hΛ i]

private theorem dist_lt_of_coords {x y : Phase 4} {ε : ℝ} (hε : 0 < ε)
    (h1 : ∀ i, |fast (a := 2) (b := 2) x.1 i - fast (a := 2) (b := 2) y.1 i| < ε)
    (h2 : ∀ i, |slow (a := 2) (b := 2) x.1 i - slow (a := 2) (b := 2) y.1 i| < ε)
    (h3 : ∀ i, |fast (a := 2) (b := 2) x.2 i - fast (a := 2) (b := 2) y.2 i| < ε)
    (h4 : ∀ i, |slow (a := 2) (b := 2) x.2 i - slow (a := 2) (b := 2) y.2 i| < ε) :
    dist x y < ε := by
  rw [Prod.dist_eq]
  refine max_lt ?_ ?_
  · refine (dist_pi_lt_iff hε).2 fun j => ?_
    rw [Real.dist_eq]
    have key : ∀ j : Fin (2 + 2), |x.1 j - y.1 j| < ε := fun j => by
      induction j using Fin.addCases with
      | left i => exact h1 i
      | right i => exact h2 i
    exact key j
  · refine (dist_pi_lt_iff hε).2 fun j => ?_
    rw [Real.dist_eq]
    have key : ∀ j : Fin (2 + 2), |x.2 j - y.2 j| < ε := fun j => by
      induction j using Fin.addCases with
      | left i => exact h3 i
      | right i => exact h4 i
    exact key j

private theorem abs_lt_of_gamma_le {x y δ ε : ℝ} (hε : 0 < ε) (h : (x ^ 2 + y ^ 2) / 2 ≤ δ)
    (hδ : δ ≤ ε ^ 2 / 4) : |x| < ε ∧ |y| < ε := by
  have h1 : x ^ 2 < ε ^ 2 := by nlinarith [sq_nonneg y, sq_pos_of_pos hε]
  have h2 : y ^ 2 < ε ^ 2 := by nlinarith [sq_nonneg x, sq_pos_of_pos hε]
  exact ⟨abs_lt_of_sq_lt_sq h1 hε.le, abs_lt_of_sq_lt_sq h2 hε.le⟩

private theorem assemble_shift (I phi : Fin 2 → ℝ) (k : Fin 2 → ℤ) :
    (assemble I (fun i => phi i + 2 * π * (k i : ℝ)) (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) :
        Phase (2 + 2)) =
      assemble I phi (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) + fastShift (a := 2) (b := 2) k := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · have key : ∀ j : Fin (2 + 2), (assemble I (fun i => phi i + 2 * π * (k i : ℝ))
        (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) : Phase (2 + 2)).1 j =
        (assemble I phi (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) +
          fastShift (a := 2) (b := 2) k).1 j := fun j => by
      induction j using Fin.addCases with
      | left i => simp [assemble, fastShift, Fin.append_left]
      | right i => simp [assemble, fastShift]
    exact key j
  · have key : ∀ j : Fin (2 + 2), (assemble I (fun i => phi i + 2 * π * (k i : ℝ))
        (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) : Phase (2 + 2)).2 j =
        (assemble I phi (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) +
          fastShift (a := 2) (b := 2) k).2 j := fun j => by
      induction j using Fin.addCases with
      | left i => simp [assemble, fastShift, Fin.append_left]
      | right i => simp [assemble, fastShift]
    exact key j

/-- bpP:p12:forward-tube, including its explicit upper radius bound. -/
theorem forward_tube (G m0 : ℝ) (m a : Fin 2 → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i) (ha : ∀ i, 0 < a i)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i, δ ≤ action_center G m0 m a i / 4) ∧
      ∀ w : Phase 4,
        (∀ i, |fast (a := 2) (b := 2) w.2 i - action_center G m0 m a i| ≤ δ) →
        (∀ i, poincareGamma (planetBlock (n := 2) w i) ≤ δ) →
        w ∈ poincareProdDom 2 ∧
        ‖poincareProd m (G * m0) w -
          circularPoint G m0 m a (fun i => fast (a := 2) (b := 2) w.1 i / (2 * π))‖ < ζ ∧
        poincareProd m (G * m0) w ∈ circularTube G m0 m a ζ := by
  have hκ : 0 < G * m0 := mul_pos hG hm0
  have hΛ : ∀ i, 0 < action_center G m0 m a i := fun i => by
    have := ha i; have := hm i; unfold action_center; positivity
  set δ0 : ℝ := min (action_center G m0 m a 0) (action_center G m0 m a 1) / 4 with hδ0
  have hδ0pos : 0 < δ0 := by
    have := hΛ 0; have := hΛ 1; rw [hδ0]; positivity
  have hδ0le : ∀ i, δ0 ≤ action_center G m0 m a i / 4 := fun i => by
    rw [hδ0]
    have : min (action_center G m0 m a 0) (action_center G m0 m a 1) ≤ action_center G m0 m a i := by
      fin_cases i
      · exact min_le_left _ _
      · exact min_le_right _ _
    linarith
  have hKdom : compact_cell G m0 m a δ0 ⊆ poincareProdDom 2 := fun w hw =>
    mem_dom_of_close hΛ hδ0le hw.2.1 hw.2.2
  have hKc := compact_cell_isCompact G m0 m a δ0
  have hcont : ContinuousOn (poincareProd m (G * m0)) (compact_cell G m0 m a δ0) :=
    (analyticOnNhd_poincareProd hm hκ).continuousOn.mono hKdom
  obtain ⟨δ1, hδ1, hunif⟩ :=
    Metric.uniformContinuousOn_iff.1 (hKc.uniformContinuousOn_of_continuous hcont) ζ hζ
  set δ : ℝ := min δ0 (min (δ1 / 2) (δ1 ^ 2 / 4)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; have := sq_pos_of_pos hδ1; positivity
  have hδle0 : δ ≤ δ0 := min_le_left _ _
  have hδle1 : δ ≤ δ1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδle2 : δ ≤ δ1 ^ 2 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδpos, fun i => hδle0.trans (hδ0le i), fun w h2 h3 => ?_⟩
  have hdom : w ∈ poincareProdDom 2 := mem_dom_of_close hΛ (fun i => hδle0.trans (hδ0le i)) h2 h3
  -- reduce the fast angles to `[0, 2π)`
  set k : Fin 2 → ℤ := fun i => ⌊fast (a := 2) (b := 2) w.1 i / (2 * π)⌋ with hk
  set w' : Phase 4 := w - fastShift (a := 2) (b := 2) k with hw'
  have hw'w : w' + fastShift (a := 2) (b := 2) k = w := sub_add_cancel _ _
  have hblock : ∀ i, planetBlock (n := 2) w i =
      (![(planetBlock (n := 2) w' i).1 0 + 2 * π * (k i : ℝ), (planetBlock (n := 2) w' i).1 1],
        (planetBlock (n := 2) w' i).2) := fun i => by
    conv_lhs => rw [← hw'w]
    exact planetBlock_shift w' k i
  have hf1 : ∀ i, fast (a := 2) (b := 2) w.1 i =
      fast (a := 2) (b := 2) w'.1 i + 2 * π * (k i : ℝ) := fun i => by
    exact congrArg (fun p => p.1 0) (hblock i)
  have hf2 : ∀ i, fast (a := 2) (b := 2) w'.2 i = fast (a := 2) (b := 2) w.2 i := fun i => by
    exact (congrArg (fun p => p.2 0) (hblock i)).symm
  have hs1 : ∀ i, slow (a := 2) (b := 2) w'.1 i = slow (a := 2) (b := 2) w.1 i := fun i => by
    exact (congrArg (fun p => p.1 1) (hblock i)).symm
  have hs2 : ∀ i, slow (a := 2) (b := 2) w'.2 i = slow (a := 2) (b := 2) w.2 i := fun i => by
    exact (congrArg (fun p => p.2 1) (hblock i)).symm
  have hΓ' : ∀ i, poincareGamma (planetBlock (n := 2) w' i) ≤ δ := fun i => by
    rw [gamma_planetBlock, hs1, hs2, ← gamma_planetBlock]; exact h3 i
  have h2' : ∀ i, |fast (a := 2) (b := 2) w'.2 i - action_center G m0 m a i| ≤ δ := fun i => by
    rw [hf2]; exact h2 i
  have hpos2pi : 0 < 2 * π := by positivity
  have hfr : ∀ i, fast (a := 2) (b := 2) w'.1 i ∈ Icc (0 : ℝ) (2 * π) := fun i => by
    have h1 := Int.floor_le (fast (a := 2) (b := 2) w.1 i / (2 * π))
    have h2 := Int.lt_floor_add_one (fast (a := 2) (b := 2) w.1 i / (2 * π))
    have e := hf1 i
    have e1 : (k i : ℝ) * (2 * π) ≤ fast (a := 2) (b := 2) w.1 i := by
      rwa [le_div_iff₀ hpos2pi] at h1
    have e2 : fast (a := 2) (b := 2) w.1 i < ((k i : ℝ) + 1) * (2 * π) := by
      rwa [div_lt_iff₀ hpos2pi] at h2
    constructor <;> nlinarith
  have hw'K : w' ∈ compact_cell G m0 m a δ0 :=
    ⟨hfr, fun i => (h2' i).trans hδle0, fun i => (hΓ' i).trans hδle0⟩
  set w0 : Phase 4 := assemble (action_center G m0 m a) (fun i => fast (a := 2) (b := 2) w'.1 i)
    (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) with hw0
  have hw0K : w0 ∈ compact_cell G m0 m a δ0 := by
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · simpa [hw0, assemble, fast, Fin.append_left] using hfr i
    · simpa [hw0, assemble, fast, Fin.append_left] using hδ0pos.le
    · simpa [hw0, gamma_planetBlock, assemble, slow, Fin.append_right] using hδ0pos.le
  have hw0dom : w0 ∈ poincareProdDom 2 := hKdom hw0K
  have hdist : dist w' w0 < δ1 := by
    have hg := fun i => abs_lt_of_gamma_le hδ1 (by rw [← gamma_planetBlock]; exact hΓ' i)
      (hδle2.trans le_rfl)
    refine dist_lt_of_coords hδ1 (fun i => ?_) (fun i => ?_) (fun i => ?_) (fun i => ?_)
    · simpa [hw0, assemble, fast, Fin.append_left] using hδ1
    · simpa [hw0, assemble, slow, Fin.append_right] using (hg i).1
    · have : fast (a := 2) (b := 2) w0.2 i = action_center G m0 m a i := by
        simp [hw0, assemble, fast, Fin.append_left]
      rw [this]
      exact lt_of_le_of_lt (h2' i) (by linarith)
    · simpa [hw0, assemble, slow, Fin.append_right] using (hg i).2
  have hclose : dist (poincareProd m (G * m0) w') (poincareProd m (G * m0) w0) < ζ :=
    hunif w' hw'K w0 hw0K hdist
  have hw'dom : w' ∈ poincareProdDom 2 := hKdom hw'K
  have hP1 : poincareProd m (G * m0) w = poincareProd m (G * m0) w' := by
    rw [← hw'w]; exact (poincareProd_lattice hm hκ hw'dom k).2
  have hcirc : circularPoint G m0 m a (fun i => fast (a := 2) (b := 2) w.1 i / (2 * π)) =
      poincareProd m (G * m0) w0 := by
    rw [circularPoint_eq_poincareProd hG hm0 hm ha]
    have e : (fun i => 2 * π * (fast (a := 2) (b := 2) w.1 i / (2 * π))) =
        fun i => fast (a := 2) (b := 2) w'.1 i + 2 * π * (k i : ℝ) := by
      funext i; rw [hf1 i]; field_simp
    rw [e]
    have := assemble_shift (action_center G m0 m a) (fun i => fast (a := 2) (b := 2) w'.1 i) k
    change poincareProd m (G * m0)
      (assemble (action_center G m0 m a) _ (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ)) = _
    rw [this]
    exact (poincareProd_lattice hm hκ hw0dom k).2
  have hnorm : ‖poincareProd m (G * m0) w -
      circularPoint G m0 m a (fun i => fast (a := 2) (b := 2) w.1 i / (2 * π))‖ < ζ := by
    rw [hcirc, hP1, ← dist_eq_norm]; exact hclose
  exact ⟨hdom, hnorm, _, hnorm⟩

end PlanarAssembly

end KAM.Planetary

end
