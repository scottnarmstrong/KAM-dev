/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.SymmetricRelation.Limits

/-!
# Symmetric relation product: the cases of the peeling induction

Blueprint P, Part 10 (`stepP:p10:F-A`, `stepP:p10:F-C`): Case A (`c'_1 ≠ 0`), the limit criterion
for `c'_1 = 0`, and the identification of the limit of `L_{c,π}` with a factor
`L^{(n-1)}_{c^{(d)},π''}` of the `(n-1)`-planet product.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

lemma tendsto_nu_zero (D : Data (n+1)) (a' : Vec n) :
    Tendsto (fun t : ℝ => nu D (action D (Fin.cons t a')) 0) (𝓝[>] 0) atTop := by
  have hK : 0 < (D.G * D.m0) ^ 2 * D.m 0 ^ 3 := by
    have := D.hG; have := D.hm0; have := D.hm 0; positivity
  have hu : Tendsto (fun t : ℝ => D.m 0 * √(D.G * D.m0 * t)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous fun t : ℝ => D.m 0 * √(D.G * D.m0 * t) := by fun_prop
      have := hc.tendsto 0
      simpa using this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have := D.hG; have := D.hm0; have := D.hm 0
      exact mul_pos (D.hm 0) (Real.sqrt_pos.2 (by positivity))
  have hu3 : Tendsto (fun t : ℝ => (D.m 0 * √(D.G * D.m0 * t)) ^ 3) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (hu.mono_right (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))).pow 3
      simpa using this
    · filter_upwards [tendsto_nhdsWithin_iff.1 hu |>.2] with t (ht : 0 < _)
      exact pow_pos ht 3
  have := (tendsto_inv_nhdsGT_zero.comp hu3).const_mul_atTop hK
  refine this.congr fun t => ?_
  simp [nu, action, div_eq_mul_inv]

lemma eventually_ne_of_cons {D : Data (n+1)} {a' : Vec n} {c : Vec (n+1) × Vec (n+1)}
    (h : ∀ p : Equiv.Perm (Fin (n+1)), ∀ᶠ t in 𝓝[>] (0 : ℝ), relation D c p (Fin.cons t a') ≠ 0)
    (ha' : a' ∈ axes n) : ∃ a ∈ axes (n+1), fc_def D c a ≠ 0 := by
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ p : Equiv.Perm (Fin (n+1)),
      relation D c p (Fin.cons t a') ≠ 0 := Filter.eventually_all.2 h
  obtain ⟨t, ht, hm⟩ := (hall.and (eventually_cons_mem ha')).exists
  exact ⟨_, hm, Finset.prod_ne_zero_iff.2 fun p _ => ht p⟩

/-- Case A: `c'_1 ≠ 0`. -/
theorem case_A (D : Data (n+1)) (hn : 0 < n) {c : Vec (n+1) × Vec (n+1)} (hc : c.1 0 ≠ 0) :
    ∃ a ∈ axes (n+1), fc_def D c a ≠ 0 := by
  obtain ⟨a', ha'⟩ := (isConnected_axes n).nonempty
  refine eventually_ne_of_cons (fun p => ?_) ha'
  have hν := tendsto_nu_zero D a'
  have hq := (tendsto_relation D hn ha' c p).div_atTop hν
  have hlim : Tendsto (fun t : ℝ => relation D c p (Fin.cons t a') /
      nu D (action D (Fin.cons t a')) 0) (𝓝[>] 0) (𝓝 (c.1 0)) := by
    have := hq.const_add (c.1 0)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [hν.eventually_gt_atTop 0] with t ht
    field_simp
    ring
  filter_upwards [hlim.eventually_ne hc] with t h1 h
  exact h1 (by rw [h, zero_div])

/-- Limit criterion when the first fast coefficient vanishes. -/
theorem case_lim (D : Data (n+1)) (hn : 0 < n) {a' : Vec n} (ha' : a' ∈ axes n)
    {c : Vec (n+1) × Vec (n+1)} (hc : c.1 0 = 0) (h : ∀ p, relLim D hn a' c p ≠ 0) :
    ∃ a ∈ axes (n+1), fc_def D c a ≠ 0 := by
  refine eventually_ne_of_cons (fun p => ?_) ha'
  have := tendsto_relation D hn ha' c p
  simp only [hc, zero_mul, sub_zero] at this
  exact this.eventually_ne (h p)

/-- The permutation of the remaining `n` slots induced by a permutation of `n+1` slots. -/
def peelPerm (p : Equiv.Perm (Fin (n+1))) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective
    (fun l => (p ((p.symm (Fin.last n)).succAbove l)).castPred (fun h => by
      have := p.injective (h.trans (p.apply_symm_apply _).symm)
      exact Fin.succAbove_ne _ _ this))
    (Finite.injective_iff_bijective.1 fun l l' h => by
      have h1 := congrArg Fin.castSucc h
      simp only [Fin.castSucc_castPred] at h1
      exact Fin.succAbove_right_injective (p.injective h1))

lemma castSucc_peelPerm (p : Equiv.Perm (Fin (n+1))) (l : Fin n) :
    (peelPerm p l).castSucc = p ((p.symm (Fin.last n)).succAbove l) := by
  simp [peelPerm]

/-- The relation vector of the `(n)`-planet system obtained by deleting slot `d`. -/
def peelRel (c : Vec (n+1) × Vec (n+1)) (d : Fin (n+1)) : Vec n × Vec n :=
  (fun i => c.1 i.succ, fun l => c.2 (d.succAbove l))

theorem relLim_eq (D : Data (n+1)) (hn : 0 < n) (a' : Vec n) (c : Vec (n+1) × Vec (n+1))
    (p : Equiv.Perm (Fin (n+1))) :
    relLim D hn a' c p =
      relation (outerData D hn) (peelRel c (p.symm (Fin.last n))) (peelPerm p) a' := by
  set d := p.symm (Fin.last n) with hd
  simp only [relLim, relation, peelRel]
  congr 1
  rw [Fin.sum_univ_succAbove _ d]
  have h1 : snocZero (sigma (outerData D hn) a') (p d) = 0 := by
    rw [hd, p.apply_symm_apply]; simp [snocZero]
  rw [h1, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← castSucc_peelPerm]
  simp [snocZero]

end Nondegeneracy
end KAM.Planetary
end
