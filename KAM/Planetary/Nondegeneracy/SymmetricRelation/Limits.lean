/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.GoodAxes
public import KAM.Planetary.Nondegeneracy.SymmetricRelation.Defs

/-!
# Symmetric relation product: the limit as the innermost axis tends to zero

Blueprint P, Part 10 (`stepP:p10:F-A`, `stepP:p10:F-C`): with `a = (t, a')`, `t ↓ 0`, the sorted
eigenvalues `σ_l(a)` tend to those of `0 ⊕ Q̂(a')` (Lemma `bpP:p10:peel` and Weyl), and
`ν_1(t) → ∞`, while `ν_i` (`i ≥ 2`) do not depend on `t`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

/-- The limit spectrum `δ ⊕ 0`. -/
abbrev snocZero (s : Vec n) : Vec (n+1) := Fin.snoc (α := fun _ => ℝ) s (0 : ℝ)

/-- A single planet has vanishing secular matrix. -/
lemma coeffs_one (D : Data 1) (a : Vec 1) : coeffs D a = 0 := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi; subst hj
  simp [SecularForm.coeffs, SecularForm.qhat]

lemma sigma_one (D : Data 1) (a : Vec 1) (j : Fin 1) : sigma D a j = 0 := by
  have h := charpoly_eq_prod_sorted (coeffs_hermitian D a)
  have hz : (coeffs D a).charpoly = (X : ℝ[X]) ^ 1 := by
    rw [coeffs_one, Matrix.charpoly_zero]; simp
  rw [hz] at h
  have := congrArg (Polynomial.eval (sigma D a 0)) h
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simpa [sigma, Finset.prod_eq_single_of_mem] using this

/-- The sorted spectrum of the peeled matrix is non-positive. -/
lemma sigma_outer_nonpos (D : Data (n+1)) (hn : 0 < n) {a' : Vec n} (ha' : a' ∈ axes n)
    (j : Fin n) : sigma (outerData D hn) a' j ≤ 0 := by
  by_cases h : n = 1
  · subst h; exact (sigma_one (outerData D hn) a' j).le
  · exact (sigma_neg (outerData D hn) (by omega) ha' j).le

/-- `stepP:p10:peel` with Weyl: the sorted spectrum of `(t, a')` is within `C t^{3/2}` of that of
`0 ⊕ Q̂(a')`. -/
lemma sigma_cons_close (D : Data (n+1)) (hn : 0 < n) {a' : Vec n} (ha' : a' ∈ axes n)
    (h0 : ∀ j, sigma (outerData D hn) a' j ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → (∀ i, t ≤ a' i / 2) → ∀ l,
      |sigma D (Fin.cons t a') l - snocZero (sigma (outerData D hn) a') l| ≤
        C * t ^ (3/2 : ℝ) := by
  obtain ⟨C, hC, hpeel⟩ := peel D hn ha'
  refine ⟨C, hC, fun t ht ht1 hta l => ?_⟩
  obtain ⟨hop, hfro, -⟩ := hpeel t ht ht1 hta
  set D' := outerData D hn with hD'
  set E := peelError D hn (Fin.cons t a') with hE
  set A := blockZero (coeffs D' a') with hA
  have hAh : A.IsHermitian := blockZero_isHermitian (coeffs_hermitian D' a')
  have hsum : A + E = coeffs D (Fin.cons t a') := by
    rw [hE, peelError_cons]; abel
  have hEh : E.IsHermitian := by
    rw [hE, peelError_cons]; exact (coeffs_hermitian D _).sub hAh
  have hAEh : (A + E).IsHermitian := hAh.add hEh
  have hw := weyl A E hAh hEh hAEh l
  have hsort := sorted_blockZero (coeffs_hermitian D' a') h0
  have hsig : sigma D (Fin.cons t a') = sorted (A + E) hAEh :=
    (sorted_congr hsum hAEh (coeffs_hermitian D _)).symm
  rw [hsig]
  rw [hsort] at hw
  exact hw.trans (hop.trans hfro)

lemma tendsto_sigma_cons (D : Data (n+1)) (hn : 0 < n) {a' : Vec n} (ha' : a' ∈ axes n)
    (h0 : ∀ j, sigma (outerData D hn) a' j ≤ 0) (l : Fin (n+1)) :
    Tendsto (fun t : ℝ => sigma D (Fin.cons t a') l) (𝓝[>] 0)
      (𝓝 (snocZero (sigma (outerData D hn) a') l)) := by
  obtain ⟨C, hC, hcl⟩ := sigma_cons_close D hn ha' h0
  have hT : Tendsto (fun t : ℝ => C * t ^ (3/2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 (3/2 : ℝ) (Or.inr (by norm_num))).tendsto.const_mul
      C).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [Real.zero_rpow (by norm_num : (3/2 : ℝ) ≠ 0)] using this
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => dist_nonneg) ?_ hT
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ 1 ∧ (∀ i, t ≤ a' i / 2) := by
    refine (eventually_mem_nhdsWithin.mono fun t (h : t ∈ Set.Ioi (0:ℝ)) => h).and ?_
    refine (((eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds).mono
      fun t h => h.le).and ?_
    exact (Filter.eventually_all.2 fun i =>
      ((eventually_lt_nhds (half_pos (ha'.1 i))).filter_mono nhdsWithin_le_nhds).mono
        fun t h => h.le)
  filter_upwards [hev] with t ⟨ht, ht1, hta⟩
  rw [Real.dist_eq]
  exact hcl t ht ht1 hta l

lemma eventually_cons_mem {a' : Vec n} (ha' : a' ∈ axes n) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), (Fin.cons t a' : Vec (n+1)) ∈ axes (n+1) := by
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ (∀ i, t ≤ a' i / 2) := by
    refine (eventually_mem_nhdsWithin.mono fun t (h : t ∈ Set.Ioi (0:ℝ)) => h).and ?_
    exact (Filter.eventually_all.2 fun i =>
      ((eventually_lt_nhds (half_pos (ha'.1 i))).filter_mono nhdsWithin_le_nhds).mono
        fun t h => h.le)
  exact hev.mono fun t ⟨ht, hta⟩ => cons_mem ha' ht hta

/-- The `t`-independent limit value of `L_{c,π}` minus its first fast term. -/
def relLim (D : Data (n+1)) (hn : 0 < n) (a' : Vec n) (c : Vec (n+1) × Vec (n+1))
    (p : Equiv.Perm (Fin (n+1))) : ℝ :=
  (∑ i : Fin n, c.1 i.succ * nu (outerData D hn) (action (outerData D hn) a') i) +
    ∑ j : Fin (n+1), c.2 j * snocZero (sigma (outerData D hn) a') (p j)

lemma relation_cons (D : Data (n+1)) (c : Vec (n+1) × Vec (n+1)) (p : Equiv.Perm (Fin (n+1)))
    (t : ℝ) (a' : Vec n) (hn : 0 < n) :
    relation D c p (Fin.cons t a') = c.1 0 * nu D (action D (Fin.cons t a')) 0 +
      ((∑ i : Fin n, c.1 i.succ * nu (outerData D hn) (action (outerData D hn) a') i) +
        ∑ j, c.2 j * sigma D (Fin.cons t a') (p j)) := by
  simp only [relation, Fin.sum_univ_succ]
  rw [add_assoc]
  rfl

lemma tendsto_relation (D : Data (n+1)) (hn : 0 < n) {a' : Vec n} (ha' : a' ∈ axes n)
    (c : Vec (n+1) × Vec (n+1)) (p : Equiv.Perm (Fin (n+1))) :
    Tendsto (fun t : ℝ => relation D c p (Fin.cons t a') -
      c.1 0 * nu D (action D (Fin.cons t a')) 0) (𝓝[>] 0) (𝓝 (relLim D hn a' c p)) := by
  have h0 := sigma_outer_nonpos D hn ha'
  have hs : Tendsto (fun t : ℝ => ∑ j, c.2 j * sigma D (Fin.cons t a') (p j)) (𝓝[>] 0)
      (𝓝 (∑ j, c.2 j * snocZero (sigma (outerData D hn) a') (p j))) :=
    tendsto_finsetSum _ fun j _ => (tendsto_sigma_cons D hn ha' h0 (p j)).const_mul _
  have := hs.const_add (∑ i : Fin n, c.1 i.succ * nu (outerData D hn)
    (action (outerData D hn) a') i)
  refine this.congr fun t => ?_
  rw [relation_cons D c p t a' hn]; ring

end Nondegeneracy
end KAM.Planetary
end
