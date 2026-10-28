/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.AnalyticZeros
public import KAM.Planetary.Nondegeneracy.SymmetricRelation.Defs
public import KAM.Planetary.Nondegeneracy.SymmetricRelation.Analytic
public import KAM.Planetary.Nondegeneracy.SymmetricRelation.Limits
public import KAM.Planetary.Nondegeneracy.SymmetricRelation.Cases
public import KAM.Planetary.Nondegeneracy.SymmetricRelation.Small

/-!
# The symmetric product of the relation forms

Blueprint P, Part 10 (`bpP:p10:Fc-def`, `bpP:p10:Fc-analytic`, `bpP:p10:F-nonzero`).  This facade
imports `SymmetricRelation.Defs` (`relation`, `fc_def`), `SymmetricRelation.Analytic`
(`fc_analytic`: the symmetric product is a polynomial in the characteristic coefficients, by
`MvPolynomial.esymmAlgEquiv` over `ℝ[X]`), `SymmetricRelation.Limits` (the innermost-axis limit of
the sorted spectrum, from `peel` and `weyl`), `SymmetricRelation.Cases` (cases A and C of the
peeling induction) and `SymmetricRelation.Small` (the `n = 2` case and the single-coefficient case);
it proves `f_nonzero` by induction on `n`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

theorem fc_analytic (D : Data n) (c : Vec n × Vec n) :
    AnalyticOnNhd ℝ (fc_def D c) (axes n) := fc_analytic_aux D c

/-- The two-planet base case of the induction. -/
lemma f_nonzero_two (D : Data 2) {c : Vec 2 × Vec 2} (hc : c ≠ 0) :
    ∃ a ∈ axes 2, fc_def D c a ≠ 0 := by
  by_cases hA : c.1 0 ≠ 0
  · exact case_A D (n := 1) (by norm_num) hA
  rw [not_not] at hA
  by_cases hB : c.1 1 ≠ 0
  · obtain ⟨a', ha'⟩ := (isConnected_axes 1).nonempty
    refine case_lim D (n := 1) (by norm_num) ha' hA fun p => ?_
    have hz : snocZero (sigma (outerData D (n := 1) (by norm_num)) a') = 0 := by
      funext l
      induction l using Fin.lastCases with
      | last => exact Fin.snoc_last (α := fun _ => ℝ) _ _
      | cast i => simp [snocZero, sigma_one]
    have hν : 0 < nu (outerData D (n := 1) (by norm_num)) (action (outerData D (n := 1)
        (by norm_num)) a') 0 := by
      have hap := action_pos (outerData D (n := 1) (by norm_num)) (a := a') (i := 0) (ha'.1 0)
      have := (outerData D (n := 1) (by norm_num)).hG
      have := (outerData D (n := 1) (by norm_num)).hm0
      have := (outerData D (n := 1) (by norm_num)).hm 0
      simp only [nu]
      positivity
    simp only [relLim, hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
      Fin.sum_univ_one]
    exact mul_ne_zero hB hν.ne'
  rw [not_not] at hB
  have h1 : c.1 = 0 := by
    funext i; fin_cases i
    exacts [hA, hB]
  have h2 : c.2 ≠ 0 := fun h => hc (Prod.ext h1 h)
  by_cases hu : c.2 0 = 0
  · have hv : c.2 1 ≠ 0 := fun h => h2 (by funext i; fin_cases i <;> assumption)
    refine fc_ne_zero_single D (by norm_num) h1 hv fun j hj => ?_
    fin_cases j
    · exact hu
    · exact absurd rfl hj
  by_cases hv : c.2 1 = 0
  · refine fc_ne_zero_single D (by norm_num) h1 hu fun j hj => ?_
    fin_cases j
    · exact absurd rfl hj
    · exact hv
  exact fc_ne_zero_two D h1 hu hv

theorem f_nonzero_aux : ∀ n : ℕ, 2 ≤ n → ∀ (D : Data n) {c : Vec n × Vec n}, c ≠ 0 →
    ∃ a ∈ axes n, fc_def D c a ≠ 0 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact fun D c hc => f_nonzero_two D hc
  | succ n hn ih =>
    intro D c hc
    have hn0 : 0 < n := by omega
    by_cases hA : c.1 0 ≠ 0
    · exact case_A D hn0 hA
    rw [not_not] at hA
    by_cases hd : ∃ d : Fin (n+1), peelRel c d = 0
    · obtain ⟨d, hd⟩ := hd
      have h1 : c.1 = 0 := by
        funext i
        induction i using Fin.cases with
        | zero => exact hA
        | succ i => exact congrFun (congrArg Prod.fst hd) i
      have h2 : ∀ j, j ≠ d → c.2 j = 0 := fun j hj => by
        obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
        exact congrFun (congrArg Prod.snd hd) l
      have hd' : c.2 d ≠ 0 := fun h => hc (Prod.ext h1 (by
        funext j
        by_cases hj : j = d
        · rw [hj]; exact h
        · exact h2 j hj))
      exact fc_ne_zero_single D (by omega) h1 hd' h2
    push Not at hd
    have hgen := generic (isOpen_axes n) (isConnected_axes n)
      (f := fun (d : Fin (n+1)) a => fc_def (outerData D hn0) (peelRel c d) a)
      (fun d => fc_analytic_aux _ _) (fun d => ih _ (hd d))
    obtain ⟨a₀, ha₀⟩ := (isConnected_axes n).nonempty
    obtain ⟨a', ha'S⟩ : ∃ a', a' ∈ {x ∈ axes n | ∀ j, fc_def (outerData D hn0)
        (peelRel c j) x ≠ 0} := by
      by_contra hne
      push Not at hne
      have := hgen.2.1 ha₀
      rw [Set.eq_empty_of_forall_notMem hne, closure_empty] at this
      exact this
    refine case_lim D hn0 ha'S.1 hA fun p => ?_
    rw [relLim_eq]
    exact Finset.prod_ne_zero_iff.1 (ha'S.2 (p.symm (Fin.last n))) (peelPerm p)
      (Finset.mem_univ _)

theorem f_nonzero (D : Data n) (hn : 2 ≤ n) {c : Vec n × Vec n} (hc : c ≠ 0) :
    ∃ a ∈ axes n, fc_def D c a ≠ 0 := f_nonzero_aux n hn D hc

end Nondegeneracy
end KAM.Planetary
end
