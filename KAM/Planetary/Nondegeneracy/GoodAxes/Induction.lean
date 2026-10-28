/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.GoodAxes.N2
public import KAM.Planetary.Nondegeneracy.GoodAxes.Block
public import KAM.Planetary.Nondegeneracy.GoodAxes.Resonance
public import KAM.Planetary.Nondegeneracy.Peel
public import KAM.Planetary.Nondegeneracy.Weyl

/-!
# Good axes: a good point in the hierarchical regime

Blueprint P, Part 10 (`bpP:p10:good-point`, `stepP:p10:gp-base`, `stepP:p10:gp-choice`,
`stepP:p10:gp-loc`, `stepP:p10:gp-nr`): induction on the number of planets, letting the innermost
semi-major axis tend to `0`.  `peel_step` is the induction step: the bordered matrix `0 ⊕ Q̂` has
sorted spectrum `(δ, 0)` (`sorted_blockZero`), Weyl's inequality moves it by at most `‖E‖`
(`peel`), and `nr4_perturb` transfers non-resonance.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

lemma sigma_neg (D : Data n) (hn : 2 ≤ n) {a : Vec n} (ha : a ∈ axes n) (j : Fin n) :
    sigma D a j < 0 := by
  have h := (definite D hn ha).2.2.2.2.1 j
  have := (definite D hn ha).2.2.1
  linarith

lemma peelError_cons (D : Data (n+1)) (hn : 0 < n) (t : ℝ) (a' : Vec n) :
    peelError D hn (Fin.cons t a') =
      coeffs D (Fin.cons t a') - blockZero (coeffs (outerData D hn) a') := by
  ext i j
  simp only [peelError, blockZero, Matrix.sub_apply, Fin.cons_succ]

lemma sorted_congr {M N : Mat n} (h : M = N) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    sorted M hM = sorted N hN := by
  subst h; rfl

/-- `stepP:p10:gp-choice`, `stepP:p10:gp-loc`, `stepP:p10:gp-nr`: one induction step. -/
theorem peel_step (D : Data (n+1)) (hn : 2 ≤ n) {a' : Vec n} (ha' : a' ∈ axes n)
    (hnr : nr4 (sigma (outerData D (by omega)) a')) {c : ℝ} (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧ t < c ∧ (Fin.cons t a' : Vec (n+1)) ∈ axes (n+1) ∧
      nr4 (sigma D (Fin.cons t a')) := by
  have hn0 : 0 < n := by omega
  obtain ⟨C, hC, hpeel⟩ := peel D hn0 ha'
  obtain ⟨κ0, hκ0, hκ⟩ := exists_gap (k4_finite n).toFinset
    (fun k => |∑ i, (k i : ℝ) * sigma (outerData D hn0) a' i|)
    (fun k hk => abs_pos.2 (hnr.2 k ((k4_finite n).mem_toFinset.1 hk)))
  have hT : Tendsto (fun t : ℝ => C * t ^ (3/2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 (3/2 : ℝ) (Or.inr (by norm_num))).tendsto.const_mul
      C).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [Real.zero_rpow (by norm_num : (3/2 : ℝ) ≠ 0)] using this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 < t ∧ t < c) ∧ t ≤ 1 ∧ (∀ i, t ≤ a' i / 2) ∧
      C * t ^ (3/2 : ℝ) < κ0 / 4 := by
    refine ((eventually_mem_nhdsWithin.mono fun t (h : t ∈ Set.Ioi (0:ℝ)) => h).and ((eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds)).and
      ?_
    refine (((eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds).mono
      fun t h => h.le).and ?_
    refine (Filter.eventually_all.2 fun i =>
      ((eventually_lt_nhds (half_pos (ha'.1 i))).filter_mono nhdsWithin_le_nhds).mono
        fun t h => h.le).and ?_
    exact hT.eventually_lt_const (by positivity)
  obtain ⟨t, ⟨ht0, htc⟩, ht1, hta, hCt⟩ := hev.exists
  have ha := cons_mem ha' ht0 hta
  refine ⟨t, ht0, htc, ha, ?_⟩
  set D' := outerData D hn0 with hD'
  obtain ⟨hop, hfro, -⟩ := hpeel t ht0 ht1 hta
  set E := peelError D hn0 (Fin.cons t a') with hE
  set A := blockZero (coeffs D' a') with hA
  have hAh : A.IsHermitian := blockZero_isHermitian (coeffs_hermitian D' a')
  have hsum : A + E = coeffs D (Fin.cons t a') := by
    rw [hE, peelError_cons]; abel
  have hEh : E.IsHermitian := by
    rw [hE, peelError_cons]; exact (coeffs_hermitian D _).sub hAh
  have hAEh : (A + E).IsHermitian := hAh.add hEh
  have hw := weyl A E hAh hEh hAEh
  have hsort := sorted_blockZero (coeffs_hermitian D' a')
    (fun j => (sigma_neg D' hn ha' j).le)
  have hsig : sigma D (Fin.cons t a') = sorted (A + E) hAEh :=
    (sorted_congr hsum hAEh (coeffs_hermitian D _)).symm
  have hn1 := sigma_neg D (by omega) ha (Fin.last n)
  refine nr4_perturb (δ := sigma D' a') (e := C * t ^ (3/2 : ℝ)) (κ0 := κ0)
    (by positivity) (by linarith) (fun k hk => hκ k ((k4_finite n).mem_toFinset.2 hk))
    (fun i => ?_) hn1
  have h1 := hw i
  rw [hsig]
  rw [hsig] at hn1
  rw [hsort] at h1
  exact h1.trans (hop.trans hfro)


/-- `stepP:p10:gp-base`: the two-planet base case. -/
lemma good_point_two (D : Data 2) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ a ∈ axes 2, (∀ i j : Fin 2, j.val = i.val+1 → a i/a j < ε) ∧ nr4 (sigma D a) := by
  have m0 := D.hm 0
  have m1 := D.hm 1
  set c : ℝ := D.m 1 ^ 2 / (16 * D.m 0 ^ 2) with hc
  have hcp : 0 < c := by positivity
  set a0 : ℝ := min (ε / 2) (c / 2) with ha0
  have ha0p : 0 < a0 := lt_min (by linarith) (by linarith)
  have ha0ε : a0 < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ha0c : a0 ≤ c := (min_le_right _ _).trans (by linarith)
  have ha : (![a0, 1] : Vec 2) ∈ axes 2 := by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [ha0p]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      linarith [ha0ε]
  refine ⟨_, ha, ?_, nr4_of_hier D ha ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    exact ha0ε
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [le_div_iff₀ ha0p]
    have : 16 * D.m 0 ^ 2 / D.m 1 ^ 2 * a0 ≤ 16 * D.m 0 ^ 2 / D.m 1 ^ 2 * c :=
      mul_le_mul_of_nonneg_left ha0c (by positivity)
    have e : 16 * D.m 0 ^ 2 / D.m 1 ^ 2 * c = 1 := by rw [hc]; field_simp
    linarith

theorem good_point (D : Data n) (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ a ∈ axes n, (∀ i j : Fin n, j.val = i.val+1 → a i/a j < ε) ∧ nr4 (sigma D a) := by
  induction n, hn using Nat.le_induction with
  | base => exact good_point_two D hε hε1
  | succ n hn ih =>
    have hn0 : 0 < n := by omega
    obtain ⟨a', ha', hchain, hnr⟩ := ih (outerData D hn0)
    obtain ⟨t, ht0, htc, hax, hnr'⟩ := peel_step D hn ha' hnr (c := ε * a' ⟨0, hn0⟩)
      (mul_pos hε (ha'.1 _))
    refine ⟨_, hax, fun i j hij => ?_, hnr'⟩
    induction i using Fin.cases with
    | zero =>
      have hj : j = Fin.succ ⟨0, hn0⟩ := Fin.ext (by simpa using hij)
      subst hj
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [div_lt_iff₀ (ha'.1 _)]; linarith
    | succ i' =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j' =>
        simp only [Fin.cons_succ]
        exact hchain i' j' (by simpa using hij)

end Nondegeneracy
end KAM.Planetary
end
