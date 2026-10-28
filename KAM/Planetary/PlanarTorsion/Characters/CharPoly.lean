/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters.Poly
public import KAM.Planetary.PlanarTorsion.Characters.Average

/-!
# Planar quartic torsion: polynomial clauses of the character lemma

Blueprint P, Part 11b (`bpP:p11b:char`): `character_polynomial` — analytic dependence on the
action, polynomial form of degree at most four in `(x₁, y₁, x₂, y₂)`, degree-four homogeneity, and
the average `F₀` as a real quartic family.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.Planetary.PlanarCharacters

lemma charIdx_single (t : Fin 4 → ℕ) (ht : ∃ s0 ∈ charIdx, (fun i => (s0 i).val) = t) (w : ℝ)
    (m : (Fin 4 → ℕ) → ℝ) :
    ∑ s ∈ charIdx, (if (fun i => (s i).val) = t then w else 0) * m (fun i => (s i).val) = w * m t := by
  obtain ⟨s0, hs0, rfl⟩ := ht
  rw [Finset.sum_eq_single_of_mem s0 hs0]
  · simp
  · intro s _ hne
    have : (fun i => (s i).val) ≠ (fun i => (s0 i).val) := fun h =>
      hne (funext fun i => Fin.ext (congrFun h i))
    simp [this]

/-- Coefficients of the quartic `a J0² + b J0 J1 + c J1²` in the monomials. -/
def charQcoef (a b c : ℝ) (s : Fin 4 → ℕ) : ℝ :=
  (if s = ![4, 0, 0, 0] then 1 / 4 * a else 0) + (if s = ![2, 2, 0, 0] then 1 / 2 * a else 0) +
  (if s = ![0, 4, 0, 0] then 1 / 4 * a else 0) + (if s = ![2, 0, 2, 0] then 1 / 4 * b else 0) +
  (if s = ![2, 0, 0, 2] then 1 / 4 * b else 0) + (if s = ![0, 2, 2, 0] then 1 / 4 * b else 0) +
  (if s = ![0, 2, 0, 2] then 1 / 4 * b else 0) + (if s = ![0, 0, 4, 0] then 1 / 4 * c else 0) +
  (if s = ![0, 0, 2, 2] then 1 / 2 * c else 0) + (if s = ![0, 0, 0, 4] then 1 / 4 * c else 0)

lemma charQcoef_analytic {O : Set (Fin 2 → ℝ)} {a b c : (Fin 2 → ℝ) → ℝ}
    (ha : AnalyticOnNhd ℝ a O) (hb : AnalyticOnNhd ℝ b O) (hc : AnalyticOnNhd ℝ c O)
    (s : Fin 4 → ℕ) : AnalyticOnNhd ℝ (fun I => charQcoef (a I) (b I) (c I) s) O := by
  unfold charQcoef
  have h := fun (f : (Fin 2 → ℝ) → ℝ) (hf : AnalyticOnNhd ℝ f O) (P : Prop) [Decidable P] (r : ℝ) =>
    charIte_analytic hf P r
  refine AnalyticOnNhd.add ?_ (h _ hc _ _)
  refine AnalyticOnNhd.add ?_ (h _ hc _ _)
  refine AnalyticOnNhd.add ?_ (h _ hc _ _)
  refine AnalyticOnNhd.add ?_ (h _ hb _ _)
  refine AnalyticOnNhd.add ?_ (h _ hb _ _)
  refine AnalyticOnNhd.add ?_ (h _ hb _ _)
  refine AnalyticOnNhd.add ?_ (h _ hb _ _)
  refine AnalyticOnNhd.add ?_ (h _ ha _ _)
  exact AnalyticOnNhd.add (h _ ha _ _) (h _ ha _ _)

lemma charIdx_mem {s : Fin 4 → Fin 5} (h : (s 0).val + (s 1).val + (s 2).val + (s 3).val = 4) :
    s ∈ charIdx := by
  simp [charIdx, Fin.sum_univ_four, h]

/-- A real quartic family is determined by a quadratic form in the oscillator actions. -/
lemma quartic_of_actions {O : Set (Fin 2 → ℝ)} {a b c : (Fin 2 → ℝ) → ℝ}
    (ha : AnalyticOnNhd ℝ a O) (hb : AnalyticOnNhd ℝ b O) (hc : AnalyticOnNhd ℝ c O) :
    ∃ A : QuarticFamily O, ∀ I z, A.eval I z =
      a I * (oscillatorAction z.2 z.1 0) ^ 2 +
      b I * oscillatorAction z.2 z.1 0 * oscillatorAction z.2 z.1 1 +
      c I * (oscillatorAction z.2 z.1 1) ^ 2 := by
  refine ⟨⟨fun s I => charQcoef (a I) (b I) (c I) s, fun s => charQcoef_analytic ha hb hc s⟩, ?_⟩
  intro I z
  rw [show QuarticFamily.eval ⟨fun s I => charQcoef (a I) (b I) (c I) s,
      fun s => charQcoef_analytic ha hb hc s⟩ I z = ∑ s ∈ charIdx,
        charQcoef (a I) (b I) (c I) (fun i => (s i).val) * p11c_monomial (fun i => (s i).val) z
      from rfl]
  simp only [charQcoef, add_mul, Finset.sum_add_distrib]
  rw [charIdx_single ![4, 0, 0, 0] ⟨![4, 0, 0, 0], by simp [charIdx, Fin.sum_univ_four], by funext i; fin_cases i <;> rfl⟩ _ (fun t => p11c_monomial t z),
    charIdx_single ![2, 2, 0, 0] ⟨![2, 2, 0, 0], by simp [charIdx, Fin.sum_univ_four], by funext i; fin_cases i <;> rfl⟩ _ (fun t => p11c_monomial t z),
    charIdx_single ![0, 4, 0, 0] ⟨![0, 4, 0, 0], by simp [charIdx, Fin.sum_univ_four], by funext i; fin_cases i <;> rfl⟩ _ (fun t => p11c_monomial t z),
    charIdx_single ![2, 0, 2, 0] ⟨![2, 0, 2, 0], by simp [charIdx, Fin.sum_univ_four], by funext i; fin_cases i <;> rfl⟩ _ (fun t => p11c_monomial t z),
    charIdx_single ![2, 0, 0, 2] ⟨![2, 0, 0, 2], by simp [charIdx, Fin.sum_univ_four], by funext i; fin_cases i <;> rfl⟩ _ (fun t => p11c_monomial t z),
    charIdx_single ![0, 2, 2, 0] ⟨![0, 2, 2, 0], by simp [charIdx, Fin.sum_univ_four], by funext i; fin_cases i <;> rfl⟩ _ (fun t => p11c_monomial t z),
    charIdx_single ![0, 2, 0, 2] ⟨![0, 2, 0, 2], by simp [charIdx, Fin.sum_univ_four], by funext i; fin_cases i <;> rfl⟩ _ (fun t => p11c_monomial t z),
    charIdx_single ![0, 0, 4, 0] ⟨![0, 0, 4, 0], by simp [charIdx, Fin.sum_univ_four], by funext i; fin_cases i <;> rfl⟩ _ (fun t => p11c_monomial t z),
    charIdx_single ![0, 0, 2, 2] ⟨![0, 0, 2, 2], by simp [charIdx, Fin.sum_univ_four], by funext i; fin_cases i <;> rfl⟩ _ (fun t => p11c_monomial t z),
    charIdx_single ![0, 0, 0, 4] ⟨![0, 0, 0, 4], by simp [charIdx, Fin.sum_univ_four], by funext i; fin_cases i <;> rfl⟩ _ (fun t => p11c_monomial t z)]
  simp only [p11c_monomial, oscillatorAction]
  simp
  ring

lemma character_mv {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (k : Fin 2 → ℤ) (I : Fin 2 → ℝ) :
    ∃ P : MvPolynomial (Fin 4) ℂ, P.totalDegree ≤ 4 ∧ ∀ z : Phase 2,
      p11c_character F.eval k I z = MvPolynomial.eval
        ![(z.1 0 : ℂ), (z.2 0 : ℂ), (z.1 1 : ℂ), (z.2 1 : ℂ)] P := by
  refine ⟨∑ a ∈ charIdx, MvPolynomial.C (F.coeff (fun i => (a i).val) I : ℂ) *
      (MvPolynomial.rename (![0, 1] : Fin 2 → Fin 4) (charFcPoly (a 0).val (a 1).val (k 0)) *
        MvPolynomial.rename (![2, 3] : Fin 2 → Fin 4) (charFcPoly (a 2).val (a 3).val (k 1))),
    ?_, ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun a ha => ?_
    have h4 := charIdx_sum ha
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 := (MvPolynomial.totalDegree_rename_le (![0, 1] : Fin 2 → Fin 4)
      (charFcPoly (a 0).val (a 1).val (k 0))).trans (charFcPoly_deg _ _ _)
    have h2 := (MvPolynomial.totalDegree_rename_le (![2, 3] : Fin 2 → Fin 4)
      (charFcPoly (a 2).val (a 3).val (k 1))).trans (charFcPoly_deg _ _ _)
    omega
  · intro z
    rw [character_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e0 : (![(z.1 0 : ℂ), (z.2 0 : ℂ), (z.1 1 : ℂ), (z.2 1 : ℂ)] ∘ (![0, 1] : Fin 2 → Fin 4)) =
        ![(z.1 0 : ℂ), (z.2 0 : ℂ)] := by
      ext i; fin_cases i <;> rfl
    have e1 : (![(z.1 0 : ℂ), (z.2 0 : ℂ), (z.1 1 : ℂ), (z.2 1 : ℂ)] ∘ (![2, 3] : Fin 2 → Fin 4)) =
        ![(z.1 1 : ℂ), (z.2 1 : ℂ)] := by
      ext i; fin_cases i <;> rfl
    simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename, e0, e1, charFcPoly_eval]

lemma character_homog {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (k : Fin 2 → ℤ) (I : Fin 2 → ℝ)
    (z : Phase 2) (t : ℝ) :
    p11c_character F.eval k I (t • z) = (t : ℂ) ^ 4 * p11c_character F.eval k I z := by
  rw [character_eq_sum, character_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have h4 := charIdx_sum ha
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  rw [charFc_smul, charFc_smul]
  have key : (t : ℂ) ^ ((a 0).val + (a 1).val) * (t : ℂ) ^ ((a 2).val + (a 3).val) = (t : ℂ) ^ 4 := by
    rw [← pow_add]; congr 1
  linear_combination ((F.coeff (fun i => (a i).val) I : ℂ) *
    (charFc (a 0).val (a 1).val (z.1 0) (z.2 0) (k 0) *
      charFc (a 2).val (a 3).val (z.1 1) (z.2 1) (k 1))) * key

theorem character_polynomial {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    (k : Fin 2 → ℤ) :
    (∀ z, AnalyticOnNhd ℝ (fun I => p11c_character F.eval k I z) O) ∧
    (∀ I, ∃ P : MvPolynomial (Fin 4) ℂ, P.totalDegree ≤ 4 ∧ ∀ z : Phase 2,
      p11c_character F.eval k I z = MvPolynomial.eval
        ![(z.1 0 : ℂ), (z.2 0 : ℂ), (z.1 1 : ℂ), (z.2 1 : ℂ)] P) ∧
    (∀ I z (t : ℝ), p11c_character F.eval k I (t • z) = (t : ℂ) ^ 4 * p11c_character F.eval k I z) ∧
    ∃ A : QuarticFamily O, ∀ I z, A.eval I z = p11c_average F.eval I z := by
  refine ⟨?_, fun I => character_mv F k I, fun I z t => character_homog F k I z t, ?_⟩
  · intro z
    have : (fun I => p11c_character F.eval k I z) = fun I => ∑ a ∈ charIdx,
        (F.coeff (fun i => (a i).val) I : ℂ) *
          (charFc ((a 0).val) ((a 1).val) (z.1 0) (z.2 0) (k 0) *
            charFc ((a 2).val) ((a 3).val) (z.1 1) (z.2 1) (k 1)) := by
      funext I; exact character_eq_sum F k I z
    rw [this]
    refine Finset.analyticOnNhd_fun_sum _ fun a _ I hI => ?_
    exact ((Complex.ofRealCLM.analyticAt _).comp (F.analytic _ I hI)).mul analyticAt_const
  · obtain ⟨A, hA⟩ := quartic_of_actions (charAvgA_analytic F) (charAvgB_analytic F)
      (charAvgC_analytic F)
    exact ⟨A, fun I z => (hA I z).trans (average_formula F I z).symm⟩

end KAM.Planetary

end
