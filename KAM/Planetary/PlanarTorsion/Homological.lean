/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters
public import KAM.Planetary.PlanarTorsion.Homological.Extract

/-!
# Planar quartic torsion: the homological equation

Blueprint P, Part 11b (`bpP:p11b:homological`, steps `ho-def`, `ho-eq`): for a quartic family
`F` and a frequency map satisfying the non-resonance condition `p11c_NR4`, the generator
`p11c_chi F freq` (a finite sum over the nonzero modes of the characters divided by
`i ⟨k, ω⟩`) is again a quartic family on `O`, and it solves the homological equation
`{χ, n₀} = F - ⟨F⟩`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.Planetary.PlanarCharacters

def p11c_chi {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  (∑' k : Fin 2 → ℤ, if k = 0 then 0 else
    p11c_character F.eval k I z / (Complex.I * (∑ j, (k j : ℂ) * freq I j))).re

/-- The nonzero modes of order at most four. -/
def chiModes : Finset (Fin 2 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 2 => Finset.Icc (-((4 : ℕ) : ℤ)) ((4 : ℕ) : ℤ)).filter
    fun k => k ≠ 0 ∧ (∑ i, |(k i : ℝ)|) ≤ 4

lemma mem_chiModes {k : Fin 2 → ℤ} : k ∈ chiModes ↔ k ≠ 0 ∧ (∑ i, |(k i : ℝ)|) ≤ 4 := by
  unfold chiModes
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  have hi : |(k i : ℝ)| ≤ 4 := (Finset.single_le_sum (f := fun j => |(k j : ℝ)|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)).trans h.2
  have : |k i| ≤ 4 := by exact_mod_cast hi
  rw [Finset.mem_Icc]; push_cast; constructor <;> linarith [abs_le.1 this]

/-- The finite sum of nonzero modes represents `p11c_chi`. -/
lemma chi_eq_sum {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) :
    p11c_chi F freq I z = (∑ k ∈ chiModes, p11c_character F.eval k I z /
      (Complex.I * (∑ j, (k j : ℂ) * freq I j))).re := by
  unfold p11c_chi
  congr 1
  rw [tsum_eq_sum (s := chiModes)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    simp [(mem_chiModes.1 hk).1]
  · intro k hk
    by_cases h0 : k = 0
    · simp [h0]
    · simp only [h0, ite_false]
      have : 4 < (∑ i, |(k i : ℝ)|) := by
        by_contra hle; exact hk (mem_chiModes.2 ⟨h0, not_lt.1 hle⟩)
      rw [(char F).2.1 I z k this, zero_div]

/-- The divisor `i ⟨k, ω⟩` does not vanish on a nonzero mode of order at most four. -/
lemma chi_div_ne {O : Set (Fin 2 → ℝ)} {freq : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hnr : p11c_NR4 O freq) {I : Fin 2 → ℝ} (hI : I ∈ O) {k : Fin 2 → ℤ} (hk : k ∈ chiModes) :
    Complex.I * (∑ j, (k j : ℂ) * freq I j) ≠ 0 := by
  have h := hnr I hI k (mem_chiModes.1 hk).1 (mem_chiModes.1 hk).2
  refine mul_ne_zero Complex.I_ne_zero ?_
  have : (∑ j, (k j : ℂ) * freq I j) = ((∑ j, (k j : ℝ) * freq I j : ℝ) : ℂ) := by push_cast; rfl
  rw [this]; exact_mod_cast h

/-- The sum of the nonzero modes of the characters is the quartic minus its average. -/
lemma chiModes_sum {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (I : Fin 2 → ℝ) (z : Phase 2) :
    (∑ k ∈ chiModes, p11c_character F.eval k I z).re = F.eval I z - p11c_average F.eval I z := by
  have hz : ∀ k ∉ insert (0 : Fin 2 → ℤ) chiModes, p11c_character F.eval k I z = 0 := by
    intro k hk
    rw [Finset.mem_insert, not_or] at hk
    apply (char F).2.1 I z k
    by_contra hle
    exact hk.2 (mem_chiModes.2 ⟨hk.1, not_lt.1 hle⟩)
  have hsum := (hasSum_sum_of_ne_finset_zero hz).unique ((char F).2.2.1 I z)
  rw [Finset.sum_insert (fun h => (mem_chiModes.1 h).1 rfl)] at hsum
  have := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.ofReal_re] at this
  unfold p11c_average
  linarith

/-- One-plane products of Fourier coefficients are finite combinations of the monomials. -/
lemma charprod_extract (a : Fin 4 → Fin 5) (ha : a ∈ charIdx) (k : Fin 2 → ℤ) :
    ∃ c : (Fin 4 → Fin 5) → ℂ, ∀ z : Phase 2,
      charFc (a 0).val (a 1).val (z.1 0) (z.2 0) (k 0) *
        charFc (a 2).val (a 3).val (z.1 1) (z.2 1) (k 1) =
      ∑ b ∈ charIdx, c b * (p11c_monomial (fun i => (b i).val) z : ℂ) := by
  refine quartic_extract _
    (MvPolynomial.rename (![0, 1] : Fin 2 → Fin 4) (charFcPoly (a 0).val (a 1).val (k 0)) *
      MvPolynomial.rename (![2, 3] : Fin 2 → Fin 4) (charFcPoly (a 2).val (a 3).val (k 1)))
    ?_ ?_
  · intro z
    have e0 : (quarticVec z ∘ (![0, 1] : Fin 2 → Fin 4)) = ![(z.1 0 : ℂ), (z.2 0 : ℂ)] := by
      ext i; fin_cases i <;> rfl
    have e1 : (quarticVec z ∘ (![2, 3] : Fin 2 → Fin 4)) = ![(z.1 1 : ℂ), (z.2 1 : ℂ)] := by
      ext i; fin_cases i <;> rfl
    simp only [map_mul, MvPolynomial.eval_rename, e0, e1, charFcPoly_eval]
  · intro z t
    have h4 := charIdx_sum ha
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [charFc_smul, charFc_smul]
    have key : (t : ℂ) ^ ((a 0).val + (a 1).val) * (t : ℂ) ^ ((a 2).val + (a 3).val) =
        (t : ℂ) ^ 4 := by rw [← pow_add]; congr 1
    linear_combination (charFc (a 0).val (a 1).val (z.1 0) (z.2 0) (k 0) *
      charFc (a 2).val (a 3).val (z.1 1) (z.2 1) (k 1)) * key

/-- The coefficient of the monomial `b` in `p11c_chi`. -/
def chiCoeff {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (freq : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (c : (Fin 4 → Fin 5) → (Fin 2 → ℤ) → (Fin 4 → Fin 5) → ℂ) (b : Fin 4 → Fin 5)
    (I : Fin 2 → ℝ) : ℝ :=
  (∑ k ∈ chiModes, ∑ a ∈ charIdx, (F.coeff (fun i => (a i).val) I : ℂ) * c a k b /
    (Complex.I * (∑ j, (k j : ℂ) * freq I j))).re

lemma chiCoeff_analytic {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    {freq : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : AnalyticOnNhd ℝ freq O) (hnr : p11c_NR4 O freq)
    (c : (Fin 4 → Fin 5) → (Fin 2 → ℤ) → (Fin 4 → Fin 5) → ℂ) (b : Fin 4 → Fin 5) :
    AnalyticOnNhd ℝ (chiCoeff F freq c b) O := by
  intro I hI
  refine (Complex.reCLM.analyticAt _).comp ?_
  refine Finset.analyticAt_fun_sum _ fun k hk => Finset.analyticAt_fun_sum _ fun a _ => ?_
  have hs : AnalyticAt ℝ (fun J => ∑ j, (k j : ℂ) * freq J j) I := by
    refine Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ?_
    exact (Complex.ofRealCLM.analyticAt _).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).analyticAt _ |>.comp
        (hf I hI))
  exact (((Complex.ofRealCLM.analyticAt _).comp (F.analytic _ I hI)).mul analyticAt_const).div
    (analyticAt_const.mul hs) (chi_div_ne hnr hI hk)

/-- The quartic family underlying `p11c_chi`. -/
lemma chi_family {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    {freq : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : AnalyticOnNhd ℝ freq O) (hnr : p11c_NR4 O freq) :
    ∃ chi : QuarticFamily O, ∀ I ∈ O, chi.eval I = p11c_chi F freq I := by
  have hex : ∀ (a : Fin 4 → Fin 5) (k : Fin 2 → ℤ), a ∈ charIdx → ∃ c : (Fin 4 → Fin 5) → ℂ,
      ∀ z : Phase 2, charFc (a 0).val (a 1).val (z.1 0) (z.2 0) (k 0) *
        charFc (a 2).val (a 3).val (z.1 1) (z.2 1) (k 1) =
      ∑ b ∈ charIdx, c b * (p11c_monomial (fun i => (b i).val) z : ℂ) :=
    fun a k ha => charprod_extract a ha k
  choose! c hc using hex
  obtain ⟨A, hA⟩ := quartic_of_coeffs (O := O) (chiCoeff F freq c)
    (chiCoeff_analytic F hf hnr c)
  refine ⟨A, fun I hI => funext fun z => ?_⟩
  rw [hA, chi_eq_sum]
  have hmain : ∑ k ∈ chiModes, p11c_character F.eval k I z /
      (Complex.I * (∑ j, (k j : ℂ) * freq I j)) = ∑ b ∈ charIdx,
        (p11c_monomial (fun i => (b i).val) z : ℂ) *
          (∑ k ∈ chiModes, ∑ a ∈ charIdx, (F.coeff (fun i => (a i).val) I : ℂ) * c a k b /
            (Complex.I * (∑ j, (k j : ℂ) * freq I j))) := by
    have hch : ∀ k, p11c_character F.eval k I z = ∑ a ∈ charIdx, ∑ b ∈ charIdx,
        (F.coeff (fun i => (a i).val) I : ℂ) * (c a k b * (p11c_monomial (fun i => (b i).val) z : ℂ)) := by
      intro k
      rw [character_eq_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hc a k ha z, Finset.mul_sum]
    simp_rw [hch, Finset.sum_div, Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hmain, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.re_ofReal_mul]
  unfold chiCoeff
  ring

/-- The homological equation for the finite sum `p11c_chi`. -/
lemma chi_bracket {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    {freq : (Fin 2 → ℝ) → Fin 2 → ℝ} (hnr : p11c_NR4 O freq) {I : Fin 2 → ℝ} (hI : I ∈ O)
    (z : Phase 2) :
    p11c_bracket (p11c_chi F freq I) (p11c_n0 freq I) z =
      F.eval I z - p11c_average F.eval I z := by
  set D : (Fin 2 → ℤ) → ℂ := fun k => Complex.I * (∑ j, (k j : ℂ) * freq I j) with hD
  have hk : ∀ k ∈ chiModes, HasFDerivAt (fun w : Phase 2 => (D k)⁻¹ • p11c_character F.eval k I w)
      ((D k)⁻¹ • fderiv ℝ (fun w => p11c_character F.eval k I w) z) z := fun k _ =>
    ((character_differentiable F k I z).hasFDerivAt).fun_const_smul _
  have hre := Complex.reCLM.hasFDerivAt.comp z (HasFDerivAt.fun_sum hk)
  have hfun : p11c_chi F freq I = ⇑Complex.reCLM ∘
      (fun w => ∑ k ∈ chiModes, (D k)⁻¹ • p11c_character F.eval k I w) := by
    funext w
    simp [chi_eq_sum, div_eq_inv_mul, hD]
  unfold p11c_bracket
  rw [hfun, hre.fderiv]
  simp only [ContinuousLinearMap.comp_apply, sum_apply, smul_apply]
  have hsum : (∑ k ∈ chiModes, (D k)⁻¹ • fderiv ℝ (fun w => p11c_character F.eval k I w) z
      (hamiltonianVectorField (p11c_n0 freq I) z)) =
      ∑ k ∈ chiModes, p11c_character F.eval k I z := by
    refine Finset.sum_congr rfl fun k hk' => ?_
    rw [character_bracket F freq I k z, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (chi_div_ne hnr hI hk'), one_mul]
  rw [hsum]
  simpa using chiModes_sum F I z

theorem homological {O : Set (Fin 2 → ℝ)} (hO : IsOpen O) (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (hf : AnalyticOnNhd ℝ freq O) (hnr : p11c_NR4 O freq) :
    (∃ chi : QuarticFamily O, ∀ I ∈ O, chi.eval I = p11c_chi F freq I) ∧
    ∀ I ∈ O, ∀ z, p11c_bracket (p11c_chi F freq I) (p11c_n0 freq I) z =
      F.eval I z - p11c_average F.eval I z :=
  ⟨chi_family F hf hnr, fun _ hI z => chi_bracket F hnr hI z⟩

end KAM.Planetary

end
