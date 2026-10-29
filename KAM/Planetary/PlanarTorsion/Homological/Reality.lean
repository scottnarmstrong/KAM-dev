/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Hamiltonian.Algebra
public import KAM.Planetary.PlanarTorsion.Homological

/-!
# Planar quartic torsion: reality of the unprojected generator and the reversed bracket

Blueprint P, Part 11b, steps `ho-def` and `ho-eq` of `bpP:p11b:homological`.
`ho_def_conj` is the conjugation identity `conj (F_k/(i k·Ω)) = F_{-k}/(i (-k)·Ω)`;
`ho_def_real` says the unprojected complex sum is real on `O` and equals the signed
`p11c_chi` (its real part). `ho_eq_forward` is the signed equation `{χ, N₀} = F - F₀` and
`ho_eq_reversed` the reversed form `{N₀, χ} = -(F - ⟨F⟩)`, in the convention of `p11c_bracket`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary

open KAM KAM.Planetary.PlanarCharacters

/-- The unprojected complex sum `∑_{k ≠ 0} F_k / (i k·Ω)` over the retained modes. -/
def chiComplex {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) : ℂ :=
  ∑ k ∈ chiModes, p11c_character F.eval k I z / (Complex.I * (∑ j, (k j : ℂ) * freq I j))

lemma neg_mem_chiModes {k : Fin 2 → ℤ} (hk : k ∈ chiModes) : -k ∈ chiModes := by
  rw [mem_chiModes] at hk ⊢
  refine ⟨neg_ne_zero.2 hk.1, ?_⟩
  simpa using hk.2

/-- `ho-def`: conjugation of a single mode. -/
theorem ho_def_conj {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) (k : Fin 2 → ℤ) :
    star (p11c_character F.eval k I z / (Complex.I * (∑ j, (k j : ℂ) * freq I j))) =
      p11c_character F.eval (-k) I z / (Complex.I * (∑ j, ((-k) j : ℂ) * freq I j)) := by
  have hs : (∑ j, (k j : ℂ) * freq I j) = ((∑ j, (k j : ℝ) * freq I j : ℝ) : ℂ) := by
    push_cast; rfl
  have hs' : (∑ j, ((-k) j : ℂ) * freq I j) = -((∑ j, (k j : ℝ) * freq I j : ℝ) : ℂ) := by
    rw [← hs, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [hs', hs, star_div₀, (char F).2.2.2 I z k]
  congr 1
  rw [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- `ho-def`: the unprojected complex sum is real-valued and equals `p11c_chi`. -/
theorem ho_def_real {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) :
    (chiComplex F freq I z).im = 0 ∧ chiComplex F freq I z = (p11c_chi F freq I z : ℂ) := by
  have hstar : star (chiComplex F freq I z) = chiComplex F freq I z := by
    unfold chiComplex
    rw [star_sum]
    simp_rw [ho_def_conj F freq I z]
    exact Finset.sum_nbij' (fun k => -k) (fun k => -k) (fun k hk => neg_mem_chiModes hk)
      (fun k hk => neg_mem_chiModes hk) (fun k _ => neg_neg k) (fun k _ => neg_neg k)
      (fun k _ => rfl)
  have him : (chiComplex F freq I z).im = 0 := by
    have := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  refine ⟨him, Complex.ext ?_ ?_⟩
  · rw [Complex.ofReal_re, chi_eq_sum]; rfl
  · rw [Complex.ofReal_im]; exact him

/-- `ho-eq`: `{χ, N₀} = F - F₀`, in the convention of `p11c_bracket`. -/
theorem ho_eq_forward {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    {freq : (Fin 2 → ℝ) → Fin 2 → ℝ} (hnr : p11c_NR4 O freq) {I : Fin 2 → ℝ} (hI : I ∈ O)
    (z : Phase 2) :
    p11c_bracket (p11c_chi F freq I) (p11c_n0 freq I) z =
      F.eval I z - p11c_average F.eval I z :=
  chi_bracket F hnr hI z

/-- Antisymmetry of `p11c_bracket`. -/
theorem p11c_bracket_antisymm (f g : Phase 2 → ℝ) (z : Phase 2) :
    p11c_bracket f g z = -p11c_bracket g f z := by
  unfold p11c_bracket
  rw [← symplecticForm_hamiltonianVectorField, ← symplecticForm_hamiltonianVectorField,
    symplecticForm_antisymm]

/-- `ho-eq`: the reversed form `{N₀, χ} = -(F - ⟨F⟩)`. -/
theorem ho_eq_reversed {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    {freq : (Fin 2 → ℝ) → Fin 2 → ℝ} (hnr : p11c_NR4 O freq) {I : Fin 2 → ℝ} (hI : I ∈ O)
    (z : Phase 2) :
    p11c_bracket (p11c_n0 freq I) (p11c_chi F freq I) z =
      -(F.eval I z - p11c_average F.eval I z) := by
  rw [p11c_bracket_antisymm, ho_eq_forward F hnr hI z]

end KAM.Planetary

end
