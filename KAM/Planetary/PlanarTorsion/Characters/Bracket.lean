/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters.CharPoly

/-!
# Planar quartic torsion: the character bracket

Blueprint P, Part 11b (`bpP:p11b:char`, step `ch-bra`): `{F_k, N₀} = i (k·Ω) F_k`.  The characters
are polynomials, hence differentiable; the Hamiltonian flow of `N₀` is the rotation by `tΩ`, along
which the character is multiplied by `e^{i t k·Ω}`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.Planetary.PlanarCharacters

lemma mv_eval_differentiable (P : MvPolynomial (Fin 4) ℂ) :
    Differentiable ℝ (fun w : Phase 2 =>
      MvPolynomial.eval ![(w.1 0 : ℂ), (w.2 0 : ℂ), (w.1 1 : ℂ), (w.2 1 : ℂ)] P) := by
  have hv : ∀ i : Fin 4, Differentiable ℝ (fun w : Phase 2 =>
      (![(w.1 0 : ℂ), (w.2 0 : ℂ), (w.1 1 : ℂ), (w.2 1 : ℂ)] : Fin 4 → ℂ) i) := by
    intro i
    fin_cases i
    · exact Complex.ofRealCLM.differentiable.comp ((differentiable_apply 0).comp differentiable_fst)
    · exact Complex.ofRealCLM.differentiable.comp ((differentiable_apply 0).comp differentiable_snd)
    · exact Complex.ofRealCLM.differentiable.comp ((differentiable_apply 1).comp differentiable_fst)
    · exact Complex.ofRealCLM.differentiable.comp ((differentiable_apply 1).comp differentiable_snd)
  induction P using MvPolynomial.induction_on with
  | C a => simpa using differentiable_const _
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (hv i)

lemma character_differentiable {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (k : Fin 2 → ℤ)
    (I : Fin 2 → ℝ) : Differentiable ℝ (fun w : Phase 2 => p11c_character F.eval k I w) := by
  obtain ⟨P, _, hP⟩ := character_mv F k I
  have : (fun w : Phase 2 => p11c_character F.eval k I w) = fun w : Phase 2 =>
      MvPolynomial.eval ![(w.1 0 : ℂ), (w.2 0 : ℂ), (w.1 1 : ℂ), (w.2 1 : ℂ)] P := funext hP
  rw [this]
  exact mv_eval_differentiable P

lemma n0_fderiv_apply (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (z v : Phase 2) :
    fderiv ℝ (p11c_n0 freq I) z v = ∑ j, freq I j * (z.2 j * v.2 j + z.1 j * v.1 j) := by
  have hd : Differentiable ℝ (p11c_n0 freq I) := by
    unfold p11c_n0 oscillatorAction; fun_prop
  have hg : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h1 := (hd z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hg (by simp)
  have ha : ∀ j, HasDerivAt (fun t : ℝ => z.2 j + t * v.2 j) (v.2 j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.2 j)).const_add (z.2 j)
  have hb : ∀ j, HasDerivAt (fun t : ℝ => z.1 j + t * v.1 j) (v.1 j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.1 j)).const_add (z.1 j)
  have h2 : HasDerivAt (fun t : ℝ => p11c_n0 freq I (z + t • v))
      (∑ j, freq I j * (z.2 j * v.2 j + z.1 j * v.1 j)) 0 := by
    unfold p11c_n0 oscillatorAction
    refine HasDerivAt.fun_sum fun j _ => ?_
    have := ((((ha j).pow 2).add ((hb j).pow 2)).div_const 2).const_mul (freq I j)
    convert this using 1
    simp; ring
  exact h1.unique h2

lemma hamiltonian_n0 (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) :
    hamiltonianVectorField (p11c_n0 freq I) z =
      (fun j => freq I j * z.2 j, fun j => -(freq I j * z.1 j)) := by
  unfold hamiltonianVectorField
  ext j
  · rw [n0_fderiv_apply]
    simp [Pi.single_apply]
  · rw [n0_fderiv_apply]
    simp [Pi.single_apply]

lemma rotation_hasDerivAt (Ω : Fin 2 → ℝ) (z : Phase 2) :
    HasDerivAt (fun t : ℝ => p11c_rotation (t • Ω) z)
      (fun j => Ω j * z.2 j, fun j => -(Ω j * z.1 j)) 0 := by
  have hf : ∀ j, HasDerivAt (fun t : ℝ => t * Ω j) (Ω j) 0 := fun j => by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (Ω j)
  refine HasDerivAt.prodMk ?_ ?_
  · rw [hasDerivAt_pi]
    intro j
    have := (((hf j).cos).mul_const (z.1 j)).add (((hf j).sin).mul_const (z.2 j))
    convert this using 1
    simp
  · rw [hasDerivAt_pi]
    intro j
    have := ((((hf j).sin).neg).mul_const (z.1 j)).add (((hf j).cos).mul_const (z.2 j))
    convert this using 1
    simp

theorem character_bracket {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (k : Fin 2 → ℤ) (z : Phase 2) :
    fderiv ℝ (fun w => p11c_character F.eval k I w) z
      (hamiltonianVectorField (p11c_n0 freq I) z) =
        Complex.I * (∑ j, (k j : ℂ) * freq I j) * p11c_character F.eval k I z := by
  set Ω := freq I with hΩ
  set S : ℂ := ∑ j, (k j : ℂ) * (Ω j : ℂ) with hS
  have hγ0 : p11c_rotation ((0 : ℝ) • Ω) z = z := by
    simp [p11c_rotation]
  have hγ : HasDerivAt (fun t : ℝ => p11c_rotation (t • Ω) z)
      (hamiltonianVectorField (p11c_n0 freq I) z) 0 := by
    rw [hamiltonian_n0]; exact rotation_hasDerivAt Ω z
  have hcomp := (character_differentiable F k I z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0
  have hfun : ((fun w : Phase 2 => p11c_character F.eval k I w) ∘
      fun t : ℝ => p11c_rotation (t • Ω) z) =
      fun t : ℝ => Complex.exp (Complex.I * ((t : ℂ) * S)) * p11c_character F.eval k I z := by
    funext t
    simp only [Function.comp]
    rw [character_covariance]
    congr 3
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  rw [hfun] at hcomp
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * ((t : ℂ) * S)) *
      p11c_character F.eval k I z) (Complex.I * S * p11c_character F.eval k I z) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have := (((h1.mul_const S).const_mul Complex.I).cexp).mul_const (p11c_character F.eval k I z)
    convert this using 1
    simp
  have := hcomp.unique hexp
  rw [this, hS]
  simp [hΩ]

end KAM.Planetary

end
