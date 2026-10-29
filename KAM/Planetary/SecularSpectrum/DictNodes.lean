/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.SpectralAdapter
public import KAM.Planetary.Nondegeneracy.SymmetricRelation.Limits

/-!
# Secular spectrum: the dictionary `Ω_j = 2 σ_j`

Blueprint P, Part 9 (`bpP:p9:dict`, package GAP-P9dict).  `sorted_smul` says that the sorted
eigenvalue list of `c • A` is `c` times that of `A` for a real symmetric `A` and `c > 0`.
`p9_dict` is the node's literal conclusion: the sorted eigenvalue list of `2 • Q_h` (the matrix of
Fej04r (36)--(37)) is `2 σ`, every `σ_j` and every `2 σ_j` is negative (`n ≥ 2`), and for `n = 1`
the matrix `Q_h` and the entry `Ω₁ = 2 σ₁` vanish.  `p9_dict_planar` identifies the landed frozen
`Ω_j = 2 * p11c_sigma` with that eigenvalue list.
-/

@[expose] public noncomputable section
open Polynomial
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm Nondegeneracy
variable {n : ℕ} {c : ℝ}

/-- The characteristic polynomial of `c • A` has the roots `c λ_k`. -/
lemma charpoly_smul_eq_prod_sorted {A : Mat n} (hA : A.IsHermitian) (c : ℝ) :
    (c • A).charpoly = ∏ k, (X - C (c * sorted A hA k)) := by
  obtain ⟨τ, hτ, hs⟩ := sorted_eq_eigenvalues_comp hA
  have h : (c • A).charpoly = ∏ i, (X - C (c * hA.eigenvalues i)) := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    set U : Mat n := (hA.eigenvectorUnitary : Mat n)
    set d : Mat n := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
    have e : c • (U * d * star U) = U * (c • d) * star U := by simp
    rw [e, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc,
      show star U * U = 1 from Unitary.coe_star_mul_self _, Matrix.mul_one]
    have hd : c • d = Matrix.diagonal fun i => c * hA.eigenvalues i := by
      ext i j
      by_cases hij : i = j <;> simp [d, hij]
    rw [hd, Matrix.charpoly_diagonal]
  rw [h]
  simp_rw [hs]
  exact hτ.prod_comp (fun i => X - C (c * hA.eigenvalues i)) |>.symm

/-- The sorted eigenvalue list of `c • A` is `c` times that of `A` (real symmetric `A`, `c > 0`). -/
theorem sorted_smul {A : Mat n} (hA : A.IsHermitian) (hcA : (c • A).IsHermitian) (hc : 0 < c) :
    sorted (c • A) hcA = c • sorted A hA := by
  refine eq_of_monotone_prod (sorted_monotone hcA)
    (fun i j hij => mul_le_mul_of_nonneg_left (sorted_monotone hA hij) hc.le) ?_
  rw [← charpoly_eq_prod_sorted hcA, charpoly_smul_eq_prod_sorted hA]
  rfl

/-- `bpP:p9:dict`: `Ω_j = 2 σ_j`.  For `n ≥ 2` and an admissible axis vector `a`, the sorted
eigenvalue list of `2 Q_h` (`Q_h = coeffs D a`, the matrix of Fej04r (36)--(37)) is `2 σ`, its
characteristic polynomial is `∏ (X - 2 σ_j)`, and every `σ_j` and every `2 σ_j` is negative; for
`n = 1`, `Q_h = 0`, `σ₁ = 0`, so the sorted list of `2 Q_h` and `Ω₁ = 2 σ₁` vanish. -/
theorem p9_dict :
    (∀ (n : ℕ) (D : Data n), 2 ≤ n → ∀ a ∈ axes n,
      (∀ h, sorted ((2 : ℝ) • coeffs D a) h = fun j => 2 * sigma D a j) ∧
      ((2 : ℝ) • coeffs D a).charpoly = ∏ j, (X - C (2 * sigma D a j)) ∧
      ∀ j, sigma D a j < 0 ∧ 2 * sigma D a j < 0) ∧
    (∀ (D : Data 1) (a : Vec 1), coeffs D a = 0 ∧
      (∀ h, sorted ((2 : ℝ) • coeffs D a) h = 0) ∧
      ∀ j, 2 * sigma D a j = 0) := by
  refine ⟨fun n D hn a ha => ⟨?_, ?_, fun j => ?_⟩, fun D a => ?_⟩
  · intro h
    rw [sorted_smul (coeffs_hermitian D a) h two_pos]
    rfl
  · exact charpoly_smul_eq_prod_sorted (coeffs_hermitian D a) 2
  · exact ⟨sigma_neg D hn ha j, by linarith [sigma_neg D hn ha j]⟩
  · refine ⟨coeffs_one D a, fun h => ?_, fun j => by rw [sigma_one D a j]; ring⟩
    rw [sorted_smul (coeffs_hermitian D a) h two_pos]
    funext j
    change (2 : ℝ) * sigma D a j = 0
    rw [sigma_one D a j]; ring

/-- `bpP:p9:dict` for the landed frozen frequency: the `Ω_j = 2 * p11c_sigma` fed to
`HasSecularBirkhoffForm` is the sorted eigenvalue list of `2 Q_h`, and every entry is negative. -/
theorem p9_dict_planar (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) :
    (∀ h, sorted ((2 : ℝ) • coeffs (p11cSecularData p hp) a) h =
        fun j => 2 * p11c_sigma p a j) ∧
      ∀ j, p11c_sigma p a j < 0 ∧ 2 * p11c_sigma p a j < 0 := by
  have hs := p11c_sigma_eq_sigma p hp ha
  obtain ⟨h1, -, h3⟩ := p9_dict.1 2 (p11cSecularData p hp) le_rfl a (p11c_axes_mem ha)
  rw [hs]
  exact ⟨h1, h3⟩

end SecularSpectrum

end KAM.Planetary

end
