/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Frequency
import KAM.Matrix.Inverse
import KAM.Matrix.Norms

/-!
# The Hessian inverse and the inverse frequency map

Blueprint Part 4, `bp:p4:hessian-inverse` and `bp:p4:inverse-freq`.

* `KAM.Head.hessian_inverse` (`bp:p4:hessian-inverse`): for `I ∈ B` and real `v`,
  `|v| ≤ L₊ |∇²h (ι I) v|`; the matrix `∇²h (ι I)` is invertible with real inverse and
  `|∇²h (ι I)⁻¹| ≤ L₊` in the row-sum norm (step `step:p4:hess-quotient`:
  `KAM.Head.norm_le_Lplus_mul_hessian_mulVec`; step `step:p4:hess-norm`:
  `KAM.Head.isUnit_map_ofReal_of_bound`, `KAM.Head.norm_inv_le_of_bound`).
* `KAM.Head.inverse_freq` (`bp:p4:inverse-freq`): the frequency map is injective on `closure B` with
  `L₊`-Lipschitz inverse; `I_ω = KAM.Head.invFreq h B ω` is the unique element of `B` with
  frequency `ω`, `|I_ω - I_ω'| ≤ L₊ |ω - ω'|`, `|ω| ≤ W_∞`, and `invFreq (∇h I) = I` on `B`
  (step `step:p4:invfreq-proof`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Head

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}

/-! ### Real matrices over `ℂ` -/

section RealMatrix

/-- A real matrix acts on `ι v` as `ι (A v)`. -/
theorem map_ofReal_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    A.map Complex.ofReal *ᵥ realInclusion n v = realInclusion n (A *ᵥ v) := by
  ext i
  exact (RingHom.map_mulVec Complex.ofRealHom A v i).symm

/-- `‖A ι v‖ = ‖A v‖` for a real matrix. -/
theorem norm_map_ofReal_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ‖A.map Complex.ofReal *ᵥ realInclusion n v‖ = ‖A *ᵥ v‖ := by
  rw [map_ofReal_mulVec, norm_realInclusion]

/-- Blueprint `step:p4:hess-norm` (invertibility): a real square matrix `A` with
`|v| ≤ L |A v|` is injective, hence invertible. -/
theorem isUnit_map_ofReal_of_bound {A : Matrix (Fin n) (Fin n) ℝ} {L : ℝ}
    (hbound : ∀ v : Fin n → ℝ, ‖v‖ ≤ L * ‖A.map Complex.ofReal *ᵥ realInclusion n v‖) :
    IsUnit (A.map Complex.ofReal) := by
  have hA : IsUnit A := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro v w hvw
    have h0 : A *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
    have h1 := hbound (v - w)
    rw [norm_map_ofReal_mulVec, h0, norm_zero, mul_zero] at h1
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  exact hA.map (Complex.ofRealHom.mapMatrix)

/-- Blueprint `step:p4:hess-norm` (the norm of the inverse): if `A` is invertible with real
inverse `B'` and `|v| ≤ L |A ι v|` for real `v`, then `|A⁻¹| ≤ L` in the row-sum norm. -/
theorem norm_inv_le_of_bound {A : Matrix (Fin n) (Fin n) ℂ} {B' : Matrix (Fin n) (Fin n) ℝ}
    {L : ℝ} (hL : 0 ≤ L) (hA : IsUnit A) (hinv : A⁻¹ = B'.map Complex.ofReal)
    (hbound : ∀ v : Fin n → ℝ, ‖v‖ ≤ L * ‖A *ᵥ realInclusion n v‖) : ‖A⁻¹‖ ≤ L := by
  refine (norm_le_iff_forall_rowSum hL).2 fun i => ?_
  -- the sign vector of row `i` of `B'`
  set w : Fin n → ℝ := fun j => if 0 ≤ B' i j then 1 else -1 with hw
  have hw1 : ‖w‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases hj : 0 ≤ B' i j <;> simp [hw, hj]
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  -- `u = B' w`
  set u : Fin n → ℝ := B' *ᵥ w with hu
  have hιu : realInclusion n u = A⁻¹ *ᵥ realInclusion n w := by
    rw [hinv, map_ofReal_mulVec]
  have hAu : A *ᵥ realInclusion n u = realInclusion n w := by
    rw [hιu, Matrix.mulVec_mulVec, hAinv, Matrix.one_mulVec]
  have hnu : ‖u‖ ≤ L := by
    refine (hbound u).trans ?_
    rw [hAu, norm_realInclusion]
    calc L * ‖w‖ ≤ L * 1 := mul_le_mul_of_nonneg_left hw1 hL
      _ = L := mul_one L
  have hui : u i = ∑ j, ‖A⁻¹ i j‖ := by
    rw [hu, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hinv, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs, hw]
    by_cases hj : 0 ≤ B' i j
    · simp [hj, abs_of_nonneg hj]
    · simp [hj, abs_of_neg (not_le.1 hj)]
  rw [← hui]
  calc u i ≤ |u i| := le_abs_self _
    _ = ‖u i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖u‖ := norm_le_pi_norm u i
    _ ≤ L := hnu

end RealMatrix

/-! ### Blueprint `bp:p4:hessian-inverse` -/

section Hessian

variable (hD : Data τ s₀ r₀ B h Lh)
include hD

/-- Blueprint `bp:p4:inverse-freq` / `step:p4:hess-quotient`: the nondegeneracy hypothesis with
`L₊` in place of `L_h`. -/
theorem norm_sub_le_Lplus_mul {I J : Fin n → ℝ} (hI : I ∈ closure B) (hJ : J ∈ closure B) :
    ‖I - J‖ ≤ Lplus Lh * ‖frequencyMap h I - frequencyMap h J‖ :=
  (hD.nondeg I hI J hJ).trans
    (mul_le_mul_of_nonneg_right (le_Lplus Lh) (norm_nonneg _))

/-- Blueprint `step:p4:hess-quotient`: for `I ∈ B` and real `v`, `|v| ≤ L₊ |∇²h (ι I) v|`. -/
theorem norm_le_Lplus_mul_hessian_mulVec {I : Fin n → ℝ} (hI : I ∈ B) (v : Fin n → ℝ) :
    ‖v‖ ≤ Lplus Lh * ‖hessian h (fun i => (I i : ℂ)) *ᵥ fun j => (v j : ℂ)‖ := by
  have hU : I ∈ realDomain B r₀ := closure_subset_realDomain hD.r₀_pos B (subset_closure hI)
  have hline : HasDerivAt (fun t : ℝ => I + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add I
  have hfd : HasFDerivAt (frequencyMap h) (fderiv ℝ (frequencyMap h) I) (I + (0 : ℝ) • v) := by
    simpa using (differentiableAt_frequencyMap hD hU).hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => frequencyMap h (I + t • v))
      (fderiv ℝ (frequencyMap h) I v) 0 := by
    have h := hfd.comp_hasDerivAt (0 : ℝ) hline
    exact h
  have hlim := (hγ.tendsto_slope_zero_right).norm.const_mul (Lplus Lh)
  have hevB : ∀ᶠ t in 𝓝[>] (0 : ℝ), I + t • v ∈ B := by
    have hcont : Continuous fun t : ℝ => I + t • v := by fun_prop
    exact eventually_nhdsWithin_of_eventually_nhds
      ((hD.isOpen.preimage hcont).mem_nhds (by simpa using hI))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖v‖ ≤ Lplus Lh * ‖t⁻¹ • (frequencyMap h (I + (0 + t) • v) -
        frequencyMap h (I + (0 : ℝ) • v))‖ := by
    filter_upwards [hevB, eventually_mem_nhdsWithin] with t htB ht
    have ht0 : 0 < t := ht
    have h1 := norm_sub_le_Lplus_mul hD (subset_closure htB) (subset_closure hI)
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le] at h1
    rw [zero_add, zero_smul, add_zero, norm_smul, norm_inv, Real.norm_of_nonneg ht0.le]
    calc ‖v‖ = t⁻¹ * (t * ‖v‖) := by field_simp
      _ ≤ t⁻¹ * (Lplus Lh * ‖frequencyMap h (I + t • v) - frequencyMap h I‖) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ht0.le)
      _ = _ := by ring
  have hlim' : ‖v‖ ≤ Lplus Lh * ‖fderiv ℝ (frequencyMap h) I v‖ := ge_of_tendsto hlim hev
  have h2 := fderiv_frequencyMap_eq_hessian hD hU v
  have h3 : ‖fderiv ℝ (frequencyMap h) I v‖ =
      ‖hessian h (fun i => (I i : ℂ)) *ᵥ fun j => (v j : ℂ)‖ := by
    rw [← h2]
    exact (norm_realInclusion (fderiv ℝ (frequencyMap h) I v)).symm
  rwa [h3] at hlim'

/-- The Hessian at a point of `U` is the complex form of a real matrix. -/
theorem hessian_eq_map_ofReal {I : Fin n → ℝ} (hI : I ∈ realDomain B r₀) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, hessian h (fun i => (I i : ℂ)) = A.map Complex.ofReal :=
  ⟨Matrix.of fun i j => (hessian h (fun i => (I i : ℂ)) i j).re, by
    ext i j
    exact (Complex.ext (by simp) (by simpa using hessian_im hD hI i j))⟩

/-- Blueprint `bp:p4:hessian-inverse`. -/
theorem hessian_inverse_at {I : Fin n → ℝ} (hI : I ∈ B) :
    (∀ v : Fin n → ℝ,
      ‖v‖ ≤ Lplus Lh * ‖hessian h (fun i => (I i : ℂ)) *ᵥ fun j => (v j : ℂ)‖) ∧
    IsUnit (hessian h (fun i => (I i : ℂ))).det ∧
    (∀ i j, ((hessian h (fun i => (I i : ℂ)))⁻¹ i j).im = 0) ∧
    ‖(hessian h (fun i => (I i : ℂ)))⁻¹‖ ≤ Lplus Lh := by
  have hU : I ∈ realDomain B r₀ := closure_subset_realDomain hD.r₀_pos B (subset_closure hI)
  have hbound := norm_le_Lplus_mul_hessian_mulVec hD hI
  obtain ⟨A, hA⟩ := hessian_eq_map_ofReal hD hU
  have hunit : IsUnit (hessian h (fun i => (I i : ℂ))) := by
    rw [hA]
    refine isUnit_map_ofReal_of_bound (L := Lplus Lh) fun v => ?_
    rw [← hA]
    exact hbound v
  obtain ⟨-, -, -, -, B', hB'⟩ := real_inverse_adjugate ⟨A, hA⟩ hunit
  refine ⟨hbound, (Matrix.isUnit_iff_isUnit_det _).1 hunit, fun i j => ?_,
    norm_inv_le_of_bound (zero_le_one.trans (one_le_Lplus Lh)) hunit hB' hbound⟩
  rw [hB']
  exact Complex.ofReal_im _

end Hessian

/-- Blueprint `bp:p4:hessian-inverse`. -/
theorem hessian_inverse (hD : Data τ s₀ r₀ B h Lh) : ∀ I ∈ B,
    (∀ v : Fin n → ℝ,
      ‖v‖ ≤ Lplus Lh * ‖hessian h (fun i => (I i : ℂ)) *ᵥ fun j => (v j : ℂ)‖) ∧
    IsUnit (hessian h (fun i => (I i : ℂ))).det ∧
    (∀ i j, ((hessian h (fun i => (I i : ℂ)))⁻¹ i j).im = 0) ∧
    ‖(hessian h (fun i => (I i : ℂ)))⁻¹‖ ≤ Lplus Lh :=
  fun _ hI => hessian_inverse_at hD hI

/-! ### Blueprint `bp:p4:inverse-freq` -/

/-- Blueprint `bp:p4:inverse-freq`, items (a)–(e) (step `step:p4:invfreq-proof`). -/
theorem inverse_freq (hD : Data τ s₀ r₀ B h Lh) :
    Set.InjOn (frequencyMap h) (closure B) ∧
    (∀ I ∈ closure B, ∀ J ∈ closure B,
      ‖I - J‖ ≤ Lplus Lh * ‖frequencyMap h I - frequencyMap h J‖) ∧
    (∀ ω ∈ frequencyMap h '' B, invFreq h B ω ∈ B ∧ frequencyMap h (invFreq h B ω) = ω ∧
      ‖ω‖ ≤ Winf s₀ r₀ B h) ∧
    (∀ ω ∈ frequencyMap h '' B, ∀ ω' ∈ frequencyMap h '' B,
      ‖invFreq h B ω - invFreq h B ω'‖ ≤ Lplus Lh * ‖ω - ω'‖) ∧
    ∀ I ∈ B, invFreq h B (frequencyMap h I) = I := by
  have hmem : ∀ ω ∈ frequencyMap h '' B, invFreq h B ω ∈ B ∧ frequencyMap h (invFreq h B ω) = ω :=
    fun ω hω => ⟨Function.invFunOn_mem hω, Function.invFunOn_eq hω⟩
  have hinj : Set.InjOn (frequencyMap h) (closure B) := by
    intro I hI J hJ heq
    have h1 := norm_sub_le_Lplus_mul hD hI hJ
    rw [heq, sub_self, norm_zero, mul_zero] at h1
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  refine ⟨hinj, fun I hI J hJ => norm_sub_le_Lplus_mul hD hI hJ, fun ω hω => ⟨(hmem ω hω).1,
    (hmem ω hω).2, ?_⟩, fun ω hω ω' hω' => ?_, fun I hI => ?_⟩
  · obtain ⟨I, hI, rfl⟩ := hω
    exact (freq_map hD).2.2.2.2.2.1 I hI
  · have h1 := norm_sub_le_Lplus_mul hD (subset_closure (hmem ω hω).1)
      (subset_closure (hmem ω' hω').1)
    rwa [(hmem ω hω).2, (hmem ω' hω').2] at h1
  · have hI' : frequencyMap h I ∈ frequencyMap h '' B := ⟨I, hI, rfl⟩
    exact hinj (subset_closure (hmem _ hI').1) (subset_closure hI) (hmem _ hI').2

end KAM.Head

end
