/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Standing
public import KAM.Torus.FrozenAgreement
public import KAM.Frozen.Defs.InvarianceError
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Defs.IsPrimaryOnStrip
import KAM.Apost.Exactness
import KAM.Head.CohUnique
import KAM.Head.DerivativeBounds
import KAM.Head.HamiltonianField

/-!
# Invariant tori with nonresonant frequency are Lagrangian

Blueprint Part 4, Lemma `bp:p4:lagrangian` and its proof steps. Let `K` be holomorphic
and primary on a strip `T_ρ` with `K(T_ρ) ⊆ 𝔇` and invariance error `E = 0` at a
Diophantine frequency `ω`. Then `Λ = DKᵀ Ω₀ DK` (`KAM.Torus.lagrangeMat`) vanishes on `T_ρ`.

* `step:p4:lag-regular`: `KAM.Head.lagrangeMat_regular`. `Λ` is holomorphic and `1`-periodic on
  `T_ρ`; both facts are already proved for Part 2
  (`KAM.Apost.Exactness.differentiableOn_lagrangeMat` and `KAM.Apost.periodic_lagrangeMat`).
* `step:p4:lag-exact`: `KAM.Head.avg_lagrangeMat_eq_zero`, the entrywise average `⟨Λ⟩ = 0`, which is
  `KAM.Apost.Exactness.avg_lagrangeMat` of `bp:p2:exactness`: `Λ_ij = ∂_i f_j - ∂_j f_i` for the
  action forms `f_j = v · ∂_j K₁`, and the average of a coordinate derivative of a periodic
  holomorphic function is zero (`bp:p1:averages`).
* `step:p4:lag-transport`: `KAM.Head.fderiv_lagrangeMat_omega`, `∂_ω Λ = 0`. Differentiating
  `X_𝐡(K) = DK ω` gives `∂_ω L = (DX_𝐡 ∘ K) L` (`KAM.Head.fderiv_tangentMat_omega`), and
  `DX_𝐡` is infinitesimally symplectic, `DX_𝐡ᵀ Ω₀ + Ω₀ DX_𝐡 = 0`
  (`KAM.Head.dotC_derivHamiltonian`, `KAM.Head.sqMat_transpose_mul_add_mul_eq_zero`), because
  `DX_𝐡 = J ∘ D²𝐡` with `D²𝐡` symmetric.
* `step:p4:lag-unique`: the body of `KAM.Head.lagrangian`, which applies the adapter
  `KAM.Head.coh_unique_zero` (`KAM/Head/CohUnique.lean`) to every entry of `Λ`.

Two hypotheses of the blueprint statement are not used by this proof: `ε ≤ 1` and the boundedness
of `DK`. The average step needs no bound, and
`coh_unique_zero` applies on `T_ρ` itself, without a loss of strip width. They stay in the
statement, which is the literal one of the blueprint.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology KAM.Torus

namespace KAM.Head

variable {n : ℕ}

/-! ### Algebra of the Hamiltonian vector field -/

/-- A linear form on `ℂⁿ × ℂⁿ` is determined by its values on the basis vectors. -/
theorem clm_prod_apply_eq_sum (ℓ : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ)
    (u : (Fin n → ℂ) × (Fin n → ℂ)) :
    ℓ u = ∑ i, u.1 i * ℓ (Pi.single i 1, 0) + ∑ i, u.2 i * ℓ (0, Pi.single i 1) := by
  have h1 : u = ((∑ i, u.1 i • (Pi.single i 1 : Fin n → ℂ)), (0 : Fin n → ℂ)) +
      ((0 : Fin n → ℂ), (∑ i, u.2 i • (Pi.single i 1 : Fin n → ℂ))) := by
    ext j <;> simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h1]
  rw [map_add, show ((∑ i, u.1 i • (Pi.single i 1 : Fin n → ℂ)), (0 : Fin n → ℂ)) =
      ∑ i, u.1 i • ((Pi.single i 1 : Fin n → ℂ), (0 : Fin n → ℂ)) by
        ext j <;> simp [Finset.sum_apply, Prod.fst_sum, Prod.snd_sum],
    show ((0 : Fin n → ℂ), (∑ i, u.2 i • (Pi.single i 1 : Fin n → ℂ))) =
      ∑ i, u.2 i • ((0 : Fin n → ℂ), (Pi.single i 1 : Fin n → ℂ)) by
        ext j <;> simp [Finset.sum_apply, Prod.fst_sum, Prod.snd_sum]]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- The second derivative of a function holomorphic on an open set is symmetric
(`bp:p1:holomorphic-regularity`). -/
theorem fderiv_fderiv_symm {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} (h𝔅 : IsOpen 𝔅)
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : DifferentiableOn ℂ φ 𝔅)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ 𝔅) (u w : (Fin n → ℂ) × (Fin n → ℂ)) :
    fderiv ℂ (fderiv ℂ φ) z u w = fderiv ℂ (fderiv ℂ φ) z w u := by
  have hD : DifferentiableAt ℂ (fderiv ℂ φ) z :=
    (differentiableOn_fderiv_of_isOpen h𝔅 hφ).differentiableAt (h𝔅.mem_nhds hz)
  have happly : ∀ a t : (Fin n → ℂ) × (Fin n → ℂ),
      fderiv ℂ (fun x => fderiv ℂ φ x a) z t = fderiv ℂ (fderiv ℂ φ) z t a := by
    intro a t
    rw [fderiv_clm_apply hD (differentiableAt_const a)]
    simp
  have h := fderiv_apply_comm_of_differentiableOn h𝔅 hφ hz u w
  rw [happly w u, happly u w] at h
  exact h

/-- Step `step:p4:lag-transport` (symplectic part): `X_φ = J ∘ Dφ` is infinitesimally symplectic,
`⟨DX_φ u, w⟩ + ⟨u, DX_φ w⟩ = 0` for `⟨a, b⟩ = a · Ω₀ b`, because `D²φ` is symmetric. -/
theorem dotC_derivHamiltonian {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} (h𝔅 : IsOpen 𝔅)
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : DifferentiableOn ℂ φ 𝔅)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ 𝔅) (u w : (Fin n → ℂ) × (Fin n → ℂ)) :
    dotℂ (fderiv ℂ (hamiltonianVectorFieldℂ φ) z u) (omegaZero w) +
      dotℂ u (omegaZero (fderiv ℂ (hamiltonianVectorFieldℂ φ) z w)) = 0 := by
  rw [fderiv_hamiltonianVectorField h𝔅 hφ hz]
  have hu := clm_prod_apply_eq_sum (fderiv ℂ (fderiv ℂ φ) z u) w
  have hw := clm_prod_apply_eq_sum (fderiv ℂ (fderiv ℂ φ) z w) u
  have hs := fderiv_fderiv_symm h𝔅 hφ hz u w
  simp only [ContinuousLinearMap.comp_apply, hamJ_apply, dotℂ, omegaZero, Pi.neg_apply]
  rw [hs] at hu
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_mul, mul_neg, neg_neg,
    mul_comm] at hu hw ⊢
  linear_combination hu - hw

/-- A square matrix whose bilinear form `x ⬝ᵥ M y` vanishes is zero. -/
theorem matrix_eq_zero_of_dotProduct_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (h : ∀ x y : ι → ℂ, x ⬝ᵥ (M *ᵥ y) = 0) : M = 0 := by
  ext s t
  simpa [Matrix.mulVec_single_one, dotProduct_single] using h (Pi.single s 1) (Pi.single t 1)

/-- A linear map `U` of `ℂⁿ × ℂⁿ` with `⟨U u, w⟩ + ⟨u, U w⟩ = 0` has the matrix identity
`Uᵀ Ω₀ + Ω₀ U = 0`. -/
theorem sqMat_transpose_mul_add_mul_eq_zero
    (U : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ))
    (hU : ∀ u w, dotℂ (U u) (omegaZero w) + dotℂ u (omegaZero (U w)) = 0) :
    (sqMat U)ᵀ * omegaZeroMatrix n + omegaZeroMatrix n * sqMat U = 0 := by
  refine matrix_eq_zero_of_dotProduct_mulVec _ fun x y => ?_
  obtain ⟨u, rfl⟩ := (sumVec n).surjective x
  obtain ⟨w, rfl⟩ := (sumVec n).surjective y
  rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, sqMat_mulVec, sqMat_mulVec,
    ← sumVec_omegaZero, ← sumVec_omegaZero]
  simpa only [dotℂ_eq_dotProduct_sumVec] using hU u w

/-! ### Step `step:p4:lag-transport`: `Λ` is constant along `ω` -/

/-- The derivative of the column `y ↦ DK(y) e_t` is the column `t` of the derivative of the
matrix `L = DK`. -/
theorem sumVec_fderiv_fderiv_apply {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {θ : Fin n → ℂ} (hL : DifferentiableAt ℂ (tangentMat K) θ) (t : Fin n) (v : Fin n → ℂ) :
    sumVec n (fderiv ℂ (fun y => fderiv ℂ K y (Pi.single t 1)) θ v) =
      fun s => fderiv ℂ (tangentMat K) θ v s t := by
  rw [← fderiv_sumVec_apply]
  have h : (fun y => sumVec n (fderiv ℂ K y (Pi.single t 1))) = fun y s => tangentMat K y s t :=
    funext fun y => funext fun s => (tangentMat_apply K y s t).symm
  rw [h, fderiv_pi (fun s => hL.matrix_apply s t)]
  ext s
  simp only [ContinuousLinearMap.pi_apply, fderiv_matrix_apply hL]

/-- Differentiating the invariance equation `X_φ(K) = DK ω` on `T_ρ` in a direction `e_t` gives
`∂_ω L = (DX_φ ∘ K) L`, by the symmetry of `D²K`. -/
theorem fderiv_tangentMat_omega {ρ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n ρ)) {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (h𝔅 : IsOpen 𝔅) {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : DifferentiableOn ℂ φ 𝔅)
    (hKB : ∀ θ ∈ complexStrip n ρ, K θ ∈ 𝔅) {ω : Fin n → ℝ}
    (hE : ∀ θ ∈ complexStrip n ρ, invarianceError φ K ω θ = 0) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) :
    fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ)) = linMat φ K θ * tangentMat K θ := by
  have hU : IsOpen (complexStrip n ρ) := isOpen_complexStrip n ρ
  have hθn : complexStrip n ρ ∈ nhds θ := hU.mem_nhds hθ
  have hL : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt hθn
  have hKθ : DifferentiableAt ℂ K θ := hK.differentiableAt hθn
  have hX : DifferentiableAt ℂ (hamiltonianVectorFieldℂ φ) (K θ) :=
    (differentiableOn_hamiltonianVectorField h𝔅 hφ).differentiableAt (h𝔅.mem_nhds (hKB θ hθ))
  ext s t
  have h1 := congrFun (sumVec_fderiv_fderiv_apply hL t (fun l => (ω l : ℂ))) s
  rw [← h1, fderiv_apply_comm_of_differentiableOn hU hK hθ]
  have h2 : (fun x => fderiv ℂ K x (fun l => (ω l : ℂ))) =ᶠ[nhds θ]
      fun x => hamiltonianVectorFieldℂ φ (K x) := by
    filter_upwards [hθn] with x hx
    have := hE x hx
    rw [invarianceError, sub_eq_zero] at this
    exact this.symm
  have h4 : fderiv ℂ (fun x => hamiltonianVectorFieldℂ φ (K x)) θ =
      (fderiv ℂ (hamiltonianVectorFieldℂ φ) (K θ)).comp (fderiv ℂ K θ) :=
    (hX.hasFDerivAt.comp θ hKθ.hasFDerivAt).fderiv
  rw [h2.fderiv_eq, h4, ContinuousLinearMap.comp_apply]
  have h3 := congrFun (sqMat_mulVec (fderiv ℂ (hamiltonianVectorFieldℂ φ) (K θ))
    (fderiv ℂ K θ (Pi.single t 1))) s
  have h5 : sumVec n (fderiv ℂ K θ (Pi.single t 1)) = fun r => tangentMat K θ r t :=
    funext fun r => (tangentMat_apply K θ r t).symm
  rw [h5] at h3
  rw [← h3]
  rfl

/-- Blueprint `step:p4:lag-transport`. Let `φ` be holomorphic on an open set `𝔅`, and let `K` be
holomorphic on `T_ρ` with `K(T_ρ) ⊆ 𝔅` and `X_φ(K) = DK ω` on `T_ρ`. Then `∂_ω Λ = 0` on `T_ρ`
for `Λ = Lᵀ Ω₀ L`: with `A = DX_φ ∘ K`,
`∂_ω Λ = (A L)ᵀ Ω₀ L + Lᵀ Ω₀ A L = Lᵀ (Aᵀ Ω₀ + Ω₀ A) L = 0`. -/
theorem fderiv_lagrangeMat_omega {ρ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n ρ)) {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (h𝔅 : IsOpen 𝔅) {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : DifferentiableOn ℂ φ 𝔅)
    (hKB : ∀ θ ∈ complexStrip n ρ, K θ ∈ 𝔅) {ω : Fin n → ℝ}
    (hE : ∀ θ ∈ complexStrip n ρ, invarianceError φ K ω θ = 0) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) :
    fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ)) = 0 := by
  have hθn : complexStrip n ρ ∈ nhds θ := (isOpen_complexStrip n ρ).mem_nhds hθ
  have hL : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt hθn
  have hω := fderiv_tangentMat_omega hK h𝔅 hφ hKB hE hθ
  have hsymp := sqMat_transpose_mul_add_mul_eq_zero
    (fderiv ℂ (hamiltonianVectorFieldℂ φ) (K θ))
    fun u w => dotC_derivHamiltonian h𝔅 hφ (hKB θ hθ) u w
  have hlam : lagrangeMat K =
      fun y => ((tangentMat K y)ᵀ * omegaZeroMatrix n) * tangentMat K y := rfl
  rw [hlam, fderiv_matrix_mul_apply (hL.matrix_transpose.matrix_mul (differentiableAt_const _)) hL,
    fderiv_matrix_mul_const_apply hL.matrix_transpose, fderiv_matrix_transpose_apply, hω]
  have : (linMat φ K θ)ᵀ * omegaZeroMatrix n + omegaZeroMatrix n * linMat φ K θ = 0 := hsymp
  calc _ = (tangentMat K θ)ᵀ * ((linMat φ K θ)ᵀ * omegaZeroMatrix n +
        omegaZeroMatrix n * linMat φ K θ) * tangentMat K θ := by
          simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [this]; simp

/-! ### Steps `step:p4:lag-regular` and `step:p4:lag-exact` -/

/-- Blueprint `step:p4:lag-regular`: for `K` holomorphic and primary on `T_ρ`, `Λ = DKᵀ Ω₀ DK` is
holomorphic and `1`-periodic on `T_ρ` (`DK` is holomorphic by `bp:p1:holomorphic-regularity`, and
periodic because `K(θ + e_i) = K(θ) + (e_i, 0)`). -/
theorem lagrangeMat_regular {ρ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n ρ)) (hKp : IsPrimaryOnStrip K ρ) :
    DifferentiableOn ℂ (lagrangeMat K) (complexStrip n ρ) ∧ IsPeriodicOn (lagrangeMat K) ρ :=
  ⟨KAM.Apost.Exactness.differentiableOn_lagrangeMat hK, KAM.Apost.periodic_lagrangeMat hKp⟩

/-- Blueprint `step:p4:lag-exact`: for `K` holomorphic and primary on `T_ρ` (`ρ > 0`), the
entrywise average of `Λ = DKᵀ Ω₀ DK` vanishes. Each entry is `∂_i f_j - ∂_j f_i` for the
holomorphic periodic action forms `f_j = v · ∂_j K₁`, by the symmetry of `D²K`; this is
`bp:p2:exactness` (first item). -/
theorem avg_lagrangeMat_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n ρ)) (hKp : IsPrimaryOnStrip K ρ) :
    avg (lagrangeMat K) = 0 :=
  KAM.Apost.Exactness.avg_lagrangeMat hρ hK hKp

/-! ### The lemma -/

section Lagrangian

variable {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε γ : ℝ}

/-- Blueprint `bp:p4:lagrangian`: `Λ = DKᵀ Ω₀ DK` (`KAM.Torus.lagrangeMat`) vanishes. -/
theorem lagrangian (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε) (hε : ε ≤ 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hγ : 0 < γ) {ω : Fin n → ℝ} (hω : IsDiophantine γ τ ω)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n ρ)) (hKp : IsPrimaryOnStrip K ρ)
    (hK𝔇 : ∀ θ ∈ complexStrip n ρ, K θ ∈ domainD n s₀ r₀ B)
    (hDK : ∃ A : ℝ, ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K θ‖ ≤ A)
    (hE : ∀ θ ∈ complexStrip n ρ, invarianceError (hbold h f) K ω θ = 0) :
    ∀ θ ∈ complexStrip n ρ, lagrangeMat K θ = 0 := by
  -- `ε ≤ 1` and the boundedness of `DK` are statement hypotheses that this proof does not use
  have _ := hε
  have _ := hDK
  have hH : DifferentiableOn ℂ (hbold h f) (domainD n s₀ r₀ B) :=
    (differentiableOn_hbold hD.s₀_pos hD.r₀_pos hD.holo hP.holo).mono
      (domainD_subset_domainD' n hD.s₀_pos hD.r₀_pos B)
  have h𝔇 : IsOpen (domainD n s₀ r₀ B) := isOpen_domainD n s₀ r₀ B
  obtain ⟨hΛ, hΛper⟩ := lagrangeMat_regular hK hKp
  have havg := avg_lagrangeMat_eq_zero hρ hK hKp
  intro θ hθ
  ext i j
  -- step `step:p4:lag-unique`: apply the uniqueness adapter to the entry `Λ_ij`
  have key := coh_unique_zero (r := ρ) (w := fun θ => lagrangeMat K θ i j) hρ hγ hω
    ((differentiableOn_matrix_iff_entries.1 hΛ) i j)
    (fun k z hz => by simpa using congrFun (congrFun (hΛper k z hz) i) j)
    ((torusAverage_matrix_apply (KAM.Apost.Exactness.continuous_real_of_differentiableOn hρ hΛ)
      i j).symm.trans (congrFun (congrFun havg i) j))
    (fun θ hθ => by
      rw [fderiv_matrix_apply (hΛ.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ)) i j,
        fderiv_lagrangeMat_omega hK h𝔇 hH hK𝔇 hE hθ]
      rfl) θ hθ
  simpa using key

end Lagrangian

end KAM.Head

end
