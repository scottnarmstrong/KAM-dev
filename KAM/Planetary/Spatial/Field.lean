/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Model

/-!
# The Hamilton field of the spatial model in body blocks

Package LP-SP-MODEL, `LP:MAIN L1 (97–108)` (equation (10) and the Newton equations), `d = 3`;
track LP, non-frozen; the statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

`hamiltonianVectorField_spatial`: at a collision-free `z`, for body `i` and coordinate `c`,
`(X_H z).1 (i,c) = p_i^c/ν_i + μ Σ_j p_j^c` and
`(X_H z).2 (i,c) = (−ν_i g_i + μ ν_i f_i)^c`, with `g_i`, `f_i` the force kernels.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary

variable {n : ℕ}

private theorem hasFDerivAt_spatialH {z : Phase (n * 3)} (ν : Fin n → ℝ) (μ : ℝ)
    (hz : SpatialNoCollision z.1) :
    ∃ D : Phase (n * 3) →L[ℝ] ℝ, HasFDerivAt (spatialHamiltonian ν μ) D z ∧
      ∀ d : Phase (n * 3), D d =
        (∑ i, (spaceDot (bodyVector3 z.2 i) (bodyVector3 d.2 i) / ν i +
          ν i * ((spaceLength (bodyVector3 z.1 i) ^ 3)⁻¹ *
            spaceDot (bodyVector3 z.1 i) (bodyVector3 d.1 i)))) +
        μ * (spaceDot (∑ i, bodyVector3 z.2 i) (∑ i, bodyVector3 d.2 i) +
          ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), ν i * ν j *
            ((spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j) ^ 3)⁻¹ *
              spaceDot (bodyVector3 z.1 i - bodyVector3 z.1 j)
                (bodyVector3 d.1 i - bodyVector3 d.1 j))) := by
  have hv : ∀ i, posCLM3 i z ≠ 0 := fun i => spaceLength_pos_iff.mp (hz.1 i)
  have hw : ∀ i j, i ≠ j → (posCLM3 i - posCLM3 j) z ≠ 0 := fun i j hij =>
    spaceLength_pos_iff.mp (hz.2 i j hij)
  have hK := HasFDerivAt.fun_sum (u := Finset.univ)
    (A := fun i (x : Phase (n * 3)) => spaceSq (momCLM3 i x) * (2 * ν i)⁻¹ -
      ν i * (spaceLength (posCLM3 i x))⁻¹)
    (fun i _ => ((hasFDerivAt_spaceSq_comp (momCLM3 i) z).mul_const (2 * ν i)⁻¹).sub
      ((hasFDerivAt_inv_spaceLength_comp (posCLM3 i) (hv i)).const_mul (ν i)))
  have hP := HasFDerivAt.fun_sum (u := Finset.univ)
    (A := fun i (x : Phase (n * 3)) => ∑ j ∈ Finset.univ.filter (fun j => i < j),
      ν i * ν j * (spaceLength ((posCLM3 i - posCLM3 j) x))⁻¹)
    (fun i _ => HasFDerivAt.fun_sum (u := Finset.univ.filter (fun j => i < j))
      (A := fun j (x : Phase (n * 3)) =>
        ν i * ν j * (spaceLength ((posCLM3 i - posCLM3 j) x))⁻¹)
      (fun j hj => (hasFDerivAt_inv_spaceLength_comp (posCLM3 i - posCLM3 j)
        (hw i j (Finset.mem_filter.mp hj).2.ne)).const_mul (ν i * ν j)))
  have hS := hasFDerivAt_spaceSq_comp (∑ i, momCLM3 i : Phase (n * 3) →L[ℝ] (Fin 3 → ℝ)) z
  have hH := hK.add (((hS.mul_const (2 : ℝ)⁻¹).sub hP).const_mul μ)
  refine ⟨_, hH.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_), ?_⟩
  · simp only [Pi.add_apply, Pi.sub_apply, spatialHamiltonian, sum_apply,
      momCLM3_apply, posCLM3_apply, div_eq_mul_inv, sub_apply]
  · intro d
    simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply, sum_apply,
      spaceDotCLM_apply, momCLM3_apply, posCLM3_apply, smul_eq_mul, mul_neg, neg_mul,
      Finset.sum_neg_distrib, sub_neg_eq_add]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring_nf


/-! ### Hamilton equations in the body blocks -/

private theorem bodyVector3_single (i0 : Fin n) (c0 : Fin 3) (i : Fin n) :
    bodyVector3 (Pi.single (finProdFinEquiv (i0, c0)) (1 : ℝ) : Fin (n * 3) → ℝ) i =
      if i = i0 then Pi.single c0 1 else 0 := by
  ext k
  simp only [bodyVector3, Pi.single_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hi : i = i0 <;> by_cases hk : k = c0 <;> simp [hi, hk]

private theorem spaceDot_ite_single (v : Fin 3 → ℝ) (c0 : Fin 3) (p : Prop) [Decidable p] :
    spaceDot v (if p then Pi.single c0 1 else 0) = if p then v c0 else 0 := by
  split_ifs <;> simp [spaceDot, Pi.single_apply]

private theorem spaceDot_single (v : Fin 3 → ℝ) (c0 : Fin 3) :
    spaceDot v (Pi.single c0 1) = v c0 := by
  simp [spaceDot, Pi.single_apply]

private theorem sum_bodyVector3_single (i0 : Fin n) (c0 : Fin 3) :
    ∑ i, bodyVector3 (Pi.single (finProdFinEquiv (i0, c0)) (1 : ℝ) : Fin (n * 3) → ℝ) i =
      Pi.single c0 1 := by
  simp [bodyVector3_single]

/-- An antisymmetric kernel summed against `δ_{i i₀} - δ_{j i₀}` over ordered pairs. -/
private theorem sum_lt_mul_delta (w : Fin n → Fin n → ℝ) (hw : ∀ i j, w j i = -w i j)
    (i0 : Fin n) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      w i j * ((if i = i0 then 1 else 0) - (if j = i0 then 1 else 0)) = ∑ j, w i0 j := by
  set F : Fin n → Fin n → ℝ :=
    fun i j => w i j * ((if i = i0 then 1 else 0) - (if j = i0 then 1 else 0)) with hF
  have hsym : ∀ i j, F i j = F j i := by
    intro i j
    simp only [hF, hw i j]
    ring
  have hdiag : ∑ i, F i i = 0 := Finset.sum_eq_zero fun i _ => by simp [hF]
  have h := sum_sum_eq_diag_add_two_mul F hsym
  have h1 : ∑ i, ∑ j, w i j * (if i = i0 then (1 : ℝ) else 0) = ∑ j, w i0 j := by
    rw [Finset.sum_eq_single i0]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have h2 : ∑ i, ∑ j, w i j * (if j = i0 then (1 : ℝ) else 0) = -∑ j, w i0 j := by
    have : ∀ i, ∑ j, w i j * (if j = i0 then (1 : ℝ) else 0) = -w i0 i := by
      intro i
      rw [Finset.sum_eq_single i0]
      · simp [hw i0 i]
      · intro j _ hj
        simp [hj]
      · simp
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_neg_distrib]
  have hfull : ∑ i, ∑ j, F i j = 2 * ∑ j, w i0 j := by
    simp only [hF, mul_sub, Finset.sum_sub_distrib]
    rw [h1, h2]
    ring
  rw [hdiag, hfull] at h
  show ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), F i j = _
  linarith

/-- The pair kernel of the position derivative of the pair potential, antisymmetric in `(i, j)`. -/
private def pairW3 (ν : Fin n → ℝ) (q : Fin (n * 3) → ℝ) (c0 : Fin 3) (i j : Fin n) : ℝ :=
  ν i * ν j * ((spaceLength (bodyVector3 q i - bodyVector3 q j) ^ 3)⁻¹ *
    (bodyVector3 q i - bodyVector3 q j) c0)

private theorem pairW3_antisymm (ν : Fin n → ℝ) (q : Fin (n * 3) → ℝ) (c0 : Fin 3)
    (i j : Fin n) : pairW3 ν q c0 j i = -pairW3 ν q c0 i j := by
  unfold pairW3
  rw [spaceLength_sub_comm (bodyVector3 q j) (bodyVector3 q i)]
  simp only [Pi.sub_apply]
  ring

private theorem pair_sum_single3 (ν : Fin n → ℝ) (q : Fin (n * 3) → ℝ) (i0 : Fin n)
    (c0 : Fin 3) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), ν i * ν j *
      ((spaceLength (bodyVector3 q i - bodyVector3 q j) ^ 3)⁻¹ *
        spaceDot (bodyVector3 q i - bodyVector3 q j)
          (bodyVector3 (Pi.single (finProdFinEquiv (i0, c0)) (1 : ℝ) : Fin (n * 3) → ℝ) i -
            bodyVector3 (Pi.single (finProdFinEquiv (i0, c0)) (1 : ℝ) : Fin (n * 3) → ℝ) j)) =
      ∑ j, pairW3 ν q c0 i0 j := by
  rw [← sum_lt_mul_delta (pairW3 ν q c0) (pairW3_antisymm ν q c0) i0]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [bodyVector3_single, bodyVector3_single, spaceDot_sub_right, spaceDot_ite_single,
    spaceDot_ite_single]
  unfold pairW3
  by_cases hi : i = i0 <;> by_cases hj : j = i0 <;> simp [hi, hj]
  ring

private theorem mul_spatialFKernel_apply (ν : Fin n → ℝ) (q : Fin (n * 3) → ℝ) (i : Fin n)
    (j : Fin 3) :
    ν i * spatialFKernel ν (fun k => bodyVector3 q k) i j = -∑ k, pairW3 ν q j i k := by
  unfold spatialFKernel
  rw [Finset.sum_apply, Finset.sum_filter_of_ne, Finset.mul_sum, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun k _ => ?_
    unfold pairW3
    rw [spaceLength_sub_comm (bodyVector3 q i) (bodyVector3 q k)]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · intro k _ hk hki
    apply hk
    subst hki
    simp

/-- The Hamilton field of `H_μ` in the body blocks (index `finProdFinEquiv (i, c)`): equation (10)
and the force law (`LP:MAIN L1 (97–108)`). -/
theorem hamiltonianVectorField_spatial (ν : Fin n → ℝ) (μ : ℝ) {z : Phase (n * 3)}
    (hz : SpatialNoCollision z.1) (i : Fin n) (c : Fin 3) :
    (hamiltonianVectorField (spatialHamiltonian ν μ) z).1 (finProdFinEquiv (i, c)) =
        bodyVector3 z.2 i c / ν i + μ * ∑ j, bodyVector3 z.2 j c ∧
      (hamiltonianVectorField (spatialHamiltonian ν μ) z).2 (finProdFinEquiv (i, c)) =
        (-(ν i) • spatialGKernel (fun j => bodyVector3 z.1 j) i
          + (μ * ν i) • spatialFKernel ν (fun j => bodyVector3 z.1 j) i) c := by
  obtain ⟨D, hD, hDd⟩ := hasFDerivAt_spatialH ν μ hz
  constructor
  · show fderiv ℝ (spatialHamiltonian ν μ) z (0, Pi.single (finProdFinEquiv (i, c)) 1) = _
    rw [hD.fderiv, hDd]
    dsimp only
    rw [sum_bodyVector3_single]
    simp only [bodyVector3_single, bodyVector3_zero, spaceDot_zero_right, spaceDot_ite_single,
      spaceDot_single, mul_zero, add_zero, ite_div, zero_div, sub_self, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_apply]
  · show -fderiv ℝ (spatialHamiltonian ν μ) z (Pi.single (finProdFinEquiv (i, c)) 1, 0) = _
    rw [hD.fderiv, hDd]
    dsimp only
    rw [pair_sum_single3 ν z.1 i c]
    simp only [bodyVector3_single, bodyVector3_zero, spaceDot_zero_right, spaceDot_ite_single,
      mul_zero, zero_add, zero_div, Finset.sum_const_zero, mul_ite, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    have hf := mul_spatialFKernel_apply ν z.1 i c
    simp only [spatialGKernel, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-μ) * hf

/-- Pair-collision-free: also the Hamilton-field blocks as vectors. -/
theorem bodyVector3_hamiltonianVectorField_spatial_fst (ν : Fin n → ℝ) (μ : ℝ)
    {z : Phase (n * 3)} (hz : SpatialNoCollision z.1) (i : Fin n) :
    bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) z).1 i =
      (1 / ν i) • bodyVector3 z.2 i + μ • ∑ j, bodyVector3 z.2 j := by
  ext c
  have h := (hamiltonianVectorField_spatial ν μ hz i c).1
  show (hamiltonianVectorField (spatialHamiltonian ν μ) z).1 (finProdFinEquiv (i, c)) = _
  rw [h]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  ring

theorem bodyVector3_hamiltonianVectorField_spatial_snd (ν : Fin n → ℝ) (μ : ℝ)
    {z : Phase (n * 3)} (hz : SpatialNoCollision z.1) (i : Fin n) :
    bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) z).2 i =
      -(ν i) • spatialGKernel (fun j => bodyVector3 z.1 j) i +
        (μ * ν i) • spatialFKernel ν (fun j => bodyVector3 z.1 j) i := by
  ext c
  exact (hamiltonianVectorField_spatial ν μ hz i c).2

end KAM.Planetary.Spatial

end
