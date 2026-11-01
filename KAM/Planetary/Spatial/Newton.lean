/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Field

/-!
# Newtonian reconstruction of spatial moving solutions (MAIN Lemma 1, `d = 3`)

Package LP-SP-MODEL, `LP:MAIN L1 (97–108)`; track LP, non-frozen; the statement surface is
proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

With `M = 1 + μ Σ ν_i`, `x_0 = −μ Σ ν_i q_i / M`, `x_i = x_0 + q_i`, `ẋ_0 = −μ Σ p_i`,
`ẋ_i = p_i/ν_i` (the frozen planar formulas with `m₀ = 1`, `Fin 3`):
`isSpatialNewtonSolutionOn_of_isSpatialMovingSolutionOn` says that a spatial moving solution with
`0 < ν_i` and `0 ≤ μ` reconstructs a Newtonian solution with masses `(1, μ ν_1, …, μ ν_n)`
(`G = 1`), Euclidean lengths, on the same time set.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary

variable {n : ℕ}

/-- Barycentric positions (star first, then the planets) from heliocentric `q`, with `m₀ = 1`. -/
def spatialBarycentricPositions (ν : Fin n → ℝ) (μ : ℝ) (q : Fin (n * 3) → ℝ) :
    Fin (n + 1) → (Fin 3 → ℝ) :=
  let x0 := (-μ / (1 + μ * ∑ i, ν i)) • ∑ i, ν i • bodyVector3 q i
  Fin.cons x0 (fun i => x0 + bodyVector3 q i)

/-- Barycentric velocities: actual planet momenta are `μ p`, total momentum zero. -/
def spatialBarycentricVelocities (ν : Fin n → ℝ) (μ : ℝ) (p : Fin (n * 3) → ℝ) :
    Fin (n + 1) → (Fin 3 → ℝ) :=
  Fin.cons ((-μ) • ∑ i, bodyVector3 p i) (fun i => (1 / ν i) • bodyVector3 p i)

/-- The masses `(1, μ ν_1, …, μ ν_n)`. -/
def spatialMasses (ν : Fin n → ℝ) (μ : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons 1 (fun i => μ * ν i)

/-- Finite-interval Newton equations in dimension three, with Euclidean lengths (`G = 1`). -/
def IsSpatialNewtonSolutionOn {N : ℕ} (mass : Fin N → ℝ) (J : Set ℝ)
    (Q V : ℝ → Fin N → (Fin 3 → ℝ)) : Prop :=
  (∀ t ∈ J, ∀ i j, i ≠ j → 0 < spaceLength (Q t j - Q t i)) ∧
  (∀ t ∈ J, ∀ i, HasDerivAt (fun s => Q s i) (V t i) t) ∧
  (∀ t ∈ J, ∀ i, HasDerivAt (fun s => V s i)
    (∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
      (mass j / spaceLength (Q t j - Q t i) ^ 3) • (Q t j - Q t i)) t)

section Barycentric

theorem spatialBarycentricPositions_succ_sub_zero (ν : Fin n → ℝ) (μ : ℝ) (q : Fin (n * 3) → ℝ)
    (i : Fin n) :
    spatialBarycentricPositions ν μ q i.succ - spatialBarycentricPositions ν μ q 0 =
      bodyVector3 q i := by
  simp [spatialBarycentricPositions]

theorem spatialBarycentricPositions_succ_sub_succ (ν : Fin n → ℝ) (μ : ℝ) (q : Fin (n * 3) → ℝ)
    (i j : Fin n) :
    spatialBarycentricPositions ν μ q j.succ - spatialBarycentricPositions ν μ q i.succ =
      bodyVector3 q j - bodyVector3 q i := by
  simp [spatialBarycentricPositions]

theorem spatialBarycentricPositions_zero (ν : Fin n → ℝ) (μ : ℝ) (q : Fin (n * 3) → ℝ) :
    spatialBarycentricPositions ν μ q 0 =
      (-μ / (1 + μ * ∑ i, ν i)) • ∑ i, ν i • bodyVector3 q i := by
  simp [spatialBarycentricPositions]

theorem spatialBarycentricVelocities_zero (ν : Fin n → ℝ) (μ : ℝ) (p : Fin (n * 3) → ℝ) :
    spatialBarycentricVelocities ν μ p 0 = (-μ) • ∑ i, bodyVector3 p i := by
  simp [spatialBarycentricVelocities]

theorem spatialBarycentricVelocities_succ (ν : Fin n → ℝ) (μ : ℝ) (p : Fin (n * 3) → ℝ)
    (i : Fin n) :
    spatialBarycentricVelocities ν μ p i.succ = (1 / ν i) • bodyVector3 p i := by
  simp [spatialBarycentricVelocities]

end Barycentric

section Reconstruction

variable {ν : Fin n → ℝ} {μ : ℝ}

private theorem sum_filter_ne_zero {E : Type*} [AddCommMonoid E] (F : Fin (n + 1) → E) :
    ∑ l ∈ Finset.univ.filter (fun l => l ≠ 0), F l = ∑ j : Fin n, F j.succ := by
  rw [Finset.sum_filter, Fin.sum_univ_succ]
  simp

private theorem sum_filter_ne_succ {E : Type*} [AddCommMonoid E] (F : Fin (n + 1) → E)
    (i : Fin n) :
    ∑ l ∈ Finset.univ.filter (fun l => l ≠ i.succ), F l =
      F 0 + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), F j.succ := by
  have h0 : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp [h0, Fin.succ_inj]

/-- The acceleration `(1/ν_i) ṗ_i` in the form of the force law. -/
private theorem smul_accel3 (c : ℝ) (ν : Fin n → ℝ) (i : Fin n) (hmi : ν i ≠ 0)
    (q : Fin n → Fin 3 → ℝ) :
    (1 / ν i) • (-(ν i) • spatialGKernel q i + (c * ν i) • spatialFKernel ν q i) =
      (-1 / spaceLength (q i) ^ 3) • q i +
        c • ∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
          (ν j / spaceLength (q j - q i) ^ 3) • (q j - q i) := by
  simp only [spatialGKernel, spatialFKernel, smul_add, smul_smul, Finset.smul_sum]
  congr 1
  · congr 1
    field_simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    field_simp

private theorem spaceLength_pos_barycentric {q : Fin (n * 3) → ℝ} (hq : SpatialNoCollision q)
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    0 < spaceLength (spatialBarycentricPositions ν μ q j -
      spatialBarycentricPositions ν μ q i) := by
  induction j using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => exact absurd rfl hij
    | succ i' =>
      rw [← neg_sub, spaceLength_neg, spatialBarycentricPositions_succ_sub_zero]
      exact hq.1 i'
  | succ j' =>
    induction i using Fin.cases with
    | zero =>
      rw [spatialBarycentricPositions_succ_sub_zero]
      exact hq.1 j'
    | succ i' =>
      rw [spatialBarycentricPositions_succ_sub_succ]
      exact hq.2 j' i' (fun h => hij (by rw [h]))

private theorem hasDerivAt_spatialBarycentricPositions (hm : ∀ i, 0 < ν i) (hμ : 0 ≤ μ)
    {z : ℝ → Phase (n * 3)} {t : ℝ} (hnc : SpatialNoCollision (z t).1)
    (hd : HasDerivAt z (hamiltonianVectorField (spatialHamiltonian ν μ) (z t)) t)
    (i : Fin (n + 1)) :
    HasDerivAt (fun s => spatialBarycentricPositions ν μ (z s).1 i)
      (spatialBarycentricVelocities ν μ (z t).2 i) t := by
  have hM : 0 ≤ ∑ i, ν i := Finset.sum_nonneg fun i _ => (hm i).le
  have hD : 1 + μ * ∑ i, ν i ≠ 0 := (add_pos_of_pos_of_nonneg one_pos (mul_nonneg hμ hM)).ne'
  have hbq : ∀ i : Fin n, HasDerivAt (fun s => bodyVector3 (z s).1 i)
      ((1 / ν i) • bodyVector3 (z t).2 i + μ • ∑ j, bodyVector3 (z t).2 j) t := fun i =>
    ((hasDerivAt_bodyVector3 hd i).1).congr_deriv
      (bodyVector3_hamiltonianVectorField_spatial_fst ν μ hnc i)
  have hx0 : HasDerivAt
      (fun s => (-μ / (1 + μ * ∑ i, ν i)) • ∑ i, ν i • bodyVector3 (z s).1 i)
      ((-μ) • ∑ j, bodyVector3 (z t).2 j) t := by
    have h := (HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (hbq i).const_smul (ν i))).const_smul (-μ / (1 + μ * ∑ i, ν i))
    refine h.congr_deriv ?_
    have hs : ∑ i, ν i • ((1 / ν i) • bodyVector3 (z t).2 i +
        μ • ∑ j, bodyVector3 (z t).2 j) =
        (1 + μ * ∑ i, ν i) • ∑ j, bodyVector3 (z t).2 j := by
      have h1 : ∀ i, ν i * (1 / ν i) = 1 := fun i => mul_one_div_cancel (hm i).ne'
      simp only [smul_add, smul_smul, Finset.sum_add_distrib, h1, one_smul]
      rw [← Finset.sum_smul, ← Finset.sum_mul, add_smul, one_smul, mul_comm μ]
    rw [hs, smul_smul]
    congr 1
    field_simp
  induction i using Fin.cases with
  | zero =>
    have hfun : (fun s => spatialBarycentricPositions ν μ (z s).1 0) =
        fun s => (-μ / (1 + μ * ∑ i, ν i)) • ∑ i, ν i • bodyVector3 (z s).1 i :=
      funext fun s => spatialBarycentricPositions_zero ν μ (z s).1
    rw [hfun, spatialBarycentricVelocities_zero]
    exact hx0
  | succ i =>
    have hfun : (fun s => spatialBarycentricPositions ν μ (z s).1 i.succ) =
        fun s => (-μ / (1 + μ * ∑ i, ν i)) • ∑ i, ν i • bodyVector3 (z s).1 i +
          bodyVector3 (z s).1 i := by
      funext s
      simp [spatialBarycentricPositions]
    rw [hfun, spatialBarycentricVelocities_succ]
    refine (hx0.add (hbq i)).congr_deriv ?_
    module

private theorem hasDerivAt_spatialBarycentricVelocities (hm : ∀ i, 0 < ν i)
    {z : ℝ → Phase (n * 3)} {t : ℝ} (hnc : SpatialNoCollision (z t).1)
    (hd : HasDerivAt z (hamiltonianVectorField (spatialHamiltonian ν μ) (z t)) t)
    (i : Fin (n + 1)) :
    HasDerivAt (fun s => spatialBarycentricVelocities ν μ (z s).2 i)
      (∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
        (spatialMasses ν μ j /
            spaceLength (spatialBarycentricPositions ν μ (z t).1 j -
              spatialBarycentricPositions ν μ (z t).1 i) ^ 3) •
          (spatialBarycentricPositions ν μ (z t).1 j -
            spatialBarycentricPositions ν μ (z t).1 i)) t := by
  induction i using Fin.cases with
  | zero =>
    have hfun : (fun s => spatialBarycentricVelocities ν μ (z s).2 0) =
        fun s => (-μ) • ∑ j, bodyVector3 (z s).2 j :=
      funext fun s => spatialBarycentricVelocities_zero ν μ (z s).2
    rw [hfun, sum_filter_ne_zero]
    refine ((HasDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => (hasDerivAt_bodyVector3 hd j).2)).const_smul (-μ)).congr_deriv ?_
    have hf : ∑ j, (μ * ν j) • spatialFKernel ν (fun k => bodyVector3 (z t).1 k) j = 0 := by
      calc _ = μ • ∑ j, ν j • spatialFKernel ν (fun k => bodyVector3 (z t).1 k) j := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun j _ => (smul_smul _ _ _).symm
        _ = 0 := by rw [sum_mass_smul_spatialFKernel, smul_zero]
    simp only [bodyVector3_hamiltonianVectorField_spatial_snd ν μ hnc, Finset.sum_add_distrib, hf,
      add_zero, spatialBarycentricPositions_succ_sub_zero, spatialMasses, Fin.cons_succ,
      spatialGKernel, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    have := (hm j).ne'
    field_simp
  | succ i =>
    have hfun : (fun s => spatialBarycentricVelocities ν μ (z s).2 i.succ) =
        fun s => (1 / ν i) • bodyVector3 (z s).2 i :=
      funext fun s => spatialBarycentricVelocities_succ ν μ (z s).2 i
    rw [hfun, sum_filter_ne_succ]
    refine ((hasDerivAt_bodyVector3 hd i).2.const_smul (1 / ν i)).congr_deriv ?_
    rw [bodyVector3_hamiltonianVectorField_spatial_snd ν μ hnc i,
      smul_accel3 μ ν i (hm i).ne',
      ← neg_sub (spatialBarycentricPositions ν μ (z t).1 i.succ)
        (spatialBarycentricPositions ν μ (z t).1 0),
      spatialBarycentricPositions_succ_sub_zero, spaceLength_neg]
    simp only [spatialBarycentricPositions_succ_sub_succ, spatialMasses, Fin.cons_zero,
      Fin.cons_succ, Finset.smul_sum, smul_smul, smul_neg, ← neg_smul]
    congr 1
    · congr 1
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      ring

/-- **Lemma 1, `d = 3`** (`LP:MAIN L1 (97–108)`): a spatial moving solution with `0 < ν_i` and
`0 ≤ μ` reconstructs a Newtonian solution with masses `(1, μ ν_1, …, μ ν_n)`. -/
theorem isSpatialNewtonSolutionOn_of_isSpatialMovingSolutionOn (hm : ∀ i, 0 < ν i) (hμ : 0 ≤ μ)
    {J : Set ℝ} {z : ℝ → Phase (n * 3)} (hz : IsSpatialMovingSolutionOn ν μ J z) :
    IsSpatialNewtonSolutionOn (spatialMasses ν μ) J
      (fun t => spatialBarycentricPositions ν μ (z t).1)
      (fun t => spatialBarycentricVelocities ν μ (z t).2) :=
  ⟨fun t ht i j hij => spaceLength_pos_barycentric (hz.2 t ht) i j hij,
    fun t ht i => hasDerivAt_spatialBarycentricPositions hm hμ (hz.2 t ht) (hz.1 t ht).2.2 i,
    fun t ht i => hasDerivAt_spatialBarycentricVelocities hm (hz.2 t ht) (hz.1 t ht).2.2 i⟩

end Reconstruction

end KAM.Planetary.Spatial

end
