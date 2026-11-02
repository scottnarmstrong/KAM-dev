/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Field
public import KAM.Planetary.Spatial.Orbital
public import KAM.Planetary.AMD.AngularMomentum

/-!
# Exact angular momentum and the strong AMD, spatial (vector form)

Source: `LP:MAIN L3 (130–139)`, `d = 3`; track LP, non-frozen.

Conservation of the vector `L = Σ q_i × p_i` along `IsSpatialMovingSolutionOn` (the recoil term is
`μ P × P = 0`, central forces have no torque, pair forces cancel); `0 ≤ C`; `C < Λ_k ⇒ L ≠ 0`;
with `L̂ = L/|L|` the projections satisfy `Λ_i − C ≤ L_i · L̂`, the margin corollary, the identity
(13) `C(t) − C(s) = Σ (Λ_i(t) − Λ_i(s))`, `C = Σ (Λ_i − L_i·L̂)` and the deficit bound
`Σ Λ_i (1 − √(1 − e_i²)) ≤ C`.  All per-planet statements assume the negative-energy carrier
`SpatialNegativeEnergy ν z`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary
open scoped BigOperators

variable {n : ℕ}

/-! ### Conservation -/

/-- Product rule for the cross product. -/
theorem hasDerivAt_spaceCross {u w : ℝ → Fin 3 → ℝ} {u₀ w₀ : Fin 3 → ℝ} {t : ℝ}
    (hu : HasDerivAt u u₀ t) (hw : HasDerivAt w w₀ t) :
    HasDerivAt (fun s => spaceCross (u s) (w s))
      (spaceCross u₀ (w t) + spaceCross (u t) w₀) t := by
  rw [hasDerivAt_pi]
  intro k
  have hu0 := hasDerivAt_pi.1 hu 0
  have hu1 := hasDerivAt_pi.1 hu 1
  have hu2 := hasDerivAt_pi.1 hu 2
  have hw0 := hasDerivAt_pi.1 hw 0
  have hw1 := hasDerivAt_pi.1 hw 1
  have hw2 := hasDerivAt_pi.1 hw 2
  fin_cases k
  · refine ((hu1.mul hw2).sub (hu2.mul hw1)).congr_deriv ?_
    simp [spaceCross]; ring
  · refine ((hu2.mul hw0).sub (hu0.mul hw2)).congr_deriv ?_
    simp [spaceCross]; ring
  · refine ((hu0.mul hw1).sub (hu1.mul hw0)).congr_deriv ?_
    simp [spaceCross]; ring

theorem spaceCross_sum_right {ι : Type*} (s : Finset ι) (P : Fin 3 → ℝ) (f : ι → Fin 3 → ℝ) :
    spaceCross P (∑ i ∈ s, f i) = ∑ i ∈ s, spaceCross P (f i) := by
  simp only [spaceCross_eq_crossProduct]
  exact map_sum (crossProduct P) f s

theorem spaceCross_self_smul_right (c : ℝ) (q : Fin 3 → ℝ) : spaceCross q (c • q) = 0 := by
  rw [spaceCross_smul_right, spaceCross_self, smul_zero]

/-- Action–reaction for torques: `Σ_i ν_i q_i × f_i = 0`. -/
theorem sum_mass_smul_cross_spatialFKernel (ν : Fin n → ℝ) (q : Fin n → Fin 3 → ℝ) :
    ∑ i, ν i • spaceCross (q i) (spatialFKernel ν q i) = 0 := by
  set g : Fin n → Fin n → Fin 3 → ℝ :=
    fun i j => (ν i * (ν j / spaceLength (q j - q i) ^ 3)) • spaceCross (q i) (q j) with hg
  have hanti : ∀ i j, g j i = -g i j := by
    intro i j
    simp only [hg]
    rw [spaceLength_sub_comm (q i) (q j), spaceCross_anticomm (q j) (q i), smul_neg, neg_inj]
    congr 1
    ring
  have hS : ∀ i, ν i • spaceCross (q i) (spatialFKernel ν q i) = ∑ j, g i j := by
    intro i
    unfold spatialFKernel
    rw [spaceCross_sum_right, Finset.smul_sum]
    rw [Finset.sum_filter_of_ne]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hg, spaceCross_smul_right, spaceCross_sub_right, spaceCross_self, sub_zero,
        smul_smul]
    · intro j _ hj hji
      exact hj (by subst hji; simp [spaceCross_zero_right])
  simp only [hS]
  have : ∑ i, ∑ j, g i j = -∑ i, ∑ j, g i j := by
    calc ∑ i, ∑ j, g i j = ∑ j, ∑ i, g i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -g j i :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hanti j i
      _ = -∑ i, ∑ j, g i j := by simp [Finset.sum_neg_distrib]
  exact self_eq_neg.mp this

/-- The rate of change of `Σ q_i × p_i` along the Hamilton field vanishes at collision-free
points: recoil `μ P × P = 0`, central torque zero, pair torques cancel. -/
theorem sum_cross_rate_eq_zero (ν : Fin n → ℝ) (μ : ℝ) {z : Phase (n * 3)}
    (hz : SpatialNoCollision z.1) :
    ∑ i, (spaceCross (bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) z).1 i)
        (bodyVector3 z.2 i) +
      spaceCross (bodyVector3 z.1 i)
        (bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) z).2 i)) = 0 := by
  have hterm : ∀ i, spaceCross (bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) z).1 i)
        (bodyVector3 z.2 i) +
      spaceCross (bodyVector3 z.1 i)
        (bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) z).2 i) =
      μ • spaceCross (∑ j, bodyVector3 z.2 j) (bodyVector3 z.2 i) +
        μ • (ν i • spaceCross (bodyVector3 z.1 i)
          (spatialFKernel ν (fun j => bodyVector3 z.1 j) i)) := by
    intro i
    rw [bodyVector3_hamiltonianVectorField_spatial_fst ν μ hz,
      bodyVector3_hamiltonianVectorField_spatial_snd ν μ hz, spaceCross_add_left,
      spaceCross_smul_left, spaceCross_smul_left, spaceCross_self, spaceCross_add_right,
      spaceCross_smul_right, spaceCross_smul_right, spatialGKernel, spaceCross_self_smul_right]
    simp only [smul_zero, zero_add, smul_smul]
  simp only [hterm, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [← spaceCross_sum_right, spaceCross_self, sum_mass_smul_cross_spatialFKernel]
  simp

/-- Lemma 3, conservation: the vector `L` is constant along a spatial moving solution on an
order-connected set (`LP:MAIN L3 (130–139)`). -/
theorem angularMomentum3_const {ν : Fin n → ℝ} {μ : ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    {z : ℝ → Phase (n * 3)} (hz : IsSpatialMovingSolutionOn ν μ J z) :
    ∀ s ∈ J, ∀ t ∈ J, angularMomentum3 (z t) = angularMomentum3 (z s) := by
  intro s hs t ht
  ext k
  refine KAM.Planetary.interval_constancy hJ (f := fun s => angularMomentum3 (z s) k)
    (fun t ht => ?_) s hs t ht
  have hd := (hz.1 t ht).2.2
  have hnc := hz.2 t ht
  have hi : ∀ i : Fin n, HasDerivAt
      (fun s => spaceCross (bodyVector3 (z s).1 i) (bodyVector3 (z s).2 i))
      (spaceCross (bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) (z t)).1 i)
          (bodyVector3 (z t).2 i) +
        spaceCross (bodyVector3 (z t).1 i)
          (bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) (z t)).2 i)) t := by
    intro i
    obtain ⟨hq, hp⟩ := hasDerivAt_bodyVector3 hd i
    exact hasDerivAt_spaceCross hq hp
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hi i
  have hk := hasDerivAt_pi.1 hsum k
  refine hk.congr_deriv ?_
  rw [sum_cross_rate_eq_zero ν μ hnc]
  rfl

/-! ### The strong AMD -/

theorem spaceLength_zero : spaceLength (0 : Fin 3 → ℝ) = 0 := by
  simp [spaceLength_eq_zero_iff]

theorem spaceLength_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin 3 → ℝ) :
    spaceLength (∑ i ∈ s, f i) ≤ ∑ i ∈ s, spaceLength (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [spaceLength_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (spaceLength_add_le _ _).trans (by linarith)

theorem spaceDot_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin 3 → ℝ) (w : Fin 3 → ℝ) :
    spaceDot (∑ i ∈ s, f i) w = ∑ i ∈ s, spaceDot (f i) w := by
  simp only [spaceDot, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- The unit vector `L̂ = L / |L|`. -/
def spatialUnit (L : Fin 3 → ℝ) : Fin 3 → ℝ := (spaceLength L)⁻¹ • L

theorem spaceLength_spatialUnit {L : Fin 3 → ℝ} (hL : L ≠ 0) : spaceLength (spatialUnit L) = 1 := by
  have h := spaceLength_pos_iff.mpr hL
  unfold spatialUnit
  rw [spaceLength_smul, abs_of_pos (inv_pos.mpr h)]
  field_simp

theorem spaceDot_spatialUnit {L : Fin 3 → ℝ} (hL : L ≠ 0) :
    spaceDot L (spatialUnit L) = spaceLength L := by
  have h := spaceLength_pos_iff.mpr hL
  unfold spatialUnit
  rw [spaceDot_smul_right, ← spaceSq_eq_spaceDot, ← spaceLength_sq]
  field_simp

private theorem length_cross_le_action {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hz : SpatialNegativeEnergy ν z) (i : Fin n) :
    spaceLength (planetAngularMomentum3 z i) ≤ spatialKeplerAction ν z i :=
  (spatial_orbital_identities i (hz i)).2.2.2.2.2.2.1

private theorem action_nonneg {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hz : SpatialNegativeEnergy ν z) (i : Fin n) : 0 ≤ spatialKeplerAction ν z i :=
  (spatial_orbital_identities i (hz i)).2.1.le

private theorem length_total_le (z : Phase (n * 3)) :
    spaceLength (angularMomentum3 z) ≤ ∑ i, spaceLength (planetAngularMomentum3 z i) :=
  spaceLength_sum_le _ _

/-- Lemma 3, (13) identity (`LP:MAIN L3 (130–139)`): `C(t) − C(s) = Σ (Λ_i(t) − Λ_i(s))`. -/
theorem spatialStrongAMD_sub_eq_sum {ν : Fin n → ℝ} {μ : ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    {z : ℝ → Phase (n * 3)} (hz : IsSpatialMovingSolutionOn ν μ J z) {s t : ℝ} (hs : s ∈ J)
    (ht : t ∈ J) :
    spatialStrongAMD ν (z t) - spatialStrongAMD ν (z s) =
      ∑ i, (spatialKeplerAction ν (z t) i - spatialKeplerAction ν (z s) i) := by
  unfold spatialStrongAMD
  rw [angularMomentum3_const hJ hz s hs t ht, Finset.sum_sub_distrib]
  ring

/-- Lemma 3: `0 ≤ C` in the negative-energy region (`LP:MAIN L3 (130–139)`). -/
theorem spatialStrongAMD_nonneg {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hz : SpatialNegativeEnergy ν z) : 0 ≤ spatialStrongAMD ν z := by
  unfold spatialStrongAMD
  have h2 : ∑ i, spaceLength (planetAngularMomentum3 z i) ≤ ∑ i, spatialKeplerAction ν z i :=
    Finset.sum_le_sum fun i _ => length_cross_le_action hz i
  linarith [length_total_le z]

/-- Lemma 3: `C < Λ_k` for some `k` forces `L ≠ 0` (`LP:MAIN L3 (130–139)`). -/
theorem angularMomentum3_ne_zero_of_strongAMD_lt {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hz : SpatialNegativeEnergy ν z) {k : Fin n}
    (hk : spatialStrongAMD ν z < spatialKeplerAction ν z k) :
    angularMomentum3 z ≠ 0 := by
  intro h0
  have : spatialStrongAMD ν z = ∑ i, spatialKeplerAction ν z i := by
    unfold spatialStrongAMD; rw [h0, spaceLength_zero]; simp
  have hle : spatialKeplerAction ν z k ≤ ∑ i, spatialKeplerAction ν z i :=
    Finset.single_le_sum (fun i _ => action_nonneg hz i) (Finset.mem_univ k)
  linarith

/-- The individual projection `H_i = L_i · L̂` is at most `|L_i|` (for `L ≠ 0`). -/
theorem proj_le_length_cross {z : Phase (n * 3)} (hL : angularMomentum3 z ≠ 0) (i : Fin n) :
    spaceDot (planetAngularMomentum3 z i) (spatialUnit (angularMomentum3 z)) ≤
      spaceLength (planetAngularMomentum3 z i) := by
  have h := abs_spaceDot_le (planetAngularMomentum3 z i) (spatialUnit (angularMomentum3 z))
  rw [spaceLength_spatialUnit hL, mul_one] at h
  exact (le_abs_self _).trans h

/-- `Σ_i L_i · L̂ = |L|` for `L ≠ 0`. -/
theorem sum_proj_eq {z : Phase (n * 3)} (hL : angularMomentum3 z ≠ 0) :
    ∑ i, spaceDot (planetAngularMomentum3 z i) (spatialUnit (angularMomentum3 z)) =
      spaceLength (angularMomentum3 z) := by
  rw [← spaceDot_sum_left, ← angularMomentum3_eq_sum, spaceDot_spatialUnit hL]

/-- Lemma 3, (13): `C = Σ_i (Λ_i − L_i · L̂)` for `L ≠ 0` (`LP:MAIN L3 (130–139)`). -/
theorem spatialStrongAMD_eq_sum_sub_proj {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hL : angularMomentum3 z ≠ 0) :
    spatialStrongAMD ν z = ∑ i, (spatialKeplerAction ν z i -
      spaceDot (planetAngularMomentum3 z i) (spatialUnit (angularMomentum3 z))) := by
  unfold spatialStrongAMD
  rw [Finset.sum_sub_distrib, sum_proj_eq hL]

/-- Lemma 3, projection bound: for `L ≠ 0`, `Λ_i − C ≤ L_i · L̂` (`LP:MAIN L3 (130–139)`). -/
theorem action_sub_strongAMD_le_proj {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hz : SpatialNegativeEnergy ν z) (hL : angularMomentum3 z ≠ 0) (i : Fin n) :
    spatialKeplerAction ν z i - spatialStrongAMD ν z ≤
      spaceDot (planetAngularMomentum3 z i) (spatialUnit (angularMomentum3 z)) := by
  rw [spatialStrongAMD_eq_sum_sub_proj hL]
  have hle : spatialKeplerAction ν z i -
      spaceDot (planetAngularMomentum3 z i) (spatialUnit (angularMomentum3 z)) ≤
      ∑ j, (spatialKeplerAction ν z j -
        spaceDot (planetAngularMomentum3 z j) (spatialUnit (angularMomentum3 z))) := by
    refine Finset.single_le_sum (f := fun j => spatialKeplerAction ν z j -
      spaceDot (planetAngularMomentum3 z j) (spatialUnit (angularMomentum3 z)))
      (fun j _ => ?_) (Finset.mem_univ i)
    linarith [length_cross_le_action hz j, proj_le_length_cross hL j]
  linarith

/-- Lemma 3, margin corollary (`LP:MAIN L3 (130–139)`): if `C ≤ Λ_i − m` for all `i`, `0 < m`,
then `L ≠ 0` and `m ≤ L_i · L̂` for every `i`. -/
theorem proj_margin {ν : Fin n → ℝ} {z : Phase (n * 3)} (hz : SpatialNegativeEnergy ν z)
    {m : ℝ} (hm : 0 < m) (hC : ∀ i, spatialStrongAMD ν z ≤ spatialKeplerAction ν z i - m)
    (i : Fin n) :
    angularMomentum3 z ≠ 0 ∧
      m ≤ spaceDot (planetAngularMomentum3 z i) (spatialUnit (angularMomentum3 z)) := by
  have hne : angularMomentum3 z ≠ 0 :=
    angularMomentum3_ne_zero_of_strongAMD_lt hz (k := i) (by linarith [hC i])
  exact ⟨hne, by linarith [action_sub_strongAMD_le_proj hz hne i, hC i]⟩

/-- Lemma 3, (13) deficit bound (`LP:MAIN L3 (130–139)`): `Σ_i Λ_i (1 − √(1 − e_i²)) ≤ C`. -/
theorem sum_action_mul_eccDeficit_le_spatialStrongAMD {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hz : SpatialNegativeEnergy ν z) :
    ∑ i, spatialKeplerAction ν z i *
        (1 - Real.sqrt (1 - spaceLength (spatialKeplerEccVector ν z i) ^ 2)) ≤
      spatialStrongAMD ν z := by
  have hterm : ∀ i, spatialKeplerAction ν z i *
      (1 - Real.sqrt (1 - spaceLength (spatialKeplerEccVector ν z i) ^ 2)) =
        spatialKeplerAction ν z i - spaceLength (planetAngularMomentum3 z i) := fun i => by
    rw [(spatial_orbital_identities i (hz i)).2.2.2.2.2.1]; ring
  simp only [hterm]
  rw [Finset.sum_sub_distrib]
  unfold spatialStrongAMD
  linarith [length_total_le z]

end KAM.Planetary.Spatial

end
