/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Vector
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Iso.Defs.IsHamiltonianSolutionOn

/-!
# The exact spatial model (dimension three)

Package LP-SP-MODEL, `LP:MAIN §1 (1) (17–25)` with `d = 3`; track LP, non-frozen; the statement
surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

* `spatialHamiltonian ν μ z = Σ_i (|p_i|²/(2ν_i) − ν_i/|q_i|)
  + μ (|Σ_i p_i|²/2 − Σ_{i<j} ν_iν_j/|q_i − q_j|)`
  (MAIN (1), literally; no totalization).
* `SpatialNoCollision q`: `q_i ≠ 0` and `q_i ≠ q_j` (positive Euclidean lengths).
* `IsSpatialMovingSolutionOn ν μ J z`: the frozen differentiability-guarded Hamiltonian ODE on the
  full action domain together with collision exclusion, the pattern of the frozen planar
  `IsMovingSolutionOn`; `SpatialMovingUniqueOn` is the pattern of the frozen `MovingUniqueOn`.
* force kernels `spatialGKernel`, `spatialFKernel`.

Also: the collision-free domain is open and the Hamiltonian is real analytic on it.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary

variable {n : ℕ}

/-- The exact spatial Hamiltonian `H_μ` (`LP:MAIN §1 (1)`, `d = 3`): positions `q_i` and scaled
canonical momenta `p_i` in `Phase (n * 3)`, masses `m_i = μ ν_i`, central Kepler parameter one. -/
def spatialHamiltonian (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) : ℝ :=
  (∑ i, (spaceSq (bodyVector3 z.2 i) / (2 * ν i) - ν i / spaceLength (bodyVector3 z.1 i))) +
    μ * (spaceSq (∑ i, bodyVector3 z.2 i) / 2 -
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ν i * ν j / spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j))

/-- The open physical domain of `H_μ`: no planet at the star and no two planets together. -/
def SpatialNoCollision (q : Fin (n * 3) → ℝ) : Prop :=
  (∀ i, 0 < spaceLength (bodyVector3 q i)) ∧
  (∀ i j, i ≠ j → 0 < spaceLength (bodyVector3 q i - bodyVector3 q j))

/-- A genuine spatial moving-Sun solution on `J`: the frozen differentiability-guarded Hamiltonian
ODE for `H_μ` together with collision exclusion (`LP:MAIN §1 (1)`). -/
def IsSpatialMovingSolutionOn (ν : Fin n → ℝ) (μ : ℝ) (J : Set ℝ)
    (z : ℝ → Phase (n * 3)) : Prop :=
  KAM.Iso.IsHamiltonianSolutionOn (spatialHamiltonian ν μ) Set.univ J z ∧
    ∀ t ∈ J, SpatialNoCollision (z t).1

/-- Agreement with every other local spatial solution on its overlap with the certified interval
(the pattern of the frozen planar `MovingUniqueOn`). -/
def SpatialMovingUniqueOn (ν : Fin n → ℝ) (μ : ℝ) (J : Set ℝ)
    (z : ℝ → Phase (n * 3)) : Prop :=
  ∀ (U : Set ℝ) (w : ℝ → Phase (n * 3)), IsOpen U → Convex ℝ U → 0 ∈ U →
    w 0 = z 0 → IsSpatialMovingSolutionOn ν μ U w → ∀ t ∈ U ∩ J, w t = z t

/-- Force kernel of the star on a planet: `g_i = |q_i|⁻³ q_i`. -/
def spatialGKernel (q : Fin n → Fin 3 → ℝ) (i : Fin n) : Fin 3 → ℝ :=
  ((spaceLength (q i)) ^ 3)⁻¹ • q i

/-- Force kernel of the other planets on planet `i`:
`f_i = Σ_{j ≠ i} ν_j |q_j − q_i|⁻³ (q_j − q_i)`. -/
def spatialFKernel (ν : Fin n → ℝ) (q : Fin n → Fin 3 → ℝ) (i : Fin n) : Fin 3 → ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), (ν j / spaceLength (q j - q i) ^ 3) • (q j - q i)

/-- The collision-free phase points. -/
def spatialCollisionFreeDomain (n : ℕ) : Set (Phase (n * 3)) := {z | SpatialNoCollision z.1}

/-! ### Pair sums -/

/-- A symmetric double sum is its diagonal plus twice the sum over ordered pairs `i < j`. -/
theorem sum_sum_eq_diag_add_two_mul (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j =
      ∑ i, f i i + 2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j := by
  have hsplit : ∀ i, ∑ j, f i j = f i i + ∑ j, (if i < j then f i j else 0) +
      ∑ j, (if j < i then f i j else 0) := by
    intro i
    have h3 : ∀ j, f i j = (if j = i then f i j else 0) + (if i < j then f i j else 0) +
        (if j < i then f i j else 0) := by
      intro j
      rcases lt_trichotomy i j with h | h | h
      · simp [h, h.ne', not_lt.mpr h.le]
      · subst h; simp
      · simp [h, h.ne, not_lt.mpr h.le]
    calc ∑ j, f i j = ∑ j, ((if j = i then f i j else 0) + (if i < j then f i j else 0) +
          (if j < i then f i j else 0)) := Finset.sum_congr rfl fun j _ => h3 j
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; simp
  have hswap : ∑ i, ∑ j, (if j < i then f i j else 0) =
      ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [hf i j]
  simp only [hsplit, Finset.sum_add_distrib, hswap, Finset.sum_filter]
  ring

/-- `|Σ v_i|² = Σ |v_i|² + 2 Σ_{i<j} v_i · v_j`. -/
theorem spaceSq_sum (v : Fin n → Fin 3 → ℝ) :
    spaceSq (∑ i, v i) =
      ∑ i, spaceSq (v i) +
        2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), spaceDot (v i) (v j) := by
  rw [spaceSq_sum_eq_sum_sum, sum_sum_eq_diag_add_two_mul (fun i j => spaceDot (v i) (v j))
    (fun i j => spaceDot_comm _ _)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [spaceSq_eq_spaceDot]

/-- Action–reaction: `Σ_i ν_i f_i = 0` (no collision hypothesis is needed). -/
theorem sum_mass_smul_spatialFKernel (ν : Fin n → ℝ) (q : Fin n → Fin 3 → ℝ) :
    ∑ i, ν i • spatialFKernel ν q i = 0 := by
  set g : Fin n → Fin n → Fin 3 → ℝ :=
    fun i j => (ν i * (ν j / spaceLength (q j - q i) ^ 3)) • (q j - q i) with hg
  have hanti : ∀ i j, g j i = -g i j := by
    intro i j
    simp only [hg]
    rw [spaceLength_sub_comm (q i) (q j), ← neg_sub (q j) (q i), smul_neg, neg_inj]
    congr 1
    ring
  have hS : ∑ i, ν i • spatialFKernel ν q i = ∑ i, ∑ j, g i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold spatialFKernel
    rw [Finset.smul_sum]
    rw [Finset.sum_filter_of_ne]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hg, mul_smul]
    · intro j _ hj hji
      exact hj (by subst hji; simp)
  rw [hS]
  have : ∑ i, ∑ j, g i j = -∑ i, ∑ j, g i j := by
    calc ∑ i, ∑ j, g i j = ∑ j, ∑ i, g i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -g j i :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hanti j i
      _ = -∑ i, ∑ j, g i j := by simp [Finset.sum_neg_distrib]
  exact self_eq_neg.mp this

/-! ### The collision-free domain and analyticity -/

theorem hasFDerivAt_spaceSq_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] (Fin 3 → ℝ)) (z : E) :
    HasFDerivAt (fun x => spaceSq (L x)) (((2 : ℝ) • spaceDotCLM (L z)).comp L) z :=
  (hasFDerivAt_spaceSq (L z)).comp z L.hasFDerivAt

theorem hasFDerivAt_inv_spaceLength_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] (Fin 3 → ℝ)) {z : E} (hz : L z ≠ 0) :
    HasFDerivAt (fun x => (spaceLength (L x))⁻¹)
      ((-((spaceLength (L z) ^ 3)⁻¹) • spaceDotCLM (L z)).comp L) z :=
  (hasFDerivAt_inv_spaceLength hz).comp z L.hasFDerivAt

theorem analyticAt_spaceSq_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] (Fin 3 → ℝ)) (z : E) : AnalyticAt ℝ (fun x => spaceSq (L x)) z :=
  (analyticAt_spaceSq (L z)).comp (L.analyticAt z)

theorem analyticAt_inv_spaceLength_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] (Fin 3 → ℝ)) {z : E} (hz : L z ≠ 0) :
    AnalyticAt ℝ (fun x => (spaceLength (L x))⁻¹) z :=
  (analyticAt_inv_spaceLength hz).comp (L.analyticAt z)

/-- The collision-free domain is open. -/
theorem isOpen_spatialCollisionFreeDomain (n : ℕ) : IsOpen (spatialCollisionFreeDomain n) := by
  have hc : ∀ i : Fin n, Continuous fun z : Phase (n * 3) => bodyVector3 z.1 i := fun i =>
    (posCLM3 i).continuous
  have h1 : IsOpen {z : Phase (n * 3) | ∀ i, 0 < spaceLength (bodyVector3 z.1 i)} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_spaceLength.comp (hc i))
  have h2 : IsOpen {z : Phase (n * 3) | ∀ i j, i ≠ j →
      0 < spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j)} := by
    simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ne_eq, not_false_eq_true]
      exact isOpen_iInter_of_finite fun _ =>
        isOpen_lt continuous_const (continuous_spaceLength.comp ((hc i).sub (hc j)))
  exact h1.inter h2

/-- `H_μ` is real analytic on the collision-free domain. -/
theorem analyticOnNhd_spatialHamiltonian (ν : Fin n → ℝ) (μ : ℝ) :
    AnalyticOnNhd ℝ (spatialHamiltonian ν μ) (spatialCollisionFreeDomain n) := by
  intro z hz
  have hv : ∀ i, posCLM3 i z ≠ 0 := fun i => spaceLength_pos_iff.mp (hz.1 i)
  have hw : ∀ i j, i ≠ j → (posCLM3 i - posCLM3 j) z ≠ 0 := fun i j hij =>
    spaceLength_pos_iff.mp (hz.2 i j hij)
  show AnalyticAt ℝ (fun z : Phase (n * 3) =>
    (∑ i, (spaceSq (bodyVector3 z.2 i) / (2 * ν i) - ν i / spaceLength (bodyVector3 z.1 i))) +
    μ * (spaceSq (∑ i, bodyVector3 z.2 i) / 2 -
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ν i * ν j / spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j))) z
  have hK : AnalyticAt ℝ (fun z : Phase (n * 3) =>
      ∑ i, (spaceSq (bodyVector3 z.2 i) / (2 * ν i) -
        ν i / spaceLength (bodyVector3 z.1 i))) z := by
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    have hs : AnalyticAt ℝ (fun x : Phase (n * 3) => spaceSq (momCLM3 i x)) z :=
      analyticAt_spaceSq_comp _ _
    have hi : AnalyticAt ℝ (fun x : Phase (n * 3) => (spaceLength (posCLM3 i x))⁻¹) z :=
      analyticAt_inv_spaceLength_comp _ (hv i)
    simp only [div_eq_mul_inv]
    exact (hs.mul analyticAt_const).sub (analyticAt_const.mul hi)
  have hP : AnalyticAt ℝ (fun z : Phase (n * 3) =>
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ν i * ν j / spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j)) z := by
    refine Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_filter.mp hj).2.ne
    have hi : AnalyticAt ℝ
        (fun x : Phase (n * 3) => (spaceLength ((posCLM3 i - posCLM3 j) x))⁻¹) z :=
      analyticAt_inv_spaceLength_comp _ (hw i j hij)
    simp only [div_eq_mul_inv]
    exact analyticAt_const.mul hi
  have hS : AnalyticAt ℝ (fun z : Phase (n * 3) => spaceSq (∑ i, bodyVector3 z.2 i)) z := by
    have := analyticAt_spaceSq_comp (∑ i, momCLM3 i : Phase (n * 3) →L[ℝ] (Fin 3 → ℝ)) z
    simpa [momCLM3_apply] using this
  have hS' : AnalyticAt ℝ (fun z : Phase (n * 3) => spaceSq (∑ i, bodyVector3 z.2 i) / 2) z := by
    simp only [div_eq_mul_inv]
    exact hS.mul analyticAt_const
  exact hK.add (analyticAt_const.mul (hS'.sub hP))

/-- `H_μ` is differentiable at every collision-free point. -/
theorem differentiableAt_spatialHamiltonian (ν : Fin n → ℝ) (μ : ℝ) {z : Phase (n * 3)}
    (hz : SpatialNoCollision z.1) : DifferentiableAt ℝ (spatialHamiltonian ν μ) z :=
  (analyticOnNhd_spatialHamiltonian ν μ z hz).differentiableAt

end KAM.Planetary.Spatial

end
