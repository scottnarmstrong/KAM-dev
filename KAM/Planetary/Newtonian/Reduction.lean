/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Newtonian.Models
public import KAM.Frozen.Planetary.Defs.ActualMasses
public import KAM.Frozen.Planetary.Defs.IsNewtonSolutionOn
public import KAM.Frozen.Planetary.Defs.IsMovingSolutionOn
public import KAM.Frozen.Defs.SymplecticForm

/-!
# Newtonian reduction: heliocentric coordinates

Blueprint P, Part 6 (`bpP:p6:nbody`, `bpP:p6:reduction`): the `N`-body Hamiltonian, the
heliocentric linear symplectic map `Θ` and its inverse, the heliocentric form of the Hamiltonian
(independent of the Sun's position), its zero-momentum restriction (`F_μ = μ H_mov`), and the
passage from Newton solutions with zero total momentum to moving-Sun Hamiltonian solutions.
-/

@[expose] public noncomputable section

namespace KAM.Planetary

open KAM KAM.Kepler

section Reduction

/-! ### The Hamiltonian and the heliocentric map -/

/-- `bpP:p6:nbody`: the `(N)`-body Hamiltonian `F_μ` for the mass array `M`
(`N = n + 1`, `M = actualMasses`). -/
def nbodyHamiltonian {N : ℕ} (G : ℝ) (M : Fin N → ℝ) (z : Phase (N * 2)) : ℝ :=
  (∑ k, planeSq (bodyVector z.2 k) / (2 * M k)) -
    G * ∑ k, ∑ l ∈ Finset.univ.filter (fun l => k < l),
      M k * M l / planeLength (bodyVector z.1 k - bodyVector z.1 l)

/-- `Θ(X, Y) = (Q₀, q, P₀, P)`: `Q₀ = X₀`, `q_i = X_i - X₀`, `P₀ = Σ Y_k`, `P_i = Y_i`
(body `0` is the Sun). -/
def helioMap {n : ℕ} (z : Phase ((n + 1) * 2)) : Phase ((n + 1) * 2) :=
  (ofBodies (Fin.cons (bodyVector z.1 0)
      (fun (i : Fin n) => bodyVector z.1 i.succ - bodyVector z.1 0)),
   ofBodies (Fin.cons (∑ k, bodyVector z.2 k) (fun (i : Fin n) => bodyVector z.2 i.succ)))
def helioInv {n : ℕ} (w : Phase ((n + 1) * 2)) : Phase ((n + 1) * 2) :=
  (ofBodies (Fin.cons (bodyVector w.1 0)
      (fun (i : Fin n) => bodyVector w.1 i.succ + bodyVector w.1 0)),
   ofBodies (Fin.cons (bodyVector w.2 0 - ∑ i : Fin n, bodyVector w.2 i.succ)
      (fun (i : Fin n) => bodyVector w.2 i.succ)))

/-! ### Plane-vector algebra and body-wise calculus -/

theorem planeDot_add_left (a b c : Fin 2 → ℝ) :
    planeDot (a + b) c = planeDot a c + planeDot b c := by
  simp only [planeDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem planeDot_sub_left (a b c : Fin 2 → ℝ) :
    planeDot (a - b) c = planeDot a c - planeDot b c := by
  simp only [planeDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem planeDot_comm (a b : Fin 2 → ℝ) : planeDot a b = planeDot b a := by
  simp only [planeDot, mul_comm]

theorem planeDot_add_right (a b c : Fin 2 → ℝ) :
    planeDot a (b + c) = planeDot a b + planeDot a c := by
  rw [planeDot_comm, planeDot_add_left, planeDot_comm b a, planeDot_comm c a]

theorem planeDot_sub_right (a b c : Fin 2 → ℝ) :
    planeDot a (b - c) = planeDot a b - planeDot a c := by
  rw [planeDot_comm, planeDot_sub_left, planeDot_comm b a, planeDot_comm c a]

theorem planeDot_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin 2 → ℝ) (w : Fin 2 → ℝ) :
    planeDot (∑ i ∈ s, f i) w = ∑ i ∈ s, planeDot (f i) w := by
  simp only [planeDot, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem planeDot_sum_right {ι : Type*} (s : Finset ι) (f : ι → Fin 2 → ℝ) (w : Fin 2 → ℝ) :
    planeDot w (∑ i ∈ s, f i) = ∑ i ∈ s, planeDot w (f i) := by
  rw [planeDot_comm, planeDot_sum_left]
  exact Finset.sum_congr rfl fun i _ => planeDot_comm _ _

theorem planeSq_neg (v : Fin 2 → ℝ) : planeSq (-v) = planeSq v := by
  simp [planeSq]

theorem bodyVector_add {N : ℕ} (a b : Fin (N * 2) → ℝ) (i : Fin N) :
    bodyVector (a + b) i = bodyVector a i + bodyVector b i := rfl

theorem bodyVector_smul {N : ℕ} (c : ℝ) (a : Fin (N * 2) → ℝ) (i : Fin N) :
    bodyVector (c • a) i = c • bodyVector a i := rfl

theorem eq_of_bodyVector_eq {N : ℕ} {a b : Fin (N * 2) → ℝ}
    (h : ∀ i, bodyVector a i = bodyVector b i) : a = b :=
  calc a = ofBodies (fun i => bodyVector a i) := (ofBodies_bodyVector a).symm
    _ = ofBodies (fun i => bodyVector b i) := by simp only [h]
    _ = b := ofBodies_bodyVector b

/-- The symplectic form body by body. -/
theorem symplecticForm_eq_bodies {N : ℕ} (u v : Phase (N * 2)) :
    symplecticForm u v = ∑ i, (planeDot (bodyVector u.2 i) (bodyVector v.1 i) -
      planeDot (bodyVector u.1 i) (bodyVector v.2 i)) := by
  unfold symplecticForm
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [planeDot, bodyVector, Finset.sum_sub_distrib]

/-- Pair sums over `k < l` in `Fin (n + 1)` split into Sun-planet and planet-planet pairs. -/
theorem sum_pairs_succ {n : ℕ} (F : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ∑ k, ∑ l ∈ Finset.univ.filter (fun l => k < l), F k l =
      ∑ i : Fin n, F 0 i.succ +
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), F i.succ j.succ := by
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Finset.sum_filter, Fin.sum_univ_succ]
    simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_filter]
    simp [Fin.succ_lt_succ_iff]

/-! ### Body vectors of `Θ` and `Θ⁻¹` -/

section Bodies

variable {n : ℕ}

theorem helioMap_pos_zero (z : Phase ((n + 1) * 2)) :
    bodyVector (helioMap z).1 0 = bodyVector z.1 0 := by
  simp [helioMap, bodyVector_ofBodies]

theorem helioMap_pos_succ (z : Phase ((n + 1) * 2)) (i : Fin n) :
    bodyVector (helioMap z).1 i.succ = bodyVector z.1 i.succ - bodyVector z.1 0 := by
  simp [helioMap, bodyVector_ofBodies]

theorem helioMap_mom_zero (z : Phase ((n + 1) * 2)) :
    bodyVector (helioMap z).2 0 = ∑ k, bodyVector z.2 k := by
  simp [helioMap, bodyVector_ofBodies]

theorem helioMap_mom_succ (z : Phase ((n + 1) * 2)) (i : Fin n) :
    bodyVector (helioMap z).2 i.succ = bodyVector z.2 i.succ := by
  simp [helioMap, bodyVector_ofBodies]

theorem helioInv_pos_zero (w : Phase ((n + 1) * 2)) :
    bodyVector (helioInv w).1 0 = bodyVector w.1 0 := by
  simp [helioInv, bodyVector_ofBodies]

theorem helioInv_pos_succ (w : Phase ((n + 1) * 2)) (i : Fin n) :
    bodyVector (helioInv w).1 i.succ = bodyVector w.1 i.succ + bodyVector w.1 0 := by
  simp [helioInv, bodyVector_ofBodies]

theorem helioInv_mom_zero (w : Phase ((n + 1) * 2)) :
    bodyVector (helioInv w).2 0 = bodyVector w.2 0 - ∑ i : Fin n, bodyVector w.2 i.succ := by
  simp [helioInv, bodyVector_ofBodies]

theorem helioInv_mom_succ (w : Phase ((n + 1) * 2)) (i : Fin n) :
    bodyVector (helioInv w).2 i.succ = bodyVector w.2 i.succ := by
  simp [helioInv, bodyVector_ofBodies]

end Bodies

/-- `bpP:p6:reduction` (a). -/
theorem helioMap_helioInv {n : ℕ} (w : Phase ((n + 1) * 2)) : helioMap (helioInv w) = w := by
  refine Prod.ext (eq_of_bodyVector_eq fun i => ?_) (eq_of_bodyVector_eq fun i => ?_)
  · induction i using Fin.cases with
    | zero => rw [helioMap_pos_zero, helioInv_pos_zero]
    | succ i => rw [helioMap_pos_succ, helioInv_pos_succ, helioInv_pos_zero, add_sub_cancel_right]
  · induction i using Fin.cases with
    | zero =>
      rw [helioMap_mom_zero, Fin.sum_univ_succ, helioInv_mom_zero]
      simp only [helioInv_mom_succ]
      abel
    | succ i => rw [helioMap_mom_succ, helioInv_mom_succ]
theorem helioInv_helioMap {n : ℕ} (z : Phase ((n + 1) * 2)) : helioInv (helioMap z) = z := by
  refine Prod.ext (eq_of_bodyVector_eq fun i => ?_) (eq_of_bodyVector_eq fun i => ?_)
  · induction i using Fin.cases with
    | zero => rw [helioInv_pos_zero, helioMap_pos_zero]
    | succ i =>
      rw [helioInv_pos_succ, helioMap_pos_succ, helioMap_pos_zero, sub_add_cancel]
  · induction i using Fin.cases with
    | zero =>
      rw [helioInv_mom_zero, helioMap_mom_zero, Fin.sum_univ_succ]
      simp only [helioMap_mom_succ]
      abel
    | succ i => rw [helioInv_mom_succ, helioMap_mom_succ]

/-! ### `Θ` is linear and symplectic -/

/-- `Θ` as a linear map. -/
private def helioLin (n : ℕ) : Phase ((n + 1) * 2) →ₗ[ℝ] Phase ((n + 1) * 2) where
  toFun := helioMap
  map_add' a b := by
    refine Prod.ext (eq_of_bodyVector_eq fun i => ?_) (eq_of_bodyVector_eq fun i => ?_)
    · induction i using Fin.cases with
      | zero => simp [helioMap_pos_zero, bodyVector_add]
      | succ i => simp only [Prod.fst_add, helioMap_pos_succ, bodyVector_add]; abel
    · induction i using Fin.cases with
      | zero => simp [helioMap_mom_zero, bodyVector_add, Finset.sum_add_distrib]
      | succ i => simp [helioMap_mom_succ, bodyVector_add]
  map_smul' c a := by
    refine Prod.ext (eq_of_bodyVector_eq fun i => ?_) (eq_of_bodyVector_eq fun i => ?_)
    · induction i using Fin.cases with
      | zero => simp [helioMap_pos_zero, bodyVector_smul]
      | succ i => simp only [Prod.smul_fst, helioMap_pos_succ, bodyVector_smul, smul_sub,
          RingHom.id_apply]
    · induction i using Fin.cases with
      | zero => simp [helioMap_mom_zero, bodyVector_smul, Finset.smul_sum]
      | succ i => simp [helioMap_mom_succ, bodyVector_smul]

theorem helioMap_pairing {n : ℕ} (z : Phase ((n + 1) * 2)) :
    ∑ k, planeDot (bodyVector z.1 k) (bodyVector z.2 k) =
      planeDot (bodyVector (helioMap z).1 0) (bodyVector (helioMap z).2 0) +
        ∑ i : Fin n,
          planeDot (bodyVector (helioMap z).1 i.succ) (bodyVector (helioMap z).2 i.succ) := by
  rw [Fin.sum_univ_succ, helioMap_pos_zero, helioMap_mom_zero, Fin.sum_univ_succ]
  simp only [helioMap_pos_succ, helioMap_mom_succ, planeDot_add_right, planeDot_sub_left,
    Finset.sum_sub_distrib, planeDot_sum_right]
  ring

theorem helioMap_symplectic (n : ℕ) : IsSymplecticOn 1 (helioMap (n := n)) Set.univ := by
  intro z _ u v
  have hL : HasFDerivAt (helioMap (n := n))
      (LinearMap.toContinuousLinearMap (helioLin n)) z :=
    (LinearMap.toContinuousLinearMap (helioLin n)).hasFDerivAt
  rw [hL.fderiv]
  show symplecticForm (helioMap u) (helioMap v) = 1 * symplecticForm u v
  rw [symplecticForm_eq_bodies, symplecticForm_eq_bodies, Fin.sum_univ_succ, Fin.sum_univ_succ,
    helioMap_pos_zero, helioMap_pos_zero, helioMap_mom_zero, helioMap_mom_zero, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp only [helioMap_pos_succ, helioMap_mom_succ, planeDot_add_left, planeDot_add_right,
    planeDot_sub_left, planeDot_sub_right, Finset.sum_sub_distrib,
    planeDot_sum_left, planeDot_sum_right]
  ring

/-! ### The Hamiltonian in heliocentric coordinates -/

/-- (b): `F_μ` in the heliocentric coordinates; independent of `Q₀`. -/
theorem nbodyHamiltonian_helio {n : ℕ} (G m0 : ℝ) (m : Fin n → ℝ) (μ : ℝ)
    (z : Phase ((n + 1) * 2)) :
    nbodyHamiltonian G (actualMasses m0 m μ) z =
      planeSq (bodyVector (helioMap z).2 0 - ∑ i : Fin n, bodyVector (helioMap z).2 i.succ) /
          (2 * m0)
        + ∑ i, planeSq (bodyVector (helioMap z).2 i.succ) / (2 * (μ * m i))
        - G * μ * ∑ i, m0 * m i / planeLength (bodyVector (helioMap z).1 i.succ)
        - G * μ ^ 2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            m i * m j / planeLength
              (bodyVector (helioMap z).1 i.succ - bodyVector (helioMap z).1 j.succ) := by
  unfold nbodyHamiltonian
  rw [sum_pairs_succ, Fin.sum_univ_succ, helioMap_mom_zero, Fin.sum_univ_succ]
  simp only [helioMap_mom_succ, helioMap_pos_succ, actualMasses, Fin.cons_zero, Fin.cons_succ,
    add_sub_cancel_right, sub_sub_sub_cancel_right]
  have h1 : ∑ i : Fin n, m0 * (μ * m i) / planeLength (bodyVector z.1 0 - bodyVector z.1 i.succ) =
      μ * ∑ i, m0 * m i / planeLength (bodyVector z.1 i.succ - bodyVector z.1 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [planeLength_sub_comm (bodyVector z.1 0)]
    ring
  have h2 : ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      μ * m i * (μ * m j) / planeLength (bodyVector z.1 i.succ - bodyVector z.1 j.succ) =
      μ ^ 2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        m i * m j / planeLength (bodyVector z.1 i.succ - bodyVector z.1 j.succ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1, h2]
  ring

theorem nbodyHamiltonian_helio_zero_momentum {n : ℕ} (G m0 : ℝ) (m : Fin n → ℝ) {μ : ℝ} (hμ : μ ≠ 0)
    (hm0 : m0 ≠ 0) (hm : ∀ i, m i ≠ 0) (x0 : Fin 2 → ℝ) (q p : Fin (n * 2) → ℝ) :
    nbodyHamiltonian G (actualMasses m0 m μ)
      (helioInv (ofBodies (Fin.cons x0 (fun i => bodyVector q i)),
        ofBodies (Fin.cons (0 : Fin 2 → ℝ) (fun i => μ • bodyVector p i)))) =
      μ * movingHamiltonian G m0 m μ (q, p) := by
  have _ := hm0
  rw [nbodyHamiltonian_helio, helioMap_helioInv, movingHamiltonian_split]
  simp only [bodyVector_ofBodies, Fin.cons_zero, Fin.cons_succ, zero_sub, planeSq_neg,
    ← Finset.smul_sum, KAM.Kepler.planeSq_smul]
  unfold keplerPart fMov pairPotential
  simp only [mul_add, Finset.mul_sum]
  have e1 : ∑ x, μ ^ 2 * planeSq (bodyVector p x) / (2 * (μ * m x)) =
      ∑ i, μ * (planeSq (bodyVector p i) / (2 * m i)) :=
    Finset.sum_congr rfl fun i _ => by have := hm i; field_simp
  have e2 : ∑ i, G * μ * (m0 * m i / planeLength (bodyVector q i)) =
      ∑ i, μ * (G * m0 * m i / planeLength (bodyVector q i)) :=
    Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ x : Fin n, ∑ i ∈ Finset.univ.filter (fun j => x < j),
      G * μ ^ 2 * (m x * m i / planeLength (bodyVector q x - bodyVector q i)) =
      μ * (μ * ∑ x : Fin n, ∑ i ∈ Finset.univ.filter (fun j => x < j),
        G * m x * m i / planeLength (bodyVector q x - bodyVector q i)) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-! ### Newton solutions with zero total momentum -/

private theorem sum_filter_ne_succ {n : ℕ} {E : Type*} [AddCommMonoid E] (F : Fin (n + 1) → E)
    (i : Fin n) :
    ∑ l ∈ Finset.univ.filter (fun l => l ≠ i.succ), F l =
      F 0 + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), F j.succ := by
  have h0 : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp [h0, Fin.succ_inj]

/-- The momentum derivative `m_i V_i'` in the form of the moving-Hamiltonian field. -/
private theorem accel_identity {n : ℕ} (G m0 μ : ℝ) (m : Fin n → ℝ) (Q : Fin (n + 1) → Fin 2 → ℝ)
    (i : Fin n) :
    m i • ∑ l ∈ Finset.univ.filter (fun l => l ≠ i.succ),
        (G * actualMasses m0 m μ l / planeLength (Q l - Q i.succ) ^ 3) • (Q l - Q i.succ) =
      -(G * m0 * m i) • gKernel (fun j => Q j.succ - Q 0) i +
        (μ * G * m i) • fKernel m (fun j => Q j.succ - Q 0) i := by
  rw [sum_filter_ne_succ]
  have e0 : planeLength (Q 0 - Q i.succ) = planeLength (Q i.succ - Q 0) :=
    planeLength_sub_comm _ _
  simp only [gKernel, fKernel, actualMasses, Fin.cons_zero, Fin.cons_succ, smul_add,
    Finset.smul_sum, smul_smul, e0, sub_sub_sub_cancel_right]
  congr 1
  · rw [← neg_sub (Q i.succ) (Q 0), smul_neg, ← neg_smul]
    congr 1
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring

/-- Assembling a curve of phase vectors from curves of body vectors. -/
private theorem hasDerivAt_ofBodies {N : ℕ} {F : ℝ → Fin N → Fin 2 → ℝ} {d : Fin N → Fin 2 → ℝ}
    {t : ℝ} (h : ∀ i, HasDerivAt (fun s => F s i) (d i) t) :
    HasDerivAt (fun s => ofBodies (F s)) (ofBodies d) t := by
  rw [hasDerivAt_pi]
  intro k
  exact (hasDerivAt_pi.1 (h (finProdFinEquiv.symm k).1)) (finProdFinEquiv.symm k).2

/-- (c): Newton solutions with zero total momentum are `H_mov`-solutions (`p_i = m_i V_i`).
For `G = m₀ = 1` the conclusion is `IsMovingSolutionOn m μ J z`. -/
theorem newton_to_moving {n : ℕ} {G m0 μ : ℝ} {m : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i)
    (hμ : 0 < μ) {J : Set ℝ} {Q V : ℝ → Fin (n + 1) → Fin 2 → ℝ}
    (hN : IsNewtonSolutionOn (fun k => G * actualMasses m0 m μ k) J Q V)
    (hP : ∀ t ∈ J, ∑ k, actualMasses m0 m μ k • V t k = 0) :
    let z : ℝ → Phase (n * 2) := fun t =>
      (ofBodies (fun (i : Fin n) => Q t i.succ - Q t 0),
        ofBodies (fun (i : Fin n) => m i • V t i.succ))
    KAM.Iso.IsHamiltonianSolutionOn (movingHamiltonian G m0 m μ) Set.univ J z ∧
      ∀ t ∈ J, NoCollision (z t).1 := by
  intro z
  have _ := hG
  have _ := hμ
  have hnc : ∀ t ∈ J, NoCollision (z t).1 := by
    intro t ht
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · show 0 < planeLength (bodyVector (ofBodies fun i : Fin n => Q t i.succ - Q t 0) i)
      rw [bodyVector_ofBodies]
      exact hN.1 t ht 0 i.succ (Fin.succ_ne_zero i).symm
    · show 0 < planeLength (bodyVector (ofBodies fun i : Fin n => Q t i.succ - Q t 0) i -
        bodyVector (ofBodies fun i : Fin n => Q t i.succ - Q t 0) j)
      rw [bodyVector_ofBodies, bodyVector_ofBodies, sub_sub_sub_cancel_right]
      exact hN.1 t ht j.succ i.succ (fun h => hij (Fin.succ_injective _ h).symm)
  refine ⟨fun t ht => ⟨Set.mem_univ _, ?_, ?_⟩, hnc⟩
  · exact (analyticOnNhd_movingHamiltonian G m0 m μ (z t) (hnc t ht)).differentiableAt
  · have hsum : ∀ c, m0 * V t 0 c + μ * ∑ j, m j * V t j.succ c = 0 := by
      intro c
      have h := congrFun (hP t ht) c
      rw [Fin.sum_univ_succ] at h
      simpa [actualMasses, Finset.sum_apply, Finset.mul_sum, mul_assoc] using h
    have hpos : ∀ i : Fin n, HasDerivAt (fun s => Q s i.succ - Q s 0) (V t i.succ - V t 0) t :=
      fun i => (hN.2.1 t ht i.succ).sub (hN.2.1 t ht 0)
    have hmom : ∀ i : Fin n, HasDerivAt (fun s => m i • V s i.succ)
        (m i • ∑ l ∈ Finset.univ.filter (fun l => l ≠ i.succ),
          (G * actualMasses m0 m μ l / planeLength (Q t l - Q t i.succ) ^ 3) •
            (Q t l - Q t i.succ)) t :=
      fun i => (hN.2.2 t ht i.succ).const_smul (m i)
    refine ((hasDerivAt_ofBodies hpos).prodMk (hasDerivAt_ofBodies hmom)).congr_deriv ?_
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective k
    · rw [(hamiltonianVectorField_moving G m0 m μ (hnc t ht) i c).1]
      have hV0 : V t 0 c = -(μ / m0) * ∑ j, m j * V t j.succ c := by
        have := hsum c
        field_simp
        linarith
      have hmi := (hm i).ne'
      simp only [z, ofBodies, Equiv.symm_apply_apply, Pi.sub_apply, bodyVector, Pi.smul_apply,
        smul_eq_mul, hV0]
      field_simp
      ring
    · rw [(hamiltonianVectorField_moving G m0 m μ (hnc t ht) i c).2]
      have := congrFun (accel_identity G m0 μ m (Q t) i) c
      simp only [z, ofBodies, Equiv.symm_apply_apply]
      simp only [bodyVector_ofBodies]
      exact this

end Reduction

end KAM.Planetary

end
