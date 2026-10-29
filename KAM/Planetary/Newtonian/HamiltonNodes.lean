/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Newtonian.Models
public import KAM.Planetary.Newtonian.Reduction
public import KAM.Planetary.Newtonian.Reconstruction

/-!
# Hamilton-equation nodes of Part 6 (literal conclusions)

Blueprint P, Part 6, graph-gap package GAP-P6a. Unsigned exports stating the literal conclusions
of `bpP:p6:hamilton-eqs` (block form of `X_Hmov`, `X_Hfix` for every real `μ`, `ε`, and the curve
statement), its steps `he-dir`, `he-coef`, `he-curve`, the coordinate step `rc-coords` of
`bpP:p6:reconstruction`, the arbitrary-real-`ε` bridge `reconstruction-fixed#real-eps` with the step
`rf-eq`, and the algebra step `sp-alg` of `bpP:p6:split`.
-/

public section

namespace KAM.Planetary

open KAM KAM.Kepler

section HamiltonNodes

variable {n : ℕ}

/-! ### Block form of the Hamilton fields (`bpP:p6:hamilton-eqs`, first two displays) -/

/-- `bpP:p6:hamilton-eqs`: `X_{H_mov}(z)` in the body blocks, for every real `μ`. -/
theorem movingField_blocks (G m0 : ℝ) (m : Fin n → ℝ) (μ : ℝ) {z : Phase (n * 2)}
    (hz : NoCollision z.1) (i : Fin n) :
    bodyVector (hamiltonianVectorField (movingHamiltonian G m0 m μ) z).1 i =
        (1 / m i) • bodyVector z.2 i + (μ / m0) • ∑ j, bodyVector z.2 j ∧
      bodyVector (hamiltonianVectorField (movingHamiltonian G m0 m μ) z).2 i =
        -(G * m0 * m i) • gKernel (fun j => bodyVector z.1 j) i +
          (μ * G * m i) • fKernel m (fun j => bodyVector z.1 j) i := by
  refine ⟨?_, ?_⟩
  · ext c
    have h := (hamiltonianVectorField_moving G m0 m μ hz i c).1
    show (hamiltonianVectorField (movingHamiltonian G m0 m μ) z).1 (finProdFinEquiv (i, c)) = _
    rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    ring
  · ext c
    exact (hamiltonianVectorField_moving G m0 m μ hz i c).2

/-- `bpP:p6:hamilton-eqs`: `X_{H_fix}(z)` in the body blocks, for every real `ε`. -/
theorem fixedField_blocks (G m0 : ℝ) (m : Fin n → ℝ) (ε : ℝ) {z : Phase (n * 2)}
    (hz : NoCollision z.1) (i : Fin n) :
    bodyVector (hamiltonianVectorField (fixedHamiltonian G m0 m ε) z).1 i =
        (1 / m i) • bodyVector z.2 i ∧
      bodyVector (hamiltonianVectorField (fixedHamiltonian G m0 m ε) z).2 i =
        -(G * m0 * m i) • gKernel (fun j => bodyVector z.1 j) i +
          (ε * G * m i) • fKernel m (fun j => bodyVector z.1 j) i := by
  refine ⟨?_, ?_⟩
  · ext c
    have h := (hamiltonianVectorField_fixed G m0 m ε hz i c).1
    show (hamiltonianVectorField (fixedHamiltonian G m0 m ε) z).1 (finProdFinEquiv (i, c)) = _
    rw [h]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · ext c
    exact (hamiltonianVectorField_fixed G m0 m ε hz i c).2

/-! ### The curve statement (`stepP:p6:he-curve`) -/

/-- `stepP:p6:he-curve`, generic part: a curve into `Phase (n * 2)` has derivative `v` at `t` iff
every body block of its position and momentum does. -/
theorem hasDerivAt_iff_bodyVector {z : ℝ → Phase (n * 2)} {v : Phase (n * 2)} {t : ℝ} :
    HasDerivAt z v t ↔ ∀ i, HasDerivAt (fun s => bodyVector (z s).1 i) (bodyVector v.1 i) t ∧
      HasDerivAt (fun s => bodyVector (z s).2 i) (bodyVector v.2 i) t := by
  refine ⟨fun h i => hasDerivAt_bodyVector h i, fun h => ?_⟩
  have hcomp : ∀ (f : ℝ → Fin (n * 2) → ℝ) (w : Fin (n * 2) → ℝ),
      (∀ i, HasDerivAt (fun s => bodyVector (f s) i) (bodyVector w i) t) → HasDerivAt f w t := by
    intro f w hf
    refine hasDerivAt_pi.2 fun k => ?_
    obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective k
    exact hasDerivAt_pi.1 (hf i) c
  exact (hcomp _ _ fun i => (h i).1).prodMk (hcomp _ _ fun i => (h i).2)

/-- `stepP:p6:he-curve` for `H_mov`: the curve has derivative `X_H(z(t))` iff the coordinates have
the displayed derivatives. -/
theorem hasDerivAt_movingField_iff (G m0 : ℝ) (m : Fin n → ℝ) (μ : ℝ) {z : ℝ → Phase (n * 2)}
    {t : ℝ} (hz : NoCollision (z t).1) :
    HasDerivAt z (hamiltonianVectorField (movingHamiltonian G m0 m μ) (z t)) t ↔
      ∀ i, HasDerivAt (fun s => bodyVector (z s).1 i)
          ((1 / m i) • bodyVector (z t).2 i + (μ / m0) • ∑ j, bodyVector (z t).2 j) t ∧
        HasDerivAt (fun s => bodyVector (z s).2 i)
          (-(G * m0 * m i) • gKernel (fun j => bodyVector (z t).1 j) i +
            (μ * G * m i) • fKernel m (fun j => bodyVector (z t).1 j) i) t := by
  rw [hasDerivAt_iff_bodyVector]
  simp only [(movingField_blocks G m0 m μ hz _).1, (movingField_blocks G m0 m μ hz _).2]

/-- `stepP:p6:he-curve` for `H_fix` (every real `ε`). -/
theorem hasDerivAt_fixedField_iff (G m0 : ℝ) (m : Fin n → ℝ) (ε : ℝ) {z : ℝ → Phase (n * 2)}
    {t : ℝ} (hz : NoCollision (z t).1) :
    HasDerivAt z (hamiltonianVectorField (fixedHamiltonian G m0 m ε) (z t)) t ↔
      ∀ i, HasDerivAt (fun s => bodyVector (z s).1 i) ((1 / m i) • bodyVector (z t).2 i) t ∧
        HasDerivAt (fun s => bodyVector (z s).2 i)
          (-(G * m0 * m i) • gKernel (fun j => bodyVector (z t).1 j) i +
            (ε * G * m i) • fKernel m (fun j => bodyVector (z t).1 j) i) t := by
  rw [hasDerivAt_iff_bodyVector]
  simp only [(fixedField_blocks G m0 m ε hz _).1, (fixedField_blocks G m0 m ε hz _).2]

/-- `bpP:p6:hamilton-eqs` for `H_mov`: the block form of `X_H` on `W` and the curve clause. -/
theorem hamilton_eqs_moving (G m0 : ℝ) (m : Fin n → ℝ) (μ : ℝ) :
    (∀ z : Phase (n * 2), NoCollision z.1 → ∀ i,
      bodyVector (hamiltonianVectorField (movingHamiltonian G m0 m μ) z).1 i =
          (1 / m i) • bodyVector z.2 i + (μ / m0) • ∑ j, bodyVector z.2 j ∧
        bodyVector (hamiltonianVectorField (movingHamiltonian G m0 m μ) z).2 i =
          -(G * m0 * m i) • gKernel (fun j => bodyVector z.1 j) i +
            (μ * G * m i) • fKernel m (fun j => bodyVector z.1 j) i) ∧
    (∀ (z : ℝ → Phase (n * 2)) (t : ℝ), NoCollision (z t).1 →
      (HasDerivAt z (hamiltonianVectorField (movingHamiltonian G m0 m μ) (z t)) t ↔
        ∀ i, HasDerivAt (fun s => bodyVector (z s).1 i)
            ((1 / m i) • bodyVector (z t).2 i + (μ / m0) • ∑ j, bodyVector (z t).2 j) t ∧
          HasDerivAt (fun s => bodyVector (z s).2 i)
            (-(G * m0 * m i) • gKernel (fun j => bodyVector (z t).1 j) i +
              (μ * G * m i) • fKernel m (fun j => bodyVector (z t).1 j) i) t)) :=
  ⟨fun _ hz i => movingField_blocks G m0 m μ hz i,
    fun _ _ hz => hasDerivAt_movingField_iff G m0 m μ hz⟩

/-- `bpP:p6:hamilton-eqs` for `H_fix`. -/
theorem hamilton_eqs_fixed (G m0 : ℝ) (m : Fin n → ℝ) (ε : ℝ) :
    (∀ z : Phase (n * 2), NoCollision z.1 → ∀ i,
      bodyVector (hamiltonianVectorField (fixedHamiltonian G m0 m ε) z).1 i =
          (1 / m i) • bodyVector z.2 i ∧
        bodyVector (hamiltonianVectorField (fixedHamiltonian G m0 m ε) z).2 i =
          -(G * m0 * m i) • gKernel (fun j => bodyVector z.1 j) i +
            (ε * G * m i) • fKernel m (fun j => bodyVector z.1 j) i) ∧
    (∀ (z : ℝ → Phase (n * 2)) (t : ℝ), NoCollision (z t).1 →
      (HasDerivAt z (hamiltonianVectorField (fixedHamiltonian G m0 m ε) (z t)) t ↔
        ∀ i, HasDerivAt (fun s => bodyVector (z s).1 i) ((1 / m i) • bodyVector (z t).2 i) t ∧
          HasDerivAt (fun s => bodyVector (z s).2 i)
            (-(G * m0 * m i) • gKernel (fun j => bodyVector (z t).1 j) i +
              (ε * G * m i) • fKernel m (fun j => bodyVector (z t).1 j) i) t)) :=
  ⟨fun _ hz i => fixedField_blocks G m0 m ε hz i,
    fun _ _ hz => hasDerivAt_fixedField_iff G m0 m ε hz⟩

/-! ### Collected coefficients (`stepP:p6:he-coef`) -/

/-- `stepP:p6:he-coef` for `H_mov`: `∂_{p_i} H = p_i/m_i + (μ/m₀) P` and
`∂_{q_i} H = G m₀ m_i g_i - μ G m_i f_i`, as partial Fréchet derivatives. -/
theorem fderiv_movingHamiltonian_partials (G m0 : ℝ) (m : Fin n → ℝ) (μ : ℝ)
    {z : Phase (n * 2)} (hz : NoCollision z.1) (i : Fin n) (c : Fin 2) :
    fderiv ℝ (movingHamiltonian G m0 m μ) z (0, Pi.single (finProdFinEquiv (i, c)) 1) =
        ((1 / m i) • bodyVector z.2 i + (μ / m0) • ∑ j, bodyVector z.2 j) c ∧
      fderiv ℝ (movingHamiltonian G m0 m μ) z (Pi.single (finProdFinEquiv (i, c)) 1, 0) =
        ((G * m0 * m i) • gKernel (fun j => bodyVector z.1 j) i -
          (μ * G * m i) • fKernel m (fun j => bodyVector z.1 j) i) c := by
  have h := movingField_blocks G m0 m μ hz i
  have h1 := congrFun h.1 c
  have h2 := congrFun h.2 c
  refine ⟨h1, ?_⟩
  have h3 : -fderiv ℝ (movingHamiltonian G m0 m μ) z
      (Pi.single (finProdFinEquiv (i, c)) 1, 0) = _ := h2
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at h3 ⊢
  linarith

/-- `stepP:p6:he-coef` for `H_fix`. -/
theorem fderiv_fixedHamiltonian_partials (G m0 : ℝ) (m : Fin n → ℝ) (ε : ℝ)
    {z : Phase (n * 2)} (hz : NoCollision z.1) (i : Fin n) (c : Fin 2) :
    fderiv ℝ (fixedHamiltonian G m0 m ε) z (0, Pi.single (finProdFinEquiv (i, c)) 1) =
        ((1 / m i) • bodyVector z.2 i) c ∧
      fderiv ℝ (fixedHamiltonian G m0 m ε) z (Pi.single (finProdFinEquiv (i, c)) 1, 0) =
        ((G * m0 * m i) • gKernel (fun j => bodyVector z.1 j) i -
          (ε * G * m i) • fKernel m (fun j => bodyVector z.1 j) i) c := by
  have h := fixedField_blocks G m0 m ε hz i
  have h1 := congrFun h.1 c
  have h2 := congrFun h.2 c
  refine ⟨h1, ?_⟩
  have h3 : -fderiv ℝ (fixedHamiltonian G m0 m ε) z
      (Pi.single (finProdFinEquiv (i, c)) 1, 0) = _ := h2
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at h3 ⊢
  linarith

/-! ### Coordinates of the equations (`stepP:p6:rc-coords`) -/

/-- `stepP:p6:rc-coords`: at each `t ∈ J`, the body blocks of the position (resp. momentum) have the
derivatives `a_i` (resp. `b_i`), and so does every linear combination of them. -/
theorem rc_coords_moving {G m0 μ : ℝ} {m : Fin n → ℝ} {J : Set ℝ} {z : ℝ → Phase (n * 2)}
    (hz : ∀ t ∈ J, NoCollision (z t).1 ∧
      HasDerivAt z (hamiltonianVectorField (movingHamiltonian G m0 m μ) (z t)) t)
    {t : ℝ} (ht : t ∈ J) :
    (∀ i, HasDerivAt (fun s => bodyVector (z s).1 i)
        ((1 / m i) • bodyVector (z t).2 i + (μ / m0) • ∑ j, bodyVector (z t).2 j) t ∧
      HasDerivAt (fun s => bodyVector (z s).2 i)
        (-(G * m0 * m i) • gKernel (fun j => bodyVector (z t).1 j) i +
          (μ * G * m i) • fKernel m (fun j => bodyVector (z t).1 j) i) t) ∧
    (∀ w : Fin n → ℝ,
      HasDerivAt (fun s => ∑ i, w i • bodyVector (z s).1 i)
        (∑ i, w i • ((1 / m i) • bodyVector (z t).2 i +
          (μ / m0) • ∑ j, bodyVector (z t).2 j)) t ∧
      HasDerivAt (fun s => ∑ i, w i • bodyVector (z s).2 i)
        (∑ i, w i • (-(G * m0 * m i) • gKernel (fun j => bodyVector (z t).1 j) i +
          (μ * G * m i) • fKernel m (fun j => bodyVector (z t).1 j) i)) t) := by
  have h := (hasDerivAt_movingField_iff G m0 m μ (hz t ht).1).1 (hz t ht).2
  refine ⟨h, fun w => ⟨?_, ?_⟩⟩
  · exact HasDerivAt.fun_sum fun i _ => (h i).1.const_smul (w i)
  · exact HasDerivAt.fun_sum fun i _ => (h i).2.const_smul (w i)

/-! ### Fixed Sun, arbitrary real `ε` (`reconstruction-fixed#real-eps`, `stepP:p6:rf-eq`) -/

/-- `bpP:p6:reconstruction-fixed#real-eps`: for every real `ε` (including `ε < 0`), the fixed-Sun
derivative hypothesis gives `q_i' = p_i/m_i` and `p_i' = -G m₀ m_i g_i + ε G m_i f_i`. -/
theorem fixedField_equations {G m0 ε : ℝ} {m : Fin n → ℝ} {J : Set ℝ} {z : ℝ → Phase (n * 2)}
    (hz : ∀ t ∈ J, NoCollision (z t).1 ∧
      HasDerivAt z (hamiltonianVectorField (fixedHamiltonian G m0 m ε) (z t)) t)
    {t : ℝ} (ht : t ∈ J) (i : Fin n) :
    HasDerivAt (fun s => bodyVector (z s).1 i) ((1 / m i) • bodyVector (z t).2 i) t ∧
      HasDerivAt (fun s => bodyVector (z s).2 i)
        (-(G * m0 * m i) • gKernel (fun j => bodyVector (z t).1 j) i +
          (ε * G * m i) • fKernel m (fun j => bodyVector (z t).1 j) i) t :=
  (hasDerivAt_fixedField_iff G m0 m ε (hz t ht).1).1 (hz t ht).2 i

/-- `stepP:p6:rf-eq`: the equations of `bpP:p6:reconstruction-fixed` for every real `ε`: positivity
of the lengths, `q_i' = p_i/m_i`, `p_i' = -G m₀ m_i g_i + ε G m_i f_i` and
`V_i' = -G m₀ q_i/ℓ(q_i)³ + ε G f_i(q)` for `V_i = p_i/m_i`. -/
theorem fixedField_rf_eq {G m0 ε : ℝ} (hm0 : 0 < m0) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    {J : Set ℝ} {z : ℝ → Phase (n * 2)}
    (hz : ∀ t ∈ J, NoCollision (z t).1 ∧
      HasDerivAt z (hamiltonianVectorField (fixedHamiltonian G m0 m ε) (z t)) t) :
    (∀ t ∈ J, ∀ i, 0 < planeLength (bodyVector (z t).1 i)) ∧
    (∀ t ∈ J, ∀ i j, i ≠ j → 0 < planeLength (bodyVector (z t).1 j - bodyVector (z t).1 i)) ∧
    (∀ t ∈ J, ∀ i, HasDerivAt (fun s => bodyVector (z s).1 i)
      ((1 / m i) • bodyVector (z t).2 i) t) ∧
    (∀ t ∈ J, ∀ i, HasDerivAt (fun s => bodyVector (z s).2 i)
      (-(G * m0 * m i) • gKernel (fun j => bodyVector (z t).1 j) i +
        (ε * G * m i) • fKernel m (fun j => bodyVector (z t).1 j) i) t) ∧
    (∀ t ∈ J, ∀ i, HasDerivAt (fun s => (1 / m i) • bodyVector (z s).2 i)
      ((-(G * m0)) • gKernel (fun j => bodyVector (z t).1 j) i +
        (ε * G) • fKernel m (fun j => bodyVector (z t).1 j) i) t) := by
  have h := reconstruction_fixed (G := G) (ε := ε) hm0 hm hz
  refine ⟨h.1, h.2.1, fun t ht i => (fixedField_equations hz ht i).1,
    fun t ht i => (fixedField_equations hz ht i).2, fun t ht i => ?_⟩
  refine ((fixedField_equations hz ht i).2.const_smul (1 / m i)).congr_deriv ?_
  have hmi : m i ≠ 0 := (hm i).ne'
  have e1 : 1 / m i * (-(G * m0 * m i)) = -(G * m0) := by field_simp
  have e2 : 1 / m i * (ε * G * m i) = ε * G := by field_simp
  rw [smul_add, smul_smul, smul_smul, e1, e2]

end HamiltonNodes

end KAM.Planetary
