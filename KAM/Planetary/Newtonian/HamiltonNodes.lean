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
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h3 ⊢
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
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h3 ⊢
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

/-! ### Directional derivative (`stepP:p6:he-dir`) -/

/-- Position block of body `i`, as a continuous linear map. -/
private def hnPos (i : Fin n) : Phase (n * 2) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n * 2) => ℝ)
      (finProdFinEquiv (i, k))).comp
      (ContinuousLinearMap.fst ℝ (Fin (n * 2) → ℝ) (Fin (n * 2) → ℝ))

/-- Momentum block of body `i`, as a continuous linear map. -/
private def hnMom (i : Fin n) : Phase (n * 2) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n * 2) => ℝ)
      (finProdFinEquiv (i, k))).comp
      (ContinuousLinearMap.snd ℝ (Fin (n * 2) → ℝ) (Fin (n * 2) → ℝ))

private theorem hnPos_apply (i : Fin n) (z : Phase (n * 2)) : hnPos i z = bodyVector z.1 i := rfl

private theorem hnMom_apply (i : Fin n) (z : Phase (n * 2)) : hnMom i z = bodyVector z.2 i := rfl

/-- `w ↦ v · w` as a continuous linear functional. -/
private def hnDot (v : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ∑ k, v k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k

private theorem hnDot_apply (v w : Fin 2 → ℝ) : hnDot v w = planeDot v w := by
  simp [hnDot, planeDot]

private theorem hasFDerivAt_hnSq (v : Fin 2 → ℝ) :
    HasFDerivAt planeSq ((2 : ℝ) • hnDot v) v := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).hasFDerivAt (x := v)).pow 2)
  refine h.congr_fderiv ?_
  unfold hnDot
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext w
  simp [smul_smul]

private theorem hasFDerivAt_hnSq_comp (L : Phase (n * 2) →L[ℝ] (Fin 2 → ℝ)) (z : Phase (n * 2)) :
    HasFDerivAt (fun x => planeSq (L x)) (((2 : ℝ) • hnDot (L z)).comp L) z :=
  (hasFDerivAt_hnSq (L z)).comp z L.hasFDerivAt

private theorem hasFDerivAt_hnInv_comp (L : Phase (n * 2) →L[ℝ] (Fin 2 → ℝ)) {z : Phase (n * 2)}
    (hz : L z ≠ 0) :
    HasFDerivAt (fun x => (planeLength (L x))⁻¹)
      ((-((planeLength (L z) ^ 3)⁻¹) • hnDot (L z)).comp L) z :=
  (hasFDerivAt_inv_planeLength hz).comp z L.hasFDerivAt

/-- The common shape `H_Kep + c (b |Σ p_i|² - V)` of both Hamiltonians. -/
private noncomputable def hnShape (κ G : ℝ) (m : Fin n → ℝ) (c b : ℝ) (z : Phase (n * 2)) : ℝ :=
  keplerPart κ m z + c * (b * planeSq (∑ i, bodyVector z.2 i) - pairPotential G m z.1)

private theorem movingHamiltonian_eq_hnShape (G m0 : ℝ) (m : Fin n → ℝ) (μ : ℝ) :
    movingHamiltonian G m0 m μ = hnShape (G * m0) G m μ (1 / (2 * m0)) := by
  funext z
  rw [movingHamiltonian_split]
  unfold hnShape fMov
  ring

private theorem fixedHamiltonian_eq_hnShape (G m0 : ℝ) (m : Fin n → ℝ) (ε : ℝ) :
    fixedHamiltonian G m0 m ε = hnShape (G * m0) G m ε 0 := by
  funext z
  rw [fixedHamiltonian_split]
  unfold hnShape fFix
  ring

private theorem hasFDerivAt_hnShape (κ G : ℝ) (m : Fin n → ℝ) (c b : ℝ) {z : Phase (n * 2)}
    (hz : NoCollision z.1) :
    ∃ D : Phase (n * 2) →L[ℝ] ℝ, HasFDerivAt (hnShape κ G m c b) D z ∧ ∀ d : Phase (n * 2),
      D d = (∑ i, (planeDot (bodyVector z.2 i) (bodyVector d.2 i) / m i +
          κ * m i * ((planeLength (bodyVector z.1 i) ^ 3)⁻¹ *
            planeDot (bodyVector z.1 i) (bodyVector d.1 i)))) +
        c * (b * (2 * planeDot (∑ i, bodyVector z.2 i) (∑ i, bodyVector d.2 i)) +
          ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), G * m i * m j *
            ((planeLength (bodyVector z.1 i - bodyVector z.1 j) ^ 3)⁻¹ *
              planeDot (bodyVector z.1 i - bodyVector z.1 j)
                (bodyVector d.1 i - bodyVector d.1 j))) := by
  have hv : ∀ i, hnPos i z ≠ 0 := fun i => planeLength_pos_iff.mp (hz.1 i)
  have hw : ∀ i j, i ≠ j → (hnPos i - hnPos j) z ≠ 0 := fun i j hij =>
    planeLength_pos_iff.mp (hz.2 i j hij)
  have hK := HasFDerivAt.fun_sum (u := Finset.univ)
    (A := fun i (x : Phase (n * 2)) => planeSq (hnMom i x) * (2 * m i)⁻¹ -
      κ * m i * (planeLength (hnPos i x))⁻¹)
    (fun i _ => ((hasFDerivAt_hnSq_comp (hnMom i) z).mul_const (2 * m i)⁻¹).sub
      ((hasFDerivAt_hnInv_comp (hnPos i) (hv i)).const_mul (κ * m i)))
  have hP := HasFDerivAt.fun_sum (u := Finset.univ)
    (A := fun i (x : Phase (n * 2)) => ∑ j ∈ Finset.univ.filter (fun j => i < j),
      G * m i * m j * (planeLength ((hnPos i - hnPos j) x))⁻¹)
    (fun i _ => HasFDerivAt.fun_sum (u := Finset.univ.filter (fun j => i < j))
      (A := fun j (x : Phase (n * 2)) => G * m i * m j * (planeLength ((hnPos i - hnPos j) x))⁻¹)
      (fun j hj => (hasFDerivAt_hnInv_comp (hnPos i - hnPos j)
        (hw i j (Finset.mem_filter.mp hj).2.ne)).const_mul (G * m i * m j)))
  have hS := hasFDerivAt_hnSq_comp (∑ i, hnMom i : Phase (n * 2) →L[ℝ] (Fin 2 → ℝ)) z
  have hH := hK.add (((hS.const_mul b).sub hP).const_mul c)
  refine ⟨_, hH.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_), ?_⟩
  · simp only [Pi.add_apply, Pi.sub_apply, hnShape, keplerPart, pairPotential,
      sum_apply, hnMom_apply, hnPos_apply, div_eq_mul_inv,
      sub_apply]
  · intro d
    simp only [add_apply, sub_apply,
      smul_apply, ContinuousLinearMap.comp_apply,
      sum_apply, hnDot_apply, hnMom_apply, hnPos_apply, smul_eq_mul, mul_neg,
      neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

private theorem planeDot_smul_right' (c : ℝ) (v w : Fin 2 → ℝ) :
    planeDot v (c • w) = c * planeDot v w := by
  simp only [planeDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem hn_bodyVector_zero (i : Fin n) :
    bodyVector (0 : Fin (n * 2) → ℝ) i = 0 := rfl

private theorem planeDot_zero_right' (v : Fin 2 → ℝ) : planeDot v 0 = 0 := by simp [planeDot]

/-- Kinetic derivative `Σ δp_i · (p_i/m_i + (μ/m₀) P)`, with `P = Σ p_i`. -/
private theorem kinetic_dir (m : Fin n → ℝ) (μ m0 : ℝ) (p dp : Fin (n * 2) → ℝ) :
    ∑ i, planeDot (bodyVector dp i)
        ((1 / m i) • bodyVector p i + (μ / m0) • ∑ j, bodyVector p j) =
      (∑ i, planeDot (bodyVector p i) (bodyVector dp i) / m i) +
        μ * (1 / (2 * m0) * (2 * planeDot (∑ i, bodyVector p i) (∑ i, bodyVector dp i))) := by
  have h1 : ∀ i, planeDot (bodyVector dp i)
      ((1 / m i) • bodyVector p i + (μ / m0) • ∑ j, bodyVector p j) =
      planeDot (bodyVector p i) (bodyVector dp i) / m i +
        μ / m0 * planeDot (bodyVector dp i) (∑ j, bodyVector p j) := fun i => by
    rw [planeDot_add_right, planeDot_smul_right', planeDot_smul_right',
      planeDot_comm (bodyVector dp i)]
    ring
  have h2 : ∑ i, planeDot (bodyVector dp i) (∑ j, bodyVector p j) =
      planeDot (∑ i, bodyVector dp i) (∑ j, bodyVector p j) := (planeDot_sum_left _ _ _).symm
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, h2]
  rw [planeDot_comm (∑ i, bodyVector dp i)]
  ring

/-- The position-direction part of the derivative of the common shape. -/
private theorem hn_potential_dir (G m0 c : ℝ) (m : Fin n → ℝ) (z d : Phase (n * 2)) :
    (∑ i, G * m0 * m i * ((planeLength (bodyVector z.1 i) ^ 3)⁻¹ *
        planeDot (bodyVector z.1 i) (bodyVector d.1 i))) +
      c * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), G * m i * m j *
        ((planeLength (bodyVector z.1 i - bodyVector z.1 j) ^ 3)⁻¹ *
          planeDot (bodyVector z.1 i - bodyVector z.1 j)
            (bodyVector d.1 i - bodyVector d.1 j)) =
    G * m0 * ∑ i, m i * ((planeLength (bodyVector z.1 i) ^ 3)⁻¹ *
        planeDot (bodyVector z.1 i) (bodyVector d.1 i)) +
      c * G * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), m i * m j *
        ((planeLength (bodyVector z.1 i - bodyVector z.1 j) ^ 3)⁻¹ *
          planeDot (bodyVector z.1 i - bodyVector z.1 j)
            (bodyVector d.1 i - bodyVector d.1 j)) := by
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `stepP:p6:he-dir` for `H_mov`: `DT(p) δp = Σ δp_i · (p_i/m_i + (μ/m₀) P)`,
`DV(q) δq = G m₀ Σ m_i q_i·δq_i/ℓ(q_i)³
+ μ G Σ_{i<j} m_i m_j (q_i - q_j)·(δq_i - δq_j)/ℓ(q_i - q_j)³`,
and `DH = DV + DT`. -/
theorem fderiv_movingHamiltonian_dir (G m0 : ℝ) (m : Fin n → ℝ) (μ : ℝ) {z : Phase (n * 2)}
    (hz : NoCollision z.1) (d : Phase (n * 2)) :
    fderiv ℝ (movingHamiltonian G m0 m μ) z (0, d.2) =
        ∑ i, planeDot (bodyVector d.2 i)
          ((1 / m i) • bodyVector z.2 i + (μ / m0) • ∑ j, bodyVector z.2 j) ∧
      fderiv ℝ (movingHamiltonian G m0 m μ) z (d.1, 0) =
        G * m0 * ∑ i, m i * ((planeLength (bodyVector z.1 i) ^ 3)⁻¹ *
            planeDot (bodyVector z.1 i) (bodyVector d.1 i)) +
          μ * G * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), m i * m j *
            ((planeLength (bodyVector z.1 i - bodyVector z.1 j) ^ 3)⁻¹ *
              planeDot (bodyVector z.1 i - bodyVector z.1 j)
                (bodyVector d.1 i - bodyVector d.1 j)) ∧
      fderiv ℝ (movingHamiltonian G m0 m μ) z d =
        fderiv ℝ (movingHamiltonian G m0 m μ) z (d.1, 0) +
          fderiv ℝ (movingHamiltonian G m0 m μ) z (0, d.2) := by
  obtain ⟨D, hD, hDd⟩ := hasFDerivAt_hnShape (G * m0) G m μ (1 / (2 * m0)) hz
  rw [movingHamiltonian_eq_hnShape, hD.fderiv]
  have hsplit : D d = D (d.1, 0) + D (0, d.2) := by rw [← map_add]; simp
  refine ⟨?_, ?_, hsplit⟩
  · rw [hDd, kinetic_dir]
    simp only [hn_bodyVector_zero, planeDot_zero_right', mul_zero, add_zero, Finset.sum_const_zero,
      sub_self]
  · rw [hDd]
    simp only [hn_bodyVector_zero, planeDot_zero_right', mul_zero, zero_div,
      Finset.sum_const_zero, zero_add]
    exact hn_potential_dir G m0 μ m z d

/-- `stepP:p6:he-dir` for `H_fix` (the potential with `μ` replaced by `ε`). -/
theorem fderiv_fixedHamiltonian_dir (G m0 : ℝ) (m : Fin n → ℝ) (ε : ℝ) {z : Phase (n * 2)}
    (hz : NoCollision z.1) (d : Phase (n * 2)) :
    fderiv ℝ (fixedHamiltonian G m0 m ε) z (0, d.2) =
        ∑ i, planeDot (bodyVector d.2 i) ((1 / m i) • bodyVector z.2 i) ∧
      fderiv ℝ (fixedHamiltonian G m0 m ε) z (d.1, 0) =
        G * m0 * ∑ i, m i * ((planeLength (bodyVector z.1 i) ^ 3)⁻¹ *
            planeDot (bodyVector z.1 i) (bodyVector d.1 i)) +
          ε * G * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), m i * m j *
            ((planeLength (bodyVector z.1 i - bodyVector z.1 j) ^ 3)⁻¹ *
              planeDot (bodyVector z.1 i - bodyVector z.1 j)
                (bodyVector d.1 i - bodyVector d.1 j)) ∧
      fderiv ℝ (fixedHamiltonian G m0 m ε) z d =
        fderiv ℝ (fixedHamiltonian G m0 m ε) z (d.1, 0) +
          fderiv ℝ (fixedHamiltonian G m0 m ε) z (0, d.2) := by
  obtain ⟨D, hD, hDd⟩ := hasFDerivAt_hnShape (G * m0) G m ε 0 hz
  rw [fixedHamiltonian_eq_hnShape, hD.fderiv]
  have hsplit : D d = D (d.1, 0) + D (0, d.2) := by rw [← map_add]; simp
  refine ⟨?_, ?_, hsplit⟩
  · rw [hDd]
    simp only [hn_bodyVector_zero, planeDot_zero_right', mul_zero, add_zero,
      Finset.sum_const_zero, zero_mul, sub_self]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [planeDot_smul_right', planeDot_comm (bodyVector d.2 i)]
    ring
  · rw [hDd]
    simp only [hn_bodyVector_zero, planeDot_zero_right', mul_zero, zero_div,
      Finset.sum_const_zero, zero_add]
    exact hn_potential_dir G m0 ε m z d

/-! ### Algebra of the splitting (`stepP:p6:sp-alg`) -/

/-- `sp-alg`, the identity `|Σ v_i|² = Σ |v_i|² + 2 Σ_{i<j} v_i · v_j`. -/
private theorem hn_sum_sum_eq (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j = f j i) :
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
  have hswap : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [hf i j]
  simp only [hsplit, Finset.sum_add_distrib, hswap, Finset.sum_filter]
  ring

private theorem hn_planeSq_sum (v : Fin n → Fin 2 → ℝ) :
    planeSq (∑ i, v i) =
      ∑ i, planeSq (v i) +
        2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), planeDot (v i) (v j) := by
  have h : planeSq (∑ i, v i) = ∑ i, ∑ j, planeDot (v i) (v j) := by
    simp only [planeSq, planeDot, Finset.sum_apply, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  rw [h, hn_sum_sum_eq (fun i j => planeDot (v i) (v j))
    (fun i j => by simp only [planeDot, mul_comm])]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [planeSq_eq_planeDot]

/-- `stepP:p6:sp-alg`: the kinetic part of `H_mov`
(`Σ (1/m_i + μ/m₀)|p_i|²/2 + (μ/m₀) Σ_{i<j} p_i·p_j`) equals
`Σ |p_i|²/(2 m_i) + (μ/m₀) (1/2) |P|²`; the potential parts of `H_mov` and `H_fix` (at `ε = μ`)
agree; and the difference is `μ |P|²/(2 m₀)`. -/
theorem sp_alg (G m0 : ℝ) (m : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) :
    ((∑ i, (1 / m i + μ / m0) * planeSq (bodyVector z.2 i) / 2) +
        μ * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          planeDot (bodyVector z.2 i) (bodyVector z.2 j) / m0 =
      ∑ i, planeSq (bodyVector z.2 i) / (2 * m i) +
        μ / m0 * (1 / 2 * planeSq (∑ i, bodyVector z.2 i))) ∧
    (movingHamiltonian G m0 m μ z -
        ((∑ i, (1 / m i + μ / m0) * planeSq (bodyVector z.2 i) / 2) +
          μ * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            planeDot (bodyVector z.2 i) (bodyVector z.2 j) / m0) =
      fixedHamiltonian G m0 m μ z - ∑ i, planeSq (bodyVector z.2 i) / (2 * m i)) ∧
    (movingHamiltonian G m0 m μ z - fixedHamiltonian G m0 m μ z =
      μ * planeSq (∑ i, bodyVector z.2 i) / (2 * m0)) := by
  have hkin : (∑ i, (1 / m i + μ / m0) * planeSq (bodyVector z.2 i) / 2) +
        μ * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          planeDot (bodyVector z.2 i) (bodyVector z.2 j) / m0 =
      ∑ i, planeSq (bodyVector z.2 i) / (2 * m i) +
        μ / m0 * (1 / 2 * planeSq (∑ i, bodyVector z.2 i)) := by
    rw [hn_planeSq_sum (fun i => bodyVector z.2 i)]
    have h1 : ∀ i, (1 / m i + μ / m0) * planeSq (bodyVector z.2 i) / 2 =
        planeSq (bodyVector z.2 i) / (2 * m i) + μ / m0 * (1 / 2 * planeSq (bodyVector z.2 i)) :=
      fun i => by ring
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    ring
  have hdiff : movingHamiltonian G m0 m μ z - fixedHamiltonian G m0 m μ z =
      μ * planeSq (∑ i, bodyVector z.2 i) / (2 * m0) := by
    rw [moving_sub_fixed]
    ring
  refine ⟨hkin, ?_, hdiff⟩
  have e : μ / m0 * (1 / 2 * planeSq (∑ i, bodyVector z.2 i)) =
      μ * planeSq (∑ i, bodyVector z.2 i) / (2 * m0) := by ring
  linarith

end HamiltonNodes

end KAM.Planetary
