/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.GraphBridge
public import KAM.Application.Observables
public import KAM.Application.Tests.ClockGraph
public import KAM.Application.Tests.Confinement

/-!
# Tests of the graph bridge to the confinement

* **Both adapters feed `twoTorus_confinement`** (`bridge_confined`), on the toy system of
  `Tests/Confinement` (`H(θ, a) = −a₂`, field `((0, −1), 0)`):
  - the torus `a = (−1/2, 0)` in the identity parametrization, through the near-identity adapter
    (`flat_isAngleGraph`: `IsAngleGraph` with `L = 0`, then `IsAngleGraph.toGraphTorus`);
  - the torus `a = (1/2, 0)` in the **sheared** parametrization `A(θ) = (θ₀, θ₁ + 3 sin 2πθ₀)`,
    through the clock-triangular adapter (`shear_isClockAngleGraph`: clock angle `0`, free
    angle `1`, `∂₁A₁ = 1`, then `IsAnalyticAngleGraph.toGraphTorus`). Its off-diagonal entry
    `∂₀A₁ = 6π cos 2πθ₀` reaches `6π`, so the near-identity criterion fails for it
    (`shear_not_derivNearId`: no `L < 1`): the clock criterion goes beyond near-identity.
  The solution through `(0, (0, 0))` exists for all times, stays strictly between the tori and is
  unique.
* **A certified torus through the bridge** (`toyCert2_graphTorus_clock`,
  `toyCert2_graphTorus_nearId`): the exact torus of the certified toy T2, with the action box
  from `checkActionRangeReal`, is a `GraphTorus` of `X_{realHam c.H}` on the level `E₀`, through
  either graph adapter (`IsClockAngleGraph.toGraphTorusOfModel`,
  `IsAngleGraph.toGraphTorusOfModel`).

No certified torus with a large off-diagonal `∂_l U_i` is available cheaply (for an integrable
toy the exact torus at a Diophantine frequency has constant `U`), so the sheared case is tested at
the pure level.
-/

@[expose] public noncomputable section

open Set Function Real

namespace KAM.Application.Tests.GraphBridge

open KAM KAM.Certificate KAM.Application KAM.Application.Confinement
  KAM.Application.Tests.Confinement

/-! ### Derivatives along lines -/

/-- `fderiv f θ v` is the derivative of `t ↦ f(θ + t v)` at `0`. -/
theorem fderiv_apply_of_hasDerivAt {f : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {θ v w : Fin 2 → ℝ}
    (hd : DifferentiableAt ℝ f θ) (h : HasDerivAt (fun t : ℝ => f (θ + t • v)) w 0) :
    fderiv ℝ f θ v = w := by
  have hline : HasDerivAt (fun t : ℝ => θ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add θ
  have hd' : HasFDerivAt f (fderiv ℝ f θ) (θ + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
  exact (hd'.comp_hasDerivAt (x := (0 : ℝ)) hline).unique h

/-! ### The near-identity torus (identity parametrization) -/

/-- The flat torus `a = (c, 0)`, identity parametrization. -/
def flatK (c : ℝ) (θ : Fin 2 → ℝ) : Phase := (θ, ![c, 0])

theorem analyticOnNhd_flatK (c : ℝ) : AnalyticOnNhd ℝ (flatK c) univ := fun _ _ =>
  analyticAt_id.prod analyticAt_const

theorem flatK_add_int (c : ℝ) (θ : Fin 2 → ℝ) (m : Fin 2 → ℤ) :
    flatK c (θ + fun i => (m i : ℝ)) = flatK c θ + (fun i => (m i : ℝ), 0) := by
  simp [flatK]

/-- The near-identity adapter: `‖DA - 1‖ = 0`. -/
theorem flat_isAngleGraph (c : ℝ) : IsAngleGraph (flatK c) 0 :=
  isAngleGraph_of_derivNearId (analyticOnNhd_flatK c) (flatK_add_int c)
    (fun x => ⟨differentiableAt_id, by
      rw [show torusAngle (flatK c) = id from rfl, fderiv_id, sub_self, norm_zero]⟩) one_pos

theorem flat_flow (c : ℝ) (θ : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => flatK c (θ + s • ![0, -1])) (toyV (flatK c (θ + t • ![0, -1]))) t := by
  have h := (((hasDerivAt_id t).smul_const (![0, -1] : Fin 2 → ℝ)).const_add θ).prodMk
    (hasDerivAt_const t (![c, 0] : Fin 2 → ℝ))
  simpa [toyV, flatK] using h

/-- The torus `a = (c, 0)` through the near-identity adapter and the bridge. -/
def nearTorus (c : ℝ) : GraphTorus toyV toyH 0 ![c, 0] ![c, 0] :=
  (flat_isAngleGraph c).toGraphTorus (analyticOnNhd_flatK c) ![0, -1] (flat_flow c)
    (fun _ => by simp [toyH, flatK]) (fun _ => ⟨le_rfl, le_rfl⟩)

/-! ### The sheared torus (clock-triangular, far from the identity) -/

/-- The shear `u(θ) = 3 sin 2πθ₀`. -/
def shearU (θ : Fin 2 → ℝ) : ℝ := 3 * Real.sin (2 * π * θ 0)

/-- The flat torus `a = (c, 0)` in the sheared parametrization `A(θ) = (θ₀, θ₁ + 3 sin 2πθ₀)`. -/
def shearK (c : ℝ) (θ : Fin 2 → ℝ) : Phase := (θ + shearU θ • Pi.single 1 1, ![c, 0])

theorem torusAngle_shearK (c : ℝ) (θ : Fin 2 → ℝ) :
    torusAngle (shearK c) θ = θ + shearU θ • Pi.single 1 1 := rfl

theorem analyticOnNhd_shearK (c : ℝ) : AnalyticOnNhd ℝ (shearK c) univ := by
  intro θ _
  have hu : AnalyticAt ℝ shearU θ := by
    unfold shearU
    have h0 : AnalyticAt ℝ (fun θ : Fin 2 → ℝ => θ 0) θ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).analyticAt θ
    exact analyticAt_const.mul (Real.analyticAt_sin.comp (analyticAt_const.mul h0))
  exact (analyticAt_id.add (hu.smul analyticAt_const)).prod analyticAt_const

/-- `u` does not depend on `θ₁`. -/
theorem shearU_add_single (θ : Fin 2 → ℝ) (t : ℝ) (v : Fin 2 → ℝ) (hv : v 0 = 0) :
    shearU (θ + t • v) = shearU θ := by
  simp [shearU, hv]

theorem shearU_add_int (θ : Fin 2 → ℝ) (m : Fin 2 → ℤ) :
    shearU (θ + fun i => (m i : ℝ)) = shearU θ := by
  unfold shearU
  rw [Pi.add_apply, show 2 * π * (θ 0 + (m 0 : ℝ)) = 2 * π * θ 0 + (m 0 : ℤ) * (2 * π) by ring,
    Real.sin_add_int_mul_two_pi]

theorem shearK_add_int (c : ℝ) (θ : Fin 2 → ℝ) (m : Fin 2 → ℤ) :
    shearK c (θ + fun i => (m i : ℝ)) = shearK c θ + (fun i => (m i : ℝ), 0) := by
  refine Prod.ext ?_ (by simp [shearK])
  simp only [shearK, shearU_add_int, Prod.fst_add]
  abel

theorem differentiableAt_torusAngle_shearK (c : ℝ) (θ : Fin 2 → ℝ) :
    DifferentiableAt ℝ (torusAngle (shearK c)) θ :=
  (analyticOnNhd_torusAngle (analyticOnNhd_shearK c) θ (mem_univ θ)).differentiableAt

/-- **The sheared torus is a clock-triangular graph**: clock angle `0` (`A₀ = θ₀`), free angle `1`
with `∂₁A₁ = 1`. -/
theorem shear_isClockAngleGraph (c : ℝ) : IsClockAngleGraph (shearK c) 1 0 1 := by
  refine isClockAngleGraph_of_clock (analyticOnNhd_shearK c) (shearK_add_int c) one_pos
    (fun θ l hl => ?_) (fun θ => ?_)
  · have : l = 0 := by fin_cases l <;> simp_all
    subst this
    simp [torusAngle_shearK]
  · have h : fderiv ℝ (torusAngle (shearK c)) θ (Pi.single 1 1) = Pi.single 1 1 := by
      refine fderiv_apply_of_hasDerivAt (differentiableAt_torusAngle_shearK c θ) ?_
      have e : (fun t : ℝ => torusAngle (shearK c) (θ + t • (Pi.single 1 1 : Fin 2 → ℝ))) =
          fun t => (θ + shearU θ • Pi.single 1 1) + t • (Pi.single 1 1 : Fin 2 → ℝ) := by
        funext t
        rw [torusAngle_shearK, shearU_add_single θ t _ (by simp)]
        abel
      rw [e]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single 1 1 : Fin 2 → ℝ)).const_add
        (θ + shearU θ • (Pi.single 1 1 : Fin 2 → ℝ))
    rw [h]
    simp

/-- **The sheared torus is not near the identity**: `∂₀A₁(0) = 6π`, so `‖DA(0) - 1‖ ≥ 6π` and no
`DerivNearId` bound with `L < 1` holds. -/
theorem shear_not_derivNearId (c : ℝ) {L : ℝ} (hL : L < 1) :
    ¬ DerivNearId (torusAngle (shearK c)) L := by
  intro hN
  set e₀ : Fin 2 → ℝ := Pi.single 0 1
  set e₁ : Fin 2 → ℝ := Pi.single 1 1
  have hD : fderiv ℝ (torusAngle (shearK c)) 0 e₀ = e₀ + (6 * π) • e₁ := by
    refine fderiv_apply_of_hasDerivAt (differentiableAt_torusAngle_shearK c 0) ?_
    have e : (fun t : ℝ => torusAngle (shearK c) (0 + t • e₀)) =
        fun t => t • e₀ + (3 * Real.sin (2 * π * t)) • e₁ := by
      funext t
      simp [torusAngle_shearK, shearU, e₀, e₁]
    rw [e]
    have hs : HasDerivAt (fun t : ℝ => 3 * Real.sin (2 * π * t)) (6 * π) 0 := by
      have := ((Real.hasDerivAt_sin (2 * π * 0)).comp (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).const_mul (2 * π))).const_mul 3
      convert this using 1
      · rfl
      · simp only [mul_zero, Real.cos_zero, mul_one]
        ring
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const e₀).add (hs.smul_const e₁)
    simp only [id, one_smul] at h
    exact h
  have h1 : ‖(fderiv ℝ (torusAngle (shearK c)) 0 - ContinuousLinearMap.id ℝ (Fin 2 → ℝ)) e₀‖ ≤
      L := by
    have := ((fderiv ℝ (torusAngle (shearK c)) 0 - ContinuousLinearMap.id ℝ (Fin 2 → ℝ)).le_opNorm
      e₀).trans (mul_le_mul_of_nonneg_right (hN 0).2 (norm_nonneg _))
    simpa [e₀, Pi.norm_single] using this
  rw [sub_apply, hD, ContinuousLinearMap.id_apply, add_sub_cancel_left,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), Pi.norm_single, norm_one,
    mul_one] at h1
  linarith [Real.pi_gt_three]

theorem shear_flow (c : ℝ) (θ : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => shearK c (θ + s • ![0, -1]))
      (toyV (shearK c (θ + t • ![0, -1]))) t := by
  have e : (fun s : ℝ => shearK c (θ + s • ![0, -1])) =
      fun s => ((θ + shearU θ • Pi.single 1 1) + s • (![0, -1] : Fin 2 → ℝ),
        (![c, 0] : Fin 2 → ℝ)) := by
    funext s
    have hu : shearU (θ + s • ![0, -1]) = shearU θ := shearU_add_single θ s _ (by simp)
    simp only [shearK, hu]
    congr 1
    abel
  rw [e]
  have h := (((hasDerivAt_id t).smul_const (![0, -1] : Fin 2 → ℝ)).const_add
    (θ + shearU θ • (Pi.single 1 1 : Fin 2 → ℝ))).prodMk (hasDerivAt_const t (![c, 0] : Fin 2 → ℝ))
  simpa [toyV] using h

/-- The torus `a = (c, 0)` through the clock-triangular adapter (sheared) and the bridge. -/
def shearTorus (c : ℝ) : GraphTorus toyV toyH 0 ![c, 0] ![c, 0] :=
  (shear_isClockAngleGraph c).toIsAnalyticAngleGraph.toGraphTorus ![0, -1] (shear_flow c)
    (fun _ => by simp [toyH, shearK]) (fun _ => ⟨le_rfl, le_rfl⟩)

/-! ### Both adapters feed the confinement -/

/-- **Confinement between a near-identity torus and a sheared clock torus**: the solution of the
toy field through `(0, (0, 0))` exists for all times, stays strictly between `a₁ = −1/2` (the
near-identity torus) and `a₁ = 1/2` (the sheared clock torus), and is the only global solution
through that point. -/
theorem bridge_confined :
    ∃ w : ℝ → Phase, w 0 = (0, ![0, 0]) ∧ (∀ t, HasDerivAt w (toyV (w t)) t ∧
      -1 / 2 < (w t).2 0 ∧ (w t).2 0 < 1 / 2) ∧
      ∀ w' : ℝ → Phase, w' 0 = (0, ![0, 0]) → (∀ t, HasDerivAt w' (toyV (w' t)) t) → w' = w := by
  obtain ⟨K, C, hV, hVC⟩ := toy_lipschitz ![-1, -1] ![1, 1]
  have hd : ∀ p : Phase, DifferentiableAt ℝ toyH p := fun p =>
    (hasFDerivAt_toyH p).differentiableAt
  have g₁ : ∀ φ, (nearTorus (-1 / 2)).graph₁ φ = -1 / 2 := fun φ => by
    simp [GraphTorus.graph₁, nearTorus, IsAngleGraph.toGraphTorus,
      IsAnalyticAngleGraph.toGraphTorus, flatK]
  have g₂ : ∀ φ, (shearTorus (1 / 2)).graph₁ φ = 1 / 2 := fun φ => by
    simp [GraphTorus.graph₁, shearTorus, IsAnalyticAngleGraph.toGraphTorus, shearK]
  obtain ⟨w, hw0, hw, huniq⟩ := twoTorus_confinement (nearTorus (-1 / 2)) (shearTorus (1 / 2))
    hV hVC (fun p _ => hd p) (fun p _ => by simp [fderiv_toyH, toyV])
    (m := 1) one_pos (fun p _ => by simp [fderiv_toyH])
    (fun j => by fin_cases j <;> norm_num) (fun j => by fin_cases j <;> norm_num)
    (fun j => by fin_cases j <;> norm_num) (fun j => by fin_cases j <;> norm_num)
    (by norm_num) (by norm_num)
    (fun θ a _ _ => ⟨fun h => by simp [toyH, h], fun h => by simp [toyH, h]⟩)
    (w₀ := (0, ![0, 0]))
    ⟨fun j => by fin_cases j <;> norm_num, fun j => by fin_cases j <;> norm_num⟩
    (by simp [toyH]) (by rw [g₁]; norm_num) (by rw [g₂]; norm_num)
  refine ⟨w, hw0, fun t => ⟨(hw t).1, ?_, ?_⟩, huniq⟩
  · simpa [g₁] using (hw t).2.2.2.1
  · simpa [g₂] using (hw t).2.2.2.2

/-! ### The certified toy T2 through the bridge -/

theorem toyCert2_actionRows :
    checkActionRangeReal toyCert2 0 (975 / 1000) (1 / 1000) = true ∧
      checkActionRangeReal toyCert2 1 (-4757 / 10000) (1 / 1000) = true := by
  decide +kernel

theorem toyCert2_angleGraphReal : checkAngleGraphReal toyCert2 (1 / 2) = true := by
  decide +kernel

/-- The action box of T2's exact torus: `[ctr - r - disp, ctr + r + disp]` per action. -/
def toyLo : Fin 2 → ℝ := fun i => ![974 / 1000, -4767 / 10000] i - toyCert2.params.disp

/-- The upper corner of T2's action box. -/
def toyHi : Fin 2 → ℝ := fun i => ![976 / 1000, -4747 / 10000] i + toyCert2.params.disp

/-- The exact real torus of T2 lies in the action box (`checkActionRangeReal`). -/
theorem mem_toyBox {Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {sinf : ℝ}
    (hT : CertifiedTorusAt toyCert2 ![lunarNuMinus / 2, 1 / 2] Kinf sinf) (θ : Fin 2 → ℝ) :
    (realRestriction Kinf θ).2 ∈ Icc toyLo toyHi := by
  have hs := ClockTests.toyCert2_static_hamBounds.1
  have a0 := abs_le.1 (hT.abs_action_sub_ctr_le_real hs (i := 0) toyCert2_actionRows.1 θ)
  have a1 := abs_le.1 (hT.abs_action_sub_ctr_le_real hs (i := 1) toyCert2_actionRows.2 θ)
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    simp [toyLo, toyHi] at a0 a1 ⊢ <;> linarith [a0.1, a0.2, a1.1, a1.2]

/-- **T2 through the clock adapter and the bridge**: the exact torus of T2 (at `s∞ = 2`) is a
confinement `GraphTorus` of `X_{realHam c.H}` on the level `E₀`. -/
theorem toyCert2_graphTorus_clock : ∃ Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ),
    CertifiedTorusAt toyCert2 ![lunarNuMinus / 2, 1 / 2] Kinf 2 ∧
    ∃ T : GraphTorus (hamiltonianVectorField (realHam toyCert2.H)) (realHam toyCert2.H)
      toyCert2.params.E0 toyLo toyHi, T.k = realRestriction Kinf := by
  obtain ⟨Kinf, hT, hR, _cc, hG⟩ := ClockTests.toyCert2_clockGraph
  exact ⟨Kinf, hT, hG.toGraphTorusOfModel hR (mem_toyBox hT), rfl⟩

/-- **T2 through the near-identity adapter and the bridge.** -/
theorem toyCert2_graphTorus_nearId : ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ))
    (sinf : ℝ), CertifiedTorusAt toyCert2 ![lunarNuMinus / 2, 1 / 2] Kinf sinf ∧
    ∃ T : GraphTorus (hamiltonianVectorField (realHam toyCert2.H)) (realHam toyCert2.H)
      toyCert2.params.E0 toyLo toyHi,
      T.k = realRestriction Kinf ∧ T.ν = sinf • ![lunarNuMinus / 2, 1 / 2] := by
  obtain ⟨Kinf, sinf, hT, hR, hG⟩ := toyCert2_torus.exists_realGraph_of_checks
    ClockTests.toyCert2_static_hamBounds.1 ClockTests.toyCert2_static_hamBounds.2
    (.inl toyCert2_angleGraphReal)
  exact ⟨Kinf, sinf, hT, hG.toGraphTorusOfModel hR (mem_toyBox hT), rfl, rfl⟩

end KAM.Application.Tests.GraphBridge
