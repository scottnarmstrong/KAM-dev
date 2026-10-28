/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.ParameterIntegral
public import KAM.Planetary.Poincare.Chart

/-!
# Secular form: symmetries of the chart, evenness of the secular function

Blueprint P, Part 8 (`bpP:p8:symmetries`, `bpP:p8:evenness`).  The three chart identities (S1)-(S3)
are proved one planet at a time from the uniqueness of the regular Kepler equation, then lifted to
the product chart.  The Kepler functions are invariant under the induced isometries, and the cell
average of a `2π`-periodic function is invariant under translation and reflection of the angles
(by a fundamental-domain argument that needs no integrability).  `evenness_taylor` is the
consequence for odd-order derivatives at the circular orbit.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

section PlanarSymmetries

/-- The reflection `σ = diag(1, -1)` of the plane. -/
def sigmaRefl (v : Fin 2 → ℝ) : Fin 2 → ℝ := ![v 0, -v 1]

private theorem planeDot_two (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

private theorem planeDot_sigma (v w : Fin 2 → ℝ) :
    planeDot (sigmaRefl v) (sigmaRefl w) = planeDot v w := by
  simp [planeDot, Fin.sum_univ_two, sigmaRefl]

private theorem planeSq_two (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem gamma_mk (a x b y : ℝ) :
    poincareGamma ((![a, x] : Fin 2 → ℝ), (![b, y] : Fin 2 → ℝ)) = (x ^ 2 + y ^ 2) / 2 := by
  simp [poincareGamma]

private theorem keplerJac_eq' (v : Fin 2 → ℝ) (F : ℝ) :
    keplerJac v F = 1 - (v 0 * Real.cos F + v 1 * Real.sin F) := by
  simp [keplerJac, planeDot_two, orbitalUnit]

/-- (S1) for one planet: `(λ + π, -ξ, Λ, -η) ↦ (-q, -p)`. -/
theorem poincare_antipode {m κ : ℝ} {w : Phase 2} (hw : w ∈ poincareDom) :
    poincare m κ (![w.1 0 + π, -w.1 1], ![w.2 0, -w.2 1]) =
      (-(poincare m κ w).1, -(poincare m κ w).2) := by
  have hlen := (poincare_facts hw).2.2.2.2.2.1
  have hΓ : poincareGamma ((![w.1 0 + π, -w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      poincareGamma w := by
    rw [gamma_mk]; simp [poincareGamma]
  have hK : poincareK ((![w.1 0 + π, -w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      poincareK w := by
    simp only [poincareK, hΓ]; simp
  have hV : poincareV ((![w.1 0 + π, -w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      -poincareV w := by
    simp only [poincareV, hΓ]; ext i; fin_cases i <;> simp
  have hF : poincareF ((![w.1 0 + π, -w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      poincareF w + π := by
    unfold poincareF
    rw [hV]
    simp only [Matrix.cons_val_zero]
    refine keplerLong_unique (by rwa [planeLength_neg]) ?_
    have h := keplerPhi_keplerLong hlen (w.1 0)
    simp only [keplerPhi] at h ⊢
    simp only [Pi.neg_apply, Real.sin_add_pi, Real.cos_add_pi]
    linarith
  have hU : orbitalUnit (poincareF w + π) = -orbitalUnit (poincareF w) := by
    ext i; fin_cases i <;> simp [orbitalUnit]
  have hJ : keplerJac (-poincareV w) (poincareF w + π) = keplerJac (poincareV w) (poincareF w) := by
    rw [keplerJac_eq', keplerJac_eq']; simp
  have hD : planeDot (-poincareV w) (orbitalUnit (poincareF w + π)) =
      planeDot (poincareV w) (orbitalUnit (poincareF w)) := by
    rw [hU]; simp [planeDot_two]
  unfold poincare
  simp only [hK, hV, hF, hJ, hD, Matrix.cons_val_zero]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
    simp [hU, quarterTurn] <;> ring

/-- The planet block obtained by rotating the angle and `(ξ, η)` by `θ`. -/
def rotBlock (θ : ℝ) (w : Phase 2) : Phase 2 :=
  (![w.1 0 + θ, (rot θ ![w.1 1, w.2 1]) 0], ![w.2 0, (rot θ ![w.1 1, w.2 1]) 1])

private theorem planeSq_rot' (g : ℝ) (v : Fin 2 → ℝ) : planeSq (rot g v) = planeSq v := by
  have := Real.sin_sq_add_cos_sq g
  simp only [planeSq_two, rot, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (v 0 ^ 2 + v 1 ^ 2) * this

/-- (S2) for one planet: simultaneous rotation of the angle and of `(ξ, η)`. -/
theorem poincare_rotate {m κ : ℝ} (θ : ℝ) {w : Phase 2} (hw : w ∈ poincareDom) :
    poincare m κ (rotBlock θ w) = (rot θ (poincare m κ w).1, rot θ (poincare m κ w).2) := by
  have hlen := (poincare_facts hw).2.2.2.2.2.1
  have hΓ : poincareGamma (rotBlock θ w) = poincareGamma w := by
    have := planeSq_rot' θ ![w.1 1, w.2 1]
    simp only [poincareGamma, rotBlock, Matrix.cons_val_zero, Matrix.cons_val_one,
      planeSq_two] at this ⊢
    linarith
  have hL : (rotBlock θ w).2 0 = w.2 0 := by simp [rotBlock]
  have hK : poincareK (rotBlock θ w) = poincareK w := by
    simp only [poincareK, hΓ, hL]
  have hV : poincareV (rotBlock θ w) = rot θ (poincareV w) := by
    unfold poincareV
    rw [hΓ, hL]
    ext i; fin_cases i <;> simp [rotBlock, rot] <;> ring
  have hF : poincareF (rotBlock θ w) = poincareF w + θ := by
    have hFw : poincareF w = keplerLong (w.1 0) (poincareV w) := rfl
    show keplerLong ((rotBlock θ w).1 0) (poincareV (rotBlock θ w)) = _
    have h0 : (rotBlock θ w).1 0 = w.1 0 + θ := by simp [rotBlock]
    rw [hV, h0, hFw]
    refine keplerLong_unique (by rwa [planeLength_rot]) ?_
    have h := keplerPhi_keplerLong hlen (w.1 0)
    generalize keplerLong (w.1 0) (poincareV w) = F at h ⊢
    simp only [keplerPhi] at h ⊢
    simp only [rot, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sin_add, Real.cos_add]
    have := Real.sin_sq_add_cos_sq θ
    linear_combination h + (-(poincareV w 0) * Real.sin F
      + poincareV w 1 * Real.cos F) * this
  have hU : orbitalUnit (poincareF w + θ) = rot θ (orbitalUnit (poincareF w)) := by
    ext i; fin_cases i <;> simp [orbitalUnit, rot, Real.sin_add, Real.cos_add] <;> ring
  have hD : planeDot (rot θ (poincareV w)) (orbitalUnit (poincareF w + θ)) =
      planeDot (poincareV w) (orbitalUnit (poincareF w)) := by
    rw [hU, planeDot_rot]
  have hJ : keplerJac (rot θ (poincareV w)) (poincareF w + θ) =
      keplerJac (poincareV w) (poincareF w) := by
    unfold keplerJac; rw [hD]
  unfold poincare
  simp only [hK, hV, hF, hJ, hU, planeDot_rot, hL]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
    simp [quarterTurn, rot] <;> ring

/-- (S3) for one planet: `(-λ, ξ, Λ, -η) ↦ (σq, -σp)`. -/
theorem poincare_reflect {m κ : ℝ} {w : Phase 2} (hw : w ∈ poincareDom) :
    poincare m κ (![-w.1 0, w.1 1], ![w.2 0, -w.2 1]) =
      (sigmaRefl (poincare m κ w).1, -sigmaRefl (poincare m κ w).2) := by
  have hlen := (poincare_facts hw).2.2.2.2.2.1
  have hΓ : poincareGamma ((![-w.1 0, w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      poincareGamma w := by
    rw [gamma_mk]; simp [poincareGamma]
  have hK : poincareK ((![-w.1 0, w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      poincareK w := by
    simp only [poincareK, hΓ]; simp
  have hV : poincareV ((![-w.1 0, w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      sigmaRefl (poincareV w) := by
    simp only [poincareV, hΓ, sigmaRefl]; ext i; fin_cases i <;> simp
  have hlen' : planeLength (sigmaRefl (poincareV w)) < 1 := by
    have : planeLength (sigmaRefl (poincareV w)) = planeLength (poincareV w) := by
      unfold planeLength; congr 1; simp [planeSq_two, sigmaRefl]
    rwa [this]
  have hF : poincareF ((![-w.1 0, w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      -poincareF w := by
    unfold poincareF
    rw [hV]
    simp only [Matrix.cons_val_zero]
    refine keplerLong_unique hlen' ?_
    have h := keplerPhi_keplerLong hlen (w.1 0)
    simp only [keplerPhi] at h ⊢
    simp only [sigmaRefl, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sin_neg, Real.cos_neg]
    linarith
  have hU : orbitalUnit (-poincareF w) = sigmaRefl (orbitalUnit (poincareF w)) := by
    ext i; fin_cases i <;> simp [orbitalUnit, sigmaRefl]
  have hD : planeDot (sigmaRefl (poincareV w)) (orbitalUnit (-poincareF w)) =
      planeDot (poincareV w) (orbitalUnit (poincareF w)) := by
    rw [hU]; simp [planeDot_two, sigmaRefl]
  have hJ : keplerJac (sigmaRefl (poincareV w)) (-poincareF w) =
      keplerJac (poincareV w) (poincareF w) := by
    unfold keplerJac; rw [hD]
  unfold poincare
  simp only [hK, hV, hF, hJ, hU, planeDot_sigma, Matrix.cons_val_zero]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
    simp [quarterTurn, sigmaRefl] <;> ring

end PlanarSymmetries

section TorusAverage

variable {n : ℕ}

/-- The scaled standard basis spanning the lattice `2π ℤⁿ`. -/
private def twoPiUnit : ℝˣ := Units.mk0 (2 * π) (by positivity)

@[simp] private theorem twoPiUnit_val : (twoPiUnit : ℝ) = 2 * π := rfl

private def twoPiBasis (n : ℕ) : Module.Basis (Fin n) ℝ (SecularForm.Vec n) :=
  (Pi.basisFun ℝ (Fin n)).unitsSMul (fun _ => twoPiUnit)

private theorem twoPiBasis_apply (i : Fin n) :
    twoPiBasis n i = fun j => 2 * π * (if j = i then 1 else 0) := by
  ext j
  simp [twoPiBasis, Module.Basis.unitsSMul_apply, Pi.single_apply, Units.smul_def]

private theorem fundamentalDomain_twoPi (n : ℕ) :
    ZSpan.fundamentalDomain (twoPiBasis n) =
      Set.pi univ (fun _ : Fin n => Ico (0 : ℝ) (2 * π)) := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, Set.mem_pi, mem_univ, forall_true_left, mem_Ico]
  refine forall_congr' fun i => ?_
  simp only [twoPiBasis, Module.Basis.repr_unitsSMul]
  have h2 : 0 < 2 * π := by positivity
  simp only [Units.smul_def, twoPiUnit_val, Units.val_inv_eq_inv_val, smul_eq_mul,
    Pi.basisFun_repr]
  rw [le_inv_mul_iff₀ h2, inv_mul_lt_iff₀ h2]
  simp

/-- A function periodic under the lattice `2π ℤⁿ` is invariant under the span of the basis. -/
private theorem periodic_span {g : SecularForm.Vec n → ℝ}
    (hg : ∀ (k : Fin n → ℤ) t, g (t + fun i => 2 * π * k i) = g t)
    {v : SecularForm.Vec n} (hv : v ∈ Submodule.span ℤ (range (twoPiBasis n)))
    (x : SecularForm.Vec n) :
    g (v + x) = g x := by
  let H : AddSubgroup (SecularForm.Vec n) :=
    { carrier := {v | ∀ x, g (v + x) = g x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by rw [add_assoc, ha, hb]
      neg_mem' := fun {a} ha x => by rw [← ha (-a + x)]; simp }
  have hle : Submodule.span ℤ (range (twoPiBasis n)) ≤ AddSubgroup.toIntSubmodule H := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ x
    have := hg (Pi.single i 1) x
    rw [add_comm]
    convert this using 2
    rw [twoPiBasis_apply]; ext j; simp [Pi.single_apply]
  exact hle hv x

private instance countable_span (n : ℕ) :
    Countable (Submodule.span ℤ (range (twoPiBasis n))).toAddSubgroup := by
  have : (Submodule.span ℤ (range (twoPiBasis n)) : Set (SecularForm.Vec n)) ⊆
      range (fun k : Fin n → ℤ => ∑ i, k i • twoPiBasis n i) := by
    intro v hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv
    exact ⟨c, hc⟩
  exact (Set.countable_range _).mono this |>.to_subtype

private theorem isAddFundamentalDomain_cell (n : ℕ) :
    IsAddFundamentalDomain (Submodule.span ℤ (range (twoPiBasis n))).toAddSubgroup
      (Set.pi univ (fun _ : Fin n => Ico (0 : ℝ) (2 * π))) volume := by
  rw [← fundamentalDomain_twoPi]
  exact ZSpan.isAddFundamentalDomain' (twoPiBasis n) volume

private theorem setIntegral_cell_eq_Ico (n : ℕ) (h : SecularForm.Vec n → ℝ) :
    ∫ t in SecularForm.cell n, h t =
      ∫ t in Set.pi univ (fun _ : Fin n => Ico (0 : ℝ) (2 * π)), h t :=
  setIntegral_congr_set (MeasureTheory.Measure.ae_eq_set_pi fun _ _ => Ico_ae_eq_Icc.symm)

/-- Translation invariance of the cell integral of a lattice-periodic function. -/
theorem cell_integral_add {g : SecularForm.Vec n → ℝ}
    (hg : ∀ (k : Fin n → ℤ) t, g (t + fun i => 2 * π * k i) = g t) (c : SecularForm.Vec n) :
    ∫ t in SecularForm.cell n, g (t + c) = ∫ t in SecularForm.cell n, g t := by
  set D := Set.pi univ (fun _ : Fin n => Ico (0 : ℝ) (2 * π)) with hD
  have hfd := isAddFundamentalDomain_cell n
  rw [setIntegral_cell_eq_Ico, setIntegral_cell_eq_Ico]
  rw [← (measurePreserving_add_right volume c).setIntegral_image_emb
    (measurableEmbedding_addRight c) g D]
  refine IsAddFundamentalDomain.setIntegral_eq ?_ hfd (fun v x => ?_)
  · refine hfd.image_of_equiv (Equiv.addRight c) ?_ (AddEquiv.refl _).toEquiv ?_
    · rw [Equiv.addRight_symm]
      exact (measurePreserving_add_right volume (-c)).quasiMeasurePreserving
    · intro v x
      exact add_assoc (v : SecularForm.Vec n) x c
  · exact periodic_span hg v.2 x

/-- Reflection invariance of the cell integral of a lattice-periodic function. -/
theorem cell_integral_neg {g : SecularForm.Vec n → ℝ}
    (hg : ∀ (k : Fin n → ℤ) t, g (t + fun i => 2 * π * k i) = g t) :
    ∫ t in SecularForm.cell n, g (-t) = ∫ t in SecularForm.cell n, g t := by
  have hset : (fun t : SecularForm.Vec n => -t) '' SecularForm.cell n =
      (fun t => t + fun _ : Fin n => -(2 * π)) '' SecularForm.cell n := by
    ext y
    simp only [SecularForm.cell, mem_image, Set.mem_pi, mem_univ, forall_true_left, mem_Icc]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨-x + fun _ => 2 * π, fun i => ?_, ?_⟩
      · have := hx i; simp only [Pi.add_apply, Pi.neg_apply]
        constructor <;> linarith [this.1, this.2]
      · ext i; simp
    · rintro ⟨x, hx, rfl⟩
      refine ⟨-x + fun _ => 2 * π, fun i => ?_, ?_⟩
      · have := hx i; simp only [Pi.add_apply, Pi.neg_apply]
        constructor <;> linarith [this.1, this.2]
      · ext i; simp; ring
  have h1 := (Measure.measurePreserving_neg
    (volume : Measure (SecularForm.Vec n))).setIntegral_image_emb measurableEmbedding_neg g
    (SecularForm.cell n)
  have h2 := (measurePreserving_add_right (volume : Measure (SecularForm.Vec n))
    (fun _ : Fin n => -(2 * π))).setIntegral_image_emb (measurableEmbedding_addRight _) g
    (SecularForm.cell n)
  have h3 : (fun t : SecularForm.Vec n => -t) '' SecularForm.cell n =
      (fun t => t + fun _ : Fin n => -(2 * π)) '' SecularForm.cell n := hset
  rw [← h1, h3, h2]
  exact cell_integral_add hg _

end TorusAverage

section OddDerivative

/-- An even function has vanishing odd-order iterated derivatives at a point of evenness. -/
theorem iteratedFDeriv_odd_eq_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (h : f =ᶠ[𝓝 0] fun u => f (-u)) {m : ℕ} (hm : Odd m) :
    iteratedFDeriv ℝ m f 0 = 0 := by
  have e1 : iteratedFDeriv ℝ m f 0 = iteratedFDeriv ℝ m (fun u => f (-u)) 0 :=
    (h.iteratedFDeriv ℝ m).eq_of_nhds
  have e2 : iteratedFDeriv ℝ m (fun u => f (-u)) 0 =
      (iteratedFDeriv ℝ m f (-0)).compContinuousLinearMap
        fun _ => (ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E) := by
    have := (ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E).iteratedFDerivWithin_comp_right f
      (uniqueDiffOn_univ) (mem_univ (-(0 : E))) m
    simp only [preimage_univ, iteratedFDerivWithin_univ] at this
    exact this
  have e3 : (iteratedFDeriv ℝ m f (-0)).compContinuousLinearMap
        (fun _ => (ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E)) =
      -iteratedFDeriv ℝ m f 0 := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.neg_apply,
      neg_apply, neg_zero]
    have : (fun i => -v i) = fun i => (-1 : ℝ) • v i := by ext i; simp
    rw [this, ContinuousMultilinearMap.map_smul_univ]
    simp [hm.neg_one_pow]
  have e4 : iteratedFDeriv ℝ m f 0 = -iteratedFDeriv ℝ m f 0 := e1.trans (e2.trans e3)
  have e5 : (2 : ℝ) • iteratedFDeriv ℝ m f 0 = 0 := by
    rw [two_smul]; nth_rewrite 1 [e4]; exact neg_add_cancel _
  exact (smul_eq_zero.1 e5).resolve_left two_ne_zero

end OddDerivative

namespace SecularForm
variable {n : ℕ}

/-- Rotation of the slow blocks, using the delivered planar rotation. -/
def rotateSlow (t : ℝ) (x : Slow n) : Slow n :=
  (fun i => (rot t ![x.1 i,x.2.2 i]) 0, x.2.1,
    fun i => (rot t ![x.1 i,x.2.2 i]) 1)
def rotatePhysical (t : ℝ) (z : Phase (n*2)) : Phase (n*2) :=
  (ofBodies (fun i => rot t (bodyVector z.1 i)), ofBodies (fun i => rot t (bodyVector z.2 i)))

theorem planetBlock_assemble (I t p q : Vec n) (i : Fin n) :
    planetBlock (assemble I t p q) i = (![t i, q i], ![I i, p i]) := by
  simp [planetBlock, assemble, fast, slow]

theorem assemble_mem_iff (I t p q : Vec n) :
    assemble I t p q ∈ poincareProdDom n ↔ ∀ i, 0 < I i ∧ (q i ^ 2 + p i ^ 2) / 2 < I i := by
  simp [poincareProdDom, poincareDom, planetBlock_assemble, poincareGamma]

theorem mem_slowDom_iff (D : Data n) (x : Slow n) :
    x ∈ slowDom D ↔ ∀ i, 0 < x.2.1 i ∧ (x.1 i ^ 2 + x.2.2 i ^ 2) / 2 < x.2.1 i := by
  simp only [slowDom, mem_ofPred_eq, assemble_mem_iff]

theorem assemble_mem_slowDom (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) (t : Vec n) :
    assemble x.2.1 t x.2.2 x.1 ∈ poincareProdDom n := by
  rw [assemble_mem_iff]; exact (mem_slowDom_iff D x).1 hx

theorem poincareProd_assemble (D : Data n) (I t p q : Vec n) :
    poincareProd D.m (D.G * D.m0) (assemble I t p q) =
      ofPlanets fun i => poincare (D.m i) (D.G * D.m0) (![t i, q i], ![I i, p i]) := by
  rw [poincareProd_eq_ofPlanets]
  simp only [planetBlock_assemble]

theorem ofPlanets_map (A B : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (P : Fin n → Phase 2) :
    (ofBodies fun i => A (bodyVector (ofPlanets P).1 i),
        ofBodies fun i => B (bodyVector (ofPlanets P).2 i)) =
      ofPlanets fun i => (A (P i).1, B (P i).2) := by
  simp [ofPlanets, bodyVector_ofBodies]

theorem neg_ofPlanets (P : Fin n → Phase 2) :
    -ofPlanets P = ofPlanets fun i => (-(P i).1, -(P i).2) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> simp [ofPlanets, ofBodies]

theorem rotateSlow_mem (D : Data n) (θ : ℝ) {x : Slow n} (hx : x ∈ slowDom D) :
    rotateSlow θ x ∈ slowDom D := by
  rw [mem_slowDom_iff] at hx ⊢
  intro i
  have h := hx i
  refine ⟨h.1, ?_⟩
  have := Real.sin_sq_add_cos_sq θ
  simp only [rotateSlow, rot, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [this, h.2]

theorem symmetries (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) (t : Vec n) (θ : ℝ) :
    poincareProd D.m (D.G*D.m0) (assemble x.2.1 (t + fun _ => π) (-x.2.2) (-x.1)) =
      -poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1) ∧
    poincareProd D.m (D.G*D.m0)
      (assemble x.2.1 (t + fun _ => θ) (rotateSlow θ x).2.2 (rotateSlow θ x).1) =
      rotatePhysical θ (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)) ∧
    poincareProd D.m (D.G*D.m0) (assemble x.2.1 (-t) (-x.2.2) x.1) =
      (ofBodies (fun i => ![(bodyVector (poincareProd D.m (D.G*D.m0)
        (assemble x.2.1 t x.2.2 x.1)).1 i) 0,
        -(bodyVector (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i) 1]),
       ofBodies (fun i => ![-(bodyVector (poincareProd D.m (D.G*D.m0)
        (assemble x.2.1 t x.2.2 x.1)).2 i) 0,
        (bodyVector (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)).2 i) 1])) := by
  have hb : ∀ i, (![t i, x.1 i], ![x.2.1 i, x.2.2 i]) ∈ poincareDom := fun i => by
    have := (mem_slowDom_iff D x).1 hx i
    simpa [poincareDom, poincareGamma] using this
  refine ⟨?_, ?_, ?_⟩
  · rw [poincareProd_assemble, poincareProd_assemble, neg_ofPlanets]
    congr 1; funext i
    have := poincare_antipode (m := D.m i) (κ := D.G * D.m0) (hb i)
    simpa using this
  · rw [poincareProd_assemble, poincareProd_assemble]
    unfold rotatePhysical
    rw [ofPlanets_map (rot θ) (rot θ)]
    congr 1; funext i
    have := poincare_rotate (m := D.m i) (κ := D.G * D.m0) θ (hb i)
    simpa [rotBlock, rotateSlow] using this
  · rw [poincareProd_assemble, poincareProd_assemble]
    refine Eq.trans ?_ (ofPlanets_map sigmaRefl (fun v => ![-v 0, v 1]) _).symm
    congr 1; funext i
    have := poincare_reflect (m := D.m i) (κ := D.G * D.m0) (hb i)
    simp only [Pi.neg_apply]
    refine this.trans (Prod.ext rfl ?_)
    ext j; fin_cases j <;> simp [sigmaRefl]

theorem pairPotential_map (G : ℝ) (m : Fin n → ℝ) (A : (Fin 2 → ℝ) →+ (Fin 2 → ℝ))
    (hA : ∀ v, planeLength (A v) = planeLength v) (q : Fin (n * 2) → ℝ) :
    pairPotential G m (ofBodies fun i => A (bodyVector q i)) = pairPotential G m q := by
  unfold pairPotential
  simp only [bodyVector_ofBodies, ← map_sub, hA]

/-- The two Kepler perturbation functions are invariant under the isometries induced by the
chart symmetries: the position block is moved by `A`, the momentum block by `B`. -/
theorem perturbation_map (D : Data n) (b : Bool) {w w' : Phase (n + n)}
    (A B : (Fin 2 → ℝ) →+ (Fin 2 → ℝ)) (hA : ∀ v, planeLength (A v) = planeLength v)
    (hB : ∀ v, planeSq (B v) = planeSq v)
    (h : poincareProd D.m (D.G * D.m0) w' =
      (ofBodies fun i => A (bodyVector (poincareProd D.m (D.G * D.m0) w).1 i),
        ofBodies fun i => B (bodyVector (poincareProd D.m (D.G * D.m0) w).2 i))) :
    perturbation D b w' = perturbation D b w := by
  have hs : planeSq (∑ i, bodyVector (poincareProd D.m (D.G * D.m0) w').2 i) =
      planeSq (∑ i, bodyVector (poincareProd D.m (D.G * D.m0) w).2 i) := by
    rw [h]
    simp only [bodyVector_ofBodies, ← map_sum, hB]
  have hp : pairPotential D.G D.m (poincareProd D.m (D.G * D.m0) w').1 =
      pairPotential D.G D.m (poincareProd D.m (D.G * D.m0) w).1 := by
    rw [h]
    exact pairPotential_map D.G D.m A hA _
  cases b <;> simp [perturbation, fMov, fFix, hs, hp]

private def rotHom (θ : ℝ) : (Fin 2 → ℝ) →+ (Fin 2 → ℝ) :=
  AddMonoidHom.mk' (rot θ) fun u v => by ext i; fin_cases i <;> simp [rot] <;> ring

private def sigHom : (Fin 2 → ℝ) →+ (Fin 2 → ℝ) :=
  AddMonoidHom.mk' sigmaRefl fun u v => by ext i; fin_cases i <;> simp [sigmaRefl]; ring

private def sigHom' : (Fin 2 → ℝ) →+ (Fin 2 → ℝ) :=
  AddMonoidHom.mk' (fun v => ![-v 0, v 1]) fun u v => by ext i; fin_cases i <;> simp; ring

theorem perturbation_antipode (D : Data n) (b : Bool) {x : Slow n} (hx : x ∈ slowDom D)
    (t : Vec n) :
    perturbation D b (assemble x.2.1 (t + fun _ => π) (-x.2.2) (-x.1)) =
      perturbation D b (assemble x.2.1 t x.2.2 x.1) := by
  refine perturbation_map D b (-AddMonoidHom.id _) (-AddMonoidHom.id _)
    (fun v => by simp [planeLength_neg]) (fun v => ?_) ?_
  · simp [planeSq, Fin.sum_univ_two]
  · rw [(symmetries D hx t 0).1]
    exact Prod.ext (ofBodies_bodyVector (-(poincareProd D.m (D.G * D.m0)
      (assemble x.2.1 t x.2.2 x.1)).1)).symm
      (ofBodies_bodyVector (-(poincareProd D.m (D.G * D.m0)
      (assemble x.2.1 t x.2.2 x.1)).2)).symm

theorem perturbation_rotate (D : Data n) (b : Bool) {x : Slow n} (hx : x ∈ slowDom D)
    (t : Vec n) (θ : ℝ) :
    perturbation D b (assemble x.2.1 (t + fun _ => θ) (rotateSlow θ x).2.2 (rotateSlow θ x).1) =
      perturbation D b (assemble x.2.1 t x.2.2 x.1) := by
  refine perturbation_map D b (rotHom θ) (rotHom θ) (fun v => planeLength_rot θ v)
    (fun v => ?_) ?_
  · exact planeSq_rot' θ v
  · exact (symmetries D hx t θ).2.1

theorem perturbation_reflect (D : Data n) (b : Bool) {x : Slow n} (hx : x ∈ slowDom D)
    (t : Vec n) :
    perturbation D b (assemble x.2.1 (-t) (-x.2.2) x.1) =
      perturbation D b (assemble x.2.1 t x.2.2 x.1) := by
  refine perturbation_map D b sigHom sigHom' (fun v => ?_) (fun v => ?_) ?_
  · unfold planeLength; congr 1
    simp [sigHom, sigmaRefl, planeSq, Fin.sum_univ_two]
  · simp [sigHom', planeSq, Fin.sum_univ_two]
  · exact (symmetries D hx t 0).2.2

theorem assemble_add_fastShift (I t p q : Vec n) (k : Fin n → ℤ) :
    assemble I t p q + fastShift (a := n) (b := n) k =
      assemble I (t + fun i => 2 * π * k i) p q := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [assemble, fastShift, Fin.append_left]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [assemble, fastShift, Fin.append_left]

theorem perturbation_periodic (D : Data n) (b : Bool) {x : Slow n} (hx : x ∈ slowDom D)
    (k : Fin n → ℤ) (t : Vec n) :
    perturbation D b (assemble x.2.1 (t + fun i => 2 * π * k i) x.2.2 x.1) =
      perturbation D b (assemble x.2.1 t x.2.2 x.1) := by
  rw [← assemble_add_fastShift]
  have := (poincareProd_lattice (m := D.m) (κ := D.G * D.m0) D.hm (mul_pos D.hG D.hm0)
    (assemble_mem_slowDom D hx t) k).2
  simp only [perturbation, this]

theorem secular_eq_of_shift (D : Data n) (b : Bool) {x y : Slow n} (hx : x ∈ slowDom D)
    (c : Vec n)
    (h : ∀ φ, perturbation D b (assemble y.2.1 φ y.2.2 y.1) =
      perturbation D b (assemble x.2.1 (φ + c) x.2.2 x.1)) :
    secular D b y = secular D b x := by
  unfold secular secularAverage
  congr 1
  simp only [h]
  exact cell_integral_add (g := fun φ => perturbation D b (assemble x.2.1 φ x.2.2 x.1))
    (fun k t => perturbation_periodic D b hx k t) c

theorem secular_eq_of_neg (D : Data n) (b : Bool) {x y : Slow n} (hx : x ∈ slowDom D)
    (h : ∀ φ, perturbation D b (assemble y.2.1 φ y.2.2 y.1) =
      perturbation D b (assemble x.2.1 (-φ) x.2.2 x.1)) :
    secular D b y = secular D b x := by
  unfold secular secularAverage
  congr 1
  simp only [h]
  exact cell_integral_neg (g := fun φ => perturbation D b (assemble x.2.1 φ x.2.2 x.1))
    (fun k t => perturbation_periodic D b hx k t)

theorem evenness (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) (b : Bool) (θ : ℝ) :
    secular D b (-x.1,x.2.1,-x.2.2) = secular D b x ∧
    secular D b (x.1,x.2.1,-x.2.2) = secular D b x ∧
    secular D b (-x.1,x.2.1,x.2.2) = secular D b x ∧
    secular D b (rotateSlow θ x) = secular D b x := by
  have h1 : secular D b (-x.1,x.2.1,-x.2.2) = secular D b x := by
    refine secular_eq_of_shift D b hx (fun _ => -π) fun φ => ?_
    have := perturbation_antipode D b hx (φ + fun _ => -π)
    have e : ((φ + fun _ => -π) + fun _ => π) = φ := by ext i; simp
    rw [e] at this
    exact this
  have h3 : ∀ z : Slow n, z ∈ slowDom D → secular D b (z.1,z.2.1,-z.2.2) = secular D b z := by
    intro z hz
    refine secular_eq_of_neg D b hz fun φ => ?_
    have := perturbation_reflect D b hz (-φ)
    rw [neg_neg] at this
    exact this
  refine ⟨h1, h3 x hx, ?_, ?_⟩
  · have hx' : (-x.1, x.2.1, -x.2.2) ∈ slowDom D := by
      rw [mem_slowDom_iff] at hx ⊢; intro i; simpa using hx i
    have := h3 _ hx'
    simp only [neg_neg] at this
    rw [← h1]; exact this
  · refine secular_eq_of_shift D b hx (fun _ => -θ) fun φ => ?_
    have := perturbation_rotate D b hx (φ + fun _ => -θ) θ
    have e : ((φ + fun _ => -θ) + fun _ => θ) = φ := by ext i; simp
    rw [e] at this
    exact this

theorem evenness_taylor (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D) (b : Bool) (k : ℕ) :
    iteratedFDeriv ℝ (2*k+1) (slowSecular D b I) 0 = 0 := by
  obtain ⟨a, ha, rfl⟩ := hI
  have hpos : ∀ i, 0 < action D a i := fun i => by
    have := ha.1 i
    have := D.hm i; have := D.hG; have := D.hm0
    unfold action; positivity
  refine iteratedFDeriv_odd_eq_zero ?_ ⟨k, rfl⟩
  have hev : ∀ᶠ u : Vec n × Vec n in 𝓝 0,
      ∀ i, 0 < action D a i ∧ (u.1 i ^ 2 + u.2 i ^ 2) / 2 < action D a i := by
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous fun u : Vec n × Vec n => (u.1 i ^ 2 + u.2 i ^ 2) / 2 := by fun_prop
    have h0 : (fun u : Vec n × Vec n => (u.1 i ^ 2 + u.2 i ^ 2) / 2) 0 < action D a i := by
      simpa using hpos i
    filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h0] with u hu
    exact ⟨hpos i, hu⟩
  filter_upwards [hev] with u hu
  have hx : ((u.1, action D a, u.2) : Slow n) ∈ slowDom D := (mem_slowDom_iff D _).2 hu
  have := (evenness D hx b 0).1
  simpa [slowSecular] using this.symm

end SecularForm

end KAM.Planetary

end
