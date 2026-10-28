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
    {v : SecularForm.Vec n} (hv : v ∈ Submodule.span ℤ (range (twoPiBasis n))) (x : SecularForm.Vec n) :
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
    ∫ t in SecularForm.cell n, h t = ∫ t in Set.pi univ (fun _ : Fin n => Ico (0 : ℝ) (2 * π)), h t :=
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
      · have := hx i; simp only [Pi.add_apply, Pi.neg_apply]; constructor <;> linarith [this.1, this.2]
      · ext i; simp
    · rintro ⟨x, hx, rfl⟩
      refine ⟨-x + fun _ => 2 * π, fun i => ?_, ?_⟩
      · have := hx i; simp only [Pi.add_apply, Pi.neg_apply]; constructor <;> linarith [this.1, this.2]
      · ext i; simp; ring
  have h1 := (Measure.measurePreserving_neg (volume : Measure (SecularForm.Vec n))).setIntegral_image_emb
    measurableEmbedding_neg g (SecularForm.cell n)
  have h2 := (measurePreserving_add_right (volume : Measure (SecularForm.Vec n))
    (fun _ : Fin n => -(2 * π))).setIntegral_image_emb (measurableEmbedding_addRight _) g
    (SecularForm.cell n)
  have h3 : (fun t : SecularForm.Vec n => -t) '' SecularForm.cell n =
      (fun t => t + fun _ : Fin n => -(2 * π)) '' SecularForm.cell n := hset
  rw [← h1, h3, h2]
  exact cell_integral_add hg _

end TorusAverage

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

end SecularForm

end KAM.Planetary

end
