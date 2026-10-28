/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Basic
public import KAM.Planetary.Poincare.Lattice
public import KAM.Planetary.Hamiltonian.Algebra
public import KAM.Planetary.Newtonian.Models

/-!
# Secular form: the product chart interface

Blueprint P, Part 7 (`bpP:p7:product-chart`, `stepP:p7:pc-prod`, `stepP:p7:pc-dec`,
`stepP:p7:pc-share`, `bpP:p7:lattice`): the consumed declarations in the form used by Parts 8-10.
`product_chart`: the analytic action Hamiltonian `keplerActionHam`, its first derivative `nu`, the
nonzero second derivative and the decoupled field of `hProd`. `pc_prod`: the joint chart
(analytic, symplectic, image, injectivity modulo the fast lattice, analytic local inverse).
`pc_share`/`pc_dec`: field transport through `poincareProd`, derived from the symplectic
identity (`fderiv` of the chart is a symplectic bijection), with no pair-collision guard for
`pc_dec`. `SecularSpectrum.lattice`: the radian quotient facts for the polar chart.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

/-! ### Linear field transport through a symplectic surjection -/

/-- `A X_{ℓ∘A} = X_ℓ` for a symplectic surjection `A` between phase spaces of possibly different
(syntactic) dimensions. -/
theorem field_transport {d e : ℕ} (A : Phase d →L[ℝ] Phase e)
    (hA : ∀ u v, symplecticForm (A u) (A v) = symplecticForm u v)
    (hs : Function.Surjective A) (ℓ : Phase e →L[ℝ] ℝ) :
    A (linearField (ℓ.comp A)) = linearField ℓ := by
  rw [← eq_linearField_iff]
  intro w
  obtain ⟨u, rfl⟩ := hs w
  rw [hA, symplecticForm_linearField]
  rfl

/-- Field transport through the product chart at a point of its domain. -/
theorem poincareProd_field {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) {H : Phase (n * 2) → ℝ}
    (hH : DifferentiableAt ℝ H (poincareProd m κ w)) :
    fderiv ℝ (poincareProd m κ) w (hamiltonianVectorField (H ∘ poincareProd m κ) w) =
      hamiltonianVectorField H (poincareProd m κ w) := by
  obtain ⟨A, hA⟩ := poincareProd_fderiv_equiv hm hκ hw
  have hΨ : DifferentiableAt ℝ (poincareProd m κ) w :=
    (analyticOnNhd_poincareProd hm hκ w hw).differentiableAt
  have hd : fderiv ℝ (H ∘ poincareProd m κ) w =
      (fderiv ℝ H (poincareProd m κ w)).comp (fderiv ℝ (poincareProd m κ) w) :=
    fderiv_comp w hH hΨ
  rw [hamiltonianVectorField_eq_linearField, hamiltonianVectorField_eq_linearField, hd]
  refine field_transport _ (fun u v => ?_) ?_ _
  · have := poincareProd_symplectic hm hκ w hw u v
    rwa [one_mul] at this
  · rw [← hA]
    exact A.surjective

/-! ### Differentiability of the Kepler part off the origin -/

private def posL (i : Fin n) : Phase (n * 2) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n * 2) => ℝ)
      (finProdFinEquiv (i, k))).comp
      (ContinuousLinearMap.fst ℝ (Fin (n * 2) → ℝ) (Fin (n * 2) → ℝ))

private def momL (i : Fin n) : Phase (n * 2) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n * 2) => ℝ)
      (finProdFinEquiv (i, k))).comp
      (ContinuousLinearMap.snd ℝ (Fin (n * 2) → ℝ) (Fin (n * 2) → ℝ))

private theorem analyticAt_planeSq' (v : Fin 2 → ℝ) : AnalyticAt ℝ planeSq v := by
  have h : planeSq = fun w : Fin 2 → ℝ => w 0 ^ 2 + w 1 ^ 2 :=
    funext fun w => by simp [planeSq, Fin.sum_univ_two]
  rw [h]
  have h0 : AnalyticAt ℝ (fun w : Fin 2 → ℝ => w 0) v :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).analyticAt v
  have h1 : AnalyticAt ℝ (fun w : Fin 2 → ℝ => w 1) v :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).analyticAt v
  exact (h0.pow 2).add (h1.pow 2)

/-- The Kepler part is analytic where every body is off the origin (no pair condition). -/
theorem analyticAt_keplerPart' (κ : ℝ) (m : Fin n → ℝ) {z : Phase (n * 2)}
    (hz : ∀ i, 0 < planeLength (bodyVector z.1 i)) : AnalyticAt ℝ (keplerPart κ m) z := by
  show AnalyticAt ℝ (fun z : Phase (n * 2) =>
    ∑ i, (planeSq (bodyVector z.2 i) / (2 * m i) - κ * m i / planeLength (bodyVector z.1 i))) z
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  have hs : AnalyticAt ℝ (fun x : Phase (n * 2) => planeSq (momL i x)) z :=
    (analyticAt_planeSq' (momL i z)).comp ((momL i).analyticAt z)
  have hv : posL i z ≠ 0 := planeLength_pos_iff.mp (hz i)
  have hi : AnalyticAt ℝ (fun x : Phase (n * 2) => (planeLength (posL i x))⁻¹) z :=
    (analyticAt_inv_planeLength hv).comp ((posL i).analyticAt z)
  simp only [div_eq_mul_inv]
  exact (hs.mul analyticAt_const).sub (analyticAt_const.mul hi)

/-! ### The action Hamiltonian -/

def keplerActionHam (D : Data n) (I : Vec n) : ℝ := hProd (D.G*D.m0) D.m (assemble I 0 0 0)

/-- The Kepler energy as a function of the actions. -/
private def kepEnergy (κ : ℝ) (m : Vec n) (I : Vec n) : ℝ :=
  -∑ i, κ ^ 2 * m i ^ 3 / (2 * I i ^ 2)

private theorem hProd_eq (κ : ℝ) (m : Vec n) (w : Phase (n + n)) :
    hProd κ m w = kepEnergy κ m (fast w.2) := rfl

private theorem fast_assemble (I phi : Vec n) (p q : Vec n) :
    fast (assemble I phi p q).2 = I := by
  funext i
  simp [fast, assemble]

private theorem keplerActionHam_eq (D : Data n) (I : Vec n) :
    keplerActionHam D I = kepEnergy (D.G*D.m0) D.m I := by
  rw [keplerActionHam, hProd_eq, fast_assemble]

private def fastL : Phase (n + n) →L[ℝ] Vec n :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + n) => ℝ) (Fin.castAdd n i)).comp
      (ContinuousLinearMap.snd ℝ (Fin (n + n) → ℝ) (Fin (n + n) → ℝ))

private theorem fastL_apply (w : Phase (n + n)) : fastL w = fast w.2 := rfl

private theorem analyticAt_kepEnergy (κ : ℝ) (m : Vec n) {I : Vec n} (hI : ∀ i, I i ≠ 0) :
    AnalyticAt ℝ (kepEnergy κ m) I := by
  unfold kepEnergy
  have h : AnalyticAt ℝ (fun I : Vec n => ∑ i, κ ^ 2 * m i ^ 3 / (2 * I i ^ 2)) I := by
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    have hp : AnalyticAt ℝ (fun I : Vec n => I i) I :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).analyticAt I
    exact analyticAt_const.div (analyticAt_const.mul (hp.pow 2))
      (mul_ne_zero two_ne_zero (pow_ne_zero 2 (hI i)))
  exact h.neg

private theorem hasDerivAt_kepEnergy_line (κ : ℝ) (m : Vec n) {I : Vec n} (hI : ∀ i, I i ≠ 0)
    (u : Vec n) :
    HasDerivAt (fun t : ℝ => kepEnergy κ m (I + t • u))
      (∑ i, κ ^ 2 * m i ^ 3 / I i ^ 3 * u i) 0 := by
  unfold kepEnergy
  have h : ∀ i ∈ Finset.univ, HasDerivAt (fun t : ℝ => κ ^ 2 * m i ^ 3 / (2 * (I + t • u) i ^ 2))
      (-(κ ^ 2 * m i ^ 3 / I i ^ 3 * u i)) 0 := by
    intro i _
    have hg : HasDerivAt (fun t : ℝ => (I + t • u) i) (u i) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).mul_const (u i)).const_add (I i)
      simpa using this
    have hg0 : (I + (0 : ℝ) • u) i ≠ 0 := by simpa using hI i
    have h2 : HasDerivAt (fun t : ℝ => 2 * (I + t • u) i ^ 2)
        (2 * (↑2 * (I + (0 : ℝ) • u) i ^ (2 - 1) * u i)) 0 := (hg.pow 2).const_mul 2
    have h3 := (h2.inv (mul_ne_zero two_ne_zero (pow_ne_zero 2 hg0))).const_mul (κ ^ 2 * m i ^ 3)
    simp only [div_eq_mul_inv]
    refine h3.congr_deriv ?_
    have := hI i
    simp
    field_simp
  have := (HasDerivAt.fun_sum h).neg
  refine this.congr_deriv ?_
  simp [Finset.sum_neg_distrib]

private theorem fderiv_apply_eq_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ f x v = deriv (fun t : ℝ => f (x + t • v)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f (x + (0 : ℝ) • v)) (x + (0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  have h2 : deriv (fun t : ℝ => f (x + t • v)) 0 = fderiv ℝ f (x + (0 : ℝ) • v) v :=
    (hf'.comp_hasDerivAt (0 : ℝ) hl).deriv
  rw [zero_smul, add_zero] at h2
  exact h2.symm

private theorem fderiv_kepEnergy (κ : ℝ) (m : Vec n) {I : Vec n} (hI : ∀ i, I i ≠ 0) (u : Vec n) :
    fderiv ℝ (kepEnergy κ m) I u = ∑ i, κ ^ 2 * m i ^ 3 / I i ^ 3 * u i := by
  rw [fderiv_apply_eq_deriv (analyticAt_kepEnergy κ m hI).differentiableAt]
  exact (hasDerivAt_kepEnergy_line κ m hI u).deriv

private theorem fderiv_hProd (κ : ℝ) (m : Vec n) {w : Phase (n + n)}
    (hw : ∀ i, fast w.2 i ≠ 0) (u : Phase (n + n)) :
    fderiv ℝ (hProd κ m) w u = ∑ i, κ ^ 2 * m i ^ 3 / fast w.2 i ^ 3 * fast u.2 i := by
  have hd : HasFDerivAt (kepEnergy κ m ∘ fastL)
      ((fderiv ℝ (kepEnergy κ m) (fast w.2)).comp fastL) w :=
    ((analyticAt_kepEnergy κ m hw).differentiableAt.hasFDerivAt).comp w fastL.hasFDerivAt
  have hf : hProd κ m = kepEnergy κ m ∘ fastL := rfl
  rw [hf, hd.fderiv]
  simpa [fastL_apply] using fderiv_kepEnergy κ m hw (fast u.2)

theorem product_chart (D : Data n) :
    AnalyticOnNhd ℝ (keplerActionHam D) {I | ∀ i, 0 < I i} ∧
    (∀ I : Vec n, (∀ i, 0 < I i) → ∀ i,
      fderiv ℝ (keplerActionHam D) I (Pi.single i 1) = nu D I i ∧
      fderiv ℝ (fun J => nu D J i) I (Pi.single i 1) = -3*(D.G*D.m0)^2*D.m i^3/I i^4 ∧
      -3*(D.G*D.m0)^2*D.m i^3/I i^4 ≠ 0) ∧
    (∀ w ∈ poincareProdDom n,
      hamiltonianVectorField (hProd (D.G*D.m0) D.m) w = (Fin.append (nu D (fast w.2)) 0,0)) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  refine ⟨?_, ?_, ?_⟩
  · intro I hI
    have hI' : ∀ i, I i ≠ 0 := fun i => (hI i).ne'
    have : keplerActionHam D = kepEnergy (D.G*D.m0) D.m := funext (keplerActionHam_eq D)
    rw [this]
    exact analyticAt_kepEnergy _ _ hI'
  · intro I hI i
    have hI' : ∀ i, I i ≠ 0 := fun i => (hI i).ne'
    refine ⟨?_, ?_, ?_⟩
    · have : keplerActionHam D = kepEnergy (D.G*D.m0) D.m := funext (keplerActionHam_eq D)
      rw [this, fderiv_kepEnergy _ _ hI']
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      rfl
    · have hna : AnalyticAt ℝ (fun J : Vec n => nu D J i) I := by
        have hp : AnalyticAt ℝ (fun J : Vec n => J i) I :=
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).analyticAt I
        exact analyticAt_const.div (hp.pow 3) (pow_ne_zero 3 (hI' i))
      rw [fderiv_apply_eq_deriv hna.differentiableAt]
      have h1 : HasDerivAt (fun t : ℝ => nu D (I + t • Pi.single i 1) i)
          (-3 * (D.G * D.m0) ^ 2 * D.m i ^ 3 / I i ^ 4) 0 := by
        have hg : HasDerivAt (fun t : ℝ => I i + t) 1 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_add (I i)
        have hn : HasDerivAt (fun y : ℝ => (D.G * D.m0) ^ 2 * D.m i ^ 3 / y ^ 3)
            (-3 * (D.G * D.m0) ^ 2 * D.m i ^ 3 / (I i + 0) ^ 4) (I i + 0) :=
          hasDerivAt_nu (m := D.m i) (κ := D.G * D.m0) (x := I i + 0) (by simpa using (hI' i))
        have h := HasDerivAt.comp (0 : ℝ) hn hg
        simp only [add_zero, mul_one] at h
        refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
        simp [nu]
      exact h1.deriv
    · have := hI' i
      have := D.hm i
      have := hκ.ne'
      positivity
  · intro w hw
    have hw' : ∀ i, fast w.2 i ≠ 0 := fun i => (hw i).1.ne'
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show fderiv ℝ (hProd (D.G*D.m0) D.m) w (0, Pi.single i 1) = _
      rw [fderiv_hProd _ _ hw']
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · simp [fast, Pi.single_apply, nu, Fin.append_left]
      · simp only [fast, Pi.single_apply, Fin.append_right]
        refine (Finset.sum_eq_zero fun j _ => ?_).trans ?_
        · have hne : Fin.castAdd n j ≠ k.addNat n := fun h => by
            have := congrArg Fin.val h
            simp at this
            omega
          simp [hne]
        · rfl
    · show -fderiv ℝ (hProd (D.G*D.m0) D.m) w (Pi.single i 1, 0) = _
      rw [fderiv_hProd _ _ hw']
      simp [fast]

theorem pc_prod (D : Data n) :
    AnalyticOnNhd ℝ (poincareProd D.m (D.G*D.m0)) (poincareProdDom n) ∧
    IsSymplecticOn 1 (poincareProd D.m (D.G*D.m0)) (poincareProdDom n) ∧
    poincareProd D.m (D.G*D.m0) '' poincareProdDom n = regionProd D.m (D.G*D.m0) ∧
    (∀ w ∈ poincareProdDom n, ∀ w' ∈ poincareProdDom n,
      poincareProd D.m (D.G*D.m0) w = poincareProd D.m (D.G*D.m0) w' ↔
      ∃ k : Fin n → ℤ, w' = w + fastShift (a := n) (b := n) k) ∧
    (∀ w ∈ poincareProdDom n,
      ∃ φ : OpenPartialHomeomorph (Phase (n+n)) (Phase (n*2)), w ∈ φ.source ∧
        (φ : Phase (n+n) → Phase (n*2)) = poincareProd D.m (D.G*D.m0) ∧
        AnalyticOnNhd ℝ φ.symm φ.target) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  exact ⟨analyticOnNhd_poincareProd D.hm hκ, poincareProd_symplectic D.hm hκ,
    poincareProd_image D.hm hκ, fun _ hw _ hw' => poincareProd_eq_iff D.hm hκ hw hw',
    fun _ hw => poincareProd_localDiffeo D.hm hκ hw⟩

/-- Source field transport, obtained from the frozen form, not assumed in Lemma 64. -/
theorem pc_share (D : Data n) (b : Bool) (μ : ℝ) {w : Phase (n+n)}
    (hw : w ∈ poincareProdDom n) (hW : NoCollision (poincareProd D.m (D.G*D.m0) w).1) :
    let H := if b then movingHamiltonian D.G D.m0 D.m μ else fixedHamiltonian D.G D.m0 D.m μ
    H (poincareProd D.m (D.G*D.m0) w) = hProd (D.G*D.m0) D.m w + μ*perturbation D b w ∧
    fderiv ℝ (poincareProd D.m (D.G*D.m0)) w
      (hamiltonianVectorField (H ∘ poincareProd D.m (D.G*D.m0)) w) =
      hamiltonianVectorField H (poincareProd D.m (D.G*D.m0) w) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  intro H
  cases b
  · refine ⟨?_, poincareProd_field D.hm hκ hw
      (differentiableAt_fixedHamiltonian D.G D.m0 D.m μ hW)⟩
    simpa [H, perturbation] using fixedHamiltonian_poincareProd D.hm hκ hw
  · refine ⟨?_, poincareProd_field D.hm hκ hw
      (differentiableAt_movingHamiltonian D.G D.m0 D.m μ hW)⟩
    simpa [H, perturbation] using movingHamiltonian_poincareProd D.hm hκ hw

/-- Collision-free Kepler version needed by p8:l64-a; no pair guard. -/
theorem pc_dec (D : Data n) {w : Phase (n+n)} (hw : w ∈ poincareProdDom n) :
    fderiv ℝ (poincareProd D.m (D.G*D.m0)) w
      (hamiltonianVectorField (hProd (D.G*D.m0) D.m) w) =
      hamiltonianVectorField (keplerPart (D.G*D.m0) D.m) (poincareProd D.m (D.G*D.m0) w) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hreg := (poincareProd_mem_regionProd D.hm hκ hw)
  have hK : DifferentiableAt ℝ (keplerPart (D.G*D.m0) D.m) (poincareProd D.m (D.G*D.m0) w) :=
    (analyticAt_keplerPart' _ _ fun i => by
      have := (hreg i).1
      simpa [bodyVector, poincareProd] using this).differentiableAt
  have hev : hProd (D.G*D.m0) D.m =ᶠ[𝓝 w]
      keplerPart (D.G*D.m0) D.m ∘ poincareProd D.m (D.G*D.m0) := by
    filter_upwards [(isOpen_poincareProdDom n).mem_nhds hw] with v hv
    exact (keplerPart_poincareProd D.hm hκ hv).symm
  have h1 : hamiltonianVectorField (hProd (D.G*D.m0) D.m) w =
      hamiltonianVectorField (keplerPart (D.G*D.m0) D.m ∘ poincareProd D.m (D.G*D.m0)) w := by
    simp only [hamiltonianVectorField_eq_linearField, hev.fderiv_eq]
  rw [h1]
  exact poincareProd_field D.hm hκ hw hK
end SecularForm

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

/-- The missing radian/polar quotient statements, on the literal existing polar map. -/
theorem lattice (D : Data n) :
    AnalyticOnNhd ℝ (polarMap (n := n)) (polarDom n) ∧
    IsSymplecticOn 1 (polarMap (n := n)) (polarDom n) ∧
    MapsTo (polarMap (n := n)) (polarDom n) (poincareProdDom n) ∧
    (∀ z ∈ polarDom n, ∀ k : Fin (n+n) → ℤ,
      z + fullShift k ∈ polarDom n ∧
      poincareProd D.m (D.G*D.m0) (polarMap (z+fullShift k)) =
        poincareProd D.m (D.G*D.m0) (polarMap z)) ∧
    (∀ z ∈ polarDom n, ∀ z' ∈ polarDom n,
      poincareProd D.m (D.G*D.m0) (polarMap z') = poincareProd D.m (D.G*D.m0) (polarMap z) →
      ∃ k : Fin (n+n) → ℤ, z' = z+fullShift k) ∧
    IsSymplecticOn (2*π) (poincareProd D.m (D.G*D.m0) ∘ polarMap ∘ angleScale (2*π))
      (angleScale (2*π) ⁻¹' polarDom n) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  refine ⟨analyticOnNhd_polarMap n, polarMap_symplectic n, polarMap_mapsTo n,
    fun z hz k => ⟨polarDom_shift k hz, (poincareProd_polar_lattice D.hm hκ hz hz k).1⟩,
    fun z hz z' hz' h => (poincareProd_polar_lattice D.hm hκ hz hz' 0).2 h, ?_⟩
  exact poincareProd_polar_periodOne_symplectic D.hm hκ
end SecularSpectrum

end KAM.Planetary

end
