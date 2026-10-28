/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.FrequencyBounds

/-!
# P Part 5: the derivative of the complex frequency map (`stepP:p5:fi-inj`, `fi-blk`)

Block projections, the splitting `complexFrequency = (complexFast ∘ blockFast, 0) + mu ∇jetPolynomial`
and the formula for its derivative on the tube; the slow-slow block of the Hessian of
`jetPolynomial` is `jetBeta` (`jetBeta_isSymm`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FI.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

/-- The fast projection as a continuous linear map. -/
def bfCLM (a b : ℕ) : (Fin (a + b) → ℂ) →L[ℂ] (Fin a → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd b i)

/-- The slow projection as a continuous linear map. -/
def bsCLM (a b : ℕ) : (Fin (a + b) → ℂ) →L[ℂ] (Fin b → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.natAdd a i)

theorem bfCLM_apply (J : Fin (a + b) → ℂ) : bfCLM a b J = blockFast J := rfl

theorem bsCLM_apply (J : Fin (a + b) → ℂ) : bsCLM a b J = blockSlow J := rfl

theorem blockFast_embFast (x : Fin a → ℂ) : blockFast (embFast a b x) = x := by
  rw [embFast_apply, blockFast_append_complex]

theorem blockSlow_embFast (x : Fin a → ℂ) : blockSlow (embFast a b x) = 0 := by
  rw [embFast_apply, blockSlow_append_complex]

theorem blockFast_embSlow (y : Fin b → ℂ) : blockFast (embSlow a b y) = 0 := by
  rw [embSlow_apply, blockFast_append_complex]

theorem blockSlow_embSlow (y : Fin b → ℂ) : blockSlow (embSlow a b y) = y := by
  rw [embSlow_apply, blockSlow_append_complex]

theorem eq_embFast_add_embSlow (J : Fin (a + b) → ℂ) :
    J = embFast a b (blockFast J) + embSlow a b (blockSlow J) := by
  rw [← append_eq_add]
  exact (Fin.append_castAdd_natAdd (f := J)).symm

theorem single_castAdd (k : Fin a) :
    (Pi.single (Fin.castAdd b k) (1 : ℂ) : Fin (a + b) → ℂ) = embFast a b (Pi.single k 1) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [embFast_apply, Pi.single_apply]
  · have := k.isLt; have := j.isLt
    simp [embFast_apply, Pi.single_apply, Fin.ext_iff]; omega

theorem single_natAdd (k : Fin b) :
    (Pi.single (Fin.natAdd a k) (1 : ℂ) : Fin (a + b) → ℂ) = embSlow a b (Pi.single k 1) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have := k.isLt; have := j.isLt
    simp [embSlow_apply, Pi.single_apply, Fin.ext_iff]; omega
  · simp [embSlow_apply, Pi.single_apply, Fin.ext_iff]

theorem hasFDerivAt_complexIntegrable (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {J : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    HasFDerivAt (complexIntegrable d mu)
      ((fderiv ℂ (pgExtension d).H0 (blockFast J)).comp (bfCLM a b) +
        (mu : ℂ) • fderiv ℂ (jetPolynomial d mu) J) J := by
  have hδ := (pgExtension d).delta_pos
  have hH0 : DifferentiableAt ℂ (pgExtension d).H0 (blockFast J) :=
    (pgExtension d).h0holo.differentiableAt ((isOpen_actionNbhd _ _).mem_nhds
      (mem_actionNbhd_mono (by linarith) hJ))
  have hjp : DifferentiableAt ℂ (jetPolynomial d mu) J :=
    (jetPolynomial_differentiableOn d hmu).differentiableAt ((isOpen_jpDom d).mem_nhds hJ)
  exact (hH0.hasFDerivAt.comp J (bfCLM a b).hasFDerivAt).add (hjp.hasFDerivAt.const_mul (mu : ℂ))

theorem complexFrequency_eq (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {J : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    complexFrequency d mu J = embFast a b (complexFast d (blockFast J)) +
      (mu : ℂ) • partialsCLM (a + b) (fderiv ℂ (jetPolynomial d mu) J) := by
  funext i
  rw [complexFrequency, (hasFDerivAt_complexIntegrable d hmu hJ).fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, Pi.add_apply, Pi.smul_apply, partialsCLM,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.apply_apply, smul_eq_mul, bfCLM_apply]
  congr 1
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · rw [single_castAdd, blockFast_embFast]
    simp [embFast_apply, complexFast]
  · rw [single_natAdd, blockFast_embSlow]
    simp [embFast_apply]

theorem hasFDerivAt_complexFrequency (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {J : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    HasFDerivAt (complexFrequency d mu)
      ((embFast a b).comp ((fderiv ℂ (complexFast d) (blockFast J)).comp (bfCLM a b)) +
        (mu : ℂ) • (partialsCLM (a + b)).comp
          (fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J)) J := by
  have hδ := (pgExtension d).delta_pos
  have hcF : DifferentiableAt ℂ (complexFast d) (blockFast J) :=
    (differentiableOn_complexFast d).differentiableAt ((isOpen_actionNbhd _ _).mem_nhds
      (mem_actionNbhd_mono (by linarith) hJ))
  have hD : DifferentiableAt ℂ (fderiv ℂ (jetPolynomial d mu)) J :=
    (differentiableOn_fderiv_jp d hmu).differentiableAt ((isOpen_jpDom d).mem_nhds hJ)
  have heq : complexFrequency d mu =ᶠ[𝓝 J] fun J' =>
      embFast a b (complexFast d (blockFast J')) +
        (mu : ℂ) • partialsCLM (a + b) (fderiv ℂ (jetPolynomial d mu) J') := by
    filter_upwards [(isOpen_jpDom d).mem_nhds hJ] with J' hJ' using
      complexFrequency_eq d hmu hJ'
  have h1 := (embFast a b).hasFDerivAt.comp J (hcF.hasFDerivAt.comp J (bfCLM a b).hasFDerivAt)
  have h2 := ((partialsCLM (a + b)).hasFDerivAt.comp J hD.hasFDerivAt).const_smul (mu : ℂ)
  exact (h1.add h2).congr_of_eventuallyEq heq

/-- The affine-in-`ξ` map `ξ ↦ (I, ξ)` has derivative `embSlow`. -/
theorem hasFDerivAt_append_slow (I : Fin a → ℂ) (ξ : Fin b → ℂ) :
    HasFDerivAt (fun ξ : Fin b → ℂ => (Fin.append I ξ : Fin (a + b) → ℂ)) (embSlow a b) ξ := by
  have : (fun ξ : Fin b → ℂ => (Fin.append I ξ : Fin (a + b) → ℂ)) =
      fun ξ => embSlow a b ξ + embFast a b I := by
    funext ξ; exact (append_eq_add I ξ).trans (add_comm _ _)
  rw [this]; exact (embSlow a b).hasFDerivAt.add_const _

/-- The slow gradient of the jet polynomial is `Θ = Ω + β ξ` (`β` is symmetric). -/
theorem fderiv_jp_embSlow (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) (ξ w : Fin b → ℂ) :
    fderiv ℂ (jetPolynomial d mu) (Fin.append I ξ) (embSlow a b w) =
      jpTheta d mu ξ I ⬝ᵥ w := by
  have hd : DifferentiableAt ℂ (jetPolynomial d mu) (Fin.append I ξ) :=
    (jetPolynomial_differentiableOn d hmu).differentiableAt
      ((isOpen_jpDom d).mem_nhds (append_mem_jpDom d hI ξ))
  have h1 := hd.hasFDerivAt.comp ξ (hasFDerivAt_append_slow I ξ)
  have hQ : (fun ξ' : Fin b → ℂ => jetPolynomial d mu (Fin.append I ξ')) =
      fun ξ' => jetP0 d mu I + ∑ j, jetOmega d mu I j * ξ' j +
        (1 / 2 : ℂ) * ∑ i, ∑ j, jetBeta d mu I i j * ξ' i * ξ' j := by
    funext ξ'
    simp [jetPolynomial, blockFast_append_complex, blockSlow_append_complex]
  have hc : ∀ i : Fin b, HasFDerivAt (fun f : Fin b → ℂ => f i) (ContinuousLinearMap.proj i) ξ :=
    fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin b => ℂ) i).hasFDerivAt
  have hB : HasFDerivAt (fun ξ' : Fin b → ℂ => ∑ i, ∑ j, jetBeta d mu I i j * ξ' i * ξ' j) _ ξ :=
    HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ =>
      ((hc i).const_mul (jetBeta d mu I i j)).mul (hc j)
  have hO : HasFDerivAt (fun ξ' : Fin b → ℂ => ∑ j, jetOmega d mu I j * ξ' j) _ ξ :=
    HasFDerivAt.fun_sum fun j _ => (hc j).const_mul (jetOmega d mu I j)
  have h2 := ((hasFDerivAt_const (jetP0 d mu I) ξ).add hO).add (hB.const_mul (1 / 2 : ℂ))
  have h2' : HasFDerivAt (fun ξ' : Fin b → ℂ => jetPolynomial d mu (Fin.append I ξ'))
    (0 + ∑ i, jetOmega d mu I i • (ContinuousLinearMap.proj i : (Fin b → ℂ) →L[ℂ] ℂ) +
      (1 / 2 : ℂ) • ∑ i, ∑ k, ((jetBeta d mu I i k * ξ i) • (ContinuousLinearMap.proj k : (Fin b → ℂ) →L[ℂ] ℂ) +
        ξ k • jetBeta d mu I i k • (ContinuousLinearMap.proj i : (Fin b → ℂ) →L[ℂ] ℂ))) ξ := by
    rw [hQ]; exact h2
  have h3 := congrArg (fun L => L w) (h1.unique h2')
  simp only [ContinuousLinearMap.comp_apply] at h3
  rw [h3]
  have hsym := jetBeta_isSymm d hmu hI
  simp only [add_apply, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    zero_add]
  have hsw : ∑ x, ∑ y, jetBeta d mu I x y * ξ x * w y =
      ∑ x, ∑ y, ξ y * (jetBeta d mu I x y * w x) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    rw [← hsym.apply x y]; ring
  have hrhs : jpTheta d mu ξ I ⬝ᵥ w = ∑ i, jetOmega d mu I i * w i +
      ∑ x, ∑ y, ξ y * (jetBeta d mu I x y * w x) := by
    simp only [jpTheta, dotProduct, Pi.add_apply, Matrix.mulVec, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [hrhs]
  simp only [Finset.sum_add_distrib]
  rw [hsw]
  ring

/-- The slow-slow block of the Hessian of the jet polynomial is `jetBeta`. -/
theorem hessian_embSlow (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) (ξ y w : Fin b → ℂ) :
    fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) (Fin.append I ξ) (embSlow a b y)
      (embSlow a b w) = (jetBeta d mu I).mulVec y ⬝ᵥ w := by
  have hD : DifferentiableAt ℂ (fderiv ℂ (jetPolynomial d mu)) (Fin.append I ξ) :=
    (differentiableOn_fderiv_jp d hmu).differentiableAt
      ((isOpen_jpDom d).mem_nhds (append_mem_jpDom d hI ξ))
  have h1 := (ContinuousLinearMap.apply ℂ ℂ (embSlow a b w)).hasFDerivAt.comp ξ
    (hD.hasFDerivAt.comp ξ (hasFDerivAt_append_slow I ξ))
  have hc : ∀ i : Fin b, HasFDerivAt (fun f : Fin b → ℂ => f i) (ContinuousLinearMap.proj i) ξ :=
    fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin b => ℂ) i).hasFDerivAt
  have hE := HasFDerivAt.fun_sum (u := Finset.univ)
    (A := fun (k : Fin b) (ξ' : Fin b → ℂ) =>
      (jetOmega d mu I k + ∑ m, jetBeta d mu I k m * ξ' m) * w k) fun k _ =>
    ((hasFDerivAt_const (jetOmega d mu I k) ξ).add (HasFDerivAt.fun_sum fun m _ =>
      (hc m).const_mul (jetBeta d mu I k m))).mul_const (w k)
  have hfun : ∀ ξ' : Fin b → ℂ, fderiv ℂ (jetPolynomial d mu) (Fin.append I ξ')
      (embSlow a b w) = ∑ k, (jetOmega d mu I k + ∑ m, jetBeta d mu I k m * ξ' m) * w k := by
    intro ξ'
    rw [fderiv_jp_embSlow d hmu hI]
    simp [jpTheta, dotProduct, Matrix.mulVec]
  have h2 := hE.congr_of_eventuallyEq (f₁ := fun ξ' : Fin b → ℂ =>
    fderiv ℂ (jetPolynomial d mu) (Fin.append I ξ') (embSlow a b w))
    (Filter.Eventually.of_forall hfun)
  have h3 := congrArg (fun L => L y) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at h3
  rw [h3]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    zero_add, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_comm, Finset.sum_mul]

end KAM.Planetary

end
