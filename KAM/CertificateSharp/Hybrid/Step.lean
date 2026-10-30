/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.ModelMul
public import KAM.CertificateSharp.V2.RouteAL1Facts
public import KAM.Sharp2.Hybrid.Step

/-!
# The step `ΔK` of the certified first step, and the model of `Ẽ` (package C8c)

The producer's step is an embedding increment `dK` (the format of `docs/campaign/design/hybrid/
format.md`, §3): real polynomials with the angle and action degrees of the base embedding, and
**no** identity in the angles. It denotes `ΔK = stepFun n dK`.

* `stepFun`, `isStep_stepFun`: the step is a `KAM.Sharp2.Hybrid.IsStep` on every strip (a real
  trigonometric polynomial);
* `stepModel`, `dstepModel`: exact models of the components of `ΔK` and of `∂_j ΔK`;
* `stepSupOk`, `stepRealOk`, `dstepOk`: the step norms `(S1)–(S4)` on a strip (any checked weight)
  and on the real torus (`realWeight`), with soundness `stepSup_le`, `stepReal_le`,
  `tangentMat_step_le`, `tangentMat_step_real_le`;
* `linModel`, `linModel_encloses`, `linOk`, `linNewError_le`: the model of
  `Ẽ = E + DX_H(K) ΔK - DΔK · s₁ω*` coordinatewise. The three parts are combined into one model by
  merged sums **before** the norm is taken (the Newton cancellation is kept), then bounded on
  `T_{ρ₁}` (`(S5)`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.CertificateSharp.Hybrid

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp CertArith Matrix
open KAM.CertificateSharp.V2.L1 (sumsOk sumsOk_col sumsOk_row ble_le)

variable {α : Type} [CertArith α] {n : ℕ}

/-! ### The step -/

/-- The step denoted by an embedding increment: `(2π)^{dU_i} U_i`, `(2π)^{dA_i} A_i`. -/
def stepFun (n : ℕ) (dK : CertEmbedding α) (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  (fun i => dK.angleAt n i.val θ, fun i => dK.actionAt n i.val θ)

theorem differentiable_stepFun (dK : CertEmbedding α) : Differentiable ℂ (stepFun n dK) :=
  Differentiable.prodMk (differentiable_pi.mpr fun _ => differentiable_realComp n _ _)
    (differentiable_pi.mpr fun _ => differentiable_realComp n _ _)

/-- The step is a real trigonometric polynomial: a step on every strip. -/
theorem isStep_stepFun (dK : CertEmbedding α) (ρ : ℝ) :
    KAM.Sharp2.Hybrid.IsStep (stepFun n dK) ρ where
  holo := (differentiable_stepFun dK).differentiableOn
  periodic := fun θ _ k => Prod.ext (funext fun i => realComp_add_int n _ _ θ k)
    (funext fun i => realComp_add_int n _ _ θ k)
  real := by
    intro x
    refine ⟨(fun i => (dK.angleAt n i.val fun i => (x i : ℂ)).re,
      fun i => (dK.actionAt n i.val fun i => (x i : ℂ)).re), Prod.ext (funext fun i => ?_)
      (funext fun i => ?_)⟩
    · have h := realComp_real n (dK.angleDeg.getD i.val 0) dK.angle[i.val]? x
      exact Complex.ext (by simp [stepFun]) (by simpa [stepFun, CertEmbedding.angleAt] using h)
    · have h := realComp_real n (dK.actionDeg.getD i.val 0) dK.action[i.val]? x
      exact Complex.ext (by simp [stepFun]) (by simpa [stepFun, CertEmbedding.actionAt] using h)

/-- Component `a` (phase numbering) of the step as an exact model. -/
def stepModel (n : ℕ) (dK : CertEmbedding α) (a : ℕ) : CertModel α :=
  if a < n then realCompModel n (dK.angleDeg.getD a 0) dK.angle[a]?
  else realCompModel n (dK.actionDeg.getD (a - n) 0) dK.action[a - n]?

/-- `∂_j` of component `a` of the step, at degree `0`. -/
def dstepModel (n : ℕ) (W : CertWeight) (pe : PiEnclosure α) (dK : CertEmbedding α)
    (a j : ℕ) : CertModel α :=
  if a < n then compDerivModel n W pe (dK.angleDeg.getD a 0) dK.angle[a]? j
  else compDerivModel n W pe (dK.actionDeg.getD (a - n) 0) dK.action[a - n]? j

section Lawful

variable [LawfulCertArith α]

theorem stepModel_encloses (dK : CertEmbedding α) (ρ : ℝ) (x : Fin n ⊕ Fin n) :
    (stepModel n dK (phaseNat x)).Encloses n ρ (fun θ => sumVec n (stepFun n dK θ) x) := by
  rcases x with i | i
  · have hlt : phaseNat (Sum.inl i : Fin n ⊕ Fin n) < n := i.isLt
    simp only [stepModel, hlt, ↓reduceIte]
    exact (realCompModel_encloses n ρ _ _).of_eq_fun fun θ => by
      simp [sumVec_apply, stepFun, CertEmbedding.angleAt, phaseNat]
  · have hlt : ¬(phaseNat (Sum.inr i : Fin n ⊕ Fin n) < n) := by simp [phaseNat]
    have e : phaseNat (Sum.inr i : Fin n ⊕ Fin n) - n = i.val := by simp [phaseNat]
    simp only [stepModel, hlt, ↓reduceIte, e]
    exact (realCompModel_encloses n ρ _ _).of_eq_fun fun θ => by
      simp [sumVec_apply, stepFun, CertEmbedding.actionAt]

end Lawful

/-- The coordinates of the derivative of a differentiable map into `ℂⁿ × ℂⁿ`. -/
theorem fderiv_fst_apply {F : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hF : DifferentiableAt ℂ F θ) (v : Fin n → ℂ) (i : Fin n) :
    (fderiv ℂ F θ v).1 i = fderiv ℂ (fun θ => (F θ).1 i) θ v := by
  let L : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ))
  have h := (L.hasFDerivAt.comp θ hF.hasFDerivAt).fderiv
  have e : (fun θ => (F θ).1 i) = L ∘ F := rfl
  rw [e, h]
  rfl

theorem fderiv_snd_apply {F : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hF : DifferentiableAt ℂ F θ) (v : Fin n → ℂ) (i : Fin n) :
    (fderiv ℂ F θ v).2 i = fderiv ℂ (fun θ => (F θ).2 i) θ v := by
  let L : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))
  have h := (L.hasFDerivAt.comp θ hF.hasFDerivAt).fderiv
  have e : (fun θ => (F θ).2 i) = L ∘ F := rfl
  rw [e, h]
  rfl

variable [LawfulCertArith α]

theorem dstepModel_encloses {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) (dK : CertEmbedding α)
    (x : Fin n ⊕ Fin n) (j : Fin n) :
    (dstepModel n W pe dK (phaseNat x) j.val).Encloses n W.rho
      (fun θ => tangentMat (stepFun n dK) θ x j) := by
  have hd := differentiable_stepFun (n := n) dK
  rcases x with i | i
  · have hlt : phaseNat (Sum.inl i : Fin n ⊕ Fin n) < n := i.isLt
    simp only [dstepModel, hlt, ↓reduceIte]
    exact (compDerivModel_encloses hW hpe _ _ j).of_eq_fun fun θ => by
      rw [tangentMat_apply, sumVec_apply, Sum.elim_inl, fderiv_fst_apply (hd θ)]
      rfl
  · have hlt : ¬(phaseNat (Sum.inr i : Fin n ⊕ Fin n) < n) := by simp [phaseNat]
    have e : phaseNat (Sum.inr i : Fin n ⊕ Fin n) - n = i.val := by simp [phaseNat]
    simp only [dstepModel, hlt, ↓reduceIte, e]
    exact (compDerivModel_encloses hW hpe _ _ j).of_eq_fun fun θ => by
      rw [tangentMat_apply, sumVec_apply, Sum.elim_inr, fderiv_snd_apply (hd θ)]
      rfl

/-! ### The step norms -/

/-- `‖ΔK‖ ≤ d` on the strip of the weight `W`. -/
def stepSupOk (W : CertWeight) (dK : CertEmbedding α) (d : ℚ) : Bool :=
  decide (0 ≤ d) && (List.finRange (n + n)).all fun a => ble ((stepModel n dK a.val).supBound W) (ofRatDown d)

/-- `‖ΔK‖ ≤ d` on the real torus. -/
def stepRealOk (dK : CertEmbedding α) (d : ℚ) : Bool :=
  decide (0 ≤ d) && (List.finRange (n + n)).all fun a =>
    ble ((stepModel n dK a.val).supBound realWeight) (ofRatDown d)

/-- The row sums (`col = false`) or the column sums of the models of `DΔK`, against `d`, with the
sup bounds at the weight `Wb` (`realWeight` for the real torus). -/
def dstepOk (W Wb : CertWeight) (pe : PiEnclosure α) (dK : CertEmbedding α) (d : ℚ)
    (col : Bool) : Bool :=
  decide (0 ≤ d) && sumsOk (n := n) (fun a j => (dstepModel n W pe dK a j).supBound Wb) d col

omit [LawfulCertArith α] in
/-- A vector of `ℂⁿ × ℂⁿ` from coordinate bounds. -/
theorem norm_pair_le {u : (Fin n → ℂ) × (Fin n → ℂ)} {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ x, ‖sumVec n u x‖ ≤ d) : ‖u‖ ≤ d := by
  rw [← norm_sumVec]
  exact (pi_norm_le_iff_of_nonneg hd).2 h

theorem phase_of_fin (a : Fin (n + n)) :
    (finSumFinEquiv.symm a : Fin n ⊕ Fin n) = finSumFinEquiv.symm a ∧
      phaseNat (finSumFinEquiv.symm a) = a.val :=
  ⟨rfl, phaseNat_finSumFinEquiv_symm a⟩

theorem fin_of_phase (x : Fin n ⊕ Fin n) : (finSumFinEquiv x).val = phaseNat x := by
  simpa using (phaseNat_finSumFinEquiv_symm (finSumFinEquiv x)).symm

/-- **`(S1)`, `(S2)`: the step on a strip.** -/
theorem stepSup_le {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    {dK : CertEmbedding α} {d : ℚ} (h : stepSupOk (n := n) W dK d = true) :
    ∀ θ ∈ complexStrip n W.rho, ‖stepFun n dK θ‖ ≤ d := by
  intro θ hθ
  simp only [stepSupOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies] at h
  refine norm_pair_le (by exact_mod_cast h.1) fun x => ?_
  have hb := h.2 (finSumFinEquiv x)
  rw [fin_of_phase] at hb
  exact (CertModel.norm_le_supBound hW (stepModel_encloses dK W.rho x) hθ).trans (ble_le hb)

/-- **`(S3)`: the step on the real torus.** -/
theorem stepReal_le {dK : CertEmbedding α} {d : ℚ} (h : stepRealOk (n := n) dK d = true)
    (x : Fin n → ℝ) : ‖stepFun n dK (fun l => (x l : ℂ))‖ ≤ d := by
  simp only [stepRealOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies] at h
  refine norm_pair_le (by exact_mod_cast h.1) fun y => ?_
  have hb := h.2 (finSumFinEquiv y)
  rw [fin_of_phase] at hb
  exact (CertModel.norm_le_supBound_real one_pos (stepModel_encloses dK 1 y) x).trans (ble_le hb)

/-- **`(S4)` on a strip**: the row and column sums of `DΔK` (`‖DΔK‖`, `‖(DΔK)ᵀ‖`). -/
theorem tangentMat_step_le {W W' : CertWeight} {s N s' N' : ℕ} (hW : checkWeight W s N = true)
    (hW' : checkWeight W' s' N' = true) (hρ : W'.rho ≤ W.rho) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {dK : CertEmbedding α} {d dt : ℚ}
    (h : dstepOk (n := n) W W' pe dK d false = true)
    (ht : dstepOk (n := n) W W' pe dK dt true = true) :
    ∀ θ ∈ complexStrip n W'.rho, ‖tangentMat (stepFun n dK) θ‖ ≤ d ∧
      ‖(tangentMat (stepFun n dK) θ)ᵀ‖ ≤ dt := by
  intro θ hθ
  simp only [dstepOk, Bool.and_eq_true, decide_eq_true_eq] at h ht
  have hθW : θ ∈ complexStrip n W.rho := fun i => (hθ i).trans_le (by exact_mod_cast hρ)
  have hent : ∀ x j, ‖tangentMat (stepFun n dK) θ x j‖ ≤
      val ((dstepModel n W pe dK (phaseNat x) j.val).supBound W') := fun x j =>
    CertModel.norm_le_supBound hW' (fun θ' hθ' => dstepModel_encloses hW hpe dK x j θ'
      (fun i => (hθ' i).trans_le (by exact_mod_cast hρ))) hθ
  refine ⟨(norm_le_iff_forall_rowSum (by exact_mod_cast h.1)).2 fun x =>
    sumsOk_row h.2 x fun j => hent x j, (norm_le_iff_forall_rowSum (by exact_mod_cast ht.1)).2
    fun j => ?_⟩
  simp only [Matrix.transpose_apply]
  exact sumsOk_col ht.2 j fun x => hent x j

/-- **`(S4)` on the real torus.** -/
theorem tangentMat_step_real_le {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) {dK : CertEmbedding α} {d dt : ℚ}
    (h : dstepOk (n := n) W realWeight pe dK d false = true)
    (ht : dstepOk (n := n) W realWeight pe dK dt true = true) (y : Fin n → ℝ) :
    ‖tangentMat (stepFun n dK) (fun l => (y l : ℂ))‖ ≤ d ∧
      ‖(tangentMat (stepFun n dK) (fun l => (y l : ℂ)))ᵀ‖ ≤ dt := by
  simp only [dstepOk, Bool.and_eq_true, decide_eq_true_eq] at h ht
  have hρ := CertWeight.rho_pos hW
  have hent : ∀ x j, ‖tangentMat (stepFun n dK) (fun l => (y l : ℂ)) x j‖ ≤
      val ((dstepModel n W pe dK (phaseNat x) j.val).supBound realWeight) := fun x j =>
    CertModel.norm_le_supBound_real hρ (dstepModel_encloses hW hpe dK x j) y
  refine ⟨(norm_le_iff_forall_rowSum (by exact_mod_cast h.1)).2 fun x =>
    sumsOk_row h.2 x fun j => hent x j, (norm_le_iff_forall_rowSum (by exact_mod_cast ht.1)).2
    fun j => ?_⟩
  simp only [Matrix.transpose_apply]
  exact sumsOk_col ht.2 j fun x => hent x j

end KAM.CertificateSharp.Hybrid

end
