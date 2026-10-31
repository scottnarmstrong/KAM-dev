/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.Energy
public import KAM.CertificateSharp.Hybrid.TransferQ
public import KAM.CertificateSharp.V2.RouteACore

/-!
# The step claims of the hybrid witness (package C8c)

The step `ΔK̂` of the witness is a rational embedding increment (format v1, `step.dK`); `ratE`
rounds its coefficients into the backend, and the step of the theorem is `stepFun n (ratE dK)` (any
rounding is sound: the claims are checked on the rounded step, which is the step that is
certified).

* `HybStep`: the step data (format v1 `step`): `ΔK̂`, `s₁`, the weights of `T_{ρ₁}`, `T_{ρ∞}` and
  the torsion strip, the claims `(S1)–(S7)` (`StepNumQ`), `ℓ_H`, `d_ω`;
* `hybStepOk`: the checks of format §3, at the restart strip `ρ₁`, the limit strip `ρi` and the
  torsion strip `ρT` (rationals of the restarted run);
* `hybStepBounds`: C8b's `StepBounds`, `|ε̃| ≤ ℓ_H` and `|s₁ω* − sω*| ≤ d_ω` from a passing check.

`dE0`, `dE0R` use the whole-error Cauchy bound `n e/(ρ − ρT)` (format §3, the alternative), which
holds on the real torus as well.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.CertificateSharp.Hybrid

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp CertArith Matrix
open KAM.CertificateSharp.V2 (BaseFacts norm_le_boxNormUp boxNormUp)

variable {n : ℕ} {α : Type} [CertArith α]

/-! ### The rational step, rounded into the backend -/

/-- A rational coefficient, rounded into the backend. -/
def ratC (z : CC ℚ) : CC α := ⟨ofRatUp z.re, ofRatUp z.im⟩

/-- A rational real polynomial, rounded into the backend. -/
def ratP (P : CertRealPoly ℚ) : CertRealPoly α :=
  ⟨ofRatUp P.zero, P.half.map fun t => (t.1, ratC t.2)⟩

/-- A rational embedding increment, rounded into the backend. -/
def ratE (K : CertEmbedding ℚ) : CertEmbedding α :=
  ⟨K.angleDeg, K.angle.map ratP, K.actionDeg, K.action.map ratP⟩

/-! ### The checks -/

/-- The step data of the hybrid witness (format v1, `step`). -/
structure HybStep where
  /-- `ΔK̂`, with the degrees of the base embedding. -/
  dK : CertEmbedding ℚ
  /-- The new ray parameter. -/
  s1 : ℚ
  /-- The weights of `T_{ρ₁}`, `T_{ρ∞}` and the torsion strip `T'`. -/
  W1 : CertWeight
  Winf : CertWeight
  WT : CertWeight
  /-- The claims `(S1)–(S7)`. -/
  cl : StepNumQ
  /-- `ℓ_H ≥ |⟨H∘K̂⟩ − E₀ + ⟨DH(K̂)ΔK̂⟩|`. -/
  lH : ℚ
  /-- `d_ω ≥ |s₁ − s| boxNormUp`. -/
  dw : ℚ

/-- The weights and the strips: `ρ₁ ≤ W1.rho ≤ ρ`, `ρi ≤ Winf.rho`, `0 < ρT ≤ WT.rho`, `ρT < ρ`. -/
def hybWeightsOk (c : TorusCertificate n α) (w : HybStep) (ρ₁ ρi ρT : ℚ) : Bool :=
  checkWeight w.W1 c.expHalvings c.expOrder && checkWeight w.Winf c.expHalvings c.expOrder &&
    checkWeight w.WT c.expHalvings c.expOrder && decide (ρ₁ ≤ w.W1.rho) &&
    decide (w.W1.rho ≤ c.weight.rho) && decide (ρi ≤ w.Winf.rho) && decide (ρT ≤ w.WT.rho) &&
    decide (0 < ρT) && decide (ρT < c.params.rho)

/-- `(S1)–(S4)`: the norms of `ΔK̂` and `DΔK̂` on `T_{ρ₁}`, `T_{ρ∞}` and the real torus (the real
bounds from models built at the weight of `T_{ρ∞}`). -/
def hybPolyOk (w : HybStep) (pe : PiEnclosure α) : Bool :=
  stepSupOk (n := n) w.W1 (ratE (α := α) w.dK) w.cl.d0 &&
    stepSupOk (n := n) w.Winf (ratE (α := α) w.dK) w.cl.dinf &&
    stepRealOk (n := n) (ratE (α := α) w.dK) w.cl.d0R &&
    dstepOk (n := n) w.W1 w.W1 pe (ratE w.dK) w.cl.d1 false &&
    dstepOk (n := n) w.W1 w.W1 pe (ratE w.dK) w.cl.d1t true &&
    dstepOk (n := n) w.Winf realWeight pe (ratE w.dK) w.cl.d1R false &&
    dstepOk (n := n) w.Winf realWeight pe (ratE w.dK) w.cl.d1tR true

/-- `(S6)`, `(S7)`: `‖Ω_K‖`, `‖Ω_{K₁}‖` on the torsion strip and on the real torus. -/
def hybOmegaOk (c : TorusCertificate n α) (w : HybStep) : Bool :=
  omegaOk (n := n) w.WT w.WT c.cfgFull c.piEnc (dkM c w.WT) w.cl.o0 &&
    omegaOk (n := n) w.Winf realWeight c.cfgFull c.piEnc (dkM c w.Winf) w.cl.o0R &&
    omegaOk (n := n) w.WT w.WT c.cfgFull c.piEnc (dk1M c w.WT (ratE w.dK)) w.cl.o1 &&
    omegaOk (n := n) w.Winf realWeight c.cfgFull c.piEnc (dk1M c w.Winf (ratE w.dK)) w.cl.o1R

/-- `‖DE‖ ≤ n e/(ρ − ρT)` (Cauchy from `T_ρ`) is below `dE0` and `dE0R`. -/
def hybCauchyOk (c : TorusCertificate n α) (w : HybStep) (ρT : ℚ) : Bool :=
  decide (n * c.params.err ≤ w.cl.dE0 * (c.params.rho - ρT)) &&
    decide (n * c.params.err ≤ w.cl.dE0R * (c.params.rho - ρT))

/-- `(S5)` and `ℓ_H`, from the compositions of the base checks. -/
def hybCompOk (c : TorusCertificate n α) (w : HybStep) : Bool :=
  match Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) with
  | some ms =>
    match Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
        (torsionSlots n c.ham.jet) with
    | some mt =>
      match Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
          [c.ham.jet.v0] with
      | some [mv] => linOk c w.W1 w.s1 (ratE w.dK) ms mt w.cl.lE &&
          energyLinOk c (ratE w.dK) mv ms w.lH
      | _ => false
    | none => false
  | none => false

/-- The step checks of format v1 §3, at the strips `ρ₁`, `ρi`, `ρT` of the restarted run. -/
def hybStepOk (c : TorusCertificate n α) (w : HybStep) (ρ₁ ρi ρT : ℚ) : Bool :=
  hybWeightsOk c w ρ₁ ρi ρT && hybPolyOk (n := n) w c.piEnc && hybOmegaOk c w &&
    hybCauchyOk c w ρT && hybCompOk c w &&
    decide (|w.s1 - c.params.s| * boxNormUp c.freqBox ≤ w.dw)

/-! ### Soundness -/

omit [CertArith α] in
theorem mem_strip_of_le {ρ ρ' : ℝ} (hρ : ρ ≤ ρ') {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ) :
    θ ∈ complexStrip n ρ' := fun i => (hθ i).trans_le hρ

omit [CertArith α] in
theorem real_mem_strip {ρ : ℝ} (hρ : 0 < ρ) (x : Fin n → ℝ) :
    (fun l => (x l : ℂ)) ∈ complexStrip n ρ := fun i => by simpa using hρ

theorem hybCompOk_sound {c : TorusCertificate n α} {w : HybStep} (h : hybCompOk c w = true) :
    ∃ ms mt mv, Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
        (d1Slots n c.ham.jet) = some ms ∧
      Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
        (torsionSlots n c.ham.jet) = some mt ∧
      Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
        [c.ham.jet.v0] = some [mv] ∧
      linOk c w.W1 w.s1 (ratE w.dK) ms mt w.cl.lE = true ∧
      energyLinOk c (ratE w.dK) mv ms w.lH = true := by
  unfold hybCompOk at h
  split at h
  · rename_i ms hc
    split at h
    · rename_i mt ht
      split at h
      · rename_i mv hv
        simp only [Bool.and_eq_true] at h
        exact ⟨ms, mt, mv, hc, ht, hv, h.1, h.2⟩
      · simp at h
    · simp at h
  · simp at h

variable [LawfulCertArith α]

/-- **The step claims give C8b's `StepBounds`**, `|ε̃| ≤ ℓ_H` and `|s₁ω* − sω*| ≤ d_ω`. -/
theorem hybStepBounds {c : TorusCertificate n α} {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    {w : HybStep} {ρ₁ ρi ρT : ℚ} (h : hybStepOk c w ρ₁ ρi ρT = true) :
    KAM.Sharp2.Hybrid.StepBounds c.H c.K (stepFun n (ratE (α := α) w.dK))
        ((c.params.s : ℝ) • ωstar) ((w.s1 : ℝ) • ωstar) ρ₁ ρi ρT w.cl.toNum ∧
      ‖KAM.Sharp2.Hybrid.linNewEnergy c.H c.K (stepFun n (ratE (α := α) w.dK)) c.params.E0‖ ≤
        w.lH ∧
      ‖(w.s1 : ℝ) • ωstar - (c.params.s : ℝ) • ωstar‖ ≤ w.dw := by
  have S := checkStatic_sound B.hs
  simp only [hybStepOk, hybWeightsOk, hybPolyOk, hybOmegaOk, hybCauchyOk, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hW1, hWi⟩, hWT⟩, hρ1⟩, hρ1c⟩, hρi⟩, hρT⟩, hT0⟩, hTρ⟩,
    ⟨⟨⟨⟨⟨⟨hd0, hdinf⟩, hd0R⟩, hd1⟩, hd1t⟩, hd1R⟩, hd1tR⟩⟩,
    ⟨⟨⟨ho0, ho0R⟩, ho1⟩, ho1R⟩⟩, ⟨hE0, hE0R⟩⟩, hcomp⟩, hdw⟩ := h
  obtain ⟨ms, mt, mv, hc, ht, hv, hlin, hen⟩ := hybCompOk_sound hcomp
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := fun θ hθ => by
    rw [S.hrho] at hθ
    exact B.hEm.1 θ hθ (Metric.mem_ball_self S.hμ)
  have hρ1' : (ρ₁ : ℝ) ≤ w.W1.rho := by exact_mod_cast hρ1
  have hρi' : (ρi : ℝ) ≤ w.Winf.rho := by exact_mod_cast hρi
  have hρT' : (ρT : ℝ) ≤ w.WT.rho := by exact_mod_cast hρT
  have hT0' : (0 : ℝ) < ρT := by exact_mod_cast hT0
  have hδ : (0 : ℝ) < (c.params.rho : ℝ) - ρT := by
    have : (ρT : ℝ) < c.params.rho := by exact_mod_cast hTρ
    linarith
  -- `DE` on `T_{ρT}` by Cauchy from `T_ρ`
  have hEd : DifferentiableOn ℂ (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar))
      (complexStrip n c.params.rho) :=
    KAM.Apost.FrameAux.differentiableOn_invarianceError (V2.L1.standingAt B hdio)
      (CertEmbedding.differentiable_eval n c.emb).differentiableOn
      fun θ hθ => B.hEm.1 θ hθ (Metric.mem_ball_self S.hμ)
  have hDE := KAM.Sharp2.Hybrid.errDerivMat_step_le hEd B.hE hδ
  have hsubT : (c.params.rho : ℝ) - ((c.params.rho : ℝ) - ρT) = ρT := by ring
  rw [hsubT] at hDE
  have hcau : ∀ {d : ℚ}, (n : ℚ) * c.params.err ≤ d * (c.params.rho - ρT) →
      (n : ℝ) * ((c.params.rho : ℝ) - ρT)⁻¹ * c.params.err ≤ d := fun {d} hd => by
    have hd' : (n : ℝ) * c.params.err ≤ d * ((c.params.rho : ℝ) - ρT) := by exact_mod_cast hd
    rw [mul_right_comm, ← div_eq_mul_inv, div_le_iff₀ hδ]
    exact hd'
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact fun θ hθ => stepSup_le hW1 hd0 θ (mem_strip_of_le hρ1' hθ)
  · exact fun θ hθ => stepSup_le hWi hdinf θ (mem_strip_of_le hρi' hθ)
  · exact fun θ hθ => tangentMat_step_le hW1 hW1 le_rfl S.hpe hd1 hd1t θ (mem_strip_of_le hρ1' hθ)
  · intro x
    exact ⟨stepReal_le hd0R x, tangentMat_step_real_le hWi S.hpe hd1R hd1tR x⟩
  · intro θ hθ
    exact linNewError_le B.hs B.hH.1 hKD hc ht hω hW1 (by exact_mod_cast hρ1c) hlin θ
      (mem_strip_of_le hρ1' hθ)
  · intro θ hθ
    exact ⟨(hDE θ hθ).trans (hcau hE0), lagrangeMat_le hWT hWT le_rfl c.cfgFull S.hpe
      (dkM_encloses B.hs hWT) ho0 θ (mem_strip_of_le hρT' hθ)⟩
  · intro x
    exact ⟨(hDE _ (real_mem_strip hT0' x)).trans (hcau hE0R),
      lagrangeMat_real_le hWi c.cfgFull S.hpe (dkM_encloses B.hs hWi) ho0R x⟩
  · intro θ hθ
    exact lagrangeMat_le hWT hWT le_rfl c.cfgFull S.hpe (dk1M_encloses B.hs hWT _) ho1 θ
      (mem_strip_of_le hρT' hθ)
  · intro x
    exact lagrangeMat_real_le hWi c.cfgFull S.hpe (dk1M_encloses B.hs hWi _) ho1R x
  · exact linNewEnergy_le B.hs B.hH.1 hKD hv hc hen
  · rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have hdw' : |(w.s1 : ℝ) - c.params.s| * (boxNormUp c.freqBox : ℝ) ≤ w.dw := by
      exact_mod_cast hdw
    exact (mul_le_mul_of_nonneg_left (norm_le_boxNormUp hω) (abs_nonneg _)).trans hdw'

end KAM.CertificateSharp.Hybrid

end
