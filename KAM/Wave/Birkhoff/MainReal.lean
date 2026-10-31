/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainConj
public import KAM.Wave.Analytic.ComplexificationLp

/-!
# Real restrictions (blueprint-W `bpW:w3:real-restrict`)

Package W3-MAIN, blueprint label `bpW:w3:real-restrict`.

`E_{a,p}` in weighted coordinates is `BirkReal = ℓ²_ℝ × ℓ²_ℝ`. `birkZR = 𝒵 ∘ ι_ℝ : E → 𝔚`
and `birkPi = Re ∘ 𝒵⁻¹ : 𝔚 → E` (`ℝ`-linear, continuous, `Π(𝒵 x) = x`, `𝒵 Π w = w` for
`ϱ w = w`). `real_restrict`: an analytic `f` commuting with `ϱ` has the real analytic restriction
`x ↦ Π f(𝒵 x)`, with `𝒵 (Π f(𝒵 x)) = f(𝒵 x)`; `real_restrict_fun` for real `P`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

/-- `E_{a,p}` in weighted coordinates. -/
abbrev BirkReal : Type := lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2

/-- `𝒵` restricted to real points, `E → 𝔚`. -/
def birkZR : BirkReal →L[ℝ] BirkSpace := (birkZ.restrictScalars ℝ).comp birkReal

/-- `Π(w) = Re 𝒵⁻¹ w`, `𝔚 → E`. -/
def birkPi : BirkSpace →L[ℝ] BirkReal :=
  ((reLp.comp (ContinuousLinearMap.fst ℝ (lp (fun _ : ℕ+ => ℂ) 2) (lp (fun _ : ℕ+ => ℂ) 2))).prod
    (reLp.comp (ContinuousLinearMap.snd ℝ (lp (fun _ : ℕ+ => ℂ) 2)
      (lp (fun _ : ℕ+ => ℂ) 2)))).comp (birkZinv.restrictScalars ℝ)

theorem birkZR_apply (x : BirkReal) : birkZR x = birkZ (birkReal x) := rfl

theorem norm_birkReal (x : BirkReal) : ‖birkReal x‖ = ‖x‖ := by
  simp only [birkReal_apply, Prod.norm_def, norm_complexifyLp]

theorem norm_birkZR_le (x : BirkReal) : ‖birkZR x‖ ≤ Real.sqrt 2 * ‖x‖ := by
  rw [birkZR_apply]
  refine (norm_birkZ_le _).trans ?_
  rw [norm_birkReal]

theorem birkPi_birkZR (x : BirkReal) : birkPi (birkZR x) = x := by
  simp only [birkPi, birkZR_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', birkZinv_birkZ, ContinuousLinearMap.prod_apply,
    birkReal_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    reLp_complexifyLp]

theorem norm_birkPi_le (w : BirkSpace) : ‖birkPi w‖ ≤ ‖w‖ := by
  simp only [birkPi, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Prod.norm_def]
  refine max_le ((norm_reLp_le _).trans ?_) ((norm_reLp_le _).trans ?_)
  · exact (le_max_left _ _).trans (norm_birkZinv_le w)
  · exact (le_max_right _ _).trans (norm_birkZinv_le w)

theorem birkZR_birkPi (w : BirkSpace) (hw : birkRho w = w) : birkZR (birkPi w) = w := by
  obtain ⟨x, hx⟩ := exists_birkZ_of_birkRho_eq w hw
  have : w = birkZR x := hx.symm
  rw [this, birkPi_birkZR]

theorem birkRho_birkZR (x : BirkReal) : birkRho (birkZR x) = birkZR x := birkRho_birkZ_real x

/-- (`bpW:w3:real-restrict`) The real restriction of an analytic `f` commuting with `ϱ`. -/
theorem real_restrict {U : Set BirkSpace} {f : BirkSpace → BirkSpace}
    (hf : AnalyticOnNhd ℂ f U) (hρ : ∀ w ∈ U, f (birkRho w) = birkRho (f w)) :
    AnalyticOnNhd ℝ (fun x : BirkReal => birkPi (f (birkZR x))) {x | birkZR x ∈ U} ∧
      ∀ x : BirkReal, birkZR x ∈ U → birkZR (birkPi (f (birkZR x))) = f (birkZR x) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have h1 : AnalyticAt ℝ f (birkZR x) := (hf _ hx).restrictScalars
    exact birkPi.analyticAt _ |>.comp (h1.comp (birkZR.analyticAt x))
  · refine birkZR_birkPi _ ?_
    have := hρ _ hx
    rw [birkRho_birkZR] at this
    exact this.symm

/-- (`bpW:w3:real-restrict`) For real analytic `P`, `x ↦ P(𝒵 x)` is real valued and real
analytic. -/
theorem real_restrict_fun {U : Set BirkSpace} {P : BirkSpace → ℂ}
    (hP : AnalyticOnNhd ℂ P U) (hreal : ∀ w ∈ U, P (birkRho w) = conj (P w)) :
    AnalyticOnNhd ℝ (fun x : BirkReal => (P (birkZR x)).re) {x | birkZR x ∈ U} ∧
      ∀ x : BirkReal, birkZR x ∈ U → (((P (birkZR x)).re : ℝ) : ℂ) = P (birkZR x) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have h1 : AnalyticAt ℝ P (birkZR x) := (hP _ hx).restrictScalars
    exact Complex.reCLM.analyticAt _ |>.comp (h1.comp (birkZR.analyticAt x))
  · have := hreal _ hx
    rw [birkRho_birkZR] at this
    exact (Complex.conj_eq_iff_re.1 this.symm)

end KAM.Wave

end
