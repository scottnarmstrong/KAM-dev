/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModConstantsBd

/-!
# Positivity and monotonicity of the constants of the modified step

* `stepConsts_nonneg`: every constant of every step (also isoenergetic) is nonnegative.
* `stepConsts_mono`: `p ≼ p'` gives `stepConsts p ≤ stepConsts p'` fieldwise, for the plain step.
* `stepConsts_mono_iso`: the same for the isoenergetic step for every field except `QbN` and `Q`:
  the term `(1 + nϑ_ξ) Θ C_Ω Q̃_N C_0 ϑ_ξ / C_{ξL}` of `QbN` divides by `C_{ξL} = c C_{gL}`, which
  grows with `c` and `δ`, and the quotient is not monotone in general (see the handoff).
* `stepConsts_mono_sd`, `stepConsts_mono_delta`: the instances for the small-divisor constants and
  the bite; `stepCond_anti`: the step conditions persist for a smaller normalised error.
-/

@[expose] public noncomputable section

namespace KAM.Sharp2

theorem stepConsts_eq (p : StepIn) : stepConsts p =
    ⟨oCΩ p, oCE p, oCDE p, oCNN p, oC0 p, oCxiN p, oCKt p, oCDLt p, oCDLtT p, oCEt p, oQtN p,
      oCgL p, oCxiL p, oCDK p, oCEb p, oCG p, oCBb p, oCNb p, oCNbT p, sCDT p, oQbN p, oQL p,
      max (oQL p) (2 ^ p.κ * oQbN p)⟩ := rfl

/-- Every constant is nonnegative. -/
structure StepConsts.Nonneg (k : StepConsts) : Prop where
  CΩ : 0 ≤ k.CΩ
  CE : 0 ≤ k.CE
  CDE : 0 ≤ k.CDE
  CNN : 0 ≤ k.CNN
  C0 : 0 ≤ k.C0
  CxiN : 0 ≤ k.CxiN
  CKt : 0 ≤ k.CKt
  CDLt : 0 ≤ k.CDLt
  CDLtT : 0 ≤ k.CDLtT
  CEt : 0 ≤ k.CEt
  QtN : 0 ≤ k.QtN
  CgL : 0 ≤ k.CgL
  CxiL : 0 ≤ k.CxiL
  CDK : 0 ≤ k.CDK
  CEb : 0 ≤ k.CEb
  CG : 0 ≤ k.CG
  CBb : 0 ≤ k.CBb
  CNb : 0 ≤ k.CNb
  CNbT : 0 ≤ k.CNbT
  CDT : 0 ≤ k.CDT
  QbN : 0 ≤ k.QbN
  QL : 0 ≤ k.QL
  Q : 0 ≤ k.Q

/-- Fieldwise `≤` of all constants except `QbN` and `Q`. -/
structure StepConsts.LeCore (k k' : StepConsts) : Prop where
  CΩ : k.CΩ ≤ k'.CΩ
  CE : k.CE ≤ k'.CE
  CDE : k.CDE ≤ k'.CDE
  CNN : k.CNN ≤ k'.CNN
  C0 : k.C0 ≤ k'.C0
  CxiN : k.CxiN ≤ k'.CxiN
  CKt : k.CKt ≤ k'.CKt
  CDLt : k.CDLt ≤ k'.CDLt
  CDLtT : k.CDLtT ≤ k'.CDLtT
  CEt : k.CEt ≤ k'.CEt
  QtN : k.QtN ≤ k'.QtN
  CgL : k.CgL ≤ k'.CgL
  CxiL : k.CxiL ≤ k'.CxiL
  CDK : k.CDK ≤ k'.CDK
  CEb : k.CEb ≤ k'.CEb
  CG : k.CG ≤ k'.CG
  CBb : k.CBb ≤ k'.CBb
  CNb : k.CNb ≤ k'.CNb
  CNbT : k.CNbT ≤ k'.CNbT
  CDT : k.CDT ≤ k'.CDT
  QL : k.QL ≤ k'.QL

/-- Fieldwise `≤`. -/
structure StepConsts.Le (k k' : StepConsts) : Prop extends k.LeCore k' where
  QbN : k.QbN ≤ k'.QbN
  Q : k.Q ≤ k'.Q

theorem nn_QbN {p : StepIn} (h : p.Ok) : 0 ≤ oQbN p := by
  have ⟨a0, _⟩ := bd_sQtN h (StepIn.Le.refl p)
  have ⟨b0, _⟩ := bd_sCΩ h (StepIn.Le.refl p)
  have ⟨c0, _⟩ := bd_sC0 h (StepIn.Le.refl p)
  have ⟨d0, _⟩ := bd_sCxiL h (StepIn.Le.refl p)
  have hn : (0 : ℝ) ≤ p.n := by positivity
  unfold oQbN
  obtain ⟨⟩ := h
  split_ifs <;> positivity

theorem stepConsts_nonneg {p : StepIn} (h : p.Ok) : (stepConsts p).Nonneg := by
  have r := StepIn.Le.refl p
  rw [stepConsts_eq]
  exact {
    CΩ := (bd_sCΩ h r).1
    CE := (bd_sCE h r).1
    CDE := (bd_sCDE h r).1
    CNN := (bd_sCNN h r).1
    C0 := (bd_sC0 h r).1
    CxiN := (bd_sCxiN h r).1
    CKt := (bd_sCKt h r).1
    CDLt := (bd_sCDLt h r).1
    CDLtT := (bd_sCDLtT h r).1
    CEt := (bd_sCEt h r).1
    QtN := (bd_sQtN h r).1
    CgL := (bd_sCgL h r).1
    CxiL := (bd_sCxiL h r).1
    CDK := (bd_sCDK h r).1
    CEb := (bd_sCEb h r).1
    CG := (bd_sCG h r).1
    CBb := (bd_sCBb h r).1
    CNb := (bd_sCNb h r).1
    CNbT := (bd_sCNbT h r).1
    CDT := (bd_sCDT h r).1
    QbN := nn_QbN h
    QL := (bd_sQL h r).1
    Q := le_max_of_le_left (bd_sQL h r).1 }

theorem stepConsts_mono_iso {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    (stepConsts p).LeCore (stepConsts p') := by
  rw [stepConsts_eq, stepConsts_eq]
  exact {
    CΩ := (bd_sCΩ h hl).2
    CE := (bd_sCE h hl).2
    CDE := (bd_sCDE h hl).2
    CNN := (bd_sCNN h hl).2
    C0 := (bd_sC0 h hl).2
    CxiN := (bd_sCxiN h hl).2
    CKt := (bd_sCKt h hl).2
    CDLt := (bd_sCDLt h hl).2
    CDLtT := (bd_sCDLtT h hl).2
    CEt := (bd_sCEt h hl).2
    QtN := (bd_sQtN h hl).2
    CgL := (bd_sCgL h hl).2
    CxiL := (bd_sCxiL h hl).2
    CDK := (bd_sCDK h hl).2
    CEb := (bd_sCEb h hl).2
    CG := (bd_sCG h hl).2
    CBb := (bd_sCBb h hl).2
    CNb := (bd_sCNb h hl).2
    CNbT := (bd_sCNbT h hl).2
    CDT := (bd_sCDT h hl).2
    QL := (bd_sQL h hl).2 }

/-- **Monotonicity of the constants of the plain step** in the small-divisor constants, the bite,
the caps, the weight and `γ̄`. -/
theorem stepConsts_mono {p p' : StepIn} (h : p.Ok) (hl : p.Le p') (hi : p.iso = false) :
    (stepConsts p).Le (stepConsts p') := by
  have hc := stepConsts_mono_iso h hl
  have hQ := bd_sQbN h hl hi
  have hQL := (bd_sQL h hl).2
  refine { hc with QbN := ?_, Q := ?_ }
  · rw [stepConsts_eq, stepConsts_eq]; exact hQ.2
  · rw [stepConsts_eq, stepConsts_eq]
    refine max_le_max hQL ?_
    rw [hl.κ]
    exact mul_le_mul_of_nonneg_left hQ.2 (by have := h.κ0; positivity)


/-- Raising only the small-divisor constants `c`, `c¹`, `c̄` and the bite `δ`. -/
theorem StepIn.Le.of_sd {p : StepIn} {c' c1' cbar' δ' : ℝ} (hc : p.c ≤ c') (hc1 : p.c1 ≤ c1')
    (hcb : p.cbar ≤ cbar') (hδ : p.δ ≤ δ') :
    p.Le { p with c := c', c1 := c1', cbar := cbar', δ := δ' } :=
  { StepIn.Le.refl p with c := hc, c1 := hc1, cbar := hcb, δ := hδ }

/-- The constants of the plain step are nondecreasing in the small-divisor constants and the
bite. -/
theorem stepConsts_mono_sd {p : StepIn} (h : p.Ok) (hi : p.iso = false) {c' c1' cbar' δ' : ℝ}
    (hc : p.c ≤ c') (hc1 : p.c1 ≤ c1') (hcb : p.cbar ≤ cbar') (hδ : p.δ ≤ δ') :
    (stepConsts p).Le (stepConsts { p with c := c', c1 := c1', cbar := cbar', δ := δ' }) :=
  stepConsts_mono h (StepIn.Le.of_sd hc hc1 hcb hδ) hi

/-- **Monotone in the bite** at fixed small-divisor constants (the tail of the engine). -/
theorem stepConsts_mono_delta {p : StepIn} (h : p.Ok) (hi : p.iso = false) {δ' : ℝ}
    (hδ : p.δ ≤ δ') : (stepConsts p).Le (stepConsts { p with δ := δ' }) :=
  stepConsts_mono_sd h hi le_rfl le_rfl le_rfl hδ

/-- The isoenergetic step: every constant except `QbN` and `Q` is monotone in the bite. -/
theorem stepConsts_monoCore_delta {p : StepIn} (h : p.Ok) {δ' : ℝ} (hδ : p.δ ≤ δ') :
    (stepConsts p).LeCore (stepConsts { p with δ := δ' }) :=
  stepConsts_mono_iso h (StepIn.Le.of_sd le_rfl le_rfl le_rfl hδ)

theorem stepConsts_CxiL_pos {p : StepIn} (h : p.Ok) (hc : 0 < p.c) (hl : 0 < p.lam) :
    0 < (stepConsts p).CxiL := by
  have r := StepIn.Le.refl p
  have ⟨a0, _⟩ := bd_sCxiN h r
  have ⟨b0, _⟩ := bd_sC0 h r
  rw [stepConsts_eq]
  show 0 < oCxiL p
  unfold oCxiL oCgL
  have := h.t
  have := h.Θ
  split_ifs <;> positivity

/-- The step conditions persist for a smaller normalised error. -/
theorem stepCond_anti {p : StepIn} (h : p.Ok) {X X' : ℝ} (hXX : X' ≤ X)
    (hc : stepCond p X) : stepCond p X' := by
  have hk := stepConsts_nonneg h
  have := hk.CΩ; have := hk.CDE; have := hk.CxiL; have := hk.CgL; have := hk.CKt
  have := hk.CDLt; have := hk.CDLtT; have := hk.CG; have := hk.CDK; have := hk.CDT; have := hk.Q
  have := h.sB; have := h.sT; have := h.γb; have := h.δ0
  unfold stepCond at hc ⊢
  dsimp only at hc ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc
  exact ⟨le_trans (by gcongr) c1, le_trans (by gcongr) c2, le_trans (by gcongr) c3,
    le_trans (by gcongr) c4, le_trans (by gcongr) c5, le_trans (by gcongr) c6,
    le_trans (by gcongr) c7, le_trans (by gcongr) c8, le_trans (by gcongr) c9,
    le_trans (by gcongr) c10⟩

end KAM.Sharp2

end
