/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModConstantsData

/-!
# Monotonicity of each constant of the modified step

`bd_X : Bd X p p'` is `0 ≤ X p ≤ X p'` for `p ≼ p'` (`StepIn.Le`) and each helper `X` of
`ModConstantsData`; every proof is a `positivity`/`gcongr` closure of the earlier ones. For
`QbN` the step must be plain (`p.iso = false`): its isoenergetic term divides by `C_{ξL}`.
-/

@[expose] public noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace KAM.Sharp2

theorem bd_sg {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sg p p' := by
  have h' := h.mono hl
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sg
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sKt {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sKt p p' := by
  have h' := h.mono hl
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sKt
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCΩ {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCΩ p p' := by
  have h' := h.mono hl
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCΩ
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCEL {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCEL p p' := by
  have h' := h.mono hl
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCEL
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCEN {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCEN p p' := by
  have h' := h.mono hl
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCEN
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCE {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCE p p' := by
  have h' := h.mono hl
  obtain ⟨asg0, asg1⟩ := bd_sg h hl
  have asg2 := asg0.trans asg1
  obtain ⟨asCEL0, asCEL1⟩ := bd_sCEL h hl
  have asCEL2 := asCEL0.trans asCEL1
  obtain ⟨asCEN0, asCEN1⟩ := bd_sCEN h hl
  have asCEN2 := asCEN0.trans asCEN1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCE
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCDE {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCDE p p' := by
  have h' := h.mono hl
  obtain ⟨asg0, asg1⟩ := bd_sg h hl
  have asg2 := asg0.trans asg1
  obtain ⟨asCE0, asCE1⟩ := bd_sCE h hl
  have asCE2 := asCE0.trans asCE1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCDE
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCNN {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCNN p p' := by
  have h' := h.mono hl
  obtain ⟨asCE0, asCE1⟩ := bd_sCE h hl
  have asCE2 := asCE0.trans asCE1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCNN
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sAvgB {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sAvgB p p' := by
  have h' := h.mono hl
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sAvgB
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sC0 {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sC0 p p' := by
  have h' := h.mono hl
  obtain ⟨asAvgB0, asAvgB1⟩ := bd_sAvgB h hl
  have asAvgB2 := asAvgB0.trans asAvgB1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sC0
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCxiN {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCxiN p p' := by
  have h' := h.mono hl
  obtain ⟨asC00, asC01⟩ := bd_sC0 h hl
  have asC02 := asC00.trans asC01
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCxiN
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCKt {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCKt p p' := by
  have h' := h.mono hl
  obtain ⟨asCxiN0, asCxiN1⟩ := bd_sCxiN h hl
  have asCxiN2 := asCxiN0.trans asCxiN1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCKt
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCDLt {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCDLt p p' := by
  have h' := h.mono hl
  obtain ⟨asC00, asC01⟩ := bd_sC0 h hl
  have asC02 := asC00.trans asC01
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCDLt
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCDLtT {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCDLtT p p' := by
  have h' := h.mono hl
  obtain ⟨asC00, asC01⟩ := bd_sC0 h hl
  have asC02 := asC00.trans asC01
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCDLtT
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCdN {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCdN p p' := by
  have h' := h.mono hl
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCdN
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCXN {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCXN p p' := by
  have h' := h.mono hl
  obtain ⟨asCdN0, asCdN1⟩ := bd_sCdN h hl
  have asCdN2 := asCdN0.trans asCdN1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCXN
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCEt {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCEt p p' := by
  have h' := h.mono hl
  obtain ⟨asCE0, asCE1⟩ := bd_sCE h hl
  have asCE2 := asCE0.trans asCE1
  obtain ⟨asCXN0, asCXN1⟩ := bd_sCXN h hl
  have asCXN2 := asCXN0.trans asCXN1
  obtain ⟨asCxiN0, asCxiN1⟩ := bd_sCxiN h hl
  have asCxiN2 := asCxiN0.trans asCxiN1
  obtain ⟨asg0, asg1⟩ := bd_sg h hl
  have asg2 := asg0.trans asg1
  obtain ⟨asCKt0, asCKt1⟩ := bd_sCKt h hl
  have asCKt2 := asCKt0.trans asCKt1
  obtain ⟨asKt0, asKt1⟩ := bd_sKt h hl
  have asKt2 := asKt0.trans asKt1
  obtain ⟨asC00, asC01⟩ := bd_sC0 h hl
  have asC02 := asC00.trans asC01
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCEt
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sQtN {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sQtN p p' := by
  have h' := h.mono hl
  obtain ⟨asCDLtT0, asCDLtT1⟩ := bd_sCDLtT h hl
  have asCDLtT2 := asCDLtT0.trans asCDLtT1
  obtain ⟨asCEt0, asCEt1⟩ := bd_sCEt h hl
  have asCEt2 := asCEt0.trans asCEt1
  obtain ⟨asCNN0, asCNN1⟩ := bd_sCNN h hl
  have asCNN2 := asCNN0.trans asCNN1
  obtain ⟨asCxiN0, asCxiN1⟩ := bd_sCxiN h hl
  have asCxiN2 := asCxiN0.trans asCxiN1
  obtain ⟨asCKt0, asCKt1⟩ := bd_sCKt h hl
  have asCKt2 := asCKt0.trans asCKt1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sQtN
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCgL {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCgL p p' := by
  have h' := h.mono hl
  obtain ⟨asCxiN0, asCxiN1⟩ := bd_sCxiN h hl
  have asCxiN2 := asCxiN0.trans asCxiN1
  obtain ⟨asC00, asC01⟩ := bd_sC0 h hl
  have asC02 := asC00.trans asC01
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCgL
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCxiL {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCxiL p p' := by
  have h' := h.mono hl
  obtain ⟨asCgL0, asCgL1⟩ := bd_sCgL h hl
  have asCgL2 := asCgL0.trans asCgL1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCxiL
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCDK {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCDK p p' := by
  have h' := h.mono hl
  obtain ⟨asKt0, asKt1⟩ := bd_sKt h hl
  have asKt2 := asKt0.trans asKt1
  obtain ⟨asCxiL0, asCxiL1⟩ := bd_sCxiL h hl
  have asCxiL2 := asCxiL0.trans asCxiL1
  obtain ⟨asg0, asg1⟩ := bd_sg h hl
  have asg2 := asg0.trans asg1
  obtain ⟨asCKt0, asCKt1⟩ := bd_sCKt h hl
  have asCKt2 := asCKt0.trans asCKt1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCDK
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCEb {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCEb p p' := by
  have h' := h.mono hl
  obtain ⟨asCEt0, asCEt1⟩ := bd_sCEt h hl
  have asCEt2 := asCEt0.trans asCEt1
  obtain ⟨asKt0, asKt1⟩ := bd_sKt h hl
  have asKt2 := asKt0.trans asKt1
  obtain ⟨asCgL0, asCgL1⟩ := bd_sCgL h hl
  have asCgL2 := asCgL0.trans asCgL1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCEb
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCG {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCG p p' := by
  have h' := h.mono hl
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCG
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCBb {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCBb p p' := by
  have h' := h.mono hl
  obtain ⟨asCG0, asCG1⟩ := bd_sCG h hl
  have asCG2 := asCG0.trans asCG1
  obtain ⟨asCDK0, asCDK1⟩ := bd_sCDK h hl
  have asCDK2 := asCDK0.trans asCDK1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCBb
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCNb {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCNb p p' := by
  have h' := h.mono hl
  obtain ⟨asCDK0, asCDK1⟩ := bd_sCDK h hl
  have asCDK2 := asCDK0.trans asCDK1
  obtain ⟨asCBb0, asCBb1⟩ := bd_sCBb h hl
  have asCBb2 := asCBb0.trans asCBb1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCNb
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCNbT {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCNbT p p' := by
  have h' := h.mono hl
  obtain ⟨asCBb0, asCBb1⟩ := bd_sCBb h hl
  have asCBb2 := asCBb0.trans asCBb1
  obtain ⟨asCDK0, asCDK1⟩ := bd_sCDK h hl
  have asCDK2 := asCDK0.trans asCDK1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCNbT
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sw {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sw p p' := by
  have h' := h.mono hl
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sw
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCDT0 {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCDT0 p p' := by
  have h' := h.mono hl
  obtain ⟨asCNbT0, asCNbT1⟩ := bd_sCNbT h hl
  have asCNbT2 := asCNbT0.trans asCNbT1
  obtain ⟨asCNb0, asCNb1⟩ := bd_sCNb h hl
  have asCNb2 := asCNb0.trans asCNb1
  obtain ⟨asCDK0, asCDK1⟩ := bd_sCDK h hl
  have asCDK2 := asCDK0.trans asCDK1
  obtain ⟨asg0, asg1⟩ := bd_sg h hl
  have asg2 := asg0.trans asg1
  obtain ⟨asCDE0, asCDE1⟩ := bd_sCDE h hl
  have asCDE2 := asCDE0.trans asCDE1
  obtain ⟨asw0, asw1⟩ := bd_sw h hl
  have asw2 := asw0.trans asw1
  obtain ⟨asCΩ0, asCΩ1⟩ := bd_sCΩ h hl
  have asCΩ2 := asCΩ0.trans asCΩ1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCDT0
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sCDT {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sCDT p p' := by
  have h' := h.mono hl
  obtain ⟨asCDT00, asCDT01⟩ := bd_sCDT0 h hl
  have asCDT02 := asCDT00.trans asCDT01
  obtain ⟨asC00, asC01⟩ := bd_sC0 h hl
  have asC02 := asC00.trans asC01
  obtain ⟨asg0, asg1⟩ := bd_sg h hl
  have asg2 := asg0.trans asg1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sCDT
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sQbN {p p' : StepIn} (h : p.Ok) (hl : p.Le p') (hi : p.iso = false) :
    Bd sQbN p p' := by
  have h' := h.mono hl
  obtain ⟨asQtN0, asQtN1⟩ := bd_sQtN h hl
  have asQtN2 := asQtN0.trans asQtN1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sQbN
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  simp only [hi, ite_false, Bool.false_eq_true]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sQL0 {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sQL0 p p' := by
  have h' := h.mono hl
  obtain ⟨asCKt0, asCKt1⟩ := bd_sCKt h hl
  have asCKt2 := asCKt0.trans asCKt1
  obtain ⟨asg0, asg1⟩ := bd_sg h hl
  have asg2 := asg0.trans asg1
  obtain ⟨asCΩ0, asCΩ1⟩ := bd_sCΩ h hl
  have asCΩ2 := asCΩ0.trans asCΩ1
  obtain ⟨asCEt0, asCEt1⟩ := bd_sCEt h hl
  have asCEt2 := asCEt0.trans asCEt1
  obtain ⟨asCxiL0, asCxiL1⟩ := bd_sCxiL h hl
  have asCxiL2 := asCxiL0.trans asCxiL1
  obtain ⟨asCgL0, asCgL1⟩ := bd_sCgL h hl
  have asCgL2 := asCgL0.trans asCgL1
  obtain ⟨asKt0, asKt1⟩ := bd_sKt h hl
  have asKt2 := asKt0.trans asKt1
  obtain ⟨asCDLt0, asCDLt1⟩ := bd_sCDLt h hl
  have asCDLt2 := asCDLt0.trans asCDLt1
  obtain ⟨asCNbT0, asCNbT1⟩ := bd_sCNbT h hl
  have asCNbT2 := asCNbT0.trans asCNbT1
  obtain ⟨asCEb0, asCEb1⟩ := bd_sCEb h hl
  have asCEb2 := asCEb0.trans asCEb1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sQL0
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

theorem bd_sQL {p p' : StepIn} (h : p.Ok) (hl : p.Le p') :
    Bd sQL p p' := by
  have h' := h.mono hl
  obtain ⟨asQL00, asQL01⟩ := bd_sQL0 h hl
  have asQL02 := asQL00.trans asQL01
  obtain ⟨asC00, asC01⟩ := bd_sC0 h hl
  have asC02 := asC00.trans asC01
  obtain ⟨asCgL0, asCgL1⟩ := bd_sCgL h hl
  have asCgL2 := asCgL0.trans asCgL1
  obtain ⟨asg0, asg1⟩ := bd_sg h hl
  have asg2 := asg0.trans asg1
  obtain ⟨asCDLt0, asCDLt1⟩ := bd_sCDLt h hl
  have asCDLt2 := asCDLt0.trans asCDLt1
  obtain ⟨asQtN0, asQtN1⟩ := bd_sQtN h hl
  have asQtN2 := asQtN0.trans asQtN1
  obtain ⟨asCKt0, asCKt1⟩ := bd_sCKt h hl
  have asCKt2 := asCKt0.trans asCKt1
  obtain ⟨asCΩ0, asCΩ1⟩ := bd_sCΩ h hl
  have asCΩ2 := asCΩ0.trans asCΩ1
  have hn1 : (0 : ℝ) ≤ (p.n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast h.n1
    linarith
  have hq1 : 0 < 1 - p.q := by have := h.q1; linarith
  have hq2 : 0 < 1 - p.q ^ 2 := by have := h.q1; have := h.q0; nlinarith
  have hθ1 : 0 < 1 - p.θ := by have := h.θ1; linarith
  unfold Bd sQL
  try simp only [hl.n, hl.κ, hl.r, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.iso]
  have hn1' : (0 : ℝ) ≤ (p.n : ℝ) := by linarith
  obtain ⟨⟩ := h; obtain ⟨⟩ := h'; obtain ⟨⟩ := hl
  refine ⟨?_, ?_⟩ <;> (try split_ifs) <;> first | positivity | gcongr

end KAM.Sharp2

end
