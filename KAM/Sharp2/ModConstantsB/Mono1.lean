/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModConstantsB.Nonneg

/-!
# Monotonicity of the `let`s of `stepConstsB` (1/2)

`mo_X : X p ≤ X p'` for `p.Le p'` (`StepInB.Dom`) on admissible inputs; every proof is a
`gcongr` closure of the earlier ones.
-/

@[expose] public noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace KAM.Sharp2

theorem mo_sg {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sg p ≤ sg p' := by
  unfold sg
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sg1 {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sg1 p ≤ sg1 p' := by
  have a_sg := nn_sg h
  have a'_sg := nn_sg h'
  have b_sg := mo_sg h h' hl
  unfold sg1
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sKt {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sKt p ≤ sKt p' := by
  unfold sKt
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_st {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    st p ≤ st p' := by
  unfold st
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_saw {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    saw p ≤ saw p' := by
  unfold saw
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCΩ {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCΩ p ≤ sCΩ p' := by
  unfold sCΩ
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCEL {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCEL p ≤ sCEL p' := by
  unfold sCEL
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCEN {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCEN p ≤ sCEN p' := by
  unfold sCEN
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCE0 {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCE0 p ≤ sCE0 p' := by
  have a_sCEL := nn_sCEL h
  have a'_sCEL := nn_sCEL h'
  have b_sCEL := mo_sCEL h h' hl
  have a_sCEN := nn_sCEN h
  have a'_sCEN := nn_sCEN h'
  have b_sCEN := mo_sCEN h h' hl
  have a_sg := nn_sg h
  have a'_sg := nn_sg h'
  have b_sg := mo_sg h h' hl
  unfold sCE0
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCE {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCE p ≤ sCE p' := by
  have a_sCE0 := nn_sCE0 h
  have a'_sCE0 := nn_sCE0 h'
  have b_sCE0 := mo_sCE0 h h' hl
  unfold sCE
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCDE0 {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCDE0 p ≤ sCDE0 p' := by
  have a_sg := nn_sg h
  have a'_sg := nn_sg h'
  have b_sg := mo_sg h h' hl
  have a_sCE := nn_sCE h
  have a'_sCE := nn_sCE h'
  have b_sCE := mo_sCE h h' hl
  unfold sCDE0
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCDE {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCDE p ≤ sCDE p' := by
  have a_sCDE0 := nn_sCDE0 h
  have a'_sCDE0 := nn_sCDE0 h'
  have b_sCDE0 := mo_sCDE0 h h' hl
  unfold sCDE
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCNN {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCNN p ≤ sCNN p' := by
  have a_sCE := nn_sCE h
  have a'_sCE := nn_sCE h'
  have b_sCE := mo_sCE h h' hl
  unfold sCNN
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sC0 {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sC0 p ≤ sC0 p' := by
  have a_st := nn_st h
  have a'_st := nn_st h'
  have b_st := mo_st h h' hl
  unfold sC0
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCxiN {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCxiN p ≤ sCxiN p' := by
  have a_sC0 := nn_sC0 h
  have a'_sC0 := nn_sC0 h'
  have b_sC0 := mo_sC0 h h' hl
  unfold sCxiN
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCKt {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCKt p ≤ sCKt p' := by
  have a_sCxiN := nn_sCxiN h
  have a'_sCxiN := nn_sCxiN h'
  have b_sCxiN := mo_sCxiN h h' hl
  unfold sCKt
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCDLt {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCDLt p ≤ sCDLt p' := by
  have a_sC0 := nn_sC0 h
  have a'_sC0 := nn_sC0 h'
  have b_sC0 := mo_sC0 h h' hl
  unfold sCDLt
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCDLtT {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCDLtT p ≤ sCDLtT p' := by
  have a_sC0 := nn_sC0 h
  have a'_sC0 := nn_sC0 h'
  have b_sC0 := mo_sC0 h h' hl
  unfold sCDLtT
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCdN {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCdN p ≤ sCdN p' := by
  unfold sCdN
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCXN {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCXN p ≤ sCXN p' := by
  have a_sCdN := nn_sCdN h
  have a'_sCdN := nn_sCdN h'
  have b_sCdN := mo_sCdN h h' hl
  unfold sCXN
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCEt {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCEt p ≤ sCEt p' := by
  have a_sCE := nn_sCE h
  have a'_sCE := nn_sCE h'
  have b_sCE := mo_sCE h h' hl
  have a_sCXN := nn_sCXN h
  have a'_sCXN := nn_sCXN h'
  have b_sCXN := mo_sCXN h h' hl
  have a_sCxiN := nn_sCxiN h
  have a'_sCxiN := nn_sCxiN h'
  have b_sCxiN := mo_sCxiN h h' hl
  have a_sg := nn_sg h
  have a'_sg := nn_sg h'
  have b_sg := mo_sg h h' hl
  have a_sCKt := nn_sCKt h
  have a'_sCKt := nn_sCKt h'
  have b_sCKt := mo_sCKt h h' hl
  have a_sKt := nn_sKt h
  have a'_sKt := nn_sKt h'
  have b_sKt := mo_sKt h h' hl
  have a_sC0 := nn_sC0 h
  have a'_sC0 := nn_sC0 h'
  have b_sC0 := mo_sC0 h h' hl
  unfold sCEt
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

end KAM.Sharp2

end
