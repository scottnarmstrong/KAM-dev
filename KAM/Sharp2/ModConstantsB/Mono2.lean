/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModConstantsB.Mono1

/-!
# Monotonicity of the `let`s of `stepConstsB` (2/2)

`mo_X : X p ≤ X p'` for `p.Le p'` (`StepInB.Dom`) on admissible inputs; every proof is a
`gcongr` closure of the earlier ones.
-/

@[expose] public noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace KAM.Sharp2

theorem mo_sQtN {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sQtN p ≤ sQtN p' := by
  have a_sCDLtT := nn_sCDLtT h
  have a'_sCDLtT := nn_sCDLtT h'
  have b_sCDLtT := mo_sCDLtT h h' hl
  have a_sCEt := nn_sCEt h
  have a'_sCEt := nn_sCEt h'
  have b_sCEt := mo_sCEt h h' hl
  have a_sCNN := nn_sCNN h
  have a'_sCNN := nn_sCNN h'
  have b_sCNN := mo_sCNN h h' hl
  have a_sCxiN := nn_sCxiN h
  have a'_sCxiN := nn_sCxiN h'
  have b_sCxiN := mo_sCxiN h h' hl
  have a_sCKt := nn_sCKt h
  have a'_sCKt := nn_sCKt h'
  have b_sCKt := mo_sCKt h h' hl
  unfold sQtN
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCgL {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCgL p ≤ sCgL p' := by
  have a_st := nn_st h
  have a'_st := nn_st h'
  have b_st := mo_st h h' hl
  have a_sCxiN := nn_sCxiN h
  have a'_sCxiN := nn_sCxiN h'
  have b_sCxiN := mo_sCxiN h h' hl
  have a_sC0 := nn_sC0 h
  have a'_sC0 := nn_sC0 h'
  have b_sC0 := mo_sC0 h h' hl
  unfold sCgL
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCxiL {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCxiL p ≤ sCxiL p' := by
  have a_sCgL := nn_sCgL h
  have a'_sCgL := nn_sCgL h'
  have b_sCgL := mo_sCgL h h' hl
  unfold sCxiL
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCDK {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCDK p ≤ sCDK p' := by
  have a_sKt := nn_sKt h
  have a'_sKt := nn_sKt h'
  have b_sKt := mo_sKt h h' hl
  have a_sCxiL := nn_sCxiL h
  have a'_sCxiL := nn_sCxiL h'
  have b_sCxiL := mo_sCxiL h h' hl
  have a_sg := nn_sg h
  have a'_sg := nn_sg h'
  have b_sg := mo_sg h h' hl
  have a_sCKt := nn_sCKt h
  have a'_sCKt := nn_sCKt h'
  have b_sCKt := mo_sCKt h h' hl
  unfold sCDK
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCEb {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCEb p ≤ sCEb p' := by
  have a_sCEt := nn_sCEt h
  have a'_sCEt := nn_sCEt h'
  have b_sCEt := mo_sCEt h h' hl
  have a_saw := nn_saw h
  have a'_saw := nn_saw h'
  have b_saw := mo_saw h h' hl
  have a_sKt := nn_sKt h
  have a'_sKt := nn_sKt h'
  have b_sKt := mo_sKt h h' hl
  have a_sCgL := nn_sCgL h
  have a'_sCgL := nn_sCgL h'
  have b_sCgL := mo_sCgL h h' hl
  unfold sCEb
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCG {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCG p ≤ sCG p' := by
  unfold sCG
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCBb {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCBb p ≤ sCBb p' := by
  have a_sCG := nn_sCG h
  have a'_sCG := nn_sCG h'
  have b_sCG := mo_sCG h h' hl
  have a_sCDK := nn_sCDK h
  have a'_sCDK := nn_sCDK h'
  have b_sCDK := mo_sCDK h h' hl
  unfold sCBb
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCNb {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCNb p ≤ sCNb p' := by
  have a_sCDK := nn_sCDK h
  have a'_sCDK := nn_sCDK h'
  have b_sCDK := mo_sCDK h h' hl
  have a_sCBb := nn_sCBb h
  have a'_sCBb := nn_sCBb h'
  have b_sCBb := mo_sCBb h h' hl
  unfold sCNb
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCNbT {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCNbT p ≤ sCNbT p' := by
  have a_sCBb := nn_sCBb h
  have a'_sCBb := nn_sCBb h'
  have b_sCBb := mo_sCBb h h' hl
  have a_sCDK := nn_sCDK h
  have a'_sCDK := nn_sCDK h'
  have b_sCDK := mo_sCDK h h' hl
  unfold sCNbT
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sw {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sw p ≤ sw p' := by
  unfold sw
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCab0 {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCab0 p ≤ sCab0 p' := by
  have a_sCNbT := nn_sCNbT h
  have a'_sCNbT := nn_sCNbT h'
  have b_sCNbT := mo_sCNbT h h' hl
  have a_sCNb := nn_sCNb h
  have a'_sCNb := nn_sCNb h'
  have b_sCNb := mo_sCNb h h' hl
  have a_sCDK := nn_sCDK h
  have a'_sCDK := nn_sCDK h'
  have b_sCDK := mo_sCDK h h' hl
  unfold sCab0
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCab {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCab p ≤ sCab p' := by
  have a_sCab0 := nn_sCab0 h
  have a'_sCab0 := nn_sCab0 h'
  have b_sCab0 := mo_sCab0 h h' hl
  have a_sC0 := nn_sC0 h
  have a'_sC0 := nn_sC0 h'
  have b_sC0 := mo_sC0 h h' hl
  have a_sg1 := nn_sg1 h
  have a'_sg1 := nn_sg1 h'
  have b_sg1 := mo_sg1 h h' hl
  unfold sCab
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sBsup {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sBsup p ≤ sBsup p' := by
  have a_sCDE := nn_sCDE h
  have a'_sCDE := nn_sCDE h'
  have b_sCDE := mo_sCDE h h' hl
  have a_sCΩ := nn_sCΩ h
  have a'_sCΩ := nn_sCΩ h'
  have b_sCΩ := mo_sCΩ h h' hl
  have a_sw := nn_sw h
  have a'_sw := nn_sw h'
  have b_sw := mo_sw h h' hl
  have a_sg := nn_sg h
  have a'_sg := nn_sg h'
  have b_sg := mo_sg h h' hl
  unfold sBsup
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sBloc {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sBloc p ≤ sBloc p' := by
  have a_sBsup := nn_sBsup h
  have a'_sBsup := nn_sBsup h'
  have b_sBsup := mo_sBsup h h' hl
  have a_sg1 := nn_sg1 h
  have a'_sg1 := nn_sg1 h'
  have b_sg1 := mo_sg1 h h' hl
  unfold sBloc
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sQbN {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sQbN p ≤ sQbN p' := by
  have a_saw := nn_saw h
  have a'_saw := nn_saw h'
  have b_saw := mo_saw h h' hl
  have a_sQtN := nn_sQtN h
  have a'_sQtN := nn_sQtN h'
  have b_sQtN := mo_sQtN h h' hl
  unfold sQbN
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sQL1 {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sQL1 p ≤ sQL1 p' := by
  have a_sCKt := nn_sCKt h
  have a'_sCKt := nn_sCKt h'
  have b_sCKt := mo_sCKt h h' hl
  have a_sg1 := nn_sg1 h
  have a'_sg1 := nn_sg1 h'
  have b_sg1 := mo_sg1 h h' hl
  have a_sCΩ := nn_sCΩ h
  have a'_sCΩ := nn_sCΩ h'
  have b_sCΩ := mo_sCΩ h h' hl
  have a_sg := nn_sg h
  have a'_sg := nn_sg h'
  have b_sg := mo_sg h h' hl
  have a_sCEt := nn_sCEt h
  have a'_sCEt := nn_sCEt h'
  have b_sCEt := mo_sCEt h h' hl
  have a_sCxiL := nn_sCxiL h
  have a'_sCxiL := nn_sCxiL h'
  have b_sCxiL := mo_sCxiL h h' hl
  have a_saw := nn_saw h
  have a'_saw := nn_saw h'
  have b_saw := mo_saw h h' hl
  have a_sCgL := nn_sCgL h
  have a'_sCgL := nn_sCgL h'
  have b_sCgL := mo_sCgL h h' hl
  have a_sKt := nn_sKt h
  have a'_sKt := nn_sKt h'
  have b_sKt := mo_sKt h h' hl
  have a_sCDLt := nn_sCDLt h
  have a'_sCDLt := nn_sCDLt h'
  have b_sCDLt := mo_sCDLt h h' hl
  have a_sC0 := nn_sC0 h
  have a'_sC0 := nn_sC0 h'
  have b_sC0 := mo_sC0 h h' hl
  unfold sQL1
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sQLc {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sQLc p ≤ sQLc p' := by
  have a_sQL1 := nn_sQL1 h
  have a'_sQL1 := nn_sQL1 h'
  have b_sQL1 := mo_sQL1 h h' hl
  have a_sCNbT := nn_sCNbT h
  have a'_sCNbT := nn_sCNbT h'
  have b_sCNbT := mo_sCNbT h h' hl
  have a_sCEb := nn_sCEb h
  have a'_sCEb := nn_sCEb h'
  have b_sCEb := mo_sCEb h h' hl
  unfold sQLc
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sQLs {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sQLs p ≤ sQLs p' := by
  have a_sQLc := nn_sQLc h
  have a'_sQLc := nn_sQLc h'
  have b_sQLc := mo_sQLc h h' hl
  have a_sQL1 := nn_sQL1 h
  have a'_sQL1 := nn_sQL1 h'
  have b_sQL1 := mo_sQL1 h h' hl
  have a_sCEL := nn_sCEL h
  have a'_sCEL := nn_sCEL h'
  have b_sCEL := mo_sCEL h h' hl
  have a_sCEN := nn_sCEN h
  have a'_sCEN := nn_sCEN h'
  have b_sCEN := mo_sCEN h h' hl
  have a_sQbN := nn_sQbN h
  have a'_sQbN := nn_sQbN h'
  have b_sQbN := mo_sQbN h h' hl
  have a_sg := nn_sg h
  have a'_sg := nn_sg h'
  have b_sg := mo_sg h h' hl
  unfold sQLs
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte,
    sCEL_eq hl, sCEN_eq hl]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sQw {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sQw p ≤ sQw p' := by
  have a_sCKt := nn_sCKt h
  have a'_sCKt := nn_sCKt h'
  have b_sCKt := mo_sCKt h h' hl
  have a_sg1 := nn_sg1 h
  have a'_sg1 := nn_sg1 h'
  have b_sg1 := mo_sg1 h h' hl
  have a_sQtN := nn_sQtN h
  have a'_sQtN := nn_sQtN h'
  have b_sQtN := mo_sQtN h h' hl
  have a_sCΩ := nn_sCΩ h
  have a'_sCΩ := nn_sCΩ h'
  have b_sCΩ := mo_sCΩ h h' hl
  unfold sQw
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sQL {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sQL p ≤ sQL p' := by
  have a_sQLs := nn_sQLs h
  have a'_sQLs := nn_sQLs h'
  have b_sQLs := mo_sQLs h h' hl
  have a_sQw := nn_sQw h
  have a'_sQw := nn_sQw h'
  have b_sQw := mo_sQw h h' hl
  unfold sQL
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sQ {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sQ p ≤ sQ p' := by
  have a_sQL := nn_sQL h
  have a'_sQL := nn_sQL h'
  have b_sQL := mo_sQL h h' hl
  have a_sQbN := nn_sQbN h
  have a'_sQbN := nn_sQbN h'
  have b_sQbN := mo_sQbN h h' hl
  unfold sQ
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

theorem mo_sCnu {p p' : StepInB} (h : p.Ok) (h' : p'.Ok) (hl : p.Le p') :
    sCnu p ≤ sCnu p' := by
  have a_sC0 := nn_sC0 h
  have a'_sC0 := nn_sC0 h'
  have b_sC0 := mo_sC0 h h' hl
  unfold sCnu
  try simp only [hl.n, hl.κ, hl.M1, hl.M2, hl.cTh, hl.cDTh, hl.sK, hl.sLt, hl.sB, hl.sN, hl.sNt,
    hl.sT, hl.ts, hl.bF, hl.θ, hl.θξ, hl.θΩ, hl.q, hl.θN, hl.θω, hl.a, hl.γb, hl.selfcons,
    hl.iso, hl.Θ, hl.y0, hl.Mh2, hl.s0, hl.s0', Bool.false_eq_true, ↓reduceIte]
  obtain ⟨⟩ := h.flat
  obtain ⟨⟩ := h'.flat
  obtain ⟨⟩ := hl
  (try split_ifs) <;> first | positivity | gcongr

end KAM.Sharp2

end
