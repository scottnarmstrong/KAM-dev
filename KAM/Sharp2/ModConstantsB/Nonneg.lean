/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModConstantsB.Data

/-!
# Nonnegativity of the `let`s of `stepConstsB`

`nn_X : 0 ≤ X p` on admissible inputs; each proof is a `positivity` closure of the earlier ones.
-/

@[expose] public noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace KAM.Sharp2

theorem nn_sg {p : StepInB} (h : p.Ok) : 0 ≤ sg p := by
  obtain ⟨⟩ := h.flat
  unfold sg
  (try split_ifs) <;> positivity

theorem nn_sg1 {p : StepInB} (h : p.Ok) : 0 ≤ sg1 p := by
  have a_sg := nn_sg h
  obtain ⟨⟩ := h.flat
  unfold sg1
  (try split_ifs) <;> positivity

theorem nn_sKt {p : StepInB} (h : p.Ok) : 0 ≤ sKt p := by
  obtain ⟨⟩ := h.flat
  unfold sKt
  (try split_ifs) <;> positivity

theorem nn_st {p : StepInB} (h : p.Ok) : 0 ≤ st p := by
  obtain ⟨⟩ := h.flat
  unfold st
  (try split_ifs) <;> positivity

theorem nn_saw {p : StepInB} (h : p.Ok) : 0 ≤ saw p := by
  obtain ⟨⟩ := h.flat
  unfold saw
  (try split_ifs) <;> positivity

theorem nn_sCΩ {p : StepInB} (h : p.Ok) : 0 ≤ sCΩ p := by
  obtain ⟨⟩ := h.flat
  unfold sCΩ
  (try split_ifs) <;> positivity

theorem nn_sCEL {p : StepInB} (h : p.Ok) : 0 ≤ sCEL p := by
  obtain ⟨⟩ := h.flat
  unfold sCEL
  (try split_ifs) <;> positivity

theorem nn_sCEN {p : StepInB} (h : p.Ok) : 0 ≤ sCEN p := by
  obtain ⟨⟩ := h.flat
  unfold sCEN
  (try split_ifs) <;> positivity

theorem nn_sCE0 {p : StepInB} (h : p.Ok) : 0 ≤ sCE0 p := by
  have a_sCEL := nn_sCEL h
  have a_sCEN := nn_sCEN h
  have a_sg := nn_sg h
  obtain ⟨⟩ := h.flat
  unfold sCE0
  (try split_ifs) <;> positivity

theorem nn_sCE {p : StepInB} (h : p.Ok) : 0 ≤ sCE p := by
  have a_sCE0 := nn_sCE0 h
  obtain ⟨⟩ := h.flat
  unfold sCE
  (try split_ifs) <;> positivity

theorem nn_sCDE0 {p : StepInB} (h : p.Ok) : 0 ≤ sCDE0 p := by
  have a_sg := nn_sg h
  have a_sCE := nn_sCE h
  obtain ⟨⟩ := h.flat
  unfold sCDE0
  (try split_ifs) <;> positivity

theorem nn_sCDE {p : StepInB} (h : p.Ok) : 0 ≤ sCDE p := by
  have a_sCDE0 := nn_sCDE0 h
  obtain ⟨⟩ := h.flat
  unfold sCDE
  (try split_ifs) <;> positivity

theorem nn_sCNN {p : StepInB} (h : p.Ok) : 0 ≤ sCNN p := by
  have a_sCE := nn_sCE h
  obtain ⟨⟩ := h.flat
  unfold sCNN
  (try split_ifs) <;> positivity

theorem nn_sC0 {p : StepInB} (h : p.Ok) : 0 ≤ sC0 p := by
  have a_st := nn_st h
  obtain ⟨⟩ := h.flat
  unfold sC0
  (try split_ifs) <;> positivity

theorem nn_sCxiN {p : StepInB} (h : p.Ok) : 0 ≤ sCxiN p := by
  have a_sC0 := nn_sC0 h
  obtain ⟨⟩ := h.flat
  unfold sCxiN
  (try split_ifs) <;> positivity

theorem nn_sCKt {p : StepInB} (h : p.Ok) : 0 ≤ sCKt p := by
  have a_sCxiN := nn_sCxiN h
  obtain ⟨⟩ := h.flat
  unfold sCKt
  (try split_ifs) <;> positivity

theorem nn_sCDLt {p : StepInB} (h : p.Ok) : 0 ≤ sCDLt p := by
  have a_sC0 := nn_sC0 h
  obtain ⟨⟩ := h.flat
  unfold sCDLt
  (try split_ifs) <;> positivity

theorem nn_sCDLtT {p : StepInB} (h : p.Ok) : 0 ≤ sCDLtT p := by
  have a_sC0 := nn_sC0 h
  obtain ⟨⟩ := h.flat
  unfold sCDLtT
  (try split_ifs) <;> positivity

theorem nn_sCdN {p : StepInB} (h : p.Ok) : 0 ≤ sCdN p := by
  obtain ⟨⟩ := h.flat
  unfold sCdN
  (try split_ifs) <;> positivity

theorem nn_sCXN {p : StepInB} (h : p.Ok) : 0 ≤ sCXN p := by
  have a_sCdN := nn_sCdN h
  obtain ⟨⟩ := h.flat
  unfold sCXN
  (try split_ifs) <;> positivity

theorem nn_sCEt {p : StepInB} (h : p.Ok) : 0 ≤ sCEt p := by
  have a_sCE := nn_sCE h
  have a_sCXN := nn_sCXN h
  have a_sCxiN := nn_sCxiN h
  have a_sg := nn_sg h
  have a_sCKt := nn_sCKt h
  have a_sKt := nn_sKt h
  have a_sC0 := nn_sC0 h
  obtain ⟨⟩ := h.flat
  unfold sCEt
  (try split_ifs) <;> positivity

theorem nn_sQtN {p : StepInB} (h : p.Ok) : 0 ≤ sQtN p := by
  have a_sCDLtT := nn_sCDLtT h
  have a_sCEt := nn_sCEt h
  have a_sCNN := nn_sCNN h
  have a_sCxiN := nn_sCxiN h
  have a_sCKt := nn_sCKt h
  obtain ⟨⟩ := h.flat
  unfold sQtN
  (try split_ifs) <;> positivity

theorem nn_sCgL {p : StepInB} (h : p.Ok) : 0 ≤ sCgL p := by
  have a_st := nn_st h
  have a_sCxiN := nn_sCxiN h
  have a_sC0 := nn_sC0 h
  obtain ⟨⟩ := h.flat
  unfold sCgL
  (try split_ifs) <;> positivity

theorem nn_sCxiL {p : StepInB} (h : p.Ok) : 0 ≤ sCxiL p := by
  have a_sCgL := nn_sCgL h
  obtain ⟨⟩ := h.flat
  unfold sCxiL
  (try split_ifs) <;> positivity

theorem nn_sCDK {p : StepInB} (h : p.Ok) : 0 ≤ sCDK p := by
  have a_sKt := nn_sKt h
  have a_sCxiL := nn_sCxiL h
  have a_sg := nn_sg h
  have a_sCKt := nn_sCKt h
  obtain ⟨⟩ := h.flat
  unfold sCDK
  (try split_ifs) <;> positivity

theorem nn_sCEb {p : StepInB} (h : p.Ok) : 0 ≤ sCEb p := by
  have a_sCEt := nn_sCEt h
  have a_saw := nn_saw h
  have a_sKt := nn_sKt h
  have a_sCgL := nn_sCgL h
  obtain ⟨⟩ := h.flat
  unfold sCEb
  (try split_ifs) <;> positivity

theorem nn_sCG {p : StepInB} (h : p.Ok) : 0 ≤ sCG p := by
  obtain ⟨⟩ := h.flat
  unfold sCG
  (try split_ifs) <;> positivity

theorem nn_sCBb {p : StepInB} (h : p.Ok) : 0 ≤ sCBb p := by
  have a_sCG := nn_sCG h
  have a_sCDK := nn_sCDK h
  obtain ⟨⟩ := h.flat
  unfold sCBb
  (try split_ifs) <;> positivity

theorem nn_sCNb {p : StepInB} (h : p.Ok) : 0 ≤ sCNb p := by
  have a_sCDK := nn_sCDK h
  have a_sCBb := nn_sCBb h
  obtain ⟨⟩ := h.flat
  unfold sCNb
  (try split_ifs) <;> positivity

theorem nn_sCNbT {p : StepInB} (h : p.Ok) : 0 ≤ sCNbT p := by
  have a_sCBb := nn_sCBb h
  have a_sCDK := nn_sCDK h
  obtain ⟨⟩ := h.flat
  unfold sCNbT
  (try split_ifs) <;> positivity

theorem nn_sw {p : StepInB} (h : p.Ok) : 0 ≤ sw p := by
  obtain ⟨⟩ := h.flat
  unfold sw
  (try split_ifs) <;> positivity

theorem nn_sCab0 {p : StepInB} (h : p.Ok) : 0 ≤ sCab0 p := by
  have a_sCNbT := nn_sCNbT h
  have a_sCNb := nn_sCNb h
  have a_sCDK := nn_sCDK h
  obtain ⟨⟩ := h.flat
  unfold sCab0
  (try split_ifs) <;> positivity

theorem nn_sCab {p : StepInB} (h : p.Ok) : 0 ≤ sCab p := by
  have a_sCab0 := nn_sCab0 h
  have a_sC0 := nn_sC0 h
  have a_sg1 := nn_sg1 h
  obtain ⟨⟩ := h.flat
  unfold sCab
  (try split_ifs) <;> positivity

theorem nn_sBsup {p : StepInB} (h : p.Ok) : 0 ≤ sBsup p := by
  have a_sCDE := nn_sCDE h
  have a_sCΩ := nn_sCΩ h
  have a_sw := nn_sw h
  have a_sg := nn_sg h
  obtain ⟨⟩ := h.flat
  unfold sBsup
  (try split_ifs) <;> positivity

theorem nn_sBloc {p : StepInB} (h : p.Ok) : 0 ≤ sBloc p := by
  have a_sBsup := nn_sBsup h
  have a_sg1 := nn_sg1 h
  obtain ⟨⟩ := h.flat
  unfold sBloc
  (try split_ifs) <;> positivity

theorem nn_sQbN {p : StepInB} (h : p.Ok) : 0 ≤ sQbN p := by
  have a_saw := nn_saw h
  have a_sQtN := nn_sQtN h
  obtain ⟨⟩ := h.flat
  unfold sQbN
  (try split_ifs) <;> positivity

theorem nn_sQL1 {p : StepInB} (h : p.Ok) : 0 ≤ sQL1 p := by
  have a_sCKt := nn_sCKt h
  have a_sg1 := nn_sg1 h
  have a_sCΩ := nn_sCΩ h
  have a_sg := nn_sg h
  have a_sCEt := nn_sCEt h
  have a_sCxiL := nn_sCxiL h
  have a_saw := nn_saw h
  have a_sCgL := nn_sCgL h
  have a_sKt := nn_sKt h
  have a_sCDLt := nn_sCDLt h
  have a_sC0 := nn_sC0 h
  obtain ⟨⟩ := h.flat
  unfold sQL1
  (try split_ifs) <;> positivity

theorem nn_sQLc {p : StepInB} (h : p.Ok) : 0 ≤ sQLc p := by
  have a_sQL1 := nn_sQL1 h
  have a_sCNbT := nn_sCNbT h
  have a_sCEb := nn_sCEb h
  obtain ⟨⟩ := h.flat
  unfold sQLc
  (try split_ifs) <;> positivity

theorem nn_sQLs {p : StepInB} (h : p.Ok) : 0 ≤ sQLs p := by
  have a_sQLc := nn_sQLc h
  have a_sQL1 := nn_sQL1 h
  have a_sCEL := nn_sCEL h
  have a_sCEN := nn_sCEN h
  have a_sQbN := nn_sQbN h
  have a_sg := nn_sg h
  obtain ⟨⟩ := h.flat
  unfold sQLs
  (try split_ifs) <;> positivity

theorem nn_sQw {p : StepInB} (h : p.Ok) : 0 ≤ sQw p := by
  have a_sCKt := nn_sCKt h
  have a_sg1 := nn_sg1 h
  have a_sQtN := nn_sQtN h
  have a_sCΩ := nn_sCΩ h
  obtain ⟨⟩ := h.flat
  unfold sQw
  (try split_ifs) <;> positivity

theorem nn_sQL {p : StepInB} (h : p.Ok) : 0 ≤ sQL p := by
  have a_sQLs := nn_sQLs h
  have a_sQw := nn_sQw h
  obtain ⟨⟩ := h.flat
  unfold sQL
  (try split_ifs) <;> positivity

theorem nn_sQ {p : StepInB} (h : p.Ok) : 0 ≤ sQ p := by
  have a_sQL := nn_sQL h
  have a_sQbN := nn_sQbN h
  obtain ⟨⟩ := h.flat
  unfold sQ
  (try split_ifs) <;> positivity

theorem nn_sCnu {p : StepInB} (h : p.Ok) : 0 ≤ sCnu p := by
  have a_sC0 := nn_sC0 h
  obtain ⟨⟩ := h.flat
  unfold sCnu
  (try split_ifs) <;> positivity

end KAM.Sharp2

end
