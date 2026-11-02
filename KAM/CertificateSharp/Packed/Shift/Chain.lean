/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Shift.Node
public import KAM.CertificateSharp.Packed.JetKeyed

/-!
# Window-sized powers as shifts: segments, characters and the block checks

The segment run of `JetSeg.lean`, the actions of `JetChain.lean`, the character and Taylor blocks of
`JetChar.lean` and `JetStage.lean`, with the shift nodes of `Shift/Node.lean`. The segment, action,
character and Taylor checks equal the landed ones (`…S_eq`). The block checks `JBlockW.okS` and
`JBlockT.okS` return `false` on the `inv` and `sqrt` witness blocks (a program without `inv`, `sqrt`
or `exp`, such as MAG's, never needs them) and imply the landed checks (`JBlockT.okS_ok`), which is
all the chain theorem needs: a generated block proves `okS … = true` by `decide +kernel` and reads
off `ok … = true`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α) (jb : JBook)

/-- `jOp` with shifts. -/
def jOpS (ops : List SlpOp) (base : ℕ) (st : List (ℕ × JNode α)) (i eT : ℕ) : Option (JNode α) :=
  match ops.getD (i - base) (.const 0 0 0) with
  | .add a b =>
    if base ≤ i ∧ a < i ∧ b < i then
      match st.lookup a, st.lookup b with
      | some x, some y => jAddS n jb x y
      | _, _ => none
    else none
  | .mul a b =>
    if base ≤ i ∧ a < i ∧ b < i then
      match st.lookup a, st.lookup b with
      | some x, some y => jMulS n W jb x y eT
      | _, _ => none
    else none
  | .const re im deg =>
    if base ≤ i ∧ i - base < ops.length then
      jLeafS W pe cfg jb true jb.aC (constModel n re im deg)
    else none
  | _ => none

/-- `jPost` with shifts. -/
def jPostS (nd : JNode α) (red : ℕ) : Option (JNode α) :=
  if red = 0 then some nd else jRedS n W jb nd red

/-- `jRun` with shifts. -/
def jRunS (ops : List SlpOp) (base : ℕ) :
    List (ℕ × JNode α) → List JStep → Option (List (ℕ × JNode α))
  | st, [] => some st
  | st, (i, eT, red) :: rest =>
    match jOpS n W pe cfg jb ops base st i eT with
    | some nd =>
      match jPostS n W jb nd red with
      | some nd' => jRunS ops base ((i, nd') :: st) rest
      | none => none
    | none => none

/-- `jSegOk` with shifts. -/
def jSegOkS (p : Slp) (start : ℕ) (imports : List (ℕ × JNode α)) (steps : List JStep)
    (exports : List (ℕ × JNode α)) : Bool :=
  jBookOk n W jb &&
    match jRunS n W pe cfg jb (p.ops.drop start) start imports steps with
    | some st =>
      exports.all fun m =>
        match st.lookup m.1 with
        | some nd => jExportOk nd m.2
        | none => false
    | none => false

/-- `jActionsOk` with shifts. -/
def jActionsOkS (K : CertEmbedding α) (p : Slp) (es : List (ℕ × JNode α)) : Bool :=
  es.all fun m =>
    match p.ops.getD m.1 (.const 0 0 0) with
    | .action j =>
      decide (m.1 < p.ops.length) &&
        match jLeafS W pe cfg jb false m.2.A (actionModel n K j) with
        | some nd => jExportOk nd m.2
        | none => false
    | _ => false

/-- `JBlock.ok` with shifts. -/
def JBlock.okS (K : CertEmbedding α) (p : Slp) : JBlock α → Bool
  | .seg start i s e => jSegOkS n W pe cfg jb p start i s e
  | .actions e => jActionsOkS n W pe cfg jb K p e
  | .given _ => true

/-- `jNorm` with shifts. -/
def jNormS (nd : JNode α) : Option (JNode α) :=
  if jb.P < nd.e then jRedS n W jb nd jb.P else some nd

/-- `jConstQ` with shifts. -/
def jConstQS (q : ℚ) : Option (JNode α) := jLeafS W pe cfg jb true jb.aC (constModel n q 0 0)

/-- `jW` with shifts. -/
def jWS (K : CertEmbedding α) (j : ℕ) (neg : Bool) : Option (JNode α) :=
  match jLeafS W pe cfg jb false (2 ^ jb.lb) (angleModel n K j),
      jLeafS W pe cfg jb true jb.aC (constModel n 0 (if neg then -1 else 1) 1) with
  | some A, some c =>
    match jMulS n W jb c A jb.P with
    | some m => jNormS n W jb m
    | none => none
  | _, _ => none

/-- `jTaylor` with shifts. -/
def jTaylorS (w : JNode α) : ℕ → Option (JNode α × JNode α)
  | 0 =>
    match jConstQS n W pe cfg jb 1 with
    | some o => some (o, o)
    | none => none
  | m + 1 =>
    match jTaylorS w m with
    | some (t, s) =>
      match jMulS n W jb t w jb.P with
      | some t1 =>
        match jNormS n W jb t1, jConstQS n W pe cfg jb (1 / ((m : ℚ) + 1)) with
        | some t2, some c =>
          match jMulS n W jb t2 c jb.P with
          | some t3 =>
            match jNormS n W jb t3 with
            | some t4 =>
              match jAddS n jb s t4 with
              | some s' => some (t4, s')
              | none => none
            | none => none
          | none => none
        | _, _ => none
      | none => none
    | none => none

/-- `jExpNode` with shifts. -/
def jExpNodeS (K : CertEmbedding α) (j : ℕ) (neg : Bool) (N : ℕ) : Option (JNode α) :=
  match jWS n W pe cfg jb K j neg with
  | some w =>
    match jTaylorS n W pe cfg jb w N, jExpRem w N with
    | some (_, s), some rem => some ⟨s.u, s.A, s.e, s.x, upAdd s.r rem, s.nb⟩
    | _, _ => none
  | none => none

/-- `jPowsAux` with shifts. -/
def jPowsAuxS (base : JNode α) : JNode α → List (JNode α) → Bool
  | _, [] => true
  | cur, o :: os =>
    match jMulS n W jb cur base jb.P with
    | some c =>
      match jNormS n W jb c with
      | some c' => jExportOk c' o && jPowsAuxS base o os
      | none => false
    | none => false

/-- `jFactor` with shifts. -/
def jFactorS (facs : List (JKey × JNode α)) (k : CertKey) (i : ℕ) : Option (JNode α) :=
  if k.getD i 0 = 0 then jConstQS n W pe cfg jb 1
  else facs.lookup (.inr (i, decide (k.getD i 0 < 0), (k.getD i 0).natAbs))

/-- `jCharProd` with shifts. -/
def jCharProdS (facs : List (JKey × JNode α)) (k : CertKey) : ℕ → Option (JNode α)
  | 0 => jLeafS W pe cfg jb false (2 ^ jb.lb) (unitModel n k)
  | m + 1 =>
    match jCharProdS facs k m, jFactorS n W pe cfg jb facs k m with
    | some a, some f =>
      match jMulS n W jb a f jb.P with
      | some c => jNormS n W jb c
      | none => none
    | _, _ => none

/-- `jCharsOk` with shifts. -/
def jCharsOkS (p : Slp) (facs : List (JKey × JNode α)) (es : List (ℕ × JNode α)) : Bool :=
  es.all fun m =>
    match p.ops.getD m.1 (.const 0 0 0) with
    | .char k =>
      decide (m.1 < p.ops.length) &&
        match jCharProdS n W pe cfg jb facs k n with
        | some nd => jExportOk nd m.2
        | none => false
    | _ => false

/-- `JBlockX.ok` with shifts. -/
def JBlockX.okS (K : CertEmbedding α) (p : Slp) : JBlockX α → Bool
  | .base b => b.okS n W pe cfg jb K p
  | .expo j neg N out =>
    match jExpNodeS n W pe cfg jb K j neg N with
    | some e => jExportOk e out
    | none => false
  | .pows _ _ b0 outs => jPowsAuxS n W jb b0 b0 outs
  | .chars facs es => jCharsOkS n W pe cfg jb p facs es

/-- `JBlockW.ok` with shifts on the character blocks; `false` on the `inv` and `sqrt` blocks. -/
def JBlockW.okS (K : CertEmbedding α) (p : Slp) : JBlockW α → Bool
  | .x b => b.okS n W pe cfg jb K p
  | .inv .. => false
  | .sqrt .. => false

/-- `jTStep` with shifts. -/
def jTStepS (w : JNode α) (m : ℕ) (t s : JNode α) : Option (JNode α × JNode α) :=
  match jMulS n W jb t w jb.P with
  | some t1 =>
    match jNormS n W jb t1, jConstQS n W pe cfg jb (1 / ((m : ℚ) + 1)) with
    | some t2, some c =>
      match jMulS n W jb t2 c jb.P with
      | some t3 =>
        match jNormS n W jb t3 with
        | some t4 =>
          match jAddS n jb s t4 with
          | some s' => some (t4, s')
          | none => none
        | none => none
      | none => none
    | _, _ => none
  | none => none

/-- `jTSteps` with shifts. -/
def jTStepsS (w : JNode α) : ℕ → ℕ → JNode α → JNode α → Option (JNode α × JNode α)
  | _, 0, t, s => some (t, s)
  | m, k + 1, t, s =>
    match jTStepS n W pe cfg jb w m t s with
    | some (t', s') => jTStepsS w (m + 1) k t' s'
    | none => none

/-- `JBlockT.ok` with shifts (`false` on the `inv` and `sqrt` blocks). -/
def JBlockT.okS (K : CertEmbedding α) (p : Slp) : JBlockT α → Bool
  | .lift b => b.okS n W pe cfg jb K p
  | .tstart j neg wo one =>
    (match jWS n W pe cfg jb K j neg with
      | some x => jExportOk x wo
      | none => false) &&
    (match jConstQS n W pe cfg jb 1 with
      | some o => jExportOk o one
      | none => false)
  | .tstep _ _ m k w t s t' s' =>
    match jTStepsS n W pe cfg jb w m k t s with
    | some (t1, s1) => jExportOk t1 t' && jExportOk s1 s'
    | none => false
  | .texp _ _ N w s out =>
    match jExpFin w s N with
    | some e => jExportOk e out
    | none => false
  | .pows _ _ _ base cur outs => jPowsAuxS n W jb base cur outs

end Defs

section Eq

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α) (jb : JBook)

theorem jOpS_eq (ops : List SlpOp) (base : ℕ) (st : List (ℕ × JNode α)) (i eT : ℕ) :
    jOpS n W pe cfg jb ops base st i eT = jOp n W pe cfg jb ops base st i eT := by
  simp only [jOpS, jOp, jAddS_eq, jMulS_eq, jLeafS_eq] <;> rfl

theorem jPostS_eq (nd : JNode α) (red : ℕ) : jPostS n W jb nd red = jPost n W jb nd red := by
  simp only [jPostS, jPost, jRedS_eq] <;> rfl

theorem jRunS_eq (ops : List SlpOp) (base : ℕ) :
    ∀ (st : List (ℕ × JNode α)) (steps : List JStep),
      jRunS n W pe cfg jb ops base st steps = jRun n W pe cfg jb ops base st steps
  | _, [] => rfl
  | st, (i, eT, red) :: rest => by
    simp only [jRunS, jRun, jOpS_eq, jPostS_eq, jRunS_eq ops base _ rest] <;> rfl

theorem jSegOkS_eq (p : Slp) (start : ℕ) (imports : List (ℕ × JNode α)) (steps : List JStep)
    (exports : List (ℕ × JNode α)) :
    jSegOkS n W pe cfg jb p start imports steps exports =
      jSegOk n W pe cfg jb p start imports steps exports := by
  simp only [jSegOkS, jSegOk, jRunS_eq] <;> rfl

theorem jActionsOkS_eq (K : CertEmbedding α) (p : Slp) (es : List (ℕ × JNode α)) :
    jActionsOkS n W pe cfg jb K p es = jActionsOk n W pe cfg jb K p es := by
  simp only [jActionsOkS, jActionsOk, jLeafS_eq] <;> rfl

theorem JBlock.okS_eq (K : CertEmbedding α) (p : Slp) (b : JBlock α) :
    b.okS n W pe cfg jb K p = b.ok n W pe cfg jb K p := by
  cases b <;> simp only [JBlock.okS, JBlock.ok, jSegOkS_eq, jActionsOkS_eq] <;> rfl

theorem jNormS_eq (nd : JNode α) : jNormS n W jb nd = jNorm n W jb nd := by
  simp only [jNormS, jNorm, jRedS_eq] <;> rfl

theorem jConstQS_eq (q : ℚ) : jConstQS n W pe cfg jb q = jConstQ n W pe cfg jb q := by
  simp only [jConstQS, jConstQ, jLeafS_eq] <;> rfl

theorem jWS_eq (K : CertEmbedding α) (j : ℕ) (neg : Bool) :
    jWS n W pe cfg jb K j neg = jW n W pe cfg jb K j neg := by
  simp only [jWS, jW, jLeafS_eq, jMulS_eq, jNormS_eq] <;> rfl

theorem jTaylorS_eq (w : JNode α) : ∀ m, jTaylorS n W pe cfg jb w m = jTaylor n W pe cfg jb w m
  | 0 => by simp only [jTaylorS, jTaylor, jConstQS_eq] <;> rfl
  | m + 1 => by
    simp only [jTaylorS, jTaylor, jTaylorS_eq w m, jMulS_eq, jNormS_eq, jConstQS_eq,
      jAddS_eq] <;> rfl

theorem jExpNodeS_eq (K : CertEmbedding α) (j : ℕ) (neg : Bool) (N : ℕ) :
    jExpNodeS n W pe cfg jb K j neg N = jExpNode n W pe cfg jb K j neg N := by
  simp only [jExpNodeS, jExpNode, jWS_eq, jTaylorS_eq] <;> rfl

theorem jPowsAuxS_eq (base : JNode α) :
    ∀ (cur : JNode α) (os : List (JNode α)),
      jPowsAuxS n W jb base cur os = jPowsAux n W jb base cur os
  | _, [] => rfl
  | cur, o :: os => by
    simp only [jPowsAuxS, jPowsAux, jMulS_eq, jNormS_eq, jPowsAuxS_eq base o os] <;> rfl

theorem jFactorS_eq (facs : List (JKey × JNode α)) (k : CertKey) (i : ℕ) :
    jFactorS n W pe cfg jb facs k i = jFactor n W pe cfg jb facs k i := by
  simp only [jFactorS, jFactor, jConstQS_eq] <;> rfl

theorem jCharProdS_eq (facs : List (JKey × JNode α)) (k : CertKey) :
    ∀ m, jCharProdS n W pe cfg jb facs k m = jCharProd n W pe cfg jb facs k m
  | 0 => by simp only [jCharProdS, jCharProd, jLeafS_eq] <;> rfl
  | m + 1 => by
    simp only [jCharProdS, jCharProd, jCharProdS_eq facs k m, jFactorS_eq, jMulS_eq,
      jNormS_eq] <;> rfl

theorem jCharsOkS_eq (p : Slp) (facs : List (JKey × JNode α)) (es : List (ℕ × JNode α)) :
    jCharsOkS n W pe cfg jb p facs es = jCharsOk n W pe cfg jb p facs es := by
  simp only [jCharsOkS, jCharsOk, jCharProdS_eq] <;> rfl

theorem JBlockX.okS_eq (K : CertEmbedding α) (p : Slp) (b : JBlockX α) :
    b.okS n W pe cfg jb K p = b.ok n W pe cfg jb K p := by
  cases b <;> simp only [JBlockX.okS, JBlockX.ok, JBlock.okS_eq, jExpNodeS_eq, jPowsAuxS_eq,
    jCharsOkS_eq] <;> rfl

theorem JBlockW.okS_ok (K : CertEmbedding α) (p : Slp) (b : JBlockW α)
    (h : b.okS n W pe cfg jb K p = true) : b.ok n W pe cfg jb K p = true := by
  cases b with
  | x b =>
    simp only [JBlockW.okS, JBlockX.okS_eq] at h
    exact h
  | inv => simp [JBlockW.okS] at h
  | sqrt => simp [JBlockW.okS] at h

theorem jTStepS_eq (w : JNode α) (m : ℕ) (t s : JNode α) :
    jTStepS n W pe cfg jb w m t s = jTStep n W pe cfg jb w m t s := by
  simp only [jTStepS, jTStep, jMulS_eq, jNormS_eq, jConstQS_eq, jAddS_eq] <;> rfl

theorem jTStepsS_eq (w : JNode α) :
    ∀ (m k : ℕ) (t s : JNode α), jTStepsS n W pe cfg jb w m k t s = jTSteps n W pe cfg jb w m k t s
  | _, 0, _, _ => rfl
  | m, k + 1, t, s => by
    simp only [jTStepsS, jTSteps, jTStepS_eq, jTStepsS_eq w (m + 1) k] <;> rfl

theorem JBlockT.okS_ok (K : CertEmbedding α) (p : Slp) (b : JBlockT α)
    (h : b.okS n W pe cfg jb K p = true) : b.ok n W pe cfg jb K p = true := by
  cases b with
  | lift b => exact JBlockW.okS_ok n W pe cfg jb K p b (by simpa only [JBlockT.okS] using h)
  | tstart =>
    simp only [JBlockT.okS, jWS_eq, jConstQS_eq] at h
    exact h
  | tstep =>
    simp only [JBlockT.okS, jTStepsS_eq] at h
    exact h
  | texp => exact h
  | pows =>
    simp only [JBlockT.okS, jPowsAuxS_eq] at h
    exact h

end Eq

end KAM.CertificateSharp.Packed
