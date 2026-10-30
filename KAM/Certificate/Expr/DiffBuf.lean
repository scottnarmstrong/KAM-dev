/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.DiffCompile

/-!
# The kernel-friendly jet compiler

The specification compiler `slpCompile` appends every operation to the program (`s ++ [op]`) and
reads the new slot as `s.length`. Evaluated by the kernel, the program of a large expression is then
a left-nested chain of appends, one per operation, and reading its first operation (or its length)
recurses through the whole chain: on a program of a few thousand operations the kernel reports deep
recursion.

`slpCompileB` is the same compiler on a buffer `SlpBuf`: the operations in reverse order (an
emission is a cons) and the length (a slot is read from it). Every builder of `DiffBuild`,
`DiffNode`, `DiffNodeSqrt` and `DiffCompile` has a buffer twin (suffix `B`) with the same
structure, and the twin runs the builder exactly: on the buffer of a program `s` it returns the
buffer of the program of the builder and the same slots (`slpCompileB_ofOpList`). So the compiled
program, its slot numbers and its tables are identical.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM

variable {n : ℕ}

/-- A program under construction: its operations in reverse order and its length. Emitting an
operation is a cons, so the program is never a nest of appends. -/
structure SlpBuf where
  rev : List SlpOp
  len : ℕ

/-- The buffer of a program. -/
def SlpBuf.ofOpList (s : List SlpOp) : SlpBuf := ⟨s.reverse, s.length⟩

/-- The program of a buffer. -/
def SlpBuf.opList (b : SlpBuf) : List SlpOp := b.rev.reverse

theorem SlpBuf.opList_ofOpList (s : List SlpOp) : (SlpBuf.ofOpList s).opList = s := by
  simp [SlpBuf.ofOpList, SlpBuf.opList]

theorem SlpBuf.len_ofOpList (s : List SlpOp) : (SlpBuf.ofOpList s).len = s.length := rfl

/-- The buffer twin `G` runs the builder `F`: on the buffer of every program it returns the buffer
of the program of `F` and the same result. -/
def SlpSim {α : Type} (F : List SlpOp → List SlpOp × α) (G : SlpBuf → SlpBuf × α) : Prop :=
  ∀ s, G (SlpBuf.ofOpList s) = (SlpBuf.ofOpList (F s).1, (F s).2)

/-! ### Emission and slot arithmetic -/

/-- Append one operation; the result is its slot. -/
def slpEmitB (b : SlpBuf) (op : SlpOp) : SlpBuf × Option ℕ :=
  (⟨op :: b.rev, b.len + 1⟩, some b.len)

theorem slpEmitB_ofOpList (s : List SlpOp) (op : SlpOp) :
    slpEmitB (SlpBuf.ofOpList s) op = (SlpBuf.ofOpList (s ++ [op]), some s.length) := by
  simp [slpEmitB, SlpBuf.ofOpList]

theorem slpEmitB_ofOpList_fst (s : List SlpOp) (op : SlpOp) :
    (slpEmitB (SlpBuf.ofOpList s) op).1 = SlpBuf.ofOpList (s ++ [op]) := by
  rw [slpEmitB_ofOpList]

/-- Sum of two slots (`slpAddO`). -/
def slpAddOB (b : SlpBuf) : Option ℕ → Option ℕ → SlpBuf × Option ℕ
  | none, y => (b, y)
  | some a, none => (b, some a)
  | some a, some c => slpEmitB b (.add a c)

/-- Product of two slots (`slpMulO`). -/
def slpMulOB (b : SlpBuf) : Option ℕ → Option ℕ → SlpBuf × Option ℕ
  | some a, some c => slpEmitB b (.mul a c)
  | _, _ => (b, none)

/-- A constant times a slot (`slpScaleO`). -/
def slpScaleOB (b : SlpBuf) (re im : ℚ) (deg : ℤ) : Option ℕ → SlpBuf × Option ℕ
  | none => (b, none)
  | some x =>
    if re = 0 ∧ im = 0 then (b, none)
    else slpMulOB (slpEmitB b (.const re im deg)).1 (slpEmitB b (.const re im deg)).2 (some x)

theorem slpAddOB_ofOpList (s : List SlpOp) (x y : Option ℕ) :
    slpAddOB (SlpBuf.ofOpList s) x y = (SlpBuf.ofOpList (slpAddO s x y).1, (slpAddO s x y).2) := by
  cases x <;> cases y <;> simp [slpAddOB, slpAddO, slpEmit, slpEmitB_ofOpList]

theorem slpMulOB_ofOpList (s : List SlpOp) (x y : Option ℕ) :
    slpMulOB (SlpBuf.ofOpList s) x y = (SlpBuf.ofOpList (slpMulO s x y).1, (slpMulO s x y).2) := by
  cases x <;> cases y <;> simp [slpMulOB, slpMulO, slpEmit, slpEmitB_ofOpList]

theorem slpScaleOB_ofOpList (s : List SlpOp) (re im : ℚ) (deg : ℤ) (x : Option ℕ) :
    slpScaleOB (SlpBuf.ofOpList s) re im deg x =
      (SlpBuf.ofOpList (slpScaleO s re im deg x).1, (slpScaleO s re im deg x).2) := by
  cases x with
  | none => rfl
  | some a =>
    by_cases hc : re = 0 ∧ im = 0
    · simp [slpScaleOB, slpScaleO, hc]
    · simp only [slpScaleOB, slpScaleO, hc, ite_false, slpEmitB_ofOpList, slpEmit,
        slpMulOB_ofOpList]

/-! ### Tables -/

/-- Thread the buffer through a list, collecting one result per element (`slpMapSt`). -/
def slpMapStB {α : Type} (f : ℕ → SlpBuf → SlpBuf × α) :
    List ℕ → SlpBuf → SlpBuf × List α
  | [], b => (b, [])
  | i :: l, b =>
    let r := f i b
    let r' := slpMapStB f l r.1
    (r'.1, r.2 :: r'.2)

theorem slpMapStB_sim {α : Type} {f : ℕ → List SlpOp → List SlpOp × α}
    {g : ℕ → SlpBuf → SlpBuf × α} (h : ∀ i, SlpSim (f i) (g i)) (l : List ℕ) :
    SlpSim (slpMapSt f l) (slpMapStB g l) := by
  induction l with
  | nil => intro s; rfl
  | cons i l ih =>
    intro s
    simp only [slpMapSt, slpMapStB, h i s, ih _]

/-- A computation on a buffer (`SlpComp`). -/
abbrev SlpCompB : Type := SlpBuf → SlpBuf × Option ℕ

/-- The constant computation returning an existing slot (`slpPure`). -/
def slpPureB (x : Option ℕ) : SlpCompB := fun b => (b, x)

/-- Sum of two computations (`slpCAdd`). -/
def slpCAddB (c1 c2 : SlpCompB) : SlpCompB := fun b =>
  let r1 := c1 b
  let r2 := c2 r1.1
  slpAddOB r2.1 r1.2 r2.2

/-- Product of two computations (`slpCMul`). -/
def slpCMulB (c1 c2 : SlpCompB) : SlpCompB := fun b =>
  let r1 := c1 b
  let r2 := c2 r1.1
  slpMulOB r2.1 r1.2 r2.2

/-- A constant times a computation (`slpCScale`). -/
def slpCScaleB (re im : ℚ) (deg : ℤ) (c : SlpCompB) : SlpCompB := fun b =>
  let r := c b
  slpScaleOB r.1 re im deg r.2

theorem slpPureB_sim (x : Option ℕ) : SlpSim (slpPure x) (slpPureB x) := fun _ => rfl

theorem slpCAddB_sim {c1 c2 : SlpComp} {d1 d2 : SlpCompB} (h1 : SlpSim c1 d1)
    (h2 : SlpSim c2 d2) : SlpSim (slpCAdd c1 c2) (slpCAddB d1 d2) := by
  intro s
  simp only [slpCAdd, slpCAddB, h1 s, h2 _, slpAddOB_ofOpList]

theorem slpCMulB_sim {c1 c2 : SlpComp} {d1 d2 : SlpCompB} (h1 : SlpSim c1 d1)
    (h2 : SlpSim c2 d2) : SlpSim (slpCMul c1 c2) (slpCMulB d1 d2) := by
  intro s
  simp only [slpCMul, slpCMulB, h1 s, h2 _, slpMulOB_ofOpList]

theorem slpCScaleB_sim (re im : ℚ) (deg : ℤ) {c : SlpComp} {d : SlpCompB} (h : SlpSim c d) :
    SlpSim (slpCScale re im deg c) (slpCScaleB re im deg d) := by
  intro s
  simp only [slpCScale, slpCScaleB, h s, slpScaleOB_ofOpList]

/-- A table of `2n` slots (`slpTab1`). -/
def slpTab1B (n : ℕ) (f : ℕ → SlpCompB) (b : SlpBuf) : SlpBuf × List (Option ℕ) :=
  slpMapStB f (List.range (2 * n)) b

/-- A table of `2n × 2n` slots (`slpTab2`). -/
def slpTab2B (n : ℕ) (f : ℕ → ℕ → SlpCompB) (b : SlpBuf) :
    SlpBuf × List (List (Option ℕ)) :=
  slpMapStB (fun i b => slpTab1B n (f i) b) (List.range (2 * n)) b

/-- A table of `2n × 2n × 2n` slots (`slpTab3`). -/
def slpTab3B (n : ℕ) (f : ℕ → ℕ → ℕ → SlpCompB) (b : SlpBuf) :
    SlpBuf × List (List (List (Option ℕ))) :=
  slpMapStB (fun i b => slpTab2B n (f i) b) (List.range (2 * n)) b

theorem slpTab1B_sim {f : ℕ → SlpComp} {g : ℕ → SlpCompB} (h : ∀ i, SlpSim (f i) (g i)) :
    SlpSim (slpTab1 n f) (slpTab1B n g) :=
  slpMapStB_sim h _

theorem slpTab2B_sim {f : ℕ → ℕ → SlpComp} {g : ℕ → ℕ → SlpCompB}
    (h : ∀ i j, SlpSim (f i j) (g i j)) : SlpSim (slpTab2 n f) (slpTab2B n g) :=
  slpMapStB_sim (fun i => slpTab1B_sim (h i)) _

theorem slpTab3B_sim {f : ℕ → ℕ → ℕ → SlpComp} {g : ℕ → ℕ → ℕ → SlpCompB}
    (h : ∀ i j k, SlpSim (f i j k) (g i j k)) : SlpSim (slpTab3 n f) (slpTab3B n g) :=
  slpMapStB_sim (fun i => slpTab2B_sim (h i)) _

/-- Finish a node from the entry computations (`slpFinish`). -/
def slpFinishB (n : ℕ) (v : ℕ) (c1 : ℕ → SlpCompB) (c2 : ℕ → ℕ → SlpCompB)
    (c3 : ℕ → ℕ → ℕ → SlpCompB) (b : SlpBuf) : SlpBuf × SlpNode :=
  let r1 := slpTab1B n c1 b
  let r2 := slpTab2B n c2 r1.1
  let r3 := slpTab3B n c3 r2.1
  (r3.1, ⟨v, r1.2, r2.2, r3.2⟩)

theorem slpFinishB_sim (v : ℕ) {c1 : ℕ → SlpComp} {c2 : ℕ → ℕ → SlpComp}
    {c3 : ℕ → ℕ → ℕ → SlpComp} {d1 : ℕ → SlpCompB} {d2 : ℕ → ℕ → SlpCompB}
    {d3 : ℕ → ℕ → ℕ → SlpCompB} (h1 : ∀ i, SlpSim (c1 i) (d1 i))
    (h2 : ∀ i j, SlpSim (c2 i j) (d2 i j)) (h3 : ∀ i j k, SlpSim (c3 i j k) (d3 i j k)) :
    SlpSim (slpFinish n v c1 c2 c3) (slpFinishB n v d1 d2 d3) := by
  intro s
  simp only [slpFinish, slpFinishB, slpTab1B_sim h1 s, slpTab2B_sim h2 _, slpTab3B_sim h3 _]

/-- Proves `SlpSim c d` for a computation `c` built from `slpPure`, `slpCAdd`, `slpCMul` and
`slpCScale` and its buffer twin `d`. -/
local macro "slp_sim" : tactic => `(tactic| repeat' first
      | exact slpPureB_sim _
      | apply slpCAddB_sim
      | apply slpCMulB_sim
      | apply slpCScaleB_sim)

/-! ### Nodes -/

/-- The node of a constant (`slpConstNode`). -/
def slpConstNodeB (n : ℕ) (b : SlpBuf) (re im : ℚ) (deg : ℤ) : SlpBuf × SlpNode :=
  slpFinishB n b.len (fun _ => slpPureB none) (fun _ _ => slpPureB none)
    (fun _ _ _ => slpPureB none) (slpEmitB b (.const re im deg)).1

theorem slpConstNodeB_ofOpList (s : List SlpOp) (re im : ℚ) (deg : ℤ) :
    slpConstNodeB n (SlpBuf.ofOpList s) re im deg =
      (SlpBuf.ofOpList (slpConstNode n s re im deg).1, (slpConstNode n s re im deg).2) := by
  simp only [slpConstNodeB, slpConstNode, slpEmitB_ofOpList_fst, SlpBuf.len_ofOpList]
  exact slpFinishB_sim _ (fun _ => slpPureB_sim _) (fun _ _ => slpPureB_sim _)
    (fun _ _ _ => slpPureB_sim _) _

/-- The node of the action coordinate `j` (`slpActionNode`). -/
def slpActionNodeB (n : ℕ) (b : SlpBuf) (j : ℕ) : SlpBuf × SlpNode :=
  slpFinishB n b.len (fun i b' => if i = n + j then slpEmitB b' (.const 1 0 0) else (b', none))
    (fun _ _ => slpPureB none) (fun _ _ _ => slpPureB none) (slpEmitB b (.action j)).1

theorem slpActionNodeB_ofOpList (s : List SlpOp) (j : ℕ) :
    slpActionNodeB n (SlpBuf.ofOpList s) j =
      (SlpBuf.ofOpList (slpActionNode n s j).1, (slpActionNode n s j).2) := by
  simp only [slpActionNodeB, slpActionNode, slpEmitB_ofOpList_fst, SlpBuf.len_ofOpList]
  refine slpFinishB_sim _ (fun i s' => ?_) (fun _ _ => slpPureB_sim _)
    (fun _ _ _ => slpPureB_sim _) _
  by_cases h : i = n + j
  · simp only [h, ite_true, slpEmitB_ofOpList, slpEmit]
  · simp only [h, ite_false]

/-- The node of the character `e^{2πi k·θ}` (`slpCharNode`). -/
def slpCharNodeB (n : ℕ) (b : SlpBuf) (k : CertKey) : SlpBuf × SlpNode :=
  slpFinishB n b.len
    (fun i => if i < n then slpCScaleB 0 ((k.getD i 0 : ℤ) : ℚ) 1 (slpPureB (some b.len))
      else slpPureB none)
    (fun i j => if i < n ∧ j < n then
      slpCScaleB (-(((k.getD i 0 : ℤ) : ℚ) * ((k.getD j 0 : ℤ) : ℚ))) 0 2
        (slpPureB (some b.len)) else slpPureB none)
    (fun i j l => if i < n ∧ j < n ∧ l < n then
      slpCScaleB 0 (-(((k.getD i 0 : ℤ) : ℚ) * ((k.getD j 0 : ℤ) : ℚ) *
        ((k.getD l 0 : ℤ) : ℚ))) 3 (slpPureB (some b.len)) else slpPureB none)
    (slpEmitB b (.char k)).1

theorem slpCharNodeB_ofOpList (s : List SlpOp) (k : CertKey) :
    slpCharNodeB n (SlpBuf.ofOpList s) k =
      (SlpBuf.ofOpList (slpCharNode n s k).1, (slpCharNode n s k).2) := by
  simp only [slpCharNodeB, slpCharNode, slpEmitB_ofOpList_fst, SlpBuf.len_ofOpList]
  refine slpFinishB_sim _ (fun i => ?_) (fun i j => ?_) (fun i j l => ?_) _ <;>
    split_ifs <;> slp_sim

/-- The cross term of the node `A` (`slpCross`). -/
def slpCrossB (A : SlpNode) (i j k : ℕ) : SlpCompB :=
  slpCAddB (slpCAddB (slpCMulB (slpPureB (A.get2 i j)) (slpPureB (A.get1 k)))
    (slpCMulB (slpPureB (A.get1 j)) (slpPureB (A.get2 i k))))
    (slpCMulB (slpPureB (A.get1 i)) (slpPureB (A.get2 j k)))

theorem slpCrossB_sim (A : SlpNode) (i j k : ℕ) : SlpSim (slpCross A i j k) (slpCrossB A i j k) :=
  by unfold slpCross slpCrossB; slp_sim

/-- The node of a sum (`slpAddNode`). -/
def slpAddNodeB (n : ℕ) (b : SlpBuf) (A B : SlpNode) : SlpBuf × SlpNode :=
  slpFinishB n b.len (fun i => slpCAddB (slpPureB (A.get1 i)) (slpPureB (B.get1 i)))
    (fun i j => slpCAddB (slpPureB (A.get2 i j)) (slpPureB (B.get2 i j)))
    (fun i j k => slpCAddB (slpPureB (A.get3 i j k)) (slpPureB (B.get3 i j k)))
    (slpEmitB b (.add A.v B.v)).1

theorem slpAddNodeB_ofOpList (s : List SlpOp) (A B : SlpNode) :
    slpAddNodeB n (SlpBuf.ofOpList s) A B =
      (SlpBuf.ofOpList (slpAddNode n s A B).1, (slpAddNode n s A B).2) := by
  simp only [slpAddNodeB, slpAddNode, slpEmitB_ofOpList_fst, SlpBuf.len_ofOpList]
  exact slpFinishB_sim _ (fun _ => by slp_sim) (fun _ _ => by slp_sim)
    (fun _ _ _ => by slp_sim) _

/-- The third derivative entry of a product (`slpMulD3`). -/
def slpMulD3B (A B : SlpNode) (i j k : ℕ) : SlpCompB :=
  slpCAddB
    (slpCAddB (slpCAddB (slpCMulB (slpPureB (A.get3 i j k)) (slpPureB (some B.v)))
      (slpCMulB (slpPureB (A.get2 j k)) (slpPureB (B.get1 i))))
      (slpCAddB (slpCMulB (slpPureB (A.get2 i k)) (slpPureB (B.get1 j)))
      (slpCMulB (slpPureB (A.get1 k)) (slpPureB (B.get2 i j)))))
    (slpCAddB (slpCAddB (slpCMulB (slpPureB (A.get2 i j)) (slpPureB (B.get1 k)))
      (slpCMulB (slpPureB (A.get1 j)) (slpPureB (B.get2 i k))))
      (slpCAddB (slpCMulB (slpPureB (A.get1 i)) (slpPureB (B.get2 j k)))
      (slpCMulB (slpPureB (some A.v)) (slpPureB (B.get3 i j k)))))

/-- The node of a product (`slpMulNode`). -/
def slpMulNodeB (n : ℕ) (b : SlpBuf) (A B : SlpNode) : SlpBuf × SlpNode :=
  slpFinishB n b.len
    (fun i => slpCAddB (slpCMulB (slpPureB (A.get1 i)) (slpPureB (some B.v)))
      (slpCMulB (slpPureB (some A.v)) (slpPureB (B.get1 i))))
    (fun i j => slpCAddB
      (slpCAddB (slpCMulB (slpPureB (A.get2 i j)) (slpPureB (some B.v)))
        (slpCMulB (slpPureB (A.get1 j)) (slpPureB (B.get1 i))))
      (slpCAddB (slpCMulB (slpPureB (A.get1 i)) (slpPureB (B.get1 j)))
        (slpCMulB (slpPureB (some A.v)) (slpPureB (B.get2 i j)))))
    (slpMulD3B A B) (slpEmitB b (.mul A.v B.v)).1

theorem slpMulNodeB_ofOpList (s : List SlpOp) (A B : SlpNode) :
    slpMulNodeB n (SlpBuf.ofOpList s) A B =
      (SlpBuf.ofOpList (slpMulNode n s A B).1, (slpMulNode n s A B).2) := by
  simp only [slpMulNodeB, slpMulNode, slpEmitB_ofOpList_fst, SlpBuf.len_ofOpList]
  exact slpFinishB_sim _ (fun _ => by slp_sim) (fun _ _ => by slp_sim)
    (fun _ _ _ => by unfold slpMulD3 slpMulD3B; slp_sim) _

/-- The third derivative entry of `exp` (`slpExpD3`). -/
def slpExpD3B (E : Option ℕ) (A : SlpNode) (i j k : ℕ) : SlpCompB :=
  slpCMulB (slpPureB E) (slpCAddB
    (slpCMulB (slpPureB (A.get1 i)) (slpCMulB (slpPureB (A.get1 j)) (slpPureB (A.get1 k))))
    (slpCAddB (slpCrossB A i j k) (slpPureB (A.get3 i j k))))

/-- The node of `exp` (`slpExpNode`). -/
def slpExpNodeB (n : ℕ) (b : SlpBuf) (A : SlpNode) : SlpBuf × SlpNode :=
  slpFinishB n b.len
    (fun i => slpCMulB (slpPureB (some b.len)) (slpPureB (A.get1 i)))
    (fun i j => slpCAddB
      (slpCMulB (slpPureB (some b.len)) (slpCMulB (slpPureB (A.get1 i)) (slpPureB (A.get1 j))))
      (slpCMulB (slpPureB (some b.len)) (slpPureB (A.get2 i j))))
    (slpExpD3B (some b.len) A) (slpEmitB b (.exp A.v)).1

theorem slpExpNodeB_ofOpList (s : List SlpOp) (A : SlpNode) :
    slpExpNodeB n (SlpBuf.ofOpList s) A =
      (SlpBuf.ofOpList (slpExpNode n s A).1, (slpExpNode n s A).2) := by
  simp only [slpExpNodeB, slpExpNode, slpEmitB_ofOpList_fst, SlpBuf.len_ofOpList]
  exact slpFinishB_sim _ (fun _ => by slp_sim) (fun _ _ => by slp_sim)
    (fun i j k => by
      unfold slpExpD3 slpExpD3B
      exact slpCMulB_sim (slpPureB_sim _) (slpCAddB_sim (by slp_sim)
        (slpCAddB_sim (slpCrossB_sim A i j k) (slpPureB_sim _)))) _

/-- The third derivative entry of `x⁻¹` (`slpInvD3`). -/
def slpInvD3B (w2 w3 w4 : Option ℕ) (A : SlpNode) (i j k : ℕ) : SlpCompB :=
  slpCAddB (slpCScaleB (-6) 0 0 (slpCMulB (slpPureB w4) (slpCMulB (slpPureB (A.get1 i))
    (slpCMulB (slpPureB (A.get1 j)) (slpPureB (A.get1 k))))))
    (slpCAddB (slpCScaleB 2 0 0 (slpCMulB (slpPureB w3) (slpCrossB A i j k)))
      (slpCScaleB (-1) 0 0 (slpCMulB (slpPureB w2) (slpPureB (A.get3 i j k)))))

theorem slpInvD3B_sim (w2 w3 w4 : Option ℕ) (A : SlpNode) (i j k : ℕ) :
    SlpSim (slpInvD3 w2 w3 w4 A i j k) (slpInvD3B w2 w3 w4 A i j k) := by
  unfold slpInvD3 slpInvD3B
  exact slpCAddB_sim (by slp_sim) (slpCAddB_sim (slpCScaleB_sim _ _ _
    (slpCMulB_sim (slpPureB_sim _) (slpCrossB_sim A i j k))) (by slp_sim))

/-- The derivative tables of `x⁻¹` (`slpInvTail`). -/
def slpInvTailB (n : ℕ) (v : ℕ) (A : SlpNode) (w2 w3 w4 : Option ℕ) (b : SlpBuf) :
    SlpBuf × SlpNode :=
  slpFinishB n v
    (fun i => slpCScaleB (-1) 0 0 (slpCMulB (slpPureB w2) (slpPureB (A.get1 i))))
    (fun i j => slpCAddB
      (slpCScaleB 2 0 0 (slpCMulB (slpPureB w3) (slpCMulB (slpPureB (A.get1 i))
        (slpPureB (A.get1 j)))))
      (slpCScaleB (-1) 0 0 (slpCMulB (slpPureB w2) (slpPureB (A.get2 i j)))))
    (slpInvD3B w2 w3 w4 A) b

theorem slpInvTailB_ofOpList (s : List SlpOp) (v : ℕ) (A : SlpNode) (w2 w3 w4 : Option ℕ) :
    slpInvTailB n v A w2 w3 w4 (SlpBuf.ofOpList s) =
      (SlpBuf.ofOpList (slpInvTail n v A w2 w3 w4 s).1, (slpInvTail n v A w2 w3 w4 s).2) :=
  slpFinishB_sim _ (fun _ => by slp_sim) (fun _ _ => by slp_sim)
    (fun i j k => slpInvD3B_sim w2 w3 w4 A i j k) s

/-- The program of the node of `x ↦ x⁻¹` before its tables (`slpInvPre`). -/
def slpInvPreB (b : SlpBuf) (A : SlpNode) : SlpBuf × Option ℕ × Option ℕ × Option ℕ :=
  let r1 := slpEmitB b (.inv A.v)
  let r2 := slpMulOB r1.1 r1.2 r1.2
  let r3 := slpMulOB r2.1 r1.2 r2.2
  let r4 := slpMulOB r3.1 r1.2 r3.2
  (r4.1, r2.2, r3.2, r4.2)

theorem slpInvPreB_ofOpList (s : List SlpOp) (A : SlpNode) :
    slpInvPreB (SlpBuf.ofOpList s) A =
      (SlpBuf.ofOpList (slpInvPre s A).1, (slpInvPre s A).2) := by
  simp only [slpInvPreB, slpInvPre, slpEmitB_ofOpList, slpEmit, slpMulOB_ofOpList]

/-- The node of `x ↦ x⁻¹` (`slpInvNode`). -/
def slpInvNodeB (n : ℕ) (b : SlpBuf) (A : SlpNode) : SlpBuf × SlpNode :=
  slpInvTailB n b.len A (slpInvPreB b A).2.1 (slpInvPreB b A).2.2.1 (slpInvPreB b A).2.2.2
    (slpInvPreB b A).1

theorem slpInvNodeB_ofOpList (s : List SlpOp) (A : SlpNode) :
    slpInvNodeB n (SlpBuf.ofOpList s) A =
      (SlpBuf.ofOpList (slpInvNode n s A).1, (slpInvNode n s A).2) := by
  simp only [slpInvNodeB, slpInvNode, slpInvPreB_ofOpList, SlpBuf.len_ofOpList,
    slpInvTailB_ofOpList]

/-- The third derivative entry of `√x` (`slpSqrtD3`). -/
def slpSqrtD3B (w1 w3 w5 : Option ℕ) (A : SlpNode) (i j k : ℕ) : SlpCompB :=
  slpCAddB (slpCScaleB (3 / 8) 0 0 (slpCMulB (slpPureB w5) (slpCMulB (slpPureB (A.get1 i))
    (slpCMulB (slpPureB (A.get1 j)) (slpPureB (A.get1 k))))))
    (slpCAddB (slpCScaleB (-1 / 4) 0 0 (slpCMulB (slpPureB w3) (slpCrossB A i j k)))
      (slpCScaleB (1 / 2) 0 0 (slpCMulB (slpPureB w1) (slpPureB (A.get3 i j k)))))

theorem slpSqrtD3B_sim (w1 w3 w5 : Option ℕ) (A : SlpNode) (i j k : ℕ) :
    SlpSim (slpSqrtD3 w1 w3 w5 A i j k) (slpSqrtD3B w1 w3 w5 A i j k) := by
  unfold slpSqrtD3 slpSqrtD3B
  exact slpCAddB_sim (by slp_sim) (slpCAddB_sim (slpCScaleB_sim _ _ _
    (slpCMulB_sim (slpPureB_sim _) (slpCrossB_sim A i j k))) (by slp_sim))

/-- The derivative tables of `√x` (`slpSqrtTail`). -/
def slpSqrtTailB (n : ℕ) (v : ℕ) (A : SlpNode) (w1 w3 w5 : Option ℕ) (b : SlpBuf) :
    SlpBuf × SlpNode :=
  slpFinishB n v
    (fun i => slpCScaleB (1 / 2) 0 0 (slpCMulB (slpPureB w1) (slpPureB (A.get1 i))))
    (fun i j => slpCAddB
      (slpCScaleB (1 / 2) 0 0 (slpCMulB (slpPureB w1) (slpPureB (A.get2 i j))))
      (slpCScaleB (-1 / 4) 0 0 (slpCMulB (slpPureB w3) (slpCMulB (slpPureB (A.get1 i))
        (slpPureB (A.get1 j))))))
    (slpSqrtD3B w1 w3 w5 A) b

theorem slpSqrtTailB_ofOpList (s : List SlpOp) (v : ℕ) (A : SlpNode) (w1 w3 w5 : Option ℕ) :
    slpSqrtTailB n v A w1 w3 w5 (SlpBuf.ofOpList s) =
      (SlpBuf.ofOpList (slpSqrtTail n v A w1 w3 w5 s).1, (slpSqrtTail n v A w1 w3 w5 s).2) :=
  slpFinishB_sim _ (fun _ => by slp_sim) (fun _ _ => by slp_sim)
    (fun i j k => slpSqrtD3B_sim w1 w3 w5 A i j k) s

/-- The program of the node of `√x` before its tables (`slpSqrtPre`). -/
def slpSqrtPreB (b : SlpBuf) (A : SlpNode) : SlpBuf × Option ℕ × Option ℕ × Option ℕ :=
  let r0 := slpEmitB b (.sqrt A.v)
  let r1 := slpEmitB r0.1 (.inv b.len)
  let r2 := slpMulOB r1.1 r1.2 r1.2
  let r3 := slpMulOB r2.1 r1.2 r2.2
  let r5 := slpMulOB r3.1 r2.2 r3.2
  (r5.1, r1.2, r3.2, r5.2)

theorem slpSqrtPreB_ofOpList (s : List SlpOp) (A : SlpNode) :
    slpSqrtPreB (SlpBuf.ofOpList s) A =
      (SlpBuf.ofOpList (slpSqrtPre s A).1, (slpSqrtPre s A).2) := by
  simp only [slpSqrtPreB, slpSqrtPre, slpEmitB_ofOpList, slpEmit, SlpBuf.len_ofOpList,
    slpMulOB_ofOpList]

/-- The node of `√x` (`slpSqrtNode`). -/
def slpSqrtNodeB (n : ℕ) (b : SlpBuf) (A : SlpNode) : SlpBuf × SlpNode :=
  slpSqrtTailB n b.len A (slpSqrtPreB b A).2.1 (slpSqrtPreB b A).2.2.1 (slpSqrtPreB b A).2.2.2
    (slpSqrtPreB b A).1

theorem slpSqrtNodeB_ofOpList (s : List SlpOp) (A : SlpNode) :
    slpSqrtNodeB n (SlpBuf.ofOpList s) A =
      (SlpBuf.ofOpList (slpSqrtNode n s A).1, (slpSqrtNode n s A).2) := by
  simp only [slpSqrtNodeB, slpSqrtNode, slpSqrtPreB_ofOpList, SlpBuf.len_ofOpList,
    slpSqrtTailB_ofOpList]

/-! ### Derived nodes and the compiler -/

/-- The constant `(re + i im)(2π)^deg` times a node (`slpScaleNode`). -/
def slpScaleNodeB (n : ℕ) (b : SlpBuf) (re im : ℚ) (deg : ℤ) (A : SlpNode) :
    SlpBuf × SlpNode :=
  slpMulNodeB n (slpConstNodeB n b re im deg).1 (slpConstNodeB n b re im deg).2 A

theorem slpScaleNodeB_ofOpList (s : List SlpOp) (re im : ℚ) (deg : ℤ) (A : SlpNode) :
    slpScaleNodeB n (SlpBuf.ofOpList s) re im deg A =
      (SlpBuf.ofOpList (slpScaleNode n s re im deg A).1, (slpScaleNode n s re im deg A).2) := by
  simp only [slpScaleNodeB, slpScaleNode, slpConstNodeB_ofOpList, slpMulNodeB_ofOpList]

/-- `exp (c · A)` for a constant `c` (`slpExpScaleNode`). -/
def slpExpScaleNodeB (n : ℕ) (b : SlpBuf) (re im : ℚ) (deg : ℤ) (A : SlpNode) :
    SlpBuf × SlpNode :=
  slpExpNodeB n (slpScaleNodeB n b re im deg A).1 (slpScaleNodeB n b re im deg A).2

theorem slpExpScaleNodeB_ofOpList (s : List SlpOp) (re im : ℚ) (deg : ℤ) (A : SlpNode) :
    slpExpScaleNodeB n (SlpBuf.ofOpList s) re im deg A =
      (SlpBuf.ofOpList (slpExpScaleNode n s re im deg A).1,
        (slpExpScaleNode n s re im deg A).2) := by
  simp only [slpExpScaleNodeB, slpExpScaleNode, slpScaleNodeB_ofOpList, slpExpNodeB_ofOpList]

/-- `c₁ X + c₂ Y` for constants `c₁`, `c₂` (`slpCombine`). -/
def slpCombineB (n : ℕ) (b : SlpBuf) (re1 im1 re2 im2 : ℚ) (X Y : SlpNode) :
    SlpBuf × SlpNode :=
  slpAddNodeB n (slpScaleNodeB n (slpScaleNodeB n b re1 im1 0 X).1 re2 im2 0 Y).1
    (slpScaleNodeB n b re1 im1 0 X).2
    (slpScaleNodeB n (slpScaleNodeB n b re1 im1 0 X).1 re2 im2 0 Y).2

theorem slpCombineB_ofOpList (s : List SlpOp) (re1 im1 re2 im2 : ℚ) (X Y : SlpNode) :
    slpCombineB n (SlpBuf.ofOpList s) re1 im1 re2 im2 X Y =
      (SlpBuf.ofOpList (slpCombine n s re1 im1 re2 im2 X Y).1,
        (slpCombine n s re1 im1 re2 im2 X Y).2) := by
  simp only [slpCombineB, slpCombine, slpScaleNodeB_ofOpList, slpAddNodeB_ofOpList]

/-- `A^m` by repeated multiplication (`slpPowNode`). -/
def slpPowNodeB (n : ℕ) (b : SlpBuf) (A : SlpNode) : ℕ → SlpBuf × SlpNode
  | 0 => slpConstNodeB n b 1 0 0
  | m + 1 => slpMulNodeB n (slpPowNodeB n b A m).1 (slpPowNodeB n b A m).2 A

theorem slpPowNodeB_ofOpList (s : List SlpOp) (A : SlpNode) (m : ℕ) :
    slpPowNodeB n (SlpBuf.ofOpList s) A m =
      (SlpBuf.ofOpList (slpPowNode n s A m).1, (slpPowNode n s A m).2) := by
  induction m with
  | zero => exact slpConstNodeB_ofOpList s 1 0 0
  | succ m ih => simp only [slpPowNodeB, slpPowNode, ih, slpMulNodeB_ofOpList]

/-- `c₁ e^{i x} + c₂ e^{-i x}` for the operand `x` of the node `A` (`slpTrigNode`). -/
def slpTrigNodeB (n : ℕ) (re1 im1 re2 im2 : ℚ) (b : SlpBuf) (A : SlpNode) : SlpBuf × SlpNode :=
  slpCombineB n (slpExpScaleNodeB n (slpExpScaleNodeB n b 0 1 0 A).1 0 (-1) 0 A).1 re1 im1 re2
    im2 (slpExpScaleNodeB n b 0 1 0 A).2
    (slpExpScaleNodeB n (slpExpScaleNodeB n b 0 1 0 A).1 0 (-1) 0 A).2

theorem slpTrigNodeB_ofOpList (re1 im1 re2 im2 : ℚ) (s : List SlpOp) (A : SlpNode) :
    slpTrigNodeB n re1 im1 re2 im2 (SlpBuf.ofOpList s) A =
      (SlpBuf.ofOpList (slpTrigNode n re1 im1 re2 im2 s A).1,
        (slpTrigNode n re1 im1 re2 im2 s A).2) := by
  simp only [slpTrigNodeB, slpTrigNode, slpExpScaleNodeB_ofOpList, slpCombineB_ofOpList]

/-- `c₁ e^{2πi k·θ} + c₂ e^{-2πi k·θ}` (`slpTrigChar`). -/
def slpTrigCharB (n : ℕ) (re1 im1 re2 im2 : ℚ) (b : SlpBuf) (k : CertKey) : SlpBuf × SlpNode :=
  slpCombineB n (slpCharNodeB n (slpCharNodeB n b k).1 (negKey k)).1 re1 im1 re2 im2
    (slpCharNodeB n b k).2 (slpCharNodeB n (slpCharNodeB n b k).1 (negKey k)).2

theorem slpTrigCharB_ofOpList (re1 im1 re2 im2 : ℚ) (s : List SlpOp) (k : CertKey) :
    slpTrigCharB n re1 im1 re2 im2 (SlpBuf.ofOpList s) k =
      (SlpBuf.ofOpList (slpTrigChar n re1 im1 re2 im2 s k).1,
        (slpTrigChar n re1 im1 re2 im2 s k).2) := by
  simp only [slpTrigCharB, slpTrigChar, slpCharNodeB_ofOpList, slpCombineB_ofOpList]

/-- The quotient `A · B⁻¹` (`slpDivNode`). -/
def slpDivNodeB (n : ℕ) (b : SlpBuf) (A B : SlpNode) : SlpBuf × SlpNode :=
  slpMulNodeB n (slpInvNodeB n b B).1 A (slpInvNodeB n b B).2

theorem slpDivNodeB_ofOpList (s : List SlpOp) (A B : SlpNode) :
    slpDivNodeB n (SlpBuf.ofOpList s) A B =
      (SlpBuf.ofOpList (slpDivNode n s A B).1, (slpDivNode n s A B).2) := by
  simp only [slpDivNodeB, slpDivNode, slpInvNodeB_ofOpList, slpMulNodeB_ofOpList]

/-- The jet compiler on a buffer (`slpCompile`). -/
def slpCompileB {n : ℕ} : HamExpr n → SlpBuf → SlpBuf × SlpNode
  | .const q, b => slpConstNodeB n b q 0 0
  | .pi, b => slpConstNodeB n b (1 / 2) 0 1
  | .action j, b => slpActionNodeB n b j.val
  | .cosMode k, b => slpTrigCharB n (1 / 2) 0 (1 / 2) 0 b k
  | .sinMode k, b => slpTrigCharB n 0 (-1 / 2) 0 (1 / 2) b k
  | .add a c, b =>
    let ra := slpCompileB a b
    let rc := slpCompileB c ra.1
    slpAddNodeB n rc.1 ra.2 rc.2
  | .mul a c, b =>
    let ra := slpCompileB a b
    let rc := slpCompileB c ra.1
    slpMulNodeB n rc.1 ra.2 rc.2
  | .div a c, b =>
    let ra := slpCompileB a b
    let rc := slpCompileB c ra.1
    slpDivNodeB n rc.1 ra.2 rc.2
  | .pow a m, b =>
    let ra := slpCompileB a b
    slpPowNodeB n ra.1 ra.2 m
  | .exp a, b =>
    let ra := slpCompileB a b
    slpExpNodeB n ra.1 ra.2
  | .sin a, b =>
    let ra := slpCompileB a b
    slpTrigNodeB n 0 (-1 / 2) 0 (1 / 2) ra.1 ra.2
  | .cos a, b =>
    let ra := slpCompileB a b
    slpTrigNodeB n (1 / 2) 0 (1 / 2) 0 ra.1 ra.2
  | .sqrt a, b =>
    let ra := slpCompileB a b
    slpSqrtNodeB n ra.1 ra.2

/-- The buffer compiler runs `slpCompile`: same program, same slots. -/
theorem slpCompileB_ofOpList {n : ℕ} (e : HamExpr n) (s : List SlpOp) :
    slpCompileB e (SlpBuf.ofOpList s) =
      (SlpBuf.ofOpList (slpCompile e s).1, (slpCompile e s).2) := by
  induction e generalizing s with
  | const q => exact slpConstNodeB_ofOpList s q 0 0
  | pi => exact slpConstNodeB_ofOpList s (1 / 2) 0 1
  | action j => exact slpActionNodeB_ofOpList s j.val
  | cosMode k => exact slpTrigCharB_ofOpList _ _ _ _ s k
  | sinMode k => exact slpTrigCharB_ofOpList _ _ _ _ s k
  | add a c iha ihc => simp only [slpCompileB, slpCompile, iha, ihc, slpAddNodeB_ofOpList]
  | mul a c iha ihc => simp only [slpCompileB, slpCompile, iha, ihc, slpMulNodeB_ofOpList]
  | div a c iha ihc => simp only [slpCompileB, slpCompile, iha, ihc, slpDivNodeB_ofOpList]
  | pow a m iha => simp only [slpCompileB, slpCompile, iha, slpPowNodeB_ofOpList]
  | exp a iha => simp only [slpCompileB, slpCompile, iha, slpExpNodeB_ofOpList]
  | sin a iha => simp only [slpCompileB, slpCompile, iha, slpTrigNodeB_ofOpList]
  | cos a iha => simp only [slpCompileB, slpCompile, iha, slpTrigNodeB_ofOpList]
  | sqrt a iha => simp only [slpCompileB, slpCompile, iha, slpSqrtNodeB_ofOpList]

/-- The program of the buffer compiler is the program of `slpCompile`. -/
theorem slpCompileB_opList {n : ℕ} (e : HamExpr n) (s : List SlpOp) :
    (slpCompileB e (SlpBuf.ofOpList s)).1.opList = (slpCompile e s).1 := by
  rw [slpCompileB_ofOpList, SlpBuf.opList_ofOpList]

end KAM.Certificate

end
