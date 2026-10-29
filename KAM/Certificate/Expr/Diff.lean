/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.DiffNode

/-!
# The symbolic jet of a Hamiltonian expression, to second order

`HamExpr.jet` compiles an expression to a straight-line program with forward-mode derivative
slots (`slpCompile`): every sub-expression is compiled once and its value, first and second
derivative slots are shared by its parents. Sine and cosine of an expression and of a mode are
compiled through `exp` and the characters `e^{±2πi k·θ}`; a quotient is a product with an
`inv` node; a power is repeated multiplication. No operation is ever dropped from the program
(only derivative slots that vanish identically are folded), so every `inv` operand of the source
stays in the program, as the ball arithmetic of SO-BALL requires.

The values are those of `HamExpr.eval` everywhere (`jet_v0`), and on an open set where the
denominators are nonvanishing the tables are the first and second derivatives (`jet_d1`,
`jet_d2`). The tables of order three (`d3`, SO-EXPR part B2) are left empty here.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM

variable {n : ℕ}

local notation "Ph" => (Fin n → ℂ) × (Fin n → ℂ)

/-- The constant `(re + i im)(2π)^deg` times a node. -/
def slpScaleNode (n : ℕ) (s : List SlpOp) (re im : ℚ) (deg : ℤ) (A : SlpNode) :
    List SlpOp × SlpNode :=
  slpMulNode n (slpConstNode n s re im deg).1 (slpConstNode n s re im deg).2 A

theorem slpScaleNode_sound {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ} (hf : JetSmoothOn S f)
    {s : List SlpOp} {A : SlpNode} (hA : A.Sound n S f s) (re im : ℚ) (deg : ℤ) :
    s <+: (slpScaleNode n s re im deg A).1 ∧ (slpScaleNode n s re im deg A).2.Sound n S
      (fun z => slpConstVal re im deg * f z) (slpScaleNode n s re im deg A).1 := by
  obtain ⟨p1, h1⟩ := slpConstNode_sound S s re im deg
  obtain ⟨p2, h2⟩ := slpMulNode_sound hS (JetSmoothOn.const S (slpConstVal re im deg)) hf h1
    (hA.mono p1)
  exact ⟨p1.trans p2, h2⟩

/-- `exp (c · A)` for a constant `c`. -/
def slpExpScaleNode (n : ℕ) (s : List SlpOp) (re im : ℚ) (deg : ℤ) (A : SlpNode) :
    List SlpOp × SlpNode :=
  slpExpNode n (slpScaleNode n s re im deg A).1 (slpScaleNode n s re im deg A).2

theorem slpExpScaleNode_sound {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ} (hf : JetSmoothOn S f)
    {s : List SlpOp} {A : SlpNode} (hA : A.Sound n S f s) (re im : ℚ) (deg : ℤ) :
    s <+: (slpExpScaleNode n s re im deg A).1 ∧ (slpExpScaleNode n s re im deg A).2.Sound n S
      (fun z => Complex.exp (slpConstVal re im deg * f z)) (slpExpScaleNode n s re im deg A).1 := by
  obtain ⟨p1, h1⟩ := slpScaleNode_sound hS hf hA re im deg
  obtain ⟨p2, h2⟩ := slpExpNode_sound hS ((JetSmoothOn.const S _).mul hf) h1
  exact ⟨p1.trans p2, h2⟩

/-- `c₁ X + c₂ Y` for constants `c₁`, `c₂` (of degree zero). -/
def slpCombine (n : ℕ) (s : List SlpOp) (re1 im1 re2 im2 : ℚ) (X Y : SlpNode) :
    List SlpOp × SlpNode :=
  slpAddNode n (slpScaleNode n (slpScaleNode n s re1 im1 0 X).1 re2 im2 0 Y).1
    (slpScaleNode n s re1 im1 0 X).2
    (slpScaleNode n (slpScaleNode n s re1 im1 0 X).1 re2 im2 0 Y).2

theorem slpCombine_sound {S : Set Ph} (hS : IsOpen S) {f g : Ph → ℂ} (hf : JetSmoothOn S f)
    (hg : JetSmoothOn S g) {s : List SlpOp} {X Y : SlpNode} (hX : X.Sound n S f s)
    (hY : Y.Sound n S g s) (re1 im1 re2 im2 : ℚ) :
    s <+: (slpCombine n s re1 im1 re2 im2 X Y).1 ∧
      (slpCombine n s re1 im1 re2 im2 X Y).2.Sound n S
        (fun z => slpConstVal re1 im1 0 * f z + slpConstVal re2 im2 0 * g z)
        (slpCombine n s re1 im1 re2 im2 X Y).1 := by
  obtain ⟨p1, h1⟩ := slpScaleNode_sound hS hf hX re1 im1 0
  obtain ⟨p2, h2⟩ := slpScaleNode_sound hS hg (hY.mono p1) re2 im2 0
  obtain ⟨p3, h3⟩ := slpAddNode_sound hS ((JetSmoothOn.const S _).mul hf)
    ((JetSmoothOn.const S _).mul hg) (h1.mono p2) h2
  exact ⟨(p1.trans p2).trans p3, h3⟩

/-- `A^m` by repeated multiplication. -/
def slpPowNode (n : ℕ) (s : List SlpOp) (A : SlpNode) : ℕ → List SlpOp × SlpNode
  | 0 => slpConstNode n s 1 0 0
  | m + 1 => slpMulNode n (slpPowNode n s A m).1 (slpPowNode n s A m).2 A

theorem slpPowNode_sound {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ} (hf : JetSmoothOn S f)
    {s : List SlpOp} {A : SlpNode} (hA : A.Sound n S f s) (m : ℕ) :
    s <+: (slpPowNode n s A m).1 ∧
      (slpPowNode n s A m).2.Sound n S (fun z => f z ^ m) (slpPowNode n s A m).1 := by
  induction m with
  | zero =>
    obtain ⟨p, h⟩ := slpConstNode_sound S s 1 0 0
    have e : (fun _ : Ph => slpConstVal 1 0 0) = fun z => f z ^ 0 := by
      funext z; simp [slpConstVal]
    rw [e] at h
    exact ⟨p, h⟩
  | succ m ih =>
    obtain ⟨p1, h1⟩ := ih
    have hfm : JetSmoothOn S (fun z => f z ^ m) := ContDiffOn.pow hf m
    obtain ⟨p2, h2⟩ := slpMulNode_sound hS hfm hf h1 (hA.mono p1)
    have e : (fun z => f z ^ m * f z) = fun z => f z ^ (m + 1) := by
      funext z; rw [pow_succ]
    rw [e] at h2
    exact ⟨p1.trans p2, h2⟩

/-- The negated key: `k ↦ -k`. -/
def negKey (k : CertKey) : CertKey := k.map (fun x => -x)

theorem modePhase_negKey (k : CertKey) (θ : Fin n → ℂ) :
    modePhase n (negKey k) θ = -modePhase n k θ := by
  unfold modePhase
  have : ∀ i : Fin n, (certKeyFun n (negKey k) i : ℂ) = -(certKeyFun n k i : ℂ) := by
    intro i
    simp only [certKeyFun, negKey, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases k[i.val]? <;> simp
  simp only [this, neg_mul, Finset.sum_neg_distrib]
  ring

/-- `c₁ e^{i x} + c₂ e^{-i x}` for the operand `x` of the node `A` (sine and cosine). -/
def slpTrigNode (n : ℕ) (re1 im1 re2 im2 : ℚ) (s : List SlpOp) (A : SlpNode) :
    List SlpOp × SlpNode :=
  slpCombine n (slpExpScaleNode n (slpExpScaleNode n s 0 1 0 A).1 0 (-1) 0 A).1 re1 im1 re2 im2
    (slpExpScaleNode n s 0 1 0 A).2 (slpExpScaleNode n (slpExpScaleNode n s 0 1 0 A).1 0 (-1) 0 A).2

/-- `c₁ e^{2πi k·θ} + c₂ e^{-2πi k·θ}` (sine and cosine modes). -/
def slpTrigChar (n : ℕ) (re1 im1 re2 im2 : ℚ) (s : List SlpOp) (k : CertKey) :
    List SlpOp × SlpNode :=
  slpCombine n (slpCharNode n (slpCharNode n s k).1 (negKey k)).1 re1 im1 re2 im2
    (slpCharNode n s k).2 (slpCharNode n (slpCharNode n s k).1 (negKey k)).2

/-- The quotient `A · B⁻¹`. -/
def slpDivNode (n : ℕ) (s : List SlpOp) (A B : SlpNode) : List SlpOp × SlpNode :=
  slpMulNode n (slpInvNode n s B).1 A (slpInvNode n s B).2

theorem JetSmoothOn.charFn (S : Set Ph) (k : CertKey) :
    JetSmoothOn S (fun z : Ph => Complex.exp (Complex.I * modePhase n k z.1)) :=
  ((JetSmoothOn.const _ _).mul (jetSmoothOn_modePhase S k)).cexp

theorem slpTrigNode_sound {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ} (hf : JetSmoothOn S f)
    {s : List SlpOp} {A : SlpNode} (hA : A.Sound n S f s) (re1 im1 re2 im2 : ℚ) :
    s <+: (slpTrigNode n re1 im1 re2 im2 s A).1 ∧ (slpTrigNode n re1 im1 re2 im2 s A).2.Sound n S
      (fun z => slpConstVal re1 im1 0 * Complex.exp (slpConstVal 0 1 0 * f z) +
        slpConstVal re2 im2 0 * Complex.exp (slpConstVal 0 (-1) 0 * f z))
      (slpTrigNode n re1 im1 re2 im2 s A).1 := by
  obtain ⟨p1, h1⟩ := slpExpScaleNode_sound hS hf hA 0 1 0
  obtain ⟨p2, h2⟩ := slpExpScaleNode_sound hS hf (hA.mono p1) 0 (-1) 0
  obtain ⟨p3, h3⟩ := slpCombine_sound hS (((JetSmoothOn.const S _).mul hf).cexp)
    (((JetSmoothOn.const S _).mul hf).cexp) (h1.mono p2) h2 re1 im1 re2 im2
  exact ⟨(p1.trans p2).trans p3, h3⟩

theorem slpTrigChar_sound (S : Set Ph) (hS : IsOpen S) (s : List SlpOp) (k : CertKey)
    (re1 im1 re2 im2 : ℚ) :
    s <+: (slpTrigChar n re1 im1 re2 im2 s k).1 ∧ (slpTrigChar n re1 im1 re2 im2 s k).2.Sound n S
      (fun z => slpConstVal re1 im1 0 * Complex.exp (Complex.I * modePhase n k z.1) +
        slpConstVal re2 im2 0 * Complex.exp (Complex.I * modePhase n (negKey k) z.1))
      (slpTrigChar n re1 im1 re2 im2 s k).1 := by
  obtain ⟨p1, h1⟩ := slpCharNode_sound S s k
  obtain ⟨p2, h2⟩ := slpCharNode_sound S (slpCharNode n s k).1 (negKey k)
  obtain ⟨p3, h3⟩ := slpCombine_sound hS (JetSmoothOn.charFn S k)
    (JetSmoothOn.charFn S (negKey k)) (h1.mono p2) h2 re1 im1 re2 im2
  exact ⟨(p1.trans p2).trans p3, h3⟩

theorem slpDivNode_sound {S : Set Ph} (hS : IsOpen S) {f g : Ph → ℂ} (hf : JetSmoothOn S f)
    (hg : JetSmoothOn S g) (h0 : ∀ z ∈ S, g z ≠ 0) {s : List SlpOp} {A B : SlpNode}
    (hA : A.Sound n S f s) (hB : B.Sound n S g s) :
    s <+: (slpDivNode n s A B).1 ∧
      (slpDivNode n s A B).2.Sound n S (fun z => f z * (g z)⁻¹) (slpDivNode n s A B).1 := by
  obtain ⟨p1, h1⟩ := slpInvNode_sound hS hg h0 hB
  obtain ⟨p2, h2⟩ := slpMulNode_sound hS hf (hg.inv h0) (hA.mono p1) h1
  exact ⟨p1.trans p2, h2⟩

theorem cos_eq_exp (x : ℂ) :
    Complex.cos x = slpConstVal (1 / 2) 0 0 * Complex.exp (slpConstVal 0 1 0 * x) +
      slpConstVal (1 / 2) 0 0 * Complex.exp (slpConstVal 0 (-1) 0 * x) := by
  simp only [slpConstVal, Complex.cos]
  push_cast
  simp only [zpow_zero, mul_one, zero_add, one_mul, neg_mul, mul_comm x]
  ring_nf

theorem sin_eq_exp (x : ℂ) :
    Complex.sin x = slpConstVal 0 (-1 / 2) 0 * Complex.exp (slpConstVal 0 1 0 * x) +
      slpConstVal 0 (1 / 2) 0 * Complex.exp (slpConstVal 0 (-1) 0 * x) := by
  simp only [slpConstVal, Complex.sin]
  push_cast
  simp only [zpow_zero, mul_one, zero_add, one_mul, neg_mul, mul_comm x]
  ring_nf

/-- Compile an expression, sharing sub-expressions, to a node of a program. -/
def slpCompile {n : ℕ} : HamExpr n → List SlpOp → List SlpOp × SlpNode
  | .const q, s => slpConstNode n s q 0 0
  | .pi, s => slpConstNode n s (1 / 2) 0 1
  | .action j, s => slpActionNode n s j.val
  | .cosMode k, s => slpTrigChar n (1 / 2) 0 (1 / 2) 0 s k
  | .sinMode k, s => slpTrigChar n 0 (-1 / 2) 0 (1 / 2) s k
  | .add a b, s =>
    let ra := slpCompile a s
    let rb := slpCompile b ra.1
    slpAddNode n rb.1 ra.2 rb.2
  | .mul a b, s =>
    let ra := slpCompile a s
    let rb := slpCompile b ra.1
    slpMulNode n rb.1 ra.2 rb.2
  | .div a b, s =>
    let ra := slpCompile a s
    let rb := slpCompile b ra.1
    slpDivNode n rb.1 ra.2 rb.2
  | .pow a m, s =>
    let ra := slpCompile a s
    slpPowNode n ra.1 ra.2 m
  | .exp a, s =>
    let ra := slpCompile a s
    slpExpNode n ra.1 ra.2
  | .sin a, s =>
    let ra := slpCompile a s
    slpTrigNode n 0 (-1 / 2) 0 (1 / 2) ra.1 ra.2
  | .cos a, s =>
    let ra := slpCompile a s
    slpTrigNode n (1 / 2) 0 (1 / 2) 0 ra.1 ra.2

theorem HamExpr.jetSmoothOn {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (h : e.NonvanishingOn S) : JetSmoothOn S e.eval :=
  (e.contDiffOn_eval hS h).of_le le_top

theorem HamExpr.nonvanishingOn_empty {n : ℕ} (e : HamExpr n) :
    e.NonvanishingOn (∅ : Set ((Fin n → ℂ) × (Fin n → ℂ))) := by
  induction e with
  | add a b iha ihb => exact ⟨iha, ihb⟩
  | mul a b iha ihb => exact ⟨iha, ihb⟩
  | div a b iha ihb => exact ⟨iha, ihb, fun z hz => absurd hz (Set.notMem_empty z)⟩
  | pow a m iha => exact iha
  | exp a iha => exact iha
  | sin a iha => exact iha
  | cos a iha => exact iha
  | _ => trivial

/-- The compiled node computes `e.eval` and its derivatives on an open set where the
denominators of `e` are nonvanishing. -/
theorem slpCompile_sound {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (hnv : e.NonvanishingOn S) (s : List SlpOp) :
    s <+: (slpCompile e s).1 ∧ (slpCompile e s).2.Sound n S e.eval (slpCompile e s).1 := by
  induction e generalizing s with
  | const q =>
    have h : (HamExpr.const q : HamExpr n).eval = fun _ => slpConstVal q 0 0 := by
      funext z; simp [HamExpr.eval, slpConstVal]
    rw [h]
    exact slpConstNode_sound S s q 0 0
  | pi =>
    have h : (HamExpr.pi : HamExpr n).eval = fun _ => slpConstVal (1 / 2) 0 1 := by
      funext z; simp [HamExpr.eval, slpConstVal]
    rw [h]
    exact slpConstNode_sound S s (1 / 2) 0 1
  | action j => exact slpActionNode_sound S s j
  | cosMode k =>
    obtain ⟨p, h⟩ := slpTrigChar_sound S hS s k (1 / 2) 0 (1 / 2) 0
    have e : (HamExpr.cosMode k : HamExpr n).eval = fun z => slpConstVal (1 / 2) 0 0 *
        Complex.exp (Complex.I * modePhase n k z.1) +
        slpConstVal (1 / 2) 0 0 * Complex.exp (Complex.I * modePhase n (negKey k) z.1) := by
      funext z
      simp only [HamExpr.eval, modePhase_negKey]
      rw [cos_eq_exp]
      simp only [slpConstVal, zpow_zero]
      push_cast
      ring_nf
    rw [e]
    exact ⟨p, h⟩
  | sinMode k =>
    obtain ⟨p, h⟩ := slpTrigChar_sound S hS s k 0 (-1 / 2) 0 (1 / 2)
    have e : (HamExpr.sinMode k : HamExpr n).eval = fun z => slpConstVal 0 (-1 / 2) 0 *
        Complex.exp (Complex.I * modePhase n k z.1) +
        slpConstVal 0 (1 / 2) 0 * Complex.exp (Complex.I * modePhase n (negKey k) z.1) := by
      funext z
      simp only [HamExpr.eval, modePhase_negKey]
      rw [sin_eq_exp]
      simp only [slpConstVal, zpow_zero]
      push_cast
      ring_nf
    rw [e]
    exact ⟨p, h⟩
  | add a b iha ihb =>
    obtain ⟨p1, h1⟩ := iha hnv.1 s
    obtain ⟨p2, h2⟩ := ihb hnv.2 (slpCompile a s).1
    obtain ⟨p3, h3⟩ := slpAddNode_sound hS (a.jetSmoothOn hS hnv.1) (b.jetSmoothOn hS hnv.2)
      (h1.mono p2) h2
    exact ⟨(p1.trans p2).trans p3, h3⟩
  | mul a b iha ihb =>
    obtain ⟨p1, h1⟩ := iha hnv.1 s
    obtain ⟨p2, h2⟩ := ihb hnv.2 (slpCompile a s).1
    obtain ⟨p3, h3⟩ := slpMulNode_sound hS (a.jetSmoothOn hS hnv.1) (b.jetSmoothOn hS hnv.2)
      (h1.mono p2) h2
    exact ⟨(p1.trans p2).trans p3, h3⟩
  | div a b iha ihb =>
    obtain ⟨p1, h1⟩ := iha hnv.1 s
    obtain ⟨p2, h2⟩ := ihb hnv.2.1 (slpCompile a s).1
    obtain ⟨p3, h3⟩ := slpDivNode_sound hS (a.jetSmoothOn hS hnv.1) (b.jetSmoothOn hS hnv.2.1)
      hnv.2.2 (h1.mono p2) h2
    have e : (HamExpr.div a b).eval = fun z => a.eval z * (b.eval z)⁻¹ := by
      funext z; simp [HamExpr.eval, div_eq_mul_inv]
    rw [e]
    exact ⟨(p1.trans p2).trans p3, h3⟩
  | pow a m iha =>
    obtain ⟨p1, h1⟩ := iha hnv s
    obtain ⟨p2, h2⟩ := slpPowNode_sound hS (a.jetSmoothOn hS hnv) h1 m
    exact ⟨p1.trans p2, h2⟩
  | exp a iha =>
    obtain ⟨p1, h1⟩ := iha hnv s
    obtain ⟨p2, h2⟩ := slpExpNode_sound hS (a.jetSmoothOn hS hnv) h1
    exact ⟨p1.trans p2, h2⟩
  | sin a iha =>
    obtain ⟨p1, h1⟩ := iha hnv s
    obtain ⟨p2, h2⟩ := slpTrigNode_sound hS (a.jetSmoothOn hS hnv) h1 0 (-1 / 2) 0 (1 / 2)
    have e : (HamExpr.sin a).eval = fun z => slpConstVal 0 (-1 / 2) 0 *
        Complex.exp (slpConstVal 0 1 0 * a.eval z) +
        slpConstVal 0 (1 / 2) 0 * Complex.exp (slpConstVal 0 (-1) 0 * a.eval z) := by
      funext z; exact sin_eq_exp (a.eval z)
    rw [e]
    exact ⟨p1.trans p2, h2⟩
  | cos a iha =>
    obtain ⟨p1, h1⟩ := iha hnv s
    obtain ⟨p2, h2⟩ := slpTrigNode_sound hS (a.jetSmoothOn hS hnv) h1 (1 / 2) 0 (1 / 2) 0
    have e : (HamExpr.cos a).eval = fun z => slpConstVal (1 / 2) 0 0 *
        Complex.exp (slpConstVal 0 1 0 * a.eval z) +
        slpConstVal (1 / 2) 0 0 * Complex.exp (slpConstVal 0 (-1) 0 * a.eval z) := by
      funext z; exact cos_eq_exp (a.eval z)
    rw [e]
    exact ⟨p1.trans p2, h2⟩

/-- The jet of an expression: the program of `slpCompile` (after the zero slot) and the tables
of `H`, `∂_a H`, `∂_a ∂_b H`; the folded slots `none` are read from the zero slot `0`. The
table of third derivatives is left empty (SO-EXPR part B2). -/
def HamExpr.jet {n : ℕ} (e : HamExpr n) : HamJet :=
  let r := slpCompile e [.const 0 0 0]
  { prog := ⟨r.1⟩
    v0 := r.2.v
    d1 := r.2.d1.map (fun o => o.getD 0)
    d2 := r.2.d2.map (fun row => row.map (fun o => o.getD 0))
    d3 := [] }

theorem slpCompile_prefix {n : ℕ} (e : HamExpr n) :
    [SlpOp.const 0 0 0] <+: (slpCompile e [.const 0 0 0]).1 :=
  (slpCompile_sound e (S := ∅) isOpen_empty e.nonvanishingOn_empty _).1

theorem zero_slot_val (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (ops : List SlpOp)
    (h : [SlpOp.const 0 0 0] <+: ops) : (Slp.vals n z ops).getD 0 0 = 0 := by
  obtain ⟨t, rfl⟩ := h
  rw [Slp.val_append n z _ t (by simp)]
  have := Slp.val_snoc_self n z [] (SlpOp.const 0 0 0)
  simp only [List.nil_append, List.length_nil] at this
  rw [this]
  simp [SlpOp.step, slpConstVal]

theorem slpOv_eq_val (n : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) (ops : List SlpOp)
    (h : [SlpOp.const 0 0 0] <+: ops) (o : Option ℕ) :
    slpOv n ops z o = (Slp.vals n z ops).getD (o.getD 0) 0 := by
  cases o with
  | none => simpa [slpOv] using (zero_slot_val n z ops h).symm
  | some i => rfl

theorem list_getD_map {α β : Type} (f : α → β) (l : List α) (i : ℕ) (d : α) :
    (l.map f).getD i (f d) = f (l.getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

theorem HamExpr.jet_v0 {n : ℕ} (e : HamExpr n) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    e.jet.prog.val n z e.jet.v0 = e.eval z :=
  (slpCompile_sound e (S := ∅) isOpen_empty e.nonvanishingOn_empty _).2.val z

theorem HamExpr.jet_d1 {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (hnv : e.NonvanishingOn S) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ S)
    (a : Fin n ⊕ Fin n) :
    e.jet.prog.val n z (e.jet.d1.getD (phaseNat a) 0) = fderiv ℂ e.eval z (phaseBasis a) := by
  obtain ⟨hp, h⟩ := slpCompile_sound e hS hnv [.const 0 0 0]
  have hr := (h.d1 (phaseNat a) (phaseNat_lt a)).2 z hz
  rw [slpOv_eq_val n z _ hp] at hr
  have : e.jet.d1.getD (phaseNat a) 0 =
      ((slpCompile e [.const 0 0 0]).2.get1 (phaseNat a)).getD 0 := by
    simp only [HamExpr.jet, SlpNode.get1]
    exact list_getD_map (fun o : Option ℕ => o.getD 0) _ _ none
  have key : e.jet.prog.val n z (e.jet.d1.getD (phaseNat a) 0) =
      (Slp.vals n z (slpCompile e [.const 0 0 0]).1).getD (e.jet.d1.getD (phaseNat a) 0) 0 := rfl
  rw [key, this, hr, phaseBasis_eq_dirVec]
  rfl

theorem HamExpr.jet_d2 {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (hnv : e.NonvanishingOn S) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ S)
    (a b : Fin n ⊕ Fin n) :
    e.jet.prog.val n z ((e.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0) =
      iteratedFDeriv ℂ 2 e.eval z ![phaseBasis a, phaseBasis b] := by
  obtain ⟨hp, h⟩ := slpCompile_sound e hS hnv [.const 0 0 0]
  have hr := (h.d2 (phaseNat a) (phaseNat_lt a) (phaseNat b) (phaseNat_lt b)).2 z hz
  rw [slpOv_eq_val n z _ hp] at hr
  have hc : ContDiffAt ℂ 2 e.eval z :=
    ((e.contDiffOn_eval hS hnv).contDiffAt (hS.mem_nhds hz)).of_le le_top
  have : (e.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0 =
      ((slpCompile e [.const 0 0 0]).2.get2 (phaseNat a) (phaseNat b)).getD 0 := by
    simp only [HamExpr.jet, SlpNode.get2]
    have h1 : (List.map (fun row => List.map (fun o : Option ℕ => o.getD 0) row)
        (slpCompile e [.const 0 0 0]).2.d2).getD (phaseNat a) [] =
        ((slpCompile e [.const 0 0 0]).2.d2.getD (phaseNat a) []).map
          (fun o : Option ℕ => o.getD 0) :=
      list_getD_map (fun row => List.map (fun o : Option ℕ => o.getD 0) row) _ _ []
    rw [h1]
    exact list_getD_map (fun o : Option ℕ => o.getD 0) _ _ none
  have key : e.jet.prog.val n z ((e.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0) =
      (Slp.vals n z (slpCompile e [.const 0 0 0]).1).getD
        ((e.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0) 0 := rfl
  rw [key, this, hr, iteratedFDeriv_two_eq_jetDeriv hc, phaseBasis_eq_dirVec,
    phaseBasis_eq_dirVec]

end KAM.Certificate

end
