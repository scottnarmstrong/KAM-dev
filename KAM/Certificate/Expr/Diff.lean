/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.DiffBuf

/-!
# The symbolic jet of a Hamiltonian expression, to third order

`HamExpr.jet` compiles an expression to a straight-line program with forward-mode derivative
slots (`slpCompile`): every sub-expression is compiled once and its value, first, second and third
derivative slots are shared by its parents. Sine and cosine of an expression and of a mode are
compiled through `exp` and the characters `e^{±2πi k·θ}`; a quotient is a product with an
`inv` node; a power is repeated multiplication; a square root is a `sqrt` node
(`slpSqrtNode`). No operation is ever dropped from the program (only derivative slots that vanish
identically are folded), so every `inv` and `sqrt` operand of the source stays in the program, as
the ball arithmetic of `Expr/Ball` requires.

The values are those of `HamExpr.eval` everywhere (`jet_v0`), and on an open set where the
denominators are nonvanishing the tables are the first, second and third derivatives (`jet_d1`,
`jet_d2`, `jet_d3`).
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM

variable {n : ℕ}

local notation "Ph" => (Fin n → ℂ) × (Fin n → ℂ)

/-- The jet of an expression, built by the specification compiler `slpCompile` (after the zero
slot): its program and the tables of `H`, `∂_a H`, `∂_a ∂_b H`, `∂_a ∂_b ∂_c H`; the folded slots
`none` are read from the zero slot `0`. Equal to `HamExpr.jet` (`HamExpr.jet_eq`). -/
def HamExpr.jetAppend {n : ℕ} (e : HamExpr n) : HamJet :=
  let r := slpCompile e [.const 0 0 0]
  { prog := ⟨r.1⟩
    v0 := r.2.v
    d1 := r.2.d1.map (fun o => o.getD 0)
    d2 := r.2.d2.map (fun row => row.map (fun o => o.getD 0))
    d3 := r.2.d3.map (fun tab => tab.map (fun row => row.map (fun o => o.getD 0))) }

/-- The jet of an expression: the program of `slpCompile` (after the zero slot) and the tables
of `H`, `∂_a H`, `∂_a ∂_b H`, `∂_a ∂_b ∂_c H`; the folded slots `none` are read from the zero
slot `0`. It runs the buffer compiler `slpCompileB`, which the kernel evaluates without deep
recursion; the result is that of `slpCompile` (`HamExpr.jet_eq`). -/
def HamExpr.jet {n : ℕ} (e : HamExpr n) : HamJet :=
  let r := slpCompileB e ⟨[.const 0 0 0], 1⟩
  { prog := ⟨r.1.opList⟩
    v0 := r.2.v
    d1 := r.2.d1.map (fun o => o.getD 0)
    d2 := r.2.d2.map (fun row => row.map (fun o => o.getD 0))
    d3 := r.2.d3.map (fun tab => tab.map (fun row => row.map (fun o => o.getD 0))) }

/-- The jet is the jet of the specification compiler: same program, same slot tables. -/
theorem HamExpr.jet_eq {n : ℕ} (e : HamExpr n) : e.jet = e.jetAppend := by
  have h := slpCompileB_ofOpList e [.const 0 0 0]
  have h0 : (⟨[.const 0 0 0], 1⟩ : SlpBuf) = SlpBuf.ofOpList [.const 0 0 0] := rfl
  simp only [HamExpr.jet, HamExpr.jetAppend, h0, h, SlpBuf.opList_ofOpList]

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
    e.jet.prog.val n z e.jet.v0 = e.eval z := by
  rw [HamExpr.jet_eq]
  exact (slpCompile_sound e (S := ∅) isOpen_empty e.nonvanishingOn_empty _).2.val z

theorem HamExpr.jet_d1 {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (hnv : e.NonvanishingOn S) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ S)
    (a : Fin n ⊕ Fin n) :
    e.jet.prog.val n z (e.jet.d1.getD (phaseNat a) 0) = fderiv ℂ e.eval z (phaseBasis a) := by
  rw [HamExpr.jet_eq]
  obtain ⟨hp, h⟩ := slpCompile_sound e hS hnv [.const 0 0 0]
  have hr := (h.d1 (phaseNat a) (phaseNat_lt a)).2 z hz
  rw [slpOv_eq_val n z _ hp] at hr
  have : e.jetAppend.d1.getD (phaseNat a) 0 =
      ((slpCompile e [.const 0 0 0]).2.get1 (phaseNat a)).getD 0 := by
    simp only [HamExpr.jetAppend, SlpNode.get1]
    exact list_getD_map (fun o : Option ℕ => o.getD 0) _ _ none
  have key : e.jetAppend.prog.val n z (e.jetAppend.d1.getD (phaseNat a) 0) =
      (Slp.vals n z (slpCompile e [.const 0 0 0]).1).getD
        (e.jetAppend.d1.getD (phaseNat a) 0) 0 := rfl
  rw [key, this, hr, phaseBasis_eq_dirVec]
  rfl

theorem HamExpr.jet_d2 {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (hnv : e.NonvanishingOn S) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ S)
    (a b : Fin n ⊕ Fin n) :
    e.jet.prog.val n z ((e.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0) =
      iteratedFDeriv ℂ 2 e.eval z ![phaseBasis a, phaseBasis b] := by
  rw [HamExpr.jet_eq]
  obtain ⟨hp, h⟩ := slpCompile_sound e hS hnv [.const 0 0 0]
  have hr := (h.d2 (phaseNat a) (phaseNat_lt a) (phaseNat b) (phaseNat_lt b)).2 z hz
  rw [slpOv_eq_val n z _ hp] at hr
  have hc : ContDiffAt ℂ 2 e.eval z :=
    ((e.contDiffOn_eval hS hnv).contDiffAt (hS.mem_nhds hz)).of_le le_top
  have : (e.jetAppend.d2.getD (phaseNat a) []).getD (phaseNat b) 0 =
      ((slpCompile e [.const 0 0 0]).2.get2 (phaseNat a) (phaseNat b)).getD 0 := by
    simp only [HamExpr.jetAppend, SlpNode.get2]
    have h1 : (List.map (fun row => List.map (fun o : Option ℕ => o.getD 0) row)
        (slpCompile e [.const 0 0 0]).2.d2).getD (phaseNat a) [] =
        ((slpCompile e [.const 0 0 0]).2.d2.getD (phaseNat a) []).map
          (fun o : Option ℕ => o.getD 0) :=
      list_getD_map (fun row => List.map (fun o : Option ℕ => o.getD 0) row) _ _ []
    rw [h1]
    exact list_getD_map (fun o : Option ℕ => o.getD 0) _ _ none
  have key : e.jetAppend.prog.val n z
      ((e.jetAppend.d2.getD (phaseNat a) []).getD (phaseNat b) 0) =
      (Slp.vals n z (slpCompile e [.const 0 0 0]).1).getD
        ((e.jetAppend.d2.getD (phaseNat a) []).getD (phaseNat b) 0) 0 := rfl
  rw [key, this, hr, iteratedFDeriv_two_eq_jetDeriv hc, phaseBasis_eq_dirVec,
    phaseBasis_eq_dirVec]

theorem HamExpr.jet_d3 {n : ℕ} (e : HamExpr n) {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hS : IsOpen S) (hnv : e.NonvanishingOn S) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ S)
    (a b c : Fin n ⊕ Fin n) :
    e.jet.prog.val n z
        (((e.jet.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD (phaseNat c) 0) =
      iteratedFDeriv ℂ 3 e.eval z ![phaseBasis a, phaseBasis b, phaseBasis c] := by
  rw [HamExpr.jet_eq]
  obtain ⟨hp, h⟩ := slpCompile_sound e hS hnv [.const 0 0 0]
  have hr := (h.d3 (phaseNat a) (phaseNat_lt a) (phaseNat b) (phaseNat_lt b) (phaseNat c)
    (phaseNat_lt c)).2 z hz
  rw [slpOv_eq_val n z _ hp] at hr
  have : ((e.jetAppend.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD (phaseNat c) 0 =
      ((slpCompile e [.const 0 0 0]).2.get3 (phaseNat a) (phaseNat b) (phaseNat c)).getD 0 := by
    simp only [HamExpr.jetAppend, SlpNode.get3]
    have h1 : (List.map (fun tab => List.map (fun row => List.map (fun o : Option ℕ => o.getD 0)
        row) tab) (slpCompile e [.const 0 0 0]).2.d3).getD (phaseNat a) [] =
        ((slpCompile e [.const 0 0 0]).2.d3.getD (phaseNat a) []).map
          (fun row => row.map (fun o : Option ℕ => o.getD 0)) :=
      list_getD_map (fun tab => List.map (fun row => List.map (fun o : Option ℕ => o.getD 0)
        row) tab) _ _ []
    have h2 : (((slpCompile e [.const 0 0 0]).2.d3.getD (phaseNat a) []).map
        (fun row => row.map (fun o : Option ℕ => o.getD 0))).getD (phaseNat b) [] =
        (((slpCompile e [.const 0 0 0]).2.d3.getD (phaseNat a) []).getD (phaseNat b) []).map
          (fun o : Option ℕ => o.getD 0) :=
      list_getD_map (fun row => row.map (fun o : Option ℕ => o.getD 0)) _ _ []
    rw [h1, h2]
    exact list_getD_map (fun o : Option ℕ => o.getD 0) _ _ none
  have key : e.jetAppend.prog.val n z
      (((e.jetAppend.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD (phaseNat c) 0) =
      (Slp.vals n z (slpCompile e [.const 0 0 0]).1).getD
        (((e.jetAppend.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD (phaseNat c) 0) 0 := rfl
  rw [key, this, hr, iteratedFDeriv_three_eq_jetDeriv hS (e.jetSmoothOn hS hnv) hz,
    phaseBasis_eq_dirVec, phaseBasis_eq_dirVec, phaseBasis_eq_dirVec]

end KAM.Certificate

end
