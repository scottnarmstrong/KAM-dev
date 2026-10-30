/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.DiffNode
public import KAM.Certificate.Expr.DiffCalculusSqrt

/-!
# The jet node of the total square root

The node of `√x` emits the operations `V = sqrt x`, `w = V⁻¹`, `w²`, `w³ = w · w²` and
`w⁵ = w² · w³` after its operand, and builds its derivative tables from the rules of
`KAM.Certificate.Expr.DiffCalculusSqrt`:
`½ w x_i`, `½ w x_ij - ¼ w³ x_i x_j` and
`⅜ w⁵ x_i x_j x_k - ¼ w³ (x_ij x_k + x_j x_ik + x_i x_jk) + ½ w x_ijk`.
On an open set where the operand has positive real part, the node is sound (`slpSqrtNode_sound`).
The value slot `V` is `sqrtE x` everywhere.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM

variable {n : ℕ}

local notation "Ph" => (Fin n → ℂ) × (Fin n → ℂ)

/-- The third derivative entry of `√x` from the slots `w`, `w³`, `w⁵` (`w = (√x)⁻¹`). -/
def slpSqrtD3 (w1 w3 w5 : Option ℕ) (A : SlpNode) (i j k : ℕ) : SlpComp :=
  slpCAdd (slpCScale (3 / 8) 0 0 (slpCMul (slpPure w5) (slpCMul (slpPure (A.get1 i))
    (slpCMul (slpPure (A.get1 j)) (slpPure (A.get1 k))))))
    (slpCAdd (slpCScale (-1 / 4) 0 0 (slpCMul (slpPure w3) (slpCross A i j k)))
      (slpCScale (1 / 2) 0 0 (slpCMul (slpPure w1) (slpPure (A.get3 i j k)))))

/-- The derivative tables of `√x` from the slots `w`, `w³` and `w⁵` (`w = (√x)⁻¹`). -/
def slpSqrtTail (n : ℕ) (v : ℕ) (A : SlpNode) (w1 w3 w5 : Option ℕ) (s : List SlpOp) :
    List SlpOp × SlpNode :=
  slpFinish n v
    (fun i => slpCScale (1 / 2) 0 0 (slpCMul (slpPure w1) (slpPure (A.get1 i))))
    (fun i j => slpCAdd
      (slpCScale (1 / 2) 0 0 (slpCMul (slpPure w1) (slpPure (A.get2 i j))))
      (slpCScale (-1 / 4) 0 0 (slpCMul (slpPure w3) (slpCMul (slpPure (A.get1 i))
        (slpPure (A.get1 j))))))
    (slpSqrtD3 w1 w3 w5 A) s

theorem slpSqrtTail_sound {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ} (hf : JetSmoothOn S f)
    (hpos : ∀ z ∈ S, 0 < (f z).re) {s : List SlpOp} {A : SlpNode} (hA : A.Sound n S f s)
    {v : ℕ} (hv : v < s.length) (hval : ∀ z, (Slp.vals n z s).getD v 0 = sqrtE (f z))
    {w1 w3 w5 : Option ℕ} (hw1 : Realizes n S s w1 (fun z => (sqrtE (f z))⁻¹))
    (hw3 : Realizes n S s w3
      (fun z => (sqrtE (f z))⁻¹ * ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹)))
    (hw5 : Realizes n S s w5 (fun z => ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹) *
      ((sqrtE (f z))⁻¹ * ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹)))) :
    s <+: (slpSqrtTail n v A w1 w3 w5 s).1 ∧
      (slpSqrtTail n v A w1 w3 w5 s).2.Sound n S (fun z => sqrtE (f z))
        (slpSqrtTail n v A w1 w3 w5 s).1 := by
  have h1 : ∀ i < 2 * n, SlpEnt n S s
      (slpCScale (1 / 2) 0 0 (slpCMul (slpPure w1) (slpPure (A.get1 i))))
      (jetDeriv (dirVec n i) (fun z => sqrtE (f z))) := by
    intro i hi
    refine (((SlpEnt.pure hw1).mul (SlpEnt.pure (hA.d1 i hi))).scale (1 / 2) 0 0).congr ?_
    intro z hz
    rw [jetDeriv_sqrtE hS _ hf hpos hz]
    beta_reduce
    rw [slpConstVal_rat]
    push_cast
    ring
  have h2 : ∀ i < 2 * n, ∀ j < 2 * n, SlpEnt n S s
      (slpCAdd
        (slpCScale (1 / 2) 0 0 (slpCMul (slpPure w1) (slpPure (A.get2 i j))))
        (slpCScale (-1 / 4) 0 0 (slpCMul (slpPure w3) (slpCMul (slpPure (A.get1 i))
          (slpPure (A.get1 j))))))
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (fun z => sqrtE (f z)))) := by
    intro i hi j hj
    refine ((((SlpEnt.pure hw1).mul (SlpEnt.pure (hA.d2 i hi j hj))).scale (1 / 2) 0 0).add
      (((SlpEnt.pure hw3).mul ((SlpEnt.pure (hA.d1 i hi)).mul
        (SlpEnt.pure (hA.d1 j hj)))).scale (-1 / 4) 0 0)).congr ?_
    intro z hz
    rw [jetDeriv2_sqrtE hS _ _ hf hpos hz]
    beta_reduce
    rw [slpConstVal_rat, slpConstVal_rat]
    push_cast
    ring
  have h3 : ∀ i < 2 * n, ∀ j < 2 * n, ∀ k < 2 * n, SlpEnt n S s (slpSqrtD3 w1 w3 w5 A i j k)
      (jetDeriv (dirVec n i) (jetDeriv (dirVec n j) (jetDeriv (dirVec n k)
        (fun z => sqrtE (f z))))) := by
    intro i hi j hj k hk
    unfold slpSqrtD3
    refine ((((SlpEnt.pure hw5).mul ((SlpEnt.pure (hA.d1 i hi)).mul
      ((SlpEnt.pure (hA.d1 j hj)).mul (SlpEnt.pure (hA.d1 k hk))))).scale (3 / 8) 0 0).add
      ((((SlpEnt.pure hw3).mul (slpCross_ent hA hi hj hk)).scale (-1 / 4) 0 0).add
      (((SlpEnt.pure hw1).mul (SlpEnt.pure (hA.d3 i hi j hj k hk))).scale (1 / 2) 0 0))).congr ?_
    intro z hz
    rw [jetDeriv3_sqrtE hS _ _ _ hf hpos hz]
    beta_reduce
    rw [slpConstVal_rat, slpConstVal_rat, slpConstVal_rat]
    push_cast
    ring
  exact slpFinish_sound hv hval _ _ _ h1 h2 h3

/-- The program of the node of `√x` before its tables: the operations `V = √x`, `w = V⁻¹`,
`w²`, `w³`, `w⁵` and the slots of `w`, `w³`, `w⁵`. -/
def slpSqrtPre (s : List SlpOp) (A : SlpNode) :
    List SlpOp × Option ℕ × Option ℕ × Option ℕ :=
  let r0 := slpEmit s (.sqrt A.v)
  let r1 := slpEmit r0.1 (.inv s.length)
  let r2 := slpMulO r1.1 r1.2 r1.2
  let r3 := slpMulO r2.1 r1.2 r2.2
  let r5 := slpMulO r3.1 r2.2 r3.2
  (r5.1, r1.2, r3.2, r5.2)

/-- The node of `√x`: the slots `V = √x`, `w = V⁻¹`, `w²`, `w³`, `w⁵` follow the operand. -/
def slpSqrtNode (n : ℕ) (s : List SlpOp) (A : SlpNode) : List SlpOp × SlpNode :=
  slpSqrtTail n s.length A (slpSqrtPre s A).2.1 (slpSqrtPre s A).2.2.1 (slpSqrtPre s A).2.2.2
    (slpSqrtPre s A).1

theorem slpSqrtPre_emit_prefix (s : List SlpOp) (A : SlpNode) :
    s ++ [SlpOp.sqrt A.v] <+: (slpSqrtPre s A).1 := by
  have m : ∀ (t : List SlpOp) (a b : Option ℕ), t <+: (slpMulO t a b).1 := fun t a b => by
    cases a <;> cases b <;> simp [slpMulO, slpEmit]
  exact (slpEmit_prefix _ _).trans ((m _ _ _).trans ((m _ _ _).trans (m _ _ _)))

theorem slpSqrtPre_spec {S : Set Ph} {f : Ph → ℂ} {s : List SlpOp} {A : SlpNode}
    (hA : A.Sound n S f s) :
    s <+: (slpSqrtPre s A).1 ∧ s.length < (slpSqrtPre s A).1.length ∧
      (∀ z, (Slp.vals n z (slpSqrtPre s A).1).getD s.length 0 = sqrtE (f z)) ∧
      Realizes n S (slpSqrtPre s A).1 (slpSqrtPre s A).2.1 (fun z => (sqrtE (f z))⁻¹) ∧
      Realizes n S (slpSqrtPre s A).1 (slpSqrtPre s A).2.2.1
        (fun z => (sqrtE (f z))⁻¹ * ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹)) ∧
      Realizes n S (slpSqrtPre s A).1 (slpSqrtPre s A).2.2.2
        (fun z => ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹) *
          ((sqrtE (f z))⁻¹ * ((sqrtE (f z))⁻¹ * (sqrtE (f z))⁻¹))) := by
  have hp0 : s <+: (slpEmit s (.sqrt A.v)).1 := slpEmit_prefix _ _
  have hV0 : ∀ z, (Slp.vals n z (slpEmit s (.sqrt A.v)).1).getD s.length 0 = sqrtE (f z) := by
    intro z
    simp only [slpEmit]
    rw [Slp.val_snoc_self]
    simp only [SlpOp.step]
    rw [hA.val z]
  have hp1 : (slpEmit s (.sqrt A.v)).1 <+:
      (slpEmit (slpEmit s (.sqrt A.v)).1 (.inv s.length)).1 := slpEmit_prefix _ _
  have hw : Realizes n S (slpEmit (slpEmit s (.sqrt A.v)).1 (.inv s.length)).1
      (slpEmit (slpEmit s (.sqrt A.v)).1 (.inv s.length)).2 (fun z => (sqrtE (f z))⁻¹) :=
    slpEmit_realizes _ _ _ fun z _ => by simp only [SlpOp.step]; rw [hV0 z]
  obtain ⟨p2, hw2⟩ := slpMulO_spec hw hw
  obtain ⟨p3, hw3⟩ := slpMulO_spec (hw.mono p2) hw2
  obtain ⟨p5, hw5⟩ := slpMulO_spec (hw2.mono p3) hw3
  have hvlt : s.length < (slpEmit s (.sqrt A.v)).1.length := by simp [slpEmit]
  have hall := hp1.trans (p2.trans (p3.trans p5))
  refine ⟨hp0.trans hall, hvlt.trans_le hall.length_le, fun z => ?_,
    ((hw.mono p2).mono p3).mono p5, hw3.mono p5, hw5⟩
  obtain ⟨t, ht⟩ := hall
  show (Slp.vals n z (slpMulO _ _ _).1).getD s.length 0 = _
  rw [← ht, Slp.val_append n z _ t hvlt]
  exact hV0 z

theorem slpSqrtNode_sound {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ} (hf : JetSmoothOn S f)
    (hpos : ∀ z ∈ S, 0 < (f z).re) {s : List SlpOp} {A : SlpNode} (hA : A.Sound n S f s) :
    s <+: (slpSqrtNode n s A).1 ∧
      (slpSqrtNode n s A).2.Sound n S (fun z => sqrtE (f z)) (slpSqrtNode n s A).1 := by
  obtain ⟨hp, hvlt, hval, hw1, hw3, hw5⟩ := slpSqrtPre_spec hA
  obtain ⟨p, h⟩ := slpSqrtTail_sound hS hf hpos (hA.mono hp) hvlt hval hw1 hw3 hw5
  exact ⟨hp.trans p, h⟩

/-- The node program begins with the emitted `sqrt` operation. -/
theorem slpSqrtNode_emit_prefix {S : Set Ph} (hS : IsOpen S) {f : Ph → ℂ}
    (hf : JetSmoothOn S f) (hpos : ∀ z ∈ S, 0 < (f z).re) {s : List SlpOp} {A : SlpNode}
    (hA : A.Sound n S f s) : s ++ [SlpOp.sqrt A.v] <+: (slpSqrtNode n s A).1 := by
  obtain ⟨hp, hvlt, hval, hw1, hw3, hw5⟩ := slpSqrtPre_spec hA
  obtain ⟨p, -⟩ := slpSqrtTail_sound hS hf hpos (hA.mono hp) hvlt hval hw1 hw3 hw5
  exact (slpSqrtPre_emit_prefix s A).trans p

end KAM.Certificate

end
