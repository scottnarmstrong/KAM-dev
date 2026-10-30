/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.SegBridges
public import KAM.CertificateSharp.Kernel.SegOne
public import KAM.Certificate.Arith.Rat

/-!
# Segmented composition tests (`Kernel/Seg*`)

On a copy of the `n = 1` toy of `Certificate/Tests/Compose.lean` (11 operations: an action,
constants, a scalar product, two characters sharing one witness through `conjReflect`, sums, a
product, an `exp` and an `inv` witness), in `ℚ`, every check is decided by `decide +kernel`:

* **Positive**: a two-segment checkpoint `[0, 5)`, `[5, 11)` for the wanted slot `10`. The dead
  infallible operations `2, 5, 6` are skipped, and the fallible `3, 4, 7, 8` always run. The ledger
  and metadata are computed by the landed `composeOps`. `planOk` and both `segOk` pass, and
  `ComposeCkpt.compose_eq` then gives `Slp.compose … [10]` without evaluating it.
* **Negative** (each a single corruption; the check fails closed): an export with a wrong radius,
  an export with a wrong cached norm, a missing import, a dead read, a wrong exp counter, a
  reordered cache, a malformed initial meta, a non-tiling plan.
* **`shadowRun_agree_needs_hR`** (design audit 2, F1): without the domain premise `hR` the agreement
  conclusion is false (a skipped dead `const` retained by `fun _ => True`).
* **Bool reflection**: `HamJet.segBeq` of a jet with itself, and of a jet with one operation
  changed.
-/

@[expose] public section

namespace KAM.Certificate

open CertArith

/-! ### The toy (a copy of `Certificate/Tests/Compose.lean`'s, exposed for kernel reduction) -/

def segToyW : CertWeight := ⟨1 / 100, 11 / 10⟩

def segToyPi : PiEnclosure ℚ := ⟨314159 / 100000, 1 / 10000, 5, 2⟩

/-- `x` rounded down to `10⁻¹²`. -/
def segToyRound (x : ℚ) : ℚ := ((x.num * 10 ^ 12 / x.den : ℤ) : ℚ) / 10 ^ 12

/-- `J_k(a)`, twelve terms of the series. -/
def segToyJ (a : ℚ) (k : ℕ) : ℚ :=
  ((List.range 12).map fun m =>
    (-1) ^ m * (a / 2) ^ (2 * m + k) / ((m.factorial * (m + k).factorial : ℕ) : ℚ)).sum

/-- `i^m x`. -/
def segToyIPow (m : ℕ) (x : ℚ) : CC ℚ :=
  match m % 4 with
  | 0 => ⟨x, 0⟩
  | 1 => ⟨0, x⟩
  | 2 => ⟨-x, 0⟩
  | _ => ⟨0, -x⟩

/-- The keys `-K, …, K`. -/
def segToyRange (K : ℕ) : List ℤ := (List.range (2 * K + 1)).map fun i => (i : ℤ) - K

/-- `exp(i a cos 2πθ₁) ≈ Σ_{|k| ≤ 5} i^{|k|} J_{|k|}(a) χ_{(k, 0, …)}` (`pad` zeros appended). -/
def segToyCharE (a : ℚ) (pad : List ℤ) (h : ℕ) : ExpWitness ℚ :=
  ⟨⟨(segToyRange 5).map fun k =>
    (k :: pad, segToyIPow k.natAbs (segToyRound (segToyJ a k.natAbs)))⟩, h, 20⟩

/-- `0.1 cos 2πθ₁` with the constant `c` (keys padded by `pad`). -/
def segToyCos (c : ℚ) (pad : List ℤ) : CertRealPoly ℚ := ⟨c, [(1 :: pad, ⟨1 / 20, 0⟩)]⟩

/-- `K(θ) = (θ + U/2π, A)`, `U = c + 0.1 cos 2πθ`, `A = 1 + 0.1 cos 2πθ`. -/
def segToyK (c : ℚ) : CertEmbedding ℚ :=
  ⟨[-1], [segToyCos c []], [0], [segToyCos 1 []]⟩

def segToyProg : Slp :=
  ⟨[.action 0, .const (1 / 2) 0 0, .mul 1 0, .char [1], .char [-1], .add 3 4, .mul 2 5,
    .exp 1, .inv 0, .const 0 1 (-1), .add 9 1]⟩

/-- `1/(1 + 0.1 cos 2πθ) ≈ s Σ_{|k| ≤ 6} (-r)^{|k|} χ_k`, `s = 1/√0.99`, `r = 10(1 - √0.99)`. -/
def segToyInv : CertPoly ℚ :=
  ⟨(segToyRange 6).map fun k =>
    ([k], ⟨segToyRound (10050378152592 / 10 ^ 13 * (-501256289 / 10 ^ 10) ^ k.natAbs), 0⟩)⟩

def segToyWit (h : ℕ) : Witnesses ℚ :=
  ⟨[⟨⟨[([0], ⟨16487212707 / 10 ^ 10, 0⟩)]⟩, 0, 20⟩], [segToyInv],
    [([1], segToyCharE (1 / 10) [] h)], []⟩

def segToyCfg : ModelConfig ℚ :=
  ⟨100, 10, 4, fun _ _ => none,
    [([0, 6], .direct), ([2, 0], .direct), ([1, 0, 0], .direct), ([1, 1, 0], .direct)]⟩


/-- The landed state after the first `k` operations of the toy program. -/
def segTestState (k : ℕ) : ComposeState ℚ :=
  (composeOps 1 (segToyK 0) (segToyWit 0) segToyW segToyCfg segToyPi
    (segToyProg.ops.take k)).getD ⟨[], 0, 0, 0, []⟩

def segTestSegs : List SegSpec :=
  [⟨0, 5, [0, 1, 3, 4], [], [0, 1]⟩, ⟨5, 11, [7, 8, 9, 10], [0, 1], [10]⟩]

def segTestLedger : List (ℕ × (CertModel ℚ × ℚ)) :=
  [0, 1, 10].map fun i => (i, (segTestState 11).slot segToyW i)

def segTestCkpt : ComposeCkpt ℚ :=
  ⟨segTestSegs, [(segTestState 0).stateMeta, (segTestState 5).stateMeta,
    (segTestState 11).stateMeta], segTestLedger⟩

/-- The segment check of the toy, segment `j`, on a checkpoint `C`. -/
def segTestOk (C : ComposeCkpt ℚ) (j : ℕ) : Bool :=
  C.segOk 1 segToyProg.ops (segToyK 0) (segToyWit 0) segToyW segToyCfg
    segToyPi j

theorem segTest_plan : segTestCkpt.planOk segToyProg.ops.length = true := by decide +kernel

theorem segTest_seg0 : segTestOk segTestCkpt 0 = true := by decide +kernel

theorem segTest_seg1 : segTestOk segTestCkpt 1 = true := by decide +kernel

theorem segTest_wanted : segTestCkpt.wantedOk [10] = true := by decide +kernel

/-- The chain: the landed composition of slot `10` from the two segment checks. -/
theorem segTest_compose :
    Slp.compose 1 segToyProg (segToyK 0) (segToyWit 0) segToyW segToyCfg
      segToyPi [10] = some [(segTestCkpt.slotPair segToyW 10).1] :=
  ComposeCkpt.compose_eq 1 _ _ _ _ _ segTestCkpt segTest_plan
    (fun j hj => by
      have hj' : j < 2 := hj
      interval_cases j
      · exact segTest_seg0
      · exact segTest_seg1)
    segTest_wanted

/-! ### Negative controls -/

/-- The ledger with slot `i`'s pair modified by `f`. -/
def segTestCorrupt (i : ℕ) (f : CertModel ℚ × ℚ → CertModel ℚ × ℚ) : ComposeCkpt ℚ :=
  { segTestCkpt with ledger := segTestLedger.map fun e => if e.1 = i then (e.1, f e.2) else e }

/-- An export with a wrong radius. -/
theorem segTest_badRadius :
    segTestOk (segTestCorrupt 10 fun p => ({ p.1 with rad := p.1.rad + 1 }, p.2)) 1 = false := by
  decide +kernel

/-- An export with a wrong cached norm. -/
theorem segTest_badNorm : segTestOk (segTestCorrupt 10 fun p => (p.1, p.2 + 1)) 1 = false := by
  decide +kernel

/-- A missing import (slot `1` is read by the live operations `7` and `10`). -/
theorem segTest_missingImport :
    segTestOk { segTestCkpt with
      segs := [⟨0, 5, [0, 1, 3, 4], [], [0, 1]⟩, ⟨5, 11, [7, 8, 9, 10], [0], [10]⟩] } 1 =
        false := by
  decide +kernel

/-- A dead read: slot `9` is not live but is read by the live slot `10`. -/
theorem segTest_deadRead :
    segTestOk { segTestCkpt with
      segs := [⟨0, 5, [0, 1, 3, 4], [], [0, 1]⟩, ⟨5, 11, [7, 8, 10], [0, 1], [10]⟩] } 1 =
        false := by
  decide +kernel

/-- A wrong exp counter in the final metadata. -/
theorem segTest_badCounter :
    segTestOk { segTestCkpt with
      metas := [(segTestState 0).stateMeta, (segTestState 5).stateMeta,
        { (segTestState 11).stateMeta with nExp := 0 }] } 1 = false := by
  decide +kernel

/-- The character cache in the wrong order at the boundary. -/
theorem segTest_badCacheOrder :
    segTestOk { segTestCkpt with
      metas := [(segTestState 0).stateMeta,
        { (segTestState 5).stateMeta with cache := (segTestState 5).cache.reverse },
        (segTestState 11).stateMeta] } 0 = false := by
  decide +kernel

/-- A malformed initial metadata. -/
theorem segTest_badInitMeta :
    ({ segTestCkpt with
      metas := [{ (segTestState 0).stateMeta with len := 1 }, (segTestState 5).stateMeta,
        (segTestState 11).stateMeta] } : ComposeCkpt ℚ).planOk segToyProg.ops.length = false := by
  decide +kernel

/-- A plan whose segments do not tile the program. -/
theorem segTest_badTiling :
    ({ segTestCkpt with
      segs := [⟨0, 5, [0, 1, 3, 4], [], [0, 1]⟩, ⟨6, 11, [7, 8, 9, 10], [0, 1], [10]⟩] } :
      ComposeCkpt ℚ).planOk segToyProg.ops.length = false := by
  decide +kernel

/-! ### The domain premise of `shadowRun_agree` -/

/-- **Negative contract test** (design audit 2, F1): the agreement conclusion fails for the retained
set `fun _ => True`, which violates `hR`, on a one-op segment whose dead `const` is skipped. -/
theorem shadowRun_agree_needs_hR {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α)
    (wit : Witnesses α) (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) :
    shadowRun n K wit W cfg pe ⟨0, 1, [], [], []⟩ (some ⟨[], 0, 0, 0, []⟩) [.const 0 0 1] =
        some ((⟨[], 0, 0, 0, []⟩ : ComposeState α).pushSlot W zeroModel) ∧
      composeOpsAux n K wit W cfg pe (some ⟨[], 0, 0, 0, []⟩) [.const 0 0 1] =
        some ((⟨[], 0, 0, 0, []⟩ : ComposeState α).pushSlot W (constModel n 0 0 1)) ∧
      ¬ ((⟨[], 0, 0, 0, []⟩ : ComposeState α).pushSlot W zeroModel).AgreeOn W (fun _ => True)
        ((⟨[], 0, 0, 0, []⟩ : ComposeState α).pushSlot W (constModel n 0 0 1)) := by
  refine ⟨rfl, rfl, fun h => ?_⟩
  have h0 := h.2.2.2.2 0 trivial (Nat.zero_lt_succ 0)
  have h1 := congrArg (fun p : CertModel α × α => p.1.deg) h0
  change (0 : ℤ) = 1 at h1
  exact absurd h1 (by decide)

/-! ### Jet equality -/

def segTestJet : HamJet := ⟨segToyProg, 10, [6, 10], [[2]], [[[5]]]⟩

theorem segTest_jetBeq : segTestJet.segBeq segTestJet = true := by decide +kernel

theorem segTest_jetBeq_ne :
    segTestJet.segBeq { segTestJet with prog := ⟨segToyProg.ops.set 6 (.mul 2 4)⟩ } = false := by
  decide +kernel

theorem segTest_jet_eq : segTestJet = segTestJet := HamJet.eq_of_segBeq segTest_jetBeq

end KAM.Certificate
