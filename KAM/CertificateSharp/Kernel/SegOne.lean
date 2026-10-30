/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.SegAgree

/-!
# Segmented composition: one-op segments (SO-CSEG-A/B, design §3.5, L1b)

A segment of a single operation that contains a packed product (the lunar slots 10 and 28) is not
decided whole: `ComposeCkpt.segOk_one_of` proves its `segOk` from the prefix check (S1, S2), its one
step, and the result check (S3 metadata, S4); `segOk` itself is never assumed. The step is proved by
rewriting with the arm equations of the landed `composeStep` (`composeStep_mul_eq`, …),
`seed_slot_of_mem` (`SegAgree.lean`) and the memoized products (`ProductSplit.lean`).
-/

@[expose] public section

namespace KAM.Certificate

open KAM KAM.CertificateSharp CertArith

variable {α : Type} [CertArith α]

theorem shadowStep_of_live (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) {s : SegSpec} {st : ComposeState α} {op : SlpOp}
    (h : s.live.contains st.len = true) :
    shadowStep n K wit W cfg pe s st op = composeStep n K wit W cfg pe st op := by
  simp only [shadowStep, h, Bool.true_or, ↓reduceIte]

/-- A one-op segment from its prefix check (S1, S2), its single step, and its result check (S3
metadata, S4). `segOk` itself is never assumed. -/
theorem ComposeCkpt.segOk_one_of [DecidableEq α] {C : ComposeCkpt α} {n : ℕ} {ops : List SlpOp}
    {K : CertEmbedding α} {wit : Witnesses α} {W : CertWeight} {cfg : ModelConfig α}
    {pe : PiEnclosure α} {j : ℕ} {s : SegSpec} {m : ComposeMeta α} {op : SlpOp}
    {st' : ComposeState α}
    (hs : C.segs[j]? = some s) (hm : C.metas[j]? = some m)
    (hone : s.ops ops = [op])
    (hprefix : C.segPrefixOk ops j = true)
    (hop : shadowStep n K wit W cfg pe s (ComposeState.seed W m C s.imports) op = some st')
    (hresult : C.segResultOk W ops j st' = true) :
    C.segOk n ops K wit W cfg pe j = true := by
  simp only [ComposeCkpt.segOk, hprefix, hs, hm, hone, shadowRun, hop, hresult, Bool.true_and]

/-! ### The arms of the landed step -/

theorem composeStep_const_eq (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (st : ComposeState α) (re im : ℚ) (d : ℤ) :
    composeStep n K wit W cfg pe st (.const re im d) =
      some (st.pushSlot W (constModel n re im d)) :=
  rfl

theorem composeStep_add_eq (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (st : ComposeState α) (a b : ℕ) :
    composeStep n K wit W cfg pe st (.add a b) =
      some (st.pushSlot W (CertModel.add W (st.slot W a).1
        (CertModel.toDeg W pe (st.slot W a).1.deg (st.slot W b).1))) :=
  rfl

theorem composeStep_mul_eq (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (st : ComposeState α) (a b : ℕ) :
    composeStep n K wit W cfg pe st (.mul a b) =
      some (st.pushSlot W (CertModel.mulN W cfg [0, st.len]
        (st.slot W a).1 (st.slot W a).2 (st.slot W b).1 (st.slot W b).2)) :=
  rfl

/-- The character arm, with its cache result `charSlot … = some (m, c)` memoized. -/
theorem composeStep_char_eq (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (st : ComposeState α) (k : CertKey)
    {m : CertModel α} {c : List (CertKey × CertPoly α × α)}
    (h : charSlot n K wit W cfg pe st.cache k = some (m, c)) :
    composeStep n K wit W cfg pe st (.char k) = some { st.pushSlot W m with cache := c } := by
  simp only [composeStep, h]

end KAM.Certificate
