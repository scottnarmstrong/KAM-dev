/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Kernel.ProductSplit

/-!
# The prefix check of a packed product, window by window (MAG-SEAL)

`checkPackedSpPrefix` contains `PackedAdvice.shapeOK`, which walks every advice window twice
(`packLenEq`, `windowZeroOK`). For a product whose advice has many long all-zero windows (stored as
`unzero [0, n]`), one kernel evaluation of the whole prefix is far slower than the windows one at a
time (measured on the magnetic product `M109`: nine all-zero windows of 16,767 slots, more than
600 s in one declaration). This module states the prefix from

* `packShapeBase`: the guards of `shapeOK` before the windows, verbatim;
* `packWindowOK adv s`: the two window guards of `shapeOK` at window `s`;
* `checkPackedSpRest`: the conjuncts of `checkPackedSpPrefix` after `shapeOK`, verbatim;

each of which the generated data decides in a declaration of its own. Nothing is assumed about the
data.
-/

@[expose] public section

namespace KAM.Magnetic.Data

open KAM.Certificate

/-- The guards of `shapeOK` before its two window walks, verbatim. -/
def packShapeBase (adv : PackedAdvice) : Bool :=
  decide (1 ≤ adv.scale) && decide (0 < adv.la.width) && decide (0 < adv.la.blockRows) &&
    decide (0 < adv.blockLen) && PackLayout.compat adv.la.dims.length adv.la adv.lb &&
    adv.lb.width == adv.la.width && adv.target.width == adv.la.width && adv.targetSubBox

/-- The two window guards of `shapeOK` at window `s` (offset `s · blockLen`). -/
def packWindowOK (adv : PackedAdvice) (s : ℕ) : Bool :=
  packLenEq (adv.rounded.getD s []) (2 * adv.blockLen - 1) &&
    adv.windowZeroOK (s * adv.blockLen) (adv.rounded.getD s [])

/-- The conjuncts of `checkPackedSpPrefix` after `shapeOK`, verbatim. -/
def checkPackedSpRest (adv : PackedAdvice) (ea eb : List (ℕ × ℤ)) : Bool :=
  decide (0 < adv.la.denseLen) && decide (0 < adv.lb.denseLen) &&
    packStrictAsc ea && packStrictAsc eb &&
    (ea.all fun e => decide (e.1 < adv.la.denseLen)) &&
    (eb.all fun e => decide (e.1 < adv.lb.denseLen)) &&
    adv.rounded.length == adv.spCount adv.la.denseLen + adv.spCount adv.lb.denseLen - 1

theorem adviceZeroOK_of_getD (adv : PackedAdvice) : ∀ (rs : List (List ℤ)) (s : ℕ),
    (∀ i < rs.length, adv.windowZeroOK ((s + i) * adv.blockLen) (rs.getD i []) = true) →
      adv.adviceZeroOK s rs = true
  | [], _, _ => rfl
  | r :: rs, s, h => by
    simp only [PackedAdvice.adviceZeroOK, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by simp), adviceZeroOK_of_getD adv rs (s + 1) fun i hi => ?_⟩
    have := h (i + 1) (by simp; omega)
    simpa [show s + (i + 1) = s + 1 + i by omega] using this

theorem all_packLenEq_of_getD (rs : List (List ℤ)) (n : ℕ)
    (h : ∀ i < rs.length, packLenEq (rs.getD i []) n = true) :
    (rs.all fun r => packLenEq r n) = true := by
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  simpa [List.getD_eq_getElem?_getD, hi] using h i hi

/-- `shapeOK` from its base guards and every window, the windows listed in `ws`. -/
theorem shapeOK_of_windows (adv : PackedAdvice) (hb : packShapeBase adv = true) (ws : List ℕ)
    (hcov : ∀ s < adv.rounded.length, s ∈ ws) (hw : ∀ s ∈ ws, packWindowOK adv s = true) :
    adv.shapeOK = true := by
  have hw' : ∀ s < adv.rounded.length, packWindowOK adv s = true := fun s hs => hw s (hcov s hs)
  simp only [packWindowOK, Bool.and_eq_true] at hw'
  have h1 := all_packLenEq_of_getD adv.rounded (2 * adv.blockLen - 1) fun i hi => (hw' i hi).1
  have h2 := adviceZeroOK_of_getD adv adv.rounded 0 fun i hi => by simpa using (hw' i hi).2
  unfold packShapeBase at hb
  unfold PackedAdvice.shapeOK
  rw [hb, h1, h2]
  rfl

/-- The prefix check from `shapeOK`'s base guards, its windows, and the rest of the prefix. -/
theorem checkPackedSpPrefix_of_parts (adv : PackedAdvice) (ea eb : List (ℕ × ℤ))
    (hb : packShapeBase adv = true) (ws : List ℕ) (hcov : ∀ s < adv.rounded.length, s ∈ ws)
    (hw : ∀ s ∈ ws, packWindowOK adv s = true) (hr : checkPackedSpRest adv ea eb = true) :
    checkPackedSpPrefix adv ea eb = true := by
  have hs := shapeOK_of_windows adv hb ws hcov hw
  unfold checkPackedSpRest at hr
  unfold checkPackedSpPrefix
  rw [hs]
  simpa only [Bool.true_and, Bool.and_assoc] using hr

end KAM.Magnetic.Data
