/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.TorsR

/-!
# Assembly of the rounded packed torsion check from its parts

A production proof of `checkTorsionR` (B3b) decides its parts in separate declarations, one kernel
computation each (`checkTorsionR_of` in `Packed/TorsRSound.lean` takes the boundary entries and the
core). This module splits the two further:

* `ptEntries_of`: the boundary entries from the `D²K`, `DX_H ∘ K` and `DH ∘ K` entries;
* `stageAll_of`: a node stage from its entries (the two largest nodes `DN`, `X_N` are decided
  entry by entry);
* `torsRCore_of`: the core from its thirteen conjuncts.

No new definition: each lemma restates its target's own conjuncts.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

variable {α : Type} [CertArith α] {n : ℕ}

/-- The boundary entries of the torsion from each entry. -/
theorem ptEntries_of {K : CertEmbedding α} {W : CertWeight} {cfg : ModelConfig α}
    {pe : PiEnclosure α} {tb : PTorsBook} {tm : PTorsMemo} {ms : List (CertModel α)}
    (hd2 : ∀ r < n + n, ∀ j < n, ∀ l < n, ptD2Ok n K W cfg pe tb tm r j l = true)
    (hA : ∀ a < n + n, ∀ b < n + n, ptAOk n W cfg pe tb tm ms a b = true)
    (hD1 : ∀ a < n + n, ptD1Ok n W cfg pe tb tm ms a = true) :
    ptEntries n K W cfg pe tb tm ms = true := by
  simp only [ptEntries, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  exact ⟨⟨hd2, hA⟩, hD1⟩

/-- A node stage from each of its entries. -/
theorem stageAll_of {W : CertWeight} {q lr ln : ℕ} {Ls Ld Lu : PackLayout} {A' e s R C : ℕ}
    {M : PMat α} {tab : List (List NodeEntry)}
    (h : ∀ i < R, ∀ j < C,
      stageOk n W q lr ln Ls Ld Lu A' e s (M.x i j) (M.r i j) (nodeAt tab i j) = true) :
    stageAll n W q lr ln Ls Ld Lu A' e s R C M tab = true := by
  simp only [stageAll, List.all_eq_true, List.mem_range]
  exact h

/-- The core of the rounded packed torsion check from its conjuncts. -/
theorem torsRCore_of {Binv : List (List (CertPoly α))} {W : CertWeight} {cfg : ModelConfig α}
    {box : FreqBox} {s : ℚ} {rb : PRBook} {mm : PGramMemo} {tm : PTorsMemo} {rm : PRMemo}
    {eps : α} {S : List (List (CC α))} {σTμ : ℚ}
    (hlay : trLayOk n rb = true) (hnrm : trNormOk n W box s rb = true)
    (hpk : ptPackOk n Binv cfg rb.toT mm tm = true)
    (hN : trStN n Binv W cfg rb mm rm eps = true)
    (hDL : trStDL (α := α) n W box s rb tm rm = true)
    (hDG : trStDG (α := α) n W rb mm rm = true)
    (hC : trStC n Binv W cfg rb rm eps = true)
    (hDGi : trStDGi n Binv W cfg rb rm eps = true)
    (hDN : trStDN n Binv W cfg rb mm rm eps = true)
    (hXN : trStXN (α := α) n W rb tm rm = true)
    (hT : trTCheck (α := α) n rb rm = true) (hY : trYCheck (α := α) n W rb tm rm = true)
    (hF : tabFinal n cfg rb.P (trCentre n box s rm) (trRad n box s rm) S σTμ = true) :
    torsRCore n Binv W cfg box s rb mm tm rm eps S σTμ = true := by
  simp only [torsRCore, hlay, hnrm, hpk, hN, hDL, hDG, hC, hDGi, hDN, hXN, hT, hY, hF,
    Bool.and_self]

end KAM.CertificateSharp.Packed

end
