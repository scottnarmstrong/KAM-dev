/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.DOpd

/-!
# Certified literal copies and derivative literals (T2-CONF, N7)

The bracket checker multiplies literals only (the expansion of a literal is a few `GMP` operations;
the packing of a sparse model and the masked derivative `derivZ` are not). Two certificates, each
checked once per model at a narrow packing `P`:

* `fCheck P L d`: the literal `L` has the slots of the sparse model `d` (`fCheck_sound`:
  `litList L.C P.S P.b L.X = d.list P.S` and the same half-width, parity and scale);
* `dCheck P Pd L dL a`: the literal `dL`, read with the digit width `Pd.b`, has the slots of the
  derivative `dlist (Layout.key L.C P.S) a L.par` of the literal `L` (`dCheck_sound`).

Both compare the packed values at one width and conclude by injectivity of the packing.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

theorem abs_le_l1_of_mem {l : List ℤ} {x : ℤ} (hx : x ∈ l) : |x| ≤ l1 l := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [l1_eq]
  have h : |l[i]| = |l.getD i 0| := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [h]
  exact single_le_sum (f := fun j => |l.getD j 0|) (fun j _ => abs_nonneg _) (mem_range.mpr hi)

theorem slotsBounded_litList {C S b w X : ℕ} (hb : 1 ≤ b) (hbw : b < w) :
    SlotsBounded w (litList C S b X) := fun c hc => by
  have h1 := abs_litList_lt hb c hc
  have h2 : (2 : ℤ) ^ b < 2 ^ w := pow_lt_pow_right₀ (by norm_num) hbw
  have h3 : (2 : ℤ) ^ b = 2 * 2 ^ (b - 1) := by rw [← pow_succ', Nat.sub_add_cancel hb]
  rcases abs_cases c with ⟨hc', -⟩ | ⟨hc', -⟩ <;> rw [hc'] <;> linarith [h1.1, h1.2]

/-- The certificate of a literal copy of a sparse model (kernel). -/
def fCheck (P : Prm) (L : LitD) (d : SpD) : Bool :=
  L.ok P && d.ok P.S && (L.C == d.C) && (L.par == d.par) && decide (L.q = d.q) &&
    decide (1 ≤ P.b) && decide (P.b < P.w) && decide (2 * d.l1E < 2 ^ P.w) &&
    decide (L.Z P = d.Z P.w P.S)

theorem fCheck_sound {P : Prm} {L : LitD} {d : SpD} (h : fCheck P L d = true) :
    litList L.C P.S P.b L.X = d.list P.S ∧ L.C = d.C ∧ L.par = d.par ∧ L.q = d.q := by
  simp only [fCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hL, hd⟩, hC⟩, hpar⟩, hq⟩, hb⟩, hbw⟩, hl1⟩, hZ⟩ := h
  refine ⟨?_, hC, hpar, hq⟩
  refine packSum_injective (slotsBounded_litList hb hbw) (fun c hc => ?_) ?_ ?_
  · have h1 := (abs_le_l1_of_mem hc).trans (SpD.l1_list_le hd)
    have h2 : ((2 * d.l1E : ℕ) : ℤ) < ((2 ^ P.w : ℕ) : ℤ) := by exact_mod_cast hl1
    push_cast at h2
    linarith
  · rw [length_litList, SpD.length_list, hC]
  · have h1 := (LitD.wf hL).pack
    simp only [LitD.opd] at h1
    rw [h1, SpD.packSum_list hd]
    exact hZ

/-- The certificate of a derivative literal (kernel). -/
def dCheck (P Pd : Prm) (L dL : LitD) (a : Fin 2) : Bool :=
  L.ok P && dL.ok Pd && (dL.C == L.C) && (dL.par == !L.par) && decide (dL.q = L.q) &&
    decide (Pd.w = P.w) && decide (Pd.S = P.S) && decide (1 ≤ P.b) && decide (1 ≤ Pd.b) &&
    decide (Pd.b < Pd.w) && decide (2 * (L.C * 2 ^ (P.b - 1)) < 2 ^ P.w) &&
    decide (dL.Z Pd = L.dZ P a)

theorem dCheck_sound {P Pd : Prm} {L dL : LitD} {a : Fin 2} (h : dCheck P Pd L dL a = true) :
    litList dL.C Pd.S Pd.b dL.X = dlist (Layout.key L.C P.S) a L.par (litList L.C P.S P.b L.X) ∧
      dL.C = L.C ∧ dL.par = !L.par ∧ dL.q = L.q := by
  simp only [dCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL, hdL⟩, hC⟩, hpar⟩, hq⟩, hw⟩, hS⟩, hb⟩, hbd⟩, hbdw⟩, hmx⟩, hZ⟩ := h
  refine ⟨?_, hC, hpar, hq⟩
  have hwfL := LitD.wf hL
  have hKS : 2 * L.C + 1 ≤ P.S := by
    simp only [LitD.ok, Bool.and_eq_true, decide_eq_true_eq] at hL; exact hL.1.1.2
  refine packSum_injective (w := P.w) ?_ (fun c hc => ?_) ?_ ?_
  · rw [← hw]; exact slotsBounded_litList hbd hbdw
  · have h1 := mx_dlist (C := L.C) (by omega) hwfL.cols hwfL.len (LitD.mx (d := L) hb) a L.par c hc
    have h2 : ((2 * (L.C * 2 ^ (P.b - 1)) : ℕ) : ℤ) < ((2 ^ P.w : ℕ) : ℤ) := by exact_mod_cast hmx
    push_cast at h1 h2
    have := abs_nonneg c
    linarith
  · rw [length_litList, length_dlist, length_litList, hC, hS]
  · have h1 := (LitD.wf hdL).pack
    have h2 := (LitD.dwf hL hb a).pack
    simp only [LitD.opd, LitD.dopd] at h1 h2
    rw [← hw, h1, hZ, ← h2, hw]

end KAM.EffectiveStability.Tube

end
