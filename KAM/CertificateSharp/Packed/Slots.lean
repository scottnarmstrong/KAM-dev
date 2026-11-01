/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Product

/-!
# Packed slot data: meaning, the list boundary, exact products and sums

Slot data `d` on a landed layout `L` denotes the Fourier sum `slotSum L n d = Σ_i d_i χ_{key(i)}`,
the key of slot `i` being `lo + digits(i)` (`keyOf PackLayout`). `SRep L B Z d` says that the
integer `Z` packs `d` (`packSum`), every slot is within `B`, and `d` vanishes off the box slots
(`InBox`). Then, with every step a single big-integer operation in the kernel:

* **boundary** (`srep_of_packRepOk`): the landed packing of a term list represents its dense slots,
  with the same Fourier sum (`intEval`);
* **exact product** (`SRep.mul`): on compatible layouts, `Z_a · Z_b` represents the convolution on
  the window layout `win`, whose Fourier sum is the product of the factors' sums;
* **sums** (`SRep.add`, `SRep.neg`, `SRep.sumN`) and a **unit at one slot** (`srep_unit`).

No rounding happens here: products and sums are exact, so chains of them need no intermediate
term lists (the representation of a product is again slot data on a layout).
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM.Certificate

open KAM

/-! ### Keys of slots and box slots -/

/-- The key carried by slot `i` of a layout: `lo + digits(i)` on its axes. -/
def keyOf (L : PackLayout) (i : ℕ) : CertKey :=
  (List.range L.dims.length).map fun j => L.lo.getD j 0 + ((packDigits L.stride i).getD j 0 : ℤ)

/-- Slot `i` is a box slot: the stride dot product of in-range digits. -/
def InBox (L : PackLayout) (i : ℕ) : Prop :=
  ∃ u : List ℕ, u.length = L.dims.length ∧ (∀ j < L.dims.length, u.getD j 0 < L.dims.getD j 0) ∧
    i = packDot u L.stride

/-- A well-formed layout: positive extents and no wrap of its own box (decidable). -/
def layoutWf (L : PackLayout) : Bool :=
  packNoWrap L.stride L.dims && L.dims.all fun d => decide (0 < d)

/-- The Fourier sum of slot data on a layout. -/
noncomputable def slotSum (L : PackLayout) (n : ℕ) (d : List ℤ) (θ : Fin n → ℂ) : ℂ :=
  ∑ i ∈ Finset.range d.length, (d.getD i 0 : ℂ) * character (certKeyFun n (keyOf L i)) θ

/-- `Z` packs the slot data `d` of the layout `L`; every slot is within `B` and `d` vanishes off the
box slots. -/
structure SRep (L : PackLayout) (B : ℕ) (Z : ℤ) (d : List ℤ) : Prop where
  len : d.length = L.denseLen
  pack : packSum L.width d = Z
  bound : ∀ c ∈ d, |c| ≤ (B : ℤ)
  box : ∀ i, d.getD i 0 ≠ 0 → InBox L i

theorem layoutWf_spec {L : PackLayout} (h : layoutWf L = true) :
    packNoWrap L.stride L.dims = true ∧ ∀ d ∈ L.dims, 0 < d := by
  simp only [layoutWf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h

/-- The key of a box slot is `lo + digits`. -/
theorem keyOf_packDot {L : PackLayout} (hw : layoutWf L = true) {u : List ℕ}
    (hu : u.length = L.dims.length) (hlt : ∀ j < L.dims.length, u.getD j 0 < L.dims.getD j 0) :
    keyOf L (packDot u L.stride) =
      (List.range L.dims.length).map fun j => L.lo.getD j 0 + (u.getD j 0 : ℤ) := by
  have hd := (packDigits_packDot L.stride L.dims u (layoutWf_spec hw).1 hu hlt).1
  unfold keyOf
  rw [hd]

/-! ### The list boundary -/

/-- The key of the slot of an in-box key is the key itself. -/
theorem keyOf_slot {L : PackLayout} (hw : layoutWf L = true) {k : CertKey} {p : ℕ}
    (h : L.slot k = some p) : keyOf L p = k ∧ InBox L p := by
  obtain ⟨hk, hbox, rfl⟩ := PackLayout.slot_eq_some h
  set u := (L.keyOffsets k).map Int.toNat with hu
  have hul : u.length = L.dims.length := by simp [hu, PackLayout.keyOffsets]
  have hget : ∀ j < L.dims.length, u.getD j 0 = (k.getD j 0 - L.lo.getD j 0).toNat := by
    intro j hj
    rw [hu, PackLayout.keyOffsets_toNat_getD, ite_eq_left hj]
  have hlt : ∀ j < L.dims.length, u.getD j 0 < L.dims.getD j 0 := by
    intro j hj
    rw [hget j hj]
    have := hbox j hj
    omega
  refine ⟨?_, u, hul, hlt, rfl⟩
  rw [keyOf_packDot hw hul hlt]
  apply List.ext_getElem
  · simp [hk]
  · intro j h1 h2
    have hj : j < L.dims.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [hget j hj]
    have := (hbox j hj).1
    have gk : k.getD j 0 = k[j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < k.length)]
    rw [← gk]
    omega

/-- **Boundary**: a passing `packRepOk` gives the packed representation of the dense slots, whose
Fourier sum is the term list's. -/
theorem srep_of_packRepOk {L : PackLayout} {x : List (CertKey × ℤ)} {B : ℕ} (hw : layoutWf L = true)
    (h : packRepOk L x B = true) :
    ∃ d : List ℤ, SRep L B (packOf L x) d ∧ ∀ (n : ℕ) (θ : Fin n → ℂ),
      intEval n x θ = slotSum L n d θ := by
  obtain ⟨d, hd, hpack, hbd⟩ := packRepOk_sound h
  have hlen := PackLayout.dense_length hd
  have hspec := PackLayout.dense_spec hd
  refine ⟨d, ⟨hlen, hpack, hbd, fun i hi => ?_⟩, fun n θ => ?_⟩
  · -- a nonzero dense slot carries a term of the list
    have hi' : i < L.denseLen := by
      by_contra hc
      apply hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hspec.2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi',
      Option.map_some, Option.getD_some] at hi
    unfold packSlotTotal at hi
    have hne : (x.map fun t => ((L.slot t.1).getD 0, t.2)).filter (fun e => e.1 == i) ≠ [] :=
      fun h0 => hi (by rw [h0]; rfl)
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨hmem, hsl⟩ := List.mem_filter.mp he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    have hs := hspec.1 t ht
    simp only [beq_iff_eq] at hsl
    rw [hsl] at hs
    exact (keyOf_slot hw hs).2
  · -- the Fourier sum, regrouped by slots
    unfold slotSum
    rw [hlen]
    have hfib := sum_range_fiber_mul x (fun t => (L.slot t.1).getD 0) L.denseLen
      (fun t ht => PackLayout.slot_lt_denseLen (hspec.1 t ht)) (fun t => (t.2 : ℂ))
      (fun p => character (certKeyFun n (keyOf L p)) θ)
    rw [Finset.sum_congr rfl fun p _ => by rw [PackLayout.dense_getD_cast hd p], hfib]
    unfold intEval
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [(keyOf_slot hw (hspec.1 t ht)).1]

/-! ### Window layouts -/

/-- The window of a product of two layouts: corner `lo_a + lo_b`, extents `dims_a + dims_b - 1`,
the strides and width of the first. -/
def win (La Lb : PackLayout) : PackLayout :=
  ⟨(List.range La.dims.length).map fun j => La.lo.getD j 0 + Lb.lo.getD j 0,
    (List.range La.dims.length).map fun j => La.dims.getD j 0 + Lb.dims.getD j 0 - 1,
    La.stride, La.width, La.blockRows⟩

theorem compat_spec {m : ℕ} {La Lb : PackLayout} (hc : PackLayout.compat m La Lb = true) :
    La.dims.length = m ∧ Lb.dims.length = m ∧ La.stride.length = m ∧ La.stride = Lb.stride ∧
      La.width = Lb.width ∧
      packNoWrap La.stride (List.zipWith (fun a b => a + b - 1) La.dims Lb.dims) = true := by
  simp only [PackLayout.compat, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem win_dims_eq {La Lb : PackLayout} (h : La.dims.length = Lb.dims.length) :
    (win La Lb).dims = List.zipWith (fun a b => a + b - 1) La.dims Lb.dims := by
  apply List.ext_getElem
  · simp [win, h]
  · intro j h1 h2
    have hj : j < La.dims.length := by simpa [win] using h1
    simp [win, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem (h ▸ hj : j < Lb.dims.length)]

theorem win_wf {m : ℕ} {La Lb : PackLayout} (hc : PackLayout.compat m La Lb = true)
    (ha : layoutWf La = true) (hb : layoutWf Lb = true) : layoutWf (win La Lb) = true := by
  obtain ⟨h1, h2, -, -, -, hnw⟩ := compat_spec hc
  have hpa := (layoutWf_spec ha).2
  have hpb := (layoutWf_spec hb).2
  simp only [layoutWf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨by rw [win_dims_eq (h1.trans h2.symm)]; exact hnw, fun d hd => ?_⟩
  simp only [win, List.mem_map, List.mem_range] at hd
  obtain ⟨j, hj, rfl⟩ := hd
  have : 0 < La.dims.getD j 0 := hpa _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem _)
  have hj2 : j < Lb.dims.length := by omega
  have : 0 < Lb.dims.getD j 0 := hpb _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2]; exact List.getElem_mem _)
  omega

theorem denseLen_eq {L : PackLayout} (h : layoutWf L = true) :
    L.denseLen = 1 + packDot (L.dims.map (· - 1)) L.stride := by
  have hp := (layoutWf_spec h).2
  unfold PackLayout.denseLen
  rw [ite_eq_left (List.all_eq_true.mpr fun d hd => decide_eq_true (hp d hd))]

theorem win_denseLen {m : ℕ} {La Lb : PackLayout} (hc : PackLayout.compat m La Lb = true)
    (ha : layoutWf La = true) (hb : layoutWf Lb = true) :
    (win La Lb).denseLen = La.denseLen + Lb.denseLen - 1 := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := compat_spec hc
  have hpa := (layoutWf_spec ha).2
  have hpb := (layoutWf_spec hb).2
  rw [denseLen_eq (win_wf hc ha hb), denseLen_eq ha, denseLen_eq hb, win_dims_eq (h1.trans h2.symm)]
  have hsplit : (List.zipWith (fun a b => a + b - 1) La.dims Lb.dims).map (· - 1) =
      List.zipWith (· + ·) (La.dims.map (· - 1)) (Lb.dims.map (· - 1)) := by
    apply List.ext_getElem
    · simp [h1, h2]
    · intro j hj1 hj2
      have hj : j < La.dims.length := by simpa [h1, h2] using hj1
      have a0 : 0 < La.dims[j] := hpa _ (List.getElem_mem _)
      have b0 : 0 < Lb.dims[j]'(by omega) := hpb _ (List.getElem_mem _)
      simp only [List.getElem_map, List.getElem_zipWith]
      omega
  rw [hsplit, packDot_add _ _ _ (by simp [h1, h2])]
  simp only [win, ← h4]
  omega

/-- Box slots add to box slots of the window, and their keys add. -/
theorem win_inBox_add {m : ℕ} {La Lb : PackLayout} (hc : PackLayout.compat m La Lb = true)
    (ha : layoutWf La = true) (hb : layoutWf Lb = true) {p q : ℕ} (hp : InBox La p)
    (hq : InBox Lb q) :
    InBox (win La Lb) (p + q) ∧
      keyOf (win La Lb) (p + q) = List.zipWith (· + ·) (keyOf La p) (keyOf Lb q) := by
  obtain ⟨h1, h2, -, h4, -, -⟩ := compat_spec hc
  obtain ⟨u, hul, hult, rfl⟩ := hp
  obtain ⟨v, hvl, hvlt, rfl⟩ := hq
  have hwl : (win La Lb).dims.length = m := by simp [win, h1]
  have huv : (List.zipWith (· + ·) u v).length = m := by simp [hul, hvl, h1, h2]
  have hget : ∀ j < m, (List.zipWith (· + ·) u v).getD j 0 = u.getD j 0 + v.getD j 0 := by
    intro j hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
      List.getElem?_eq_getElem (by omega : j < u.length),
      List.getElem?_eq_getElem (by omega : j < v.length)]
  have hwd : ∀ j < m, (win La Lb).dims.getD j 0 = La.dims.getD j 0 + Lb.dims.getD j 0 - 1 := by
    intro j hj
    simp [win, List.getD_eq_getElem?_getD, h1, hj]
  have hlt : ∀ j < (win La Lb).dims.length,
      (List.zipWith (· + ·) u v).getD j 0 < (win La Lb).dims.getD j 0 := by
    intro j hj
    rw [hwl] at hj
    rw [hget j hj, hwd j hj]
    have := hult j (by omega)
    have := hvlt j (by omega)
    omega
  have hsum : packDot u La.stride + packDot v Lb.stride =
      packDot (List.zipWith (· + ·) u v) (win La Lb).stride := by
    simp only [win, ← h4]
    rw [packDot_add _ _ _ (by rw [hul, hvl, h1, h2])]
  refine ⟨⟨_, by rw [huv, hwl], hlt, hsum⟩, ?_⟩
  rw [hsum, keyOf_packDot (win_wf hc ha hb) (by rw [huv, hwl]) hlt,
    keyOf_packDot ha hul hult, keyOf_packDot hb hvl hvlt]
  apply List.ext_getElem
  · simp [hwl, h1, h2]
  · intro j hj1 hj2
    have hj : j < m := by simpa [hwl] using hj1
    simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith]
    rw [hget j hj]
    simp only [win, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (h1 ▸ hj : j < La.dims.length), Option.map_some, Option.getD_some]
    push_cast
    ring

/-! ### Exact products -/

theorem listConv_getD_eq {a b : List ℤ} (ha : a ≠ []) (hb : b ≠ []) {i : ℕ}
    (hi : i < a.length + b.length - 1) :
    (listConv a b).getD i 0 = ∑ p ∈ Finset.range (i + 1), a.getD p 0 * b.getD (i - p) 0 := by
  have : (a.isEmpty || b.isEmpty) = false := by simp [ha, hb]
  simp only [listConv, this, Bool.false_eq_true, ↓reduceIte]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some, sum_map_range_eq]

/-- **Exact product**: on compatible well-formed layouts the product of two packed integers
represents the convolution on the window layout, and its Fourier sum is the product. -/
theorem SRep.mul {m : ℕ} {La Lb : PackLayout} (hc : PackLayout.compat m La Lb = true)
    (hwa : layoutWf La = true) (hwb : layoutWf Lb = true) {A B : ℕ} {Za Zb : ℤ} {da db : List ℤ}
    (ha : SRep La A Za da) (hb : SRep Lb B Zb db) {C : ℕ}
    (hC : min La.denseLen Lb.denseLen * A * B ≤ C) :
    SRep (win La Lb) C (Za * Zb) (listConv da db) ∧ ∀ (n : ℕ) (θ : Fin n → ℂ),
      slotSum (win La Lb) n (listConv da db) θ = slotSum La n da θ * slotSum Lb n db θ := by
  obtain ⟨h1, h2, -, -, hwid, -⟩ := compat_spec hc
  have hNa : 0 < La.denseLen := by
    rw [denseLen_eq hwa]; omega
  have hNb : 0 < Lb.denseLen := by
    rw [denseLen_eq hwb]; omega
  have hane : da ≠ [] := List.ne_nil_of_length_pos (ha.len ▸ hNa)
  have hbne : db ≠ [] := List.ne_nil_of_length_pos (hb.len ▸ hNb)
  have hclen : (listConv da db).length = (win La Lb).denseLen := by
    rw [listConv_length hane hbne, ha.len, hb.len, win_denseLen hc hwa hwb]
  have hkey : ∀ p q, da.getD p 0 * db.getD q 0 ≠ 0 →
      InBox (win La Lb) (p + q) ∧
        keyOf (win La Lb) (p + q) = List.zipWith (· + ·) (keyOf La p) (keyOf Lb q) := by
    intro p q hpq
    exact win_inBox_add hc hwa hwb (ha.box p (left_ne_zero_of_mul hpq))
      (hb.box q (right_ne_zero_of_mul hpq))
  refine ⟨⟨hclen, ?_, ?_, ?_⟩, fun n θ => ?_⟩
  · simp only [win]
    rw [packSum_listConv, ha.pack, ← hb.pack, hwid]
  · intro c hcm
    refine (listConv_abs_le ha.bound hb.bound c hcm).trans ?_
    rw [ha.len, hb.len]
    exact_mod_cast hC
  · intro i hi
    have hi' : i < da.length + db.length - 1 := by
      by_contra hcon
      apply hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
        (by rw [listConv_length hane hbne]; omega)]
      rfl
    rw [listConv_getD_eq hane hbne hi'] at hi
    obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    have := (hkey p (i - p) hne).1
    rwa [Nat.add_sub_cancel' (by simpa [Nat.lt_succ_iff] using hp)] at this
  · -- the Fourier identity
    have hlenK : ∀ p q, da.getD p 0 * db.getD q 0 ≠ 0 →
        (keyOf La p).length = (keyOf Lb q).length := by
      intro p q _
      simp [keyOf, h1, h2]
    have hterm : ∀ p q, (da.getD p 0 : ℂ) * character (certKeyFun n (keyOf La p)) θ *
        ((db.getD q 0 : ℂ) * character (certKeyFun n (keyOf Lb q)) θ) =
        (da.getD p 0 : ℂ) * (db.getD q 0 : ℂ) *
          character (certKeyFun n (keyOf (win La Lb) (p + q))) θ := by
      intro p q
      by_cases hz : da.getD p 0 * db.getD q 0 = 0
      · have : (da.getD p 0 : ℂ) * (db.getD q 0 : ℂ) = 0 := by exact_mod_cast hz
        linear_combination (character (certKeyFun n (keyOf La p)) θ *
          character (certKeyFun n (keyOf Lb q)) θ -
          character (certKeyFun n (keyOf (win La Lb) (p + q))) θ) * this
      · rw [(hkey p q hz).2, certKeyFun_zipWith_add n (hlenK p q hz), ← character_mul]
        ring
    unfold slotSum
    rw [Finset.sum_mul_sum]
    simp_rw [hterm]
    rw [← sum_range_cauchy_weighted (fun p => (da.getD p 0 : ℂ)) (fun q => (db.getD q 0 : ℂ))
      (fun i => character (certKeyFun n (keyOf (win La Lb) i)) θ) da.length db.length
      (fun p hp => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hp])
      (fun q hq => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hq]),
      listConv_length hane hbne]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [listConv_getD_eq hane hbne (Finset.mem_range.mp hi)]
    push_cast
    rfl

/-! ### Sums -/

/-- Slotwise sum of two slot lists (the shorter is cut off; equal lengths in use). -/
def zadd (d e : List ℤ) : List ℤ := List.zipWith (· + ·) d e

theorem zadd_getD {d e : List ℤ} (h : d.length = e.length) (i : ℕ) :
    (zadd d e).getD i 0 = d.getD i 0 + e.getD i 0 := by
  by_cases hi : i < d.length
  · simp [zadd, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (h ▸ hi : i < e.length)]
  · have hi' : ¬ i < e.length := h ▸ hi
    simp [zadd, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
      List.getElem?_eq_none (not_lt.mp hi), List.getElem?_eq_none (not_lt.mp hi')]

theorem packSum_zadd (w : ℕ) {d e : List ℤ} (h : d.length = e.length) :
    packSum w (zadd d e) = packSum w d + packSum w e := by
  have hl : (zadd d e).length = d.length := by simp [zadd, h]
  rw [packSum_eq_sum, packSum_eq_sum, packSum_eq_sum, hl, h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zadd_getD h]
  ring

theorem SRep.add {L : PackLayout} {A B : ℕ} {Z Y : ℤ} {d e : List ℤ} (ha : SRep L A Z d)
    (hb : SRep L B Y e) : SRep L (A + B) (Z + Y) (zadd d e) ∧
      ∀ (n : ℕ) (θ : Fin n → ℂ), slotSum L n (zadd d e) θ = slotSum L n d θ + slotSum L n e θ := by
  have hl : d.length = e.length := ha.len.trans hb.len.symm
  have hzl : (zadd d e).length = d.length := by simp [zadd, hl]
  refine ⟨⟨hzl.trans ha.len, by rw [packSum_zadd _ hl, ha.pack, hb.pack], fun c hc => ?_,
    fun i hi => ?_⟩, fun n θ => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hi1 : i < d.length := by rw [← hzl]; exact hi
    have hg := zadd_getD hl i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hg
    rw [hg]
    have hm1 : d.getD i 0 ∈ d := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1]; exact List.getElem_mem _
    have hm2 : e.getD i 0 ∈ e := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ hi1)]
      exact List.getElem_mem _
    have h1 := ha.bound _ hm1
    have h2 := hb.bound _ hm2
    push_cast
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  · rw [zadd_getD hl] at hi
    by_cases hd0 : d.getD i 0 = 0
    · rw [hd0, zero_add] at hi
      exact hb.box i hi
    · exact ha.box i hd0
  · unfold slotSum
    rw [hzl, ← hl, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zadd_getD hl]
    push_cast
    ring

theorem SRep.neg {L : PackLayout} {A : ℕ} {Z : ℤ} {d : List ℤ} (ha : SRep L A Z d) :
    SRep L A (-Z) (d.map Neg.neg) ∧ ∀ (n : ℕ) (θ : Fin n → ℂ),
      slotSum L n (d.map Neg.neg) θ = -slotSum L n d θ := by
  have hget : ∀ i, (d.map Neg.neg).getD i 0 = -d.getD i 0 := by
    intro i
    by_cases hi : i < d.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]
  refine ⟨⟨by simp [ha.len], ?_, fun c hc => ?_, fun i hi => ha.box i (by
    rw [hget] at hi; exact neg_ne_zero.mp hi)⟩, fun n θ => ?_⟩
  · rw [← ha.pack, packSum_eq_sum, packSum_eq_sum, List.length_map, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hget]; ring
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    rw [abs_neg]
    exact ha.bound c' hc'
  · unfold slotSum
    rw [List.length_map, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hget]; push_cast; ring

/-- The zero slot data of a layout. -/
def zzero (L : PackLayout) : List ℤ := List.replicate L.denseLen 0

theorem srep_zero (L : PackLayout) : SRep L 0 0 (zzero L) := by
  refine ⟨by simp [zzero], ?_, fun c hc => ?_, fun i hi => ?_⟩
  · rw [zzero, packSum_replicate, zero_mul]
  · rw [zzero, List.mem_replicate] at hc
    rw [hc.2]; simp
  · exfalso
    apply hi
    simp only [zzero, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl

theorem slotSum_zero (L : PackLayout) (n : ℕ) (θ : Fin n → ℂ) : slotSum L n (zzero L) θ = 0 := by
  unfold slotSum
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i < L.denseLen := by simpa [zzero] using hi
  simp [zzero, List.getD_eq_getElem?_getD, hi']

/-- Packed sum `Σ_{r<N} f r`. -/
def zsumN (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | N + 1 => zsumN f N + f N

/-- Slot data of a packed sum. -/
def dsumN (L : PackLayout) (g : ℕ → List ℤ) : ℕ → List ℤ
  | 0 => zzero L
  | N + 1 => zadd (dsumN L g N) (g N)

/-- **Sums of packed data** on one layout. -/
theorem SRep.sumN {L : PackLayout} {A : ℕ → ℕ} {f : ℕ → ℤ} {g : ℕ → List ℤ} :
    ∀ N : ℕ, (∀ r < N, SRep L (A r) (f r) (g r)) →
      SRep L ((List.range N).map A).sum (zsumN f N) (dsumN L g N) ∧
        ∀ (n : ℕ) (θ : Fin n → ℂ), slotSum L n (dsumN L g N) θ =
          ∑ r ∈ Finset.range N, slotSum L n (g r) θ
  | 0, _ => ⟨by simpa [zsumN, dsumN] using srep_zero L, fun n θ => by
      simp [dsumN, slotSum_zero]⟩
  | N + 1, h => by
    obtain ⟨hs, he⟩ := SRep.sumN N fun r hr => h r (by omega)
    obtain ⟨hs2, he2⟩ := hs.add (h N (by omega))
    refine ⟨by simpa [zsumN, dsumN, List.range_succ] using hs2, fun n θ => ?_⟩
    rw [dsumN, he2, he, Finset.sum_range_succ]

/-! ### A unit at one slot -/

/-- The slot data with `c` at slot `p` and zeros elsewhere. -/
def zunit (L : PackLayout) (p : ℕ) (c : ℤ) : List ℤ :=
  (List.range L.denseLen).map fun i => if i = p then c else 0

theorem srep_unit {L : PackLayout} {p : ℕ} (hp : p < L.denseLen) (hbox : InBox L p) (c : ℤ) :
    SRep L c.natAbs (c * 2 ^ (L.width * p)) (zunit L p c) ∧ ∀ (n : ℕ) (θ : Fin n → ℂ),
      slotSum L n (zunit L p c) θ = c * character (certKeyFun n (keyOf L p)) θ := by
  have hget : ∀ i, (zunit L p c).getD i 0 = if i = p then c else 0 := by
    intro i
    by_cases hi : i < L.denseLen
    · simp [zunit, List.getD_eq_getElem?_getD, hi]
    · have : i ≠ p := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [zunit]; omega)]
      simp [this]
  refine ⟨⟨by simp [zunit], ?_, fun x hx => ?_, fun i hi => ?_⟩, fun n θ => ?_⟩
  · rw [packSum_eq_sum, show (zunit L p c).length = L.denseLen by simp [zunit],
      Finset.sum_eq_single p (fun i _ hip => by rw [hget, ite_eq_right hip, zero_mul])
        (fun h => absurd (Finset.mem_range.mpr hp) h), hget, ite_eq_left rfl, pow_mul]
  · simp only [zunit, List.mem_map, List.mem_range] at hx
    obtain ⟨i, -, rfl⟩ := hx
    split_ifs
    · rw [Int.abs_eq_natAbs]
    · simp
  · rw [hget] at hi
    split_ifs at hi with hip
    · exact hip ▸ hbox
    · exact absurd rfl hi
  · unfold slotSum
    rw [show (zunit L p c).length = L.denseLen by simp [zunit],
      Finset.sum_eq_single p (fun i _ hip => by rw [hget, ite_eq_right hip]; simp)
        (fun h => absurd (Finset.mem_range.mpr hp) h), hget, ite_eq_left rfl]

end KAM.CertificateSharp.Packed
