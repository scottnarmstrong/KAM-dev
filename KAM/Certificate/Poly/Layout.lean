/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.Packed

/-!
# Dense box layouts of integer Fourier data

A `PackLayout` lays the keys `lo ≤ k < lo + dims` of a box out densely: the key `k` goes to the
slot `Σ_j (k_j - lo_j) · stride_j` (`PackLayout.slot`; keys of the wrong length are outside the
box). `PackLayout.dense` scatters integer Fourier data into its slots (repeated keys add), with a
binary-splitting scatter that the kernel runs in `O(#terms · log + slots)`. Two layouts are
compatible at dimension `n` (`PackLayout.compat`) when they have `n` axes, equal strides and
widths, and no product offset wraps (each stride covers the next stride times the next product
extent; mixed-radix decoding by `packDigits` is then exact). Under `compat`, the product of two
integer Fourier sums is the laid-out convolution of their dense slot lists, with the product key
`PackLayout.prodKey` read off each slot (`PackLayout.intEval_mul`, at every dimension of
evaluation: `PackLayout.intEval_mul_of_compat`).
-/

@[expose] public section

namespace KAM.Certificate

open KAM

/-! ### Mixed-radix slot arithmetic -/

/-- The natural dot product `Σ u_j s_j` (truncated to the shorter list). -/
def packDot (u s : List ℕ) : ℕ := (List.zipWith (· * ·) u s).sum

theorem packDot_cons (a b : ℕ) (u s : List ℕ) :
    packDot (a :: u) (b :: s) = a * b + packDot u s := by
  simp [packDot]

theorem packDot_nil_left (s : List ℕ) : packDot [] s = 0 := by simp [packDot]

theorem packDot_add (s : List ℕ) : ∀ (u v : List ℕ), u.length = v.length →
    packDot (List.zipWith (· + ·) u v) s = packDot u s + packDot v s := by
  induction s with
  | nil => intro u v _; simp [packDot]
  | cons c s ih =>
    intro u v hl
    cases u with
    | nil => cases v with
      | nil => simp [packDot]
      | cons _ _ => simp at hl
    | cons a u => cases v with
      | nil => simp at hl
      | cons b v =>
        simp only [List.zipWith_cons_cons, packDot_cons]
        rw [ih u v (by simpa using hl)]
        ring

/-- Monotonicity of the dot product in its first argument. -/
theorem packDot_le_packDot (s : List ℕ) : ∀ (u v : List ℕ), u.length = v.length →
    (∀ j < u.length, u.getD j 0 ≤ v.getD j 0) → packDot u s ≤ packDot v s := by
  induction s with
  | nil => intro u v _ _; simp [packDot]
  | cons c s ih =>
    intro u v hl hle
    cases u with
    | nil => cases v with
      | nil => exact le_rfl
      | cons _ _ => simp at hl
    | cons a u => cases v with
      | nil => simp at hl
      | cons b v =>
        simp only [packDot_cons]
        have h0 : a ≤ b := by simpa using hle 0 (by simp)
        have h1 := ih u v (by simpa using hl) fun j hj => by
          simpa using hle (j + 1) (by simpa using hj)
        exact Nat.add_le_add (Nat.mul_le_mul_right c h0) h1

/-- The mixed-radix digits of `i` for the strides `ss` (outermost first): `i / s₀`, then the
digits of `i % s₀` for the remaining strides. -/
def packDigits : List ℕ → ℕ → List ℕ
  | [], _ => []
  | s :: ss, i => i / s :: packDigits ss (i % s)

/-- No wrap for the extents `es` (decidable): each stride is at least the next stride times the
next extent, the last stride is positive, and the two lists have equal lengths. -/
def packNoWrap : List ℕ → List ℕ → Bool
  | [], [] => true
  | [s], [_] => decide (1 ≤ s)
  | s :: s' :: ss, _ :: e' :: es => decide (s' * e' ≤ s) && packNoWrap (s' :: ss) (e' :: es)
  | _, _ => false

/-- **Exact mixed-radix decoding**: digits below the extents are recovered from their dot
product with no-wrap strides (and that dot product stays below the first stride times the first
extent). -/
theorem packDigits_packDot (ss : List ℕ) : ∀ (es us : List ℕ), packNoWrap ss es = true →
    us.length = es.length → (∀ j < es.length, us.getD j 0 < es.getD j 0) →
    packDigits ss (packDot us ss) = us ∧
      ∀ s e, ss.head? = some s → es.head? = some e → packDot us ss < s * e := by
  induction ss with
  | nil =>
    intro es us hw hl _
    cases es with
    | nil =>
      cases us with
      | nil => simp [packDigits, packDot]
      | cons _ _ => simp at hl
    | cons _ _ => simp [packNoWrap] at hw
  | cons s ss ih =>
    intro es us hw hl hlt
    cases ss with
    | nil =>
      match es, us, hw, hl, hlt with
      | [e], [u], hw, _, hlt =>
        have hs : 1 ≤ s := by simpa [packNoWrap] using hw
        have hu : u < e := by simpa using hlt 0 (by simp)
        refine ⟨?_, ?_⟩
        · simp [packDigits, packDot, Nat.mul_div_cancel u (by omega : 0 < s)]
        · intro s' e' hs' he'
          simp only [List.head?_cons, Option.some.injEq] at hs' he'
          rw [← hs', ← he']
          simp only [packDot, List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons,
            List.sum_nil, add_zero]
          rw [Nat.mul_comm s e]
          exact Nat.mul_lt_mul_of_pos_right hu (by omega)
      | [], _, hw, _, _ => simp [packNoWrap] at hw
      | _ :: _ :: _, _, hw, _, _ => simp [packNoWrap] at hw
      | [_], [], _, hl, _ => simp at hl
      | [_], _ :: _ :: _, _, hl, _ => simp at hl
    | cons s' ss =>
      match es, us, hw, hl, hlt with
      | e :: e' :: es, u :: us, hw, hl, hlt =>
        simp only [packNoWrap, Bool.and_eq_true, decide_eq_true_eq] at hw
        obtain ⟨hss, hw'⟩ := hw
        have hl' : us.length = (e' :: es).length := by simpa using hl
        have hlt' : ∀ j < (e' :: es).length, us.getD j 0 < (e' :: es).getD j 0 := fun j hj => by
          simpa using hlt (j + 1) (by simpa using hj)
        obtain ⟨hdec, hbd⟩ := ih (e' :: es) us hw' hl' hlt'
        have hr : packDot us (s' :: ss) < s := (hbd s' e' rfl rfl).trans_le hss
        have hu : u < e := by simpa using hlt 0 (by simp)
        have hspos : 0 < s := by omega
        rw [packDot_cons]
        refine ⟨?_, ?_⟩
        · rw [packDigits, Nat.add_comm, Nat.add_mul_div_right _ _ hspos,
            Nat.div_eq_of_lt hr, Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr,
            hdec]
        · intro s₀ e₀ hs₀ he₀
          simp only [List.head?_cons, Option.some.injEq] at hs₀ he₀
          rw [← hs₀, ← he₀]
          calc u * s + packDot us (s' :: ss) < u * s + s := by omega
            _ = (u + 1) * s := by ring
            _ ≤ e * s := Nat.mul_le_mul_right _ hu
            _ = s * e := mul_comm _ _
      | [], _, hw, _, _ => simp [packNoWrap] at hw
      | [_], _, hw, _, _ => simp [packNoWrap] at hw
      | _ :: _ :: _, [], _, hl, _ => simp at hl

/-! ### Layouts -/

/-- A dense box layout of Fourier keys `lo ≤ k < lo + dims` (mixed radix, row-major with the
row strides `stride`), slot width `width` and shard block size `blockRows` (rows). -/
structure PackLayout where
  lo : CertKey
  dims : List ℕ
  stride : List ℕ
  width : ℕ
  blockRows : ℕ

/-- The offsets `k_j - lo_j` of a key on the `dims.length` axes. -/
def PackLayout.keyOffsets (L : PackLayout) (k : CertKey) : List ℤ :=
  (List.range L.dims.length).map fun j => k.getD j 0 - L.lo.getD j 0

/-- A key lies in the box: exactly `dims.length` entries, and `0 ≤ k_j - lo_j < dims_j` on every
axis. -/
def PackLayout.keyInBox (L : PackLayout) (k : CertKey) : Bool :=
  k.length == L.dims.length && (List.range L.dims.length).all fun j =>
    decide (0 ≤ k.getD j 0 - L.lo.getD j 0) &&
      decide (k.getD j 0 - L.lo.getD j 0 < (L.dims.getD j 0 : ℤ))

/-- The slot of a key (`none` outside the box). -/
def PackLayout.slot (L : PackLayout) (k : CertKey) : Option ℕ :=
  if L.keyInBox k then some (packDot ((L.keyOffsets k).map Int.toNat) L.stride) else none

/-- **Canonical dense length** of a layout (Revision 7, audit 6 F14): `1 + Σ_j (dims_j - 1) ·
stride_j` when every extent is positive, `0` on an empty box. Padding by `cut` forgets the raw
factor length, so the whole check compares the RAW lists against this number. -/
def PackLayout.denseLen (L : PackLayout) : ℕ :=
  if L.dims.all fun d => decide (0 < d) then 1 + packDot (L.dims.map (· - 1)) L.stride else 0

/-- The total of the values at slot `p` of a list of `(slot, value)` pairs. -/
def packSlotTotal (es : List (ℕ × ℤ)) (p : ℕ) : ℤ :=
  ((es.filter fun e => e.1 == p).map Prod.snd).sum

/-- Scatter-add of `(slot, value)` pairs into `size` dense slots from `base`, by binary splitting
of the slot range (`fuel` levels, then the direct formula): `O(#es · log size + size)` kernel
steps for any order and any repetition of the slots. -/
def packScatter : ℕ → ℕ → ℕ → List (ℕ × ℤ) → List ℤ
  | 0, base, size, es => (List.range size).map fun q => packSlotTotal es (base + q)
  | fuel + 1, base, size, es =>
    if size ≤ 1 then (List.range size).map fun q => packSlotTotal es (base + q)
    else
      packScatter fuel base (size / 2) (es.filter fun e => decide (e.1 < base + size / 2)) ++
        packScatter fuel (base + size / 2) (size - size / 2)
          (es.filter fun e => !decide (e.1 < base + size / 2))

theorem packScatter_eq (fuel : ℕ) : ∀ (base size : ℕ) (es : List (ℕ × ℤ)),
    packScatter fuel base size es = (List.range size).map fun q => packSlotTotal es (base + q) := by
  induction fuel with
  | zero => intro base size es; rfl
  | succ fuel ih =>
    intro base size es
    rw [packScatter]
    split_ifs with hs
    · rfl
    · rw [ih, ih]
      have hsz : size = size / 2 + (size - size / 2) := by omega
      conv_rhs => rw [hsz, List.range_add, List.map_append, List.map_map]
      congr 1
      · refine List.map_congr_left fun q hq => ?_
        rw [List.mem_range] at hq
        simp only [packSlotTotal, List.filter_filter]
        congr 2
        refine List.filter_congr fun e _ => ?_
        by_cases he : e.1 = base + q
        · simp [he, hq]
        · simp [he]
      · refine List.map_congr_left fun q _ => ?_
        simp only [Function.comp_apply, packSlotTotal, List.filter_filter]
        congr 2
        refine List.filter_congr fun e _ => ?_
        by_cases he : e.1 = base + (size / 2 + q)
        · simp [he, ← Nat.add_assoc]
        · have he' : ¬ e.1 = base + size / 2 + q := by omega
          simp [he', ← Nat.add_assoc]

/-- The slot of a key computed by walking the key, `lo`, `dims` and `stride` together (the kernel
form of `PackLayout.slot`, `packSlotAux_eq`). -/
def packSlotAux : List ℤ → List ℤ → List ℕ → List ℕ → Option ℕ
  | [], _, [], _ => some 0
  | x :: xs, lo, d :: ds, ss =>
    match x - lo.headD 0 with
    | Int.ofNat u => if u < d then (packSlotAux xs lo.tail ds ss.tail).map (u * ss.headD 0 + ·)
        else none
    | Int.negSucc _ => none
  | _, _, _, _ => none

/-- Strictly increasing slots (decidable): the linear fill applies. -/
def packStrictAsc : List (ℕ × ℤ) → Bool
  | a :: b :: rest => decide (a.1 < b.1) && packStrictAsc (b :: rest)
  | _ => true

/-- Linear fill of `n` dense slots from slot `p` by strictly increasing `(slot, value)` pairs. -/
def packFill : ℕ → ℕ → List (ℕ × ℤ) → List ℤ
  | 0, _, _ => []
  | n + 1, p, [] => 0 :: packFill n (p + 1) []
  | n + 1, p, e :: es =>
    if e.1 = p then e.2 :: packFill n (p + 1) es else 0 :: packFill n (p + 1) (e :: es)

/-- Dense slot list of integer Fourier data (`none` on an out-of-box key; repeated keys add).
Strictly increasing slots are filled in one pass; any other order (or repetition) goes through
the binary scatter. -/
def PackLayout.dense (L : PackLayout) (cs : List (CertKey × ℤ)) : Option (List ℤ) :=
  if cs.all fun t => (packSlotAux t.1 L.lo L.dims L.stride).isSome then
    some (if packStrictAsc (cs.map fun t => ((packSlotAux t.1 L.lo L.dims L.stride).getD 0, t.2))
      then packFill L.denseLen 0
        (cs.map fun t => ((packSlotAux t.1 L.lo L.dims L.stride).getD 0, t.2))
      else packScatter L.denseLen 0 L.denseLen
        (cs.map fun t => ((packSlotAux t.1 L.lo L.dims L.stride).getD 0, t.2)))
  else none

/-- The key carried by slot `i` of the product window of two layouts (mixed-radix digits of `i`
added to `lo_a + lo_b`). -/
def PackLayout.prodKey (La Lb : PackLayout) (i : ℕ) : CertKey :=
  (List.range La.dims.length).map fun j =>
    La.lo.getD j 0 + Lb.lo.getD j 0 + ((packDigits La.stride i).getD j 0 : ℤ)

/-- Compatibility at dimension `n` (decidable): `n` axes, equal widths and strides, and NO WRAP
(each stride at least the next stride times the next product extent `dims_a + dims_b - 1`, the
last stride positive; for two axes: the row stride is at least the sum of the two column
extents minus one). -/
def PackLayout.compat (n : ℕ) (La Lb : PackLayout) : Bool :=
  La.dims.length == n && Lb.dims.length == n && La.stride.length == n &&
    La.stride == Lb.stride && La.width == Lb.width &&
    packNoWrap La.stride (List.zipWith (fun a b => a + b - 1) La.dims Lb.dims)

/-- `Σ c χ_k(θ)` for integer Fourier data. -/
noncomputable def intEval (n : ℕ) (cs : List (CertKey × ℤ)) (θ : Fin n → ℂ) : ℂ :=
  (cs.map fun t => (t.2 : ℂ) * character (certKeyFun n t.1) θ).sum

/-! ### Slots and dense lists -/

theorem PackLayout.slot_eq_some {L : PackLayout} {k : CertKey} {p : ℕ} (h : L.slot k = some p) :
    k.length = L.dims.length ∧
      (∀ j < L.dims.length, 0 ≤ k.getD j 0 - L.lo.getD j 0 ∧
        k.getD j 0 - L.lo.getD j 0 < (L.dims.getD j 0 : ℤ)) ∧
      p = packDot ((L.keyOffsets k).map Int.toNat) L.stride := by
  unfold PackLayout.slot at h
  split_ifs at h with hb
  simp only [Option.some.injEq] at h
  simp only [PackLayout.keyInBox, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hb
  exact ⟨hb.1, hb.2, h.symm⟩

theorem PackLayout.keyOffsets_toNat_getD (L : PackLayout) (k : CertKey) (j : ℕ) :
    ((L.keyOffsets k).map Int.toNat).getD j 0 =
      if j < L.dims.length then (k.getD j 0 - L.lo.getD j 0).toNat else 0 := by
  unfold PackLayout.keyOffsets
  split_ifs with hj
  · simp [List.getD_eq_getElem?_getD, hj]
  · simp [List.getD_eq_getElem?_getD, hj]

/-- In-box keys land below the dense length. -/
theorem PackLayout.slot_lt_denseLen {L : PackLayout} {k : CertKey} {p : ℕ}
    (h : L.slot k = some p) : p < L.denseLen := by
  obtain ⟨_, hbox, rfl⟩ := PackLayout.slot_eq_some h
  have hpos : (L.dims.all fun d => decide (0 < d)) = true := by
    rw [List.all_eq_true]
    intro d hd
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
    obtain ⟨h0, h1⟩ := hbox j hj
    have hg : L.dims.getD j 0 = L.dims[j] := by
      simp [List.getD_eq_getElem?_getD, hj]
    rw [hg] at h1
    simp only [decide_eq_true_eq]
    omega
  rw [PackLayout.denseLen, ite_eq_left hpos]
  have : packDot ((L.keyOffsets k).map Int.toNat) L.stride ≤
      packDot (L.dims.map (· - 1)) L.stride := by
    refine packDot_le_packDot _ _ _ (by simp [PackLayout.keyOffsets]) fun j hj => ?_
    have hj' : j < L.dims.length := by simpa [PackLayout.keyOffsets] using hj
    rw [PackLayout.keyOffsets_toNat_getD, ite_eq_left hj']
    have hb := hbox j hj'
    have hg : (L.dims.map (· - 1)).getD j 0 = L.dims.getD j 0 - 1 := by
      simp [List.getD_eq_getElem?_getD, hj']
    rw [hg]
    omega
  omega

theorem getD_succ_eq_tail_getD (l : List ℤ) (j : ℕ) : l.getD (j + 1) 0 = l.tail.getD j 0 := by
  cases l <;> simp

theorem packDot_cons_left (a : ℕ) (u ss : List ℕ) :
    packDot (a :: u) ss = a * ss.headD 0 + packDot u ss.tail := by
  cases ss <;> simp [packDot]

/-- The kernel walk computes `PackLayout.slot`. -/
theorem packSlotAux_eq (ds : List ℕ) : ∀ (k lo : List ℤ) (ss : List ℕ) (w b : ℕ),
    packSlotAux k lo ds ss = PackLayout.slot ⟨lo, ds, ss, w, b⟩ k := by
  induction ds with
  | nil =>
    intro k lo ss w b
    cases k with
    | nil => simp [packSlotAux, PackLayout.slot, PackLayout.keyInBox, PackLayout.keyOffsets,
        packDot]
    | cons x xs => simp [packSlotAux, PackLayout.slot, PackLayout.keyInBox]
  | cons d ds ih =>
    intro k lo ss w b
    cases k with
    | nil => simp [packSlotAux, PackLayout.slot, PackLayout.keyInBox]
    | cons x xs =>
      have hbox : (⟨lo, d :: ds, ss, w, b⟩ : PackLayout).keyInBox (x :: xs) =
          ((decide (0 ≤ x - lo.headD 0) && decide (x - lo.headD 0 < (d : ℤ))) &&
            (⟨lo.tail, ds, ss.tail, w, b⟩ : PackLayout).keyInBox xs) := by
        have h0 : lo.getD 0 0 = lo.headD 0 := by cases lo <;> rfl
        apply Bool.eq_iff_iff.mpr
        simp only [PackLayout.keyInBox, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
          List.mem_range, decide_eq_true_eq, List.length_cons, Nat.add_right_cancel_iff]
        constructor
        · rintro ⟨hl, h⟩
          have h00 := h 0 (by omega)
          simp only [List.getD_cons_zero, h0] at h00
          refine ⟨h00, hl, fun j hj => ?_⟩
          have := h (j + 1) (by omega)
          simpa [getD_succ_eq_tail_getD] using this
        · rintro ⟨h00, hl, h⟩
          refine ⟨hl, fun j hj => ?_⟩
          cases j with
          | zero =>
            simp only [List.getD_cons_zero, h0]
            exact h00
          | succ j => simpa [getD_succ_eq_tail_getD] using h j (by omega)
      have hoff : ((⟨lo, d :: ds, ss, w, b⟩ : PackLayout).keyOffsets (x :: xs)).map Int.toNat =
          (x - lo.headD 0).toNat ::
            ((⟨lo.tail, ds, ss.tail, w, b⟩ : PackLayout).keyOffsets xs).map Int.toNat := by
        simp only [PackLayout.keyOffsets, List.length_cons, List.range_succ_eq_map, List.map_cons,
          List.map_map, List.getD_cons_zero, Function.comp_def, List.getD_cons_succ,
          getD_succ_eq_tail_getD]
        cases lo <;> rfl
      have ih' := ih xs lo.tail ss.tail w b
      rw [PackLayout.slot, hbox, hoff, packDot_cons_left, packSlotAux]
      rw [PackLayout.slot] at ih'
      rcases hx : x - lo.headD 0 with u | u
      · simp only [Int.ofNat_eq_natCast, Nat.cast_nonneg, decide_true, Nat.cast_lt,
          Bool.true_and, Int.toNat_natCast]
        by_cases hu : u < d
        · simp only [hu, ite_true, decide_true, Bool.true_and, ih']
          split_ifs <;> rfl
        · simp [hu]
      · simp

theorem packStrictAsc_pairwise : ∀ {es : List (ℕ × ℤ)}, packStrictAsc es = true →
    es.Pairwise fun a b => a.1 < b.1
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [packStrictAsc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := packStrictAsc_pairwise h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hc)

theorem packSlotTotal_eq_zero {es : List (ℕ × ℤ)} {p : ℕ} (h : ∀ e ∈ es, e.1 ≠ p) :
    packSlotTotal es p = 0 := by
  have : (es.filter fun e => e.1 == p) = [] :=
    List.filter_eq_nil_iff.mpr fun e he => by simpa using h e he
  simp [packSlotTotal, this]

/-- The linear fill is the dense list of strictly increasing pairs at or above the start. -/
theorem packFill_eq (n : ℕ) : ∀ (p : ℕ) (es : List (ℕ × ℤ)), es.Pairwise (fun a b => a.1 < b.1) →
    (∀ e ∈ es, p ≤ e.1) →
    packFill n p es = (List.range n).map fun q => packSlotTotal es (p + q) := by
  induction n with
  | zero => intro p es _ _; rfl
  | succ n ih =>
    intro p es hs hp
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    cases es with
    | nil =>
      rw [packFill, ih (p + 1) [] List.Pairwise.nil (by simp)]
      simp [packSlotTotal, Function.comp_def]
    | cons e es =>
      have hrest : ∀ e' ∈ es, e.1 < e'.1 := fun e' he' => List.rel_of_pairwise_cons hs he'
      rw [packFill]
      split_ifs with he
      · rw [ih (p + 1) es (List.Pairwise.of_cons hs) (fun e' he' => by
          have := hrest e' he'; omega)]
        congr 1
        · rw [Nat.add_zero, packSlotTotal]
          simp only [List.filter_cons, he, beq_self_eq_true, ite_true, List.map_cons,
            List.sum_cons]
          have h0 := packSlotTotal_eq_zero (es := es) (p := p) fun e' he' => by
            have := hrest e' he'; omega
          rw [packSlotTotal] at h0
          rw [h0, add_zero]
        · refine List.map_congr_left fun q _ => ?_
          simp only [Function.comp_apply, packSlotTotal, List.filter_cons]
          have : ¬ (e.1 = p + (q + 1)) := by omega
          simp [this, Nat.add_assoc, Nat.add_comm 1 q]
      · rw [ih (p + 1) (e :: es) hs (fun e' he' => by
          rcases List.mem_cons.mp he' with rfl | he'
          · have := hp e' (by simp); omega
          · have := hrest e' he'; have := hp e (by simp); omega)]
        congr 1
        · rw [Nat.add_zero, packSlotTotal_eq_zero fun e' he' => by
            rcases List.mem_cons.mp he' with rfl | he'
            · exact he
            · have := hrest e' he'; have := hp e (by simp); omega]
        · refine List.map_congr_left fun q _ => ?_
          simp only [Function.comp_apply, Nat.add_assoc, Nat.add_comm 1 q]

/-- The dense list's characterization: every key in the box, and slot `p` carries the total of
the values at `p`. -/
theorem PackLayout.dense_spec {L : PackLayout} {cs : List (CertKey × ℤ)} {d : List ℤ}
    (h : L.dense cs = some d) :
    (∀ t ∈ cs, L.slot t.1 = some ((L.slot t.1).getD 0)) ∧
      d = (List.range L.denseLen).map fun p =>
        packSlotTotal (cs.map fun t => ((L.slot t.1).getD 0, t.2)) p := by
  have hs : ∀ k, packSlotAux k L.lo L.dims L.stride = L.slot k := fun k =>
    packSlotAux_eq L.dims k L.lo L.stride L.width L.blockRows
  unfold PackLayout.dense at h
  simp only [hs] at h
  split_ifs at h with hall hasc
  · simp only [Option.some.injEq] at h
    refine ⟨fun t ht => ?_, ?_⟩
    · have := List.all_eq_true.mp hall t ht
      cases hs' : L.slot t.1 with
      | none => simp [hs'] at this
      | some p => rfl
    · rw [← h, packFill_eq _ _ _ (packStrictAsc_pairwise hasc) (by simp)]
      simp
  · simp only [Option.some.injEq] at h
    refine ⟨fun t ht => ?_, ?_⟩
    · have := List.all_eq_true.mp hall t ht
      cases hs' : L.slot t.1 with
      | none => simp [hs'] at this
      | some p => rfl
    · rw [← h, packScatter_eq]
      simp

theorem PackLayout.dense_length {L : PackLayout} {cs : List (CertKey × ℤ)} {d : List ℤ}
    (h : L.dense cs = some d) : d.length = L.denseLen := by
  rw [(PackLayout.dense_spec h).2]
  simp

/-! ### Product keys -/

theorem certKeyFun_zipWith_add (n : ℕ) {k l : CertKey} (h : k.length = l.length) :
    certKeyFun n (List.zipWith (· + ·) k l) = certKeyFun n k + certKeyFun n l := by
  funext j
  simp only [certKeyFun, Pi.add_apply, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  by_cases hj : j.val < k.length
  · have hj' : j.val < l.length := h ▸ hj
    simp [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj']
  · have hj' : ¬ j.val < l.length := h ▸ hj
    simp [List.getElem?_eq_none (not_lt.mp hj), List.getElem?_eq_none (not_lt.mp hj')]

/-- **Product keys**: under `compat`, the slot sum of two in-box keys decodes to the key sum. -/
theorem PackLayout.prodKey_slot_add {m : ℕ} {La Lb : PackLayout}
    (hc : PackLayout.compat m La Lb = true) {ka kb : CertKey} {p q : ℕ}
    (hp : La.slot ka = some p) (hq : Lb.slot kb = some q) :
    La.prodKey Lb (p + q) = List.zipWith (· + ·) ka kb := by
  simp only [PackLayout.compat, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨hLa, hLb⟩, hsl⟩, hst⟩, -⟩, hw⟩ := hc
  obtain ⟨hka, hbA, rfl⟩ := PackLayout.slot_eq_some hp
  obtain ⟨hkb, hbB, rfl⟩ := PackLayout.slot_eq_some hq
  set uA := (La.keyOffsets ka).map Int.toNat with huA
  set uB := (Lb.keyOffsets kb).map Int.toNat with huB
  have hlA : uA.length = m := by simp [huA, PackLayout.keyOffsets, hLa]
  have hlB : uB.length = m := by simp [huB, PackLayout.keyOffsets, hLb]
  rw [← hst, ← packDot_add _ _ _ (by rw [hlA, hlB])]
  set es := List.zipWith (fun a b => a + b - 1) La.dims Lb.dims with hes
  have hles : es.length = m := by simp [hes, hLa, hLb]
  have hu : ∀ j < m, (List.zipWith (· + ·) uA uB).getD j 0 =
      (ka.getD j 0 - La.lo.getD j 0).toNat + (kb.getD j 0 - Lb.lo.getD j 0).toNat := by
    intro j hj
    have h1 := PackLayout.keyOffsets_toNat_getD La ka j
    have h2 := PackLayout.keyOffsets_toNat_getD Lb kb j
    rw [ite_eq_left (hLa ▸ hj)] at h1
    rw [ite_eq_left (hLb ▸ hj)] at h2
    rw [← huA] at h1
    rw [← huB] at h2
    rw [← h1, ← h2]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
    rw [List.getElem?_eq_getElem (by omega : j < uA.length),
      List.getElem?_eq_getElem (by omega : j < uB.length)]
    simp
  have hdec := (packDigits_packDot La.stride es (List.zipWith (· + ·) uA uB) hw
    (by rw [List.length_zipWith, hlA, hlB, hles, min_self]) fun j hj => by
      rw [hles] at hj
      rw [hu j hj]
      have hA := hbA j (hLa ▸ hj)
      have hB := hbB j (hLb ▸ hj)
      have he : es.getD j 0 = La.dims.getD j 0 + Lb.dims.getD j 0 - 1 := by
        simp only [hes, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
        rw [List.getElem?_eq_getElem (by omega : j < La.dims.length),
          List.getElem?_eq_getElem (by omega : j < Lb.dims.length)]
        simp
      rw [he]
      omega).1
  rw [PackLayout.prodKey, hdec]
  apply List.ext_getElem
  · simp [hka, hkb, hLa, hLb]
  · intro j h1 h2
    have hj : j < m := by simpa [hLa] using h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith]
    rw [hu j hj]
    obtain ⟨hA0, -⟩ := hbA j (hLa ▸ hj)
    obtain ⟨hB0, -⟩ := hbB j (hLb ▸ hj)
    have gA : ka.getD j 0 = ka[j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < ka.length)]
    have gB : kb.getD j 0 = kb[j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < kb.length)]
    rw [gA] at hA0 ⊢
    rw [gB] at hB0 ⊢
    push_cast
    rw [Int.toNat_of_nonneg hA0, Int.toNat_of_nonneg hB0]
    ring

/-! ### Regrouping finite sums -/

theorem list_sum_map_range_eq {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- Summing a list fiberwise over the values `< D` of a slot function. -/
theorem sum_range_list_fiber {R : Type*} [AddCommMonoid R] {ι : Type*} (l : List ι) (σ : ι → ℕ)
    (D : ℕ) (hσ : ∀ x ∈ l, σ x < D) (F : ι → ℕ → R) :
    ∑ p ∈ Finset.range D, ((l.filter fun x => σ x == p).map fun x => F x p).sum =
      (l.map fun x => F x (σ x)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx : σ x ∈ Finset.range D := Finset.mem_range.mpr (hσ x (by simp))
    have hrest := ih fun y hy => hσ y (by simp [hy])
    have hsplit : ∀ p, ((List.filter (fun y => σ y == p) (x :: l)).map fun y => F y p).sum =
        (if σ x = p then F x p else 0) + ((l.filter fun y => σ y == p).map fun y => F y p).sum := by
      intro p
      by_cases h : σ x = p
      · simp [h]
      · simp [h]
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, hx, ite_true, hrest,
      List.map_cons, List.sum_cons]

/-- The fiberwise sum with a slot weight: `Σ_{p<D} (Σ_{σ x = p} w x) S p = Σ_x w x S (σ x)`. -/
theorem sum_range_fiber_mul {ι : Type*} (l : List ι) (σ : ι → ℕ) (D : ℕ) (hσ : ∀ x ∈ l, σ x < D)
    (w : ι → ℂ) (S : ℕ → ℂ) :
    ∑ p ∈ Finset.range D, ((l.filter fun x => σ x == p).map w).sum * S p =
      (l.map fun x => w x * S (σ x)).sum := by
  rw [← sum_range_list_fiber l σ D hσ fun x p => w x * S p]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← List.sum_map_mul_right]

/-- Cauchy regrouping with a weight: for sequences vanishing from `A` and `B` on,
`Σ_{i < A+B-1} (Σ_{p ≤ i} x_p y_{i-p}) H_i = Σ_{p<A} Σ_{q<B} x_p y_q H_{p+q}`. -/
theorem sum_range_cauchy_weighted {R : Type*} [CommSemiring R] (x y H : ℕ → R) (A B : ℕ)
    (hx : ∀ p, A ≤ p → x p = 0) (hy : ∀ q, B ≤ q → y q = 0) :
    ∑ i ∈ Finset.range (A + B - 1), (∑ p ∈ Finset.range (i + 1), x p * y (i - p)) * H i =
      ∑ p ∈ Finset.range A, ∑ q ∈ Finset.range B, x p * y q * H (p + q) := by
  by_cases hB : B = 0
  · subst hB
    simp only [Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_eq_zero fun p _ => by rw [hy _ (Nat.zero_le _), mul_zero]]
    simp
  set N := A + B - 1 with hN
  have hAN : A ≤ N := by omega
  -- extend the inner range of the right side to `N - p`, then reindex by `i = p + q`
  have h1 : ∀ p ∈ Finset.range A, ∑ q ∈ Finset.range B, x p * y q * H (p + q) =
      ∑ i ∈ Finset.Ico p N, x p * y (i - p) * H i := by
    intro p hp
    rw [Finset.mem_range] at hp
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    have hBN : B ≤ N - p := by omega
    rw [← Finset.sum_range_add_sum_Ico _ hBN, Finset.sum_eq_zero (s := Finset.Ico B (N - p))
      fun q hq => by rw [hy q (Finset.mem_Ico.mp hq).1, mul_zero, zero_mul], add_zero]
  rw [Finset.sum_congr rfl h1]
  -- extend the outer range to `N`
  have h2 : ∑ p ∈ Finset.range A, ∑ i ∈ Finset.Ico p N, x p * y (i - p) * H i =
      ∑ p ∈ Finset.range N, ∑ i ∈ Finset.Ico p N, x p * y (i - p) * H i := by
    rw [← Finset.sum_range_add_sum_Ico _ hAN]
    rw [Finset.sum_eq_zero (s := Finset.Ico A N) fun p hp => Finset.sum_eq_zero fun i _ => by
      rw [hx p (Finset.mem_Ico.mp hp).1, zero_mul, zero_mul]]
    simp
  rw [h2, Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr (by rw [Finset.range_eq_Ico]) fun p _ => ?_
  ring

/-! ### Kronecker substitution for Fourier data -/

/-- The dense value at slot `p` is the fiber total, cast to `ℂ`. -/
theorem PackLayout.dense_getD_cast {L : PackLayout} {cs : List (CertKey × ℤ)} {d : List ℤ}
    (h : L.dense cs = some d) (p : ℕ) :
    ((d.getD p 0 : ℤ) : ℂ) = ((cs.filter fun t => (L.slot t.1).getD 0 == p).map
      fun t => (t.2 : ℂ)).sum := by
  rw [(PackLayout.dense_spec h).2]
  by_cases hp : p < L.denseLen
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
      Option.map_some, Option.getD_some, packSlotTotal, List.filter_map, List.map_map]
    push_cast
    rw [List.map_map]
    rfl
  · have hnil : (cs.filter fun t => (L.slot t.1).getD 0 == p) = [] := by
      rw [List.filter_eq_nil_iff]
      intro t ht
      have hs := (PackLayout.dense_spec h).1 t ht
      have := PackLayout.slot_lt_denseLen hs
      simp only [beq_iff_eq]
      omega
    rw [hnil]
    simp [List.getD_eq_getElem?_getD, hp]

/-- **Kronecker for Fourier data, at every dimension of evaluation**: under `compat` at the
layout's own dimension `m`, the product of two integer Fourier sums (evaluated at any `n`) is the
laid-out convolution of the dense slot lists. -/
theorem PackLayout.intEval_mul_of_compat {m n : ℕ} {La Lb : PackLayout}
    (hc : PackLayout.compat m La Lb = true) {a b : List (CertKey × ℤ)} {da db : List ℤ}
    (ha : La.dense a = some da) (hb : Lb.dense b = some db) (θ : Fin n → ℂ) :
    intEval n a θ * intEval n b θ =
      ((List.range (listConv da db).length).map fun i =>
        ((listConv da db).getD i 0 : ℂ) * character (certKeyFun n (La.prodKey Lb i)) θ).sum := by
  set σA : CertKey × ℤ → ℕ := fun t => (La.slot t.1).getD 0 with hσA
  set σB : CertKey × ℤ → ℕ := fun t => (Lb.slot t.1).getD 0 with hσB
  have hA := (PackLayout.dense_spec ha).1
  have hB := (PackLayout.dense_spec hb).1
  have hlA := PackLayout.dense_length ha
  have hlB := PackLayout.dense_length hb
  have hltA : ∀ t ∈ a, σA t < da.length := fun t ht => hlA ▸ PackLayout.slot_lt_denseLen (hA t ht)
  have hltB : ∀ t ∈ b, σB t < db.length := fun t ht => hlB ▸ PackLayout.slot_lt_denseLen (hB t ht)
  have hstd : ∀ t ∈ a, t.1.length = m := fun t ht => by
    have := (PackLayout.slot_eq_some (hA t ht)).1
    simp only [PackLayout.compat, Bool.and_eq_true, beq_iff_eq] at hc
    rw [this, hc.1.1.1.1.1]
  have hstdB : ∀ t ∈ b, t.1.length = m := fun t ht => by
    have := (PackLayout.slot_eq_some (hB t ht)).1
    simp only [PackLayout.compat, Bool.and_eq_true, beq_iff_eq] at hc
    rw [this, hc.1.1.1.1.2]
  -- the left side as a double sum over terms, with the product key of the slot sum
  have hL : intEval n a θ * intEval n b θ = (a.map fun t => (b.map fun u =>
      (t.2 : ℂ) * (u.2 : ℂ) *
        character (certKeyFun n (La.prodKey Lb (σA t + σB u))) θ).sum).sum := by
    rw [intEval, intEval, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun u hu => ?_)
    rw [PackLayout.prodKey_slot_add hc (hA t ht) (hB u hu),
      certKeyFun_zipWith_add n (by rw [hstd t ht, hstdB u hu]), ← character_mul]
    ring
  rw [hL]
  by_cases hemp : da.isEmpty || db.isEmpty
  · have hconv : listConv da db = [] := by simp [listConv, hemp]
    rw [hconv]
    simp only [List.length_nil, List.range_zero, List.map_nil, List.sum_nil]
    rcases Bool.or_eq_true_iff.mp hemp with h | h
    · have h0 : da.length = 0 := by simpa using h
      have : a = [] := List.eq_nil_iff_forall_not_mem.mpr fun t ht => by
        have := hltA t ht; omega
      simp [this]
    · have h0 : db.length = 0 := by simpa using h
      have : b = [] := List.eq_nil_iff_forall_not_mem.mpr fun t ht => by
        have := hltB t ht; omega
      simp [this]
  · have hconv : listConv da db = (List.range (da.length + db.length - 1)).map fun k =>
        ((List.range (k + 1)).map fun i => da.getD i 0 * db.getD (k - i) 0).sum := by
      simp [listConv, hemp]
    rw [hconv, List.length_map, List.length_range, list_sum_map_range_eq]
    have hconvi : ∀ i ∈ Finset.range (da.length + db.length - 1),
        ((((List.range (da.length + db.length - 1)).map fun k =>
          ((List.range (k + 1)).map fun i => da.getD i 0 * db.getD (k - i) 0).sum).getD i 0 :
            ℤ) : ℂ) * character (certKeyFun n (La.prodKey Lb i)) θ =
        (∑ p ∈ Finset.range (i + 1), ((da.getD p 0 : ℤ) : ℂ) * ((db.getD (i - p) 0 : ℤ) : ℂ)) *
          character (certKeyFun n (La.prodKey Lb i)) θ := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
        Option.getD_some, sum_map_range_eq]
      push_cast
      rfl
    rw [Finset.sum_congr rfl hconvi, sum_range_cauchy_weighted
      (fun p => ((da.getD p 0 : ℤ) : ℂ)) (fun q => ((db.getD q 0 : ℤ) : ℂ))
      (fun i => character (certKeyFun n (La.prodKey Lb i)) θ) da.length db.length
      (fun p hp => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hp])
      (fun q hq => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hq])]
    -- expand the dense values as fiber totals and collapse the fibers
    have hxa := PackLayout.dense_getD_cast ha
    have hxb := PackLayout.dense_getD_cast hb
    simp only [hxa, hxb]
    symm
    calc (∑ p ∈ Finset.range da.length, ∑ q ∈ Finset.range db.length,
          ((a.filter fun t => (La.slot t.1).getD 0 == p).map fun t => (t.2 : ℂ)).sum *
            ((b.filter fun t => (Lb.slot t.1).getD 0 == q).map fun t => (t.2 : ℂ)).sum *
            character (certKeyFun n (La.prodKey Lb (p + q))) θ : ℂ)
        = ∑ p ∈ Finset.range da.length,
          ((a.filter fun t => (La.slot t.1).getD 0 == p).map fun t => (t.2 : ℂ)).sum *
            (b.map fun u => (u.2 : ℂ) *
              character (certKeyFun n (La.prodKey Lb (p + (Lb.slot u.1).getD 0))) θ).sum := by
          refine Finset.sum_congr rfl fun p _ => ?_
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          congr 1
          exact sum_range_fiber_mul b (fun u => (Lb.slot u.1).getD 0) db.length hltB
            (fun u => (u.2 : ℂ)) fun q => character (certKeyFun n (La.prodKey Lb (p + q))) θ
      _ = _ := by
          refine (sum_range_fiber_mul a (fun t => (La.slot t.1).getD 0) da.length hltA
            (fun t => (t.2 : ℂ)) fun p => (b.map fun u => (u.2 : ℂ) *
              character (certKeyFun n (La.prodKey Lb (p + (Lb.slot u.1).getD 0))) θ).sum).trans ?_
          refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
          rw [← List.sum_map_mul_left]
          refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
          ring

/-- **Kronecker for Fourier data**: under `compat`, the product polynomial is the laid-out
convolution of the dense slot lists. -/
theorem PackLayout.intEval_mul {n : ℕ} {La Lb : PackLayout} (hc : PackLayout.compat n La Lb = true)
    {a b : List (CertKey × ℤ)} {da db : List ℤ} (ha : La.dense a = some da)
    (hb : Lb.dense b = some db) (θ : Fin n → ℂ) :
    intEval n a θ * intEval n b θ =
      ((List.range (listConv da db).length).map fun i =>
        ((listConv da db).getD i 0 : ℂ) * character (certKeyFun n (La.prodKey Lb i)) θ).sum :=
  PackLayout.intEval_mul_of_compat hc ha hb θ

end KAM.Certificate
