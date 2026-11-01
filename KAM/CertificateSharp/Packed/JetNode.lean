/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.StageZ
public import KAM.CertificateSharp.Packed.TorsChain

/-!
# Packed jet nodes (`V2-PACKED.md` §12.3)

A node is a packed model (`PEnc`) of a slot function on the box `Lb` (or, for a constant, on the
one-slot layout `LU0`), with its load, its scale `2^e`, its radius and its norm bound. The
operations, all in the kernel and with no literal:

* `jUp`: a change of scale (and from `LU0` to `Lb`) by an exact unit shift (`PEnc.shift`);
* `jAdd`: both operands brought to the larger scale, then the exact sum (`PEnc.add`);
* `jMul`: the exact product (`PEnc.mul`); when both operands live on the box, the product lives
  on the window `Lw` and is reduced at once to the box at the scale `2^eT`: the candidate is
  computed (`zPC`), validated by `boxOk`, and its radius is the product's plus the packed norm of
  the residual (`PEnc.reduceZ`);
* `jRed`: the same reduce in place on the box (after sums and products by constants).

The book guards (`jBookOk`) are decided once per segment: the layouts and their windows, the zero
slots and the three norm guards at the largest loads and rounding shift allowed. Each operation
then only compares its load and its shift against the book (`decide`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-- The book of a packed jet segment (untrusted numbers; `jBookOk` checks them). -/
structure JBook where
  /-- the box of the nodes, the one-slot layout of the constants, the window of the products -/
  Lb : PackLayout
  LU0 : PackLayout
  Lw : PackLayout
  /-- the weight exponent of the packed norm -/
  q : ℕ
  /-- a reduced node packs digits in `[-2^lb, 2^lb]` -/
  lb : ℕ
  /-- the norm guards: residual on the window, residual on the box, reduced node -/
  lr : ℕ
  lrb : ℕ
  ln : ℕ
  /-- the largest load of a product before its reduce, of a node before a reduce in place -/
  aW : ℕ
  aB : ℕ
  /-- the largest rounding shift -/
  smax : ℕ
  /-- the offset exponents of the candidate computation on the window and on the box, and the
  offset (in slots) of the box in the window -/
  ls : ℕ
  lsb : ℕ
  off : ℕ
  /-- the scale `2^P` of leaf nodes (constants, actions, characters, witnesses), the load bound of
  a constant on `LU0` and its norm guard -/
  P : ℕ
  aC : ℕ
  lc : ℕ
  /-- the norm guards of a reduce in place on `LU0` (residual, reduced node) -/
  lrc : ℕ
  lnc : ℕ

/-- A packed jet node. -/
structure JNode (α : Type) where
  /-- on the one-slot layout `LU0` (a constant) or on the box `Lb` -/
  u : Bool
  A : ℕ
  e : ℕ
  x : PC
  r : α
  nb : α

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (jb : JBook)

/-- The layout of a node. -/
def jLay (u : Bool) : PackLayout := if u then jb.LU0 else jb.Lb

/-- **The book guards** (once per segment). -/
def jBookOk : Bool :=
  layoutWf jb.Lb && layoutWf jb.LU0 && PackLayout.compat n jb.Lb jb.Lb &&
    PackLayout.compat n jb.Lb jb.LU0 && PackLayout.compat n jb.LU0 jb.Lb &&
    PackLayout.compat n jb.LU0 jb.LU0 && layoutEq (win jb.Lb jb.Lb) jb.Lw &&
    layoutEq (win jb.Lb jb.LU0) jb.Lb && layoutEq (win jb.LU0 jb.Lb) jb.Lb &&
    layoutEq (win jb.LU0 jb.LU0) jb.LU0 && (jb.Lb.slot (List.replicate n 0)).isSome &&
    (jb.LU0.slot (List.replicate n 0)).isSome &&
    normOk W jb.q jb.lr (jb.aW + mulLoad jb.Lb jb.Lb (2 ^ jb.lb) (2 ^ jb.smax)) jb.Lw &&
    normOk W jb.q jb.lrb (jb.aB + mulLoad jb.Lb jb.LU0 (2 ^ jb.lb) (2 ^ jb.smax)) jb.Lb &&
    normOk W jb.q jb.ln (2 ^ jb.lb) jb.Lb && normOk W jb.q jb.lc jb.aC jb.LU0 &&
    normOk W jb.q jb.lrc (jb.aB + mulLoad jb.LU0 jb.LU0 (2 ^ jb.lb) (2 ^ jb.smax)) jb.LU0 &&
    normOk W jb.q jb.lnc (2 ^ jb.lb) jb.LU0

/-- The unit `2^k` at the zero slot of a layout. -/
def jUnit (L : PackLayout) (k : ℕ) : PC := pcUnit L.width (zslot n L) (2 ^ k)

/-- A node at the layout `u'` (only `LU0 → Lb` or unchanged) and the scale `e' ≥ e`. -/
def jUp (nd : JNode α) (u' : Bool) (e' : ℕ) : Option (JNode α) :=
  if nd.u = u' ∧ nd.e = e' then some nd
  else if nd.e ≤ e' then
    if nd.u = true ∧ u' = false then
      some ⟨false, mulLoad jb.LU0 jb.Lb nd.A (2 ^ (e' - nd.e)), e',
        pcMul nd.x (jUnit n jb.Lb (e' - nd.e)), nd.r, nd.nb⟩
    else if nd.u = u' then
      some ⟨u', mulLoad (jLay jb u') jb.LU0 nd.A (2 ^ (e' - nd.e)), e',
        pcMul nd.x (jUnit n jb.LU0 (e' - nd.e)), nd.r, nd.nb⟩
    else none
  else none

/-- The sum of two nodes. -/
def jAdd (a b : JNode α) : Option (JNode α) :=
  match jUp n jb a (a.u && b.u) (max a.e b.e), jUp n jb b (a.u && b.u) (max a.e b.e) with
  | some a', some b' =>
    some ⟨a.u && b.u, a'.A + b'.A, max a.e b.e, pcAdd a'.x b'.x, upAdd a'.r b'.r,
      upAdd a'.nb b'.nb⟩
  | _, _ => none

/-- A reduce of the product `x` (load `A`, scale `2^e`, radius `r`) on the window to the box at
the scale `2^eT`. -/
def jRedW (A e : ℕ) (x : PC) (r : α) (eT : ℕ) : Option (JNode α) :=
  if A ≤ jb.aW ∧ eT < e ∧ e - eT ≤ jb.smax then
    if boxOk jb.Lb jb.lb (zPC jb.Lw.width jb.Lw.denseLen jb.ls (e - eT) (jb.Lb.stride.getD 0 0)
          (jb.Lb.dims.getD 0 0) (jb.Lb.dims.getD 1 0) jb.off x).re &&
        boxOk jb.Lb jb.lb (zPC jb.Lw.width jb.Lw.denseLen jb.ls (e - eT)
          (jb.Lb.stride.getD 0 0) (jb.Lb.dims.getD 0 0) (jb.Lb.dims.getD 1 0) jb.off x).im then
      some ⟨false, 2 ^ jb.lb, eT,
        zPC jb.Lw.width jb.Lw.denseLen jb.ls (e - eT) (jb.Lb.stride.getD 0 0)
          (jb.Lb.dims.getD 0 0) (jb.Lb.dims.getD 1 0) jb.off x,
        upAdd r (pnorm W jb.q jb.lr jb.Lw e (zRes n jb.Lb (e - eT) x
          (zPC jb.Lw.width jb.Lw.denseLen jb.ls (e - eT) (jb.Lb.stride.getD 0 0)
            (jb.Lb.dims.getD 0 0) (jb.Lb.dims.getD 1 0) jb.off x))),
        pnorm W jb.q jb.ln jb.Lb eT
          (zPC jb.Lw.width jb.Lw.denseLen jb.ls (e - eT) (jb.Lb.stride.getD 0 0)
            (jb.Lb.dims.getD 0 0) (jb.Lb.dims.getD 1 0) jb.off x)⟩
    else none
  else none

/-- The norm guards of a reduce in place on the node's layout. -/
def jRedL (u : Bool) : ℕ := if u then jb.lrc else jb.lrb

def jRedN (u : Bool) : ℕ := if u then jb.lnc else jb.ln

/-- A reduce in place of a node (on the box or on `LU0`) to the scale `2^eT`. -/
def jRed (nd : JNode α) (eT : ℕ) : Option (JNode α) :=
  if nd.A ≤ jb.aB ∧ eT < nd.e ∧ nd.e - eT ≤ jb.smax then
    if boxOk (jLay jb nd.u) jb.lb (zPC (jLay jb nd.u).width (jLay jb nd.u).denseLen jb.lsb
          (nd.e - eT)
          ((jLay jb nd.u).stride.getD 0 0) ((jLay jb nd.u).dims.getD 0 0)
          ((jLay jb nd.u).dims.getD 1 0) 0 nd.x).re &&
        boxOk (jLay jb nd.u) jb.lb (zPC (jLay jb nd.u).width (jLay jb nd.u).denseLen jb.lsb
          (nd.e - eT) ((jLay jb nd.u).stride.getD 0 0) ((jLay jb nd.u).dims.getD 0 0)
          ((jLay jb nd.u).dims.getD 1 0) 0 nd.x).im then
      some ⟨nd.u, 2 ^ jb.lb, eT,
        zPC (jLay jb nd.u).width (jLay jb nd.u).denseLen jb.lsb (nd.e - eT)
          ((jLay jb nd.u).stride.getD 0 0) ((jLay jb nd.u).dims.getD 0 0)
          ((jLay jb nd.u).dims.getD 1 0) 0 nd.x,
        upAdd nd.r (pnorm W jb.q (jRedL jb nd.u) (jLay jb nd.u) nd.e
          (zRes n jb.LU0 (nd.e - eT) nd.x
            (zPC (jLay jb nd.u).width (jLay jb nd.u).denseLen jb.lsb (nd.e - eT)
              ((jLay jb nd.u).stride.getD 0 0) ((jLay jb nd.u).dims.getD 0 0)
              ((jLay jb nd.u).dims.getD 1 0) 0 nd.x))),
        pnorm W jb.q (jRedN jb nd.u) (jLay jb nd.u) eT
          (zPC (jLay jb nd.u).width (jLay jb nd.u).denseLen jb.lsb (nd.e - eT)
            ((jLay jb nd.u).stride.getD 0 0) ((jLay jb nd.u).dims.getD 0 0)
            ((jLay jb nd.u).dims.getD 1 0) 0 nd.x)⟩
    else none
  else none

/-- The product of two nodes; a box-by-box product is reduced to the box at the scale `2^eT`. -/
def jMul (a b : JNode α) (eT : ℕ) : Option (JNode α) :=
  if a.u || b.u then
    some ⟨a.u && b.u, mulLoad (jLay jb a.u) (jLay jb b.u) a.A b.A, a.e + b.e, pcMul a.x b.x,
      pmulRad a.nb a.r b.nb b.r, upMul a.nb b.nb⟩
  else jRedW n W jb (mulLoad jb.Lb jb.Lb a.A b.A) (a.e + b.e) (pcMul a.x b.x)
    (pmulRad a.nb a.r b.nb b.r) eT

end Defs

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight} {jb : JBook}

/-- A node encloses `f`: a packed model on its layout at its scale. -/
def JEnc (n : ℕ) (W : CertWeight) (jb : JBook) (nd : JNode α) (f : (Fin n → ℂ) → ℂ) : Prop :=
  PEnc (jLay jb nd.u) nd.A nd.e nd.x nd.r nd.nb n W.rho f

/-- The book facts. -/
structure JBookFacts (n : ℕ) (W : CertWeight) (jb : JBook) : Prop where
  wb : layoutWf jb.Lb = true
  w0 : layoutWf jb.LU0 = true
  cbb : PackLayout.compat n jb.Lb jb.Lb = true
  cb0 : PackLayout.compat n jb.Lb jb.LU0 = true
  c0b : PackLayout.compat n jb.LU0 jb.Lb = true
  c00 : PackLayout.compat n jb.LU0 jb.LU0 = true
  ebb : win jb.Lb jb.Lb = jb.Lw
  eb0 : win jb.Lb jb.LU0 = jb.Lb
  e0b : win jb.LU0 jb.Lb = jb.Lb
  e00 : win jb.LU0 jb.LU0 = jb.LU0
  sb : jb.Lb.slot (List.replicate n 0) = some (zslot n jb.Lb)
  s0 : jb.LU0.slot (List.replicate n 0) = some (zslot n jb.LU0)
  nW : normOk W jb.q jb.lr (jb.aW + mulLoad jb.Lb jb.Lb (2 ^ jb.lb) (2 ^ jb.smax)) jb.Lw = true
  nB : normOk W jb.q jb.lrb (jb.aB + mulLoad jb.Lb jb.LU0 (2 ^ jb.lb) (2 ^ jb.smax)) jb.Lb =
    true
  nN : normOk W jb.q jb.ln (2 ^ jb.lb) jb.Lb = true
  nC : normOk W jb.q jb.lc jb.aC jb.LU0 = true
  nBc : normOk W jb.q jb.lrc (jb.aB + mulLoad jb.LU0 jb.LU0 (2 ^ jb.lb) (2 ^ jb.smax)) jb.LU0 = true
  nNc : normOk W jb.q jb.lnc (2 ^ jb.lb) jb.LU0 = true

theorem slot_eq_zslot {L : PackLayout} (h : (L.slot (List.replicate n 0)).isSome = true) :
    L.slot (List.replicate n 0) = some (zslot n L) := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
  simp [zslot, hp]

theorem jBookOk_spec (h : jBookOk n W jb = true) : JBookFacts n W jb := by
  simp only [jBookOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, layoutEq_eq h7, layoutEq_eq h8, layoutEq_eq h9,
    layoutEq_eq h10, slot_eq_zslot h11, slot_eq_zslot h12, h13, h14, h15, h16, h17, h18⟩

/-- `normOk` is monotone in the load. -/
theorem normOk_mono {q l B B' : ℕ} {L : PackLayout} (h : normOk W q l B L = true) (hB : B' ≤ B) :
    normOk W q l B' L = true := by
  simp only [normOk, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2⟩, h.1.1.1.1.1.1.2⟩, h.1.1.1.1.1.2⟩,
    h.1.1.1.1.2⟩, h.1.1.1.2⟩, lt_of_le_of_lt hB h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem mulLoad_mono {La Lb : PackLayout} {A A' B B' : ℕ} (hA : A ≤ A') (hB : B ≤ B') :
    mulLoad La Lb A B ≤ mulLoad La Lb A' B' := by
  unfold mulLoad
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hA) hB)

/-- The unit `2^k` as a packed representation of the constant. -/
theorem jUnit_rep {L : PackLayout} (hw : layoutWf L = true)
    (hs : L.slot (List.replicate n 0) = some (zslot n L)) (k : ℕ) :
    PCRep L (2 ^ k) (jUnit n L k) n (fun _ => (2 : ℂ) ^ k) := by
  have h := PCRep.unit (n := n) hw hs ((2 : ℤ) ^ k)
  rw [Int.natAbs_pow] at h
  simpa [jUnit] using h

omit [CertArith α] [LawfulCertArith α] in
/-- The layout and the scale of a lifted node. -/
theorem jUp_spec {nd nd' : JNode α} {u' : Bool} {e' : ℕ} (h : jUp n jb nd u' e' = some nd') :
    nd'.u = u' ∧ nd'.e = e' := by
  unfold jUp at h
  split_ifs at h with h1 h2 h3 h4
  · cases h; exact h1
  · cases h; exact ⟨h3.2.symm, rfl⟩
  · cases h; exact ⟨rfl, rfl⟩

omit [LawfulCertArith α] in
theorem jUp_sound (B : JBookFacts n W jb) {nd nd' : JNode α} {f : (Fin n → ℂ) → ℂ}
    (hx : JEnc n W jb nd f) {u' : Bool} {e' : ℕ} (h : jUp n jb nd u' e' = some nd') :
    JEnc n W jb nd' f := by
  unfold jUp at h
  split_ifs at h with h1 h2 h3 h4
  · cases h; exact hx
  · cases h
    obtain ⟨hu, -⟩ := h3
    unfold JEnc jLay at hx ⊢
    rw [hu] at hx
    simp only [↓reduceIte] at hx
    have := hx.shift B.c0b B.w0 B.wb (jUnit_rep B.wb B.sb (e' - nd.e))
    rw [B.e0b, Nat.add_sub_cancel' h2] at this
    simpa using this
  · cases h
    unfold JEnc at hx ⊢
    rw [h4] at hx
    have := hx.shift (m := n) (by cases u' <;> simp [jLay, B.c00, B.cb0]) (by cases u' <;>
      simp [jLay, B.w0, B.wb]) B.w0 (jUnit_rep B.w0 B.s0 (e' - nd.e))
    rw [Nat.add_sub_cancel' h2, show win (jLay jb u') jb.LU0 = jLay jb u' by
      cases u' <;> simp [jLay, B.e00, B.eb0]] at this
    exact this

theorem jAdd_sound (B : JBookFacts n W jb) {a b c : JNode α} {f g : (Fin n → ℂ) → ℂ}
    (ha : JEnc n W jb a f) (hb : JEnc n W jb b g) (h : jAdd n jb a b = some c) :
    JEnc n W jb c (fun θ => f θ + g θ) := by
  unfold jAdd at h
  split at h
  · rename_i a' b' ha' hb'
    cases h
    have h1 := jUp_sound B ha ha'
    have h2 := jUp_sound B hb hb'
    obtain ⟨hu1, he1⟩ := jUp_spec ha'
    obtain ⟨hu2, he2⟩ := jUp_spec hb'
    unfold JEnc at h1 h2 ⊢
    rw [hu1, he1] at h1
    rw [hu2, he2] at h2
    exact h1.add h2
  · cases h

/-- The reduce on the window. -/
theorem jRedW_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) (B : JBookFacts n W jb)
    {A e eT : ℕ} {x : PC} {r nb : α} {c : JNode α} {f : (Fin n → ℂ) → ℂ}
    (hx : PEnc jb.Lw A e x r nb n W.rho f) (h : jRedW n W jb A e x r eT = some c) :
    JEnc n W jb c f := by
  unfold jRedW at h
  split_ifs at h with h1 h2
  · cases h
    simp only [Bool.and_eq_true] at h2
    obtain ⟨hA, he, hs⟩ := h1
    have hokr := normOk_mono B.nW (Nat.add_le_add hA (mulLoad_mono le_rfl
      (Nat.pow_le_pow_right (by norm_num) hs)))
    have := PEnc.reduceZ (m := n) hW B.cbb B.wb B.wb B.ebb B.sb (Nat.sub_le e eT) hokr B.nN hx
      h2.1 h2.2
    rw [Nat.sub_sub_self he.le] at this
    exact this

theorem jRed_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) (B : JBookFacts n W jb)
    {nd c : JNode α} {eT : ℕ} {f : (Fin n → ℂ) → ℂ} (hx : JEnc n W jb nd f)
    (h : jRed n W jb nd eT = some c) : JEnc n W jb c f := by
  unfold jRed at h
  split_ifs at h with h1 h2
  · cases h
    simp only [Bool.and_eq_true] at h2
    obtain ⟨hA, he, hs⟩ := h1
    have hload : nd.A + mulLoad (jLay jb nd.u) jb.LU0 (2 ^ jb.lb) (2 ^ (nd.e - eT)) ≤
        jb.aB + mulLoad (jLay jb nd.u) jb.LU0 (2 ^ jb.lb) (2 ^ jb.smax) :=
      Nat.add_le_add hA (mulLoad_mono le_rfl (Nat.pow_le_pow_right (by norm_num) hs))
    unfold JEnc at hx ⊢
    cases hu : nd.u
    · simp only [hu, jLay, jRedL, jRedN, Bool.false_eq_true, ↓reduceIte] at hx h2 hload ⊢
      have := PEnc.reduceZ (m := n) hW B.cb0 B.wb B.w0 B.eb0 B.s0 (Nat.sub_le nd.e eT)
        (normOk_mono B.nB hload) B.nN hx h2.1 h2.2
      rw [Nat.sub_sub_self he.le] at this
      exact this
    · simp only [hu, jLay, jRedL, jRedN, ↓reduceIte] at hx h2 hload ⊢
      have := PEnc.reduceZ (m := n) hW B.c00 B.w0 B.w0 B.e00 B.s0 (Nat.sub_le nd.e eT)
        (normOk_mono B.nBc hload) B.nNc hx h2.1 h2.2
      rw [Nat.sub_sub_self he.le] at this
      exact this

theorem jMul_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) (B : JBookFacts n W jb)
    {a b c : JNode α} {eT : ℕ} {f g : (Fin n → ℂ) → ℂ} (ha : JEnc n W jb a f)
    (hb : JEnc n W jb b g) (h : jMul n W jb a b eT = some c) :
    JEnc n W jb c (fun θ => f θ * g θ) := by
  unfold jMul at h
  split_ifs at h with h1
  · cases h
    have hc : PackLayout.compat n (jLay jb a.u) (jLay jb b.u) = true := by
      cases a.u <;> cases b.u <;> simp [jLay, B.cbb, B.cb0, B.c0b, B.c00]
    have hwin : win (jLay jb a.u) (jLay jb b.u) = jLay jb (a.u && b.u) := by
      cases hau : a.u <;> cases hbu : b.u <;> simp_all [jLay, B.e00, B.eb0, B.e0b]
    have hwa : layoutWf (jLay jb a.u) = true := by cases a.u <;> simp [jLay, B.wb, B.w0]
    have hwb : layoutWf (jLay jb b.u) = true := by cases b.u <;> simp [jLay, B.wb, B.w0]
    have := PEnc.mul hc hwa hwb ha hb
    unfold JEnc
    rw [← hwin]
    exact this
  · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h1
    have ha' : PEnc jb.Lb a.A a.e a.x a.r a.nb n W.rho f := by
      have := ha; unfold JEnc jLay at this; rw [h1.1] at this; simpa using this
    have hb' : PEnc jb.Lb b.A b.e b.x b.r b.nb n W.rho g := by
      have := hb; unfold JEnc jLay at this; rw [h1.2] at this; simpa using this
    have := PEnc.mul B.cbb B.wb B.wb ha' hb'
    rw [B.ebb] at this
    exact jRedW_sound hW B this h

end Sound

end KAM.CertificateSharp.Packed
