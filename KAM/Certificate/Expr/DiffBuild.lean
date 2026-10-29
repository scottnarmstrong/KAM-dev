/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.DiffCalculus

/-!
# Building straight-line programs with folded slots

The program builder of the jet compiler. A program under construction is its operation list; every
combinator appends operations and returns the new list with the slot of the result. A slot is an
`Option ℕ`: `none` is the identically zero slot (zero folding), so a sum with a `none` summand
adds nothing and a product with a `none` factor is `none`. `Realizes n S s x g` says that on `S`
the slot `x` of the program `s` takes the values of `g`; it is preserved by extending the program.
Tables of slots are built by threading the program through a list (`slpMapSt`).
-/

@[expose] public noncomputable section

namespace KAM.Certificate

variable {n : ℕ}

local notation "Ph" => (Fin n → ℂ) × (Fin n → ℂ)

/-- Append one operation; the result is its slot. -/
def slpEmit (s : List SlpOp) (op : SlpOp) : List SlpOp × Option ℕ := (s ++ [op], some s.length)

/-- Sum of two slots (a `none` summand is dropped). -/
def slpAddO (s : List SlpOp) : Option ℕ → Option ℕ → List SlpOp × Option ℕ
  | none, y => (s, y)
  | some a, none => (s, some a)
  | some a, some b => slpEmit s (.add a b)

/-- Product of two slots (`none` if a factor is `none`). -/
def slpMulO (s : List SlpOp) : Option ℕ → Option ℕ → List SlpOp × Option ℕ
  | some a, some b => slpEmit s (.mul a b)
  | _, _ => (s, none)

/-- The constant `(re + i im)(2π)^deg` times a slot (`none` if the slot or the constant is zero). -/
def slpScaleO (s : List SlpOp) (re im : ℚ) (deg : ℤ) : Option ℕ → List SlpOp × Option ℕ
  | none => (s, none)
  | some x =>
    if re = 0 ∧ im = 0 then (s, none)
    else slpMulO (slpEmit s (.const re im deg)).1 (slpEmit s (.const re im deg)).2 (some x)

/-- The value of a slot (`none` is `0`). -/
def slpOv (n : ℕ) (s : List SlpOp) (z : (Fin n → ℂ) × (Fin n → ℂ)) : Option ℕ → ℂ
  | none => 0
  | some i => (Slp.vals n z s).getD i 0

/-- A slot is `none` or an existing slot of the program. -/
def SlotOk (s : List SlpOp) : Option ℕ → Prop
  | none => True
  | some i => i < s.length

/-- On `S`, the slot `x` of the program `s` takes the values of `g`. -/
def Realizes (n : ℕ) (S : Set ((Fin n → ℂ) × (Fin n → ℂ))) (s : List SlpOp) (x : Option ℕ)
    (g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop :=
  SlotOk s x ∧ ∀ z ∈ S, slpOv n s z x = g z

theorem SlotOk.mono {s s' : List SlpOp} (h : s <+: s') {x : Option ℕ} (hx : SlotOk s x) :
    SlotOk s' x := by
  cases x with
  | none => trivial
  | some i =>
    obtain ⟨t, rfl⟩ := h
    simp only [SlotOk, List.length_append] at hx ⊢
    omega

theorem Realizes.mono {S : Set Ph} {s s' : List SlpOp} (h : s <+: s') {x : Option ℕ}
    {g : Ph → ℂ} (hx : Realizes n S s x g) : Realizes n S s' x g := by
  refine ⟨hx.1.mono h, fun z hz => ?_⟩
  rw [← hx.2 z hz]
  cases x with
  | none => rfl
  | some i =>
    obtain ⟨t, rfl⟩ := h
    simp only [slpOv]
    exact (Slp.val_append n z s t hx.1)

theorem Realizes.congr {S : Set Ph} {s : List SlpOp} {x : Option ℕ} {g h : Ph → ℂ}
    (hx : Realizes n S s x g) (hgh : Set.EqOn g h S) : Realizes n S s x h :=
  ⟨hx.1, fun z hz => (hx.2 z hz).trans (hgh hz)⟩

theorem Realizes.none (S : Set Ph) (s : List SlpOp) : Realizes n S s none (fun _ => 0) :=
  ⟨trivial, fun _ _ => rfl⟩

theorem slpEmit_prefix (s : List SlpOp) (op : SlpOp) : s <+: (slpEmit s op).1 :=
  List.prefix_append _ _

theorem slpEmit_realizes {S : Set Ph} (s : List SlpOp) (op : SlpOp) (g : Ph → ℂ)
    (hg : ∀ z ∈ S, op.step n z (Slp.vals n z s) = g z) :
    Realizes n S (slpEmit s op).1 (slpEmit s op).2 g := by
  refine ⟨by simp [slpEmit, SlotOk], fun z hz => ?_⟩
  simp only [slpEmit, slpOv]
  rw [Slp.val_snoc_self]
  exact hg z hz

theorem slpAddO_spec {S : Set Ph} {s : List SlpOp} {x y : Option ℕ} {g h : Ph → ℂ}
    (hx : Realizes n S s x g) (hy : Realizes n S s y h) :
    s <+: (slpAddO s x y).1 ∧
      Realizes n S (slpAddO s x y).1 (slpAddO s x y).2 (fun z => g z + h z) := by
  cases x with
  | none =>
    refine ⟨List.prefix_refl _, hy.1, fun z hz => ?_⟩
    simp only [slpAddO]
    rw [hy.2 z hz, ← hx.2 z hz]
    simp [slpOv]
  | some a =>
    cases y with
    | none =>
      refine ⟨List.prefix_refl _, hx.1, fun z hz => ?_⟩
      simp only [slpAddO]
      rw [hx.2 z hz, ← hy.2 z hz]
      simp [slpOv]
    | some b =>
      refine ⟨slpEmit_prefix _ _, slpEmit_realizes _ _ _ fun z hz => ?_⟩
      have h1 := hx.2 z hz
      have h2 := hy.2 z hz
      simp only [slpOv, List.getD_eq_getElem?_getD] at h1 h2
      simp [SlpOp.step, h1, h2]

theorem slpMulO_spec {S : Set Ph} {s : List SlpOp} {x y : Option ℕ} {g h : Ph → ℂ}
    (hx : Realizes n S s x g) (hy : Realizes n S s y h) :
    s <+: (slpMulO s x y).1 ∧
      Realizes n S (slpMulO s x y).1 (slpMulO s x y).2 (fun z => g z * h z) := by
  cases x with
  | none =>
    refine ⟨List.prefix_refl _, trivial, fun z hz => ?_⟩
    have := hx.2 z hz
    simp only [slpOv] at this
    simp [slpMulO, slpOv, ← this]
  | some a =>
    cases y with
    | none =>
      refine ⟨List.prefix_refl _, trivial, fun z hz => ?_⟩
      have := hy.2 z hz
      simp only [slpOv] at this
      simp [slpMulO, slpOv, ← this]
    | some b =>
      refine ⟨slpEmit_prefix _ _, slpEmit_realizes _ _ _ fun z hz => ?_⟩
      have h1 := hx.2 z hz
      have h2 := hy.2 z hz
      simp only [slpOv, List.getD_eq_getElem?_getD] at h1 h2
      simp [SlpOp.step, h1, h2]

theorem slpScaleO_spec {S : Set Ph} {s : List SlpOp} {x : Option ℕ} {g : Ph → ℂ}
    (re im : ℚ) (deg : ℤ) (hx : Realizes n S s x g) :
    s <+: (slpScaleO s re im deg x).1 ∧
      Realizes n S (slpScaleO s re im deg x).1 (slpScaleO s re im deg x).2
        (fun z => slpConstVal re im deg * g z) := by
  cases x with
  | none =>
    refine ⟨List.prefix_refl _, trivial, fun z hz => ?_⟩
    have := hx.2 z hz
    simp only [slpOv] at this
    simp [slpScaleO, slpOv, ← this]
  | some a =>
    by_cases hc : re = 0 ∧ im = 0
    · refine ⟨?_, by simp [slpScaleO, hc, SlotOk], fun z hz => ?_⟩
      · simp [slpScaleO, hc]
      · obtain ⟨rfl, rfl⟩ := hc
        simp [slpScaleO, slpOv, slpConstVal]
    · simp only [slpScaleO, hc, ite_false]
      have hc1 := slpEmit_realizes (S := S) s (.const re im deg) (fun _ => slpConstVal re im deg)
        (fun z hz => rfl)
      have hxm := hx.mono (slpEmit_prefix s (.const re im deg))
      obtain ⟨hp, hr⟩ := slpMulO_spec hc1 hxm
      exact ⟨(slpEmit_prefix _ _).trans hp, hr⟩

/-- Thread the program through a list, collecting one slot per element. -/
def slpMapSt {α : Type} (f : ℕ → List SlpOp → List SlpOp × α) :
    List ℕ → List SlpOp → List SlpOp × List α
  | [], s => (s, [])
  | i :: l, s =>
    let r := f i s
    let r' := slpMapSt f l r.1
    (r'.1, r.2 :: r'.2)

theorem slpMapSt_spec {α : Type} (f : ℕ → List SlpOp → List SlpOp × α) (l : List ℕ)
    (Q : ℕ → List SlpOp → α → Prop)
    (hmono : ∀ i s s' a, s <+: s' → Q i s a → Q i s' a) (s0 : List SlpOp)
    (hf : ∀ i ∈ l, ∀ s, s0 <+: s → s <+: (f i s).1 ∧ Q i (f i s).1 (f i s).2)
    (s : List SlpOp) (hs : s0 <+: s) :
    s <+: (slpMapSt f l s).1 ∧ (slpMapSt f l s).2.length = l.length ∧
      ∀ k (hk : k < l.length), ∃ a, (slpMapSt f l s).2[k]? = some a ∧
        Q l[k] (slpMapSt f l s).1 a := by
  induction l generalizing s with
  | nil => exact ⟨List.prefix_refl _, rfl, fun k hk => absurd hk (by simp)⟩
  | cons i l ih =>
    have hf' : ∀ j ∈ l, ∀ s, s0 <+: s → s <+: (f j s).1 ∧ Q j (f j s).1 (f j s).2 :=
      fun j hj => hf j (List.mem_cons_of_mem _ hj)
    obtain ⟨hp, hQ⟩ := hf i (List.mem_cons_self) s hs
    obtain ⟨ih1, ih2, ih3⟩ := ih hf' (f i s).1 (hs.trans hp)
    refine ⟨hp.trans ih1, by simp [slpMapSt, ih2], fun k hk => ?_⟩
    cases k with
    | zero =>
      exact ⟨(f i s).2, by simp [slpMapSt], hmono _ _ _ _ ih1 hQ⟩
    | succ k =>
      have hk' : k < l.length := by simpa using hk
      obtain ⟨a, ha, hQa⟩ := ih3 k hk'
      exact ⟨a, by simpa [slpMapSt] using ha, hQa⟩

/-- A computation on a program: new program and the slot of the result. -/
abbrev SlpComp : Type := List SlpOp → List SlpOp × Option ℕ

/-- The constant computation returning an existing slot. -/
def slpPure (x : Option ℕ) : SlpComp := fun s => (s, x)

/-- Sum of two computations. -/
def slpCAdd (c1 c2 : SlpComp) : SlpComp := fun s =>
  let r1 := c1 s
  let r2 := c2 r1.1
  slpAddO r2.1 r1.2 r2.2

/-- Product of two computations. -/
def slpCMul (c1 c2 : SlpComp) : SlpComp := fun s =>
  let r1 := c1 s
  let r2 := c2 r1.1
  slpMulO r2.1 r1.2 r2.2

/-- A constant times a computation. -/
def slpCScale (re im : ℚ) (deg : ℤ) (c : SlpComp) : SlpComp := fun s =>
  let r := c s
  slpScaleO r.1 re im deg r.2

/-- The computation `c` realizes `G` on `S` from every extension of the program `s0`. -/
def SlpEnt (n : ℕ) (S : Set ((Fin n → ℂ) × (Fin n → ℂ))) (s0 : List SlpOp) (c : SlpComp)
    (G : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop :=
  ∀ s, s0 <+: s → s <+: (c s).1 ∧ Realizes n S (c s).1 (c s).2 G

theorem SlpEnt.pure {S : Set Ph} {s0 : List SlpOp} {x : Option ℕ} {g : Ph → ℂ}
    (hx : Realizes n S s0 x g) : SlpEnt n S s0 (slpPure x) g :=
  fun _ hs => ⟨List.prefix_refl _, hx.mono hs⟩

theorem SlpEnt.congr {S : Set Ph} {s0 : List SlpOp} {c : SlpComp} {g h : Ph → ℂ}
    (hc : SlpEnt n S s0 c g) (hgh : Set.EqOn g h S) : SlpEnt n S s0 c h :=
  fun s hs => ⟨(hc s hs).1, (hc s hs).2.congr hgh⟩

theorem SlpEnt.add {S : Set Ph} {s0 : List SlpOp} {c1 c2 : SlpComp} {g h : Ph → ℂ}
    (h1 : SlpEnt n S s0 c1 g) (h2 : SlpEnt n S s0 c2 h) :
    SlpEnt n S s0 (slpCAdd c1 c2) (fun z => g z + h z) := by
  intro s hs
  obtain ⟨p1, r1⟩ := h1 s hs
  obtain ⟨p2, r2⟩ := h2 (c1 s).1 (hs.trans p1)
  obtain ⟨p3, r3⟩ := slpAddO_spec (r1.mono p2) r2
  exact ⟨(p1.trans p2).trans p3, r3⟩

theorem SlpEnt.mul {S : Set Ph} {s0 : List SlpOp} {c1 c2 : SlpComp} {g h : Ph → ℂ}
    (h1 : SlpEnt n S s0 c1 g) (h2 : SlpEnt n S s0 c2 h) :
    SlpEnt n S s0 (slpCMul c1 c2) (fun z => g z * h z) := by
  intro s hs
  obtain ⟨p1, r1⟩ := h1 s hs
  obtain ⟨p2, r2⟩ := h2 (c1 s).1 (hs.trans p1)
  obtain ⟨p3, r3⟩ := slpMulO_spec (r1.mono p2) r2
  exact ⟨(p1.trans p2).trans p3, r3⟩

theorem SlpEnt.scale {S : Set Ph} {s0 : List SlpOp} {c : SlpComp} {g : Ph → ℂ}
    (re im : ℚ) (deg : ℤ) (h1 : SlpEnt n S s0 c g) :
    SlpEnt n S s0 (slpCScale re im deg c) (fun z => slpConstVal re im deg * g z) := by
  intro s hs
  obtain ⟨p1, r1⟩ := h1 s hs
  obtain ⟨p2, r2⟩ := slpScaleO_spec re im deg r1
  exact ⟨p1.trans p2, r2⟩

/-- A table of `2n` slots, one per direction. -/
def slpTab1 (n : ℕ) (f : ℕ → SlpComp) (s : List SlpOp) : List SlpOp × List (Option ℕ) :=
  slpMapSt f (List.range (2 * n)) s

/-- A table of `2n × 2n` slots. -/
def slpTab2 (n : ℕ) (f : ℕ → ℕ → SlpComp) (s : List SlpOp) :
    List SlpOp × List (List (Option ℕ)) :=
  slpMapSt (fun i s => slpTab1 n (f i) s) (List.range (2 * n)) s

theorem slpTab1_spec {S : Set Ph} {s0 : List SlpOp} (f : ℕ → SlpComp)
    (G : ℕ → Ph → ℂ) (hf : ∀ i < 2 * n, SlpEnt n S s0 (f i) (G i))
    {s : List SlpOp} (hs : s0 <+: s) :
    s <+: (slpTab1 n f s).1 ∧
      ∀ i < 2 * n, Realizes n S (slpTab1 n f s).1 ((slpTab1 n f s).2.getD i none) (G i) := by
  obtain ⟨p, -, h⟩ := slpMapSt_spec f (List.range (2 * n))
    (fun i s' a => Realizes n S s' a (G i)) (fun i _ _ a hss h => h.mono hss) s0
    (fun i hi s' hs' => hf i (List.mem_range.1 hi) s' hs') s hs
  refine ⟨p, fun i hi => ?_⟩
  obtain ⟨a, ha, hQ⟩ := h i (by simpa using hi)
  simp only [List.getElem_range] at hQ
  simp only [slpTab1]
  rw [List.getD_eq_getElem?_getD, ha]
  exact hQ

theorem slpTab2_spec {S : Set Ph} {s0 : List SlpOp} (f : ℕ → ℕ → SlpComp)
    (G : ℕ → ℕ → Ph → ℂ) (hf : ∀ i < 2 * n, ∀ j < 2 * n, SlpEnt n S s0 (f i j) (G i j))
    {s : List SlpOp} (hs : s0 <+: s) :
    s <+: (slpTab2 n f s).1 ∧ ∀ i < 2 * n, ∀ j < 2 * n,
      Realizes n S (slpTab2 n f s).1
        (((slpTab2 n f s).2.getD i []).getD j none) (G i j) := by
  obtain ⟨p, -, h⟩ := slpMapSt_spec (fun i s => slpTab1 n (f i) s) (List.range (2 * n))
    (fun i s' row => ∀ j < 2 * n, Realizes n S s' (row.getD j none) (G i j))
    (fun i _ s' row hss h j hj => (h j hj).mono hss) s0
    (fun i hi s' hs' => slpTab1_spec (f i) (G i) (hf i (List.mem_range.1 hi)) hs') s hs
  refine ⟨p, fun i hi j hj => ?_⟩
  obtain ⟨a, ha, hQ⟩ := h i (by simpa using hi)
  simp only [List.getElem_range] at hQ
  have e : (slpTab2 n f s).2.getD i [] = a := by
    simp only [slpTab2]
    rw [List.getD_eq_getElem?_getD, ha]
    rfl
  rw [e]
  exact hQ j hj

end KAM.Certificate

end
