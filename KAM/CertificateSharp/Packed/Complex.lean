/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Norm

/-!
# Packed complex arrays and their Fourier meaning

A packed complex array `PC` is a pair of packed integers (real and imaginary slots). `PCRep L A x n F`
says that its slot data on the layout `L` are within `A` and that its Fourier sum is the function `F`.
The operations are exact and cost a constant number of big-integer operations each:

* `pcMul`: the complex product (four multiplications), on the window layout (`PCRep.mul`);
* `pcAdd`, `pcSumN`: sums on one layout (`PCRep.add`, `PCRep.sumN`);
* `pcUnitSub`: `c - x` with `c` placed at the slot of the zero key (`PCRep.unitSub`);
* `pcOfPoly`: the boundary from a landed backend polynomial, checked by `pcOfPolyOk`
  (`PCRep.ofPoly`: Fourier sum `2^P` times the polynomial);
* `pcNorm`: the packed weighted norm of both parts, a strip bound of the Fourier sum
  (`PCRep.norm_le`).
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate

/-- A packed complex array: the packings of the real and imaginary slot data. -/
structure PC where
  re : ℤ
  im : ℤ

/-- Packed complex product. -/
def pcMul (x y : PC) : PC := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩

/-- Packed complex sum. -/
def pcAdd (x y : PC) : PC := ⟨x.re + y.re, x.im + y.im⟩

/-- `Σ_{r<N} f r`. -/
def pcSumN (f : ℕ → PC) : ℕ → PC
  | 0 => ⟨0, 0⟩
  | N + 1 => pcAdd (pcSumN f N) (f N)

/-- `c - x`, the constant `c` placed at slot `p` (width `w`). -/
def pcUnitSub (w p : ℕ) (c : ℤ) (x : PC) : PC := ⟨c * 2 ^ (w * p) - x.re, -x.im⟩

/-- `x` packs complex slot data on `L`, every slot within `A`, with Fourier sum `F`. -/
def PCRep (L : PackLayout) (A : ℕ) (x : PC) (n : ℕ) (F : (Fin n → ℂ) → ℂ) : Prop :=
  ∃ dr di : List ℤ, SRep L A x.re dr ∧ SRep L A x.im di ∧
    ∀ θ, F θ = slotSum L n dr θ + Complex.I * slotSum L n di θ

/-- The load of a packed complex product. -/
def mulLoad (La Lb : PackLayout) (A B : ℕ) : ℕ := 2 * (min La.denseLen Lb.denseLen * A * B)

theorem SRep.mono {L : PackLayout} {A A' : ℕ} {Z : ℤ} {d : List ℤ} (h : SRep L A Z d)
    (hA : A ≤ A') : SRep L A' Z d :=
  ⟨h.len, h.pack, fun c hc => (h.bound c hc).trans (by exact_mod_cast hA), h.box⟩

theorem PCRep.mono {L : PackLayout} {A A' : ℕ} {x : PC} {n : ℕ} {F : (Fin n → ℂ) → ℂ}
    (h : PCRep L A x n F) (hA : A ≤ A') : PCRep L A' x n F := by
  obtain ⟨dr, di, hr, hi, hF⟩ := h
  exact ⟨dr, di, hr.mono hA, hi.mono hA, hF⟩

theorem PCRep.congr {L : PackLayout} {A : ℕ} {x : PC} {n : ℕ} {F G : (Fin n → ℂ) → ℂ}
    (h : PCRep L A x n F) (hFG : ∀ θ, F θ = G θ) : PCRep L A x n G := by
  obtain ⟨dr, di, hr, hi, hF⟩ := h
  exact ⟨dr, di, hr, hi, fun θ => (hFG θ).symm.trans (hF θ)⟩

/-- **Packed complex product** on the window layout. -/
theorem PCRep.mul {m : ℕ} {La Lb : PackLayout} (hc : PackLayout.compat m La Lb = true)
    (hwa : layoutWf La = true) (hwb : layoutWf Lb = true) {A B : ℕ} {x y : PC} {n : ℕ}
    {F G : (Fin n → ℂ) → ℂ} (hx : PCRep La A x n F) (hy : PCRep Lb B y n G) :
    PCRep (win La Lb) (mulLoad La Lb A B) (pcMul x y) n (fun θ => F θ * G θ) := by
  obtain ⟨dr, di, hr, hi, hF⟩ := hx
  obtain ⟨er, ei, hr', hi', hG⟩ := hy
  set C := min La.denseLen Lb.denseLen * A * B
  obtain ⟨m1, s1⟩ := SRep.mul hc hwa hwb hr hr' (C := C) le_rfl
  obtain ⟨m2, s2⟩ := SRep.mul hc hwa hwb hi hi' (C := C) le_rfl
  obtain ⟨m3, s3⟩ := SRep.mul hc hwa hwb hr hi' (C := C) le_rfl
  obtain ⟨m4, s4⟩ := SRep.mul hc hwa hwb hi hr' (C := C) le_rfl
  obtain ⟨n2, t2⟩ := m2.neg
  obtain ⟨re, sre⟩ := m1.add n2
  obtain ⟨im, sim⟩ := m3.add m4
  have hload : C + C = mulLoad La Lb A B := by unfold mulLoad; ring
  refine ⟨zadd (listConv dr er) ((listConv di ei).map Neg.neg),
    zadd (listConv dr ei) (listConv di er), ?_, ?_, fun θ => ?_⟩
  · rw [hload] at re
    simpa [pcMul, sub_eq_add_neg] using re
  · rw [hload] at im
    simpa [pcMul] using im
  · beta_reduce
    rw [sre, sim, t2, s1, s2, s3, s4, hF, hG]
    ring_nf
    rw [Complex.I_sq]
    ring

theorem PCRep.add {L : PackLayout} {A B : ℕ} {x y : PC} {n : ℕ} {F G : (Fin n → ℂ) → ℂ}
    (hx : PCRep L A x n F) (hy : PCRep L B y n G) :
    PCRep L (A + B) (pcAdd x y) n (fun θ => F θ + G θ) := by
  obtain ⟨dr, di, hr, hi, hF⟩ := hx
  obtain ⟨er, ei, hr', hi', hG⟩ := hy
  obtain ⟨re, sre⟩ := hr.add hr'
  obtain ⟨im, sim⟩ := hi.add hi'
  refine ⟨zadd dr er, zadd di ei, re, im, fun θ => ?_⟩
  beta_reduce
  rw [sre, sim, hF, hG]
  ring

theorem PCRep.zero (L : PackLayout) (n : ℕ) : PCRep L 0 ⟨0, 0⟩ n (fun _ => 0) :=
  ⟨zzero L, zzero L, srep_zero L, srep_zero L, fun θ => by simp [slotSum_zero]⟩

/-- **Packed sums** on one layout. -/
theorem PCRep.sumN {L : PackLayout} {A : ℕ → ℕ} {f : ℕ → PC} {n : ℕ}
    {F : ℕ → (Fin n → ℂ) → ℂ} :
    ∀ N : ℕ, (∀ r < N, PCRep L (A r) (f r) n (F r)) →
      PCRep L ((List.range N).map A).sum (pcSumN f N) n (fun θ => ∑ r ∈ Finset.range N, F r θ)
  | 0, _ => by simpa [pcSumN] using PCRep.zero L n
  | N + 1, h => by
    have ih := PCRep.sumN N fun r hr => h r (by omega)
    have := ih.add (h N (by omega))
    simp only [pcSumN, List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, Finset.sum_range_succ]
    exact this

/-- **`c - x`** with `c` at the slot of the zero key. -/
theorem PCRep.unitSub {L : PackLayout} (hw : layoutWf L = true) {n : ℕ} {p : ℕ}
    (hp : L.slot (List.replicate n 0) = some p) (c : ℤ) {A : ℕ} {x : PC}
    {F : (Fin n → ℂ) → ℂ} (hx : PCRep L A x n F) :
    PCRep L (c.natAbs + A) (pcUnitSub L.width p c x) n (fun θ => c - F θ) := by
  obtain ⟨dr, di, hr, hi, hF⟩ := hx
  obtain ⟨hkey, hbox⟩ := keyOf_slot hw hp
  obtain ⟨u1, su⟩ := srep_unit (PackLayout.slot_lt_denseLen hp) hbox c
  obtain ⟨nr, tr⟩ := hr.neg
  obtain ⟨ni, ti⟩ := hi.neg
  obtain ⟨re, sre⟩ := u1.add nr
  have hk0 : certKeyFun n (keyOf L p) = 0 := by
    rw [hkey]
    funext j
    simp [certKeyFun, List.getD_eq_getElem?_getD]
  refine ⟨zadd (zunit L p c) (dr.map Neg.neg), di.map Neg.neg,
    by simpa [pcUnitSub, sub_eq_add_neg] using re,
    by simpa [pcUnitSub] using ni.mono (Nat.le_add_left A c.natAbs), fun θ => ?_⟩
  beta_reduce
  rw [sre, su, tr, ti, hk0, character_zero, hF]
  ring

/-! ### The boundary and the norm -/

/-- The packed complex array of a backend polynomial at mantissa scale `P` (decoder `dec`). -/
def pcOfPoly {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (P : ℕ) (L : PackLayout)
    (p : CertPoly α) : PC :=
  let mt := (p.toMants dec P).getD ([], [])
  ⟨packOf L mt.1, packOf L mt.2⟩

/-- The boundary check of `pcOfPoly`: the mantissas decode and both parts pass `packRepOk`. -/
def pcOfPolyOk {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (P : ℕ) (L : PackLayout)
    (B : ℕ) (p : CertPoly α) : Bool :=
  match p.toMants dec P with
  | some mt => packRepOk L mt.1 B && packRepOk L mt.2 B
  | none => false

/-- **Boundary**: the packed array of a polynomial denotes `2^P` times it. -/
theorem PCRep.ofPoly {α : Type} [CertArith α] [LawfulCertArith α] {dec : ℕ → α → Option ℤ}
    {P : ℕ} {L : PackLayout} {B : ℕ} {p : CertPoly α} (hw : layoutWf L = true)
    (h : pcOfPolyOk dec P L B p = true) (n : ℕ) :
    PCRep L B (pcOfPoly dec P L p) n (fun θ => p.eval n θ * 2 ^ P) := by
  unfold pcOfPolyOk at h
  split at h
  · rename_i mt hmt
    simp only [Bool.and_eq_true] at h
    obtain ⟨d1, s1, e1⟩ := srep_of_packRepOk hw h.1
    obtain ⟨d2, s2, e2⟩ := srep_of_packRepOk hw h.2
    refine ⟨d1, d2, by simpa [pcOfPoly, hmt] using s1, by simpa [pcOfPoly, hmt] using s2,
      fun θ => ?_⟩
    beta_reduce
    rw [CertPoly.toMants_sound hmt θ, e1 n θ, e2 n θ]
    field_simp
  · exact absurd h (by simp)

/-- The packed weighted norm of both parts. -/
def pcNorm (W : CertWeight) (q l : ℕ) (L : PackLayout) (x : PC) : ℕ :=
  packNorm W q l L x.re + packNorm W q l L x.im

/-- **Strip bound** of a packed complex array. -/
theorem PCRep.norm_le {L : PackLayout} {A : ℕ} {x : PC} {n : ℕ} {F : (Fin n → ℂ) → ℂ}
    (hx : PCRep L A x n F) {W : CertWeight} {q l : ℕ} (hok : normOk W q l A L = true) {s N : ℕ}
    (hW : checkWeight W s N = true) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) :
    ‖F θ‖ ≤ (pcNorm W q l L x : ℝ) / 2 ^ (2 * q) := by
  obtain ⟨dr, di, hr, hi, hF⟩ := hx
  rw [hF, pcNorm, Nat.cast_add, add_div]
  refine (norm_add_le _ _).trans (add_le_add (slotSum_le_packNorm hr hok hW hθ) ?_)
  rw [norm_mul, Complex.norm_I, one_mul]
  exact slotSum_le_packNorm hi hok hW hθ

end KAM.CertificateSharp.Packed
