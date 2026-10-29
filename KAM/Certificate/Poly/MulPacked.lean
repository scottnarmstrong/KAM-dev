/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.OverlapAdd
public import KAM.Certificate.Model.Basic

/-!
# Advice-checked complex products of backend polynomials

`CertPoly.toMants` reads the integer mantissas `(re, im)` of a backend polynomial at scale `P`
through an UNTRUSTED decoder, re-verifying every value by `mantCheck` (zero mantissas are dropped,
so an all-zero part is the empty list). `CertPoly.mulPacked` forms the four real products
(`re·re`, `im·im`, `re·im`, `im·re`) by `packedRealProduct`: an empty factor gives the exact zero
product with no advice and no kernel work (SO-ADVCOUNT lever 2: parity makes three of the four
real products of a lunar complex product identically zero); otherwise the factors are laid out
densely, checked by `checkPackedProduct`, and the result is the combined rounded target
(nonzero slots) plus a remainder bound `Σ_i b_i w^{|k_i|₁} / 2^{2P}` over every product slot
(`b_i = 2^scale` on the target box, `2^(outLog+1)` elsewhere). The coefficients are made exact in
the backend by `ofDyadic` (fail closed). `CertPoly.mulPacked_sound` encloses the EXACT product on
the strip.
-/

@[expose] public section

namespace KAM.Certificate

open KAM CertArith

/-! ### Mantissas -/

/-- The mantissa loop of `CertPoly.toMants`. -/
def certMantsAux {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (P : ℕ) :
    List (CertKey × CC α) → Option (List (CertKey × ℤ) × List (CertKey × ℤ))
  | [] => some ([], [])
  | t :: ts =>
    match dec P t.2.re, dec P t.2.im, certMantsAux dec P ts with
    | some zr, some zi, some m =>
      if mantCheck P t.2.re zr && mantCheck P t.2.im zi then
        some (if zr = 0 then m.1 else (t.1, zr) :: m.1, if zi = 0 then m.2 else (t.1, zi) :: m.2)
      else none
    | _, _, _ => none

/-- Integer mantissas `(re, im)` of a backend polynomial at scale `P`, read with the decoder
`dec` and each verified by `mantCheck` (`none` on any failure: fail closed). Zero mantissas are
dropped, so an all-zero part is the empty list. -/
def CertPoly.toMants {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (P : ℕ)
    (p : CertPoly α) : Option (List (CertKey × ℤ) × List (CertKey × ℤ)) :=
  certMantsAux dec P p.terms

theorem intEval_nil (n : ℕ) (θ : Fin n → ℂ) : intEval n [] θ = 0 := rfl

theorem intEval_cons (n : ℕ) (t : CertKey × ℤ) (ts : List (CertKey × ℤ)) (θ : Fin n → ℂ) :
    intEval n (t :: ts) θ = (t.2 : ℂ) * character (certKeyFun n t.1) θ + intEval n ts θ := by
  simp [intEval]

theorem intEval_append (n : ℕ) (ts us : List (CertKey × ℤ)) (θ : Fin n → ℂ) :
    intEval n (ts ++ us) θ = intEval n ts θ + intEval n us θ := by
  simp [intEval]

theorem intEval_map_neg (n : ℕ) (ts : List (CertKey × ℤ)) (θ : Fin n → ℂ) :
    intEval n (ts.map fun t => (t.1, -t.2)) θ = -intEval n ts θ := by
  induction ts with
  | nil => simp [intEval_nil]
  | cons t ts ih =>
    rw [List.map_cons, intEval_cons, intEval_cons, ih]
    push_cast
    ring

theorem certMantsAux_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {dec : ℕ → α → Option ℤ} {P : ℕ} (θ : Fin n → ℂ) : ∀ (ts : List (CertKey × CC α))
    {m : List (CertKey × ℤ) × List (CertKey × ℤ)}, certMantsAux dec P ts = some m →
    (ts.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum =
      (intEval n m.1 θ + Complex.I * intEval n m.2 θ) / 2 ^ P
  | [], m, h => by
    simp only [certMantsAux, Option.some.injEq] at h
    subst h
    simp [intEval_nil]
  | t :: ts, m, h => by
    simp only [certMantsAux] at h
    split at h
    · rename_i zr zi m' hr hi hm
      by_cases hc : (mantCheck P t.2.re zr && mantCheck P t.2.im zi) = true
      · simp only [hc, ite_true, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hc
        have er := mantCheck_sound hc.1
        have ei := mantCheck_sound hc.2
        have ih := certMantsAux_sound θ ts hm
        have hz : t.2.toC = ((zr : ℂ) + Complex.I * (zi : ℂ)) / 2 ^ P := by
          rw [CC.toC, Complex.mk_eq_add_mul_I, er, ei]
          push_cast
          ring
        rw [List.map_cons, List.sum_cons, ih, hz]
        have e1 : intEval n (if zr = 0 then m'.1 else (t.1, zr) :: m'.1) θ =
            (zr : ℂ) * character (certKeyFun n t.1) θ + intEval n m'.1 θ := by
          split_ifs with h0
          · simp [h0]
          · rw [intEval_cons]
        have e2 : intEval n (if zi = 0 then m'.2 else (t.1, zi) :: m'.2) θ =
            (zi : ℂ) * character (certKeyFun n t.1) θ + intEval n m'.2 θ := by
          split_ifs with h0
          · simp [h0]
          · rw [intEval_cons]
        simp only
        rw [e1, e2]
        ring
      · simp only [hc] at h
        simp at h
    · simp at h

theorem CertPoly.toMants_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {dec : ℕ → α → Option ℤ} {P : ℕ} {p : CertPoly α}
    {m : List (CertKey × ℤ) × List (CertKey × ℤ)} (h : p.toMants dec P = some m)
    (θ : Fin n → ℂ) :
    p.eval n θ = (intEval n m.1 θ + Complex.I * intEval n m.2 θ) / 2 ^ P :=
  certMantsAux_sound θ p.terms h

end KAM.Certificate
