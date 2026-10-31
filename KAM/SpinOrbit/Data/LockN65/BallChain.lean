/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.Ball

/-!
# Chaining the disc pass through literal checkpoints (LOCK-DATA)

The evaluated disc pass `ballsRev` is a left fold over the operations, so a pass over `ops₁ ++ ops₂`
is the pass over `ops₂` started from the state after `ops₁` (`ballsRev_append`). With literal
states at the cut points, each segment is its own kernel computation (`segOk`), decided as a
Boolean comparison (`ballsBeq`, sound by `eq_of_ballsBeq`); `balls_eq_of_segs` assembles a whole
pass `Slp.balls … = some bs` from a list of decided segments.

The disc pass of the `N = 65` lock (3158 operations at `slpBallPrec = 320` bits) is about 8 GB as one
kernel computation (SO-LOCK-COST §12); three segments keep each theorem well under that.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate

/-- Boolean equality of balls (no `DecidableEq (CC ℚ)` is landed). -/
def ballBeq (b b' : CC ℚ × ℚ) : Bool := b.1.re == b'.1.re && b.1.im == b'.1.im && b.2 == b'.2

/-- Boolean equality of lists of balls. -/
def ballsBeq : List (CC ℚ × ℚ) → List (CC ℚ × ℚ) → Bool
  | [], [] => true
  | b :: l, b' :: l' => ballBeq b b' && ballsBeq l l'
  | _, _ => false

theorem eq_of_ballBeq {b b' : CC ℚ × ℚ} (h : ballBeq b b' = true) : b = b' := by
  obtain ⟨⟨re, im⟩, r⟩ := b
  obtain ⟨⟨re', im'⟩, r'⟩ := b'
  simp only [ballBeq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  subst h1 h2 h3
  rfl

theorem eq_of_ballsBeq : ∀ {l l' : List (CC ℚ × ℚ)}, ballsBeq l l' = true → l = l'
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [ballsBeq, Bool.and_eq_true] at h
    rw [eq_of_ballBeq h.1, eq_of_ballsBeq h.2]
  | [], _ :: _, h => by simp [ballsBeq] at h
  | _ :: _, [], h => by simp [ballsBeq] at h

/-- The pass over `ops₁ ++ ops₂` continues from the state after `ops₁`. -/
theorem ballsRev_append (P n : ℕ) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ)
    (ops₁ ops₂ : List SlpOp) : ∀ (k : ℕ) (racc : List (CC ℚ × ℚ)),
    ballsRev P n WH centre radius taylorN k racc (ops₁ ++ ops₂) =
      (ballsRev P n WH centre radius taylorN k racc ops₁).bind
        (ballsRev P n WH centre radius taylorN (k + ops₁.length) · ops₂) := by
  induction ops₁ with
  | nil => intro k racc; simp [ballsRev]
  | cons op ops ih =>
    intro k racc
    simp only [List.cons_append, ballsRev, List.length_cons]
    split
    · rw [ih]; congr 2; funext r; congr 1; omega
    · rfl

/-- One segment of the pass: from the literal state `rin` after `k` slots, the operations `ops`
lead to the literal state `rout` (decided by `decide +kernel`). -/
def segOk (n : ℕ) (WH : CertWeight) (centre radius : List ℚ) (taylorN k : ℕ)
    (rin : List (CC ℚ × ℚ)) (ops : List SlpOp) (rout : List (CC ℚ × ℚ)) : Bool :=
  match ballsRev slpBallPrec n WH centre radius taylorN k rin ops with
  | some r => ballsBeq r rout
  | none => false

theorem ballsRev_of_segOk {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN k : ℕ}
    {rin rout : List (CC ℚ × ℚ)} {ops : List SlpOp}
    (h : segOk n WH centre radius taylorN k rin ops rout = true) :
    ballsRev slpBallPrec n WH centre radius taylorN k rin ops = some rout := by
  unfold segOk at h
  split at h
  · next r hr => rw [hr, eq_of_ballsBeq h]
  · exact absurd h Bool.false_ne_true

/-- Three decided segments give the whole pass (`rout` is the reversed final state). The offsets
`k₁`, `k₂` are literals, tied to the segment lengths by `hk₁`, `hk₂` (decided in the kernel, so the
elaborator never unfolds a long operation list). -/
theorem balls_eq_of_segs {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    {o₁ o₂ o₃ : List SlpOp} {r₁ r₂ r₃ : List (CC ℚ × ℚ)} {k₁ k₂ : ℕ}
    (hk₁ : o₁.length = k₁) (hk₂ : o₁.length + o₂.length = k₂)
    (h₁ : segOk n WH centre radius taylorN 0 [] o₁ r₁ = true)
    (h₂ : segOk n WH centre radius taylorN k₁ r₁ o₂ r₂ = true)
    (h₃ : segOk n WH centre radius taylorN k₂ r₂ o₃ r₃ = true) :
    Slp.balls n ⟨o₁ ++ o₂ ++ o₃⟩ WH centre radius taylorN = some r₃.reverse := by
  subst hk₁ hk₂
  simp only [Slp.balls, ballsAux, List.length_nil, List.reverse_nil]
  rw [ballsRev_append, ballsRev_append, ballsRev_of_segOk h₁, Option.bind_some,
    ballsRev_of_segOk (by simpa using h₂), Option.bind_some,
    ballsRev_of_segOk (by simpa [List.length_append] using h₃)]
  rfl

end KAM.SpinOrbit.Data.LockN65
