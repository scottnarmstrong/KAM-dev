/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.Roots

/-!
# Range-reduced certified complex exponential

`certCExpReduced z zRad s N` scales the input ball by `2 ^ (-s)`, requires the reduced ball to
pass `certCExpSmall`, evaluates `certCExp` of order `N` there and squares the result ball `s`
times. A successful call is sound with no size hypothesis on the input ball
(`certCExpReduced_sound`).
-/

@[expose] public section

namespace KAM.Certificate

open CertArith

/-- Square a ball `s` times (structural recursion on `s`). -/
def certBallSquareIter {α : Type} [CertArith α] (b : CertBall α) : ℕ → CertBall α
  | 0 => b
  | s + 1 => CertBall.times (certBallSquareIter b s) (certBallSquareIter b s)

theorem mem_certBallSquareIter {α : Type} [CertArith α] [LawfulCertArith α] {v : ℂ}
    {b : CertBall α} (hv : CertBall.Mem (Complex.exp v) b) (s : ℕ) :
    CertBall.Mem (Complex.exp (2 ^ s * v)) (certBallSquareIter b s) := by
  induction s with
  | zero => simpa [certBallSquareIter] using hv
  | succ s ih =>
    have e : Complex.exp (2 ^ (s + 1) * v) =
        Complex.exp (2 ^ s * v) * Complex.exp (2 ^ s * v) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [e]
    exact CertBall.mem_times ih ih

/-- Range-reduced certified complex exponential ball. Scales the input ball by `2^(-s)` (ball
product with `CertBall.ofRat (1 / 2 ^ s)`), returns `none` unless the reduced ball passes
`certCExpSmall`, evaluates `certCExp` of order `N` there, and squares the result ball `s` times
with `CertBall.times`. -/
def certCExpReduced {α : Type} [CertArith α] (z : CC α) (zRad : α) (s N : ℕ) :
    Option (CC α × α) :=
  let red := CertBall.times ⟨z, zRad⟩ (CertBall.ofRat (1 / 2 ^ s))
  if certCExpSmall red.c red.r then
    let e := certCExp red.c red.r N
    let out := certBallSquareIter ⟨e.1, e.2⟩ s
    some (out.c, out.r)
  else none

theorem certCExpReduced_sound {α : Type} [CertArith α] [LawfulCertArith α] {z : CC α}
    {zRad : α} {s N : ℕ} {out : CC α × α} (h : certCExpReduced z zRad s N = some out) {w : ℂ}
    (hw : ‖w - z.toC‖ ≤ val zRad) :
    ‖Complex.exp w - out.1.toC‖ ≤ val out.2 := by
  unfold certCExpReduced at h
  set red := CertBall.times ⟨z, zRad⟩ (CertBall.ofRat (α := α) (1 / 2 ^ s)) with hred
  by_cases hs : certCExpSmall red.c red.r = true
  · simp only [hs, ite_true] at h
    have hmem : CertBall.Mem (w * (((1 / 2 ^ s : ℚ)) : ℂ)) red :=
      CertBall.mem_times (b₁ := ⟨z, zRad⟩) hw (CertBall.mem_ofRat _)
    have hexp := certCExp_sound_of_small red.c red.r N (certCExpSmall_sound hs) hmem
    have hsq := mem_certBallSquareIter (b := ⟨(certCExp red.c red.r N).1,
      (certCExp red.c red.r N).2⟩) hexp s
    have e : (2 : ℂ) ^ s * (w * (((1 / 2 ^ s : ℚ)) : ℂ)) = w := by
      push_cast
      have : (2 : ℂ) ^ s ≠ 0 := pow_ne_zero _ two_ne_zero
      field_simp
    rw [e] at hsq
    cases h
    exact hsq
  · simp only [hs] at h
    cases h
