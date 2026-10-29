/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.Fixed

/-!
# Mantissa checks

`mantCheck P a z` tests the claim `val a = z / 2^P` with the backend's own outward conversions and
equality test; it is law-free as a definition and sound for every lawful backend. `ofDyadic`
builds the exact backend value of `z / 2^P` or fails closed. For the fixed-point backend the
true mantissa always passes (`CertFixed.mantCheck_m`), so the packed route never falls back.
-/

@[expose] public section

namespace KAM.Certificate

open CertArith

/-- A mantissa claim `val a = z / 2^P`, tested with the backend's own outward conversions and
equality test. Law-free; its soundness needs only `LawfulCertArith` (`beq_sound`, `ofRatUp_ge`,
`ofRatDown_le`). -/
def mantCheck {α : Type} [CertArith α] (P : ℕ) (a : α) (z : ℤ) : Bool :=
  beq a (ofRatUp ((z : ℚ) / 2 ^ P)) && beq a (ofRatDown ((z : ℚ) / 2 ^ P))

theorem mantCheck_sound {α : Type} [CertArith α] [LawfulCertArith α] {P : ℕ} {a : α} {z : ℤ}
    (h : mantCheck P a z = true) : val a = (z : ℝ) / 2 ^ P := by
  simp only [mantCheck, Bool.and_eq_true] at h
  have h1 := LawfulCertArith.beq_sound _ _ h.1
  have h2 := LawfulCertArith.beq_sound _ _ h.2
  have hu := LawfulCertArith.ofRatUp_ge (α := α) ((z : ℚ) / 2 ^ P)
  have hd := LawfulCertArith.ofRatDown_le (α := α) ((z : ℚ) / 2 ^ P)
  have hq : (((z : ℚ) / 2 ^ P : ℚ) : ℝ) = (z : ℝ) / 2 ^ P := by push_cast; rfl
  rw [hq] at hu hd
  linarith

/-- The exact backend value `z / 2^P`, or `none` if the backend cannot represent it exactly
(checked by `mantCheck`; fail closed). -/
def ofDyadic {α : Type} [CertArith α] (P : ℕ) (z : ℤ) : Option α :=
  let a : α := ofRatDown ((z : ℚ) / 2 ^ P)
  if mantCheck P a z then some a else none

theorem ofDyadic_sound {α : Type} [CertArith α] [LawfulCertArith α] {P : ℕ} {z : ℤ} {a : α}
    (h : ofDyadic P z = some a) : val a = (z : ℝ) / 2 ^ P := by
  simp only [ofDyadic] at h
  by_cases hc : mantCheck P (ofRatDown ((z : ℚ) / 2 ^ P) : α) z = true
  · simp only [hc, ite_true, Option.some.injEq] at h
    subst h
    exact mantCheck_sound hc
  · simp [hc] at h

/-- The mantissa decoder the production certificate supplies (untrusted data: `mantCheck`
re-verifies each value). -/
def CertFixed.toMant (P : ℕ) : ℕ → CertFixed P → Option ℤ :=
  fun P' a => if P' = P then some a.m else none

/-- Completeness (not soundness): the landed fixed-point `ofRatUp`/`ofRatDown` are exact on the
grid `ℤ/2^P` and `beq` compares mantissas, so `mantCheck` accepts the true mantissa and the
packed route never falls back (part of SO-POLY-A, against the landed instance). -/
theorem CertFixed.mantCheck_m (P : ℕ) (a : CertFixed P) : mantCheck P a a.m = true := by
  set q : ℚ := (a.m : ℚ) / 2 ^ P with hq
  have hden : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have hkey : q.num * ulpDen P = a.m * q.den := by
    have h1 : (q.num : ℚ) / q.den = (a.m : ℚ) / 2 ^ P := by
      rw [hq]; exact Rat.num_div_den q
    have h2 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
    have h3 : ((2 : ℚ) ^ P) ≠ 0 := by positivity
    rw [div_eq_div_iff h2 h3] at h1
    have : ((q.num * ulpDen P : ℤ) : ℚ) = ((a.m * q.den : ℤ) : ℚ) := by
      simp only [ulpDen]; push_cast; linarith
    exact_mod_cast this
  have hup : (cdiv (q.num * ulpDen P) q.den) = a.m := by
    rw [hkey, cdiv, show -(a.m * (q.den : ℤ)) = (-a.m) * q.den by ring,
      Int.mul_ediv_cancel _ hden.ne']
    simp
  have hdn : (q.num * ulpDen P) / q.den = a.m := by
    rw [hkey]; exact Int.mul_ediv_cancel _ hden.ne'
  simp only [mantCheck, Bool.and_eq_true]
  constructor
  · show decide (a.m = (cdiv (q.num * ulpDen P) q.den)) = true
    rw [hup]; simp
  · show decide (a.m = (q.num * ulpDen P) / q.den) = true
    rw [hdn]; simp

end KAM.Certificate
