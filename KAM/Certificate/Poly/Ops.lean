/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.MulPacked

/-!
# Exact operations on finite Fourier data

Multiplication by a character `χ_m` (`CertPoly.shift`: keys shifted by `m`, coefficients
untouched) and the conjugate reflection `P*(θ) = conj (P (conj θ))` (`CertPoly.conjReflect`:
keys negated, coefficients conjugated). Both are exact; the shift is law-free, the reflection
needs the laws for the backend negation. This module also re-exports the advice-checked packed
products (`Poly/Packed`, `Poly/Layout`, `Poly/Advice`, `Poly/OverlapAdd`, `Poly/MulPacked`), so
the model layer imports `Poly/Ops` alone.
-/

@[expose] public section

namespace KAM.Certificate

open KAM CertArith

/-- Multiplication by the character `χ_m` (index shift; exact, law-free). -/
def CertPoly.shift {α : Type} [CertArith α] (m : CertKey) (P : CertPoly α) : CertPoly α :=
  ⟨P.terms.map fun t => (packAddZ m t.1, t.2)⟩

theorem certKeyFun_packAddZ (n : ℕ) (k l : CertKey) :
    certKeyFun n (packAddZ k l) = certKeyFun n k + certKeyFun n l := by
  funext i
  simp only [certKeyFun, packAddZ_getD, Pi.add_apply]

theorem CertPoly.eval_shift {α : Type} [CertArith α] (n : ℕ) (m : CertKey) (P : CertPoly α)
    (hm : m.length = n) (θ : Fin n → ℂ) :
    (P.shift m).eval n θ = character (certKeyFun n m) θ * P.eval n θ := by
  -- the length premise is part of the signed contract; the zero-extended key sum needs none
  subst hm
  simp only [CertPoly.eval, CertPoly.shift, List.map_map]
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply, certKeyFun_packAddZ, ← character_mul]
  ring

/-- `P ↦ P*(θ) := conj (P (conj θ))`: coefficients `c_k ↦ conj c_{-k}` (exact; uses `neg`). -/
def CertPoly.conjReflect {α : Type} [CertArith α] (P : CertPoly α) : CertPoly α :=
  ⟨P.terms.map fun t => (t.1.map Neg.neg, t.2.conj)⟩

theorem character_neg_eq_conj {n : ℕ} (k : Fin n → ℤ) (θ : Fin n → ℂ) :
    character (-k) θ = (starRingEnd ℂ) (character k fun i => (starRingEnd ℂ) (θ i)) := by
  simp only [character]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sum, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast,
    Complex.conj_conj, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

theorem CertPoly.eval_conjReflect {α : Type} [CertArith α] [LawfulCertArith α] (n : ℕ)
    (P : CertPoly α) (θ : Fin n → ℂ) :
    P.conjReflect.eval n θ = (starRingEnd ℂ) (P.eval n fun i => (starRingEnd ℂ) (θ i)) := by
  simp only [CertPoly.eval, CertPoly.conjReflect, List.map_map, map_list_sum]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply, CC.toC_conj, certKeyFun_map_neg, character_neg_eq_conj,
    map_mul]

end KAM.Certificate
