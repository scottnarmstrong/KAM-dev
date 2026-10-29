/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.Ops
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals

/-!
# Certified embeddings

`CertEmbedding α` is the embedding `K(θ) = (θ + (2π)^{dU_i} U_i(θ), (2π)^{dA_i} A_i(θ))` given by
real Fourier data `U_i`, `A_i` (SO design §2); a missing component denotes `0` (no backend default
value, finding F2). It is entire, primary and real on reals by construction, with law-free proofs
(`CertEmbedding.differentiable_eval`, `CertEmbedding.isPrimaryOnStrip`,
`CertEmbedding.isRealOnReals`). The angle displacement `θ ↦ (2π)^{dU_i} U_i(θ)` (`angleAt`) commutes
with complex conjugation (`CertEmbedding.angleAt_conj`), which the composition uses for the
reflected character witnesses.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

/-- The embedding `K(θ) = (θ + (2π)^{dU_i} U_i(θ), (2π)^{dA_i} A_i(θ))` from real Fourier data;
a missing component denotes `0` (no backend default value is used, finding F2). -/
structure CertEmbedding (α : Type) where
  angleDeg : List ℤ
  angle : List (CertRealPoly α)
  actionDeg : List ℤ
  action : List (CertRealPoly α)

def CertEmbedding.eval {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α)
    (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  (fun i => θ i + (2 * (Real.pi : ℂ)) ^ (K.angleDeg.getD i.val 0) *
      ((K.angle[i.val]?.map fun P => P.eval n θ).getD 0),
    fun i => (2 * (Real.pi : ℂ)) ^ (K.actionDeg.getD i.val 0) *
      ((K.action[i.val]?.map fun P => P.eval n θ).getD 0))

section Embedding

variable {α : Type} [CertArith α]

/-- The value `(2π)^d (P(θ) or 0)` of an optional real component. -/
def realComp (n : ℕ) (d : ℤ) (P : Option (CertRealPoly α)) (θ : Fin n → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ d * ((P.map fun P => P.eval n θ).getD 0)

/-- The angle displacement `(2π)^{dU_j} U_j(θ)` of coordinate `j` (`0` if `U_j` is missing). -/
def CertEmbedding.angleAt (n : ℕ) (K : CertEmbedding α) (j : ℕ) (θ : Fin n → ℂ) : ℂ :=
  realComp n (K.angleDeg.getD j 0) K.angle[j]? θ

/-- The action component `(2π)^{dA_j} A_j(θ)` (`0` if `A_j` is missing). -/
def CertEmbedding.actionAt (n : ℕ) (K : CertEmbedding α) (j : ℕ) (θ : Fin n → ℂ) : ℂ :=
  realComp n (K.actionDeg.getD j 0) K.action[j]? θ

theorem CertEmbedding.eval_fst (n : ℕ) (K : CertEmbedding α) (θ : Fin n → ℂ) (i : Fin n) :
    (K.eval n θ).1 i = θ i + K.angleAt n i.val θ := rfl

theorem CertEmbedding.eval_snd (n : ℕ) (K : CertEmbedding α) (θ : Fin n → ℂ) (i : Fin n) :
    (K.eval n θ).2 i = K.actionAt n i.val θ := rfl

theorem differentiable_realComp (n : ℕ) (d : ℤ) (P : Option (CertRealPoly α)) :
    Differentiable ℂ (realComp n d P) := by
  unfold realComp
  cases P with
  | none => simp
  | some P => simpa using (P.differentiable_eval n).const_mul _

theorem realComp_add_int (n : ℕ) (d : ℤ) (P : Option (CertRealPoly α)) (θ : Fin n → ℂ)
    (k : Fin n → ℤ) : realComp n d P (θ + fun i => (k i : ℂ)) = realComp n d P θ := by
  cases P <;> simp [realComp, CertRealPoly.eval_add_int]

theorem realComp_real (n : ℕ) (d : ℤ) (P : Option (CertRealPoly α)) (x : Fin n → ℝ) :
    (realComp n d P fun i => (x i : ℂ)).im = 0 := by
  have h2 : (2 * (Real.pi : ℂ)) ^ d = (((2 * Real.pi) ^ d : ℝ) : ℂ) := by push_cast; ring
  cases P with
  | none => simp [realComp]
  | some P =>
    simp only [realComp, Option.map_some, Option.getD_some, h2, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, P.eval_real n x, mul_zero]

end Embedding

theorem CertEmbedding.differentiable_eval {α : Type} [CertArith α] (n : ℕ)
    (K : CertEmbedding α) : Differentiable ℂ (K.eval n) := by
  refine Differentiable.prodMk (differentiable_pi.mpr fun i => ?_)
    (differentiable_pi.mpr fun i => ?_)
  · exact (differentiable_apply i).add (differentiable_realComp n _ _)
  · exact differentiable_realComp n _ _

theorem CertEmbedding.isPrimaryOnStrip {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α)
    (ρ : ℝ) : IsPrimaryOnStrip (K.eval n) ρ := by
  intro θ _ k
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change (θ + fun i => (k i : ℂ)) i + realComp n _ _ (θ + fun i => (k i : ℂ)) =
      (θ i + realComp n _ _ θ) + (k i : ℂ)
    rw [realComp_add_int, Pi.add_apply]
    ring
  · change realComp n _ _ (θ + fun i => (k i : ℂ)) = realComp n _ _ θ + 0
    rw [realComp_add_int, add_zero]

/-- Law-free (finding F2): `CertRealPoly.eval_real` and the `0` default. -/
theorem CertEmbedding.isRealOnReals {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) :
    IsRealOnReals (K.eval n) := by
  intro θ
  refine ⟨(fun i => ((K.eval n fun i => (θ i : ℂ)).1 i).re,
    fun i => ((K.eval n fun i => (θ i : ℂ)).2 i).re), ?_⟩
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have h : ((K.eval n fun i => (θ i : ℂ)).1 i).im = 0 := by
      change (((θ i : ℂ) + realComp n _ _ fun i => (θ i : ℂ))).im = 0
      rw [Complex.add_im, Complex.ofReal_im, realComp_real, add_zero]
    exact Complex.ext (by simp) (by simp [h])
  · have h : ((K.eval n fun i => (θ i : ℂ)).2 i).im = 0 := realComp_real n _ _ θ
    exact Complex.ext (by simp) (by simp [h])

/-! ### Conjugation -/

section Conj

variable {α : Type} [CertArith α]

theorem character_conj {n : ℕ} (k : Fin n → ℤ) (θ : Fin n → ℂ) :
    character k (fun i => (starRingEnd ℂ) (θ i)) = (starRingEnd ℂ) (character (-k) θ) := by
  have := character_neg_eq_conj (-k) (fun i => (starRingEnd ℂ) (θ i))
  simp only [neg_neg, Complex.conj_conj] at this
  rw [this]

/-- Real data commutes with conjugation (law-free). -/
theorem CertRealPoly.eval_conj (n : ℕ) (P : CertRealPoly α) (θ : Fin n → ℂ) :
    P.eval n (fun i => (starRingEnd ℂ) (θ i)) = (starRingEnd ℂ) (P.eval n θ) := by
  unfold CertRealPoly.eval
  rw [map_add, Complex.conj_ofReal, map_list_sum, List.map_map]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply, character_conj, neg_neg, map_add, map_mul, Complex.conj_conj]
  ring

theorem realComp_conj (n : ℕ) (d : ℤ) (P : Option (CertRealPoly α)) (θ : Fin n → ℂ) :
    realComp n d P (fun i => (starRingEnd ℂ) (θ i)) = (starRingEnd ℂ) (realComp n d P θ) := by
  have h2 : (2 * (Real.pi : ℂ)) ^ d = (((2 * Real.pi) ^ d : ℝ) : ℂ) := by push_cast; ring
  cases P with
  | none => simp [realComp]
  | some P =>
    simp only [realComp, Option.map_some, Option.getD_some, h2, map_mul, Complex.conj_ofReal,
      CertRealPoly.eval_conj]

theorem CertEmbedding.angleAt_conj (n : ℕ) (K : CertEmbedding α) (j : ℕ) (θ : Fin n → ℂ) :
    K.angleAt n j (fun i => (starRingEnd ℂ) (θ i)) = (starRingEnd ℂ) (K.angleAt n j θ) :=
  realComp_conj n _ _ θ

theorem differentiable_angleAt (n : ℕ) (K : CertEmbedding α) (j : ℕ) :
    Differentiable ℂ (K.angleAt n j) :=
  differentiable_realComp n _ _

end Conj

end KAM.Certificate
