/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorStep.Drift

/-!
# Chains of normalization steps: data and complex-side analysis (track B, B2-MULTI)

A *chain* is a `List (OscStepK K)` (outermost generator first): the chart is `Ψ = Φ₁ ∘ ⋯ ∘ Φ_m`.
All data are `ℚ`-valued polynomials and radii. The predicates `OscStepOK`, `OscChainOK`,
`OscDomOK` are finite exact checks (`cartEqCheck`, `cartSupBound` majorants, rational/real
inequalities between data).

On the complex side: `oscChainTheta l` is the composition of the complex time-one flows of `l`,
`oscChainRem l Q` the sum of the pushed-forward Lie remainders, `oscChainDom l` an open domain on
which both are holomorphic, and `oscChainBound` the rational majorant of `‖oscChainRem‖` on the
Cauchy discs.
-/

@[expose] public noncomputable section

open Set KAM.Canonical

namespace KAM.EffectiveStability

open CartPoly

variable {n : ℕ} {K : Type} [CertCoeff K]

/-- One normalization step: generator `χ`, output polynomial `Q_k`, Lie order `L_k`, polydisc
radius `ρ_k`, gauge `δ_k`, small-field constant `ε_k` (finite data only). -/
structure OscStepK (K : Type) where
  gen : CartPolyK K
  out : CartPolyK K
  order : ℕ
  ρ : ℚ
  δ : ℚ
  ε : ℚ

/-- The `ℚ`-coefficient steps (the original name). -/
abbrev OscStep := OscStepK ℚ

/-- Total displacement budget `∑ ε_k δ_k` of a chain. -/
def oscTail : List (OscStepK K) → ℚ
  | [] => 0
  | s :: l => s.ε * s.δ + oscTail l

/-- The rational majorant `∑_k B_k / L_k!` of the remainders,
`B_k = cartSupBound (ad^{L_k} Q_{k-1})`. -/
def oscChainBound (n : ℕ) : List (OscStepK K) → CartPolyK K → ℚ
  | [], _ => 0
  | s :: l, Q => cartSupBound (cartAdPow s.gen s.order Q) (List.replicate n s.ρ)
      (List.replicate n s.ρ) / (s.order.factorial : ℚ) + oscChainBound n l s.out

/-- Per-step checks: positivity, small field majorants, polynomial typing. -/
structure OscStepOK (n : ℕ) (s : OscStepK K) : Prop where
  δ_pos : 0 < s.δ
  ε_nonneg : 0 ≤ s.ε
  ε_le : s.ε ≤ 1 / 2
  order_pos : 1 ≤ s.order
  fits_gen : CartFits n s.gen
  fits_out : CartFits n s.out
  bound_q : ∀ i : Fin n, cartSupBound (cartDq i s.gen) (List.replicate n s.ρ)
    (List.replicate n s.ρ) ≤ s.ε * s.δ
  bound_p : ∀ i : Fin n, cartSupBound (cartDp i s.gen) (List.replicate n s.ρ)
    (List.replicate n s.ρ) ≤ s.ε * s.δ

/-- The step identity `Q_k = ∑_{j<L} (j!)⁻¹ ad_χ^j Q_{k-1}`: either literally (`out` is the
unnormalized Lie sum) or by the exact normal-form check `cartEqCheck`. -/
def OscLieOK (gen Q out : CartPolyK K) (L : ℕ) : Prop :=
  out = cartLieSum gen Q L ∨ cartEqCheck (cartLieSum gen Q L) out = true

theorem OscLieOK.cartEval_lieSum_eq {gen Q out : CartPolyK K} {L : ℕ}
    (h : OscLieOK gen Q out L) {R : Type*} [CommRing R] [Algebra K R] {n : ℕ}
    (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartLieSum gen Q L) z = cartEval out z := by
  rcases h with rfl | h
  · rfl
  · exact cartEval_eq_of_eqCheck h z

/-- The exact identity checks of a chain started at the polynomial `Q`: step identities
`Q_k = ∑_{j<L_k} (j!)⁻¹ ad_{χ_k}^j Q_{k-1}` and the final `Q_m = Nact(I) + P`. -/
def OscChainOK (n : ℕ) (Nact P : CartPolyK K) : List (OscStepK K) → CartPolyK K → Prop
  | [], Q => cartEqCheck Q (cartAdd (cartActSubst Nact) P) = true
  | s :: l, Q => OscStepOK n s ∧ OscLieOK s.gen Q s.out s.order ∧
      OscChainOK n Nact P l s.out

/-- The real/complex radius budget of a chain: for every step, the real chart domain
(`r + (displacement of the inner steps) + δ_k < ρ_k`) and the Cauchy discs
(`r + δc + (inner displacement) + δ_k / 2 < ρ_k`). -/
def OscDomOK (n : ℕ) (r : Fin n → ℝ) (δc : ℝ) : List (OscStepK K) → Prop
  | [] => True
  | s :: l => (∀ i, r i + (oscTail l : ℝ) + (s.δ : ℝ) < (s.ρ : ℝ)) ∧
      (∀ i, r i + δc + (oscTail l : ℝ) + (s.δ : ℝ) / 2 < (s.ρ : ℝ)) ∧ OscDomOK n r δc l

section Semantic

variable [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ]
  [CertNormLe K ℂ]

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
/-- The complex time-one flow of the step generator on `cpolyOpen ρ`. -/
def oscStepFlow (s : OscStepK K) : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  flow (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval s.gen w))
    (cpolyOpen (s.ρ : ℝ)) 1

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
/-- The composite of the complex flows `X₁ ∘ ⋯ ∘ X_m` of a chain. -/
def oscChainTheta : List (OscStepK K) → (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)
  | [] => id
  | s :: l => oscStepFlow s ∘ oscChainTheta l

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
/-- The pushed-forward remainders `∑_k E_k ∘ (X_{k+1} ∘ ⋯ ∘ X_m)`, started at the polynomial `Q`. -/
def oscChainRem : List (OscStepK K) → CartPolyK K → (Fin n → ℂ) × (Fin n → ℂ) → ℂ
  | [], _ => fun _ => 0
  | s :: l, Q => fun z => stepRem s.gen Q (s.ρ : ℝ) s.order (oscChainTheta l z) +
      oscChainRem l s.out z

/-- Coordinates of a complex point lie within `r i + c`. -/
def OscBound (r : Fin n → ℝ) (c : ℝ) (z : (Fin n → ℂ) × (Fin n → ℂ)) : Prop :=
  ∀ i, ‖z.1 i‖ ≤ r i + c ∧ ‖z.2 i‖ ≤ r i + c

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
theorem oscStepFlow_apply (s : OscStepK K) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    oscStepFlow s z = flow (KAM.hamiltonianVectorFieldℂ
      (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval s.gen w)) (cpolyOpen (s.ρ : ℝ)) 1 z := rfl

theorem replicate_getD_oscRad (ρ : ℚ) (i : Fin n) :
    ((List.replicate n ρ).getD i 0 : ℚ) = ρ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [i.2]

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] in
/-- The coordinate bounds of a step give the small-field hypothesis. -/
theorem OscStepOK.smallField {s : OscStepK K} (hs : OscStepOK n s)
    (hδ : 0 < (s.δ : ℝ)) :
    SmallField (gaugeScalar (s.δ : ℝ) hδ) (cpolyOpen (s.ρ : ℝ))
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval s.gen w))
      (s.ε : ℝ) :=
  smallField_of_supBound hs.fits_gen hδ (List.replicate n s.ρ)
    (fun i => by rw [replicate_getD_oscRad]) (by exact_mod_cast hs.ε_nonneg)
    (by
      have h : ((s.ε : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.2 hs.ε_le
      simpa using h)
    (fun i => by exact_mod_cast hs.bound_q i) (fun i => by exact_mod_cast hs.bound_p i)

omit [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
theorem OscStepOK.delta_posℝ {s : OscStepK K} (hs : OscStepOK n s) : (0 : ℝ) < (s.δ : ℝ) := by
  exact_mod_cast hs.δ_pos

omit [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
theorem oscTail_nonneg_of {l : List (OscStepK K)} (h : ∀ s ∈ l, OscStepOK n s) :
    0 ≤ oscTail l := by
  induction l with
  | nil => simp [oscTail]
  | cons s l ih =>
    have hs := h s (by simp)
    have := ih (fun t ht => h t (by simp [ht]))
    simp only [oscTail]
    have := mul_nonneg hs.ε_nonneg hs.δ_pos.le
    positivity

end Semantic

end KAM.EffectiveStability
