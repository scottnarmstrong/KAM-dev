/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.IterativeMap
public import KAM.Nekhoroshev.NormalForm.BracketDecomp
public import KAM.Canonical.CompositionIntegral
public import KAM.Canonical.Transform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Iterative Lemma: the remainder (`bpN:p6:iterative` (c), (d))

`H ∘ Φ = h + g₊ + f₊` (definitional for `iterF`), `ξ = P_Λ T_K f ∈ O(r,s)` of norm `≤ δ`,
`f₊ ∈ O(r-2ρ,s-2σ)` and the estimate of `f₊`. The proof splits `H ∘ Φ` with `transform`
(`h ↦ h ∘ snd`, `f₀ = g + T_K f`), the integrand `{g + (1-t)ξ + t T_K f, φ}` is bounded by
`bracket_g` with the extra decomposition term, and `(f - T_K f) ∘ Φ` by `truncation_tail` and
`composition_series`. Design `docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-6.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

/-! ### Decompositions and linear combinations -/

private theorem inClass_mono' {D : Set (Fin n → ℂ)} {r₀ s₀ r s : ℝ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r₀ s₀ u) (hr : r ≤ r₀) (hs : s ≤ s₀) :
    InClass D r s u :=
  ⟨hu.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hu.periodic j z (Dom_mono hr hs hz)⟩

private theorem wbound_zero {D : Set (Fin n → ℂ)} {r s : ℝ} :
    WBound D r s (fun _ : (Fin n → ℂ) × (Fin n → ℂ) => (0 : ℂ)) 0 := by
  intro I _
  have h0 : ∀ k : Fin n → ℤ, coeff (fun _ : (Fin n → ℂ) × (Fin n → ℂ) => (0 : ℂ)) I k = 0 :=
    fun k => by simp [coeff, KAM.torusCoeffW, KAM.torusAverage]
  simp [WSummable, wsum, h0]

/-- A decomposed `g` is in the class and has a finite weighted norm at smaller widths. -/
private theorem decomp_wbound {D : Set (Fin n → ℂ)} {r s r₀ s₀ : ℝ}
    {g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ} {gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {rj sj Mj : Fin N → ℝ} (hg : IsDecomp D r s g gj rj sj Mj) (hr : r₀ ≤ r) (hs : s₀ ≤ s)
    (hs₀ : 0 < s₀) :
    InClass D r₀ s₀ g ∧ WBound D r₀ s₀ g (∑ j, Mj j) := by
  have hcl : ∀ j, InClass D r₀ s₀ (gj j) := fun j =>
    inClass_mono' (hg.inClass j) (hr.trans (hg.r_le j)) (hs.trans (hg.s_le j))
  have hb : ∀ j, WBound D r₀ s₀ (gj j) (Mj j) := fun j =>
    (hg.bound j).mono (hr.trans (hg.r_le j)) (hs.trans (hg.s_le j)) le_rfl
  have key : ∀ S : Finset (Fin N), InClass D r₀ s₀ (fun z => ∑ j ∈ S, gj j z) ∧
      WBound D r₀ s₀ (fun z => ∑ j ∈ S, gj j z) (∑ j ∈ S, Mj j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨⟨differentiableOn_const 0, fun _ _ _ => rfl⟩, by simpa using wbound_zero⟩
    | insert a S ha ih =>
      have e : (fun z => ∑ j ∈ insert a S, gj j z) = fun z => gj a z + ∑ j ∈ S, gj j z := by
        funext z; rw [Finset.sum_insert ha]
      rw [e, Finset.sum_insert ha]
      exact ⟨⟨(hcl a).differentiableOn.add ih.1.differentiableOn, fun j z hz => by
        simp only [(hcl a).periodic j z hz, ih.1.periodic j z hz]⟩,
        wbound_add hs₀ (hcl a) ih.1 (hb a) ih.2⟩
  have := key Finset.univ
  rw [hg.eq_sum]
  exact this

/-- Linearity of `{·, φ}` on a combination of three differentiable functions. -/
private theorem poissonBracket_lin {u v w φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (a b : ℂ) (hu : DifferentiableAt ℂ u z)
    (hv : DifferentiableAt ℂ v z) (hw : DifferentiableAt ℂ w z) :
    poissonBracket (fun x => u x + a * v x + b * w x) φ z =
      poissonBracket u φ z + a * poissonBracket v φ z + b * poissonBracket w φ z := by
  have hd : fderiv ℂ (fun x => u x + a * v x + b * w x) z =
      fderiv ℂ u z + a • fderiv ℂ v z + b • fderiv ℂ w z := by
    have h1 : HasFDerivAt (fun x => u x + a * v x + b * w x)
        (fderiv ℂ u z + a • fderiv ℂ v z + b • fderiv ℂ w z) z :=
      (hu.hasFDerivAt.add (hv.hasFDerivAt.const_mul a)).add (hw.hasFDerivAt.const_mul b)
    exact h1.fderiv
  unfold poissonBracket
  rw [hd]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The bracket of a class function with `φ` is determined by values on an open set. -/
private theorem poissonBracket_congr {u u' φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U) (h : EqOn u u' U)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ U) : poissonBracket u φ z = poissonBracket u' φ z := by
  have : fderiv ℂ u z = fderiv ℂ u' z :=
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h)
  simp only [poissonBracket, this]

/-- The extra decomposition term: `g` with one more piece of width `(r,s)` and bound `δ`. -/
private theorem isDecomp_snoc {D : Set (Fin n → ℂ)} {r s δ : ℝ}
    {g f₁ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ} {gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {rj sj Mj : Fin N → ℝ} (hg : IsDecomp D r s g gj rj sj Mj) (hf : InClass D r s f₁)
    (hb : WBound D r s f₁ δ) :
    IsDecomp D r s (fun z => g z + f₁ z) (Fin.cons f₁ gj : Fin (N + 1) → _)
      (Fin.cons r rj : Fin (N + 1) → ℝ) (Fin.cons s sj : Fin (N + 1) → ℝ)
      (Fin.cons δ Mj : Fin (N + 1) → ℝ) where
  eq_sum := by
    funext z
    rw [Fin.sum_univ_succ, hg.eq_sum]
    simp [add_comm]
  r_le := fun j => Fin.cases le_rfl (fun j => by simpa using hg.r_le j) j
  s_le := fun j => Fin.cases le_rfl (fun j => by simpa using hg.s_le j) j
  inClass := fun j => Fin.cases (by simpa using hf) (fun j => by simpa using hg.inClass j) j
  bound := fun j => Fin.cases (by simpa using hb) (fun j => by simpa using hg.bound j) j

private theorem starNorm_snoc {r s ρ σ δ : ℝ} {N : ℕ} (rj sj Mj : Fin N → ℝ) (hρ : 0 < ρ)
    (hσ : 0 < σ) :
    starNorm r s ρ σ (Fin.cons r rj : Fin (N + 1) → ℝ) (Fin.cons s sj : Fin (N + 1) → ℝ)
      (Fin.cons δ Mj : Fin (N + 1) → ℝ) = starNorm r s ρ σ rj sj Mj + δ := by
  unfold starNorm
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, sub_self, zero_add]
  rw [div_self hρ.ne', div_self hσ.ne']
  ring


section Iterative

variable {D : Set (Fin n → ℂ)} {r s ρ σ K α p δ : ℝ} {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ}
  {g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ} {gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {rj sj Mj : Fin N → ℝ}

namespace IterHyp

/-- The compose data of `φ = homGen` with widths `(r-ρ, s-σ)` inside `(r, s)`. -/
theorem compose (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    ComposeData D (r - ρ) (s - σ) r s ρ σ (conjExp p * δ / (2 * Real.pi * α))
      (homGen K Λ h f) := by
  obtain ⟨c1, -, -, -, -, -, -, -, c9, -⟩ :=
    homological_direct H.hp H.hα H.hs H.hK H.h_holo H.divisor H.f_class H.f_bound
  have hq := IterHyp.conjExp_pos H.hp
  have hπ := Real.pi_pos
  have hα := H.hα
  have hδ := H.δ_nonneg
  refine ⟨H.hρ, by linarith [H.hρr], le_rfl, H.hσ, by linarith [H.hσs], le_rfl, c1, ?_, c9, ?_⟩
  · positivity
  · rw [mul_div_assoc, IterHyp.phi_div H]
    linarith [H.iterU_le]

/-- `iterMap` is the flow of `ComposeData.omega`. -/
theorem iterMap_eq (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) (z) :
    iterMap D r s ρ σ K Λ h f z =
      flow (KAM.hamiltonianVectorFieldℂ (homGen K Λ h f)) H.compose.omega 1 z := rfl

end IterHyp

end Iterative

end KAM.NormalForm

end
