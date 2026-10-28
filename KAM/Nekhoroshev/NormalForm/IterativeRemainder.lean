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

/-- The generator `φ` is in `O(r,s)` with bound `Φ = qδ/(2πα)`, and `ξ`, `T_K f` are in the class
with bound `δ`; the homological equation in the form `{h ∘ snd, φ} = ξ - T_K f`. -/
theorem bracket_eq (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ Dom n D r s) :
    poissonBracket (fun w => h w.2) (homGen K Λ h f) z = homRes K Λ f z - truncate K f z := by
  obtain ⟨-, -, -, c4, -⟩ :=
    homological_direct H.hp H.hα H.hs H.hK H.h_holo H.divisor H.f_class H.f_bound
  have := c4 z hz
  rw [poissonBracket_antisymm]
  linear_combination (-1 : ℂ) * this

/-- `h ∘ snd` is in `O(r-ρ,s-σ)`. -/
theorem hClass (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    InClass D (r - ρ) (s - σ) (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2) :=
  ⟨H.h_holo.comp differentiable_snd.differentiableOn fun z hz =>
    polyNbhd_mono (by linarith [H.hρ]) hz.2, fun _ _ _ => rfl⟩

/-- The interpolated integrand `v_t = {h∘snd·(1-t) ... + f₀, φ}` of the Lie remainder. -/
def remIntegrand (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (t : ℝ) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  poissonBracket (fun w => ((1 - t : ℝ) : ℂ) * poissonBracket (fun w => h w.2) (homGen K Λ h f) w +
    (g w + truncate K f w)) (homGen K Λ h f)

/-- Class, bound and continuity data of the integrand (the three hypotheses of
`composition_integral`). -/
theorem integrand (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    (∀ t ∈ Icc (0 : ℝ) 1, InClass D (r - ρ) (s - σ) (remIntegrand K Λ h g f t) ∧
      WBound D (r - ρ) (s - σ) (remIntegrand K Λ h g f t)
        (2 / (Real.exp 1 * ρ * σ) * (starNorm r s ρ σ rj sj Mj + δ) *
          (conjExp p * δ / (2 * Real.pi * α)))) ∧
    ContinuousOn (fun q : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => remIntegrand K Λ h g f q.1 q.2)
      (Icc 0 1 ×ˢ Dom n D (r - ρ) (s - σ)) ∧
    ContinuousOn (fun q : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) =>
      fderiv ℂ (remIntegrand K Λ h g f q.1) q.2) (Icc 0 1 ×ˢ Dom n D (r - ρ) (s - σ)) := by
  obtain ⟨c1, c2, -, -, -, -, c7, c8, c9, -⟩ :=
    homological_direct H.hp H.hα H.hs H.hK H.h_holo H.divisor H.f_class H.f_bound
  have hρ := H.hρ
  have hσ := H.hσ
  have hΩ : IsOpen (Dom n D (r - ρ) (s - σ)) := isOpen_Dom D _ _
  have hΩr : IsOpen (Dom n D r s) := isOpen_Dom D _ _
  have hsub : Dom n D (r - ρ) (s - σ) ⊆ Dom n D r s := Dom_mono (by linarith) (by linarith)
  have hTc : InClass D r s (truncate K f) :=
    (projections H.hs H.f_class H.f_bound {k | KAM.Fourier.modeSize k ≤ K}).1
  obtain ⟨hgc, -⟩ := decomp_wbound H.decomp le_rfl le_rfl H.hs
  -- the three brackets
  have hAd : DifferentiableOn ℂ (poissonBracket g (homGen K Λ h f)) (Dom n D (r - ρ) (s - σ)) :=
    differentiableOn_poissonBracket hΩ (hgc.differentiableOn.mono hsub)
      (c1.differentiableOn.mono hsub)
  have hBd : DifferentiableOn ℂ (poissonBracket (homRes K Λ f) (homGen K Λ h f))
      (Dom n D (r - ρ) (s - σ)) :=
    differentiableOn_poissonBracket hΩ (c2.differentiableOn.mono hsub) (c1.differentiableOn.mono hsub)
  have hCd : DifferentiableOn ℂ (poissonBracket (truncate K f) (homGen K Λ h f))
      (Dom n D (r - ρ) (s - σ)) :=
    differentiableOn_poissonBracket hΩ (hTc.differentiableOn.mono hsub) (c1.differentiableOn.mono hsub)
  have hat : ∀ {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}, DifferentiableOn ℂ u (Dom n D r s) →
      ∀ z ∈ Dom n D r s, DifferentiableAt ℂ u z := fun hu z hz =>
    hu.differentiableAt (hΩr.mem_nhds hz)
  -- pointwise form of the integrand on `Ω`
  have eq1 : ∀ t : ℝ, ∀ z ∈ Dom n D (r - ρ) (s - σ), remIntegrand K Λ h g f t z =
      poissonBracket g (homGen K Λ h f) z +
        ((1 - t : ℝ) : ℂ) * poissonBracket (homRes K Λ f) (homGen K Λ h f) z +
        (t : ℂ) * poissonBracket (truncate K f) (homGen K Λ h f) z := fun t z hz => by
    have hz' := hsub hz
    have hG : EqOn (fun w => ((1 - t : ℝ) : ℂ) *
        poissonBracket (fun w => h w.2) (homGen K Λ h f) w + (g w + truncate K f w))
        (fun x => g x + ((1 - t : ℝ) : ℂ) * homRes K Λ f x + (t : ℂ) * truncate K f x)
        (Dom n D r s) := fun w hw => by
      beta_reduce
      rw [H.bracket_eq hw]
      push_cast
      ring
    unfold remIntegrand
    rw [poissonBracket_congr hΩr hG hz']
    exact poissonBracket_lin _ _ (hat hgc.differentiableOn z hz') (hat c2.differentiableOn z hz')
      (hat hTc.differentiableOn z hz')
  have eq2 : ∀ t : ℝ, ∀ z ∈ Dom n D (r - ρ) (s - σ), fderiv ℂ (remIntegrand K Λ h g f t) z =
      fderiv ℂ (poissonBracket g (homGen K Λ h f)) z +
        ((1 - t : ℝ) : ℂ) • fderiv ℂ (poissonBracket (homRes K Λ f) (homGen K Λ h f)) z +
        (t : ℂ) • fderiv ℂ (poissonBracket (truncate K f) (homGen K Λ h f)) z :=
    fun t z hz => by
    have hA := (hAd.differentiableAt (hΩ.mem_nhds hz))
    have hB := (hBd.differentiableAt (hΩ.mem_nhds hz))
    have hC := (hCd.differentiableAt (hΩ.mem_nhds hz))
    have h1 : HasFDerivAt (fun x => poissonBracket g (homGen K Λ h f) x +
        ((1 - t : ℝ) : ℂ) * poissonBracket (homRes K Λ f) (homGen K Λ h f) x +
        (t : ℂ) * poissonBracket (truncate K f) (homGen K Λ h f) x) _ z :=
      (hA.hasFDerivAt.add (hB.hasFDerivAt.const_mul _)).add (hC.hasFDerivAt.const_mul _)
    rw [← h1.fderiv]
    exact Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (hΩ.mem_nhds hz) fun w hw => eq1 t w hw)
  have hcont : ∀ {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}, DifferentiableOn ℂ u (Dom n D (r - ρ) (s - σ)) →
      ContinuousOn (fun z => fderiv ℂ u z) (Dom n D (r - ρ) (s - σ)) := fun hu =>
    ((KAM.contDiffOn_infty_of_differentiableOn hΩ hu).of_le
      (by exact_mod_cast le_top)).continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hsnd : ∀ {E : Type} [TopologicalSpace E] {u : (Fin n → ℂ) × (Fin n → ℂ) → E},
      ContinuousOn u (Dom n D (r - ρ) (s - σ)) →
      ContinuousOn (fun q : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => u q.2)
        (Icc 0 1 ×ˢ Dom n D (r - ρ) (s - σ)) := fun hu =>
    hu.comp continuousOn_snd fun q hq => hq.2
  have hc1 : Continuous fun q : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => ((1 - q.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)
  have hc2 : Continuous fun q : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => (q.1 : ℂ) :=
    Complex.continuous_ofReal.comp continuous_fst
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · -- class and bound through `bracket_g` with the extra term `f_t`
    have hξc := c2
    have hft : InClass D r s (fun x => ((1 - t : ℝ) : ℂ) * homRes K Λ f x + (t : ℂ) * truncate K f x) ∧
        WBound D r s (fun x => ((1 - t : ℝ) : ℂ) * homRes K Λ f x + (t : ℂ) * truncate K f x) δ := by
      have e1 : ‖((1 - t : ℝ) : ℂ)‖ = 1 - t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      have e2 : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      refine ⟨⟨(inClass_const_mul _ hξc).differentiableOn.add (inClass_const_mul _ hTc).differentiableOn,
        fun j z hz => by
          simp only [(inClass_const_mul ((1 - t : ℝ) : ℂ) hξc).periodic j z hz,
            (inClass_const_mul (t : ℂ) hTc).periodic j z hz]⟩, ?_⟩
      refine (wbound_add H.hs (inClass_const_mul _ hξc) (inClass_const_mul _ hTc)
        (wbound_const_mul _ c7) (wbound_const_mul _ c8)).mono le_rfl le_rfl ?_
      rw [e1, e2]
      linarith
    obtain ⟨b1, b2, -⟩ := bracket_g (isDecomp_snoc H.decomp hft.1 hft.2) c1 c9 hρ
      (by linarith [H.hρr]) hσ (by linarith [H.hσs])
    rw [starNorm_snoc rj sj Mj hρ hσ] at b2
    have hEq : EqOn (poissonBracket (fun z => g z + (((1 - t : ℝ) : ℂ) * homRes K Λ f z +
        (t : ℂ) * truncate K f z)) (homGen K Λ h f)) (remIntegrand K Λ h g f t)
        (Dom n D (r - ρ) (s - σ)) := fun z hz => by
      rw [eq1 t z hz]
      have hz' := hsub hz
      have := poissonBracket_lin (φ := homGen K Λ h f) ((1 - t : ℝ) : ℂ) (t : ℂ)
        (hat hgc.differentiableOn z hz') (hat c2.differentiableOn z hz')
        (hat hTc.differentiableOn z hz')
      rw [← this]
      simp only [add_assoc]
    exact ⟨inClass_congr hEq b1, wbound_congr (by linarith [H.hσs]) hEq b2⟩
  · refine ContinuousOn.congr (f := fun q : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) =>
      poissonBracket g (homGen K Λ h f) q.2 +
        ((1 - q.1 : ℝ) : ℂ) * poissonBracket (homRes K Λ f) (homGen K Λ h f) q.2 +
        (q.1 : ℂ) * poissonBracket (truncate K f) (homGen K Λ h f) q.2) ?_
      fun q hq => eq1 q.1 q.2 hq.2
    exact ((hsnd hAd.continuousOn).add (hc1.continuousOn.mul (hsnd hBd.continuousOn))).add
      (hc2.continuousOn.mul (hsnd hCd.continuousOn))
  · refine ContinuousOn.congr (f := fun q : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) =>
      fderiv ℂ (poissonBracket g (homGen K Λ h f)) q.2 +
        ((1 - q.1 : ℝ) : ℂ) • fderiv ℂ (poissonBracket (homRes K Λ f) (homGen K Λ h f)) q.2 +
        (q.1 : ℂ) • fderiv ℂ (poissonBracket (truncate K f) (homGen K Λ h f)) q.2) ?_
      fun q hq => eq2 q.1 q.2 hq.2
    exact ((hsnd (hcont hAd)).add (hc1.continuousOn.smul (hsnd (hcont hBd)))).add
      (hc2.continuousOn.smul (hsnd (hcont hCd)))

end IterHyp

end Iterative

end KAM.NormalForm

end
