/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.Homological
public import KAM.Canonical.CanonicalMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Iterative Lemma: the map (`bpN:p6:iterative` (a), (b))

The time-one map `iterMap` of the generating function `homGen`, the data `iterG`, `iterF`, `iterU`,
the direct-form hypotheses `IterHyp`, the items (a), (b) of `bpN:p6:iterative-direct` (restatements
of `canonical_map_a`..`e` for `CanonData` built from `homological_direct`) and
`iterHyp_of_source`. Design `docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-5.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

/-- The time-one map `Φ = X¹_φ` of the generating function, flow domain `𝒟_{r-ρ,s-σ}` (the
`omega` of both `CanonData D r s ρ σ _ φ` and `ComposeData D (r-ρ) (s-σ) r s ρ σ _ φ`). -/
def iterMap (D : Set (Fin n → ℂ)) (r s ρ σ K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  flow (KAM.hamiltonianVectorFieldℂ (homGen K Λ h f)) (Dom n D (r - ρ) (s - σ)) 1

/-- `g₊ = g + P_Λ T_K f`. -/
def iterG (K : ℝ) (Λ : Set (Fin n → ℤ)) (g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) :
    (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  fun z => g z + homRes K Λ f z

/-- `f₊ = H ∘ Φ - h - g₊` (so item (c)'s identity is definitional; its content is (d)). -/
def iterF (D : Set (Fin n → ℂ)) (r s ρ σ K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  fun z => (fun w => h w.2 + g w + f w) (iterMap D r s ρ σ K Λ h f z) - h z.2 - iterG K Λ g f z

/-- The source premises of the Iterative Lemma in direct-divisor form (`bpN:p6:iterative-direct`):
`s > 0`, `0 < ρ`, `2ρ < r`, `0 < σ`, `2σ < s`, `h` holomorphic on `V_r D`, `(N-dir)` with `α/q`,
`g` decomposed, `f ∈ O(r,s)`, `|f| ≤ δ ≤ ᾱρσ/(4q)`. -/
structure IterHyp (D : Set (Fin n → ℂ)) (r s ρ σ K α p δ : ℝ) (Λ : Set (Fin n → ℤ))
    (h : (Fin n → ℂ) → ℂ) (g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) {N : ℕ}
    (gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (rj sj Mj : Fin N → ℝ) : Prop where
  hp : 1 < p
  hα : 0 < α
  hK : 0 ≤ K
  hs : 0 < s
  hρ : 0 < ρ
  hρr : 2 * ρ < r
  hσ : 0 < σ
  hσs : 2 * σ < s
  h_holo : DifferentiableOn ℂ h (polyNbhd D r)
  divisor : DivisorBound (polyNbhd D r) K Λ h (α / conjExp p)
  decomp : IsDecomp D r s g gj rj sj Mj
  f_class : InClass D r s f
  f_bound : WBound D r s f δ
  δ_nonneg : 0 ≤ δ
  δ_small : δ ≤ 2 * Real.pi * α * ρ * σ / (4 * conjExp p)

/-- `u = qδ/(ᾱρσ)`. -/
def iterU (α p δ ρ σ : ℝ) : ℝ := conjExp p * δ / (2 * Real.pi * α * ρ * σ)

section Iterative

variable {D : Set (Fin n → ℂ)} {r s ρ σ K α p δ : ℝ} {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ}
  {g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ} {gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {rj sj Mj : Fin N → ℝ}

namespace IterHyp

/-- `conjExp p ≥ 1` for `p > 1`; in particular positive. -/
theorem conjExp_pos (hp : 1 < p) : 0 < conjExp p := by
  unfold conjExp
  exact div_pos (by linarith) (by linarith)

/-- `iterU ≤ 1/4`. -/
theorem iterU_le (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    iterU α p δ ρ σ ≤ 1 / 4 := by
  have hq := IterHyp.conjExp_pos H.hp
  have hpos : 0 < 2 * Real.pi * α * ρ * σ := by
    have := Real.pi_pos
    have := H.hα
    have := H.hρ
    have := H.hσ
    positivity
  unfold iterU
  rw [div_le_iff₀ hpos]
  have := H.δ_small
  rw [le_div_iff₀ (by linarith)] at this
  linarith

/-- The canonical-map data of the generating function `homGen`. -/
theorem canon (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    CanonData D r s ρ σ (conjExp p * δ / (2 * Real.pi * α)) (homGen K Λ h f) := by
  have hq := IterHyp.conjExp_pos H.hp
  have hπ := Real.pi_pos
  obtain ⟨c1, -, -, -, -, -, -, -, c9, -⟩ :=
    homological_direct H.hp H.hα H.hs H.hK H.h_holo H.divisor H.f_class H.f_bound
  refine ⟨H.hρ, by linarith [H.hρr], H.hσ, by linarith [H.hσs], c1, ?_, c9, ?_⟩
  · have := H.hα
    have := H.δ_nonneg
    positivity
  · have := H.iterU_le
    unfold iterU at this
    have e : conjExp p * δ / (2 * Real.pi * α) / (ρ * σ) =
        conjExp p * δ / (2 * Real.pi * α * ρ * σ) := by
      rw [div_div]; ring_nf
    rw [e]
    linarith

theorem phi_div (_H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    conjExp p * δ / (2 * Real.pi * α) / (ρ * σ) = iterU α p δ ρ σ := by
  unfold iterU
  rw [div_div]; ring_nf

end IterHyp

/-- `bpN:p6:iterative-direct` (a): holomorphic on `𝒟_{r-3ρ/2,s-3σ/2}` into `𝒟_{r-ρ,s-σ}`, canonical,
integer translations, injective on `𝒟_{r-2ρ,s-2σ}` with left inverse `X⁻¹_φ`. -/
theorem iterative_direct_a (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    DifferentiableOn ℂ (iterMap D r s ρ σ K Λ h f) (Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2)) ∧
    MapsTo (iterMap D r s ρ σ K Λ h f) (Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2))
      (Dom n D (r - ρ) (s - σ)) ∧
    (∀ z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2), ∀ v w,
      symplFormC (fderiv ℂ (iterMap D r s ρ σ K Λ h f) z v)
        (fderiv ℂ (iterMap D r s ρ σ K Λ h f) z w) = symplFormC v w) ∧
    (∀ k : Fin n → ℤ, ∀ z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2),
      iterMap D r s ρ σ K Λ h f (z.1 + (fun i => (k i : ℂ)), z.2) =
        iterMap D r s ρ σ K Λ h f z + ((fun i => (k i : ℂ)), 0)) ∧
    InjOn (iterMap D r s ρ σ K Λ h f) (Dom n D (r - 2 * ρ) (s - 2 * σ)) ∧
    ∀ z ∈ Dom n D (r - 2 * ρ) (s - 2 * σ),
      flow (KAM.hamiltonianVectorFieldℂ (homGen K Λ h f)) (Dom n D (r - ρ) (s - σ)) (-1)
        (iterMap D r s ρ σ K Λ h f z) = z := by
  have hd := H.canon
  refine ⟨(canonical_map_a hd).2.2.2.1 1 ⟨by norm_num, le_rfl⟩, fun z hz => ?_,
    canonical_map_d hd, (canonical_map_b hd).1, ?_, fun z hz => (canonical_map_e hd z hz).1⟩
  · exact ((canonical_map_a hd).2.2.2.2.1 z hz 1 ⟨by norm_num, le_rfl⟩).1
  · intro x hx y hy hxy
    have hx' := (canonical_map_e hd x hx).1
    have hy' := (canonical_map_e hd y hy).1
    have hxy' : flow (KAM.hamiltonianVectorFieldℂ (homGen K Λ h f)) hd.omega 1 x =
        flow (KAM.hamiltonianVectorFieldℂ (homGen K Λ h f)) hd.omega 1 y := hxy
    have := congrArg (flow (KAM.hamiltonianVectorFieldℂ (homGen K Λ h f)) hd.omega (-1)) hxy'
    rw [hx', hy'] at this
    exact this

/-- `bpN:p6:iterative-direct` (b): displacement. -/
theorem iterative_direct_b (H : IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj) :
    (∀ z ∈ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2),
      scaledNorm ρ σ (iterMap D r s ρ σ K Λ h f z - z) ≤ iterU α p δ ρ σ ∧
      ‖(iterMap D r s ρ σ K Λ h f z).1 - z.1‖ ≤ conjExp p * δ / (2 * Real.pi * α * ρ) ∧
      ‖(iterMap D r s ρ σ K Λ h f z).2 - z.2‖ ≤
        conjExp p * δ / (Real.exp 1 * (2 * Real.pi * α) * σ)) ∧
    ∀ z ∈ Dom n D (r - 2 * ρ) (s - 2 * σ), ∀ v,
      scaledNorm ρ σ (fderiv ℂ (iterMap D r s ρ σ K Λ h f) z v - v) ≤
        2 * iterU α p δ ρ σ * scaledNorm ρ σ v := by
  have hd := H.canon
  have hq := IterHyp.conjExp_pos H.hp
  have hπ := Real.pi_pos
  have hα := H.hα
  have hρ := H.hρ
  have hσ := H.hσ
  refine ⟨fun z hz => ?_, fun z hz v => ?_⟩
  · obtain ⟨-, -, -, -, h5, h6⟩ := canonical_map_a hd
    have h5' := (h5 z hz 1 ⟨by norm_num, le_rfl⟩).2
    rw [abs_one, one_mul, IterHyp.phi_div H] at h5'
    obtain ⟨b1, b2, -, -⟩ := h6 z hz
    refine ⟨h5', ?_, ?_⟩
    · refine b1.trans_eq ?_
      field_simp
    · refine b2.trans_eq ?_
      field_simp
  · have := canonical_map_c hd z hz 1 ⟨by norm_num, le_rfl⟩ v
    rwa [IterHyp.phi_div H] at this

end Iterative

/-- The source hypotheses `(N1)`, `(N2)`, `KLr ≤ α/p` give the direct-form premise (`divisor`):
this is how `bpN:p6:iterative` is obtained from `IterHyp`. -/
theorem iterHyp_of_source {D : Set (Fin n → ℂ)} {r s ρ σ K α L p δ : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {g f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {N : ℕ}
    {gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {rj sj Mj : Fin N → ℝ}
    (hp : 1 < p) (hα : 0 < α) (hK : 0 ≤ K) (hL : 0 ≤ L) (hs : 0 < s) (hρ : 0 < ρ) (hρr : 2 * ρ < r)
    (hσ : 0 < σ) (hσs : 2 * σ < s) (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hnr : IsNonresonant D K α Λ h) (hlip : FreqLipschitz D r L h) (hrad : K * L * r ≤ α / p)
    (hg : IsDecomp D r s g gj rj sj Mj) (hf : InClass D r s f) (hfb : WBound D r s f δ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 2 * Real.pi * α * ρ * σ / (4 * conjExp p)) :
    IterHyp D r s ρ σ K α p δ Λ h g f gj rj sj Mj :=
  ⟨hp, hα, hK, hs, hρ, hρr, hσ, hσs, hh, (divisor hp hα hK hL hnr hlip hrad).2, hg, hf, hfb, hδ0,
    hδ⟩

end KAM.NormalForm

end
