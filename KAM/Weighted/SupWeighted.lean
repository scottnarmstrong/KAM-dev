/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Coefficients
import Mathlib.Tactic.Positivity

/-!
# Sup versus weighted norm (`bpN:p4:sup-weighted`)

* (a) `sup_le_wbound`: `sup_{𝒟_{r,s}} |u| ≤ |u|_{r,s}`, from the Fourier representation
  (`coefficients_repr`) and `|χ_k| ≤ e^{2π s |k|₁}` on the strip.
* (b) `wbound_of_sup_bound`: `|u|_{r,s} ≤ coth(πσ)ⁿ M` if `|u| ≤ M` on `𝒟_{r,s+σ}`, fixed-`I` case
  `KAM.summableWeighted_torusCoeffW`.

`coth` is defined in `KAM.Weighted.Norm`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Weighted

-- The signatures keep the common instance block; not every lemma uses all of it.
set_option linter.unusedSectionVars false

variable {n m : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
  [IsScalarTower ℝ ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W]

/-- For `n = 0` the width plays no role: class and weighted bound at width `s` and at width `1`
coincide. -/
private theorem n_zero_width {D : Set (Fin m → ℂ)} {r s M : ℝ}
    {u : (Fin 0 → ℂ) × (Fin m → ℂ) → W} (hu : InClass D r s u) (hb : WBound D r s u M) :
    InClass D r 1 u ∧ WBound D r 1 u M := by
  have hDom : Dom 0 D r 1 = Dom 0 D r s := by
    ext z
    simp [Dom, KAM.complexStrip]
  have hw : ∀ k : Fin 0 → ℤ, modeWeight 1 k = modeWeight s k := fun k => by
    simp [modeWeight, KAM.Fourier.modeSize]
  refine ⟨⟨hDom ▸ hu.differentiableOn, fun j _ => j.elim0⟩, fun I hI => ?_⟩
  obtain ⟨h1, h2⟩ := hb I hI
  refine ⟨?_, ?_⟩
  · simpa only [WSummable, hw] using h1
  · simpa only [wsum, hw] using h2

private theorem sup_le_wbound_pos {D : Set (Fin m → ℂ)} {r s M : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → W} (hs : 0 < s) (hu : InClass D r s u)
    (hb : WBound D r s u M) : ∀ z ∈ Dom n D r s, ‖u z‖ ≤ M := by
  intro z hz
  obtain ⟨hrep, -⟩ := coefficients_repr hs hu hb
  obtain ⟨hsum, hle⟩ := hb z.2 hz.2
  refine ((hrep z hz).norm_le_of_bounded hsum.hasSum fun k => ?_).trans hle
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (KAM.norm_character_le k hz.1) (norm_nonneg _)

/-- (a) `sup_{𝒟_{r,s}} |u| ≤ |u|_{r,s}`. -/
theorem sup_le_wbound {D : Set (Fin m → ℂ)} {r s M : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hu : InClass D r s u) (hb : WBound D r s u M) : ∀ z ∈ Dom n D r s, ‖u z‖ ≤ M := by
  by_cases hs : 0 < s
  · exact sup_le_wbound_pos hs hu hb
  · -- `s ≤ 0`: the strip is empty unless `n = 0`
    intro z hz
    have hn : n = 0 := by
      by_contra hn
      obtain ⟨j⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
      have h1 := hz.1 j
      have h2 := abs_nonneg (z.1 j).im
      exact hs (by linarith)
    subst hn
    obtain ⟨hu1, hb1⟩ := n_zero_width hu hb
    exact sup_le_wbound_pos one_pos hu1 hb1 z ⟨fun j => j.elim0, hz.2⟩

/-- (b) `|u|_{r,s} ≤ coth(πσ)ⁿ M` if `|u| ≤ M` on `𝒟_{r,s+σ}`. -/
theorem wbound_of_sup_bound {D : Set (Fin m → ℂ)} {r s σ M : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → W} (hs : 0 < s) (hσ : 0 < σ) (hu : InClass D r (s + σ) u)
    (hM : ∀ z ∈ Dom n D r (s + σ), ‖u z‖ ≤ M) :
    WBound D r s u (coth (Real.pi * σ) ^ n * M) := by
  intro I hI
  have hmem : ∀ θ ∈ KAM.complexStrip n (s + σ), (θ, I) ∈ Dom n D r (s + σ) := fun θ hθ => ⟨hθ, hI⟩
  have hd : DifferentiableOn ℂ (fun θ : Fin n → ℂ => u (θ, I)) (KAM.complexStrip n (s + σ)) :=
    hu.differentiableOn.comp (differentiable_id.prodMk (differentiable_const I)).differentiableOn
      hmem
  obtain ⟨h1, h2⟩ := KAM.summableWeighted_torusCoeffW (ρ := s + σ) (δ := σ) hσ (by linarith) hd
    (fun i θ hθ => hu.periodic i (θ, I) (hmem θ hθ)) (fun θ hθ => hM _ (hmem θ hθ))
  have he : s + σ - σ = s := by ring
  rw [he] at h1 h2
  exact ⟨h1, h2⟩

end KAM.Weighted

end
