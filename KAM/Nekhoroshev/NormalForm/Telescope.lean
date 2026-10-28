/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.SymplecticForm

/-!
# Telescoping of a finite composition (`bpN:p6:telescope`)

`chain Φ m = Φ₀ ∘ Φ₁ ∘ ⋯ ∘ Φₘ`. On a decreasing family of sets `Uᵢ` with `Φᵢ : Uᵢ₊₁ → Uᵢ`, the
composition maps `Uₘ₊₁` into `U₀`, its displacement is bounded by the sum of the displacements
(for any seminorm), and, on open sets, holomorphy, preservation of `symplFormC` and injectivity
pass to the composition. Design `docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-4.
-/

@[expose] public noncomputable section

open Set

namespace KAM.NormalForm

open KAM.Canonical

variable {n : ℕ}

/-- `Ψₘ = Φ₀ ∘ Φ₁ ∘ ⋯ ∘ Φₘ`. -/
def chain {E : Type*} (Φ : ℕ → E → E) : ℕ → E → E
  | 0 => Φ 0
  | m + 1 => chain Φ m ∘ Φ (m + 1)

private lemma chain_mapsTo {U : ℕ → Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {Φ : ℕ → (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {m : ℕ}
    (hU : ∀ i ≤ m, U (i + 1) ⊆ U i) (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i)) :
    MapsTo (chain Φ m) (U (m + 1)) (U 0) := by
  induction m with
  | zero => exact hmap 0 le_rfl
  | succ m ih =>
    have h1 := ih (fun i hi => hU i (hi.trans (Nat.le_succ _)))
      (fun i hi => hmap i (hi.trans (Nat.le_succ _)))
    exact h1.comp (hmap (m + 1) le_rfl)

private lemma chain_disp {U : ℕ → Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {Φ : ℕ → (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {m : ℕ}
    (hU : ∀ i ≤ m, U (i + 1) ⊆ U i) (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (μ : Seminorm ℂ ((Fin n → ℂ) × (Fin n → ℂ))) (d : ℕ → ℝ)
    (hd : ∀ i ≤ m, ∀ z ∈ U (i + 1), μ (Φ i z - z) ≤ d i) :
    ∀ z ∈ U (m + 1), μ (chain Φ m z - z) ≤ ∑ i ∈ Finset.range (m + 1), d i := by
  induction m with
  | zero =>
    intro z hz
    simpa [chain] using hd 0 le_rfl z hz
  | succ m ih =>
    intro z hz
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hU i (hle i hi)) (fun i hi => hmap i (hle i hi))
      (fun i hi => hd i (hle i hi))
    have hz' : Φ (m + 1) z ∈ U (m + 1) := hmap (m + 1) le_rfl hz
    have h2 := h1 _ hz'
    have h3 := hd (m + 1) le_rfl z hz
    have hsplit : chain Φ (m + 1) z - z =
        (chain Φ m (Φ (m + 1) z) - Φ (m + 1) z) + (Φ (m + 1) z - z) := by
      simp [chain]
    rw [hsplit, Finset.sum_range_succ]
    calc μ _ ≤ μ (chain Φ m (Φ (m + 1) z) - Φ (m + 1) z) + μ (Φ (m + 1) z - z) :=
          map_add_le_add μ _ _
      _ ≤ _ := add_le_add h2 h3

private lemma chain_diff_sympl {U : ℕ → Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {Φ : ℕ → (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {m : ℕ}
    (hU : ∀ i ≤ m, U (i + 1) ⊆ U i) (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i))
    (hopen : ∀ i ≤ m, IsOpen (U (i + 1)))
    (hdiff : ∀ i ≤ m, DifferentiableOn ℂ (Φ i) (U (i + 1)))
    (hsympl : ∀ i ≤ m, ∀ z ∈ U (i + 1), ∀ v w,
      symplFormC (fderiv ℂ (Φ i) z v) (fderiv ℂ (Φ i) z w) = symplFormC v w) :
    DifferentiableOn ℂ (chain Φ m) (U (m + 1)) ∧
    ∀ z ∈ U (m + 1), ∀ v w,
      symplFormC (fderiv ℂ (chain Φ m) z v) (fderiv ℂ (chain Φ m) z w) = symplFormC v w := by
  induction m with
  | zero => exact ⟨hdiff 0 le_rfl, hsympl 0 le_rfl⟩
  | succ m ih =>
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    obtain ⟨ihd, ihs⟩ := ih (fun i hi => hU i (hle i hi)) (fun i hi => hmap i (hle i hi))
      (fun i hi => hopen i (hle i hi)) (fun i hi => hdiff i (hle i hi))
      (fun i hi => hsympl i (hle i hi))
    have hΦd := hdiff (m + 1) le_rfl
    have hΦm := hmap (m + 1) le_rfl
    have hopen' := hopen (m + 1) le_rfl
    refine ⟨ihd.comp hΦd hΦm, ?_⟩
    intro z hz v w
    have hz' : Φ (m + 1) z ∈ U (m + 1) := hΦm hz
    have hA : DifferentiableAt ℂ (Φ (m + 1)) z := hΦd.differentiableAt (hopen'.mem_nhds hz)
    have hB : DifferentiableAt ℂ (chain Φ m) (Φ (m + 1) z) :=
      ihd.differentiableAt ((hopen m (Nat.le_succ _)).mem_nhds hz')
    have hfd : fderiv ℂ (chain Φ (m + 1)) z =
        (fderiv ℂ (chain Φ m) (Φ (m + 1) z)).comp (fderiv ℂ (Φ (m + 1)) z) := by
      show fderiv ℂ (chain Φ m ∘ Φ (m + 1)) z = _
      exact fderiv_comp z hB hA
    rw [hfd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ihs _ hz', hsympl (m + 1) le_rfl z hz]

theorem telescope {U : ℕ → Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {Φ : ℕ → (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {m : ℕ}
    (hU : ∀ i ≤ m, U (i + 1) ⊆ U i) (hmap : ∀ i ≤ m, MapsTo (Φ i) (U (i + 1)) (U i)) :
    MapsTo (chain Φ m) (U (m + 1)) (U 0) ∧
    (∀ (μ : Seminorm ℂ ((Fin n → ℂ) × (Fin n → ℂ))) (d : ℕ → ℝ),
      (∀ i ≤ m, ∀ z ∈ U (i + 1), μ (Φ i z - z) ≤ d i) →
      ∀ z ∈ U (m + 1), μ (chain Φ m z - z) ≤ ∑ i ∈ Finset.range (m + 1), d i) ∧
    ((∀ i ≤ m, IsOpen (U (i + 1))) → (∀ i ≤ m, DifferentiableOn ℂ (Φ i) (U (i + 1))) →
      (∀ i ≤ m, ∀ z ∈ U (i + 1), ∀ v w,
        symplFormC (fderiv ℂ (Φ i) z v) (fderiv ℂ (Φ i) z w) = symplFormC v w) →
      DifferentiableOn ℂ (chain Φ m) (U (m + 1)) ∧
      ∀ z ∈ U (m + 1), ∀ v w,
        symplFormC (fderiv ℂ (chain Φ m) z v) (fderiv ℂ (chain Φ m) z w) = symplFormC v w) ∧
    ((∀ i ≤ m, InjOn (Φ i) (U (i + 1))) → InjOn (chain Φ m) (U (m + 1))) := by
  refine ⟨chain_mapsTo hU hmap, fun μ d hd => chain_disp hU hmap μ d hd,
    fun ho hd hs => chain_diff_sympl hU hmap ho hd hs, ?_⟩
  intro hinj
  induction m with
  | zero => exact hinj 0 le_rfl
  | succ m ih =>
    have hle : ∀ i ≤ m, i ≤ m + 1 := fun i hi => hi.trans (Nat.le_succ _)
    have h1 := ih (fun i hi => hU i (hle i hi)) (fun i hi => hmap i (hle i hi))
      (fun i hi => hinj i (hle i hi))
    exact h1.comp (hinj (m + 1) le_rfl) (hmap (m + 1) le_rfl)

end KAM.NormalForm
