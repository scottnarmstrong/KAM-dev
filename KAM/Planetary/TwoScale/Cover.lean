/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Measure.McShane

/-!
# Two-scale KAM: the cover map

`bpP:p3:cover` with `stepP:p3:cv-ext`, `stepP:p3:cv-bij`, `stepP:p3:cv-loc`. A map `g` that is
`lam`-Lipschitz and `η`-bounded on a base set `X ⊆ ℝᴺ` (max norm) is McShane-extended to a
`lam`-Lipschitz map `G` on all of `ℝᴺ`; `x ↦ x + G x` is then a bi-Lipschitz bijection, whose
inverse is obtained from the contraction `x ↦ y - G x`. It moves points of `X` by at most
`η / (1 - lam)`. The cases `η = 0` and `X = ∅` need no separate treatment.
-/

@[expose] public section

open Set
open scoped NNReal

namespace KAM.Planetary

/-- No bound on g_e off X is needed. The inverse is an actual equivalence. -/
theorem cover {N : ℕ} {X : Set (Fin N → ℝ)} {g : (Fin N → ℝ) → (Fin N → ℝ)} {lam η : ℝ}
    (hlam : 0 ≤ lam ∧ lam < 1) (hη : 0 ≤ η)
    (hlip : ∀ x ∈ X, ∀ y ∈ X, ‖g x - g y‖ ≤ lam * ‖x - y‖)
    (hbound : ∀ x ∈ X, ‖g x‖ ≤ η) :
    ∃ F : (Fin N → ℝ) ≃ (Fin N → ℝ),
      (∀ x ∈ X, F x = x + g x) ∧
      (∀ x y, (1 - lam) * ‖x - y‖ ≤ ‖F x - F y‖ ∧ ‖F x - F y‖ ≤ (1 + lam) * ‖x - y‖) ∧
      ∀ y ∈ X, ‖F.symm y - y‖ ≤ η / (1 - lam) := by
  obtain ⟨hl0, hl1⟩ := hlam
  -- `cv-ext`: Lipschitz extension of `g` to the whole space
  obtain ⟨⟨G, hG, hGg⟩, -⟩ := KAM.mcshane (S := X) (φ := g) hl0
    (fun x hx y hy => by simpa [dist_eq_norm] using hlip x hx y hy)
  have hG' : ∀ x y, ‖G x - G y‖ ≤ lam * ‖x - y‖ := fun x y => by
    simpa [dist_eq_norm] using hG x y
  -- two-sided bound for `x ↦ x + G x`
  have hbi : ∀ x y, (1 - lam) * ‖x - y‖ ≤ ‖(x + G x) - (y + G y)‖ ∧
      ‖(x + G x) - (y + G y)‖ ≤ (1 + lam) * ‖x - y‖ := fun x y => by
    have e : (x + G x) - (y + G y) = (x - y) + (G x - G y) := by abel
    have h1 := hG' x y
    rw [e]
    constructor
    · have := norm_sub_norm_le (x - y) (-(G x - G y))
      rw [sub_neg_eq_add, norm_neg] at this
      nlinarith
    · have := norm_add_le (x - y) (G x - G y)
      linarith
  -- `cv-bij`: bijectivity via the contraction `x ↦ y - G x`
  have hinj : Function.Injective fun x => x + G x := fun x y h => by
    have := (hbi x y).1
    simp only at h
    rw [h, sub_self, norm_zero] at this
    have h2 : 0 < 1 - lam := by linarith
    have : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hsurj : Function.Surjective fun x => x + G x := fun y => by
    have hc : ContractingWith lam.toNNReal fun x => y - G x := by
      refine ⟨?_, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
      · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hl0]; simpa using hl1
      · rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hl0,
          show y - G a - (y - G b) = -(G a - G b) by abel, norm_neg]
        exact hG' a b
    obtain ⟨x, hx⟩ : ∃ x, x = y - G x :=
      ⟨_, (ContractingWith.fixedPoint_isFixedPt (f := fun x => y - G x) hc).symm⟩
    exact ⟨x, by
      calc x + G x = (y - G x) + G x := by rw [← hx]
        _ = y := by abel⟩
  let F : (Fin N → ℝ) ≃ (Fin N → ℝ) := Equiv.ofBijective _ ⟨hinj, hsurj⟩
  have hF : ∀ x, F x = x + G x := fun x => rfl
  refine ⟨F, fun x hx => by rw [hF, hGg x hx], fun x y => by simpa [hF] using hbi x y, ?_⟩
  -- `cv-loc`: displacement of the inverse on `X`
  intro y hy
  set x := F.symm y with hx
  have hxy : x + G x = y := by rw [← hF, hx, Equiv.apply_symm_apply]
  have hd : x - y = -G x := by rw [← hxy]; abel
  have h1 : ‖G x‖ ≤ lam * ‖x - y‖ + η := by
    have := norm_le_insert' (G x) (G y)
    have h3 := hG' x y
    have h4 : G y = g y := hGg y hy
    have h5 := hbound y hy
    rw [h4] at this h3
    linarith
  have h2 : ‖x - y‖ = ‖G x‖ := by rw [hd, norm_neg]
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end KAM.Planetary
