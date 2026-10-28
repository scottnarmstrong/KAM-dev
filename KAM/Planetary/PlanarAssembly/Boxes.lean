/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Planetary.PlanarAssembly.Geometry
public import KAM.Frozen.Planetary.Defs.FastFrequency
public import KAM.Frozen.Planetary.Defs.HasFastDiffeomorphism
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm

/-!
# Planar assembly: boxes, the Kepler frequency and radius arithmetic (Part 12)

Blueprint P, Part 12 (`bpP:p12:collar`, `bpP:p12:fast-diffeo`, `bpP:p12:f-mono`, the elementary
radius and threshold choices of `bpP:p12:data`, and the supplementary
`bpP:p7:product-chart` (b) completion):

* `collar`: the `t`-collar of the frontier of an open box in the plane has volume at most
  `4 t (L₀ + L₁)`, the exact difference of two box volumes;
* `product_chart`: analyticity of the action Hamiltonian `kepler_h` on positive actions, its
  gradient, frequency and diagonal Hessian, and the decoupling identity with `hProd`;
* `fast_diffeo`: the frozen `HasFastDiffeomorphism` for `kepler_h` on a positive open box, with
  the explicit inverse `(κ² mᵢ³ / vᵢ)^(1/3)`;
* `radius_choices`, `birkhoff_mono_radius`: the explicit radius and threshold arithmetic and the
  restriction of the frozen secular Birkhoff expansion to a smaller disc.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function
open scoped BigOperators

namespace KAM.Planetary
open KAM KAM.Kepler

namespace PlanarAssembly

/-! ### Radius arithmetic -/

/-- Elementary output of the P-G radius/threshold choices, not a P-G premise. -/
def secular_radius (rG δ : ℝ) : ℝ := min rG (√(δ / 2)) / 2

def coupling_threshold (r c : ℝ) : ℝ := min 1 (r ^ 6 / (log (1 / r)) ^ c)

theorem radius_choices (rG δ c : ℝ) (hrG : 0 < rG) (hrG1 : rG < 1)
    (hδ : 0 < δ) (hc : 0 < c) :
    let r := secular_radius rG δ
    0 < r ∧ r < rG ∧ r < 1 ∧ 2 * r ^ 2 ≤ δ / 2 ∧
    0 < coupling_threshold r c ∧ coupling_threshold r c ≤ 1 ∧
    ∀ μ, 0 < μ → μ < coupling_threshold r c → μ < r ^ 6 / (log (1 / r)) ^ c := by
  intro r
  have _ := hc
  have hsq : 0 < √(δ / 2) := Real.sqrt_pos.mpr (by positivity)
  have hmin : 0 < min rG (√(δ / 2)) := lt_min hrG hsq
  have hr : 0 < r := by unfold r secular_radius; positivity
  have hr1 : r < rG := by
    have : r ≤ rG / 2 := by
      unfold r secular_radius
      linarith [min_le_left rG (√(δ / 2))]
    linarith
  have hrs : r ≤ √(δ / 2) / 2 := by
    unfold r secular_radius
    linarith [min_le_right rG (√(δ / 2))]
  have hr2 : r < 1 := hr1.trans hrG1
  have hlog : 0 < log (1 / r) := by
    apply Real.log_pos
    rw [lt_one_div (by norm_num) hr]; simpa using hr2
  have hpos : 0 < r ^ 6 / (log (1 / r)) ^ c := by positivity
  refine ⟨hr, hr1, hr2, ?_, ?_, min_le_left _ _, ?_⟩
  · have h0 : 0 ≤ r := hr.le
    have h1 : r ^ 2 ≤ (√(δ / 2) / 2) ^ 2 := pow_le_pow_left₀ h0 hrs 2
    have h2 : (√(δ / 2) / 2) ^ 2 = δ / 8 := by
      rw [div_pow, Real.sq_sqrt (by positivity)]; ring
    nlinarith
  · exact lt_min one_pos hpos
  · intro μ _ hμ
    exact lt_of_lt_of_le hμ (min_le_right _ _)

/-! ### Restriction of the secular Birkhoff expansion -/

theorem birkhoff_mono_radius {a b : ℕ} {P : ℝ → Phase (a + b) → ℝ}
    {V : Set (Fin a → ℝ)} {r r0 μ0 : ℝ}
    {P0 : ℝ → (Fin a → ℝ) → ℝ}
    {Ω : ℝ → (Fin a → ℝ) → (Fin b → ℝ)}
    {β : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ}
    (hr : 0 < r) (hrr0 : r ≤ r0)
    (h : HasSecularBirkhoffForm P V r0 μ0 P0 Ω β) :
    HasSecularBirkhoffForm P V r μ0 P0 Ω β := by
  intro μ hμ I hI
  obtain ⟨h1, h2⟩ := h μ hμ I hI
  refine ⟨fun p q hpq => h1 p q fun j => ?_, fun ε hε => ?_⟩
  · exact (hpq j).trans_le (pow_le_pow_left₀ hr.le hrr0 2)
  · obtain ⟨δ, hδ, hδr, hδ'⟩ := h2 ε hε
    refine ⟨min δ r, lt_min hδ hr, min_le_right _ _, fun p q hpq => hδ' p q fun j => ?_⟩
    have hm : min δ r ≤ δ := min_le_left _ _
    exact (hpq j).trans_le (pow_le_pow_left₀ (lt_min hδ hr).le hm 2)

end PlanarAssembly
end KAM.Planetary
end
