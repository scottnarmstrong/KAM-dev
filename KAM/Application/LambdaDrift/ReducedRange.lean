/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Application.LambdaDrift.ReducedElements
public import KAM.Planetary.StrongAMD.Orbital
public import KAM.Planetary.StrongAMD.PlanarDictionary

/-!
# The range of the reduced action against the heliocentric action

Scoping note `docs/tracks/LP/REDUCED-MASS-SCOPE.md` §0 (consistency check), made rigorous. Additive
core; non-frozen.

For a negative heliocentric energy, the reduced action `G_i = keplerAction (redMass ν μ) z i`
(`Λ^red_i`, `ReducedElements.lean`) is, with `k = μ ν_i`, `a` the semi-axis and `r = |q_i|`,

`G_i = Λ_i / √((1 + k)(1 - k (2a/r - 1)))` (`keplerAction_redMass_eq_div_sqrt`).

Vis-viva gives `|p|² = ν²(2/r - 1/a)`, so `E^red = E (1 - k (2a/r - 1))`. Along the orbit
`a(1 - e) ≤ r ≤ a(1 + e)`, so `2a/r - 1` lies between `(1 - e)/(1 + e)` and `(1 + e)/(1 - e)`, and
`G_i - Λ_i` lies between `Λ_i (1/√X_lo - 1)` and `Λ_i (1/√X_hi - 1)`, with
`X_lo = (1 + k)(1 - k (1 - e)/(1 + e))` and `X_hi = (1 + k)(1 - k (1 + e)/(1 - e))`
(`keplerAction_redMass_sub_bounds`). To first order the range is `≈ 2 k Λ e`, the note's figure.

In the Poincaré chart `L_i = Λ_i - Γ_i`, so `e² = 1 - (1 - Γ_i/Λ_i)²`: a bound `Γ_i ≤ Γmax` and
`Λ_i ≥ Λmin` bound the eccentricity (`chart_ecc_le`), and `chart_reducedAction_sub_bounds` bounds
`G_i - Λ_i` on a chart box. The two `sqrt` comparisons `le_mul_one_div_sqrt_sub_one` and
`mul_one_div_sqrt_sub_one_le` turn the bounds into decided rational inequalities.
-/

@[expose] public noncomputable section

open KAM.Planetary KAM.Planetary.StrongAMD

namespace KAM.Application.LambdaDrift

variable {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} {i : Fin n} {z : Phase (n * 2)}

/-- **The reduced action in orbital form:** `G_i = Λ_i / √((1 + k)(1 - k (2a/r - 1)))`, `k = μν_i`,
for a negative heliocentric energy and a positive reduced factor. -/
theorem keplerAction_redMass_eq_div_sqrt (hν : 0 < ν i) (hμ : 0 ≤ μ)
    (hq : 0 < planeLength (bodyVector z.1 i)) (hE : keplerEnergy ν z i < 0)
    (hX : μ * ν i * (2 * keplerAxis ν z i / planeLength (bodyVector z.1 i) - 1) < 1) :
    keplerAction (redMass ν μ) z i = keplerAction ν z i / Real.sqrt ((1 + μ * ν i) *
      (1 - μ * ν i * (2 * keplerAxis ν z i / planeLength (bodyVector z.1 i) - 1))) := by
  have hs : 0 < 1 + μ * ν i := by have := mul_nonneg hμ hν.le; linarith
  obtain ⟨ha, -, -, -, -, -, -, -, -, hP⟩ := orbital_identities i ⟨hν, hq, hE⟩
  rw [keplerAction_redMass_eq_mul hν hs z hE, reducedKeplerEnergy_eq_add hν]
  have hEa : keplerEnergy ν z i = -ν i / (2 * keplerAxis ν z i) := by
    unfold keplerAxis
    field_simp
  set a := keplerAxis ν z i
  set r := planeLength (bodyVector z.1 i)
  have hX0 : 0 < 1 - μ * ν i * (2 * a / r - 1) := by linarith
  have hEr : keplerEnergy ν z i + μ * planeSq (bodyVector z.2 i) / 2 =
      -ν i / (2 * a) * (1 - μ * ν i * (2 * a / r - 1)) := by
    rw [hP, hEa]
    field_simp
    ring
  have hEne : -ν i / (2 * a) ≠ 0 := div_ne_zero (neg_ne_zero.2 hν.ne') (by positivity)
  rw [hEr, hEa, div_mul_eq_div_div, div_self hEne, Real.sqrt_mul hs.le,
    one_div, Real.sqrt_inv]
  field_simp

/-- **The range of `G_i - Λ_i` along the orbit**, for an eccentricity bound `e` with
`k (1 + e) < 1 - e`, `k = μν_i`. -/
theorem keplerAction_redMass_sub_bounds (hν : 0 < ν i) (hμ : 0 ≤ μ)
    (hq : 0 < planeLength (bodyVector z.1 i)) (hE : keplerEnergy ν z i < 0) {e : ℝ}
    (he : planeLength (keplerEccVector ν z i) ≤ e) (hke : μ * ν i * (1 + e) < 1 - e) :
    keplerAction ν z i * (1 / Real.sqrt ((1 + μ * ν i) * (1 - μ * ν i * ((1 - e) / (1 + e)))) - 1)
        ≤ keplerAction (redMass ν μ) z i - keplerAction ν z i ∧
      keplerAction (redMass ν μ) z i - keplerAction ν z i ≤ keplerAction ν z i *
        (1 / Real.sqrt ((1 + μ * ν i) * (1 - μ * ν i * ((1 + e) / (1 - e)))) - 1) := by
  obtain ⟨ha, hΛ, -, -, -, -, -, hperi, hapo, -⟩ := orbital_identities i ⟨hν, hq, hE⟩
  set a := keplerAxis ν z i
  set r := planeLength (bodyVector z.1 i)
  set k := μ * ν i with hk
  set Λ := keplerAction ν z i
  have hk0 : 0 ≤ k := mul_nonneg hμ hν.le
  have he0 : 0 ≤ planeLength (keplerEccVector ν z i) := Real.sqrt_nonneg _
  have hee : 0 ≤ e := he0.trans he
  have h1e : 0 < 1 - e := by nlinarith
  -- the orbit radius between the perihelion and the aphelion of the bound `e`
  have hperi' : a * (1 - e) ≤ r := le_trans (by nlinarith) hperi
  have hapo' : r ≤ a * (1 + e) := le_trans hapo (by nlinarith)
  set u := 2 * a / r - 1 with hu
  have hu_hi : u ≤ (1 + e) / (1 - e) := by
    rw [hu, div_sub_one hq.ne', div_le_div_iff₀ hq h1e]
    nlinarith
  have hu_lo : (1 - e) / (1 + e) ≤ u := by
    rw [hu, div_sub_one hq.ne', div_le_div_iff₀ (by linarith) hq]
    nlinarith
  have hkv : k * ((1 + e) / (1 - e)) < 1 := by
    rw [mul_div_assoc', div_lt_one h1e]; exact hke
  have hku : k * u < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hu_hi hk0) hkv
  have hs : 0 < 1 + k := by linarith
  have heq := keplerAction_redMass_eq_div_sqrt hν hμ hq hE hku
  rw [heq]
  set X := (1 + k) * (1 - k * u)
  set Xhi := (1 + k) * (1 - k * ((1 + e) / (1 - e)))
  set Xlo := (1 + k) * (1 - k * ((1 - e) / (1 + e)))
  have hXhi : 0 < Xhi := mul_pos hs (by linarith)
  have hXXhi : Xhi ≤ X :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hu_hi hk0]) hs.le
  have hXXlo : X ≤ Xlo :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hu_lo hk0]) hs.le
  have hX : 0 < X := lt_of_lt_of_le hXhi hXXhi
  have hsq : Real.sqrt Xhi ≤ Real.sqrt X := Real.sqrt_le_sqrt hXXhi
  have hsq' : Real.sqrt X ≤ Real.sqrt Xlo := Real.sqrt_le_sqrt hXXlo
  have hpos : 0 < Real.sqrt Xhi := Real.sqrt_pos.2 hXhi
  have hposX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hup : 1 / Real.sqrt X ≤ 1 / Real.sqrt Xhi := one_div_le_one_div_of_le hpos hsq
  have hdn : 1 / Real.sqrt Xlo ≤ 1 / Real.sqrt X := one_div_le_one_div_of_le hposX hsq'
  have hGeq : Λ / Real.sqrt X - Λ = Λ * (1 / Real.sqrt X - 1) := by ring
  rw [hGeq]
  exact ⟨mul_le_mul_of_nonneg_left (by linarith) hΛ.le,
    mul_le_mul_of_nonneg_left (by linarith) hΛ.le⟩

/-- **The eccentricity on a chart box:** if `Λmin ≤ Λ_i` and `Γ_i ≤ Γmax`, then the eccentricity of
planet `i` of the chart image is at most every `e ≥ 0` with `1 - e² ≤ (1 - Γmax/Λmin)²`. -/
theorem chart_ecc_le (hν : ∀ i, 0 < ν i) {w : Phase (n + n)} (hw : w ∈ poincareProdDom n)
    (i : Fin n) {Λmin Γmax e : ℝ} (hΛmin : 0 < Λmin) (hΛ : Λmin ≤ fast w.2 i)
    (hΓ : lpGamma w i ≤ Γmax) (hc : 0 ≤ 1 - Γmax / Λmin) (he0 : 0 ≤ e)
    (he : 1 - e ^ 2 ≤ (1 - Γmax / Λmin) ^ 2) :
    planeLength (keplerEccVector ν (poincareProd ν 1 w) i) ≤ e := by
  obtain ⟨hpro, hfacts, -⟩ := sec_domain_chart_facts hν hw
  obtain ⟨hact, -, hcross⟩ := hfacts i
  obtain ⟨-, -, -, he2, -⟩ := orbital_identities i ⟨hν i, (hpro i).2.1, (hpro i).2.2.1⟩
  set Λ := fast w.2 i
  have hΓ0 : 0 ≤ lpGamma w i := by unfold lpGamma; positivity
  have hΛ0 : 0 < Λ := lt_of_lt_of_le hΛmin hΛ
  have hC : planeCross (bodyVector (poincareProd ν 1 w).1 i) (bodyVector (poincareProd ν 1 w).2 i)
      = Λ - lpGamma w i := by rw [hcross]; rfl
  rw [hact, hC] at he2
  set c := 1 - Γmax / Λmin
  -- `c Λ ≤ Λ - Γ`
  have hq : Γmax / Λmin * Λmin = Γmax := div_mul_cancel₀ _ hΛmin.ne'
  have hGm : 0 ≤ Γmax / Λmin := div_nonneg (hΓ0.trans hΓ) hΛmin.le
  have hcΛ : c * Λ ≤ Λ - lpGamma w i := by
    have : Γmax ≤ Γmax / Λmin * Λ := by
      calc Γmax = Γmax / Λmin * Λmin := hq.symm
        _ ≤ Γmax / Λmin * Λ := mul_le_mul_of_nonneg_left hΛ hGm
    simp only [c]
    linarith
  have hsq : (c * Λ) ^ 2 ≤ (Λ - lpGamma w i) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hc hΛ0.le) hcΛ 2
  have hratio : c ^ 2 ≤ (Λ - lpGamma w i) ^ 2 / Λ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc c ^ 2 * Λ ^ 2 = (c * Λ) ^ 2 := by ring
      _ ≤ _ := hsq
  have he2' : planeLength (keplerEccVector ν (poincareProd ν 1 w) i) ^ 2 ≤ e ^ 2 := by
    rw [he2]; linarith
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) he0 two_ne_zero).1 he2'

/-- **The range of `G_i - Λ_i` on a chart box** `Λmin ≤ Λ_i ≤ Λmax`, `Γ_i ≤ Γmax`, for an
eccentricity bound `e` as in `chart_ecc_le`, with `k (1 + e) < 1 - e` and `1 ≤ X_lo`. -/
theorem chart_reducedAction_sub_bounds (hν : ∀ i, 0 < ν i) (hμ : 0 ≤ μ) {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) (i : Fin n) {Λmin Λmax Γmax e : ℝ} (hΛmin : 0 < Λmin)
    (hΛ : Λmin ≤ fast w.2 i ∧ fast w.2 i ≤ Λmax) (hΓ : lpGamma w i ≤ Γmax)
    (hc : 0 ≤ 1 - Γmax / Λmin) (he0 : 0 ≤ e) (he : 1 - e ^ 2 ≤ (1 - Γmax / Λmin) ^ 2)
    (hke : μ * ν i * (1 + e) < 1 - e)
    (hlo1 : 1 ≤ (1 + μ * ν i) * (1 - μ * ν i * ((1 - e) / (1 + e)))) :
    Λmax * (1 / Real.sqrt ((1 + μ * ν i) * (1 - μ * ν i * ((1 - e) / (1 + e)))) - 1) ≤
        keplerAction (redMass ν μ) (poincareProd ν 1 w) i - fast w.2 i ∧
      keplerAction (redMass ν μ) (poincareProd ν 1 w) i - fast w.2 i ≤
        Λmax * (1 / Real.sqrt ((1 + μ * ν i) * (1 - μ * ν i * ((1 + e) / (1 - e)))) - 1) := by
  obtain ⟨hpro, hfacts, -⟩ := sec_domain_chart_facts hν hw
  have hact := (hfacts i).1
  have hecc := chart_ecc_le hν hw i hΛmin hΛ.1 hΓ hc he0 he
  obtain ⟨hlo, hhi⟩ := keplerAction_redMass_sub_bounds (hν i) hμ (hpro i).2.1 (hpro i).2.2.1
    hecc hke
  rw [hact] at hlo hhi
  set k := μ * ν i
  have hk0 : 0 ≤ k := mul_nonneg hμ (hν i).le
  have hee : e < 1 := by nlinarith
  -- the upper factor is `≥ 0`: `X_hi ≤ 1`
  have hXhi1 : (1 + k) * (1 - k * ((1 + e) / (1 - e))) ≤ 1 := by
    have hv : 1 ≤ (1 + e) / (1 - e) := by rw [le_div_iff₀ (by linarith)]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hv hk0]
  have hfhi : 0 ≤ 1 / Real.sqrt ((1 + k) * (1 - k * ((1 + e) / (1 - e)))) - 1 := by
    have h1 : Real.sqrt ((1 + k) * (1 - k * ((1 + e) / (1 - e)))) ≤ 1 :=
      Real.sqrt_le_one.2 hXhi1
    have hkv : k * ((1 + e) / (1 - e)) < 1 := by
      rw [mul_div_assoc', div_lt_one (by linarith)]; exact hke
    have h0 : 0 < Real.sqrt ((1 + k) * (1 - k * ((1 + e) / (1 - e)))) :=
      Real.sqrt_pos.2 (mul_pos (by linarith) (by linarith))
    rw [sub_nonneg, le_div_iff₀ h0]; linarith
  -- the lower factor is `≤ 0`: `1 ≤ X_lo`
  have hflo : 1 / Real.sqrt ((1 + k) * (1 - k * ((1 - e) / (1 + e)))) - 1 ≤ 0 := by
    have h1 : 1 ≤ Real.sqrt ((1 + k) * (1 - k * ((1 - e) / (1 + e)))) :=
      Real.one_le_sqrt.2 hlo1
    rw [sub_nonpos, div_le_one (by linarith)]
    exact h1
  exact ⟨le_trans (mul_le_mul_of_nonpos_right hΛ.2 hflo) hlo,
    hhi.trans (mul_le_mul_of_nonneg_right hΛ.2 hfhi)⟩

/-! ### Decided comparisons of `L (1/√X - 1)` -/

/-- `L (1/√X - 1) ≤ h` as soon as `1 ≤ (1 + h/L)² X` (with `1 + h/L ≥ 0`). -/
theorem mul_one_div_sqrt_sub_one_le {L X h : ℝ} (hL : 0 < L) (hX : 0 < X)
    (hh : 0 ≤ 1 + h / L) (h1 : 1 ≤ (1 + h / L) ^ 2 * X) :
    L * (1 / Real.sqrt X - 1) ≤ h := by
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hroot : Real.sqrt ((1 + h / L) ^ 2 * X) = (1 + h / L) * Real.sqrt X := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hh]
  have h2 : 1 ≤ (1 + h / L) * Real.sqrt X := by
    rw [← hroot]; exact Real.one_le_sqrt.2 h1
  have h3 : 1 / Real.sqrt X ≤ 1 + h / L := by
    rw [div_le_iff₀ hsX]; linarith
  have h4 : L * (h / L) = h := by field_simp
  nlinarith

/-- `g ≤ L (1/√X - 1)` as soon as `(1 + g/L)² X ≤ 1` (with `1 + g/L ≥ 0`). -/
theorem le_mul_one_div_sqrt_sub_one {L X g : ℝ} (hL : 0 < L) (hX : 0 < X)
    (hg : 0 ≤ 1 + g / L) (h1 : (1 + g / L) ^ 2 * X ≤ 1) :
    g ≤ L * (1 / Real.sqrt X - 1) := by
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hroot : Real.sqrt ((1 + g / L) ^ 2 * X) = (1 + g / L) * Real.sqrt X := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hg]
  have h2 : (1 + g / L) * Real.sqrt X ≤ 1 := by
    rw [← hroot]; exact Real.sqrt_le_one.2 h1
  have h3 : 1 + g / L ≤ 1 / Real.sqrt X := by
    rw [le_div_iff₀ hsX]; linarith
  have h4 : L * (g / L) = g := by field_simp
  nlinarith

end KAM.Application.LambdaDrift

end
