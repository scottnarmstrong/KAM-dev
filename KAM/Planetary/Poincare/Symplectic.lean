/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Chart
public import KAM.Kepler.Mass

/-!
# The Poincaré chart: Delaunay form, symplecticity, elements, circular torus, means

`bpP:p7:poincare` (b)-(d), (f) and the mean values (`bpP:p7:kepler` (c) transported):

* (b) on `Γ > 0` the chart is the mass/strength Delaunay chart `delaunayMK` in the variables
  `(λ - g, g, Λ, Λ - Γ)` with `(ξ, η) = √(2Γ) e_g`;
* (c) the chart is symplectic of factor one on all of `𝒪` (polar pull-back on `{(ξ, η) ≠ 0}` where
  it factors through the Delaunay chart, then continuity of `fderiv` across `ξ = η = 0`);
* (d) the elements (energy, axis, action, angular momentum, Laplace-Runge-Lenz vector), by one
  algebraic computation valid also at `ξ = η = 0`;
* (f) the circular torus `Γ = 0`;
* the `λ`-means of `1/|q|`, `|p|²`, `|q|`.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology
open scoped ContDiff

namespace KAM.Planetary

open KAM KAM.Kepler

section PoincareChart

private theorem sy_planeDot (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

private theorem sy_planeSq (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

section ElementsAlgebra

/-- Unit-level identities for `q̂ = K c - v + δ v`, `p̂ = J₀ (c - δ v)` with `|c| = 1`,
`|v|² = 1 - K²`, `δ (1 + K) = v · c`; the certificates are for the ideal `(hc, hv, hd)`. -/
private theorem alg_U1 (c0 c1 v0 v1 K de : ℝ) (hc : c0 ^ 2 + c1 ^ 2 = 1)
    (hv : v0 ^ 2 + v1 ^ 2 = 1 - K ^ 2) (hd : de * (1 + K) = v0 * c0 + v1 * c1) :
    (K * c0 - v0 + de * v0) ^ 2 + (K * c1 - v1 + de * v1) ^ 2 = (1 - (v0 * c0 + v1 * c1)) ^ 2 := by
  linear_combination K ^ 2 * hc + (de - 1) ^ 2 * hv +
    (-K * de + 2 * K + c0 * v0 + c1 * v1 + de - 2) * hd

private theorem alg_U2 (c0 c1 v0 v1 K de : ℝ) (hc : c0 ^ 2 + c1 ^ 2 = 1)
    (hv : v0 ^ 2 + v1 ^ 2 = 1 - K ^ 2) (hd : de * (1 + K) = v0 * c0 + v1 * c1) :
    (-c1 + de * v1) ^ 2 + (c0 - de * v0) ^ 2 = 1 - (v0 * c0 + v1 * c1) ^ 2 := by
  linear_combination hc + de ^ 2 * hv + (-K * de - c0 * v0 - c1 * v1 + de) * hd

private theorem alg_U3 (c0 c1 v0 v1 K de : ℝ) (hc : c0 ^ 2 + c1 ^ 2 = 1)
    (hv : v0 ^ 2 + v1 ^ 2 = 1 - K ^ 2) (hd : de * (1 + K) = v0 * c0 + v1 * c1) :
    (K * c0 - v0 + de * v0) * (c0 - de * v0) - (K * c1 - v1 + de * v1) * (-c1 + de * v1) =
      K * (1 - (v0 * c0 + v1 * c1)) := by
  linear_combination K * hc - de * (de - 1) * hv + (K - 1) * (de - 1) * hd

private theorem alg_U4 (c0 c1 v0 v1 K de : ℝ) (_hc : c0 ^ 2 + c1 ^ 2 = 1)
    (_hv : v0 ^ 2 + v1 ^ 2 = 1 - K ^ 2) (hd : de * (1 + K) = v0 * c0 + v1 * c1) :
    (K * c0 - v0 + de * v0) * (-c1 + de * v1) + (K * c1 - v1 + de * v1) * (c0 - de * v0) =
      (v0 * c1 - v1 * c0) * (1 - (v0 * c0 + v1 * c1)) := by
  linear_combination (c0 * v1 - c1 * v0) * hd

private theorem alg_U5a (c0 c1 v0 v1 K de : ℝ) (hc : c0 ^ 2 + c1 ^ 2 = 1)
    (hv : v0 ^ 2 + v1 ^ 2 = 1 - K ^ 2) (hd : de * (1 + K) = v0 * c0 + v1 * c1) :
    (v0 * c0 + v1 * c1) * (K * c0 - v0 + de * v0) - (v0 * c1 - v1 * c0) * (-c1 + de * v1) =
      (1 - (v0 * c0 + v1 * c1)) * v0 := by
  linear_combination v0 * hc + c0 * de * hv - c0 * (K - 1) * hd

private theorem alg_U5b (c0 c1 v0 v1 K de : ℝ) (hc : c0 ^ 2 + c1 ^ 2 = 1)
    (hv : v0 ^ 2 + v1 ^ 2 = 1 - K ^ 2) (hd : de * (1 + K) = v0 * c0 + v1 * c1) :
    (v0 * c0 + v1 * c1) * (K * c1 - v1 + de * v1) - (v0 * c1 - v1 * c0) * (c0 - de * v0) =
      (1 - (v0 * c0 + v1 * c1)) * v1 := by
  linear_combination v1 * hc + c1 * de * hv - c1 * (K - 1) * hd

end ElementsAlgebra

/-- The algebra of (d): for a unit vector `c`, `|V|² = 1 - K²` and `J = 1 - V · c > 0`, the pair
`(q, p) = (a (K c - V + δ V), M (J₀ c - δ J₀ V))` has the stated elements. -/
private theorem sy_elements_alg {m κ Λ K : ℝ} (hm : 0 < m) (hκ : 0 < κ) (hΛ : 0 < Λ) (hK : 0 < K)
    (c V : Fin 2 → ℝ) (hc : c 0 ^ 2 + c 1 ^ 2 = 1) (hv : V 0 ^ 2 + V 1 ^ 2 = 1 - K ^ 2)
    (hJ : 0 < 1 - planeDot V c) (q p : Fin 2 → ℝ)
    (hq : q = (Λ ^ 2 / (m ^ 2 * κ)) • (K • c - V + (planeDot V c / (1 + K)) • V))
    (hp : p = (m ^ 2 * κ / (Λ * (1 - planeDot V c))) •
      (quarterTurn c - (planeDot V c / (1 + K)) • quarterTurn V)) :
    (q, p) ∈ regionMK m κ ∧ energyMK m κ (q, p) = -(κ ^ 2 * m ^ 3) / (2 * Λ ^ 2) ∧
      axisMK m κ (q, p) = Λ ^ 2 / (m ^ 2 * κ) ∧ actionMK m κ (q, p) = Λ ∧
      planeCross q p = Λ * K ∧
      κ⁻¹ • ((planeSq p / m ^ 2 - κ / planeLength q) • q - (planeDot q p / m ^ 2) • p) = V := by
  obtain ⟨d, hd⟩ : ∃ d, planeDot V c = d := ⟨_, rfl⟩
  rw [hd] at hq hp hJ
  have hd' : V 0 * c 0 + V 1 * c 1 = d := by rw [← hd, sy_planeDot]
  have h1K : (1 + K) ≠ 0 := by linarith
  obtain ⟨de, hdedef⟩ : ∃ de, de = d / (1 + K) := ⟨_, rfl⟩
  rw [← hdedef] at hq hp
  have hde : de * (1 + K) = V 0 * c 0 + V 1 * c 1 := by
    rw [hdedef, hd']; exact div_mul_cancel₀ _ h1K
  have hJne : 1 - d ≠ 0 := hJ.ne'
  obtain ⟨a, hadef⟩ : ∃ a, a = Λ ^ 2 / (m ^ 2 * κ) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = m ^ 2 * κ / (Λ * (1 - d)) := ⟨_, rfl⟩
  rw [← hadef] at hq
  rw [← hMdef] at hp
  have ha : 0 < a := by rw [hadef]; positivity
  have hM : 0 < M := by rw [hMdef]; positivity
  have hq0 : q 0 = a * (K * c 0 - V 0 + de * V 0) := by rw [hq]; simp
  have hq1 : q 1 = a * (K * c 1 - V 1 + de * V 1) := by rw [hq]; simp
  have hp0 : p 0 = M * (-c 1 + de * V 1) := by rw [hp]; simp [quarterTurn]
  have hp1 : p 1 = M * (c 0 - de * V 0) := by rw [hp]; simp [quarterTurn]
  have U1 := alg_U1 (c 0) (c 1) (V 0) (V 1) K de hc hv hde
  have U2 := alg_U2 (c 0) (c 1) (V 0) (V 1) K de hc hv hde
  have U3 := alg_U3 (c 0) (c 1) (V 0) (V 1) K de hc hv hde
  have U4 := alg_U4 (c 0) (c 1) (V 0) (V 1) K de hc hv hde
  have U5a := alg_U5a (c 0) (c 1) (V 0) (V 1) K de hc hv hde
  have U5b := alg_U5b (c 0) (c 1) (V 0) (V 1) K de hc hv hde
  rw [hd'] at U1 U2 U3 U4 U5a U5b
  -- the lengths
  have hqsq : planeSq q = (a * (1 - d)) ^ 2 := by
    rw [sy_planeSq, hq0, hq1]; linear_combination a ^ 2 * U1
  have hqlen : planeLength q = a * (1 - d) := by
    unfold planeLength; rw [hqsq]; exact Real.sqrt_sq (by positivity)
  have hpsq : planeSq p = M ^ 2 * (1 - d ^ 2) := by
    rw [sy_planeSq, hp0, hp1]; linear_combination M ^ 2 * U2
  have haMJ : a * M * (1 - d) = Λ := by rw [hadef, hMdef]; field_simp
  have hcross : planeCross q p = Λ * K := by
    unfold planeCross
    rw [hq0, hq1, hp0, hp1]
    calc a * (K * c 0 - V 0 + de * V 0) * (M * (c 0 - de * V 0)) -
          a * (K * c 1 - V 1 + de * V 1) * (M * (-c 1 + de * V 1))
        = a * M * ((K * c 0 - V 0 + de * V 0) * (c 0 - de * V 0) -
            (K * c 1 - V 1 + de * V 1) * (-c 1 + de * V 1)) := by ring
      _ = a * M * (K * (1 - d)) := by rw [U3]
      _ = Λ * K := by rw [← haMJ]; ring
  have hdot : planeDot q p = Λ * (V 0 * c 1 - V 1 * c 0) := by
    rw [sy_planeDot, hq0, hq1, hp0, hp1]
    calc a * (K * c 0 - V 0 + de * V 0) * (M * (-c 1 + de * V 1)) +
          a * (K * c 1 - V 1 + de * V 1) * (M * (c 0 - de * V 0))
        = a * M * ((K * c 0 - V 0 + de * V 0) * (-c 1 + de * V 1) +
            (K * c 1 - V 1 + de * V 1) * (c 0 - de * V 0)) := by ring
      _ = a * M * ((V 0 * c 1 - V 1 * c 0) * (1 - d)) := by rw [U4]
      _ = Λ * (V 0 * c 1 - V 1 * c 0) := by rw [← haMJ]; ring
  have hE : energyMK m κ (q, p) = -(κ ^ 2 * m ^ 3) / (2 * Λ ^ 2) := by
    unfold energyMK
    show planeSq p / (2 * m) - κ * m / planeLength q = _
    rw [hpsq, hqlen, hMdef, hadef]
    field_simp
    ring
  have hAx : axisMK m κ (q, p) = Λ ^ 2 / (m ^ 2 * κ) := by
    unfold axisMK
    rw [hE]
    field_simp
  refine ⟨⟨?_, ?_, ?_⟩, hE, hAx, ?_, hcross, ?_⟩
  · show 0 < planeLength q
    rw [hqlen]; positivity
  · show energyMK m κ (q, p) < 0
    rw [hE]
    have : 0 < (κ ^ 2 * m ^ 3) / (2 * Λ ^ 2) := by positivity
    rw [neg_div]; linarith
  · show 0 < planeCross q p
    rw [hcross]; positivity
  · unfold actionMK
    rw [hAx, show κ * (Λ ^ 2 / (m ^ 2 * κ)) = (Λ / m) ^ 2 by field_simp,
      Real.sqrt_sq (by positivity)]
    field_simp
  · show κ⁻¹ • ((planeSq p / m ^ 2 - κ / planeLength q) • q - (planeDot q p / m ^ 2) • p) = V
    rw [hpsq, hqlen, hdot]
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      rw [hq0, hp0]
      have e : κ⁻¹ * ((M ^ 2 * (1 - d ^ 2) / m ^ 2 - κ / (a * (1 - d))) *
            (a * (K * c 0 - V 0 + de * V 0)) -
          Λ * (V 0 * c 1 - V 1 * c 0) / m ^ 2 * (M * (-c 1 + de * V 1))) =
          (d * (K * c 0 - V 0 + de * V 0) - (V 0 * c 1 - V 1 * c 0) * (-c 1 + de * V 1)) /
            (1 - d) := by
        rw [hMdef, hadef]; field_simp; ring
      rw [e, U5a]; field_simp
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      rw [hq1, hp1]
      have e : κ⁻¹ * ((M ^ 2 * (1 - d ^ 2) / m ^ 2 - κ / (a * (1 - d))) *
            (a * (K * c 1 - V 1 + de * V 1)) -
          Λ * (V 0 * c 1 - V 1 * c 0) / m ^ 2 * (M * (c 0 - de * V 0))) =
          (d * (K * c 1 - V 1 + de * V 1) - (V 0 * c 1 - V 1 * c 0) * (c 0 - de * V 0)) /
            (1 - d) := by
        rw [hMdef, hadef]; field_simp; ring
      rw [e, U5b]; field_simp

/-- (d): elements, including the Laplace-Runge-Lenz identity (`keplerEccVector` for `κ = 1`). -/
theorem poincare_elements {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2} (hw : w ∈ poincareDom) :
    poincare m κ w ∈ regionMK m κ ∧
    energyMK m κ (poincare m κ w) = -(κ ^ 2 * m ^ 3) / (2 * w.2 0 ^ 2) ∧
    axisMK m κ (poincare m κ w) = w.2 0 ^ 2 / (m ^ 2 * κ) ∧
    actionMK m κ (poincare m κ w) = w.2 0 ∧
    planeCross (poincare m κ w).1 (poincare m κ w).2 = w.2 0 - poincareGamma w ∧
    κ⁻¹ • ((planeSq (poincare m κ w).2 / m ^ 2 - κ / planeLength (poincare m κ w).1) •
        (poincare m κ w).1
      - (planeDot (poincare m κ w).1 (poincare m κ w).2 / m ^ 2) • (poincare m κ w).2) =
      poincareV w := by
  obtain ⟨-, hK, -, -, hsq, -, hJ⟩ := poincare_facts hw
  have hΛ : 0 < w.2 0 := hw.1
  have hc : orbitalUnit (poincareF w) 0 ^ 2 + orbitalUnit (poincareF w) 1 ^ 2 = 1 := by
    simp [orbitalUnit, Real.cos_sq_add_sin_sq]
  have hv : poincareV w 0 ^ 2 + poincareV w 1 ^ 2 = 1 - poincareK w ^ 2 := by
    rw [← sy_planeSq]; exact hsq
  have hJ' : 0 < 1 - planeDot (poincareV w) (orbitalUnit (poincareF w)) := hJ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sy_elements_alg hm hκ hΛ hK (orbitalUnit (poincareF w))
    (poincareV w) hc hv hJ' (poincare m κ w).1 (poincare m κ w).2 rfl rfl
  refine ⟨h1, h2, h3, h4, ?_, h6⟩
  rw [h5]
  have : poincareK w = 1 - poincareGamma w / w.2 0 := rfl
  rw [this]
  field_simp

/-- (f): the circular torus `Γ = 0`. -/
theorem poincare_circular {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {lam Λ : ℝ} (hΛ : 0 < Λ) :
    poincare m κ (![lam, 0], ![Λ, 0]) =
      ((Λ ^ 2 / (m ^ 2 * κ)) • (![Real.cos lam, Real.sin lam] : Fin 2 → ℝ),
       (m * √(κ / (Λ ^ 2 / (m ^ 2 * κ)))) • (![-Real.sin lam, Real.cos lam] : Fin 2 → ℝ)) := by
  have hΓ : poincareGamma ((![lam, 0], ![Λ, 0]) : Phase 2) = 0 := by simp [poincareGamma]
  have hK : poincareK ((![lam, 0], ![Λ, 0]) : Phase 2) = 1 := by simp [poincareK, hΓ]
  have hV : poincareV ((![lam, 0], ![Λ, 0]) : Phase 2) = 0 := by
    ext i; fin_cases i <;> simp [poincareV]
  have hF : poincareF ((![lam, 0], ![Λ, 0]) : Phase 2) = lam := by
    simp [poincareF, hV, keplerLong_zero_vec]
  have hs : √(κ / (Λ ^ 2 / (m ^ 2 * κ))) = m * κ / Λ := by
    rw [show κ / (Λ ^ 2 / (m ^ 2 * κ)) = (m * κ / Λ) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [hs]
  unfold poincare
  rw [hK, hV, hF]
  refine Prod.ext ?_ ?_
  · ext i; fin_cases i <;> simp [orbitalUnit]
  · ext i; fin_cases i <;> simp [orbitalUnit, keplerJac, quarterTurn, sy_planeDot] <;>
      field_simp <;> simp

private theorem sy_eccOf_scaled {m : ℝ} (hm : 0 < m) {Λ Γ : ℝ} (hΛ : 0 < Λ) :
    eccOf (m⁻¹ * Λ) (m⁻¹ * (Λ - Γ)) = √(1 - (1 - Γ / Λ) ^ 2) := by
  unfold eccOf
  congr 1
  field_simp

/-- (b): Delaunay on `Γ > 0`, `(ξ, η) = ρ e_g`, `ρ = √(2Γ)`. -/
theorem poincare_eq_delaunayMK {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {lam Λ Γ g : ℝ} (hΓ : 0 < Γ)
    (hΓΛ : Γ < Λ) :
    poincare m κ (![lam, √(2 * Γ) * Real.cos g], ![Λ, √(2 * Γ) * Real.sin g]) =
      delaunayMK m κ (![lam - g, g], ![Λ, Λ - Γ]) := by
  have hΛ : 0 < Λ := hΓ.trans hΓΛ
  have hρ : 0 < √(2 * Γ) := Real.sqrt_pos.2 (by linarith)
  have hρ2 : √(2 * Γ) ^ 2 = 2 * Γ := Real.sq_sqrt (by linarith)
  set ρ := √(2 * Γ) with hρdef
  set w : Phase 2 := (![lam, ρ * Real.cos g], ![Λ, ρ * Real.sin g]) with hw
  have h1 : w.1 1 = ρ * Real.cos g := by simp [hw]
  have h2 : w.2 1 = ρ * Real.sin g := by simp [hw]
  have h3 : w.2 0 = Λ := by simp [hw]
  have h4 : w.1 0 = lam := by simp [hw]
  have hΓw : poincareGamma w = Γ := by
    have := Real.cos_sq_add_sin_sq g
    simp only [poincareGamma, h1, h2]
    linear_combination (ρ ^ 2 / 2) * this + hρ2 / 2
  have hmem : w ∈ poincareDom := by
    refine ⟨by rw [h3]; exact hΛ, ?_⟩
    rw [hΓw, h3]; exact hΓΛ
  have hpol := poincare_facts_polar hmem hρ h1 h2
  have hK : poincareK w = 1 - Γ / Λ := by simp only [poincareK, hΓw, h3]
  have hK0 : 0 < 1 - Γ / Λ := by
    rw [← hK]; exact (poincare_facts hmem).2.1
  have hK1 : 1 - Γ / Λ < 1 := by
    have : 0 < Γ / Λ := div_pos hΓ hΛ
    linarith
  set K := 1 - Γ / Λ with hKdef
  have hpos : 0 < 1 - K ^ 2 := by nlinarith
  have he0 : 0 < √(1 - K ^ 2) := Real.sqrt_pos.2 hpos
  have he1 : √(1 - K ^ 2) < 1 := by
    rw [Real.sqrt_lt' one_pos]; nlinarith
  have he2 : √(1 - K ^ 2) ^ 2 = 1 - K ^ 2 := Real.sq_sqrt hpos.le
  have hsq : √(1 - √(1 - K ^ 2) ^ 2) = K := by
    rw [he2, show 1 - (1 - K ^ 2) = K ^ 2 by ring]
    exact Real.sqrt_sq hK0.le
  set e := √(1 - K ^ 2) with hedef
  have hV : poincareV w = e • ex g := by rw [hpol.2.1, hK]
  have hF : poincareF w = g + eccAnom (lam - g) e := by
    show keplerLong (w.1 0) (poincareV w) = _
    rw [h4, hV]; exact keplerLong_eq_add_eccAnom he0 he1 lam
  set u := eccAnom (lam - g) e with hu
  have hd : planeDot (poincareV w) (orbitalUnit (poincareF w)) = e * Real.cos u := by
    rw [hpol.2.2 (poincareF w), hF, hK, add_sub_cancel_left]
  have hJ : keplerJac (poincareV w) (poincareF w) = 1 - e * Real.cos u := by
    unfold keplerJac; rw [hd]
  have hecc : eccOf (m⁻¹ * Λ) (m⁻¹ * (Λ - Γ)) = e := sy_eccOf_scaled hm hΛ
  have h1K : 1 + K ≠ 0 := by linarith
  have hJ0 : 1 - e * Real.cos u ≠ 0 := by
    rw [← hJ]; exact (poincare_facts hmem).2.2.2.2.2.2.ne'
  show poincare m κ w = _
  unfold poincare
  rw [hK, hJ, hd, hV, hF, h3]
  simp only [delaunayMK, delaunay, orbitMapR, orbitFrame, scaleMK, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul, hecc, hsq]
  rw [← hu]
  have hee : ∀ X : ℝ, e * Real.cos u / (1 + K) * (e * X) = (1 - K) * (Real.cos u * X) := by
    intro X
    field_simp
    linear_combination (Real.cos u * X) * he2
  refine Prod.ext ?_ ?_
  · ext i; fin_cases i <;> simp [rot, ex, orbitalUnit, Real.cos_add, Real.sin_add, hee] <;>
      field_simp <;> ring
  · ext i; fin_cases i <;> simp [rot, ex, orbitalUnit, quarterTurn, Real.cos_add, Real.sin_add,
      hee] <;> field_simp <;> ring

section Means

private theorem sy_integral_shift {H : ℝ → ℝ} (hH : Function.Periodic H (2 * π)) (g : ℝ) :
    ∫ lam in (0 : ℝ)..2 * π, H (lam - g) = ∫ x in (0 : ℝ)..2 * π, H x := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => H x) g]
  have := hH.intervalIntegral_add_eq (0 - g) 0
  rw [show 2 * π - g = 0 - g + 2 * π by ring]
  simpa using this

private theorem sy_polar (x y : ℝ) :
    ∃ g : ℝ, x = √(x ^ 2 + y ^ 2) * Real.cos g ∧ y = √(x ^ 2 + y ^ 2) * Real.sin g := by
  refine ⟨Complex.arg ⟨x, y⟩, ?_, ?_⟩
  · have h := Complex.norm_mul_cos_arg (⟨x, y⟩ : ℂ)
    rw [Complex.norm_def, Complex.normSq_mk] at h
    simpa [sq] using h.symm
  · have h := Complex.norm_mul_sin_arg (⟨x, y⟩ : ℂ)
    rw [Complex.norm_def, Complex.normSq_mk] at h
    simpa [sq] using h.symm

private theorem sy_delaunayMK_eq {m κ : ℝ} (hm : 0 < m) {ℓ g Λ Γ : ℝ} (hΛ : 0 < Λ) :
    delaunayMK m κ (![ℓ, g], ![Λ, Λ - Γ]) =
      scaleMK m κ (orbitMapR ℓ g (Λ / m) (√(1 - (1 - Γ / Λ) ^ 2))) := by
  have h := sy_eccOf_scaled hm hΛ (Γ := Γ)
  simp only [delaunayMK, delaunay, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
    smul_eq_mul, h]
  rw [show Λ / m = m⁻¹ * Λ from div_eq_inv_mul Λ m]

private theorem sy_planeLength_unit (x : ℝ) :
    planeLength (![Real.cos x, Real.sin x] : Fin 2 → ℝ) = 1 := by
  simp [planeLength, sy_planeSq, Real.cos_sq_add_sin_sq]

private theorem sy_planeSq_unit (x : ℝ) : planeSq (![-Real.sin x, Real.cos x] : Fin 2 → ℝ) = 1 := by
  simp only [sy_planeSq, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [Real.cos_sq_add_sin_sq x]

/-- Mean values over `λ` of the chart (`bpP:p7:kepler` (c) transported; includes the circular
case). -/
theorem poincare_means {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2} (hw : w ∈ poincareDom) :
    let a := w.2 0 ^ 2 / (m ^ 2 * κ)
    let pt := fun lam : ℝ => poincare m κ (![lam, w.1 1], w.2)
    (2 * π)⁻¹ * (∫ lam in (0 : ℝ)..2 * π, 1 / planeLength (pt lam).1) = 1 / a ∧
    (2 * π)⁻¹ * (∫ lam in (0 : ℝ)..2 * π, planeSq (pt lam).2) = m ^ 2 * κ / a ∧
    (2 * π)⁻¹ * (∫ lam in (0 : ℝ)..2 * π, planeLength (pt lam).1) =
      a * (1 + (1 - poincareK w ^ 2) / 2) := by
  intro a pt
  have hΛ : 0 < w.2 0 := hw.1
  have hΓlt : poincareGamma w < w.2 0 := hw.2
  have ha : 0 < a := by positivity
  have hpi : (2 * π)⁻¹ * (2 * π) = 1 := inv_mul_cancel₀ (by positivity)
  obtain ⟨hΓ0, hK0, -⟩ := poincare_facts hw
  rcases hΓ0.eq_or_lt with hΓ | hΓ
  · -- the circular torus
    have h1 : w.1 1 = 0 := by
      have : w.1 1 ^ 2 = 0 := by
        unfold poincareGamma at hΓ; nlinarith [sq_nonneg (w.1 1), sq_nonneg (w.2 1)]
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    have h2 : w.2 1 = 0 := by
      have : w.2 1 ^ 2 = 0 := by
        unfold poincareGamma at hΓ; nlinarith [sq_nonneg (w.1 1), sq_nonneg (w.2 1)]
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    have hK : poincareK w = 1 := by unfold poincareK; rw [← hΓ]; simp
    have hpt : ∀ lam, pt lam = (a • (![Real.cos lam, Real.sin lam] : Fin 2 → ℝ),
        (m * √(κ / a)) • (![-Real.sin lam, Real.cos lam] : Fin 2 → ℝ)) := by
      intro lam
      have : pt lam = poincare m κ (![lam, 0], ![w.2 0, 0]) := by
        show poincare m κ (![lam, w.1 1], w.2) = _
        congr 1
        refine Prod.ext (by rw [h1]) ?_
        ext i; fin_cases i <;> simp [h2]
      rw [this, poincare_circular hm hκ hΛ]
    have hq : ∀ lam, planeLength (pt lam).1 = a := by
      intro lam
      rw [hpt lam]
      show planeLength (a • _) = a
      rw [planeLength_smul, abs_of_pos ha, sy_planeLength_unit, mul_one]
    have hp : ∀ lam, planeSq (pt lam).2 = m ^ 2 * κ / a := by
      intro lam
      rw [hpt lam]
      show planeSq ((m * √(κ / a)) • _) = _
      rw [KAM.Kepler.planeSq_smul, sy_planeSq_unit, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    simp only [hq, hp, hK]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    refine ⟨?_, ?_, ?_⟩
    · field_simp
    · field_simp
    · field_simp; ring
  · -- `Γ > 0`
    obtain ⟨Γ, hΓdef⟩ : ∃ Γ, poincareGamma w = Γ := ⟨_, rfl⟩
    rw [hΓdef] at hΓ hΓlt
    have hK : poincareK w = 1 - Γ / w.2 0 := by unfold poincareK; rw [hΓdef]
    have hKlt : poincareK w < 1 := by
      rw [hK]; have : 0 < Γ / w.2 0 := div_pos hΓ hΛ
      linarith
    obtain ⟨g, hg1, hg2⟩ := sy_polar (w.1 1) (w.2 1)
    have hsum : w.1 1 ^ 2 + w.2 1 ^ 2 = 2 * Γ := by
      rw [← hΓdef]; unfold poincareGamma; ring
    rw [hsum] at hg1 hg2
    have hpt : ∀ lam, pt lam = scaleMK m κ
        (orbitMapR (lam - g) g (w.2 0 / m) (√(1 - (1 - Γ / w.2 0) ^ 2))) := by
      intro lam
      have : pt lam = poincare m κ (![lam, √(2 * Γ) * Real.cos g],
          ![w.2 0, √(2 * Γ) * Real.sin g]) := by
        show poincare m κ (![lam, w.1 1], w.2) = _
        congr 1
        refine Prod.ext (by rw [← hg1]) ?_
        ext i; fin_cases i
        · rfl
        · simpa using hg2
      rw [this, poincare_eq_delaunayMK hm hκ hΓ hΓlt, sy_delaunayMK_eq hm hΛ]
    have hK0' : 0 < 1 - Γ / w.2 0 := by rw [← hK]; exact hK0
    have hK1' : 1 - Γ / w.2 0 < 1 := by rw [← hK]; exact hKlt
    have hpos : 0 < 1 - (1 - Γ / w.2 0) ^ 2 := by nlinarith
    have he0 : 0 < √(1 - (1 - Γ / w.2 0) ^ 2) := Real.sqrt_pos.2 hpos
    have he1 : √(1 - (1 - Γ / w.2 0) ^ 2) < 1 := by
      rw [Real.sqrt_lt' one_pos]; nlinarith
    have he2 : √(1 - (1 - Γ / w.2 0) ^ 2) ^ 2 = 1 - (1 - Γ / w.2 0) ^ 2 :=
      Real.sq_sqrt hpos.le
    obtain ⟨e, hedef⟩ : ∃ e, e = √(1 - (1 - Γ / w.2 0) ^ 2) := ⟨_, rfl⟩
    rw [← hedef] at hpt he0 he1 he2
    obtain ⟨f, hfdef⟩ : ∃ f : ℝ → Phase 2, f = fun ℓ => scaleMK m κ (orbitMapR ℓ g (w.2 0 / m) e) :=
      ⟨_, rfl⟩
    have hptf : ∀ lam, pt lam = f (lam - g) := fun lam => by rw [hpt lam, hfdef]
    have hper : Function.Periodic f (2 * π) := by
      intro ℓ
      have := orbitMapR_periodic (ℓ := ℓ) (g := g) (L := w.2 0 / m) (e := e) 1 0
        (by positivity) he0.le he1
      rw [hfdef]
      simp only [Int.cast_one, mul_one, Int.cast_zero, mul_zero, add_zero] at this ⊢
      rw [this]
    have hmean := delaunayMK_means (m := m) (κ := κ) (g := g) (Λ := w.2 0) (e := e) hm hκ hΛ
      he0.le he1
    dsimp only at hmean
    obtain ⟨m1, m2, m3⟩ := hmean
    have hK2 : 1 - poincareK w ^ 2 = e ^ 2 := by rw [hK, he2]
    refine ⟨?_, ?_, ?_⟩
    · have hI : ∫ lam in (0 : ℝ)..2 * π, 1 / planeLength (f (lam - g)).1 =
          ∫ x in (0 : ℝ)..2 * π, 1 / planeLength (f x).1 :=
        sy_integral_shift (H := fun x => 1 / planeLength (f x).1)
          (hper.comp fun z => 1 / planeLength z.1) g
      simp only [hptf]
      rw [hI, hfdef]
      exact m1
    · have hI : ∫ lam in (0 : ℝ)..2 * π, planeSq (f (lam - g)).2 =
          ∫ x in (0 : ℝ)..2 * π, planeSq (f x).2 :=
        sy_integral_shift (H := fun x => planeSq (f x).2) (hper.comp fun z => planeSq z.2) g
      simp only [hptf]
      rw [hI, hfdef]
      exact m2
    · have hI : ∫ lam in (0 : ℝ)..2 * π, planeLength (f (lam - g)).1 =
          ∫ x in (0 : ℝ)..2 * π, planeLength (f x).1 :=
        sy_integral_shift (H := fun x => planeLength (f x).1) (hper.comp fun z => planeLength z.1) g
      simp only [hptf]
      rw [hI, hfdef, hK2]
      exact m3

end Means

section Polar

/-- The polar parametrisation `((λ, ρ), (Λ, g)) ↦ ((λ, ρ cos g), (Λ, ρ sin g))` of the chart
variables. -/
private def sy_P (x : Phase 2) : Phase 2 :=
  (![x.1 0, x.1 1 * Real.cos (x.2 1)], ![x.2 0, x.1 1 * Real.sin (x.2 1)])

/-- The Delaunay variables `((λ - g, g), (Λ, Λ - ρ²/2))` (written `ρ² * 2⁻¹`) in the polar
parametrisation. -/
private def sy_T (x : Phase 2) : Phase 2 :=
  (![x.1 0 - x.2 1, x.2 1], ![x.2 0, x.2 0 - x.1 1 ^ 2 * 2⁻¹])

/-- Coordinate functionals of `Phase 2`. -/
private def sy_c1 (i : Fin 2) : Phase 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))

private def sy_c2 (i : Fin 2) : Phase 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))

private theorem sy_c1_apply (i : Fin 2) (h : Phase 2) : sy_c1 i h = h.1 i := rfl

private theorem sy_c2_apply (i : Fin 2) (h : Phase 2) : sy_c2 i h = h.2 i := rfl

private def sy_mk4 (l0 l1 l2 l3 : Phase 2 →L[ℝ] ℝ) : Phase 2 →L[ℝ] Phase 2 :=
  (ContinuousLinearMap.pi ![l0, l1]).prod (ContinuousLinearMap.pi ![l2, l3])

private theorem sy_mk4_apply (l0 l1 l2 l3 : Phase 2 →L[ℝ] ℝ) (h : Phase 2) :
    sy_mk4 l0 l1 l2 l3 h = (![l0 h, l1 h], ![l2 h, l3 h]) := by
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> rfl

private theorem sy_hasFDerivAt_mk4 {f0 f1 f2 f3 : Phase 2 → ℝ} {l0 l1 l2 l3 : Phase 2 →L[ℝ] ℝ}
    {x : Phase 2} (h0 : HasFDerivAt f0 l0 x) (h1 : HasFDerivAt f1 l1 x)
    (h2 : HasFDerivAt f2 l2 x) (h3 : HasFDerivAt f3 l3 x) :
    HasFDerivAt (fun y => ((![f0 y, f1 y] : Fin 2 → ℝ), (![f2 y, f3 y] : Fin 2 → ℝ)))
      (sy_mk4 l0 l1 l2 l3) x := by
  have hA : HasFDerivAt (fun y => (![f0 y, f1 y] : Fin 2 → ℝ))
      (ContinuousLinearMap.pi ![l0, l1]) x := by
    have := (hasFDerivAt_pi (φ := ![f0, f1]) (φ' := ![l0, l1]) (x := x)).2 (by
      intro i; fin_cases i
      · exact h0
      · exact h1)
    convert this using 2 with y
    ext i; fin_cases i <;> rfl
  have hB : HasFDerivAt (fun y => (![f2 y, f3 y] : Fin 2 → ℝ))
      (ContinuousLinearMap.pi ![l2, l3]) x := by
    have := (hasFDerivAt_pi (φ := ![f2, f3]) (φ' := ![l2, l3]) (x := x)).2 (by
      intro i; fin_cases i
      · exact h2
      · exact h3)
    convert this using 2 with y
    ext i; fin_cases i <;> rfl
  exact hA.prodMk hB

private theorem sy_hasFDerivAt_P (x : Phase 2) :
    ∃ D : Phase 2 →L[ℝ] Phase 2, HasFDerivAt sy_P D x ∧ ∀ h : Phase 2,
      D h = (![h.1 0, Real.cos (x.2 1) * h.1 1 - x.1 1 * Real.sin (x.2 1) * h.2 1],
             ![h.2 0, Real.sin (x.2 1) * h.1 1 + x.1 1 * Real.cos (x.2 1) * h.2 1]) := by
  have e1 : HasFDerivAt (fun y : Phase 2 => y.1 0) (sy_c1 0) x := (sy_c1 0).hasFDerivAt
  have e2 : HasFDerivAt (fun y : Phase 2 => y.2 0) (sy_c2 0) x := (sy_c2 0).hasFDerivAt
  have hr : HasFDerivAt (fun y : Phase 2 => y.1 1) (sy_c1 1) x := (sy_c1 1).hasFDerivAt
  have hg : HasFDerivAt (fun y : Phase 2 => y.2 1) (sy_c2 1) x := (sy_c2 1).hasFDerivAt
  have e3 := hr.mul hg.cos
  have e4 := hr.mul hg.sin
  refine ⟨sy_mk4 (sy_c1 0) _ (sy_c2 0) _, sy_hasFDerivAt_mk4 e1 e3 e2 e4, fun h => ?_⟩
  rw [sy_mk4_apply]
  simp only [add_apply, smul_apply, smul_eq_mul,
    sy_c1_apply, sy_c2_apply]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp <;> ring

private theorem sy_hasFDerivAt_T (x : Phase 2) :
    ∃ D : Phase 2 →L[ℝ] Phase 2, HasFDerivAt sy_T D x ∧ ∀ h : Phase 2,
      D h = (![h.1 0 - h.2 1, h.2 1], ![h.2 0, h.2 0 - x.1 1 * h.1 1]) := by
  have e1 : HasFDerivAt (fun y : Phase 2 => y.1 0) (sy_c1 0) x := (sy_c1 0).hasFDerivAt
  have e2 : HasFDerivAt (fun y : Phase 2 => y.2 0) (sy_c2 0) x := (sy_c2 0).hasFDerivAt
  have hr : HasFDerivAt (fun y : Phase 2 => y.1 1) (sy_c1 1) x := (sy_c1 1).hasFDerivAt
  have hg : HasFDerivAt (fun y : Phase 2 => y.2 1) (sy_c2 1) x := (sy_c2 1).hasFDerivAt
  have e3 := e1.sub hg
  have e4 := e2.sub ((hr.pow 2).mul_const 2⁻¹)
  refine ⟨sy_mk4 _ (sy_c2 1) (sy_c2 0) _, sy_hasFDerivAt_mk4 e3 hg e2 e4, fun h => ?_⟩
  rw [sy_mk4_apply]
  simp only [sub_apply, smul_apply, smul_eq_mul, sy_c1_apply, sy_c2_apply]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp
  ring

/-- The pull-back computation `d Λ ∧ d(λ - g) + d(Λ - Γ) ∧ d g = d Λ ∧ d λ + d η ∧ d ξ` in polar
coordinates, as an identity of the frozen form on the two derivative formulas. -/
private theorem sy_form_T_eq_P (ρ g : ℝ) (h k : Phase 2) :
    symplecticForm ((![h.1 0 - h.2 1, h.2 1], ![h.2 0, h.2 0 - ρ * h.1 1]) : Phase 2)
        (![k.1 0 - k.2 1, k.2 1], ![k.2 0, k.2 0 - ρ * k.1 1]) =
      symplecticForm ((![h.1 0, Real.cos g * h.1 1 - ρ * Real.sin g * h.2 1],
          ![h.2 0, Real.sin g * h.1 1 + ρ * Real.cos g * h.2 1]) : Phase 2)
        (![k.1 0, Real.cos g * k.1 1 - ρ * Real.sin g * k.2 1],
          ![k.2 0, Real.sin g * k.1 1 + ρ * Real.cos g * k.2 1]) := by
  have hsc := Real.sin_sq_add_cos_sq g
  simp only [symplecticForm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (ρ * (h.1 1 * k.2 1 - h.2 1 * k.1 1)) * hsc

private theorem sy_surj (ρ g : ℝ) (hρ : ρ ≠ 0) (u : Phase 2) :
    ∃ h : Phase 2, ((![h.1 0, Real.cos g * h.1 1 - ρ * Real.sin g * h.2 1],
          ![h.2 0, Real.sin g * h.1 1 + ρ * Real.cos g * h.2 1]) : Phase 2) = u := by
  refine ⟨(![u.1 0, Real.cos g * u.1 1 + Real.sin g * u.2 1],
    ![u.2 0, (-Real.sin g * u.1 1 + Real.cos g * u.2 1) / ρ]), ?_⟩
  have hsc := Real.sin_sq_add_cos_sq g
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp <;> field_simp <;>
    first | linear_combination (u.1 1) * hsc | linear_combination (u.2 1) * hsc

/-- On `{ρ > 0}` the chart factors through the Delaunay chart: the identity of (b) in the polar
parameters. -/
private theorem sy_chart_polar {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {y : Phase 2}
    (hρ : 0 < y.1 1) (hΓ : y.1 1 ^ 2 * 2⁻¹ < y.2 0) :
    poincare m κ (sy_P y) = delaunayMK m κ (sy_T y) := by
  have hΓ0 : 0 < y.1 1 ^ 2 * 2⁻¹ := by positivity
  have h := poincare_eq_delaunayMK hm hκ (lam := y.1 0) (g := y.2 1) hΓ0 hΓ
  have e : 2 * (y.1 1 ^ 2 * 2⁻¹) = y.1 1 ^ 2 := by ring
  rw [e, Real.sqrt_sq hρ.le] at h
  exact h

private theorem sy_P_mem {x : Phase 2} (hΛ : 0 < x.2 0) (hΓ : x.1 1 ^ 2 * 2⁻¹ < x.2 0) :
    sy_P x ∈ poincareDom := by
  refine ⟨by simpa [sy_P] using hΛ, ?_⟩
  have : poincareGamma (sy_P x) = x.1 1 ^ 2 * 2⁻¹ := by
    have hsc := Real.sin_sq_add_cos_sq (x.2 1)
    have h1 : (sy_P x).1 1 = x.1 1 * Real.cos (x.2 1) := by simp [sy_P]
    have h2 : (sy_P x).2 1 = x.1 1 * Real.sin (x.2 1) := by simp [sy_P]
    simp only [poincareGamma, h1, h2]
    linear_combination (x.1 1 ^ 2 * 2⁻¹) * hsc
  rw [this]; simpa [sy_P] using hΓ

/-- Symplecticity on `{(ξ, η) ≠ 0}`, through the polar parametrisation. -/
private theorem sy_step1 {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {x : Phase 2}
    (hρ : 0 < x.1 1) (hΛ : 0 < x.2 0) (hΓ : x.1 1 ^ 2 * 2⁻¹ < x.2 0) (u v : Phase 2) :
    symplecticForm (fderiv ℝ (poincare m κ) (sy_P x) u) (fderiv ℝ (poincare m κ) (sy_P x) v) =
      1 * symplecticForm u v := by
  have hΓ0 : 0 < x.1 1 ^ 2 * 2⁻¹ := by positivity
  have hmemP := sy_P_mem hΛ hΓ
  have hmemT : sy_T x ∈ deDom := by
    refine ⟨?_, ?_⟩ <;> simp only [sy_T, Matrix.cons_val_zero, Matrix.cons_val_one] <;> linarith
  obtain ⟨DP, hP, hDP⟩ := sy_hasFDerivAt_P x
  obtain ⟨DT, hT, hDT⟩ := sy_hasFDerivAt_T x
  have hψ : HasFDerivAt (poincare m κ) (fderiv ℝ (poincare m κ) (sy_P x)) (sy_P x) :=
    ((analyticOnNhd_poincare hm hκ) _ hmemP).differentiableAt.hasFDerivAt
  have hQ : HasFDerivAt (delaunayMK m κ) (fderiv ℝ (delaunayMK m κ) (sy_T x)) (sy_T x) :=
    ((analyticOnNhd_delaunayMK hm hκ) _ hmemT).differentiableAt.hasFDerivAt
  have h1 := hψ.comp x hP
  have h2 := hQ.comp x hT
  have hU : {y : Phase 2 | 0 < y.1 1 ∧ 0 < y.2 0 ∧ y.1 1 ^ 2 * 2⁻¹ < y.2 0} ∈ 𝓝 x := by
    have c1 : Continuous fun y : Phase 2 => y.1 1 := by fun_prop
    have c2 : Continuous fun y : Phase 2 => y.2 0 := by fun_prop
    have c3 : Continuous fun y : Phase 2 => y.1 1 ^ 2 * 2⁻¹ := by fun_prop
    exact IsOpen.mem_nhds ((isOpen_lt continuous_const c1).inter
      ((isOpen_lt continuous_const c2).inter (isOpen_lt c3 c2))) ⟨hρ, hΛ, hΓ⟩
  have heq : (poincare m κ ∘ sy_P) =ᶠ[𝓝 x] (delaunayMK m κ ∘ sy_T) := by
    filter_upwards [hU] with y hy
    exact sy_chart_polar hm hκ hy.1 hy.2.2
  have h3 : HasFDerivAt (poincare m κ ∘ sy_P)
      ((fderiv ℝ (delaunayMK m κ) (sy_T x)).comp DT) x := h2.congr_of_eventuallyEq heq
  have hder := h1.unique h3
  obtain ⟨h, rfl⟩ := sy_surj (x.1 1) (x.2 1) hρ.ne' u
  obtain ⟨k, rfl⟩ := sy_surj (x.1 1) (x.2 1) hρ.ne' v
  have e1 : ∀ z : Phase 2, fderiv ℝ (poincare m κ) (sy_P x) (DP z) =
      fderiv ℝ (delaunayMK m κ) (sy_T x) (DT z) := fun z => by
    have := congrArg (fun L : Phase 2 →L[ℝ] Phase 2 => L z) hder
    simpa using this
  rw [← hDP h, ← hDP k, e1, e1, delaunayMK_symplectic hm hκ _ hmemT, hDT, hDT, hDP, hDP,
    sy_form_T_eq_P]

end Polar

/-- (c): symplectic with factor one on all of `𝒪` (density argument across `Γ = 0`). -/
theorem poincare_symplectic {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) :
    IsSymplecticOn 1 (poincare m κ) poincareDom := by
  -- the part `Γ > 0`
  have hA : ∀ w ∈ poincareDom, 0 < poincareGamma w → ∀ u v : Phase 2,
      symplecticForm (fderiv ℝ (poincare m κ) w u) (fderiv ℝ (poincare m κ) w v) =
        1 * symplecticForm u v := by
    intro w hw hΓ u v
    obtain ⟨g, hg1, hg2⟩ := sy_polar (w.1 1) (w.2 1)
    have hsum : w.1 1 ^ 2 + w.2 1 ^ 2 = 2 * poincareGamma w := by unfold poincareGamma; ring
    rw [hsum] at hg1 hg2
    have hρ : 0 < √(2 * poincareGamma w) := Real.sqrt_pos.2 (by linarith)
    have hρ2 : √(2 * poincareGamma w) ^ 2 = 2 * poincareGamma w := Real.sq_sqrt (by linarith)
    have hx : sy_P ((![w.1 0, √(2 * poincareGamma w)], ![w.2 0, g]) : Phase 2) = w := by
      refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i
      · simp [sy_P]
      · simpa [sy_P] using hg1.symm
      · simp [sy_P]
      · simpa [sy_P] using hg2.symm
    have := sy_step1 hm hκ (x := ((![w.1 0, √(2 * poincareGamma w)], ![w.2 0, g]) : Phase 2))
      (by simpa using hρ) (by simpa using hw.1)
      (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; nlinarith [hw.2]) u v
    rwa [hx] at this
  intro w hw u v
  by_contra hne
  have hana := analyticOnNhd_poincare hm hκ
  have hcont : ContinuousOn (fun z => symplecticForm (fderiv ℝ (poincare m κ) z u)
      (fderiv ℝ (poincare m κ) z v)) poincareDom := by
    have hc : ContinuousOn (fun z => fderiv ℝ (poincare m κ) z) poincareDom :=
      hana.fderiv.continuousOn
    have h1 : ContinuousOn (fun z => fderiv ℝ (poincare m κ) z u) poincareDom :=
      hc.clm_apply continuousOn_const
    have h2 : ContinuousOn (fun z => fderiv ℝ (poincare m κ) z v) poincareDom :=
      hc.clm_apply continuousOn_const
    unfold symplecticForm
    refine continuousOn_finsetSum _ fun i _ => ?_
    have a1 : ContinuousOn (fun z => (fderiv ℝ (poincare m κ) z u).1 i) poincareDom :=
      (continuous_apply i).comp_continuousOn (continuous_fst.comp_continuousOn h1)
    have a2 : ContinuousOn (fun z => (fderiv ℝ (poincare m κ) z u).2 i) poincareDom :=
      (continuous_apply i).comp_continuousOn (continuous_snd.comp_continuousOn h1)
    have b1 : ContinuousOn (fun z => (fderiv ℝ (poincare m κ) z v).1 i) poincareDom :=
      (continuous_apply i).comp_continuousOn (continuous_fst.comp_continuousOn h2)
    have b2 : ContinuousOn (fun z => (fderiv ℝ (poincare m κ) z v).2 i) poincareDom :=
      (continuous_apply i).comp_continuousOn (continuous_snd.comp_continuousOn h2)
    exact (a2.mul b1).sub (a1.mul b2)
  rcases (poincare_facts hw).1.eq_or_lt with h0 | hpos
  swap
  · exact hne (hA w hw hpos u v)
  -- the circular locus `ξ = η = 0`: approach it along `ξ = t`
  have h1 : w.1 1 = 0 := by
    have : w.1 1 ^ 2 = 0 := by
      unfold poincareGamma at h0; nlinarith [sq_nonneg (w.1 1), sq_nonneg (w.2 1)]
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  have h2 : w.2 1 = 0 := by
    have : w.2 1 ^ 2 = 0 := by
      unfold poincareGamma at h0; nlinarith [sq_nonneg (w.1 1), sq_nonneg (w.2 1)]
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  set γ : ℝ → Phase 2 := fun t => (![w.1 0, t], w.2) with hγ
  have hγc : Continuous γ := by
    refine Continuous.prodMk ?_ continuous_const
    exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
  have hγ0 : γ 0 = w := by
    refine Prod.ext ?_ rfl
    ext i; fin_cases i <;> simp [hγ, h1]
  have hF : ContinuousAt (fun z => symplecticForm (fderiv ℝ (poincare m κ) z u)
      (fderiv ℝ (poincare m κ) z v)) w :=
    hcont.continuousAt (isOpen_poincareDom.mem_nhds hw)
  have hne' : symplecticForm (fderiv ℝ (poincare m κ) w u) (fderiv ℝ (poincare m κ) w v) ≠
      1 * symplecticForm u v := hne
  have hev : ∀ᶠ z in 𝓝 w, symplecticForm (fderiv ℝ (poincare m κ) z u)
      (fderiv ℝ (poincare m κ) z v) ≠ 1 * symplecticForm u v ∧ z ∈ poincareDom :=
    (hF.eventually_ne hne').and (isOpen_poincareDom.mem_nhds hw)
  have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), symplecticForm (fderiv ℝ (poincare m κ) (γ t) u)
      (fderiv ℝ (poincare m κ) (γ t) v) ≠ 1 * symplecticForm u v ∧ γ t ∈ poincareDom := by
    have : Filter.Tendsto γ (𝓝 0) (𝓝 w) := by
      rw [← hγ0]; exact hγc.tendsto 0
    exact this.eventually hev
  obtain ⟨t, ⟨hFt, hdom⟩, ht⟩ :=
    ((hev'.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists (f := 𝓝[≠] (0 : ℝ))
  have htne : t ≠ 0 := ht
  have hΓt : 0 < poincareGamma (γ t) := by
    have e1 : (γ t).1 1 = t := by simp [hγ]
    have e2 : (γ t).2 1 = 0 := h2
    simp only [poincareGamma, e1, e2]
    have : 0 < t ^ 2 := by positivity
    nlinarith
  exact hFt (hA (γ t) hdom hΓt u v)

end PoincareChart

end KAM.Planetary

end
