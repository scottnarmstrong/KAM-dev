/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Measure.Lipschitz
public import KAM.Planetary.Quantitative.Interface
public import KAM.Russmann.FundamentalDomain

/-!
# Track R: volume of the union of tori of track P's family

* `volume_le_of_lower_bound`: a map with `c ‖x - y‖ ≤ ‖T x - T y‖` on `A ⊆ ℝⁿ × ℝⁿ` (max norm)
  satisfies `meas A ≤ c^{-2n} meas T(A)`; the inverse `T(A) → A` is `c⁻¹`-Lipschitz
  (`KAM.lip_image_prod`).
* `QuantitativeFamily.volume_image_lower`: for track P's family, the union of tori over
  `[0,1)ⁿ × good` has volume at least `(1 - 2⁻¹⁰)^{2n} · meas good`; this sharpens the exported
  clause `cell_lower` (`2^{-2n}`).
* `QuantitativeFamily.image_eq_add_angleTranslate`: the union over `[0,1)ⁿ × good` meets each
  orbit of the integer angle translations at most once.
-/

@[expose] public section

open MeasureTheory Set

namespace KAM.Russmann

open KAM KAM.Planetary

variable {n : ℕ}

/-- **Inverse-Lipschitz volume bound.** If `c ‖x - y‖ ≤ ‖T x - T y‖` for `x, y ∈ A` with `c > 0`,
then `meas A ≤ c^{-2n} meas T(A)` (outer measures, max norm on `ℝⁿ × ℝⁿ`). -/
theorem volume_le_of_lower_bound {A : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {T : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} {c : ℝ} (hc : 0 < c)
    (hT : ∀ x ∈ A, ∀ y ∈ A, c * ‖x - y‖ ≤ ‖T x - T y‖) :
    volume A ≤ ENNReal.ofReal (c⁻¹ ^ (2 * n)) * volume (T '' A) := by
  set g := Function.invFunOn T A
  have hg : ∀ x ∈ A, g (T x) = x := by
    intro x hx
    have hmem : g (T x) ∈ A := Function.invFunOn_mem ⟨x, hx, rfl⟩
    have heq : T (g (T x)) = T x := Function.invFunOn_eq ⟨x, hx, rfl⟩
    have h := hT _ hmem x hx
    rw [heq, sub_self, norm_zero] at h
    have : ‖g (T x) - x‖ = 0 :=
      le_antisymm (le_of_mul_le_mul_left (by simpa using h) hc) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  have himg : g '' (T '' A) = A := by
    rw [image_image]
    exact (image_congr hg).trans (image_id' A)
  have hlip : ∀ u ∈ T '' A, ∀ v ∈ T '' A, ‖g u - g v‖ ≤ c⁻¹ * ‖u - v‖ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hg x hx, hg y hy, inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact hT x hx y hy
  have := lip_image_prod (n := n) hlip
  rwa [himg] at this

/-- The union of the tori of track P's family over `[0,1)ⁿ × good` has volume at least
`(1 - 2⁻¹⁰)^{2N} · meas good` (from the lower bi-Lipschitz clause). -/
theorem QuantitativeFamily.volume_image_lower {N : ℕ} {d : QuantitativeData N}
    {H : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} {cΔ ε : ℝ} (Q : QuantitativeFamily d H cΔ ε) :
    ENNReal.ofReal ((1 - (2 : ℝ) ^ (-10 : ℤ)) ^ (2 * N)) * volume Q.good ≤
      volume ((fun z : (Fin N → ℝ) × (Fin N → ℝ) => Q.torus z.2 z.1) '' (unitCube N ×ˢ Q.good)) := by
  set c : ℝ := 1 - (2 : ℝ) ^ (-10 : ℤ) with hcdef
  have hc : 0 < c := by rw [hcdef]; norm_num
  have hlow : ∀ x ∈ unitCube N ×ˢ Q.good, ∀ y ∈ unitCube N ×ˢ Q.good,
      c * ‖x - y‖ ≤ ‖Q.torus x.2 x.1 - Q.torus y.2 y.1‖ :=
    fun x hx y hy => Q.lower x.2 hx.2 y.2 hy.2 x.1 y.1
  have h1 := volume_le_of_lower_bound (n := N) hc hlow
  have hcube : volume (unitCube N) = 1 := by simp [unitCube, Real.volume_pi_Ico]
  rw [Measure.volume_eq_prod, Measure.prod_prod, hcube, one_mul, ← Measure.volume_eq_prod] at h1
  have hpow : ENNReal.ofReal (c ^ (2 * N)) * ENNReal.ofReal (c⁻¹ ^ (2 * N)) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow,
      ENNReal.ofReal_one]
  calc ENNReal.ofReal (c ^ (2 * N)) * volume Q.good
      ≤ ENNReal.ofReal (c ^ (2 * N)) * (ENNReal.ofReal (c⁻¹ ^ (2 * N)) *
          volume ((fun z : (Fin N → ℝ) × (Fin N → ℝ) => Q.torus z.2 z.1) ''
            (unitCube N ×ˢ Q.good))) := by gcongr
    _ = _ := by rw [← mul_assoc, hpow, one_mul]

/-- The union of the tori of track P's family over `[0,1)ⁿ × good` meets each orbit of the integer
angle translations at most once. -/
theorem QuantitativeFamily.image_eq_add_angleTranslate {N : ℕ} {d : QuantitativeData N}
    {H : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} {cΔ ε : ℝ} (Q : QuantitativeFamily d H cΔ ε) :
    ∀ z ∈ (fun z : (Fin N → ℝ) × (Fin N → ℝ) => Q.torus z.2 z.1) '' (unitCube N ×ˢ Q.good),
    ∀ z' ∈ (fun z : (Fin N → ℝ) × (Fin N → ℝ) => Q.torus z.2 z.1) '' (unitCube N ×ˢ Q.good),
    ∀ k : Fin N → ℤ, z = z' + angleTranslate k → k = 0 := by
  rintro _ ⟨⟨θ, b⟩, ⟨hθ, hb⟩, rfl⟩ _ ⟨⟨θ', b'⟩, ⟨hθ', hb'⟩, rfl⟩ k hk
  have hlat : Q.torus b' (θ' + fun i => (k i : ℝ)) = Q.torus b' θ' + angleTranslate k :=
    (Q.lattice b' hb').2.1 θ' k
  have h3 := Q.lower b hb b' hb' θ (θ' + fun i => (k i : ℝ))
  simp only at hk
  rw [hk, ← hlat, sub_self, norm_zero] at h3
  have hc : 0 < 1 - (2 : ℝ) ^ (-10 : ℤ) := by norm_num
  have h4 : ‖(θ, b) - (θ' + fun i => (k i : ℝ), b')‖ = 0 :=
    le_antisymm (le_of_mul_le_mul_left (by simpa using h3) hc) (norm_nonneg _)
  have h5 : θ = θ' + fun i => (k i : ℝ) := by
    have := congrArg Prod.fst (sub_eq_zero.1 (norm_eq_zero.1 h4))
    simpa using this
  funext i
  have e : (k i : ℝ) = θ i - θ' i := by
    have := congrFun h5 i
    simp only [Pi.add_apply] at this
    linarith
  obtain ⟨h0, h1⟩ := hθ i (mem_univ i)
  obtain ⟨h0', h1'⟩ := hθ' i (mem_univ i)
  have hlt : (k i : ℝ) < 1 := by rw [e]; linarith
  have hgt : (-1 : ℝ) < k i := by rw [e]; linarith
  have : k i < 1 := by exact_mod_cast hlt
  have : -1 < k i := by exact_mod_cast hgt
  simp only [Pi.zero_apply]
  omega

end KAM.Russmann

end
