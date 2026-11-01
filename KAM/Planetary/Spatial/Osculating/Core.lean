/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Osculating.Estimates

/-!
# The pointwise core of `LP:MAIN L16 (43)` in dimension three

Package LP-SP-OSC, `LP:MAIN L16 (508–529)` with `d = 3`; track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

`spatial_osc_core` is the whole estimate (43) at the level of one position `q`, one reference
velocity
`v` (unperturbed specific elements, `k = 1`) and the actual velocity `V` (parameter `k`), with the
explicit constants of the planar `Osculating/Core.lean` (`oscAE`, `oscAF`, `oscB`, `oscAa`, `oscAe`,
`oscAmax`, `oscAperi`), which are dimension free and reused unchanged.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD

/-- **The estimate (43), pointwise** (`LP:MAIN L16 (508–529)`).  Data: a position `q` with
`dS ≤ |q| ≤ R`, a reference velocity `v` with `|v| ≤ Pv`, the perturbed velocity `V` with
`|V - v| ≤ s D`, a parameter `k` with `1 ≤ k ≤ 1 + s`, `s ≤ 1`, the unperturbed energy
`E ≤ -c₁` and eccentricity `|e| ≤ e_* < 1`, and `s` small.  Conclusions: the perturbed energy is
`≤ E + c₁/2` (hence `≤ -c₁/2`), the perturbed eccentricity is `< 1`, and the axis, eccentricity
vector, perihelion and aphelion errors are bounded linearly in `s`. -/
theorem spatial_osc_core {k s D Pv R dS c1 eStar : ℝ} {q v V : Fin 3 → ℝ}
    (hdS : 0 < dS) (hr : dS ≤ spaceLength q) (hrR : spaceLength q ≤ R)
    (hv : spaceLength v ≤ Pv) (hVv : spaceLength (V - v) ≤ s * D)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hD : 0 ≤ D) (hPv : 0 ≤ Pv) (hk1 : 1 ≤ k) (hk : k - 1 ≤ s)
    (hc1 : 0 < c1) (hE0 : spatialSpecEnergy 1 q v ≤ -c1)
    (he : eStar < 1) (he0 : spaceLength (spatialSpecEccVector 1 q v) ≤ eStar)
    (hsE : s * oscAE D Pv dS ≤ c1 / 2) (hsEcc : s * oscAe R D Pv dS ≤ (1 - eStar) / 2) :
    spatialSpecEnergy k q V ≤ spatialSpecEnergy 1 q v + c1 / 2 ∧
    |spatialSpecAxis k q V - spatialSpecAxis 1 q v| ≤ s * oscAa D Pv dS c1 ∧
    spaceLength (spatialSpecEccVector k q V - spatialSpecEccVector 1 q v) ≤ s * oscAe R D Pv dS ∧
    spaceLength (spatialSpecEccVector k q V) < 1 ∧
    |spatialSpecAxis k q V * (1 - spaceLength (spatialSpecEccVector k q V)) -
        spatialSpecAxis 1 q v * (1 - spaceLength (spatialSpecEccVector 1 q v))| ≤ s * oscAperi R D
            Pv dS c1 ∧
    |spatialSpecAxis k q V * (1 + spaceLength (spatialSpecEccVector k q V)) -
        spatialSpecAxis 1 q v * (1 + spaceLength (spatialSpecEccVector 1 q v))| ≤ s * oscAperi R D
            Pv dS c1 := by
  have hrpos : 0 < spaceLength q := hdS.trans_le hr
  have hEn := abs_spatialSpecEnergy_sub_le hdS hr hv hVv hs0 hs1 hD hk1 hk
  have hAE : oscAE D Pv dS = D * (2 * Pv + D) / 2 + 1 / dS := rfl
  have hE1 : spatialSpecEnergy k q V ≤ spatialSpecEnergy 1 q v + c1 / 2 := by
    have := (abs_le.1 hEn).2
    rw [← hAE] at this
    linarith
  have hE1' : spatialSpecEnergy k q V ≤ -(c1 / 2) := by linarith
  have hB : |spatialSpecEnergy 1 q v| ≤ oscB Pv dS := by
    have hsq : spaceSq v = spaceLength v ^ 2 := (spaceLength_sq v).symm
    have h1 : spaceLength v ^ 2 ≤ Pv ^ 2 :=
      pow_le_pow_left₀ (spaceLength_nonneg v) hv 2
    have h2 : 1 / spaceLength q ≤ 1 / dS := one_div_le_one_div_of_le hdS hr
    have h3 : 0 < 1 / spaceLength q := by positivity
    have h4 : 0 ≤ spaceSq v := by rw [hsq]; positivity
    unfold oscB spatialSpecEnergy
    rw [abs_le]
    constructor <;> linarith
  have hAEn := oscAE_pos hD hPv hdS
  have hBn := oscB_pos (Pv := Pv) hdS
  have hax := abs_specAxis_sub_le (k := k) (μ := s) (E1 := spatialSpecEnergy k q V)
    (E0 := spatialSpecEnergy 1 q v) (AE := oscAE D Pv dS) (B := oscB Pv dS) hc1 hE0 hE1' hk1 hk hs0
    hAEn.le hBn.le (by rw [hAE]; exact hEn) hB
  have hax' : |spatialSpecAxis k q V - spatialSpecAxis 1 q v| ≤ s * oscAa D Pv dS c1 := hax
  have hF1 : spaceLength (spatialSpecEccVector 1 q v) ≤ 1 := he0.trans he.le
  have hecc := spaceLength_spatialSpecEccVector_sub_le hdS hr hrR hv hVv hs0 hs1 hD hPv hk1 hk hF1
  have hecc' : spaceLength (spatialSpecEccVector k q V - spatialSpecEccVector 1 q v) ≤ s * oscAe R
      D Pv dS :=
    hecc
  have hlt : spaceLength (spatialSpecEccVector k q V) < 1 := by
    have := (abs_le.1 (abs_spaceLength_sub_spaceLength_le (spatialSpecEccVector k q V)
      (spatialSpecEccVector 1 q v))).2
    linarith
  have hε : |spaceLength (spatialSpecEccVector k q V) - spaceLength (spatialSpecEccVector 1 q v)| ≤
      s * oscAe R D Pv dS :=
    (abs_spaceLength_sub_spaceLength_le _ _).trans hecc'
  have ha0 : 0 ≤ spatialSpecAxis 1 q v := by
    unfold spatialSpecAxis
    exact (div_pos_of_neg_of_neg (by norm_num) (by linarith)).le
  have hamax : spatialSpecAxis 1 q v ≤ oscAmax c1 := by
    have : spatialSpecAxis 1 q v = 1 / (-(2 * spatialSpecEnergy 1 q v)) := by
      unfold spatialSpecAxis; rw [div_neg, neg_div]
    rw [this]
    unfold oscAmax
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hpm : ∀ σ : ℝ, |σ| ≤ 1 →
      |spatialSpecAxis k q V * (1 + σ * spaceLength (spatialSpecEccVector k q V)) -
        spatialSpecAxis 1 q v * (1 + σ * spaceLength (spatialSpecEccVector 1 q v))| ≤
        s * oscAperi R D Pv dS c1 := fun σ hσ =>
    abs_peri_apo_sub_le (a1 := spatialSpecAxis k q V) (a0 := spatialSpecAxis 1 q v)
      (ε1 := spaceLength (spatialSpecEccVector k q V)) (ε0 := spaceLength (spatialSpecEccVector 1 q
          v))
      (s := s) (Aa := oscAa D Pv dS c1) (Ae := oscAe R D Pv dS) (amax := oscAmax c1)
      hσ (spaceLength_nonneg _) hlt.le ha0 hamax hax' hε
  refine ⟨hE1, hax', hecc', hlt, ?_, ?_⟩
  · have h := hpm (-1) (by simp)
    have e1 : spatialSpecAxis k q V * (1 - spaceLength (spatialSpecEccVector k q V)) -
        spatialSpecAxis 1 q v * (1 - spaceLength (spatialSpecEccVector 1 q v)) =
        spatialSpecAxis k q V * (1 + -1 * spaceLength (spatialSpecEccVector k q V)) -
        spatialSpecAxis 1 q v * (1 + -1 * spaceLength (spatialSpecEccVector 1 q v)) := by ring
    rw [e1]; exact h
  · have h := hpm 1 (by simp)
    have e1 : spatialSpecAxis k q V * (1 + spaceLength (spatialSpecEccVector k q V)) -
        spatialSpecAxis 1 q v * (1 + spaceLength (spatialSpecEccVector 1 q v)) =
        spatialSpecAxis k q V * (1 + 1 * spaceLength (spatialSpecEccVector k q V)) -
        spatialSpecAxis 1 q v * (1 + 1 * spaceLength (spatialSpecEccVector 1 q v)) := by ring
    rw [e1]; exact h

end KAM.Planetary.Spatial

end
