/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Osculating.Estimates

/-!
# The pointwise core of `LP:MAIN L16 (43)`

Package LP-OSC, `LP:MAIN L16 (508–529)`; track LP, non-frozen; the statement surface is proposed
in docs/tracks/LP/FREEZE-PROPOSAL.md.

`osc_core` is the whole estimate (43) at the level of one position `q`, one reference velocity `v`
(with the unperturbed specific elements, `k = 1`) and the actual velocity `V` (parameter `k`),
with explicit constants.  The caller (`Osculating.lean`) supplies masses and phases.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Kepler KAM.Planetary

/-- Energy-error constant `A_E`. -/
def oscAE (D Pv dS : ℝ) : ℝ := D * (2 * Pv + D) / 2 + 1 / dS

/-- Eccentricity-vector error constant `A_F` (before the `k`-normalization). -/
def oscAF (R D Pv dS : ℝ) : ℝ := R * (D * (4 * Pv + 2 * D) + 1 / dS)

/-- Bound for the unperturbed specific energy `|E| ≤ B`. -/
def oscB (Pv dS : ℝ) : ℝ := Pv ^ 2 / 2 + 1 / dS

/-- Axis-error constant `A_a`. -/
def oscAa (D Pv dS c1 : ℝ) : ℝ := (oscAE D Pv dS + oscB Pv dS) / c1 ^ 2

/-- Eccentricity-vector error constant `A_e`. -/
def oscAe (R D Pv dS : ℝ) : ℝ := oscAF R D Pv dS + 1

/-- Axis bound `a ≤ a_max = 1/(2 c₁)`. -/
def oscAmax (c1 : ℝ) : ℝ := 1 / (2 * c1)

/-- Peri/apo-error constant `A_osc`. -/
def oscAperi (R D Pv dS c1 : ℝ) : ℝ :=
  2 * oscAa D Pv dS c1 + oscAmax c1 * oscAe R D Pv dS

theorem oscAE_pos {D Pv dS : ℝ} (hD : 0 ≤ D) (hPv : 0 ≤ Pv) (hdS : 0 < dS) : 0 < oscAE D Pv dS := by
  unfold oscAE; positivity

theorem oscAF_pos {R D Pv dS : ℝ} (hR : 0 < R) (hD : 0 ≤ D) (hPv : 0 ≤ Pv) (hdS : 0 < dS) :
    0 < oscAF R D Pv dS := by
  unfold oscAF; positivity

theorem oscB_pos {Pv dS : ℝ} (hdS : 0 < dS) : 0 < oscB Pv dS := by unfold oscB; positivity

theorem oscAe_pos {R D Pv dS : ℝ} (hR : 0 < R) (hD : 0 ≤ D) (hPv : 0 ≤ Pv) (hdS : 0 < dS) :
    0 < oscAe R D Pv dS := by
  unfold oscAe; have := oscAF_pos hR hD hPv hdS; linarith

theorem oscAa_pos {D Pv dS c1 : ℝ} (hD : 0 ≤ D) (hPv : 0 ≤ Pv) (hdS : 0 < dS) (hc1 : 0 < c1) :
    0 < oscAa D Pv dS c1 := by
  unfold oscAa
  have := oscAE_pos hD hPv hdS
  have := oscB_pos (Pv := Pv) hdS
  positivity

theorem oscAperi_pos {R D Pv dS c1 : ℝ} (hR : 0 < R) (hD : 0 ≤ D) (hPv : 0 ≤ Pv) (hdS : 0 < dS)
    (hc1 : 0 < c1) : 0 < oscAperi R D Pv dS c1 := by
  unfold oscAperi oscAmax
  have := oscAa_pos hD hPv hdS hc1
  have := oscAe_pos hR hD hPv hdS
  positivity

/-- Perihelion/aphelion error from the axis and eccentricity errors (`σ = ∓1`):
`a₁ (1 + σ ε₁) - a₀ (1 + σ ε₀) = (a₁ - a₀) + σ ((a₁ - a₀) ε₁ + a₀ (ε₁ - ε₀))`. -/
theorem abs_peri_apo_sub_le {a1 a0 ε1 ε0 s Aa Ae amax σ : ℝ} (hσ : |σ| ≤ 1) (hε0 : 0 ≤ ε1)
    (hε1 : ε1 ≤ 1) (ha0 : 0 ≤ a0) (ha : a0 ≤ amax) (h1 : |a1 - a0| ≤ s * Aa)
    (h2 : |ε1 - ε0| ≤ s * Ae) :
    |a1 * (1 + σ * ε1) - a0 * (1 + σ * ε0)| ≤ s * (2 * Aa + amax * Ae) := by
  have hid : a1 * (1 + σ * ε1) - a0 * (1 + σ * ε0) =
      (a1 - a0) + σ * ((a1 - a0) * ε1 + a0 * (ε1 - ε0)) := by ring
  have t1 : |(a1 - a0) * ε1| ≤ s * Aa := by
    rw [abs_mul, abs_of_nonneg hε0]
    calc |a1 - a0| * ε1 ≤ |a1 - a0| * 1 :=
          mul_le_mul_of_nonneg_left hε1 (abs_nonneg _)
      _ ≤ s * Aa := by linarith
  have t2 : |a0 * (ε1 - ε0)| ≤ amax * (s * Ae) := by
    rw [abs_mul, abs_of_nonneg ha0]
    exact mul_le_mul ha h2 (abs_nonneg _) (ha0.trans ha)
  have t3 : |σ * ((a1 - a0) * ε1 + a0 * (ε1 - ε0))| ≤ s * Aa + amax * (s * Ae) := by
    rw [abs_mul]
    calc |σ| * |(a1 - a0) * ε1 + a0 * (ε1 - ε0)|
        ≤ 1 * |(a1 - a0) * ε1 + a0 * (ε1 - ε0)| :=
          mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
      _ ≤ s * Aa + amax * (s * Ae) := by
          rw [one_mul]; exact (abs_add_le _ _).trans (add_le_add t1 t2)
  rw [hid]
  calc _ ≤ |a1 - a0| + |σ * ((a1 - a0) * ε1 + a0 * (ε1 - ε0))| := abs_add_le _ _
    _ ≤ s * Aa + (s * Aa + amax * (s * Ae)) := add_le_add h1 t3
    _ = s * (2 * Aa + amax * Ae) := by ring

/-- **The estimate (43), pointwise** (`LP:MAIN L16 (508–529)`).  Data: a position `q` with
`dS ≤ |q| ≤ R`, a reference velocity `v` with `|v| ≤ Pv`, the perturbed velocity `V` with
`|V - v| ≤ s D`, a parameter `k` with `1 ≤ k ≤ 1 + s`, `s ≤ 1`, the unperturbed energy
`E ≤ -c₁` and eccentricity `|e| ≤ e_* < 1`, and `s` small.  Conclusions: the perturbed energy is
`≤ E + c₁/2` (hence `≤ -c₁/2`), the perturbed eccentricity is `< 1`, and the axis, eccentricity
vector, perihelion and aphelion errors are bounded linearly in `s`. -/
theorem osc_core {k s D Pv R dS c1 eStar : ℝ} {q v V : Fin 2 → ℝ}
    (hdS : 0 < dS) (hr : dS ≤ planeLength q) (hrR : planeLength q ≤ R)
    (hv : planeLength v ≤ Pv) (hVv : planeLength (V - v) ≤ s * D)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hD : 0 ≤ D) (hPv : 0 ≤ Pv) (hk1 : 1 ≤ k) (hk : k - 1 ≤ s)
    (hc1 : 0 < c1) (hE0 : specEnergy 1 q v ≤ -c1)
    (he : eStar < 1) (he0 : planeLength (specEccVector 1 q v) ≤ eStar)
    (hsE : s * oscAE D Pv dS ≤ c1 / 2) (hsEcc : s * oscAe R D Pv dS ≤ (1 - eStar) / 2) :
    specEnergy k q V ≤ specEnergy 1 q v + c1 / 2 ∧
    |specAxis k q V - specAxis 1 q v| ≤ s * oscAa D Pv dS c1 ∧
    planeLength (specEccVector k q V - specEccVector 1 q v) ≤ s * oscAe R D Pv dS ∧
    planeLength (specEccVector k q V) < 1 ∧
    |specAxis k q V * (1 - planeLength (specEccVector k q V)) -
        specAxis 1 q v * (1 - planeLength (specEccVector 1 q v))| ≤ s * oscAperi R D Pv dS c1 ∧
    |specAxis k q V * (1 + planeLength (specEccVector k q V)) -
        specAxis 1 q v * (1 + planeLength (specEccVector 1 q v))| ≤ s * oscAperi R D Pv dS c1 := by
  have hrpos : 0 < planeLength q := hdS.trans_le hr
  have hEn := abs_specEnergy_sub_le hdS hr hv hVv hs0 hs1 hD hk1 hk
  have hAE : oscAE D Pv dS = D * (2 * Pv + D) / 2 + 1 / dS := rfl
  have hE1 : specEnergy k q V ≤ specEnergy 1 q v + c1 / 2 := by
    have := (abs_le.1 hEn).2
    rw [← hAE] at this
    linarith
  have hE1' : specEnergy k q V ≤ -(c1 / 2) := by linarith
  have hB : |specEnergy 1 q v| ≤ oscB Pv dS := by
    have hsq : planeSq v = planeLength v ^ 2 := (KAM.Kepler.planeLength_sq v).symm
    have h1 : planeLength v ^ 2 ≤ Pv ^ 2 :=
      pow_le_pow_left₀ (KAM.Kepler.planeLength_nonneg v) hv 2
    have h2 : 1 / planeLength q ≤ 1 / dS := one_div_le_one_div_of_le hdS hr
    have h3 : 0 < 1 / planeLength q := by positivity
    have h4 : 0 ≤ planeSq v := by rw [hsq]; positivity
    unfold oscB specEnergy
    rw [abs_le]
    constructor <;> linarith
  have hAEn := oscAE_pos hD hPv hdS
  have hBn := oscB_pos (Pv := Pv) hdS
  have hax := abs_specAxis_sub_le (k := k) (μ := s) (E1 := specEnergy k q V)
    (E0 := specEnergy 1 q v) (AE := oscAE D Pv dS) (B := oscB Pv dS) hc1 hE0 hE1' hk1 hk hs0
    hAEn.le hBn.le (by rw [hAE]; exact hEn) hB
  have hax' : |specAxis k q V - specAxis 1 q v| ≤ s * oscAa D Pv dS c1 := hax
  have hF1 : planeLength (specEccVector 1 q v) ≤ 1 := he0.trans he.le
  have hecc := planeLength_specEccVector_sub_le hdS hr hrR hv hVv hs0 hs1 hD hPv hk1 hk hF1
  have hecc' : planeLength (specEccVector k q V - specEccVector 1 q v) ≤ s * oscAe R D Pv dS :=
    hecc
  have hlt : planeLength (specEccVector k q V) < 1 := by
    have := (abs_le.1 (abs_planeLength_sub_le (specEccVector k q V)
      (specEccVector 1 q v))).2
    linarith
  have hε : |planeLength (specEccVector k q V) - planeLength (specEccVector 1 q v)| ≤
      s * oscAe R D Pv dS :=
    (abs_planeLength_sub_le _ _).trans hecc'
  have ha0 : 0 ≤ specAxis 1 q v := by
    unfold specAxis
    exact (div_pos_of_neg_of_neg (by norm_num) (by linarith)).le
  have hamax : specAxis 1 q v ≤ oscAmax c1 := by
    have : specAxis 1 q v = 1 / (-(2 * specEnergy 1 q v)) := by
      unfold specAxis; rw [div_neg, neg_div]
    rw [this]
    unfold oscAmax
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hpm : ∀ σ : ℝ, |σ| ≤ 1 →
      |specAxis k q V * (1 + σ * planeLength (specEccVector k q V)) -
        specAxis 1 q v * (1 + σ * planeLength (specEccVector 1 q v))| ≤
        s * oscAperi R D Pv dS c1 := fun σ hσ =>
    abs_peri_apo_sub_le (a1 := specAxis k q V) (a0 := specAxis 1 q v)
      (ε1 := planeLength (specEccVector k q V)) (ε0 := planeLength (specEccVector 1 q v))
      (s := s) (Aa := oscAa D Pv dS c1) (Ae := oscAe R D Pv dS) (amax := oscAmax c1)
      hσ (KAM.Kepler.planeLength_nonneg _) hlt.le ha0 hamax hax' hε
  refine ⟨hE1, hax', hecc', hlt, ?_, ?_⟩
  · have h := hpm (-1) (by simp)
    have e1 : specAxis k q V * (1 - planeLength (specEccVector k q V)) -
        specAxis 1 q v * (1 - planeLength (specEccVector 1 q v)) =
        specAxis k q V * (1 + -1 * planeLength (specEccVector k q V)) -
        specAxis 1 q v * (1 + -1 * planeLength (specEccVector 1 q v)) := by ring
    rw [e1]; exact h
  · have h := hpm 1 (by simp)
    have e1 : specAxis k q V * (1 + planeLength (specEccVector k q V)) -
        specAxis 1 q v * (1 + planeLength (specEccVector 1 q v)) =
        specAxis k q V * (1 + 1 * planeLength (specEccVector k q V)) -
        specAxis 1 q v * (1 + 1 * planeLength (specEccVector 1 q v)) := by ring
    rw [e1]; exact h

end KAM.Planetary.StrongAMD

end
