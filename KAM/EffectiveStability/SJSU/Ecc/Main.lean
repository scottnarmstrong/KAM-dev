/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Ecc.Sound
public import KAM.EffectiveStability.SJSU.Ecc.TreePP
public import KAM.EffectiveStability.SJSU.Ecc.TreePM
public import KAM.EffectiveStability.SJSU.Ecc.TreeMP
public import KAM.EffectiveStability.SJSU.Ecc.TreeMM

/-!
# SJSU eccentricity enclosure on the tube (T2-CONF, package N6)

The tube of T2-CONF is `I_k = B_k(φ) + v_k`, `|v_k| ≤ r = κδ = 2·10⁻⁶`, all `φ`, with the centre
`B_k(φ) = Ī_k + Σ_m (-m_k σ_m) cos(m₁ φ₀ + m₂ φ₁)` (`sjsuEccCenter`, the 2,790 modes of `S` in
`.drafts/g2/data/literal-v1.json`, `m_3 = -m₁ - m₂`). With `V′` the exact rotation (`z = V′ w`),
`w_k = √I_k e^{i q_k}` and `q = (φ₀, φ₁, 0)`, `Γ_j = |z_j|²` (`eccGamma sjsuEccV I φ j`).

* `sjsu_tube_gamma`: `Γ_lo_j ≤ Γ_j ≤ Γ_hi_j` on the tube, with the rational `Γ` bounds
  `sjsuEccData.Glo`, `sjsuEccData.Ghi` (`sjsuGammaLo`, `sjsuGammaHi`).
* `sjsu_tube_ecc`: **owner ruling (a).** On the tube, `e_j = √(1 - (1 - Γ_j/Λ*_j)²)` lies in
  `[0.026, 0.062]` (Jupiter), `[0.009, 0.085]` (Saturn), `[0.006, 0.063]` (Uranus), with `Λ*` the
  dataset's `parameters.Lambda_star` (`applications/sjsu/data/sjsu18-o2.json`).
* `sjsu_tube_ecc_of_dev`: the same in the form `I = B(φ) + v`, `|v_k| ≤ 2·10⁻⁶`.

The proof is the generic checker `KAM.EffectiveStability.Tube.eccGamma_bounds_of_check` run on the
data `sjsuEccData` (`sjsuEcc_globalOK`) and the four chart trees (900 cells,
`sjsuEccTree{PP,PM,MP,MM}_ok`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The SJSU tube centre `B_k(φ) = Ī_k + Σ_m (-m_k σ_m) cos(m₁ φ₀ + m₂ φ₁)`. -/
def sjsuEccCenter (k : Fin 3) (φ : Fin 2 → ℝ) : ℝ := tubeCenter sjsuEccModes sjsuEccIbar k φ

/-- The dataset's reference actions `Λ*` (`parameters.Lambda_star`, verbatim). -/
def sjsuLambdaStar : Fin 3 → ℝ :=
  ![5.3993226066969503769e-1, 2.1912825008425995084e-1, 4.7474331515411474555e-2]

/-- The lower `Γ` bounds, `Λ*_j (1 - √(1 - lo_j²)) ≤ Γ_lo_j`. -/
def sjsuGammaLo : Fin 3 → ℚ := sjsuEccData.Glo

/-- The upper `Γ` bounds, `Γ_hi_j ≤ Λ*_j (1 - √(1 - hi_j²))`. -/
def sjsuGammaHi : Fin 3 → ℚ := sjsuEccData.Ghi

/-- The four chart trees. -/
def sjsuEccTrees : Bool → Bool → ETree
  | true, true => sjsuEccTreePP
  | true, false => sjsuEccTreePM
  | false, true => sjsuEccTreeMP
  | false, false => sjsuEccTreeMM

theorem sjsuEccTrees_ok (s₁ s₂ : Bool) :
    checkTree sjsuEccData (rootBox s₁ s₂) (sjsuEccTrees s₁ s₂) = true := by
  cases s₁ <;> cases s₂
  · exact sjsuEccTreeMM_ok
  · exact sjsuEccTreeMP_ok
  · exact sjsuEccTreePM_ok
  · exact sjsuEccTreePP_ok

/-- **`Γ` on the SJSU tube**: for every `φ` and every `I` with `|I_k - B_k(φ)| ≤ 2·10⁻⁶`,
`Γ_lo_j ≤ Γ_j(I, φ) ≤ Γ_hi_j`. -/
theorem sjsu_tube_gamma (φ : Fin 2 → ℝ) (I : Fin 3 → ℝ)
    (hI : ∀ k, |I k - sjsuEccCenter k φ| ≤ 2 / 10 ^ 6)
    (j : Fin 3) :
    (sjsuGammaLo j : ℝ) ≤ eccGamma sjsuEccV I φ j ∧ eccGamma sjsuEccV I φ j ≤ sjsuGammaHi j := by
  have hr : ((sjsuEccData.r : ℚ) : ℝ) = 2 / 10 ^ 6 := by
    simp only [sjsuEccData]; norm_num
  exact eccGamma_bounds_of_check sjsuEcc_globalOK sjsuEccTrees sjsuEccTrees_ok φ I
    (fun k => by rw [hr]; exact hI k) j

/-- The rational conditions turning the `Γ` bounds into the eccentricity intervals. -/
theorem sjsu_ecc_conditions (j : Fin 3) :
    0 < sjsuLambdaStar j ∧ (0 : ℝ) ≤ ![0.026, 0.009, 0.006] j ∧ (0 : ℝ) ≤ ![0.062, 0.085, 0.063] j ∧
      0 ≤ 1 - (sjsuGammaHi j : ℝ) / sjsuLambdaStar j ∧
      (1 - (sjsuGammaLo j : ℝ) / sjsuLambdaStar j) ^ 2 ≤ 1 - (![0.026, 0.009, 0.006] j : ℝ) ^ 2 ∧
      1 - (![0.062, 0.085, 0.063] j : ℝ) ^ 2 ≤
        (1 - (sjsuGammaHi j : ℝ) / sjsuLambdaStar j) ^ 2 := by
  fin_cases j <;>
    simp [sjsuLambdaStar, sjsuGammaLo, sjsuGammaHi, sjsuEccData] <;> norm_num

/-- **Eccentricities on the SJSU tube** (owner ruling (a)): for every `φ` and every `I` with
`|I_k - B_k(φ)| ≤ 2·10⁻⁶`, `e_j = √(1 - (1 - Γ_j/Λ*_j)²)` lies in `[0.026, 0.062]`,
`[0.009, 0.085]`, `[0.006, 0.063]` for `j = J, S, U`. -/
theorem sjsu_tube_ecc (φ : Fin 2 → ℝ) (I : Fin 3 → ℝ)
    (hI : ∀ k, |I k - sjsuEccCenter k φ| ≤ 2 / 10 ^ 6)
    (j : Fin 3) :
    ![0.026, 0.009, 0.006] j ≤
        Real.sqrt (1 - (1 - eccGamma sjsuEccV I φ j / sjsuLambdaStar j) ^ 2) ∧
      Real.sqrt (1 - (1 - eccGamma sjsuEccV I φ j / sjsuLambdaStar j) ^ 2) ≤
        ![0.062, 0.085, 0.063] j := by
  obtain ⟨h1, h2⟩ := sjsu_tube_gamma φ I hI j
  obtain ⟨hΛ, -, hhi, hu, hl, hh⟩ := sjsu_ecc_conditions j
  exact ecc_bounds_of_gamma hΛ hhi h1 h2 hu hl hh

/-- `sjsu_tube_ecc` in the deviation form `I = B(φ) + v`, `|v_k| ≤ 2·10⁻⁶`. -/
theorem sjsu_tube_ecc_of_dev (φ : Fin 2 → ℝ) (v : Fin 3 → ℝ) (hv : ∀ k, |v k| ≤ 2 / 10 ^ 6)
    (j : Fin 3) :
    ![0.026, 0.009, 0.006] j ≤
        Real.sqrt (1 - (1 - eccGamma sjsuEccV (fun k => sjsuEccCenter k φ + v k) φ j /
          sjsuLambdaStar j) ^ 2) ∧
      Real.sqrt (1 - (1 - eccGamma sjsuEccV (fun k => sjsuEccCenter k φ + v k) φ j /
          sjsuLambdaStar j) ^ 2) ≤
        ![0.062, 0.085, 0.063] j :=
  sjsu_tube_ecc φ _ (fun k => by simpa using hv k) j

end KAM.EffectiveStability.SJSU

end
