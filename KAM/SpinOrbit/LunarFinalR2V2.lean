/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.Lower.Passes
public import KAM.SpinOrbit.Data.Upper.Passes
public import KAM.SpinOrbit.LunarConstsR2

/-!
# The `N = 65` lunar theorems through the v2 certifier (SO-DATA3; nothing frozen)

* `lunar_barriers_65_v2`: two barriers in the band `[lunarR2BandLo, lunarR2BandHi]`
  (`1 ∓ 2.755 %`) enclosing the window `(lunarR2PLo, lunarR2PHi) = (0.9934, 1.0066)`: one
  application of `lunar_barriers_of_R2V2` to the kernel-checked data conclusions of
  `Data/{Lower,Upper}/Passes.lean`, with the five band inequalities by `decide +kernel` on the
  graph literals;
* `lunar_spin_confinement_65_v2`: a solution started in the window keeps `|p − 1| ≤ 2.755 %`
  for all time, by `lunar_spin_confinement_of_band`.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate

/-- The graph literals of the lower barrier. -/
theorem lunarR2_lower_graph :
    Data.Lower.cert.pLo = 9724531 / 10000000 ∧ Data.Lower.cert.pHi = 4966629 / 5000000 :=
  ⟨rfl, rfl⟩

/-- The graph literals of the upper barrier. -/
theorem lunarR2_upper_graph :
    Data.Upper.cert.pLo = 10066821 / 10000000 ∧ Data.Upper.cert.pHi = 128443 / 125000 :=
  ⟨rfl, rfl⟩

/-- The five band inequalities, on the literals. -/
theorem lunarR2_band_ineqs :
    lunarR2BandLo ≤ 9724531 / 10000000 - lunarR2LowerDisp ∧
      4966629 / 5000000 + lunarR2LowerDisp < lunarR2PLo ∧ lunarR2PLo < lunarR2PHi ∧
      lunarR2PHi < 10066821 / 10000000 - lunarR2UpperDisp ∧
      128443 / 125000 + lunarR2UpperDisp ≤ lunarR2BandHi := by
  decide +kernel

/-- **Theorem A at `N = 65`** (package R2, the v2 certifier `routeAV2` at the refined-route
witnesses, backend `CertFixed 96`). -/
theorem lunar_barriers_65_v2 :
    ∃ (Bm : SoBarrier lunarR2BandLo lunarR2BandHi) (Bp : SoBarrier lunarR2BandLo lunarR2BandHi),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < lunarR2PLo) ∧ (∀ q φ, (lunarR2PHi : ℝ) < Bp.P q φ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := lunarR2_band_ineqs
  exact lunar_barriers_of_R2V2 Data.Lower.cert Data.Upper.cert (.inr (.inr Data.Lower.refinedWit))
    (.inr (.inr Data.Upper.refinedWit)) lunarR2LowerErr lunarR2LowerDisp lunarR2UpperErr
    lunarR2UpperDisp lunarR2BandLo lunarR2BandHi lunarR2PLo lunarR2PHi Data.Lower.lower_ham
    Data.Upper.upper_ham Data.Lower.lower_params Data.Upper.upper_params Data.Lower.lower_passes
    Data.Upper.upper_passes Data.Lower.lowerGraph_passes Data.Upper.upperGraph_passes
    Data.Lower.lower_freq Data.Upper.upper_freq (lunarR2_lower_graph.1 ▸ h1)
    (lunarR2_lower_graph.2 ▸ h2) h3 (lunarR2_upper_graph.1 ▸ h4) (lunarR2_upper_graph.2 ▸ h5)

/-- **Theorem B at `N = 65`**: a solution of the spin–orbit field started with
`lunarR2PLo < p₀ < lunarR2PHi` exists for all time, is unique, and keeps `|p − 1| ≤ 2.755 %`. -/
theorem lunar_spin_confinement_65_v2 (q₀ p₀ φ₀ : ℝ)
    (hp : (lunarR2PLo : ℝ) < p₀ ∧ p₀ < lunarR2PHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ (lunarR2Delta : ℝ)) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z :=
  lunar_spin_confinement_of_band lunarR2BandLo lunarR2BandHi lunarR2Delta lunarR2PLo lunarR2PHi
    (by decide +kernel) (by decide +kernel) lunar_barriers_65_v2 q₀ p₀ φ₀ hp

end KAM.SpinOrbit
