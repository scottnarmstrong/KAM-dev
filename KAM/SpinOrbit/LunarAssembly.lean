/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Graph.Cert
public import KAM.SpinOrbit.RotFreq
public import KAM.SpinOrbit.LunarParams
public import KAM.SpinOrbit.Barrier
public import KAM.Certificate.Arith.Fixed

/-!
# The lunar assembly, parametric in the certificate data (track SO, package SO-LUNAR-A)

The final results for arbitrary graph certificates `gL`, `gU` (design §6, 'Barrier and final
theorems'): the hypotheses are the signed conclusions of the data theorems with the data
constants replaced by variables, plus the rational band inequalities the data must satisfy.

* `lunar_barriers_of`: two barriers in `[967/1000, 1033/1000]`, below `pLo` and above `pHi`
  (`soRotBarrier_of_cert` with `lunarRotFreq{Minus,Plus}_isDiophantine`, then band widening).
* `lunar_spin_confinement_of`: confinement through `so_confinement`.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate

/-- The mantissa precision of the production backend. -/
def soPrecision : ℕ := 320

/-- The production backend: fixed point. -/
abbrev SoBackend : Type := CertFixed soPrecision

/-- A barrier with values in `[lo, hi]` is a barrier for any wider band. -/
def SoBarrier.widen {lo hi lo' hi' : ℝ} (B : SoBarrier lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    SoBarrier lo' hi' where
  P := B.P
  continuous := B.continuous
  periodic_q := B.periodic_q
  periodic_φ := B.periodic_φ
  invariant := B.invariant
  lower q φ := hlo.trans (B.lower q φ)
  upper q φ := (B.upper q φ).trans hhi

private theorem lunarR1Kappa_pos : 0 < lunarR1Kappa := by decide +kernel

private theorem lunarR1TimeScale_pos : 0 < lunarR1TimeScale := by decide +kernel

/-- The barrier of a passing lunar certificate at the R1 parameters. -/
private theorem lunar_barrier_of_cert (g : SoGraphCert SoBackend) {err disp : ℚ} {ν : ℝ}
    (hham : g.base.ham = soRotHamExprScaled lunarR1TimeScale)
    (hpar : g.base.params = lunarR1 err disp) (hc : checkTorusCertificate g.base = true)
    (hg : checkSoGraph g = true) (hω : FreqEncloses 2 g.base.freqBox (lunarRotFreq ν lunarR1Kappa))
    (hdio : IsDiophantine ((lunarR1Kappa : ℝ) / 42) 1 (lunarRotFreq ν lunarR1Kappa)) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - disp) ((g.pHi : ℝ) + disp)) := by
  have h := soRotBarrier_of_cert g lunarR1TimeScale_pos hham hc hg hω (by
    rw [hpar]; simpa [lunarR1] using hdio)
  rwa [hpar] at h

/-- **Theorem A, parametric in the data.** -/
theorem lunar_barriers_of (gL gU : SoGraphCert SoBackend) (errL dispL errU dispU pLo pHi : ℚ)
    (hhamL : gL.base.ham = soRotHamExprScaled lunarR1TimeScale)
    (hhamU : gU.base.ham = soRotHamExprScaled lunarR1TimeScale)
    (hparL : gL.base.params = lunarR1 errL dispL) (hparU : gU.base.params = lunarR1 errU dispU)
    (hcL : checkTorusCertificate gL.base = true) (hcU : checkTorusCertificate gU.base = true)
    (hgL : checkSoGraph gL = true) (hgU : checkSoGraph gU = true)
    (hωL : FreqEncloses 2 gL.base.freqBox (lunarRotFreq lunarNuMinus lunarR1Kappa))
    (hωU : FreqEncloses 2 gU.base.freqBox (lunarRotFreq lunarNuPlus lunarR1Kappa))
    (hbandL : 967 / 1000 ≤ gL.pLo - dispL) (hbelow : gL.pHi + dispL < pLo) (hlt : pLo < pHi)
    (habove : pHi < gU.pLo - dispU) (hbandU : gU.pHi + dispU ≤ 1033 / 1000) :
    ∃ (Bm : SoBarrier (967 / 1000) (1033 / 1000)) (Bp : SoBarrier (967 / 1000) (1033 / 1000)),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ) := by
  obtain ⟨BL⟩ := lunar_barrier_of_cert gL hhamL hparL hcL hgL hωL
    (lunarRotFreqMinus_isDiophantine lunarR1Kappa_pos)
  obtain ⟨BU⟩ := lunar_barrier_of_cert gU hhamU hparU hcU hgU hωU
    (lunarRotFreqPlus_isDiophantine lunarR1Kappa_pos)
  have hbL : ((967 / 1000 : ℚ) : ℝ) ≤ (gL.pLo : ℝ) - dispL := by exact_mod_cast hbandL
  have hbe : ((gL.pHi : ℝ) + dispL) < pLo := by exact_mod_cast hbelow
  have hl : (pLo : ℝ) < pHi := by exact_mod_cast hlt
  have hab : (pHi : ℝ) < (gU.pLo : ℝ) - dispU := by exact_mod_cast habove
  have hbU : (gU.pHi : ℝ) + dispU ≤ ((1033 / 1000 : ℚ) : ℝ) := by exact_mod_cast hbandU
  have hL0 := (BL.lower 0 0).trans (BL.upper 0 0)
  have hU0 := (BU.lower 0 0).trans (BU.upper 0 0)
  push_cast at hbL hbU
  refine ⟨BL.widen hbL (by linarith), BU.widen (by linarith) hbU, fun q φ => ?_,
    fun q φ => ?_, fun q φ => ?_⟩
  · have := BL.upper q φ; have := BU.lower q φ
    show BL.P q φ < BU.P q φ
    linarith
  · have := BL.upper q φ
    show BL.P q φ < pLo
    linarith
  · have := BU.lower q φ
    show (pHi : ℝ) < BU.P q φ
    linarith

/-- **Theorem B, parametric in the window.** -/
theorem lunar_spin_confinement_of (pLo pHi : ℚ)
    (hB : ∃ (Bm : SoBarrier (967 / 1000) (1033 / 1000))
      (Bp : SoBarrier (967 / 1000) (1033 / 1000)),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ))
    (q₀ p₀ φ₀ : ℝ) (hp : (pLo : ℝ) < p₀ ∧ p₀ < pHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ 33 / 1000) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := by
  obtain ⟨Bm, Bp, -, hm, hpB⟩ := hB
  obtain ⟨z, hz, hconf, huniq⟩ := so_confinement Bm Bp (q₀, p₀, φ₀)
    ((hm q₀ φ₀).trans hp.1) (hp.2.trans (hpB q₀ φ₀))
  refine ⟨z, hz, fun t => ?_, huniq⟩
  have h1 := Bm.lower (z t).1 (z t).2.2
  have h2 := Bp.upper (z t).1 (z t).2.2
  obtain ⟨c1, c2⟩ := hconf t
  rw [abs_le]
  constructor <;> linarith

end KAM.SpinOrbit
