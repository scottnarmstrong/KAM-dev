/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.ScalingReal
public import KAM.Planetary.SecularForm.Quartic.ScalingComplex
public import KAM.Planetary.SecularForm.Quartic.ScalingTube
public import KAM.Planetary.SecularForm.Quartic.ScalingEmb
public import KAM.Strip.AnalyticTaylor

/-!
# Secular form: analyticity of the dimensionless pair average

Blueprint P, Part 8, `stepP:p8:q4-a`: `dimensionlessPair` is real-analytic on `separatedDomain`.
The real change of variables to the eccentric longitudes is `ScalingReal`, the complexified
integrand `ScalingComplex`, the uniform branch conditions and holomorphy of the cell integral
`ScalingTube`, and the real embedding `ScalingEmb`; here the real analyticity is descended from
the complex one.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

theorem quartic_scaling : AnalyticOnNhd ℝ dimensionlessPair separatedDomain := by
  intro z₀ hz₀
  obtain ⟨U, hUo, hU0, hUg⟩ := qsc_tube hz₀
  have hdiff := qsc_differentiableOn hUo hUg
  have hA : AnalyticAt ℂ qscAvgC (qscEmb z₀) :=
    analyticOnNhd_of_differentiableOn hUo hdiff _ hU0
  have h1 : AnalyticAt ℝ (fun y => (qscAvgC (qscEmbCLM y)).re) z₀ :=
    (Complex.reCLM.analyticAt _).comp
      ((hA.restrictScalars (𝕜 := ℝ)).comp (qscEmbCLM.analyticAt z₀))
  refine h1.congr ?_
  filter_upwards [qsc_isOpen_separatedDomain.mem_nhds hz₀] with y hy
  rw [qscEmbCLM_apply, qsc_avgC_real hy, Complex.ofReal_re, qsc_dimensionlessPair hy]

end SecularForm
end KAM.Planetary
end
