/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ecc.Data
public import KAM.EffectiveStability.Tube.Poly.Center

/-!
# The shift `B` of the SJSU tube (T2-CONF, N5a)

`sjsuB φ = Ī + ∂_θ S(φ)` is N6's tube centre `tubeCenter sjsuEccModes sjsuEccIbar` (the literal
`σ`, `Ī` of `.drafts/g2/data/literal-v1.json`). It satisfies N2's symmetry hypothesis
(`sjsuB_symm`), is smooth (`contDiff_sjsuB`) and `2π`-periodic in each reduced angle
(`sjsuB_add_two_pi`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube Real

/-- The tube centre `B(φ) = Ī + ∂_θ S(φ)` of the SJSU tube. -/
def sjsuB (φ : Fin 2 → ℝ) : Fin 3 → ℝ := fun k => tubeCenter sjsuEccModes sjsuEccIbar k φ

/-- `B = Ī + ∂_θ S` with `S = -Σ σ sin(m·φ)`. -/
theorem sjsuB_eq_gradient :
    sjsuB = fun φ k => (sjsuEccIbar k : ℝ) +
      fderiv ℝ (gradPot sjsuEccModes) φ (phiOf (Pi.single k 1)) :=
  tubeCenter_eq_gradient sjsuEccModes sjsuEccIbar

/-- **N2's symmetry hypothesis** `∂_{θ_i} B_l = ∂_{θ_l} B_i` for the SJSU shift. -/
theorem sjsuB_symm (φ : Fin 2 → ℝ) (i l : Fin 3) :
    fderiv ℝ sjsuB φ (phiOf (Pi.single i 1)) l = fderiv ℝ sjsuB φ (phiOf (Pi.single l 1)) i :=
  tubeCenter_symm sjsuEccModes sjsuEccIbar φ i l

theorem contDiff_sjsuB {n : WithTop ℕ∞} : ContDiff ℝ n sjsuB :=
  contDiff_tubeCenter_pi sjsuEccModes sjsuEccIbar

theorem sjsuB_add_two_pi (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ) :
    sjsuB (φ + fun a => 2 * π * m a) = sjsuB φ :=
  tubeCenter_add_two_pi sjsuEccModes sjsuEccIbar φ m

end KAM.EffectiveStability.SJSU

end
