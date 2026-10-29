/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarAssembly.Main

/-!
# Provider for the frozen theorem `KAM.Planetary.planarTwoPlanetKAM`

The proof of `KAM.Planetary.planarTwoPlanetKAM` is assembled here as
`KAM.Provider.Planetary.planarTwoPlanetKAM`, from graph predecessors and approved external inputs
only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other than the
anchor may import it.
-/

@[expose] public section

open MeasureTheory

namespace KAM.Provider.Planetary

theorem planarTwoPlanetKAM (G m0 : ℝ) (m a : Fin 2 → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : a 0 < a 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ mu0 d D : ℝ, 0 < mu0 ∧ 0 < d ∧ d < D ∧
      ∀ mu : ℝ, 0 < mu → mu < mu0 →
        ∃ S : Set (KAM.Planetary.Phase (2 * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          KAM.Planetary.MovingKolmogorovSet G m0 m a mu eta d D S :=
  KAM.Planetary.PlanarAssembly.planar G m0 m a hG hm0 hm ha hsep eta heta

end KAM.Provider.Planetary

end
