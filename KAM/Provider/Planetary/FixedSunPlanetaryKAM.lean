/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.FixedKolmogorovSet
public import KAM.Planetary.FixedAssembly.Main

/-!
# Provider for the frozen theorem `KAM.Planetary.fixedSunPlanetaryKAM`

The proof of `KAM.Planetary.fixedSunPlanetaryKAM` is assembled here as
`KAM.Provider.Planetary.fixedSunPlanetaryKAM`, from graph predecessors and approved external inputs
only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other than the
anchor may import it.

Until the signed wrapper is proved, the parametric form `fixedSunPlanetaryKAM_of_wrapper` is
provided; it takes the wrapper's statement as its single hypothesis `hw`.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Provider.Planetary

open KAM.Planetary

/-- The frozen anchor's statement, conditional on the signed wrapper `hw` (verbatim). -/
theorem fixedSunPlanetaryKAM_of_wrapper {n : ℕ}
    (hw : ∀ {n : ℕ} (D : P11Physical n),
      ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), MeasurableSet S ∧ 0 < volume S ∧ volume S < ⊤ ∧
          S ⊆ circularTube D.G D.m0 D.m D.a (p11Zeta D) ∧
          ∀ z ∈ S, ∃ w : P11Vec (n * 2), ∃ K : P11Vec (n * 2) → Phase (n * 2),
            ∃ theta0, z = K theta0 ∧ Set.range K ⊆ S ∧
              IsPhysicalTorus (fixedHamiltonian D.G D.m0 D.m eps) w K)
    (hn : 2 ≤ n)
    (G m0 : ℝ) (m a : Fin n → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : ∀ i j, i < j → a i < a j)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ eps0 d D : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S :=
  FixedAssembly.fixed_of_wrapper hw hn G m0 m a hG hm0 hm ha hsep eta heta

end KAM.Provider.Planetary

end
