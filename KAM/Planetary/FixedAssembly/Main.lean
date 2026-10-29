/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.FixedAssembly.General
public import KAM.Planetary.FixedAssembly.TwoPlanet

/-!
# Fixed assembly: the dimension split (Part 13)

`bpP:p13:fixed` (`stepP:p13:fx-split`, `fx-2`, `fx-n`), in parametric form with the signed
wrapper as the hypothesis `hw`. For `n = 2` the two-planet route `n2` is used after
substituting `n`; for `2 < n` the general route supplies `eps0` and the canonical
`tubeD (axisGap a)`, `tubeBigD (axisGap a) (axisMax a)` are packaged as the witnesses.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Planetary

open KAM KAM.Kepler

namespace FixedAssembly

/-- bpP:p13:fixed, conditional on the signed wrapper `hw` (its statement verbatim). -/
theorem fixed_of_wrapper {n : ℕ}
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
          FixedKolmogorovSet G m0 m a eps eta d D S := by
  rcases hn.eq_or_lt with rfl | hlt
  · exact n2 G m0 m a hG hm0 hm ha (hsep 0 1 (by decide)) eta heta
  · obtain ⟨eps0, he0, hd, hdD, h⟩ :=
      n_general_of_wrapper hw hn G m0 m a hG hm0 hm ha hsep eta heta
    exact ⟨eps0, _, _, he0, hd, hdD, h⟩

/-- **Signed `fixed`** (bpP:p13:fixed): `fixed_of_wrapper` applied to the signed `wrapper`
(ruling OVERNIGHT 03:50). -/
theorem fixed {n : ℕ} (hn : 2 ≤ n)
    (G m0 : ℝ) (m a : Fin n → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : ∀ i j, i < j → a i < a j)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ eps0 d D : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S :=
  fixed_of_wrapper (fun D => KAM.Planetary.wrapper D) hn G m0 m a hG hm0 hm ha hsep eta heta

end FixedAssembly

end KAM.Planetary

end
