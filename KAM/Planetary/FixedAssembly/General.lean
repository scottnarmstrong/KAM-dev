/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Working
public import KAM.Planetary.Newtonian.Assembly
public import KAM.Planetary.Preparation.Wrapper

/-!
# Fixed assembly: the general-dimension route (Part 13)

`bpP:p13:n-general` (`stepP:p13:ng-const`, `ng-wrap`, `ng-phys`), in parametric form: the
signed `KAM.Planetary.wrapper` enters as the single hypothesis `hw`, exactly its statement
universally quantified over `n` and the physical data. The threshold is taken from `hw` before
epsilon; at each epsilon the set, its volume and torus witnesses are kept, and
`fixedKolmogorovSet_of_tube` is applied at `gamma = axisGap a`, `A = axisMax a`.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Planetary

open KAM KAM.Kepler

namespace FixedAssembly

/-- bpP:p13:n-general, conditional on the signed wrapper `hw` (its statement verbatim). -/
theorem n_general_of_wrapper {n : ℕ}
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
    let d := tubeD (axisGap a)
    let D := tubeBigD (axisGap a) (axisMax a)
    ∃ eps0 : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S := by
  intro d D
  have hn0 : 0 < n := by omega
  have hinj : Function.Injective a := fun i j h => by
    by_contra hij
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact (hsep i j h').ne h
    · exact (hsep j i h').ne h.symm
  have hax := axisData_canonical hn0 ha hinj
  let P : P11Physical n :=
    ⟨G, m0, m, a, eta, hn, hG, hm0, hm, ha, fun _ _ h => hsep _ _ h, heta⟩
  obtain ⟨eps0, he0, hmain⟩ := hw P
  refine ⟨eps0, he0, ?_, tubeD_lt_tubeBigD hax hn0, fun eps hε hεt => ?_⟩
  · have := hax.gap_pos
    simp only [d, tubeD]; positivity
  obtain ⟨S, hSm, hpos, hfin, hSt, hS2⟩ := hmain eps hε hεt
  refine ⟨S, hpos, hfin, fixedKolmogorovSet_of_tube hax heta hn0 hG hm0 hm hSm hSt
    fun z hz => ?_⟩
  obtain ⟨w, K, θ, hz, hK, hT⟩ := hS2 z hz
  exact ⟨w, K, θ, hz.symm, hK, hT⟩

/-- **Signed `n_general`** (bpP:p13:n-general): `n_general_of_wrapper` applied to the
signed `wrapper`
(ruling OVERNIGHT 03:50). -/
theorem n_general {n : ℕ} (hn : 2 ≤ n)
    (G m0 : ℝ) (m a : Fin n → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : ∀ i j, i < j → a i < a j)
    (eta : ℝ) (heta : 0 < eta) :
    let d := tubeD (axisGap a)
    let D := tubeBigD (axisGap a) (axisMax a)
    ∃ eps0 : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S :=
  n_general_of_wrapper (fun D => KAM.Planetary.wrapper D) hn G m0 m a hG hm0 hm ha hsep eta heta

end FixedAssembly

end KAM.Planetary

end
