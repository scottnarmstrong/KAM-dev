/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.ODE.NewtonReduction
public import KAM.ODE.Uniqueness

/-!
# Uniqueness of physical restricted solutions

Blueprint-I Part 8 (`bpI:p8:pf-uniq`).

* `KAM.Iso.R3bp.restricted_unique`: a restricted three-body solution `z` on all of `ℝ` and a
  restricted solution `y` on an interval `(a, b) ∋ 0` that agree at time `0` agree on `(a, b)`.
  There is no confinement hypothesis on the competitor `y`: `restricted_reduction` identifies both
  with solutions of the smooth collision-free field `restrictedField μ` on the open set
  `restrictedDomain μ`, and `gen_uniqueness` applies on the interval `(a, b)`.
-/

public section

open Set KAM.ODE

namespace KAM.Iso.R3bp

/-- `bpI:p8:pf-uniq`: uniqueness in the physical variables (`restricted_reduction` +
`gen_uniqueness` on `Ioo a b`); no confinement of the competitor. -/
theorem restricted_unique (μ : ℝ) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {y z : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)} (h0 : y 0 = z 0)
    (hy : IsRestrictedSolutionOn μ (Set.Ioo a b) y) (hz : IsRestrictedSolutionOn μ Set.univ z) :
    ∀ t ∈ Set.Ioo a b, y t = z t := by
  obtain ⟨hW, hF, hiff⟩ := restricted_reduction μ
  have hy' : IsSolutionIn (restrictedField μ) (restrictedDomain μ) (Set.Ioo a b) y :=
    (hiff _ y).1 hy
  have hz' : IsSolutionIn (restrictedField μ) (restrictedDomain μ) (Set.Ioo a b) z :=
    ((hiff _ z).1 hz).mono (Set.subset_univ _)
  exact fun t ht => gen_uniqueness hW (hF.of_le (by exact_mod_cast le_top))
    Set.ordConnected_Ioo (Set.mem_Ioo.2 ⟨ha, hb⟩) hy' hz' h0 ht

end KAM.Iso.R3bp
