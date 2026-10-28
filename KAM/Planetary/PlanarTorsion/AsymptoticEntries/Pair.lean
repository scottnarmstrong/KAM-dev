/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.PairCoefficients

/-!
# Planar quartic torsion: big-O bookkeeping for the pair coefficients (P11C, package T18)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, steps `as-in`, `as-c`): the eight pair coefficients
`p11c_pairCoeffs a` agree with their explicit series jet `p11c_pairSeriesJet a` up to `O(a ^ 7)`
as `a → 0⁺` (`p11cAe_pair`), and the power-comparison helper `p11cAe_pow_isBigO` used throughout
the asymptotic package.
-/

@[expose] public noncomputable section
open Set Filter Asymptotics Real
open scoped Topology
namespace KAM.Planetary

/-- Power comparison on `(0, 1]`: a larger real exponent is smaller near `0⁺`. -/
theorem p11cAe_rpow_isBigO {r s : ℝ} (hrs : r ≤ s) :
    (fun a : ℝ => a ^ s) =O[𝓝[>] 0] fun a : ℝ => a ^ r := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with a ha
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ha.1.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg ha.1.le _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_ge ha.1 ha.2.le hrs

/-- A function analytic at `0` is bounded near `0`, so `a ^ m * h a = O(a ^ m)`. -/
theorem p11cAe_pow_mul_isBigO {m : ℕ} {h : ℝ → ℝ} (hh : AnalyticAt ℝ h 0) :
    (fun a : ℝ => a ^ m * h a) =O[𝓝[>] 0] fun a : ℝ => a ^ m := by
  have hb : h =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := hh.continuousAt.isBigO_one ℝ
  refine ((isBigO_refl (fun a : ℝ => a ^ m) _).mul (hb.mono nhdsWithin_le_nhds)).trans ?_
  simp only [mul_one]
  exact isBigO_refl _ _

/-- The pair coefficients agree with their series jet up to `O(a ^ 7)` as `a → 0⁺`. -/
theorem p11cAe_pair (i : Fin 8) :
    (fun a : ℝ => p11c_pairCoeffs a i - p11c_pairSeriesJet a i) =O[𝓝[>] 0] fun a : ℝ => a ^ 7 := by
  obtain ⟨h, hh, hfe⟩ := (p11c_comp_vanishes i).mono (p11cOrd_ge i)
  exact ((p11cAe_pow_mul_isBigO (m := 7) hh).congr' (hfe.filter_mono nhdsWithin_le_nhds).symm
    (Eventually.of_forall fun _ => rfl))

end KAM.Planetary

end
