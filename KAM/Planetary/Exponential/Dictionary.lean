/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.ProgradeElliptic
public import KAM.Frozen.Planetary.Defs.PhysicalAMD
public import KAM.Frozen.Planetary.Defs.KeplerAction
public import KAM.Frozen.Planetary.Defs.KeplerAxis
public import KAM.Planetary.Exponential.Setting
public import KAM.Planetary.Poincare.Product

/-!
# P14 package E1: the general-`n` chart dictionary

Blueprint P, Part 14 (`bpP:p14:sec-domain#chart-facts`): on the product chart domain the physical
point `poincareProd m 1 w` is prograde elliptic, its Kepler action, axis and angular momentum are
read off the chart coordinates, and the physical AMD equals `chartAMD w`.  The statement is proved
componentwise from `poincare_elements` (no `Fin 2` supplier is instantiated at general `n`).

The general-`n` onto bridge to the physical prograde region is `poincareProd_image_prograde`.
-/

@[expose] public noncomputable section

open KAM KAM.Kepler

namespace KAM.Planetary

variable {n : ℕ}

/-- Per-planet dictionary: the frozen Kepler quantities of the `i`-th body of `poincareProd m 1 w`
in terms of the `i`-th block of the chart coordinates. -/
theorem poincareProd_planet_facts {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) (i : Fin n) :
    keplerAction m (poincareProd m 1 w) i = fast w.2 i ∧
      keplerAxis m (poincareProd m 1 w) i = fast w.2 i ^ 2 / m i ^ 2 ∧
      planeCross (bodyVector (poincareProd m 1 w).1 i)
        (bodyVector (poincareProd m 1 w).2 i) =
        fast w.2 i - ((slow w.1 i) ^ 2 + (slow w.2 i) ^ 2) / 2 := by
  obtain ⟨-, hE, hax, hact, hcr, -⟩ := poincare_elements (hm i) one_pos (hw i)
  have hblock := poincareProd_block m 1 w i
  have hE' : keplerEnergy m (poincareProd m 1 w) i =
      energyMK (m i) 1 (poincare (m i) 1 (planetBlock w i)) := by
    rw [← hblock]; simp [keplerEnergy, energyMK]
  have hax' : keplerAxis m (poincareProd m 1 w) i = fast w.2 i ^ 2 / m i ^ 2 := by
    have h1 : keplerAxis m (poincareProd m 1 w) i =
        axisMK (m i) 1 (poincare (m i) 1 (planetBlock w i)) := by
      rw [keplerAxis, hE', axisMK]; simp
    rw [h1, hax]; simp [planetBlock, fast]
  refine ⟨?_, hax', ?_⟩
  · have h1 : keplerAction m (poincareProd m 1 w) i =
        actionMK (m i) 1 (poincare (m i) 1 (planetBlock w i)) := by
      rw [keplerAction, hax', actionMK, hax]; simp [planetBlock, fast]
    rw [h1, hact]; simp [planetBlock, fast]
  · have h1 := congrArg (fun p : Phase 2 => planeCross p.1 p.2) hblock
    simp only at h1
    rw [h1, hcr]
    simp [poincareGamma, planetBlock, fast, slow]

theorem sec_domain_chart_facts {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) :
    ProgradeElliptic m (poincareProd m 1 w) ∧
    (∀ i, keplerAction m (poincareProd m 1 w) i = fast w.2 i ∧
      keplerAxis m (poincareProd m 1 w) i = fast w.2 i ^ 2 / m i ^ 2 ∧
      planeCross (bodyVector (poincareProd m 1 w).1 i)
        (bodyVector (poincareProd m 1 w).2 i) =
        fast w.2 i - ((slow w.1 i)^2 + (slow w.2 i)^2) / 2) ∧
    physicalAMD m (poincareProd m 1 w) = chartAMD w := by
  refine ⟨(regionProd_one_iff hm _).1 (poincareProd_mem_regionProd hm one_pos hw),
    poincareProd_planet_facts hm hw, ?_⟩
  unfold physicalAMD totalMomentum chartAMD
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h1, -, h3⟩ := poincareProd_planet_facts hm hw i
  rw [h1, h3]; ring

/-- General-`n` onto bridge: the product chart maps its domain onto the physical prograde elliptic
region. -/
theorem poincareProd_image_prograde {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) :
    poincareProd m 1 '' poincareProdDom n = {z | ProgradeElliptic m z} := by
  rw [poincareProd_image hm one_pos]
  ext z
  exact regionProd_one_iff hm z

end KAM.Planetary

end
