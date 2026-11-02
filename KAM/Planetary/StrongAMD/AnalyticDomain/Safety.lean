/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.AnalyticDomain.Core
public import KAM.Planetary.StrongAMD.Geometry

/-!
# Safety of the sharp core

Source: `LP:MAIN L8 (251–252)`, track LP, non-frozen.

* D3 `strongCore_barrierState`: for `w` in the sharp core, `poincareProd ν 1 w` is a
  `BarrierState ν U (3δ/16)` with `U = cthickening (4 r_g) L_δ`.
* D3 `strongCore_subset_chartSafe`: hence the core lies in `chartSafe ν` (the compact
  collision-free set of `exists_barrierCompact`).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Metric

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

/-- D3 (`LP:MAIN L8 (251–252)`): core points are barrier states with margin `3δ/16`. -/
theorem strongCore_barrierState (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hg : IsSharedTube ν L δ r)
    (hδ : 0 < δ) {w : Phase (n + n)} (hw : w ∈ strongCore ν L δ r) :
    BarrierState ν (sharedTube ν L δ r) (3 * δ / 16) (poincareProd ν 1 w) := by
  have hdom : w ∈ poincareProdDom n := strongCore_subset_dom hν hn hg hδ hw
  obtain ⟨hI, hamd⟩ := strongCore_margin hν hn hg hw
  have hpro := (sec_domain_chart_facts hν hdom).1
  have hact : actionVector ν (poincareProd ν 1 w) = fast w.2 := by
    funext i
    exact lpChart_action hν hdom i
  refine ⟨fun i => ⟨(hpro i).2.1, (hpro i).2.2.1⟩, by rw [hact]; exact hI, ?_⟩
  rw [hact, lpChart_strongAMD hν hdom]
  exact hamd

/-- D3: the sharp core lies in the collision-free chart domain `chartSafe ν`. -/
theorem strongCore_subset_chartSafe (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) : strongCore ν L δ r ⊆ chartSafe ν := by
  obtain ⟨K, -, hKsub, hbar⟩ := exists_barrierCompact hν hn hg.compact hg.subset_chamber
    (m := 3 * δ / 16) (by positivity)
  intro w hw
  exact ⟨strongCore_subset_dom hν hn hg hδ hw,
    hKsub (hbar _ (strongCore_barrierState hν hn hg hδ hw))⟩

end KAM.Planetary.StrongAMD

end
