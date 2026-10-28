/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Data

/-! # P11B continuous series on a compact carrier

Local bridge for the graph SOURCE_GAP `ps-lim`: a series of functions continuous on a subset with
summable scalar envelopes converges uniformly there, and its sum is continuous there.
-/

public section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

/-- Added local bridge for graph SOURCE_GAP ps-lim. Works on a real compact carrier. -/
theorem continuous_series_on_compact {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (K : Set (SelectionR n)) (v : ℕ → SelectionR n → E) (B : ℕ → ℝ)
    (hv : ∀ j, ContinuousOn (v j) K) (hB : Summable B)
    (hbound : ∀ j, ∀ b ∈ K, ‖v j b‖ ≤ B j) :
    TendstoUniformlyOn (fun m b => ∑ j ∈ Finset.range m, v j b)
      (fun b => ∑' j, v j b) atTop K ∧
    ContinuousOn (fun b => ∑' j, v j b) K ∧
    ∀ b ∈ K, Summable (fun j => v j b) :=
  ⟨tendstoUniformlyOn_tsum_nat hB hbound, continuousOn_tsum hv hB hbound,
    fun b hb => Summable.of_norm_bounded hB (fun j => hbound j b hb)⟩

end KAM.Planetary
