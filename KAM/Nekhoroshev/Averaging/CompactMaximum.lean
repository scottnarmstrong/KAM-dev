/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuity of a maximum over a compact time interval

Blueprint N Part 12 (`bpN:p12:ext-markov#compact-max`): if `(t, x) ↦ g t x` is jointly continuous on
`[0, T] × X`, then `x ↦ sup_{t ∈ [0, T]} g t x` is continuous. The case `T = 0` is allowed.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Nekhoroshev

theorem compact_max {X : Type*} [TopologicalSpace X] {T : ℝ} (hT : 0 ≤ T)
    {g : ℝ → X → ℝ} (hg : ContinuousOn (fun p : ℝ × X => g p.1 p.2)
      (Icc 0 T ×ˢ univ)) :
    Continuous (fun x => sSup ((fun t => g t x) '' Icc 0 T)) := by
  let G : X → Icc (0 : ℝ) T → ℝ := fun x t => g t x
  have hcont : Continuous (Function.uncurry G) := by
    have hmap : Continuous (fun p : X × Icc (0 : ℝ) T => ((p.2 : ℝ), p.1)) :=
      (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst
    refine (hg.comp_continuous hmap ?_)
    intro p
    exact ⟨p.2.2, mem_univ _⟩
  have hK : IsCompact (univ : Set (Icc (0 : ℝ) T)) := isCompact_univ
  have := IsCompact.continuous_sSup (f := G) hK hcont
  refine this.congr fun x => ?_
  congr 1
  ext y
  simp only [mem_image, mem_univ, true_and, G]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩

end KAM.Nekhoroshev
