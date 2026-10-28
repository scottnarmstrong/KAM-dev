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

Local form (`compact_max_on`): joint continuity on `[0, T] × S` gives continuity on `S`.
Variable-time form (`compact_max_variable`): on a domain `D` with `(t, x) ∈ D, t ≥ 0` implying
`(v t, x) ∈ D` for `v ∈ [0, 1]`, `(t, x) ↦ sup_{0 ≤ u ≤ t} g u x` is continuous on `D ∩ {t ≥ 0}`;
`image_Icc_mul` is the reparameterization `u = v t` of the time images.
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

theorem compact_max_on {X : Type*} [TopologicalSpace X] {T : ℝ} (hT : 0 ≤ T)
    {S : Set X} {g : ℝ → X → ℝ} (hg : ContinuousOn (fun p : ℝ × X => g p.1 p.2)
      (Icc 0 T ×ˢ S)) :
    ContinuousOn (fun x => sSup ((fun t => g t x) '' Icc 0 T)) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hmap : Continuous (fun p : ℝ × S => (p.1, (p.2 : X))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hg' : ContinuousOn (fun p : ℝ × S => g p.1 (p.2 : X)) (Icc 0 T ×ˢ univ) :=
    hg.comp hmap.continuousOn fun p hp => ⟨hp.1, p.2.2⟩
  exact compact_max (g := fun t (s : S) => g t (s : X)) hT hg'

theorem image_Icc_mul {t : ℝ} (ht : 0 ≤ t) (f : ℝ → ℝ) :
    f '' Icc 0 t = (fun v => f (v * t)) '' Icc 0 1 := by
  ext y
  constructor
  · rintro ⟨u, ⟨hu0, hut⟩, rfl⟩
    rcases ht.eq_or_lt with rfl | htp
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [le_antisymm hut hu0]⟩
    · exact ⟨u / t, ⟨div_nonneg hu0 ht, (div_le_one htp).2 hut⟩, by field_simp⟩
  · rintro ⟨v, ⟨hv0, hv1⟩, rfl⟩
    exact ⟨v * t, ⟨mul_nonneg hv0 ht, by nlinarith⟩, rfl⟩

theorem compact_max_variable {X : Type*} [TopologicalSpace X] {D : Set (ℝ × X)}
    {g : ℝ → X → ℝ}
    (hg : ContinuousOn (fun p : ℝ × X => g p.1 p.2) {p | p ∈ D ∧ 0 ≤ p.1})
    (hD : ∀ p ∈ D, 0 ≤ p.1 → ∀ v ∈ Icc (0 : ℝ) 1, (v * p.1, p.2) ∈ D) :
    ContinuousOn (fun p : ℝ × X => sSup ((fun u => g u p.2) '' Icc 0 p.1))
      {p | p ∈ D ∧ 0 ≤ p.1} := by
  have hmap : Continuous (fun q : ℝ × (ℝ × X) => (q.1 * q.2.1, q.2.2)) :=
    ((continuous_fst.mul (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd)
  have hg' : ContinuousOn (fun q : ℝ × (ℝ × X) => g (q.1 * q.2.1) q.2.2)
      (Icc 0 1 ×ˢ {p | p ∈ D ∧ 0 ≤ p.1}) := by
    refine hg.comp hmap.continuousOn fun q hq => ⟨hD _ hq.2.1 hq.2.2 _ hq.1, ?_⟩
    exact mul_nonneg hq.1.1 hq.2.2
  refine (compact_max_on (g := fun v (p : ℝ × X) => g (v * p.1) p.2) zero_le_one
    hg').congr fun p hp => ?_
  simp only
  rw [image_Icc_mul hp.2 (fun u => g u p.2)]

end KAM.Nekhoroshev
