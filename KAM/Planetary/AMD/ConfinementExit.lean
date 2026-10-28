/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Exit

/-!
# AMD confinement: the first-exit argument

Blueprint `bpP:p14:amd` (steps `amd-fwd`, `amd-bwd`).  An abstract continuity argument: if a curve
starts in an open set `V`, a sequentially closed subset `C ⊆ V` (closed among limits in a "good"
set `N`) catches the curve at every time at which it has stayed in `V` so far, then the curve
stays in `C` for all forward times (`amd_exit_forward`) and all backward times
(`amd_exit_backward`).
-/

@[expose] public noncomputable section

open Set Filter Topology

namespace KAM.Planetary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forward first-exit argument. -/
theorem amd_exit_forward {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {y : ℝ → E}
    (hy : ContinuousOn y J) {V C N : Set E} (hV : IsOpen V) (hCV : C ⊆ V)
    (hclosed : ∀ (x : ℕ → E) (xs : E), (∀ k, x k ∈ C) → Tendsto x atTop (𝓝 xs) → xs ∈ N →
      xs ∈ C)
    (hN : ∀ t ∈ J, y t ∈ N) (hy0 : y 0 ∈ V)
    (hloc : ∀ s ∈ J, 0 ≤ s → (∀ t, 0 ≤ t → t ≤ s → y t ∈ V) → y s ∈ C) :
    ∀ t ∈ J, 0 ≤ t → y t ∈ C := by
  have hmain : ∀ t ∈ J, 0 ≤ t → y t ∈ V := by
    rcases KAM.ODE.gen_exit hJ h0 hy hV hy0 with ⟨-, h⟩ | ⟨-, ts, hts, hts0, htsJ, hbefore, -, -⟩
    · exact h
    · -- the exit time itself is a limit of earlier times, where `y` is in `C`
      exfalso
      have hbC : ∀ t ∈ Ico 0 ts, y t ∈ C := fun t ht =>
        hloc t (hJ.out h0 htsJ ⟨ht.1, ht.2.le⟩) ht.1 fun u hu0 hut =>
          hbefore u ⟨hu0, lt_of_le_of_lt hut ht.2⟩
      set x : ℕ → ℝ := fun k => ts - ts / (k + 2) with hx
      have hxmem : ∀ k, x k ∈ Ico 0 ts := fun k => by
        have : 0 < ts / (k + 2) := by positivity
        have h2 : ts / (k + 2) ≤ ts := div_le_self hts0.le
          (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
        exact ⟨by linarith, by linarith⟩
      have hlim : Tendsto x atTop (𝓝 ts) := by
        have h1 : Tendsto (fun k : ℕ => ts / ((k : ℝ) + 2)) atTop (𝓝 0) := by
          have := tendsto_const_div_atTop_nhds_zero_nat ts
          have h3 := (tendsto_add_atTop_iff_nat 2).2 this
          simpa [Nat.cast_add] using h3
        simpa [hx] using (tendsto_const_nhds (x := ts)).sub h1
      have hlimJ : Tendsto x atTop (𝓝[J] ts) :=
        tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k =>
          hJ.out h0 htsJ ⟨(hxmem k).1, (hxmem k).2.le⟩⟩
      have hyl : Tendsto (fun k => y (x k)) atTop (𝓝 (y ts)) :=
        (hy ts htsJ).tendsto.comp hlimJ
      have hts' : y ts ∈ C := hclosed _ _ (fun k => hbC _ (hxmem k)) hyl (hN ts htsJ)
      exact hts.1.2.2 (hCV hts')
  exact fun t ht ht0 => hloc t ht ht0 fun u hu0 hut =>
    hmain u (hJ.out h0 ht ⟨hu0, hut⟩) hu0

/-- Backward first-exit argument (time reversal of `amd_exit_forward`). -/
theorem amd_exit_backward {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {y : ℝ → E}
    (hy : ContinuousOn y J) {V C N : Set E} (hV : IsOpen V) (hCV : C ⊆ V)
    (hclosed : ∀ (x : ℕ → E) (xs : E), (∀ k, x k ∈ C) → Tendsto x atTop (𝓝 xs) → xs ∈ N →
      xs ∈ C)
    (hN : ∀ t ∈ J, y t ∈ N) (hy0 : y 0 ∈ V)
    (hloc : ∀ s ∈ J, s ≤ 0 → (∀ t, s ≤ t → t ≤ 0 → y t ∈ V) → y s ∈ C) :
    ∀ t ∈ J, t ≤ 0 → y t ∈ C := by
  have hJ' : (Neg.neg ⁻¹' J).OrdConnected := by
    refine ⟨fun a ha b hb u hu => ?_⟩
    have := hJ.out hb ha ⟨neg_le_neg hu.2, neg_le_neg hu.1⟩
    simpa using this
  have h := amd_exit_forward (y := fun t => y (-t)) hJ' (by simpa using h0)
    (hy.comp continuousOn_neg fun t ht => ht) hV hCV hclosed (fun t ht => hN _ ht)
    (by simpa using hy0) (fun s hs hs0 hV' => by
      have := hloc (-s) hs (by linarith) fun t ht1 ht2 => by
        simpa using hV' (-t) (by linarith) (by linarith)
      simpa using this)
  intro t ht ht0
  simpa using h (-t) (by simpa using ht) (by linarith)

end KAM.Planetary

end
