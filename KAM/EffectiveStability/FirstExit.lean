/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.StoppedDrift
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# First exit from a box (track B)

A continuous vector observable `f` along an order-connected time set, whose drift is controlled by
`η` as long as it stays in the box `|f j| ≤ b j` (a *stopped* bound), and which starts in the
smaller box `|f 0 j| ≤ a j` with the strict margin `a j + T η j < b j`, never leaves the box on
`[-T, T]`, and drifts by at most `η j |t|`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set Filter Topology

variable {n : ℕ}

/-- One-sided (forward time) first exit. -/
theorem firstExit_box_nonneg {f : ℝ → Fin n → ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    (h0 : (0 : ℝ) ∈ J) (hcont : ContinuousOn f J) {a b η : Fin n → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hη : ∀ j, 0 ≤ η j) (hmargin : ∀ j, a j + T * η j < b j) (hf0 : ∀ j, |f 0 j| ≤ a j)
    (hstop : ∀ t ∈ J, 0 ≤ t → t ≤ T → (∀ u ∈ Icc 0 t, ∀ j, |f u j| ≤ b j) →
      ∀ j, |f t j - f 0 j| ≤ η j * t) :
    ∀ t ∈ J, 0 ≤ t → t ≤ T → ∀ j, |f t j - f 0 j| ≤ η j * t ∧ |f t j| ≤ a j + η j * T := by
  -- the key claim: confinement up to any admissible time
  have hdrift_le : ∀ t ∈ J, 0 ≤ t → t ≤ T → (∀ u ∈ Icc 0 t, ∀ j, |f u j| ≤ b j) →
      ∀ j, |f t j| < b j := fun t ht ht0 htT hc j => by
    have h1 := hstop t ht ht0 htT hc j
    have h2 : |f t j| ≤ |f 0 j| + |f t j - f 0 j| := by
      have := abs_add_le (f 0 j) (f t j - f 0 j); simpa using this
    have := hmargin j
    have h3 : η j * t ≤ T * η j := by nlinarith [hη j]
    linarith [hf0 j]
  have hconf : ∀ t₁ ∈ J, 0 ≤ t₁ → t₁ ≤ T → ∀ u ∈ Icc 0 t₁, ∀ j, |f u j| ≤ b j := by
    intro t₁ ht₁ ht₁0 ht₁T
    by_contra hbad
    have hIcc : Icc 0 t₁ ⊆ J := hJ.out h0 ht₁
    let A : Set ℝ := {t | t ∈ Icc 0 t₁ ∧ ∀ u ∈ Icc 0 t, ∀ j, |f u j| ≤ b j}
    have hA0 : (0 : ℝ) ∈ A := by
      refine ⟨⟨le_rfl, ht₁0⟩, fun u hu j => ?_⟩
      have : u = 0 := le_antisymm hu.2 hu.1
      subst this
      have := hmargin j
      have h3 : 0 ≤ T * η j := mul_nonneg hT (hη j)
      linarith [hf0 j]
    have hAne : A.Nonempty := ⟨0, hA0⟩
    have hAbdd : BddAbove A := ⟨t₁, fun t ht => ht.1.2⟩
    set s := sSup A with hs
    have hs0 : 0 ≤ s := le_csSup hAbdd hA0
    have hst₁ : s ≤ t₁ := csSup_le hAne fun t ht => ht.1.2
    have hsIcc : s ∈ Icc 0 t₁ := ⟨hs0, hst₁⟩
    -- confinement before s
    have hbefore : ∀ u, 0 ≤ u → u < s → ∀ j, |f u j| ≤ b j := by
      intro u hu0 hus j
      obtain ⟨t, htA, hut⟩ := exists_lt_of_lt_csSup hAne hus
      exact htA.2 u ⟨hu0, hut.le⟩ j
    -- confinement at s
    have hBd : ∀ u ∈ Icc 0 s, ∀ j, |f u j| ≤ b j := by
      intro u hu j
      rcases hu.2.lt_or_eq with hlt | heq
      · exact hbefore u hu.1 hlt j
      · have hut : u ≤ t₁ := heq ▸ hst₁
        rcases hu.1.lt_or_eq with hpos | hzero
        · have hclosed : IsClosed {x ∈ Icc 0 t₁ | |f x j| ≤ b j} := by
            have : {x ∈ Icc 0 t₁ | |f x j| ≤ b j} =
                Icc 0 t₁ ∩ (fun x => |f x j|) ⁻¹' Iic (b j) := by
              ext; simp
            rw [this]
            exact (((continuous_apply j).comp_continuousOn (hcont.mono hIcc)).abs
              ).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
          have hsub : Ico 0 u ⊆ {x ∈ Icc 0 t₁ | |f x j| ≤ b j} := fun x hx =>
            ⟨⟨hx.1, hx.2.le.trans hut⟩, hbefore x hx.1 (heq ▸ hx.2) j⟩
          have := hclosed.closure_subset_iff.2 hsub
          have hmem : u ∈ closure (Ico 0 u) := by rw [closure_Ico hpos.ne]; exact ⟨hpos.le, le_rfl⟩
          exact (this hmem).2
        · rw [← hzero]; exact (hA0.2 0 ⟨le_rfl, le_rfl⟩ j)
    have hsA : s ∈ A := ⟨hsIcc, hBd⟩
    have hsJ : s ∈ J := hIcc hsIcc
    have hsT : s ≤ T := hst₁.trans ht₁T
    have hlt := hdrift_le s hsJ hs0 hsT hBd
    rcases hst₁.lt_or_eq with hlt₁ | heq₁
    · -- extend past s
      have hcw : ContinuousWithinAt f (Icc s t₁) s :=
        (hcont s hsJ).mono (fun x hx => hIcc ⟨hs0.trans hx.1, hx.2⟩)
      have hev : ∀ᶠ x in 𝓝[Icc s t₁] s, ∀ j, |f x j| < b j := by
        rw [eventually_all]
        intro j
        have hc : ContinuousWithinAt (fun x => |f x j|) (Icc s t₁) s :=
          ((continuous_apply j).continuousAt.comp_continuousWithinAt hcw).abs
        exact hc.eventually (gt_mem_nhds (hlt j))
      rw [nhdsWithin_Icc_eq_nhdsGE hlt₁, Filter.Eventually, mem_nhdsGE_iff_exists_Ico_subset] at hev
      obtain ⟨u, hu, hsub⟩ := hev
      set x := (s + min u t₁) / 2 with hx
      have hmin : s < min u t₁ := lt_min hu hlt₁
      have hsx : s < x := by rw [hx]; linarith
      have hxm : x < min u t₁ := by rw [hx]; linarith
      have hxA : x ∈ A := by
        refine ⟨⟨hs0.trans hsx.le, (hxm.trans_le (min_le_right _ _)).le⟩, fun v hv j => ?_⟩
        rcases le_or_gt v s with hvs | hvs
        · exact hBd v ⟨hv.1, hvs⟩ j
        · exact (hsub ⟨hvs.le, lt_of_le_of_lt hv.2 (hxm.trans_le (min_le_left _ _))⟩ j).le
      exact absurd (le_csSup hAbdd hxA) (not_le.2 hsx)
    · exact hbad (heq₁ ▸ hBd)
  intro t ht ht0 htT j
  have hd := hstop t ht ht0 htT (hconf t ht ht0 htT) j
  refine ⟨hd, ?_⟩
  have h2 : |f t j| ≤ |f 0 j| + |f t j - f 0 j| := by
    have := abs_add_le (f 0 j) (f t j - f 0 j); simpa using this
  have : η j * t ≤ η j * T := mul_le_mul_of_nonneg_left htT (hη j)
  linarith [hf0 j]

/-- First exit, both time directions. -/
theorem firstExit_box {f : ℝ → Fin n → ℝ} {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    (hcont : ContinuousOn f J) {a b η : Fin n → ℝ} {T : ℝ} (hT : 0 ≤ T) (hη : ∀ j, 0 ≤ η j)
    (hmargin : ∀ j, a j + T * η j < b j) (hf0 : ∀ j, |f 0 j| ≤ a j)
    (hstop : ∀ t ∈ J, |t| ≤ T → (∀ u ∈ Set.uIcc 0 t, ∀ j, |f u j| ≤ b j) →
      ∀ j, |f t j - f 0 j| ≤ η j * |t|) :
    ∀ t ∈ J, |t| ≤ T → ∀ j, |f t j - f 0 j| ≤ η j * |t| ∧ |f t j| ≤ a j + η j * T := by
  intro t ht htT j
  rcases le_total 0 t with ht0 | ht0
  · have := firstExit_box_nonneg hJ h0 hcont hT hη hmargin hf0
      (fun t ht ht0 htT hc j => by
        have := hstop t ht (by rwa [abs_of_nonneg ht0]) (by rwa [uIcc_of_le ht0]) j
        rwa [abs_of_nonneg ht0] at this) t ht ht0 (by rwa [abs_of_nonneg ht0] at htT) j
    rwa [abs_of_nonneg ht0]
  · -- reflect time
    have hJ' : (Neg.neg ⁻¹' J).OrdConnected := hJ.preimage_anti (fun x y h => neg_le_neg h)
    have := firstExit_box_nonneg (f := fun s => f (-s)) (J := Neg.neg ⁻¹' J) hJ'
      (by simpa using h0) (hcont.comp continuousOn_neg (fun s hs => hs)) hT hη hmargin
      (by simpa using hf0)
      (fun t ht ht0 htT hc j => by
        have := hstop (-t) ht (by rwa [abs_neg, abs_of_nonneg ht0])
          (fun u hu => by
            rw [uIcc_of_ge (by linarith : -t ≤ 0)] at hu
            simpa using hc (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩) j
        simpa [abs_of_nonneg ht0] using this) (-t) (by simpa using ht) (by linarith)
      (by rwa [abs_of_nonpos ht0] at htT) j
    simpa [abs_of_nonpos ht0] using this

/-- First exit from derivative bounds. -/
theorem firstExit_box_of_deriv {f f' : ℝ → Fin n → ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    (h0 : (0 : ℝ) ∈ J) {a b η : Fin n → ℝ} {T : ℝ} (hT : 0 ≤ T) (hη : ∀ j, 0 ≤ η j)
    (hmargin : ∀ j, a j + T * η j < b j) (hf0 : ∀ j, |f 0 j| ≤ a j)
    (hderiv : ∀ t ∈ J, ∀ j, HasDerivAt (fun s => f s j) (f' t j) t)
    (hbound : ∀ t ∈ J, (∀ j, |f t j| ≤ b j) → ∀ j, |f' t j| ≤ η j) :
    ∀ t ∈ J, |t| ≤ T → ∀ j, |f t j - f 0 j| ≤ η j * |t| ∧ |f t j| ≤ a j + η j * T := by
  refine firstExit_box hJ h0
    (continuousOn_pi.2 fun j t ht => (hderiv t ht j).continuousAt.continuousWithinAt) hT hη hmargin
    hf0 (fun t ht _ hc j => ?_)
  refine abs_sub_le_of_deriv_bound (f := fun s => f s j) (f' := fun s => f' s j)
    (fun u hu => hderiv u (hJ.uIcc_subset h0 ht hu) j) (fun u hu => ?_)
  exact hbound u (hJ.uIcc_subset h0 ht hu) (fun i => hc u hu i) j

end KAM.EffectiveStability
