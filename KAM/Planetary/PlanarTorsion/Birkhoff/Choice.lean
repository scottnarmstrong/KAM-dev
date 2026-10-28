/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff.Jets
public import KAM.Planetary.PlanarTorsion.Birkhoff.Defs

/-!
# Planar quartic torsion: the action neighbourhoods of the Birkhoff map (package T16)

Blueprint P, Part 11b (`stepP:p11b:bt-nf`).  The good axis set `{a ∈ p11c_axes | p11c_phi4 p a ≠ 0}`
is open (`p11c_phi4` is continuous on the axis cone), and `p11c_phi4 p a ≠ 0` gives the
nonresonance `p11c_NR4` of the frequency `2σ`.  `p11cB_O p Kc ε` is the open set of positive
actions whose axes lie in the `ε`-thickening of the compact axis set `Kc`; its closure is compact
and lies in the action image of the closed thickening.
-/

@[expose] public noncomputable section

open Set Metric Real Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler

theorem p11cB_phi4_continuousAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) : ContinuousAt (p11c_phi4 p) a := by
  unfold p11c_phi4
  refine continuousAt_finset_prod _ fun k _ => ?_
  refine continuousAt_finset_sum _ fun i _ => ?_
  exact continuousAt_const.mul (p11cB_sigma_analyticAt p hp ha i).continuousAt

/-- The good axis set is open. -/
theorem p11cB_goodA_isOpen (p : PlanarData) (hp : p.Valid) :
    IsOpen {a ∈ p11c_axes | p11c_phi4 p a ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  have h1 : ∀ᶠ b in 𝓝 a, b ∈ p11c_axes := p11c_axes_isOpen.mem_nhds ha.1
  have h2 : ∀ᶠ b in 𝓝 a, p11c_phi4 p b ≠ 0 :=
    (p11cB_phi4_continuousAt p hp ha.1).eventually_ne ha.2
  exact h1.and h2

/-- `p11c_phi4 ≠ 0` gives the nonresonance of the frequency `2σ`. -/
theorem p11cB_NR4 (p : PlanarData) {O : Set (Fin 2 → ℝ)}
    (hO : ∀ I ∈ O, p11c_phi4 p (p.axes I) ≠ 0) : p11c_NR4 O (p11cB_freq p) := by
  intro I hI k hk hk4
  have hphi := hO I hI
  have hbd : ∀ i, |(k i : ℝ)| ≤ 4 := by
    intro i
    have h0 : ∀ j, 0 ≤ |(k j : ℝ)| := fun j => abs_nonneg _
    have : |(k i : ℝ)| ≤ ∑ j, |(k j : ℝ)| :=
      Finset.single_le_sum (f := fun j => |(k j : ℝ)|) (fun j _ => h0 j) (Finset.mem_univ i)
    linarith
  have hbdz : ∀ i, -4 ≤ k i ∧ k i ≤ 4 := by
    intro i
    have := abs_le.1 (hbd i)
    constructor <;> [have := this.1; have := this.2] <;> exact_mod_cast ‹_›
  let k' : Fin 2 → Fin 9 := fun i => ⟨(k i + 4).toNat, by have := hbdz i; omega⟩
  have hk'v : ∀ i, ((k' i).val : ℤ) - 4 = k i := by
    intro i
    have := hbdz i
    simp only [k']
    omega
  have hmem : k' ∈ (Finset.univ : Finset (Fin 2 → Fin 9)).filter
      (fun k => 0 < (∑ i, |((k i).val : ℤ) - 4|) ∧ (∑ i, |((k i).val : ℤ) - 4|) ≤ 4) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hk'v]
    constructor
    · by_contra hcon
      push Not at hcon
      apply hk
      funext i
      have h0 : ∀ j, 0 ≤ |k j| := fun j => abs_nonneg _
      have : ∑ j, |k j| = 0 := le_antisymm hcon (Finset.sum_nonneg fun j _ => h0 j)
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => h0 j).1 this i (Finset.mem_univ i)
      simpa using this
    · have : ((∑ i, |k i| : ℤ) : ℝ) = ∑ i, |(k i : ℝ)| := by push_cast; rfl
      have h2 : ((∑ i, |k i| : ℤ) : ℝ) ≤ 4 := by rw [this]; exact hk4
      exact_mod_cast h2
  have hne : (∑ i, (((k' i).val : ℝ) - 4) * p11c_sigma p (p.axes I) i) ≠ 0 := by
    unfold p11c_phi4 at hphi
    exact (Finset.prod_ne_zero_iff.1 hphi) k' hmem
  have hcast : ∀ i, (((k' i).val : ℝ) - 4) = (k i : ℝ) := by
    intro i
    have := hk'v i
    exact_mod_cast this
  simp only [hcast] at hne
  simp only [p11cB_freq]
  intro h0
  apply hne
  have : ∑ i, (k i : ℝ) * (2 * p11c_sigma p (p.axes I) i) =
      2 * ∑ i, (k i : ℝ) * p11c_sigma p (p.axes I) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this] at h0
  linarith

/-- Positive actions whose axes lie in the `ε`-thickening of `Kc`. -/
def p11cB_O (p : PlanarData) (Kc : Set (Fin 2 → ℝ)) (ε : ℝ) : Set (Fin 2 → ℝ) :=
  {I | (∀ i, 0 < I i) ∧ p.axes I ∈ thickening ε Kc}

theorem p11cB_O_isOpen (p : PlanarData) (Kc : Set (Fin 2 → ℝ)) (ε : ℝ) :
    IsOpen (p11cB_O p Kc ε) := by
  have hax : Continuous p.axes := by
    refine continuous_pi fun i => ?_
    unfold PlanarData.axes
    fun_prop
  have h1 : IsOpen {I : Fin 2 → ℝ | ∀ i, 0 < I i} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  exact h1.inter (isOpen_thickening.preimage hax)

theorem p11cB_O_mono (p : PlanarData) (Kc : Set (Fin 2 → ℝ)) {ε ε' : ℝ} (h : ε ≤ ε') :
    p11cB_O p Kc ε ⊆ p11cB_O p Kc ε' :=
  fun _ hI => ⟨hI.1, thickening_mono h Kc hI.2⟩

theorem p11cB_actions_mem_O (p : PlanarData) (hp : p.Valid) {Kc : Set (Fin 2 → ℝ)}
    (hKax : Kc ⊆ p11c_axes) {ε : ℝ} (hε : 0 < ε) {a : Fin 2 → ℝ} (ha : a ∈ Kc) :
    p.actions a ∈ p11cB_O p Kc ε := by
  have hpos : ∀ i, 0 < p.actions a i := by
    intro i
    have ha0 : 0 < a i := by
      fin_cases i
      · exact (hKax ha).1
      · exact (hKax ha).1.trans (hKax ha).2
    have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
    unfold PlanarData.actions
    have := hp.2.2 i
    positivity
  have hax : p.axes (p.actions a) = a := by
    funext i
    have hm := hp.2.2 i
    have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
    have ha0 : 0 < a i := by
      fin_cases i
      · exact (hKax ha).1
      · exact (hKax ha).1.trans (hKax ha).2
    unfold PlanarData.axes PlanarData.actions
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  exact ⟨hpos, by rw [hax]; exact self_subset_thickening hε Kc ha⟩

theorem p11cB_O_closure (p : PlanarData) (hp : p.Valid) {Kc : Set (Fin 2 → ℝ)}
    (hK : IsCompact Kc) {ε : ℝ} (hε : 0 < ε) (hsub : cthickening ε Kc ⊆ p11c_axes) :
    IsCompact (p.actions '' cthickening ε Kc) ∧
      closure (p11cB_O p Kc ε) ⊆ p.actions '' cthickening ε Kc := by
  have hcont : Continuous p.actions := by
    refine continuous_pi fun i => ?_
    unfold PlanarData.actions
    fun_prop
  have hc : IsCompact (p.actions '' cthickening ε Kc) := (hK.cthickening).image hcont
  refine ⟨hc, closure_minimal ?_ hc.isClosed⟩
  intro I hI
  have hax : p.actions (p.axes I) = I := by
    funext i
    have hm := hp.2.2 i
    have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
    have hi := hI.1 i
    unfold PlanarData.axes PlanarData.actions
    have : p.kappa * (I i ^ 2 / (p.m i ^ 2 * p.kappa)) = (I i / p.m i) ^ 2 := by
      field_simp
    rw [this, Real.sqrt_sq (by positivity)]
    field_simp
  exact ⟨p.axes I, thickening_subset_cthickening ε Kc hI.2, hax⟩

end KAM.Planetary

end
