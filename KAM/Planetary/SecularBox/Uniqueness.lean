/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Uniqueness
public import KAM.Planetary.SecularBox.Field

/-!
# Uniqueness for the secular Hamiltonian system

Blueprint `bpP:p14:sb-unique` (steps `sb-un-1`..`sb-un-3`).

* `sb_unique`: a competing Hamiltonian solution `v` on an open interval `U ∋ 0`, with the same
  initial value as a global solution `w` in `S`, equals `w` on `U`. Regularity of `v` is not
  assumed: the agreement set is relatively closed by continuity and open by local uniqueness
  inside the open set `S` (`sb-un-1`, `sb-un-2`), hence everything by connectedness (`sb-un-3`).
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff
open KAM.Kepler

namespace KAM.Planetary

/-- Local uniqueness (`sb-un-1`, `sb-un-2`): agreement at `s ∈ U` propagates to a neighbourhood. -/
private theorem sbUnique_local (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w : ℝ → Phase (2+2)}
    (hw : KAM.Iso.IsHamiltonianSolutionOn
      (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) univ univ w)
    (hW : ∀ t, w t ∈ sb_sdef saturn) {U : Set ℝ} (hU : IsOpen U) {v : ℝ → Phase (2+2)}
    (hv : KAM.Iso.IsHamiltonianSolutionOn
      (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) univ U v)
    {s : ℝ} (hsU : s ∈ U) (hvs : v s = w s) :
    ∃ ε > 0, Metric.ball s ε ⊆ U ∧ EqOn v w (Metric.ball s ε) := by
  have hvc : ContinuousAt v s := (hv s hsU).2.2.continuousAt
  have hev : ∀ᶠ x in nhds s, x ∈ U ∧ v x ∈ sb_sdef saturn :=
    Filter.Eventually.and (hU.mem_nhds hsU)
      (hvc.eventually_mem ((sb_s saturn hs).1.mem_nhds (hvs ▸ hW s)))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hJ : (Metric.ball s ε).OrdConnected := by
    rw [Real.ball_eq_Ioo]; exact ordConnected_Ioo
  have h1 : KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField
      (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu)) (sb_sdef saturn)
      (Metric.ball s ε) v :=
    (sb_pred saturn mu hs _ v fun t ht => (hball t ht).2).1 fun t ht => hv t (hball t ht).1
  have h2 : KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField
      (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu)) (sb_sdef saturn)
      (Metric.ball s ε) w :=
    (sb_pred saturn mu hs _ w fun t _ => hW t).1 fun t _ => hw t (mem_univ t)
  exact ⟨ε, hε, fun x hx => (hball x hx).1,
    KAM.ODE.gen_uniqueness (sb_s saturn hs).1 (sb_regular saturn mu hs).2 hJ
      (Metric.mem_ball_self hε) h1 h2 hvs⟩

/-- Stronger uniqueness: regularity of the competing curve is unnecessary. -/
theorem sb_unique (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w : ℝ → Phase (2+2)}
    (hw : KAM.Iso.IsHamiltonianSolutionOn
      (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) univ univ w)
    (hW : ∀ t, w t ∈ sb_sdef saturn)
    {U : Set ℝ} (hU : IsOpen U) (hUc : Convex ℝ U) (h0 : (0 : ℝ) ∈ U)
    {v : ℝ → Phase (2+2)} (hv0 : v 0 = w 0)
    (hv : KAM.Iso.IsHamiltonianSolutionOn
      (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) univ U v) :
    ∀ t ∈ U, v t = w t := by
  set A : Set ℝ := {t | t ∈ U ∧ v t = w t} with hA
  have key : ∀ s ∈ A, s ∈ interior A := fun s hsA => by
    obtain ⟨ε, hε, hball, heq⟩ := sbUnique_local saturn mu hs hw hW hU hv hsA.1 hsA.2
    exact interior_maximal (t := Metric.ball s ε)
      (fun x (hx : x ∈ Metric.ball s ε) => (⟨hball hx, heq hx⟩ : x ∈ A)) Metric.isOpen_ball
      (Metric.mem_ball_self hε)
  have hcl : closure (interior A) ∩ U ⊆ interior A := by
    rintro t ⟨htc, htU⟩
    have hvt : ContinuousAt v t := (hv t htU).2.2.continuousAt
    have hwt : ContinuousAt w t := (hw t (mem_univ t)).2.2.continuousAt
    suffices hvw : v t = w t from key t ⟨htU, hvw⟩
    by_contra hne
    have hopen : {p : Phase (2+2) × Phase (2+2) | p.1 ≠ p.2} ∈ nhds (v t, w t) :=
      (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hne
    have hev : ∀ᶠ x in nhds t, v x ≠ w x := (hvt.prodMk hwt).eventually hopen
    obtain ⟨x, hx1, hx2⟩ := mem_closure_iff_nhds.1 htc _ hev
    exact hx1 (interior_subset hx2).2
  have := hUc.isPreconnected.subset_of_closure_inter_subset isOpen_interior
    (⟨0, h0, key 0 ⟨h0, hv0⟩⟩ : (U ∩ interior A).Nonempty) hcl
  exact fun t ht => (interior_subset (this ht)).2

end KAM.Planetary

end
