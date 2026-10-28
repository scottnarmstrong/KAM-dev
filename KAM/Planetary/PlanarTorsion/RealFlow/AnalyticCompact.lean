/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Uniqueness
public import KAM.Planetary.PlanarTorsion.RealFlow.Analytic

/-!
# Planar quartic torsion: real analytic flow on a common neighbourhood (package R2)

Blueprint P, Part 11b (`bpP:p11b:e-ode`, package R2, design row R2 "real analytic parametric
Picard convergence on common neighbourhoods").  The local analytic flow of
`p11c_analytic_flow_fin` is glued over a finite subcover of a compact set `K ⊆ W`: one open
neighbourhood `U ⊇ K` and one time `T > 0` carry a single flow `Φ`, jointly real analytic on
`Ioo (-T) T ×ˢ U`.  Parameters are handled, as usual, by the augmented autonomous field on the
product of parameters and states, so that `K` ranges over initial data and parameters together.
The gluing uses ODE uniqueness (`KAM.ODE.gen_uniqueness`), since two local flows with the same
initial datum coincide.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology

namespace KAM.Planetary

variable {n : ℕ}

/-- `bpP:p11b:e-ode` (package R2), compact common neighbourhood: a real analytic vector field `f`
on an open `W ⊆ ℝⁿ` has, around every compact `K ⊆ W`, an open neighbourhood `U ⊆ W` and a time
`T > 0` with one flow `Φ`, jointly real analytic on `Ioo (-T) T ×ˢ U`, with `Φ 0 y = y` and
`t ↦ Φ t y` a solution in `W` on `Ioo (-T) T` for every `y ∈ U`. -/
theorem p11c_analytic_flow_compact_nbhd {f : (Fin n → ℝ) → Fin n → ℝ} {W : Set (Fin n → ℝ)}
    (hW : IsOpen W) (hf : AnalyticOnNhd ℝ f W) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKW : K ⊆ W) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ K ⊆ U ∧ U ⊆ W ∧ ∃ T : ℝ, 0 < T ∧
      ∃ Φ : ℝ → (Fin n → ℝ) → Fin n → ℝ,
        AnalyticOnNhd ℝ (fun u : ℝ × (Fin n → ℝ) => Φ u.1 u.2) (Ioo (-T) T ×ˢ U) ∧
        ∀ y ∈ U, Φ 0 y = y ∧ KAM.ODE.IsSolutionIn f W (Ioo (-T) T) (fun t => Φ t y) := by
  have hloc : ∀ x ∈ K, ∃ r T : ℝ, 0 < r ∧ 0 < T ∧ ∃ Φ : ℝ → (Fin n → ℝ) → Fin n → ℝ,
      AnalyticOnNhd ℝ (fun u : ℝ × (Fin n → ℝ) => Φ u.1 u.2) (Ioo (-T) T ×ˢ ball x r) ∧
      ∀ y ∈ ball x r, Φ 0 y = y ∧ KAM.ODE.IsSolutionIn f W (Ioo (-T) T) (fun t => Φ t y) :=
    fun x hx => p11c_analytic_flow_fin (hf x (hKW hx)) (hW.mem_nhds (hKW hx))
  choose! r T hr hT Φ hΦa hΦs using hloc
  obtain ⟨s, hsK, hcov⟩ := hK.elim_nhds_subcover (fun x => ball x (r x))
    (fun x hx => ball_mem_nhds x (hr x hx))
  have hTmin : ∀ s : Finset (Fin n → ℝ), (∀ x ∈ s, 0 < T x) →
      ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ x ∈ s, T₀ ≤ T x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨1, one_pos, by simp⟩
    | insert a s ha ih =>
      intro h
      obtain ⟨T₀, h0, hle⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
      refine ⟨min T₀ (T a), lt_min h0 (h a (Finset.mem_insert_self a s)), fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle x hx)
  obtain ⟨T₀, hT₀, hle⟩ := hTmin s fun x hx => hT x (hsK x hx)
  have hC1 : ContDiffOn ℝ 1 f W := (hf.contDiffOn hW.uniqueDiffOn).of_le (by norm_cast)
  set U : Set (Fin n → ℝ) := ⋃ x ∈ s, ball x (r x) with hU
  have hUo : IsOpen U := isOpen_biUnion fun x _ => isOpen_ball
  have hUW : U ⊆ W := by
    intro y hy
    simp only [hU, mem_iUnion] at hy
    obtain ⟨x, hx, hy⟩ := hy
    have := (hΦs x (hsK x hx) y hy).2 0 ⟨by linarith [hT x (hsK x hx)], hT x (hsK x hx)⟩
    have h0 := (hΦs x (hsK x hx) y hy).1
    simp only [h0] at this
    exact this.1
  -- two local flows through the same point agree on the common time interval
  have hagree : ∀ x ∈ s, ∀ x' ∈ s, ∀ y ∈ ball x (r x), y ∈ ball x' (r x') →
      ∀ t ∈ Ioo (-T₀) T₀, Φ x t y = Φ x' t y := by
    intro x hx x' hx' y hy hy' t ht
    have hi : ∀ z ∈ s, Ioo (-T₀) T₀ ⊆ Ioo (-T z) (T z) := fun z hz =>
      Ioo_subset_Ioo (neg_le_neg (hle z hz)) (hle z hz)
    refine KAM.ODE.gen_uniqueness hW hC1 ordConnected_Ioo (t₀ := 0)
      ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
      ((hΦs x (hsK x hx) y hy).2.mono (hi x hx)) ((hΦs x' (hsK x' hx') y hy').2.mono (hi x' hx'))
      (by rw [(hΦs x (hsK x hx) y hy).1, (hΦs x' (hsK x' hx') y hy').1]) ht
  classical
  let Ψ : ℝ → (Fin n → ℝ) → Fin n → ℝ := fun t y =>
    if h : ∃ x ∈ s, y ∈ ball x (r x) then Φ h.choose t y else y
  have hΨ : ∀ x ∈ s, ∀ y ∈ ball x (r x), ∀ t ∈ Ioo (-T₀) T₀, Ψ t y = Φ x t y := by
    intro x hx y hy t ht
    have h : ∃ x ∈ s, y ∈ ball x (r x) := ⟨x, hx, hy⟩
    simp only [Ψ, h, dite_true]
    exact hagree _ h.choose_spec.1 x hx y h.choose_spec.2 hy t ht
  refine ⟨U, hUo, fun y hy => ?_, hUW, T₀, hT₀, Ψ, ?_, fun y hy => ?_⟩
  · have := hcov hy
    simpa only [hU, mem_iUnion] using this
  · intro z hz
    have hzU := hz.2
    simp only [hU, mem_iUnion] at hzU
    obtain ⟨x, hx, hzx⟩ := hzU
    have hzT : z.1 ∈ Ioo (-T x) (T x) := ⟨by linarith [hz.1.1, hle x hx],
      by linarith [hz.1.2, hle x hx]⟩
    refine (hΦa x (hsK x hx) z ⟨hzT, hzx⟩).congr ?_
    have hnb : Ioo (-T₀) T₀ ×ˢ ball x (r x) ∈ 𝓝 z :=
      (isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨hz.1, hzx⟩
    filter_upwards [hnb] with w hw
    exact (hΨ x hx w.2 hw.2 w.1 hw.1).symm
  · simp only [hU, mem_iUnion] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    have hs' := hΦs x (hsK x hx) y hyx
    have hΨy : ∀ t ∈ Ioo (-T₀) T₀, Ψ t y = Φ x t y := hΨ x hx y hyx
    have h0 : (0 : ℝ) ∈ Ioo (-T₀) T₀ := ⟨by linarith, hT₀⟩
    refine ⟨by rw [hΨy 0 h0, hs'.1], fun t ht => ?_⟩
    have hmem : Ioo (-T₀) T₀ ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    have hti : t ∈ Ioo (-T x) (T x) := ⟨by linarith [ht.1, hle x hx], by linarith [ht.2, hle x hx]⟩
    obtain ⟨hm, hd⟩ := hs'.2 t hti
    show Ψ t y ∈ W ∧ HasDerivAt (fun t => Ψ t y) (f (Ψ t y)) t
    rw [hΨy t ht]
    refine ⟨hm, ?_⟩
    refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [hmem] with τ hτ using hΨy τ hτ
    · rfl

end KAM.Planetary
