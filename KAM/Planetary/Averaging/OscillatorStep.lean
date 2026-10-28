/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorGen
public import KAM.Planetary.Averaging.OscillatorClassAlgebra
public import KAM.Planetary.Averaging.OscillatorFlowProps
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# P Part 2: the oscillator step (`bpP:p2:osc-iter`)

`oscStepMap` is the time-one map of the Hamiltonian flow of `oscGen` on the domain `𝒪`.
`osc_iter_core` proves every clause of `osc_iter` except the class, the weighted bound and the
reality of the new remainder `fp` (see the handoff: the Lie-series transfer is not yet done).
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-13.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

def oscStepMap {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S ρ ρp ρq σ K : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m)) : CPhase (n + m) → CPhase (n + m) :=
  flow (KAM.hamiltonianVectorFieldℂ (oscGen K h f)) (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) 1

section Core

variable {n m J : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ K α δ : ℝ}
  {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)}

/-- The flow hypotheses for the generator of the step. -/
theorem osc_flowHyp (hα : 0 < α) (hK : 0 ≤ K)
    (hwidths : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧
      0 < ρq ∧ 2 * ρq < rq ∧ 0 < σ ∧ 2 * σ < S)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hδ : oscBound D r rp rq S f δ)
    (hδpos : 0 ≤ δ) (hsmall : δ ≤ (2 * π * α) * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ)))) :
    OscFlowHyp D r rp rq S ρ ρp ρq σ (δ / (2 * π * α)) (oscGen K h f) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hwidths
  have hπ := Real.pi_pos
  have hS : 0 < S := by linarith
  obtain ⟨c1, c2⟩ := oscGen_class_bound hS hK hα hh hdiv hf hδ
  have hd : 0 < min (ρ * σ) (ρp * ρq) := lt_min (mul_pos h1 h7) (mul_pos h3 h5)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨h1, by linarith, h3, by linarith, h5, by linarith, h7, by linarith, c1, c2,
    div_nonneg hδpos (by positivity), ?_⟩
  rw [div_le_iff₀ hd, div_le_iff₀ (by positivity)]
  have h16 : (16 : ℝ) * (1 + m) ≥ 2 := by linarith
  have : (2 * π * α) * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))) ≤
      (2 * π * α) * min (ρ * σ) (ρp * ρq) / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) h16
  nlinarith

/-- Every clause of `osc_iter` except the class, the weighted bound and the reality of `fp`
(and the conditional reality clause, which mentions `fp`). Same hypotheses and `let`s. -/
theorem osc_iter_core {n m J : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ K α δ : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)} {gj : Fin J → CHam (n + m)}
    {rj rpj rqj Sj Mj : Fin J → ℝ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hα : 0 < α) (hK : 0 ≤ K)
    (hwidths : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧
      0 < ρq ∧ 2 * ρq < rq ∧ 0 < σ ∧ 2 * σ < S)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hδ : oscBound D r rp rq S f δ)
    (hδpos : 0 ≤ δ) (hsmall : δ ≤ (2 * π * α) * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))))
    (hg : ∀ j, oscClass D (rj j) (rpj j) (rqj j) (Sj j) (gj j) ∧
      oscBound D (rj j) (rpj j) (rqj j) (Sj j) (gj j) (Mj j) ∧
      r ≤ rj j ∧ rp ≤ rpj j ∧ rq ≤ rqj j ∧ S ≤ Sj j) :
    let Ψ := oscStepMap D r rp rq S ρ ρp ρq σ K h f
    let g := fun z => ∑ j, gj j z
    let gp := fun z => g z + coeff (oscFunction f) (oscPack z).2 0
    let fp := fun z => h (firstBlock (b := m) (Ψ z).2) + g (Ψ z) + f (Ψ z) -
      h (firstBlock (b := m) z.2) - gp z
    let d := min (ρ * σ) (ρp * ρq)
    let φ := oscGen K h f
    let O := oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
    let U := oscDom D (r - 3 * ρ / 2) (rp - 3 * ρp / 2)
      (rq - 3 * ρq / 2) (S - 3 * σ / 2)
    let u := δ / (2 * π * α * d)
    let V := oscDom D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
    oscClass D r rp rq S φ ∧
    oscBound D r rp rq S φ (δ / (2 * π * α)) ∧
    DifferentiableOn ℂ Ψ U ∧ MapsTo Ψ U O ∧ Set.InjOn Ψ V ∧
    (∀ z ∈ U, ∀ k : Fin n → ℤ,
      Ψ (z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) =
        Ψ z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) ∧
    (∀ z ∈ V, flow (KAM.hamiltonianVectorFieldℂ φ) O (-1) (Ψ z) = z) ∧
    oscClass D r rp rq S gp ∧
    oscBound D r rp rq S (fun z => gp z - g z) δ ∧
    (∀ z ∈ V, h (firstBlock (b := m) (Ψ z).2) + g (Ψ z) + f (Ψ z) =
      h (firstBlock (b := m) z.2) + gp z + fp z) ∧
    (∀ z ∈ U, oscGauge ρ ρp ρq σ (Ψ z - z) ≤ u) ∧
    (∀ z ∈ V, ∀ v,
      oscGauge ρ ρp ρq σ (fderiv ℂ Ψ z v - v) ≤
        2 * u * oscGauge ρ ρp ρq σ v) ∧
    (∀ z ∈ U, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
    (∀ z ∈ U,
      ‖firstBlock (b := m) ((Ψ z).1 - z.1)‖ ≤ δ / (2 * π * α * ρ) ∧
      ‖firstBlock (b := m) ((Ψ z).2 - z.2)‖ ≤ δ / (exp 1 * (2 * π * α) * σ) ∧
      ‖lastBlock (a := n) ((Ψ z).1 - z.1)‖ ≤ δ / (2 * π * α * ρp) ∧
      ‖lastBlock (a := n) ((Ψ z).2 - z.2)‖ ≤ δ / (2 * π * α * ρq)) := by
  intro Ψ g gp fp d φ O U u V
  have H := osc_flowHyp hα hK hwidths hh hdiv hf hδ hδpos hsmall
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hwidths
  have hπ := Real.pi_pos
  have hS : 0 < S := by linarith
  have hd : 0 < d := lt_min (mul_pos h1 h7) (mul_pos h3 h5)
  have hu : δ / (2 * π * α) / d = u := by
    show _ = δ / (2 * π * α * d)
    rw [div_div]
  obtain ⟨c1, c2⟩ := oscGen_class_bound hS hK hα hh hdiv hf hδ
  obtain ⟨z1, z2⟩ := oscZero_class_bound hS hK hα hh hdiv hf hδ
  have hgcl : ∀ j, oscClass D r rp rq S (gj j) := fun j =>
    (hg j).1.mono (hg j).2.2.1 (hg j).2.2.2.1 (hg j).2.2.2.2.1 (hg j).2.2.2.2.2
  have hgsum : oscClass D r rp rq S g := oscClass.sum hgcl
  have hgp : oscClass D r rp rq S gp := hgsum.add z1
  refine ⟨c1, c2, H.diff_flow, H.mapsTo_flow, H.injOn_flow, H.lattice_flow,
    H.inverse_flow, hgp, ?_, fun z _ => by simp only [fp]; ring, ?_, ?_, H.symplectic_flow, ?_⟩
  · refine oscBound.congr hS (fun z _ => ?_) z2
    simp only [gp, oscZero]
    ring
  · intro z hz
    rw [← hu]
    exact H.gauge_disp z hz
  · intro z hz v
    rw [← hu]
    exact H.gauge_fderiv z hz v
  · intro z hz
    obtain ⟨e1, e2, e3, e4⟩ := H.disp_components z hz
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [div_div] at e1; exact e1
    · have : δ / (2 * π * α) / (Real.exp 1 * σ) = δ / (Real.exp 1 * (2 * π * α) * σ) := by
        field_simp
      rw [this] at e2; exact e2
    · rw [div_div] at e3; exact e3
    · rw [div_div] at e4; exact e4

end Core

end KAM.Planetary

end
