/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorStep
public import KAM.Planetary.Averaging.OscillatorRemainder
public import KAM.Planetary.Averaging.OscillatorReality

/-!
# P Parts 2-3: the complete oscillator step (`bpP:p2:osc-iter`)

`osc_iter` is the full inherited oscillator step contract. It is assembled from `osc_iter_core`
(every clause except the class and the bound of `fp` and the conditional reality),
`osc_fp_class`, `osc_remainder_bound` and `osc_iter_reality`, all stated for the same maps
`Ψ`, `gp`, `fp`; the conjuncts are spliced in the order of the signed statement.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md` (Revision 3), package P23-13j.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- Full inherited oscillator step contract (audit 1 F1, Revision 2).
Finite source decomposition only; reality is a conditional conclusion. -/
theorem osc_iter {n m J : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ K α δ : ℝ}
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
    let Rsum := ∑ j, max (max (ρ / (rj j - r + ρ)) (σ / (Sj j - S + σ)))
      (max (ρp / (rpj j - rp + ρp)) (ρq / (rqj j - rq + ρq))) * Mj j
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
    oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) fp ∧
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) fp
      ((1 - 2 * exp 1 * (1 + (m : ℝ)) * δ / (2 * π * α * d))⁻¹ *
        (2 * (1 + (m : ℝ)) / (2 * π * α * d) * (Rsum + δ) + exp (-(2 * π * K * σ))) * δ) ∧
    (∀ z ∈ U,
      ‖firstBlock (b := m) ((Ψ z).1 - z.1)‖ ≤ δ / (2 * π * α * ρ) ∧
      ‖firstBlock (b := m) ((Ψ z).2 - z.2)‖ ≤ δ / (exp 1 * (2 * π * α) * σ) ∧
      ‖lastBlock (a := n) ((Ψ z).1 - z.1)‖ ≤ δ / (2 * π * α * ρp) ∧
      ‖lastBlock (a := n) ((Ψ z).2 - z.2)‖ ≤ δ / (2 * π * α * ρq)) ∧
    (RealOn (oscDom D r rp rq S) (fun z => h (firstBlock (b := m) z.2)) →
      RealOn (oscDom D r rp rq S) g → RealOn (oscDom D r rp rq S) f →
      RealOn (oscDom D r rp rq S) φ ∧ RealOn (oscDom D r rp rq S) gp ∧
      RealOn V fp ∧
      ∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈ U →
        Ψ (KAM.realInclusion₂ (n + m) x) ∈ range (KAM.realInclusion₂ (n + m))) := by
  intro Ψ g gp fp d Rsum φ O U u V
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ :=
    osc_iter_core hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
  have b1 := osc_fp_class hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
  have b2 := osc_remainder_bound hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
  have b3 := osc_iter_reality hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, b1, b2, a14, b3⟩

end KAM.Planetary
