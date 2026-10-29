/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorCompositionIntegral
public import KAM.Planetary.Averaging.OscillatorRemainderData
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# P Parts 2-3: the weighted bound of the new oscillator remainder (`bpP:p2:osc-iter`)

`osc_remainder_bound`: the remainder `fp` of one oscillator step lies in the oscillator class on `V`
with the exact signed constant of `osc_iter`. The generator data are instantiated at
`Φ = δ / (2 π α)`; `osc_remainder_decomposition` writes `fp` as the integral of `v t` along the
flow plus `(f - T) ∘ Ψ`, `osc_composition_integral` bounds the integral and `osc_composition_t`
(at `t = 1`) bounds the tail composition, both with the factor `(1 - θ)⁻¹`. When the parameter
set of the target domain is empty the bound holds vacuously, so no positivity of the majorants
`Mj` is assumed.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md` (Revision 3), package P23-13h.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

set_option linter.unusedVariables false in
theorem osc_remainder_of_gen_bound {n m J : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ K α δ : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)} {gj : Fin J → CHam (n + m)}
    {rj rpj rqj Sj Mj : Fin J → ℝ} {Φ : ℝ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hα : 0 < α) (hK : 0 ≤ K)
    (hwidths : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧
      0 < ρq ∧ 2 * ρq < rq ∧ 0 < σ ∧ 2 * σ < S)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hδ : oscBound D r rp rq S f δ)
    (hδpos : 0 ≤ δ) (hsmall : δ ≤ (2 * π * α) * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))))
    (hc : oscClass D r rp rq S (oscGen K h f)) (hb : oscBound D r rp rq S (oscGen K h f) Φ)
    (hΦ : 0 ≤ Φ) (hΦδ : Φ ≤ δ / (2 * π * α))
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
    let O := oscDom (m := m) D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
    let U := oscDom (m := m) D (r - 3 * ρ / 2) (rp - 3 * ρp / 2)
      (rq - 3 * ρq / 2) (S - 3 * σ / 2)
    let u := δ / (2 * π * α * d)
    let V := oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) fp
      ((1 - oscTheta m Φ d)⁻¹ *
        (2 * (1 + (m : ℝ)) / (2 * π * α * d) * (Rsum + δ) + exp (-(2 * π * K * σ))) * δ) := by
  intro Ψ g gp fp d Rsum φ O U u V
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hwidths
  have hπ := Real.pi_pos
  have hS : 0 < S := by linarith
  have hS2 : 0 < S - 2 * σ := by linarith
  have hd : 0 < d := lt_min (mul_pos h1 h7) (mul_pos h3 h5)
  have hw : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧
      0 < ρq ∧ 2 * ρq < rq ∧ 0 < σ ∧ 2 * σ < S := ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨hdv1, hdv2, hdv3, hdv4⟩ := osc_remainder_decomposition hn hm hα hK hw hh hdiv hf hδ
    hδpos hsmall hg
  obtain ⟨t1, t2, t3⟩ := osc_truncation_tail hf hδ h7 (by linarith : σ < S) hK
  have hsm : Φ ≤ min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))) := by
    have hs := (le_div_iff₀ (by positivity)).1 hsmall
    refine hΦδ.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hs]
  have H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ := ⟨hn, hm, hw, hc, hb, hΦ, hsm⟩
  by_cases hne : (oscParams (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq)).Nonempty
  swap
  · intro x hx; exact absurd ⟨x, hx⟩ hne
  obtain ⟨x0, hx0⟩ := hne
  have hMj : ∀ j, 0 ≤ Mj j := fun j => osc_bound_nonneg (hg j).2.1
    (oscParams_mono (by linarith [(hg j).2.2.1]) (by linarith [(hg j).2.2.2.1])
      (by linarith [(hg j).2.2.2.2.1]) hx0)
  have hRsum : 0 ≤ Rsum := Finset.sum_nonneg fun j _ => mul_nonneg
    (((div_nonneg h1.le (by linarith [(hg j).2.2.1])).trans (le_max_left _ _)).trans
      (le_max_left _ _)) (hMj j)
  have hB : 0 ≤ 2 * (1 + (m : ℝ)) * (δ / (2 * π * α)) / d * (Rsum + δ) :=
    mul_nonneg (div_nonneg (by positivity) hd.le) (add_nonneg hRsum hδpos)
  obtain ⟨hRc, hRb⟩ := osc_composition_integral H hB hdv1 hdv2 hdv3
  -- the tail `(f - T) ∘ Ψ`
  have hTc : oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (fun z => f z - oscTruncate K f z) :=
    (hf.sub t1).mono (by linarith) (by linarith) (by linarith) (by linarith)
  have hTb : oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (fun z => f z - oscTruncate K f z)
      (exp (-(2 * π * K * σ)) * δ) := fun x hx =>
    t3 x (oscParams_mono (by linarith) (by linarith) (by linarith) hx)
  have hE0 : 0 ≤ exp (-(2 * π * K * σ)) * δ := mul_nonneg (exp_pos _).le hδpos
  obtain ⟨hCc, hCb⟩ := osc_composition_t H hTc hTb hE0 (t := 1) ⟨by norm_num, le_rfl⟩
  rw [abs_one, one_mul] at hCb
  have hsum := osc_bound_add hS2 hRc hCc hRb hCb
  refine oscBound.congr hS2 (fun z hz => ?_) (osc_bound_mono hsum ?_)
  · refine Eq.trans ?_ (hdv4 z hz).symm
    exact (add_sub_assoc _ _ _).symm
  · rw [← mul_add]
    refine le_of_eq ?_
    rw [mul_assoc ((1 - oscTheta m Φ d)⁻¹)]
    congr 1
    field_simp

set_option linter.unusedVariables false in
theorem osc_remainder_bound {n m J : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ K α δ : ℝ}
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
    let O := oscDom (m := m) D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
    let U := oscDom (m := m) D (r - 3 * ρ / 2) (rp - 3 * ρp / 2)
      (rq - 3 * ρq / 2) (S - 3 * σ / 2)
    let u := δ / (2 * π * α * d)
    let V := oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) fp
      ((1 - 2 * exp 1 * (1 + (m : ℝ)) * δ / (2 * π * α * d))⁻¹ *
        (2 * (1 + (m : ℝ)) / (2 * π * α * d) * (Rsum + δ) + exp (-(2 * π * K * σ))) * δ) := by
  intro Ψ g gp fp d Rsum φ O U u V
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hwidths
  have hπ := Real.pi_pos
  have hd : 0 < d := lt_min (mul_pos h1 h7) (mul_pos h3 h5)
  obtain ⟨c1, c2⟩ := oscGen_class_bound (by linarith) hK hα hh hdiv hf hδ
  have hΦ : 0 ≤ δ / (2 * π * α) := div_nonneg hδpos (by positivity)
  have hθ : oscTheta m (δ / (2 * π * α)) d =
      2 * exp 1 * (1 + (m : ℝ)) * δ / (2 * π * α * d) := by
    unfold oscTheta
    field_simp
  rw [← hθ]
  exact osc_remainder_of_gen_bound hn hm hα hK ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ hh hdiv hf hδ
    hδpos hsmall c1 c2 hΦ le_rfl hg

end KAM.Planetary

end
