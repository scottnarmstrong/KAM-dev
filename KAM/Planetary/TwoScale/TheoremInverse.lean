/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.Inverse
public import KAM.Planetary.TwoScale.StepFreq

/-!
# Two-scale KAM: the source inverse locus and inverse-frequency estimates (`bpP:p3:two-scale-kam`)

On the real points of `D` the frequency map is real and injective (from the source premises of
`KamHyp`), so every `ω ∈ Ω` has a unique `I ∈ dioBase` with `realFreq h I = ω`
(`exists_inverse_locus`). The local estimate `‖I - J‖ ≤ M̄ ‖ω - ω'‖` for `‖ω - ω'‖ < ρ/M̄` comes
from the ball continuation `ball` of `Inverse`; the global one needs `Bornology.IsBounded D`.
Design package P23-22.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

/-- The frequency at a real point of `D` is real. -/
theorem KamHyp.freq_real (H : KamHyp D sbar p h f) {I : Fin (a + b) → ℝ} (hI : I ∈ D) :
    freq h (KAM.realInclusion (a + b) I) = KAM.realInclusion (a + b) (realFreq h I) :=
  freq_realInclusion_eq H.holo (by linarith [H.positive.2.1, H.widths.1]) H.real_h
    (mem_actionNbhd_of_mem H.positive.2.2.1 hI)

/-- `realFreq h` is injective on `D`. -/
theorem KamHyp.realFreq_injOn (H : KamHyp D sbar p h f) : InjOn (realFreq h) D := by
  intro I hI J hJ hIJ
  have e1 := H.freq_real hI
  have e2 := H.freq_real hJ
  have := H.injective (mem_actionNbhd_of_mem H.positive.2.2.1 hI)
    (mem_actionNbhd_of_mem H.positive.2.2.1 hJ) (by rw [e1, e2, hIJ])
  exact KAM.realInclusion_injective (a + b) this

/-- The source inverse locus: each `ω ∈ Ω` has a unique `I ∈ dioBase` with `realFreq h I = ω`. -/
theorem KamHyp.exists_inverse_locus (H : KamHyp D sbar p h f) :
    ∀ ω ∈ omegaSet D h p, ∃ I ∈ dioBase D h p, realFreq h I = ω ∧
      ∀ J ∈ dioBase D h p, realFreq h J = ω → J = I := by
  rintro ω ⟨⟨I, hI, rfl⟩, hω⟩
  exact ⟨I, ⟨hI, hω⟩, rfl, fun J hJ hJI => H.realFreq_injOn hJ.1 hI hJI⟩

/-- Local inverse-frequency estimate on `D`. -/
theorem KamHyp.inverse_local (H : KamHyp D sbar p h f) {I J : Fin (a + b) → ℝ} (hI : I ∈ D)
    (hJ : J ∈ D) (hlt : ‖realFreq h I - realFreq h J‖ < p.ρ / p.Mbar) :
    ‖I - J‖ ≤ p.Mbar * ‖realFreq h I - realFreq h J‖ := by
  have hρ := H.positive.2.2.1
  have hm := H.positive.2.2.2.2.2.2.1
  have hx : Metric.ball (KAM.realInclusion (a + b) I) p.ρ ⊆ KAM.actionNbhd D p.ρ :=
    actionNbhd_ball hI
  obtain ⟨hcov, hlip⟩ := ball (isOpen_actionNbhd' D p.ρ) (fun z hz =>
    (differentiableAt_freq (isOpen_actionNbhd' D p.ρ) H.holo hz).differentiableWithinAt)
    H.injective hm hρ
    (fun x hx => by
      obtain ⟨-, -, A, hA, hAn, -⟩ := H.hessian x hx
      exact ⟨A, hA, hAn⟩) hx
  have e1 := H.freq_real hI
  have e2 := H.freq_real hJ
  have hJmem := mem_actionNbhd_of_mem hρ hJ
  have hFJ : freq h (KAM.realInclusion (a + b) J) ∈
      Metric.ball (freq h (KAM.realInclusion (a + b) I)) (p.ρ / p.Mbar) := by
    rw [mem_ball_iff_norm, e1, e2, ← map_sub, KAM.norm_realInclusion, norm_sub_rev]
    simpa [norm_sub_rev] using hlt
  obtain ⟨y, hy, hyF⟩ := hcov hFJ
  have hyJ : y = KAM.realInclusion (a + b) J := H.injective (hx hy) hJmem hyF
  rw [hyJ] at hy
  have := hlip _ (mem_ball_self hρ) _ hy (mem_ball_self (div_pos hρ hm)) hFJ
  rw [e1, e2, ← map_sub, ← map_sub, KAM.norm_realInclusion, KAM.norm_realInclusion] at this
  exact this

/-- Global inverse-frequency estimate on a bounded `D`. -/
theorem KamHyp.inverse_global (H : KamHyp D sbar p h f) (hb : Bornology.IsBounded D)
    {I J : Fin (a + b) → ℝ} (hI : I ∈ D) (hJ : J ∈ D) :
    ‖I - J‖ ≤ p.Mbar * max 1 (Metric.diam D / p.ρ) * ‖realFreq h I - realFreq h J‖ := by
  have hρ := H.positive.2.2.1
  have hm := H.positive.2.2.2.2.2.2.1
  set w := ‖realFreq h I - realFreq h J‖ with hw
  have hw0 : 0 ≤ w := norm_nonneg _
  have hmax1 : 1 ≤ max 1 (Metric.diam D / p.ρ) := le_max_left _ _
  by_cases hlt : w < p.ρ / p.Mbar
  · refine (H.inverse_local hI hJ hlt).trans ?_
    calc p.Mbar * w = p.Mbar * 1 * w := by ring
      _ ≤ _ := by gcongr
  · rw [not_lt] at hlt
    have hd : ‖I - J‖ ≤ Metric.diam D := by
      rw [← dist_eq_norm]; exact dist_le_diam_of_mem hb hI hJ
    have h1 : 1 ≤ p.Mbar * w / p.ρ := by
      rw [le_div_iff₀ hρ]; rw [div_le_iff₀ hm] at hlt; linarith
    have h2 : Metric.diam D ≤ p.Mbar * (Metric.diam D / p.ρ) * w := by
      have hd0 : 0 ≤ Metric.diam D := Metric.diam_nonneg
      calc Metric.diam D = Metric.diam D * 1 := by ring
        _ ≤ Metric.diam D * (p.Mbar * w / p.ρ) := by gcongr
        _ = _ := by ring
    refine hd.trans (h2.trans ?_)
    have : Metric.diam D / p.ρ ≤ max 1 (Metric.diam D / p.ρ) := le_max_right _ _
    gcongr

end KAM.Planetary

end
