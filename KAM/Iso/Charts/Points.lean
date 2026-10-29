/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Charts.Rays

/-!
# Part 3 (local charts): the point of an energy curve on a ray

Blueprint node `bpI:p3:points`. `n = 2`.

* `points` (`bpI:p3:points`, one ray; both signs are instances): for a patch with centre `c`, a
  ray `ω*` of slope `m` (`|m| < δ_m`) and an energy `E` with `|E - h(c)| ≤ δ_E`, the point
  `I = Ψ(E, m)` lies in `W`, has `h(I) = E` and `m_c(I) = m`, its gradient is
  `s° ω*` with `s° = ‖∇h(I)‖ / ‖ω*‖ ∈ (2, 4 M_g / m_h)` (by `slope_ray`), and it is close to
  every `I₀` with `‖I₀ - c‖ < ρ_c`. Moreover `Φ_c` maps the energy segment
  `{I ∈ W : h(I) = E, |m_c(I)| ≤ δ_m}` bijectively onto `{E} × [-δ_m, δ_m]` (`Set.BijOn`; the
  restriction of the homeomorphism `Φ_c|_W`).
-/

public section

open scoped Matrix.Norms.Operator
open Matrix Set Metric Topology

namespace KAM.Iso.Charts

open KAM KAM.Torus KAM.Iso.Confinement

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ} {B' : Set (Fin 2 → ℝ)} {η : ℝ}

/-- The energy segment `{I ∈ W : h(I) = E, |m_c(I)| ≤ δ_m}` is mapped bijectively by `Φ_c` onto
`{E} × [-δ_m, δ_m]` (the last claim of `bpI:p3:points`). -/
theorem bijOn_energySegment {c : Fin 2 → ℝ} {W : Set (Fin 2 → ℝ)} {Ψ : ℝ × ℝ → Fin 2 → ℝ}
    {δE δm : ℝ} (hQ : Icc (realPart h c - δE) (realPart h c + δE) ×ˢ Icc (-δm) δm ⊆
      chartPhi h c '' W) (hleft : ∀ I ∈ W, Ψ (chartPhi h c I) = I) {E : ℝ}
    (hE : |E - realPart h c| ≤ δE) :
    Set.BijOn (chartPhi h c) {I | I ∈ W ∧ realPart h I = E ∧ |chartM h c I| ≤ δm}
      ({E} ×ˢ Icc (-δm) δm) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro I ⟨-, hIE, hIm⟩
    exact ⟨hIE, abs_le.1 hIm⟩
  · intro I hI J hJ hIJ
    rw [← hleft I hI.1, ← hleft J hJ.1, hIJ]
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hx' : x = E := hx
    subst hx'
    obtain ⟨I, hIW, hIv⟩ :=
      hQ ⟨⟨by linarith [(abs_le.1 hE).1], by linarith [(abs_le.1 hE).2]⟩, hy⟩
    refine ⟨I, ⟨hIW, ?_, ?_⟩, hIv⟩
    · exact congrArg Prod.fst hIv
    · have : chartM h c I = y := congrArg Prod.snd hIv
      rw [this]
      exact abs_le.2 hy

/-- `bpI:p3:points`, for one ray (both signs are instances). -/
theorem points (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty) {δE δm ρc : ℝ}
    {c : Fin 2 → ℝ} {W : Set (Fin 2 → ℝ)} {Ψ : ℝ × ℝ → Fin 2 → ℝ}
    (hp : IsPatch h B r₀ B' (eta1 η B B') c W Ψ δE δm ρc) {γ m : ℝ} {ωs : Fin 2 → ℝ}
    (hray : IsRay h B B' c γ ωs m) (hm : |m| < δm) {E : ℝ} (hE : |E - realPart h c| ≤ δE) :
    (E, m) ∈ chartPhi h c '' W ∧ Ψ (E, m) ∈ W ∧ realPart h (Ψ (E, m)) = E ∧
    chartM h c (Ψ (E, m)) = m ∧
    frequencyMap h (Ψ (E, m)) = (‖frequencyMap h (Ψ (E, m))‖ / ‖ωs‖) • ωs ∧
    2 < ‖frequencyMap h (Ψ (E, m))‖ / ‖ωs‖ ∧
    ‖frequencyMap h (Ψ (E, m))‖ / ‖ωs‖ < 4 * MgConst h B B' / mhConst h B B' ∧
    ‖Ψ (E, m) - c‖ < eta1 η B B' / 4 ∧ Ψ (E, m) ∈ sSet B B' ∧ Ψ (E, m) ∈ B ∧
    (∀ I₀ : Fin 2 → ℝ, ‖I₀ - c‖ < ρc → ‖Ψ (E, m) - I₀‖ < eta1 η B B' / 2) ∧
    Set.BijOn (chartPhi h c) {I | I ∈ W ∧ realPart h I = E ∧ |chartM h c I| ≤ δm}
      ({E} ×ˢ Icc (-δm) δm) := by
  obtain ⟨hdB, -, -, -, hmh, hmhMg, -, hSbd⟩ := compact hd hne
  have hQmem : (E, m) ∈ Icc (realPart h c - δE) (realPart h c + δE) ×ˢ Icc (-δm) δm :=
    ⟨⟨by linarith [(abs_le.1 hE).1], by linarith [(abs_le.1 hE).2]⟩, (abs_lt.1 hm).1.le,
      (abs_lt.1 hm).2.le⟩
  have hV : (E, m) ∈ chartPhi h c '' W := hp.Q_subset hQmem
  have hIW : Ψ (E, m) ∈ W := hp.Ψ_mem _ hV
  have hΦ : chartPhi h c (Ψ (E, m)) = (E, m) := hp.Ψ_right _ hV
  have hIE : realPart h (Ψ (E, m)) = E := congrArg Prod.fst hΦ
  have hIm : chartM h c (Ψ (E, m)) = m := congrArg Prod.snd hΦ
  have hc : c ∈ closure B' := hp.c_mem
  have hg : frequencyMap h c ≠ 0 := frequencyMap_ne_zero_of_mem_closure hd hc
  have hη₁ : eta1 η B B' ≤ dB B B' / 2 := min_le_right _ _
  -- position
  have hpos : ‖Ψ (E, m) - c‖ < eta1 η B B' / 4 := by
    have := hp.W_subset_ball hIW
    rwa [mem_ball, dist_eq_norm] at this
  have hIS : Ψ (E, m) ∈ sSet B B' := by
    refine Metric.mem_cthickening_of_dist_le _ c _ _ hc ?_
    rw [dist_eq_norm]
    linarith
  -- the gradient is parallel to the ray
  have hdom := hp.W_dom hIW
  have hslope : slope (frequencyMap h c) (frequencyMap h (Ψ (E, m))) =
      slope (frequencyMap h c) ωs := by
    rw [hray.2.2.2.1]
    exact hIm
  obtain ⟨hlr, hlr2⟩ := slope_ray hg hray.2.2.1 hdom.2
  have hpar := hlr.1 hslope.symm
  have hratio := hlr2 hslope.symm
  rw [hratio] at hpar
  -- bounds on the ratio
  obtain ⟨hlow, hup, -⟩ := hSbd _ hIS
  have hωlow : mhConst h B B' / 4 < ‖ωs‖ := hray.2.2.2.2.1
  have hωup : ‖ωs‖ < mhConst h B B' / 2 := hray.2.2.2.2.2
  have hωpos : 0 < ‖ωs‖ := lt_trans (by positivity) hωlow
  have hratio_low : 2 < ‖frequencyMap h (Ψ (E, m))‖ / ‖ωs‖ := by
    rw [lt_div_iff₀ hωpos]
    nlinarith
  have hratio_up : ‖frequencyMap h (Ψ (E, m))‖ / ‖ωs‖ < 4 * MgConst h B B' / mhConst h B B' := by
    rw [div_lt_div_iff₀ hωpos hmh]
    nlinarith [norm_nonneg (frequencyMap h (Ψ (E, m)))]
  refine ⟨hV, hIW, hIE, hIm, hpar, hratio_low, hratio_up, hpos, hIS, hp.W_subset_B hIW, ?_,
    bijOn_energySegment hp.Q_subset hp.Ψ_left hE⟩
  intro I₀ hI₀
  calc ‖Ψ (E, m) - I₀‖ = ‖(Ψ (E, m) - c) + (c - I₀)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖Ψ (E, m) - c‖ + ‖c - I₀‖ := norm_add_le _ _
    _ < eta1 η B B' / 4 + eta1 η B B' / 4 := by
        have h1 : ‖c - I₀‖ < ρc := by rwa [norm_sub_rev]
        linarith [hp.ρc_le]
    _ = eta1 η B B' / 2 := by ring

end KAM.Iso.Charts
