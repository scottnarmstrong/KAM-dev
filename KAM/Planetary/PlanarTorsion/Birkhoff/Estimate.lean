/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff.Map
public import KAM.Planetary.PlanarTorsion.Birkhoff.Average
public import KAM.Planetary.PlanarTorsion.Birkhoff.BetaAvg
public import KAM.Planetary.PlanarTorsion.Birkhoff.Chi
public import KAM.Planetary.PlanarTorsion.NormalForm

/-!
# Planar quartic torsion: the sixth-order estimate for the transformed average (package T16)

Blueprint P, Part 11b (`stepP:p11b:bt-avg`, `stepP:p11b:bt-nf`).  Combining the Lie-series estimate
`lie` (T10) for the rotated secular function with the identification of the torus average of
`f̂ ∘ T` (`p11cB_secular_T`), the constant `δ(I)` of the moving average cancels in the difference
(`p11cB_secular_mov`), and `p11cB_average_beta` turns the average of the quartic into `½ ∑ β R R`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

/-- The sixth-order estimate for the torus average of `f̂ ∘ T`. -/
theorem p11cB_estimate (p : PlanarData) (hp : p.Valid) (b : Bool) (P : Phase (2 + 2) → ℝ)
    (hP : ∀ w, P w = SecularForm.perturbation (p11cSecularData p hp) b w)
    {Og K : Set (Fin 2 → ℝ)} (hOg : ∀ I ∈ Og, I ∈ p11c_frameActionDomain p) (hKOg : K ⊆ Og)
    (hKpos : ∀ I ∈ K, ∀ i, 0 < I i) (F₀ : QuarticFamily Og)
    (hF₀ : ∀ I z, F₀.eval I z = p11c_quartic (p11c_coeffs p (p.axes I))
      (p11c_rotateSlow (p11c_frame p (p.axes I)) z))
    (chi : QuarticFamily Og) (hchi : ∀ I ∈ Og, chi.eval I = p11c_chi F₀ (p11cB_freq p) I)
    {A rl δ r : ℝ}
    (hlie : ∀ I ∈ K, ∀ z : Phase 2, p11c_slowLength z < rl →
      |(p11cB_C p I + p11c_n0 (p11cB_freq p) I (p11c_flow (p11c_chi F₀ (p11cB_freq p)) I 1 z) +
        F₀.eval I (p11c_flow (p11c_chi F₀ (p11cB_freq p)) I 1 z) +
        p11cB_R p I (p11c_flow (p11c_chi F₀ (p11cB_freq p)) I 1 z)) -
        (p11cB_C p I + p11c_n0 (p11cB_freq p) I z + p11c_average F₀.eval I z)| ≤
          A * p11c_slowLength z ^ 6)
    (hδ : 0 < δ)
    (hdom : ∀ w : Phase (2 + 2), (fun i => w.2 (Fin.castAdd 2 i)) ∈ K →
      (∀ i, |w.1 (Fin.natAdd 2 i)| < δ) → (∀ i, |w.2 (Fin.natAdd 2 i)| < δ) → w ∈ p11cB_good p)
    (hr : 2 * r ≤ δ) (hrl : r ≤ rl)
    (hflow : ∀ I ∈ K, ∀ z : Phase 2, p11c_slowLength z < r →
      p11c_slowLength (p11c_flow chi.eval I 1 z) ^ 2 ≤ 2 * p11c_slowLength z ^ 2)
    {I : Fin 2 → ℝ} (hIK : I ∈ K) {z : Phase 2} (hz : p11c_slowLength z < r) :
    |p11c_secular (P ∘ (p11c_rotationLift p ∘ p11c_liftFlow chi.eval)) I z -
      (p11c_secular P I 0 + (∑ j, 2 * p11c_sigma p (p.axes I) j * oscillatorAction z.2 z.1 j) +
        (1 / 2 : ℝ) * ∑ i, ∑ j, p11c_beta p (p.axes I) i j * oscillatorAction z.2 z.1 i *
          oscillatorAction z.2 z.1 j)| ≤ A * p11c_slowLength z ^ 6 := by
  have hKd : K ⊆ p11c_frameActionDomain p := fun I hI => hOg I (hKOg hI)
  have hIOg : I ∈ Og := hKOg hIK
  have hax : p.axes I ∈ p11c_axes := hKd hIK
  obtain ⟨c, hc⟩ := p11cB_T_assemble p chi.eval I z
  set T := p11c_rotationLift p ∘ p11c_liftFlow chi.eval with hT
  set Y := p11c_flow chi.eval I 1 z with hY
  set Zs := p11c_rotateSlow (p11c_frame p (p.axes I)) Y with hZs
  have hYe : Y = p11c_flow (p11c_chi F₀ (p11cB_freq p)) I 1 z := by
    rw [hY, p11cN_flow_congr (hchi I hIOg)]
  have hgoodall := fun t => p11cB_Zs_good p hp chi.eval hKd hδ hdom hr hflow hIK hz t
  have hsec := p11cB_secular_T p hp b P hP T I z Zs c hc (by simpa using hgoodall c |>.1)
  have hKY : p11c_secular (p11c_hatFix p) I Zs = SecularForm.secular (p11cSecularData p hp)
      false (Zs.1, I, Zs.2) := p11cB_secular_eq p hp I Zs
  -- the constant of the moving average
  have key : ∃ d : ℝ, p11c_secular (P ∘ T) I z = p11cB_K p I Y + d ∧
      p11c_secular P I 0 = p11cB_C p I + d := by
    cases b
    · have hPe : P = p11c_hatFix p := funext fun w => (hP w).trans rfl
      subst hPe
      refine ⟨0, ?_, ?_⟩
      · rw [hsec, add_zero]; exact hKY.symm
      · rw [add_zero]; rfl
    · have hPe : P = p11c_hatMov p := funext fun w => (hP w).trans rfl
      subst hPe
      refine ⟨SecularForm.modelDelta (p11cSecularData p hp) I, ?_, ?_⟩
      · rw [hsec, p11cB_secular_mov p hp I Zs hgoodall]
        rw [← hKY]; rfl
      · have h0 := p11cB_secular_mov p hp I (0 : Phase 2) (fun t => by
          have := p11cB_circular_mem p hp (hKd hIK) (hKpos I hIK) t
          simpa using this)
        change SecularForm.secular (p11cSecularData p hp) true _ = _ at h0
        have : p11c_secular (p11c_hatMov p) I 0 = SecularForm.secular (p11cSecularData p hp)
            true ((0 : Phase 2).1, I, (0 : Phase 2).2) := rfl
        rw [this, h0]
        rfl
  obtain ⟨d, hd1, hd2⟩ := key
  have hmain := hlie I hIK z (lt_of_lt_of_le hz hrl)
  rw [← hYe, hF₀] at hmain
  have havg : p11c_average F₀.eval I z = (1 / 2 : ℝ) * ∑ i, ∑ j, p11c_beta p (p.axes I) i j *
      oscillatorAction z.2 z.1 i * oscillatorAction z.2 z.1 j := by
    rw [p11cB_average_congr (G := fun _ w => p11c_quartic (p11c_coeffs p (p.axes I))
      (p11c_rotateSlow (p11c_frame p (p.axes I)) w)) (J := 0) (funext (hF₀ I)) z]
    exact p11cB_average_beta p hp hax z
  have hn0z : p11c_n0 (p11cB_freq p) I z =
      ∑ j, 2 * p11c_sigma p (p.axes I) j * oscillatorAction z.2 z.1 j := rfl
  have hKe : p11cB_K p I Y = p11cB_C p I + p11c_n0 (p11cB_freq p) I Y +
      p11c_quartic (p11c_coeffs p (p.axes I)) (p11c_rotateSlow (p11c_frame p (p.axes I)) Y) +
      p11cB_R p I Y := by
    unfold p11cB_R; ring
  rw [hd1, hd2]
  rw [hn0z, havg] at hmain
  have heq : p11cB_K p I Y + d - (p11cB_C p I + d + (∑ j, 2 * p11c_sigma p (p.axes I) j *
        oscillatorAction z.2 z.1 j) + (1 / 2 : ℝ) * ∑ i, ∑ j, p11c_beta p (p.axes I) i j *
          oscillatorAction z.2 z.1 i * oscillatorAction z.2 z.1 j) =
      p11cB_C p I + p11c_n0 (p11cB_freq p) I Y +
        p11c_quartic (p11c_coeffs p (p.axes I)) (p11c_rotateSlow (p11c_frame p (p.axes I)) Y) +
        p11cB_R p I Y - (p11cB_C p I + (∑ j, 2 * p11c_sigma p (p.axes I) j *
          oscillatorAction z.2 z.1 j) + (1 / 2 : ℝ) * ∑ i, ∑ j, p11c_beta p (p.axes I) i j *
            oscillatorAction z.2 z.1 i * oscillatorAction z.2 z.1 j) := by
    rw [hKe]; ring
  rw [heq]
  exact hmain

end KAM.Planetary

end
