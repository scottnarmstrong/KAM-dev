/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff.Estimate
public import KAM.Planetary.PlanarTorsion.FrozenBridge

/-!
# Planar quartic torsion: the clause for one physical perturbation (package T16)

Blueprint P, Part 11b (`stepP:p11b:bt-frozen`).  For `f̂ ∈ {f̂_fix, f̂_mov}` pulled back by the same
`T`, the function `f̂ ∘ T` is analytic on the tube, its torus average has the sixth-order expansion
(`p11cB_estimate`), and `hasSecularBirkhoffForm_of_sixth_order` (T15), applied to this actual
pullback, yields the frozen predicate `HasSecularBirkhoffForm`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

theorem p11cB_fhat_clause (p : PlanarData) (hp : p.Valid) (b : Bool) (fhat : Phase (2 + 2) → ℝ)
    (hfhat : ∀ w, fhat w = SecularForm.perturbation (p11cSecularData p hp) b w)
    (hfan : AnalyticOnNhd ℝ fhat (p11cB_good p))
    {Og K₁ O' Kimg : Set (Fin 2 → ℝ)} (hOg : ∀ I ∈ Og, I ∈ p11c_frameActionDomain p)
    (hKOg : K₁ ⊆ Og) (hKpos : ∀ I ∈ K₁, ∀ i, 0 < I i) (F₀ : QuarticFamily Og)
    (hF₀ : ∀ I z, F₀.eval I z = p11c_quartic (p11c_coeffs p (p.axes I))
      (p11c_rotateSlow (p11c_frame p (p.axes I)) z))
    (chi : QuarticFamily Og) (hchi : ∀ I ∈ Og, chi.eval I = p11c_chi F₀ (p11cB_freq p) I)
    {A C rl δ r : ℝ}
    (hlie : ∀ I ∈ K₁, ∀ z : Phase 2, p11c_slowLength z < rl →
      |(p11cB_C p I + p11c_n0 (p11cB_freq p) I (p11c_flow (p11c_chi F₀ (p11cB_freq p)) I 1 z) +
        F₀.eval I (p11c_flow (p11c_chi F₀ (p11cB_freq p)) I 1 z) +
        p11cB_R p I (p11c_flow (p11c_chi F₀ (p11cB_freq p)) I 1 z)) -
        (p11cB_C p I + p11c_n0 (p11cB_freq p) I z + p11c_average F₀.eval I z)| ≤
          A * p11c_slowLength z ^ 6)
    (hδ : 0 < δ)
    (hdom : ∀ w : Phase (2 + 2), (fun i => w.2 (Fin.castAdd 2 i)) ∈ K₁ →
      (∀ i, |w.1 (Fin.natAdd 2 i)| < δ) → (∀ i, |w.2 (Fin.natAdd 2 i)| < δ) → w ∈ p11cB_good p)
    (hr : 2 * r ≤ δ) (hrl : r ≤ rl) (hr0 : 0 < r) (hAC : A ≤ C) (hC : 0 < C)
    (hflow : ∀ I ∈ K₁, ∀ z : Phase 2, p11c_slowLength z < r →
      p11c_slowLength (p11c_flow chi.eval I 1 z) ^ 2 ≤ 2 * p11c_slowLength z ^ 2)
    (hO'K : O' ⊆ K₁) (hKimg : Kimg ⊆ O')
    (hch : IsChart 1 (p11c_rotationLift p ∘ p11c_liftFlow chi.eval) (p11c_tube O' r)) :
    AnalyticOnNhd ℝ (fhat ∘ (p11c_rotationLift p ∘ p11c_liftFlow chi.eval)) (p11c_tube O' r) ∧
      ∃ P0 : (Fin 2 → ℝ) → ℝ, (∀ I ∈ Kimg, P0 I = p11c_secular fhat I 0) ∧
        (∀ I ∈ Kimg, ∀ z : Phase 2, p11c_slowLength z < r →
          |p11c_secular (fhat ∘ (p11c_rotationLift p ∘ p11c_liftFlow chi.eval)) I z -
            (P0 I + (∑ j, 2 * p11c_sigma p (p.axes I) j * oscillatorAction z.2 z.1 j) +
              (1 / 2 : ℝ) * ∑ i, ∑ j, p11c_beta p (p.axes I) i j *
                oscillatorAction z.2 z.1 i * oscillatorAction z.2 z.1 j)| ≤
            C * p11c_slowLength z ^ 6) ∧
        ∀ mu0 : ℝ, 0 < mu0 → ∀ r0 : ℝ, 0 < r0 → r0 ≤ r / sqrt 2 →
          HasSecularBirkhoffForm
            (fun _ => fhat ∘ (p11c_rotationLift p ∘ p11c_liftFlow chi.eval))
            (interior Kimg) r0 mu0 (fun _ => fun I => p11c_secular fhat I 0)
            (fun _ I j => 2 * p11c_sigma p (p.axes I) j) (fun _ I => p11c_beta p (p.axes I)) := by
  set T := p11c_rotationLift p ∘ p11c_liftFlow chi.eval with hT
  have hKd : K₁ ⊆ p11c_frameActionDomain p := fun I hI => hOg I (hKOg hI)
  have hTg : ∀ w ∈ p11c_tube O' r, T w ∈ p11cB_good p := fun w hw =>
    p11cB_T_good p hp chi.eval hKd hδ hdom hr hflow w
      ⟨(hO'K hw.1), hw.2⟩
  have hana : AnalyticOnNhd ℝ (fhat ∘ T) (p11c_tube O' r) := hfan.comp hch.1 hTg
  have hbound : ∀ I ∈ Kimg, ∀ z : Phase 2, p11c_slowLength z < r →
      |p11c_secular (fhat ∘ T) I z -
        (p11c_secular fhat I 0 + (∑ j, 2 * p11c_sigma p (p.axes I) j * oscillatorAction z.2 z.1 j) +
          (1 / 2 : ℝ) * ∑ i, ∑ j, p11c_beta p (p.axes I) i j * oscillatorAction z.2 z.1 i *
            oscillatorAction z.2 z.1 j)| ≤ C * p11c_slowLength z ^ 6 := by
    intro I hI z hz
    have h := p11cB_estimate p hp b fhat hfhat hOg hKOg hKpos F₀ hF₀ chi hchi hlie hδ hdom hr hrl
      hflow (hO'K (hKimg hI)) hz
    exact h.trans (mul_le_mul_of_nonneg_right hAC (by positivity))
  refine ⟨hana, fun I => p11c_secular fhat I 0, fun I _ => rfl, hbound, ?_⟩
  intro mu0 hmu r0 hr0' hrr
  refine hasSecularBirkhoffForm_of_sixth_order (fun _ => fhat ∘ T) (interior Kimg) r C mu0 hr0 hC
    hmu (fun _ I => p11c_secular fhat I 0) (fun _ I j => 2 * p11c_sigma p (p.axes I) j)
    (fun _ I => p11c_beta p (p.axes I)) ?_ ?_ r0 hr0' hrr
  · intro mu _ I hI p' q hlen
    have hIO' : I ∈ O' := hKimg (interior_subset hI)
    have hcts : Continuous (fun φ : Fin 2 → ℝ => (fhat ∘ T) (assemble I φ p' q)) := by
      refine (hana.continuousOn).comp_continuous (p11cB_assemble_continuous I p' q) fun φ => ?_
      refine ⟨?_, ?_⟩
      · simpa [assemble, Fin.append_left, p11c_tube] using hIO'
      · simpa [assemble, p11c_tube, p11c_slowLength, Fin.append_right] using hlen
    exact hcts.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  · intro mu _ I hI p' q hlen
    have := hbound I (interior_subset hI) (q, p') hlen
    exact this

end KAM.Planetary

end
