/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.Parameter
public import KAM.Planetary.WeakMeasure.Bridge

/-!
# Divisors on the complex neighbourhood (P11A-C4, `bpP:p11a:divisor-perturb`, `divisor_wide`)

`p11_norm_dotC_le` is the finite Hölder duality `|k·v| ≤ |k|₁ ‖v‖` (`bpP:p11a:x-duality`).
`divisor_perturb`: a lower bound `D` on the divisors `|k·ω(b)|`, `0<|k|₁≤T`, at the real points of
`E`, with `ω` holomorphic and `‖Dω‖ ≤ L` on `E+t` and `tTL ≤ D/2`, gives the lower bound `D/2`
on all of `E+t` (mean value inequality on the polydisc around the real point).
`divisor_wide` is the retained-set form of the limit bridge: the `2γ|k|^(-τ)` lower bounds at
`u k` and the closeness `γ|k|^(-τ-1)` to `v` give `γ T^(-τ)` at `v` for all `0<|k|₁≤T`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- `bpP:p11a:x-duality`: `|k·v| ≤ |k|₁ ‖v‖` for the max norm. -/
theorem p11_norm_dotC_le {m : ℕ} (k : Fin m → ℤ) (v : P11CVec m) :
    ‖p11dotC k v‖ ≤ KAM.Fourier.modeSize k * ‖v‖ := by
  unfold p11dotC KAM.Fourier.modeSize
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have : ‖(k i : ℂ)‖ = |(k i : ℝ)| := by simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)

/-- `bpP:p11a:divisor-wide`. -/
theorem divisor_wide {n : ℕ} {gamma tau T : ℝ}
    (hg : 0 < gamma) (ht : 0 ≤ tau) (hT : 0 < T)
    (v : P11Vec n) (u : (Fin n → ℤ) → P11Vec n)
    (hu : ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      2*gamma*KAM.Fourier.modeSize k^(-tau) ≤ |p11dotZ k (u k)|)
    (hc : ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      ‖u k-v‖ ≤ gamma*KAM.Fourier.modeSize k^(-tau-1)) :
    ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      gamma*T^(-tau) ≤ |p11dotZ k v| := by
  intro k hk hkT
  have h1 := limit_bridge hg hk (hu k hk hkT) (hc k hk hkT)
  have h2 : T ^ (-tau) ≤ KAM.Fourier.modeSize k ^ (-tau) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [KAM.Fourier.one_le_modeSize hk]) hkT
      (by linarith)
  exact (mul_le_mul_of_nonneg_left h2 hg.le).trans h1

/-- `bpP:p11a:divisor-perturb`. -/
theorem divisor_perturb {n : ℕ} {E : Set (P11Vec n)} {t T D L : ℝ}
    (ht : 0 < t) (hT : 0 < T) (hD : 0 < D) (hL : 0 ≤ L)
    (w : P11CVec n → P11CVec n) (hw : DifferentiableOn ℂ w (KAM.actionNbhd E t))
    (hb : ∀ b ∈ KAM.actionNbhd E t, ‖fderiv ℂ w b‖ ≤ L)
    (hsmall : t*T*L ≤ D/2)
    (hdiv : ∀ b ∈ E, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      D ≤ ‖p11dotC k (w (KAM.realInclusion n b))‖) :
    ∀ b ∈ KAM.actionNbhd E t, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      D/2 ≤ ‖p11dotC k (w b)‖ := by
  intro b hbE k hk hkT
  obtain ⟨J, hJ, hbJ⟩ := hbE
  set b0 : P11CVec n := fun i => (J i : ℂ) with hb0
  have hball : ball b0 t ⊆ KAM.actionNbhd E t := fun x hx =>
    ⟨J, hJ, by simpa [dist_eq_norm] using hx⟩
  have hdA : ∀ x ∈ ball b0 t, DifferentiableAt ℂ w x := fun x hx =>
    hw.differentiableAt ((p11_isOpen_actionNbhd E t).mem_nhds (hball hx))
  have hbb : b ∈ ball b0 t := by simpa [dist_eq_norm] using hbJ
  have hmv : ‖w b - w b0‖ ≤ L * ‖b - b0‖ :=
    (convex_ball b0 t).norm_image_sub_le_of_norm_fderiv_le hdA (fun x hx => hb x (hball hx))
      (mem_ball_self ht) hbb |> fun h => by simpa [norm_sub_rev] using h
  have hlin : p11dotC k (w b) - p11dotC k (w b0) = p11dotC k (w b - w b0) := by
    simp [p11dotC, mul_sub, Finset.sum_sub_distrib]
  have hdist : ‖p11dotC k (w b) - p11dotC k (w b0)‖ ≤ D / 2 := by
    rw [hlin]
    calc ‖p11dotC k (w b - w b0)‖ ≤ KAM.Fourier.modeSize k * ‖w b - w b0‖ := p11_norm_dotC_le _ _
      _ ≤ T * (L * t) := by
        gcongr
        exact hmv.trans (by gcongr)
      _ ≤ D / 2 := by nlinarith
  have h0 := hdiv J hJ k hk hkT
  have : ‖p11dotC k (w b0)‖ ≤ ‖p11dotC k (w b)‖ + ‖p11dotC k (w b) - p11dotC k (w b0)‖ := by
    calc ‖p11dotC k (w b0)‖ = ‖p11dotC k (w b) - (p11dotC k (w b) - p11dotC k (w b0))‖ := by
          ring_nf
      _ ≤ _ := norm_sub_le _ _
  have hb0' : ‖p11dotC k (w b0)‖ = ‖p11dotC k (w (KAM.realInclusion n J))‖ := rfl
  linarith

end KAM.Planetary
