/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.ComplexTube
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds.Cauchy

/-!
# Tube and Cauchy-estimate lemmas on `Phase (n + m)` for the spatial first-derivative bounds

Source: `LP:MAIN L18 (595)` with `LP:MAIN L8 (253, 270)`, track LP, non-frozen.

Twins of the analytic-domain bounds' `Bounds.TubeBound` for `complexTubeNM` (`n` fast and `m` slow
pairs); the multivariable Cauchy estimate `norm_fderiv_le_cauchyBall` is dimension-free and reused.

* `closedBall_subset_complexTubeNM`: thickening of a tube (monotonicity, openness and shift
  invariance are SP-TUBE's `complexTubeNM_mono`, `isOpen_complexTubeNM`,
  `complexTubeNM_add_fastShift`).
* `exists_norm_le_halfTubeNM`: a shift-periodic continuous function is bounded on the half tube.
* `norm_fderiv_le_quarterTubeNM`: Cauchy estimate on the quarter tube.
* `norm_sub_le_of_quarterTubeNM`: Lipschitz estimate around a real centre.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Metric

variable {n m : ℕ} {K : Set (Phase (n + m))}

theorem mem_periodicOrbitSetNM_self {x : Phase (n + m)} (hx : x ∈ K) :
    x ∈ periodicOrbitSetNM K :=
  ⟨0, x, hx, by
    rw [show (fastShift (0 : Fin n → ℤ) : Phase (n + m)) = 0 from by
      refine Prod.ext ?_ rfl
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [fastShift], add_zero]⟩

theorem closedBall_subset_complexTubeNM {ρ σ : ℝ}
    {z : (Fin (n + m) → ℂ) × (Fin (n + m) → ℂ)} (hz : z ∈ complexTubeNM K ρ) :
    closedBall z σ ⊆ complexTubeNM K (ρ + σ) := by
  obtain ⟨x, hx, hzx⟩ := hz
  intro y hy
  refine ⟨x, hx, ?_⟩
  have h1 : ‖y - z‖ ≤ σ := by simpa [dist_eq_norm] using hy
  calc ‖y - KAM.Nekhoroshev.complexifyPhase x‖
      = ‖(y - z) + (z - KAM.Nekhoroshev.complexifyPhase x)‖ := by congr 1; abel
    _ ≤ ‖y - z‖ + ‖z - KAM.Nekhoroshev.complexifyPhase x‖ := norm_add_le _ _
    _ < ρ + σ := by linarith

/-- A continuous shift-periodic function on `complexTubeNM K R` is bounded on
`complexTubeNM K (R/2)` (compactness of one fundamental cell thickened by `R/2`). -/
theorem exists_norm_le_halfTubeNM {F : Type*} [NormedAddCommGroup F] (hK : IsCompact K) {R : ℝ}
    (hR : 0 < R) {G : ((Fin (n + m) → ℂ) × (Fin (n + m) → ℂ)) → F}
    (hG : ContinuousOn G (complexTubeNM K R))
    (hper : ∀ (k : Fin n → ℤ) (z : (Fin (n + m) → ℂ) × (Fin (n + m) → ℂ)),
      z ∈ complexTubeNM K R →
      G (z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + m))) = G z) :
    ∃ M : ℝ, ∀ z ∈ complexTubeNM K (R / 2), ‖G z‖ ≤ M := by
  set C : Set ((Fin (n + m) → ℂ) × (Fin (n + m) → ℂ)) :=
    (fun p : Phase (n + m) × ((Fin (n + m) → ℂ) × (Fin (n + m) → ℂ)) =>
      KAM.Nekhoroshev.complexifyPhase p.1 + p.2) '' (K ×ˢ closedBall 0 (R / 2)) with hC
  have hcx : Continuous (KAM.Nekhoroshev.complexifyPhase (n := n + m)) := by
    unfold KAM.Nekhoroshev.complexifyPhase
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun i => Complex.continuous_ofReal.comp
        ((continuous_apply i).comp continuous_fst)
    · exact continuous_pi fun i => Complex.continuous_ofReal.comp
        ((continuous_apply i).comp continuous_snd)
  have hCc : IsCompact C :=
    (hK.prod (isCompact_closedBall _ _)).image ((hcx.comp continuous_fst).add continuous_snd)
  have hCT : C ⊆ complexTubeNM K R := by
    rintro _ ⟨⟨x, v⟩, ⟨hx, hv⟩, rfl⟩
    refine ⟨x, mem_periodicOrbitSetNM_self hx, ?_⟩
    have : ‖v‖ ≤ R / 2 := by simpa using hv
    simp only [add_sub_cancel_left]
    exact this.trans_lt (half_lt_self hR)
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (hG.mono hCT)
  refine ⟨M, fun z hz => ?_⟩
  obtain ⟨x, ⟨k, x0, hx0, rfl⟩, hn'⟩ := hz
  have hz' : z - KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + m)) ∈ C := by
    refine ⟨(x0, z - KAM.Nekhoroshev.complexifyPhase (x0 + fastShift k)), ⟨hx0, ?_⟩, ?_⟩
    · simpa using hn'.le
    · simp only [complexifyPhase_add]; abel
  have h1 := hper k _ (hCT hz')
  rw [sub_add_cancel] at h1
  exact h1 ▸ hM _ hz'

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Cauchy estimate on the quarter tube from a sup bound on the half tube. -/
theorem norm_fderiv_le_quarterTubeNM {R M : ℝ} (hR : 0 < R)
    {G : ((Fin (n + m) → ℂ) × (Fin (n + m) → ℂ)) → F}
    (hG : DifferentiableOn ℂ G (complexTubeNM K R))
    (hM : ∀ z ∈ complexTubeNM K (R / 2), ‖G z‖ ≤ M) :
    ∀ z ∈ complexTubeNM K (R / 4), ‖fderiv ℂ G z‖ ≤ M / (R / 4) := by
  intro z hz
  have hsub : closedBall z (R / 4) ⊆ complexTubeNM K (R / 2) :=
    (closedBall_subset_complexTubeNM hz).trans
      (complexTubeNM_mono K (by linarith : R / 4 + R / 4 ≤ R / 2))
  exact norm_fderiv_le_cauchyBall (by positivity)
    (hG.mono (hsub.trans (complexTubeNM_mono K (by linarith : R / 2 ≤ R))))
    fun y hy => hM y (hsub hy)

/-- Lipschitz estimate on a quarter-tube ball around a real centre of the periodic orbit set. -/
theorem norm_sub_le_of_quarterTubeNM {R C : ℝ}
    {G : ((Fin (n + m) → ℂ) × (Fin (n + m) → ℂ)) → F}
    (hG : DifferentiableOn ℂ G (complexTubeNM K R))
    (hC : ∀ z ∈ complexTubeNM K (R / 4), ‖fderiv ℂ G z‖ ≤ C) {x : Phase (n + m)}
    (hx : x ∈ periodicOrbitSetNM K) {z : (Fin (n + m) → ℂ) × (Fin (n + m) → ℂ)}
    (hz : ‖z - KAM.Nekhoroshev.complexifyPhase x‖ < R / 4) (hR : 0 < R) :
    ‖G z - G (KAM.Nekhoroshev.complexifyPhase x)‖ ≤
      C * ‖z - KAM.Nekhoroshev.complexifyPhase x‖ := by
  have hball : ball (KAM.Nekhoroshev.complexifyPhase x) (R / 4) ⊆ complexTubeNM K (R / 4) :=
    fun y hy => ⟨x, hx, by simpa [dist_eq_norm] using hy⟩
  have hcent : KAM.Nekhoroshev.complexifyPhase x ∈
      ball (KAM.Nekhoroshev.complexifyPhase x) (R / 4) :=
    mem_ball_self (by positivity)
  refine (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le (fun y hy => ?_)
    (fun y hy => hC y (hball hy)) hcent (by simpa [dist_eq_norm] using hz)
  exact (hG.differentiableAt ((isOpen_complexTubeNM K R).mem_nhds
    ((complexTubeNM_mono K (by linarith : R / 4 ≤ R)) (hball hy))))

end KAM.Planetary.Spatial

end
