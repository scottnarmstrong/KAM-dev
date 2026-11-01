/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds.Cauchy
public import KAM.Planetary.Exponential.Perturbation

/-!
# Bounds on thin complex tubes

Package LP-DOMX, `LP:MAIN L8 (253, 270)`, track LP, non-frozen.

* `complexTube_mono`, `complexTube_add_shift`, `closedBall_subset_complexTube`,
  `isOpen_complexTube`.
* `exists_norm_le_halfTube`: a shift-periodic continuous function is bounded on the half tube.
* `norm_fderiv_le_quarterTube`: Cauchy estimate on the quarter tube from a bound on the half tube.
* `norm_sub_le_of_quarterTube`: the resulting Lipschitz estimate near a real centre.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Metric

variable {n : ℕ}

section Tube

variable {K : Set (Phase (n + n))}

theorem complexTube_mono {r r' : ℝ} (h : r ≤ r') : complexTube K r ⊆ complexTube K r' := by
  rintro z ⟨x, hx, hz⟩
  exact ⟨x, hx, hz.trans_le h⟩

theorem isOpen_complexTube (r : ℝ) : IsOpen (complexTube K r) := by
  have : complexTube K r = ⋃ x ∈ periodicOrbitSet K,
      ball (KAM.Nekhoroshev.complexifyPhase x) r := by
    ext z
    simp only [complexTube, mem_ofPred_eq, mem_iUnion, mem_ball, dist_eq_norm, exists_prop]
  rw [this]
  exact isOpen_biUnion fun _ _ => isOpen_ball

theorem complexTube_add_shift {r : ℝ} (k : Fin n → ℤ) {z : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)}
    (hz : z ∈ complexTube K r) :
    z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + n)) ∈ complexTube K r := by
  obtain ⟨x, ⟨k', x0, hx0, rfl⟩, hzx⟩ := hz
  refine ⟨x0 + fastShift k' + fastShift k, ⟨k' + k, x0, hx0, ?_⟩, ?_⟩
  · rw [fastShift_add]; abel
  · have h1 : z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + n)) -
        KAM.Nekhoroshev.complexifyPhase (x0 + fastShift k' + fastShift k) =
        z - KAM.Nekhoroshev.complexifyPhase (x0 + fastShift k') := by
      simp only [complexifyPhase_add]; abel
    rw [h1]; exact hzx

theorem closedBall_subset_complexTube {ρ σ : ℝ} {z : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)}
    (hz : z ∈ complexTube K ρ) : closedBall z σ ⊆ complexTube K (ρ + σ) := by
  obtain ⟨x, hx, hzx⟩ := hz
  intro y hy
  refine ⟨x, hx, ?_⟩
  have h1 : ‖y - z‖ ≤ σ := by simpa [dist_eq_norm] using hy
  calc ‖y - KAM.Nekhoroshev.complexifyPhase x‖
      = ‖(y - z) + (z - KAM.Nekhoroshev.complexifyPhase x)‖ := by congr 1; abel
    _ ≤ ‖y - z‖ + ‖z - KAM.Nekhoroshev.complexifyPhase x‖ := norm_add_le _ _
    _ < ρ + σ := by linarith

/-- A continuous shift-periodic function on `complexTube K R` is bounded on `complexTube K (R/2)`
(compactness of one fundamental cell thickened by `R/2`). -/
theorem exists_norm_le_halfTube {F : Type*} [NormedAddCommGroup F] (hK : IsCompact K) {R : ℝ}
    (hR : 0 < R) {G : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → F}
    (hG : ContinuousOn G (complexTube K R))
    (hper : ∀ (k : Fin n → ℤ) (z : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)), z ∈ complexTube K R →
      G (z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + n))) = G z) :
    ∃ M : ℝ, ∀ z ∈ complexTube K (R / 2), ‖G z‖ ≤ M := by
  set C : Set ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) :=
    (fun p : Phase (n + n) × ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) =>
      KAM.Nekhoroshev.complexifyPhase p.1 + p.2) '' (K ×ˢ closedBall 0 (R / 2)) with hC
  have hcx : Continuous (KAM.Nekhoroshev.complexifyPhase (n := n + n)) := by
    unfold KAM.Nekhoroshev.complexifyPhase
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun i => Complex.continuous_ofReal.comp
        ((continuous_apply i).comp continuous_fst)
    · exact continuous_pi fun i => Complex.continuous_ofReal.comp
        ((continuous_apply i).comp continuous_snd)
  have hCc : IsCompact C :=
    (hK.prod (isCompact_closedBall _ _)).image ((hcx.comp continuous_fst).add continuous_snd)
  have hCT : C ⊆ complexTube K R := by
    rintro _ ⟨⟨x, v⟩, ⟨hx, hv⟩, rfl⟩
    refine ⟨x, mem_periodicOrbitSet_self hx, ?_⟩
    have : ‖v‖ ≤ R / 2 := by simpa using hv
    simp only [add_sub_cancel_left]
    exact this.trans_lt (half_lt_self hR)
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (hG.mono hCT)
  refine ⟨M, fun z hz => ?_⟩
  obtain ⟨x, ⟨k, x0, hx0, rfl⟩, hn'⟩ := hz
  have hz' : z - KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + n)) ∈ C := by
    refine ⟨(x0, z - KAM.Nekhoroshev.complexifyPhase (x0 + fastShift k)), ⟨hx0, ?_⟩, ?_⟩
    · simpa using hn'.le
    · simp only [complexifyPhase_add]; abel
  have h1 := hper k _ (hCT hz')
  rw [sub_add_cancel] at h1
  exact h1 ▸ hM _ hz'

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Cauchy estimate on the quarter tube from a sup bound on the half tube. -/
theorem norm_fderiv_le_quarterTube {R M : ℝ} (hR : 0 < R)
    {G : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → F}
    (hG : DifferentiableOn ℂ G (complexTube K R))
    (hM : ∀ z ∈ complexTube K (R / 2), ‖G z‖ ≤ M) :
    ∀ z ∈ complexTube K (R / 4), ‖fderiv ℂ G z‖ ≤ M / (R / 4) := by
  intro z hz
  have hsub : closedBall z (R / 4) ⊆ complexTube K (R / 2) :=
    (closedBall_subset_complexTube hz).trans (complexTube_mono (by linarith))
  exact norm_fderiv_le_cauchyBall (by positivity)
    (hG.mono (hsub.trans (complexTube_mono (by linarith)))) fun y hy => hM y (hsub hy)

/-- Lipschitz estimate on a quarter-tube ball around a real centre of the periodic orbit set. -/
theorem norm_sub_le_of_quarterTube {R C : ℝ}
    {G : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → F}
    (hG : DifferentiableOn ℂ G (complexTube K R))
    (hC : ∀ z ∈ complexTube K (R / 4), ‖fderiv ℂ G z‖ ≤ C) {x : Phase (n + n)}
    (hx : x ∈ periodicOrbitSet K) {z : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)}
    (hz : ‖z - KAM.Nekhoroshev.complexifyPhase x‖ < R / 4) (hR : 0 < R) :
    ‖G z - G (KAM.Nekhoroshev.complexifyPhase x)‖ ≤
      C * ‖z - KAM.Nekhoroshev.complexifyPhase x‖ := by
  have hball : ball (KAM.Nekhoroshev.complexifyPhase x) (R / 4) ⊆ complexTube K (R / 4) :=
    fun y hy => ⟨x, hx, by simpa [dist_eq_norm] using hy⟩
  have hcent : KAM.Nekhoroshev.complexifyPhase x ∈
      ball (KAM.Nekhoroshev.complexifyPhase x) (R / 4) :=
    mem_ball_self (by positivity)
  refine (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le (fun y hy => ?_)
    (fun y hy => hC y (hball hy)) hcent (by simpa [dist_eq_norm] using hz)
  exact (hG.differentiableAt ((isOpen_complexTube R).mem_nhds
    ((complexTube_mono (by linarith)) (hball hy))))

end Tube

end KAM.Planetary.StrongAMD

end
