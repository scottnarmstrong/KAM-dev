/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Sound.Ham
public import KAM.Certificate.Sound.Embedding

/-!
# Soundness of the torsion sub-check

`checkTorsion_sound_of` assembles `torsionModels_sound` (domain `D = c.D`, open by
`isOpen_certDomain`; `K θ ∈ D` from the `μ`-ball of the embedding contract; the denominators from
the Hamiltonian-bounds contract; the Gram check's own `(δ, β)`) with `torsionAvgCheck_sound` at the
certificate's own `n`. Its two extra hypotheses are verbatim the conclusions of
`checkHamBounds_sound` and `checkEmbedding_sound`; `checkTorsion_sound` (in
`KAM.Certificate.Sound`) discharges them.
-/

public section

namespace KAM.Certificate

open KAM KAM.Torus CertArith

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- `checkTorsion_sound` with the conclusions of the Hamiltonian-bounds and embedding contracts as
hypotheses. -/
theorem checkTorsion_sound_of {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    (h : checkTorsion c = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar))⁻¹ i j‖ ≤
        (c.params.σT : ℝ) - c.params.μ := by
  have S := checkStatic_sound hs
  have hn : 1 ≤ n := le_trans (by norm_num) S.hn
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  unfold checkTorsion at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i T hT
      obtain ⟨-, hTe, hTc⟩ := torsionModels_sound hn (isOpen_certDomain _ _ _ _) hH.1 S.hW hKD
        c.wit c.gramInv c.cfgLow S.hpe hG c.freqBox c.params.s hT hω
      have hρ : (0 : ℝ) < c.weight.rho := by
        rw [S.hrho]; exact S.hρinf.trans S.hρinfρ
      have := torsionAvgCheck_sound hρ hTe hTc c.torsInv _ h
      push_cast at this
      exact this
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Assembled from `torsionModels_sound` and `torsionAvgCheck_sound` (through
`checkTorsion_sound_of`); the Gram premise is part of the signed interface (the torsion check
repeats the Gram certificate itself). -/
theorem checkTorsion_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true) (hg : checkGram c = true)
    (h : checkTorsion c = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar))⁻¹ i j‖ ≤
        (c.params.σT : ℝ) - c.params.μ :=
  have _ := hg
  checkTorsion_sound_of hs (checkHamBounds_sound hs hh) (checkEmbedding_sound hs he) h hω

end KAM.Certificate
