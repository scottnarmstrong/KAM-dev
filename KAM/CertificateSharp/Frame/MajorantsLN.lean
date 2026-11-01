/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Frame.Majorants

/-!
# The frame majorants without the torsion

`checkFrameMajorants` (`Frame/Majorants.lean`) certifies `|Lᵀ|`, `|N|`, `|Nᵀ|`, `sup |T|` and
`|ω*|`. Route B reads only the first three, so `checkFrameLN` runs the same `checkFrameL` and
`checkFrameN` and neither builds the torsion models nor reads a bound on them. `checkFrameLN_sound`
needs only the static contract: the three bounds concern `K` alone.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Torus KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- `|Lᵀ| ≤ bL`, `|N| ≤ bN`, `|Nᵀ| ≤ bNt`. -/
def checkFrameLN (c : TorusCertificate n α) (bL bN bNt : ℚ) : Bool :=
  checkFrameL c bL && checkFrameN c bN bNt

/-- The real statement of `checkFrameLN` on the strip `T_ρ`. -/
def FrameMajorantsLN (c : TorusCertificate n α) (bL bN bNt : ℚ) : Prop :=
  (∀ θ ∈ complexStrip n c.params.rho, ∀ j : Fin n,
      ∑ r : Fin n ⊕ Fin n, ‖tangentMat c.K θ r j‖ ≤ bL) ∧
  (∀ θ ∈ complexStrip n c.params.rho, ∀ r : Fin n ⊕ Fin n,
      ∑ j : Fin n, ‖normalMat c.K θ r j‖ ≤ bN) ∧
  (∀ θ ∈ complexStrip n c.params.rho, ∀ j : Fin n,
      ∑ r : Fin n ⊕ Fin n, ‖normalMat c.K θ r j‖ ≤ bNt)

/-- **Soundness of the frame majorants without the torsion.** -/
theorem checkFrameLN_sound [LawfulCertArith α] {c : TorusCertificate n α}
    (hs : checkStatic c = true) {bL bN bNt : ℚ} (h : checkFrameLN c bL bN bNt = true) :
    FrameMajorantsLN c bL bN bNt := by
  have S := checkStatic_sound hs
  have hn : 1 ≤ n := le_trans (by norm_num) S.hn
  have hstrip : ∀ θ ∈ complexStrip n c.params.rho, θ ∈ complexStrip n c.weight.rho := by
    intro θ hθ; rw [S.hrho]; exact hθ
  simp only [checkFrameLN, Bool.and_eq_true] at h
  obtain ⟨hL, hN⟩ := h
  have hdb : ∀ x : ℚ, val (ofRatDown x : α) ≤ x := fun x => LawfulCertArith.ofRatDown_le x
  have hNm : normalMat c.K = fun θ => omegaZeroMatrix n * (tangentMat (c.emb.eval n) θ *
      (gramMatrix (c.emb.eval n) θ)⁻¹) := by
    funext θ
    simp [normalMat, TorusCertificate.K, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · -- |Lᵀ|
    intro θ hθ j
    unfold checkFrameL at hL
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at hL
    exact (col_sum_le (N' := c.expOrder) (dkModels_encloses (n := n) S.hW S.hpe c.emb) S.hW
      (hstrip θ hθ) j (hL j)).trans (hdb bL)
  · -- |N|
    intro θ hθ r
    unfold checkFrameN frameGram at hN
    split at hN
    · rename_i δβ hG
      split at hN
      · rename_i eps heps
        simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hN
        have hM := frameNModels_encloses hn S.hW c.emb c.gramInv c.cfgLow S.hpe hG heps
        rw [hNm]
        exact (row_sum_le (N' := c.expOrder) hM S.hW (hstrip θ hθ) r hN.1).trans (hdb bN)
      · exact absurd hN (by simp)
    · exact absurd hN (by simp)
  · -- |Nᵀ|
    intro θ hθ j
    unfold checkFrameN frameGram at hN
    split at hN
    · rename_i δβ hG
      split at hN
      · rename_i eps heps
        simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hN
        have hM := frameNModels_encloses hn S.hW c.emb c.gramInv c.cfgLow S.hpe hG heps
        rw [hNm]
        exact (col_sum_le (N' := c.expOrder) hM S.hW (hstrip θ hθ) j (hN.2 j)).trans (hdb bNt)
      · exact absurd hN (by simp)
    · exact absurd hN (by simp)

end KAM.CertificateSharp

end
