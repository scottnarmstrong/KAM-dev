/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Corner.SupBound
public import KAM.Certificate.Sound.Invariance

/-!
# Corner variants of the invariance and embedding checks

`checkInvarianceCorner` and `checkEmbeddingCorner` are `checkInvariance` and `checkEmbedding` with
the final comparison of the landed `supBound` (weight `w^{|k|₁}` for every coefficient at once)
replaced by the corner check (`Corner/SupBound.lean`): the invariance rows and the `Fourier` action
shifts by `cornerLeq`, the rows of `DK` (an `ℓ¹` row sum of sups) by the joint `rowCornerLeq`.
Model construction (`Slp.compose`, `invarianceModel`, `dkModels`, `actionShiftModel`) is the landed
one. Contracts: exactly those of `checkInvariance_sound` and `checkEmbedding_sound`
(`hE`, respectively `hball` and `hDK`).

The Gram and torsion checks are not sharpened in this package (the measured gains are 8 % on `σB`
and none on the exact torsion inverse, design study §1.2); the landed ones are reused.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Torus KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- `checkInvariance` with the corner bound in place of `supBound`. -/
def checkInvarianceCorner (c : TorusCertificate n α) : Bool :=
  match Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) with
  | some ms => (List.range (n + n)).all fun a =>
      cornerLeq c.weight (wloOf c.weight c.expOrder) n
        (invarianceModel n c.emb c.freqBox c.params.s c.weight c.cfgFull c.piEnc ms a)
        (ofRatDown c.params.err)
  | none => false

/-- `checkEmbedding` with the corner bounds: the action shifts by `cornerLeq`, the `DK` rows by the
joint `rowCornerLeq`. -/
def checkEmbeddingCorner (c : TorusCertificate n α) : Bool :=
  let p := c.params
  (List.range n).all (fun i =>
      angleImOk n c.emb c.weight c.piEnc p.rho (c.weightH.rho - p.rho - p.μ) i) &&
    (List.range n).all (fun i =>
      cornerLeq c.weight (wloOf c.weight c.expOrder) n
        (actionShiftModel n c.emb c.weight c.piEnc (c.centre.getD i 0) i)
        (ofRatDown (c.radius.getD i 0 - p.μ))) &&
    (List.range (n + n)).all (fun r =>
      rowCornerLeq c.weight (wloOf c.weight c.expOrder) n
        ((List.finRange n).map fun j =>
          modelMatrixEntry (dkModels n c.emb c.weight c.piEnc) r j.val)
        (ofRatDown (p.σK - p.μ)))

variable [LawfulCertArith α]

/-- `checkInvarianceCorner_sound`, with the conclusions of the Hamiltonian-bounds and embedding
contracts as hypotheses: exactly the contract of `checkInvariance_sound_of`. -/
theorem checkInvarianceCorner_sound_of {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    (h : checkInvarianceCorner c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err := by
  have S := checkStatic_sound hs
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  have hD := isOpen_certDomain n c.weightH.rho c.centre c.radius
  unfold checkInvarianceCorner at h
  split at h
  · rename_i ms hc
    obtain ⟨hlen, hm⟩ := Slp.compose_sound c.ham.jet.prog c.emb c.wit S.hW c.cfgFull S.hpe _ hc
    have hslot : ∀ y : Fin n ⊕ Fin n, (ms.getD (phaseNat y) zeroModel).Encloses n c.weight.rho
        (fun θ => fderiv ℂ c.H (c.K θ) (phaseBasis y)) := by
      intro y
      have hy := phaseNat_lt_add y
      have hq : phaseNat y < ms.length := by rw [hlen]; simpa [d1Slots] using hy
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
      refine (hm _ hq).of_eqOn fun θ hθ => ?_
      have : (d1Slots n c.ham.jet).getD (phaseNat y) 0 = c.ham.jet.d1.getD (phaseNat y) 0 := by
        simp [d1Slots, List.getD_eq_getElem?_getD, hy]
      rw [this, c.ham.jet_d1 hD hH.1 (hKD θ hθ) y]
      rfl
    have hcoord : ∀ x : Fin n ⊕ Fin n,
        (invarianceModel n c.emb c.freqBox c.params.s c.weight c.cfgFull c.piEnc ms
          (phaseNat x)).Encloses n c.weight.rho
          (fun θ => sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ) x) := by
      intro x
      have hdk := (dkFreqModel_encloses S.hW c.cfgFull S.hpe c.emb hω c.params.s x).negM
      have hfun : ∀ θ, sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ) x =
          hamSign x * fderiv ℂ c.H (c.K θ) (phaseBasis x.swap) +
            -∑ l, ((((c.params.s : ℝ) • ωstar) l : ℝ) : ℂ) * tangentMat (c.emb.eval n) θ x l := by
        intro θ
        rw [invarianceError, map_sub, Pi.sub_apply, sumVec_hamiltonianVectorFieldℂ,
          sumVec_fderiv_apply, sub_eq_add_neg]
        rfl
      have hsw : swapNat n (phaseNat x) = phaseNat x.swap := swapNat_phaseNat x
      unfold invarianceModel
      rcases x with i | i
      · have hlt : phaseNat (Sum.inl i : Fin n ⊕ Fin n) < n := i.isLt
        simp only [hlt, ↓reduceIte, hsw]
        exact ((hslot _).addMixed S.hW S.hpe hdk).of_eq_fun fun θ => by
          rw [hfun]; simp [hamSign]
      · have hlt : ¬(phaseNat (Sum.inr i : Fin n ⊕ Fin n) < n) := by simp [phaseNat]
        simp only [hlt, ↓reduceIte, hsw]
        exact ((hslot _).negM.addMixed S.hW S.hpe hdk).of_eq_fun fun θ => by
          rw [hfun]; simp [hamSign]
    intro θ hθ
    rw [← S.hrho] at hθ
    rw [← norm_sumVec, pi_norm_le_iff_of_nonneg S.he0]
    intro x
    simp only [List.all_eq_true, List.mem_range] at h
    have hb := (norm_le_of_cornerLeq (N' := c.expOrder) S.hW (hcoord x) hθ
      (h _ (phaseNat_lt_add x))).trans (LawfulCertArith.ofRatDown_le _)
    exact hb
  · exact absurd h (by simp)

theorem checkInvarianceCorner_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true)
    (hemb : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    (h : checkInvarianceCorner c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err :=
  checkInvarianceCorner_sound_of hs (checkHamBounds_sound hs hh) hemb h hω

open scoped Matrix.Norms.Operator in
/-- `checkEmbeddingCorner_sound`: exactly the contract of `checkEmbedding_sound` (`hball`,
`hDK`). The ball part is the landed argument with `norm_le_of_cornerLeq` for the action shifts; the
`DK` row sums use the joint vertex bound `sum_norm_le_of_rowCornerLeq`. -/
theorem checkEmbeddingCorner_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkEmbeddingCorner c = true) :
    (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ := by
  have hS := checkStatic_sound hs
  have hW := hS.hW
  have hpe := hS.hpe
  have hstrip : ∀ θ ∈ complexStrip n c.params.rho, θ ∈ complexStrip n c.weight.rho := by
    intro θ hθ; rw [hS.hrho]; exact hθ
  unfold checkEmbeddingCorner at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hang, hact⟩, hdk⟩ := h
  rw [← hS.hrho] at hang
  have hr : (c.weight.rho : ℝ) = c.params.rho := by rw [hS.hrho]
  refine ⟨fun θ hθ w hw => ?_, fun θ hθ => ?_⟩
  · have hθ' := hstrip θ hθ
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw1 : ‖w.1 - (c.K θ).1‖ < c.params.μ := (norm_fst_le _).trans_lt hw
    have hw2 : ‖w.2 - (c.K θ).2‖ < c.params.μ := (norm_snd_le _).trans_lt hw
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hU := angleImOk_sound hW hpe (hang i i.isLt) hθ'
      have hd : |(w.1 i - (c.K θ).1 i).im| < c.params.μ :=
        (Complex.abs_im_le_norm _).trans_lt ((norm_le_pi_norm _ i).trans_lt hw1)
      have he : w.1 i = θ i + c.emb.angleAt n i.val θ + (w.1 i - (c.K θ).1 i) := by
        rw [TorusCertificate.K, CertEmbedding.eval_fst]; ring
      rw [he, Complex.add_im, Complex.add_im]
      have := hθ i
      push_cast at hU
      calc |(θ i).im + (c.emb.angleAt n i.val θ).im + (w.1 i - (c.K θ).1 i).im|
          ≤ |(θ i).im| + |(c.emb.angleAt n i.val θ).im| + |(w.1 i - (c.K θ).1 i).im| :=
            abs_add_three _ _ _
        _ < c.weightH.rho := by linarith
    · have hA := norm_le_of_cornerLeq (N' := c.expOrder) hW
        ((realCompModel_encloses (α := α) n c.weight.rho (c.emb.actionDeg.getD i 0)
          c.emb.action[i.val]?).addMixed hW hpe (constModel_encloses n c.weight.rho
            (-(c.centre.getD i 0)) 0 0)) hθ' (hact i i.isLt)
      have h2 := LawfulCertArith.ofRatDown_le (α := α) (c.radius.getD i 0 - c.params.μ)
      have hA' : ‖c.emb.actionAt n i.val θ - ((c.centre.getD i 0 : ℚ) : ℂ)‖ ≤
          ((c.radius.getD i 0 - c.params.μ : ℚ) : ℝ) := by
        refine le_trans (le_of_eq ?_) (hA.trans h2)
        simp [slpConstVal, CertEmbedding.actionAt, sub_eq_add_neg]
      have hd : ‖w.2 i - (c.K θ).2 i‖ < c.params.μ := (norm_le_pi_norm _ i).trans_lt hw2
      have he : w.2 i - ((c.centre.getD i 0 : ℚ) : ℂ) = (w.2 i - (c.K θ).2 i) +
          (c.emb.actionAt n i.val θ - ((c.centre.getD i 0 : ℚ) : ℂ)) := by
        rw [TorusCertificate.K, CertEmbedding.eval_snd]; ring
      rw [he]
      push_cast at hA'
      exact (norm_add_le _ _).trans_lt (by linarith)
  · have hθ' := hstrip θ hθ
    have henc := dkModels_encloses (n := n) hW hpe c.emb
    have hrow (r : Fin n ⊕ Fin n) : ∑ j, ‖tangentMat c.K θ r j‖ ≤
        (c.params.σK : ℝ) - c.params.μ := by
      have hsum := sum_norm_le_of_rowCornerLeq (N' := c.expOrder) hW
        ((List.finRange n).map fun j => (modelMatrixEntry (dkModels n c.emb c.weight c.piEnc)
          (phaseNat r) j.val, fun θ => tangentMat c.K θ r j))
        (by
          intro p hp
          obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
          exact henc r j) hθ' (by
            simp only [List.map_map]
            exact hdk _ (phaseNat_lt_add r))
      have h2 := LawfulCertArith.ofRatDown_le (α := α) (c.params.σK - c.params.μ)
      push_cast at h2
      have hlist : ∑ j : Fin n, ‖tangentMat c.K θ r j‖ = (((List.finRange n).map fun j =>
          (modelMatrixEntry (dkModels n c.emb c.weight c.piEnc) (phaseNat r) j.val,
            fun θ => tangentMat c.K θ r j)).map fun p => ‖p.2 θ‖).sum := by
        rw [List.map_map]
        exact (sum_finRange_map_eq (fun j : Fin n => ‖tangentMat c.K θ r j‖)).symm
      rw [hlist]
      exact hsum.trans h2
    have hB : (0 : ℝ) ≤ (c.params.σK : ℝ) - c.params.μ :=
      (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hrow (.inl ⟨0, by
        have := hS.hn; omega⟩))
    rw [← norm_colMat]
    exact (KAM.norm_le_iff_forall_rowSum hB).2 hrow

end KAM.CertificateSharp
