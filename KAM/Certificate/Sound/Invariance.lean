/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Sound.Ham
public import KAM.Certificate.Sound.Embedding

/-!
# Soundness of the invariance sub-check

`checkInvariance_sound_of`: coordinate `x` (in `sumVec` order) of the invariance error
`X_H ∘ K - DK (s ω)` is enclosed by `invarianceModel` at row `phaseNat x`: the composed slot
`∂_{x.swap} H ∘ K` (`Slp.compose_sound`, `HamExpr.jet_d1`, sign `hamSign x`) minus
`dkFreqModel`, which encloses `Σ_l (s ω)_l DK_{x l}` (`freqModel_encloses`,
`dkModels_encloses`). Each sup bound is `≤ e`, and the max norm of the error is the max of its
`2n` coordinates (`norm_sumVec`). Its two extra hypotheses are verbatim the conclusions of
`checkHamBounds_sound` and `checkEmbedding_sound`.
-/

public section

namespace KAM.Certificate

open KAM KAM.Torus CertArith

/-- Coordinate `x` of the Hamiltonian vector field is `± ∂_{x.swap} H`. -/
theorem sumVec_hamiltonianVectorFieldℂ {n : ℕ} (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) (x : Fin n ⊕ Fin n) :
    sumVec n (hamiltonianVectorFieldℂ H z) x = hamSign x * fderiv ℂ H z (phaseBasis x.swap) := by
  rcases x with i | i
  · simp [sumVec_apply, hamiltonianVectorFieldℂ, hamSign, phaseBasis_inr]
  · simp [sumVec_apply, hamiltonianVectorFieldℂ, hamSign, phaseBasis_inl]

/-- Coordinate `x` of `DK v` is `Σ_l v_l DK_{x l}`. -/
theorem sumVec_fderiv_apply {n : ℕ} (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (θ v : Fin n → ℂ) (x : Fin n ⊕ Fin n) :
    sumVec n (fderiv ℂ K θ v) x = ∑ l, v l * tangentMat K θ x l := by
  conv_lhs => rw [show v = ∑ l, v l • (Pi.single l 1 : Fin n → ℂ) by
    ext i; simp [Finset.sum_apply, Pi.single_apply]]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tangentMat_apply]

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

theorem dkFreqModel_encloses {W : CertWeight} {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (cfg : ModelConfig α) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    (K : CertEmbedding α) {box : FreqBox} {ω : Fin n → ℝ} (hω : FreqEncloses n box ω) (sc : ℚ)
    (x : Fin n ⊕ Fin n) :
    (dkFreqModel n K box sc W cfg pe (phaseNat x)).Encloses n W.rho
      (fun θ => ∑ l, ((((sc : ℝ) • ω) l : ℝ) : ℂ) * tangentMat (K.eval n) θ x l) := by
  let L : EnclosedList α n := List.ofFn fun l : Fin n =>
    (CertModel.mul W cfg [5, phaseNat x, l.val] (freqModel n box sc l.val)
      (modelMatrixEntry (dkModels n K W pe) (phaseNat x) l.val),
     fun θ => ((((sc : ℝ) • ω) l : ℝ) : ℂ) * tangentMat (K.eval n) θ x l)
  have hL : ∀ p ∈ L, p.1.Encloses n W.rho p.2 := by
    intro p hp
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).mp hp
    exact CertModel.Encloses.mul hW cfg _ (freqModel_encloses hω sc l)
      (dkModels_encloses hW hpe K x l)
  have := (modelSum_encloses hW hpe L hL).toDeg hW hpe 0
  have hfst : L.map Prod.fst = List.ofFn fun l : Fin n =>
      CertModel.mul W cfg [5, phaseNat x, l.val] (freqModel n box sc l.val)
        (modelMatrixEntry (dkModels n K W pe) (phaseNat x) l.val) := by
    simp only [L, List.map_ofFn]
    rfl
  rw [hfst] at this
  refine this.of_eq_fun fun θ => ?_
  simp only [L, List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- `checkInvariance_sound` with the conclusions of the Hamiltonian-bounds and embedding
contracts as hypotheses. -/
theorem checkInvariance_sound_of {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    (h : checkInvariance c = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err := by
  have S := checkStatic_sound hs
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  have hD := isOpen_certDomain n c.weightH.rho c.centre c.radius
  unfold checkInvariance at h
  split at h
  · rename_i ms hc
    obtain ⟨hlen, hm⟩ := Slp.compose_sound c.ham.jet.prog c.emb c.wit S.hW c.cfgFull S.hpe _ hc
    -- the composed slots
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
    -- every coordinate
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
    have hb := (LawfulCertArith.ble_sound _ _ (h _ (phaseNat_lt_add x))).trans
      (LawfulCertArith.ofRatDown_le _)
    exact (CertModel.norm_le_supBound S.hW (hcoord x) hθ).trans hb
  · exact absurd h (by simp)

theorem checkInvariance_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true)
    (h : checkInvariance c = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err :=
  checkInvariance_sound_of hs (checkHamBounds_sound hs hh) (checkEmbedding_sound hs he) h hω

end KAM.Certificate
