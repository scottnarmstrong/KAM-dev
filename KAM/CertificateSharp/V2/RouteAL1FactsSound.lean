/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAL1Facts

/-!
# Soundness of the ℓ¹ check (package C6L1)

`checkL1Claim_sound`: a passing `checkL1Claim c L` gives `L1Facts c L ωstar` for every `ω*` of
the box, under the facts the base sub-checks establish (`BaseFacts`) and the Diophantine premise
(which gives the standing hypotheses at `sω*`, hence the holomorphy and periodicity of `E` and of
the torsion).

* `invarianceModel_encloses`: the coordinates of `E` are enclosed by `invarianceModel` (the proof of
  the landed `checkInvariance_sound_of`, stated for one coordinate);
* `standingAt`: the standing hypotheses at `sω*` from `BaseFacts`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.CertificateSharp.V2.L1

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp CertArith KAM.Sharp2.L1 Matrix
  KAM.CertificateSharp.V2

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- The coordinates of the invariance error are enclosed by the models of `checkInvariance`. -/
theorem invarianceModel_encloses {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hnv : c.ham.NonvanishingOn c.D)
    (hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D) {ms : List (CertModel α)}
    (hc : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) = some ms)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) (x : Fin n ⊕ Fin n) :
    (invarianceModel n c.emb c.freqBox c.params.s c.weight c.cfgFull c.piEnc ms
      (phaseNat x)).Encloses n c.weight.rho
      (fun θ => sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ) x) := by
  have S := checkStatic_sound hs
  have hD := isOpen_certDomain n c.weightH.rho c.centre c.radius
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
    rw [this, c.ham.jet_d1 hD hnv (hKD θ hθ) y]
    rfl
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

/-- The standing hypotheses at `sω*`. -/
theorem standingAt {c : TorusCertificate n α} {ωstar : Fin n → ℝ} (B : BaseFacts c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) :
    KAM.Apost.Standing n (c.params.tau : ℝ) c.params.M c.params.σK c.params.σB c.params.σT c.D
      c.H ((c.params.s : ℝ) • ωstar) c.params.γ := by
  have S := checkStatic_sound B.hs
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  exact
    { toParams := ⟨S.hn, S.hτ, S.hM, S.hσK, S.hσB, S.hσT⟩
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := fun z hz => ⟨(B.hH.2 z hz).2.1, (B.hH.2 z hz).2.2.1, (B.hH.2 z hz).2.2.2.1⟩
      gamma_pos := S.hγ
      dio := KAM.Iso.Linear.isDiophantine_smul hdio S.hs1.le }

/-- The nonnegativity of a checked bound of nonnegative quantities. -/
theorem bound_nonneg {b : ℚ} {f : ℝ} (hf : 0 ≤ f) (h : f ≤ b) : (0 : ℝ) ≤ b := hf.trans h

/-- **Soundness of the ℓ¹ check.** -/
theorem checkL1Claim_sound {c : TorusCertificate n α} {L : L1Claim} {ωstar : Fin n → ℝ}
    (B : BaseFacts c ωstar) (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar)
    (h : checkL1Claim c L = true) : L1Facts c L ωstar := by
  have S := checkStatic_sound B.hs
  simp only [checkL1Claim, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hW1, hWT⟩, hr1⟩, hrT⟩, hL⟩, hN⟩, hT⟩, hE⟩ := h
  have hn1 : 1 ≤ n := by have := S.hn; omega
  have j0 : Fin n := ⟨0, hn1⟩
  have hrw : c.weight.rho = c.params.rho := S.hrho
  have hr1w : L.W1.rho < c.weight.rho := by rw [hrw]; exact hr1
  have hrTw : L.WT.rho < c.weight.rho := by rw [hrw]; exact hrT
  have hK : Differentiable ℂ c.K := CertEmbedding.differentiable_eval n c.emb
  have hKp : ∀ r, IsPrimaryOnStrip c.K r := fun r => CertEmbedding.isPrimaryOnStrip n c.emb r
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.K θ ∈ c.D := fun θ hθ => by
    rw [hrw] at hθ; exact B.hEm.1 θ hθ (Metric.mem_ball_self S.hμ)
  have hGu : ∀ θ ∈ complexStrip n c.weight.rho, IsUnit (gramMatrix c.K θ).det := fun θ hθ => by
    rw [hrw] at hθ; exact (B.hG θ hθ).1
  have hSt := standingAt B hdio
  have hρ1 : (0 : ℝ) < L.W1.rho := CertWeight.rho_pos hW1
  have hρT : (0 : ℝ) < L.WT.rho := CertWeight.rho_pos hWT
  have hcw : cothPowUp n (c.weight.rho - L.W1.rho) = cothPowUp n (c.params.rho - L.W1.rho) := by
    rw [hrw]
  have hcwT : cothPowUp n (c.weight.rho - L.WT.rho) = cothPowUp n (c.params.rho - L.WT.rho) := by
    rw [hrw]
  -- `L`
  have hdk := dkModels_encloses (n := n) S.hW S.hpe c.emb
  have hLd : DifferentiableOn ℂ (tangentMat c.K) (complexStrip n c.weight.rho) :=
    differentiableOn_tangentMat hK.differentiableOn
  have hLp : IsPeriodicOn (tangentMat c.K) c.weight.rho := KAM.Apost.periodic_tangentMat (hKp _)
  have hLe := entry_l1 hdk hLd hLp hW1 hr1w
  rw [hcw] at hLe
  simp only [checkL1L, Bool.and_eq_true] at hL
  obtain ⟨hLc, hLr⟩ := hL
  have hLcol : ∀ j : Fin n, ∑ a, val (l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
      (modelMatrixEntry (dkModels n c.emb c.weight c.piEnc) (phaseNat a) j.val)) ≤ L.aLt :=
    fun j => sumsOk_col hLc j fun a => le_rfl
  have hLrow : ∀ a, ∑ j : Fin n, val (l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
      (modelMatrixEntry (dkModels n c.emb c.weight c.piEnc) (phaseNat a) j.val)) ≤ L.nuK :=
    fun a => sumsOk_row hLr a fun j => le_rfl
  have hLnn : ∀ a (j : Fin n), 0 ≤ val (l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
      (modelMatrixEntry (dkModels n c.emb c.weight c.piEnc) (phaseNat a) j.val)) :=
    fun a j => (weightedNorm_nonneg _ _).trans (hLe a j).2
  -- `N`
  unfold checkL1N at hN
  split at hN
  · rename_i δβ hG
    split at hN
    · rename_i eps heps
      simp only [Bool.and_eq_true] at hN
      obtain ⟨hNc, hNr⟩ := hN
      have hNe0 := frameNModels_encloses hn1 S.hW c.emb c.gramInv c.cfgLow S.hpe hG heps
      have heq : (fun θ => omegaZeroMatrix n * (tangentMat (c.emb.eval n) θ *
          (gramMatrix (c.emb.eval n) θ)⁻¹)) = normalMat c.K := funext fun θ => by
        simp only [normalMat, Matrix.mul_assoc]; rfl
      rw [heq] at hNe0
      have hNd : DifferentiableOn ℂ (normalMat c.K) (complexStrip n c.weight.rho) :=
        differentiableOn_normalMat hK.differentiableOn hGu
      have hNp : IsPeriodicOn (normalMat c.K) c.weight.rho := KAM.Apost.periodic_normalMat (hKp _)
      have hNe := entry_l1 hNe0 hNd hNp hW1 hr1w
      rw [hcw] at hNe
      have hNnn : ∀ a (j : Fin n), 0 ≤ val (l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
          (modelMatrixEntry (frameNModels n c.emb c.gramInv eps c.weight c.cfgLow c.piEnc)
            (phaseNat a) j.val)) :=
        fun a j => (weightedNorm_nonneg _ _).trans (hNe a j).2
      -- the torsion
      unfold checkL1T at hT
      simp only [show frameGram c = some δβ from hG] at hT
      split at hT
      · rename_i T hTm
        have hTs := torsionModels_sound hn1 (isOpen_certDomain n c.weightH.rho c.centre c.radius)
          B.hH.1 S.hW hKD c.wit c.gramInv c.cfgLow S.hpe hG c.freqBox c.params.s hTm hω
        have hTe0 : T.EntryEncloses n c.weight.rho Fin.val Fin.val
            (torsion c.H c.K ((c.params.s : ℝ) • ωstar)) := by
          intro i j
          obtain ⟨m, hm, hme⟩ := hTs.2.1 (Sum.inl i) (Sum.inl j)
          have e : modelMatrixEntry T i.val j.val = m := by
            unfold modelMatrixEntry
            simp only [torsionIdx, Sum.elim_inl] at hm
            rw [hm]; rfl
          rw [e]
          exact hme
        have hlin := KAM.Apost.FrameAux.differentiableOn_linMat hSt hK.differentiableOn hKD
        have hTd : DifferentiableOn ℂ (torsion c.H c.K ((c.params.s : ℝ) • ωstar))
            (complexStrip n c.weight.rho) :=
          KAM.Apost.FrameAux.differentiableOn_torsion hNd
            (KAM.Apost.FrameAux.differentiableOn_normalFieldMat hlin hNd)
        have hTp : IsPeriodicOn (torsion c.H c.K ((c.params.s : ℝ) • ωstar)) c.weight.rho :=
          KAM.Apost.periodic_torsion hSt hKD (hKp _) hK.differentiableOn hGu
        have hTe := entry_l1 hTe0 hTd hTp hWT hrTw
        rw [hcwT] at hTe
        simp only [List.all_eq_true, List.mem_finRange, true_implies] at hT
        have hTrow : ∀ i : Fin n, ∑ j : Fin n, val (l1Up L.WT
            (cothPowUp n (c.params.rho - L.WT.rho)) (modelMatrixEntry T i.val j.val)) ≤ L.t1 :=
          fun i => sum_fin_le (g := fun k => l1Up L.WT (cothPowUp n (c.params.rho - L.WT.rho))
            (modelMatrixEntry T i.val k)) (hT i) fun j => le_rfl
        -- the invariance error
        unfold checkL1E at hE
        split at hE
        · rename_i ms hms
          simp only [List.all_eq_true, List.mem_finRange, true_implies] at hE
          have hEd : DifferentiableOn ℂ (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar))
              (complexStrip n c.weight.rho) :=
            KAM.Apost.FrameAux.differentiableOn_invarianceError hSt hK.differentiableOn hKD
          have hEp : IsPeriodicOn (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar))
              c.weight.rho := KAM.Apost.periodic_invarianceError hSt hKD (hKp _)
          have hvd : DifferentiableOn ℂ
              (fun θ => sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ))
              (complexStrip n c.weight.rho) := by
            exact (sumVecIso n).differentiable.comp_differentiableOn hEd
          have hEe : ∀ x : Fin n ⊕ Fin n, Fourier.SummableWeighted (2 * Real.pi * L.W1.rho)
                (coeffR (fun θ => sumVec n (invarianceError c.H c.K
                  ((c.params.s : ℝ) • ωstar) θ)) x) ∧
              Fourier.weightedNorm (2 * Real.pi * L.W1.rho)
                (coeffR (fun θ => sumVec n (invarianceError c.H c.K
                  ((c.params.s : ℝ) • ωstar) θ)) x) ≤ L.aE := fun x => by
            have hm := invarianceModel_encloses B.hs B.hH.1 hKD hms hω x
            have hd : DifferentiableOn ℂ
                (fun θ => sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ) x)
                (complexStrip n c.weight.rho) := differentiableOn_pi.mp hvd x
            have hp : IsPeriodicOn
                (fun θ => sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ) x)
                c.weight.rho := fun l z hz => by
              show sumVec n _ x = sumVec n _ x
              rw [hEp l z hz]
            have hb := weightedNorm_le_l1Up (C := cothPowUp n (c.weight.rho - L.W1.rho))
              (f := fun θ => sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ) x)
              hW1 hr1w (le_refl _) hd hp hm
            rw [hcw] at hb
            have hk := hE (finSumFinEquiv x)
            have e : (finSumFinEquiv x).val = phaseNat x := by
              simpa using (phaseNat_finSumFinEquiv_symm (finSumFinEquiv x)).symm
            rw [e] at hk
            exact ⟨hb.1, hb.2.trans (ble_le hk)⟩
          have haE : (0 : ℝ) ≤ L.aE := (weightedNorm_nonneg _ _).trans (hEe (Sum.inl j0)).2
          refine
            { rho1 := ⟨hρ1, by exact_mod_cast hr1⟩
              rhoT := hρT
              err := ⟨haE, hEe⟩
              lt := l1Mat_transpose_omega
                ((Finset.sum_nonneg fun a _ => hLnn a j0).trans (hLcol j0)) hLe hLcol
              nt := l1Mat_transpose_omega
                ((Finset.sum_nonneg fun a _ => hNnn a j0).trans
                  (sumsOk_col hNc j0 fun a => le_rfl)) hNe (fun j => sumsOk_col hNc j fun a => le_rfl)
              nuK := l1Mat_of ((Finset.sum_nonneg fun j _ => hLnn (Sum.inl j0) j).trans
                (hLrow (Sum.inl j0))) hLe hLrow
              nuN := l1Mat_of ((Finset.sum_nonneg fun j _ => hNnn (Sum.inl j0) j).trans
                (sumsOk_row hNr (Sum.inl j0) fun j => le_rfl)) hNe
                (fun a => sumsOk_row hNr a fun j => le_rfl)
              tors := l1Mat_of ((Finset.sum_nonneg fun j _ =>
                  (weightedNorm_nonneg _ _).trans (hTe j0 j).2).trans (hTrow j0)) hTe hTrow }
        · exact absurd hE (by simp)
      · exact absurd hT (by simp)
    · exact absurd hN (by simp)
  · exact absurd hN (by simp)

end KAM.CertificateSharp.V2.L1

end
