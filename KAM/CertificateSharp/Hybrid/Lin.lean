/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.Step
public import KAM.CertificateSharp.V2.RouteAL1FactsSound

/-!
# The model of the linearised new error `Ẽ` (package C8c)

`Ẽ_s = E(K, s₁ω*) + DX_H(K) ΔK − DΔK · s₁ω*` (`KAM.Sharp2.Hybrid.linNewError` at `s₁ω*`). Its model,
coordinate by coordinate:

* `E(K, s₁ω*)`: the invariance model of the certifier at the scale `s₁` (`invarianceModel`, from the
  composition of the first derivatives of `H` along `K`, `ms`);
* `DX_H(K) ΔK`: the composed models of `DX_H ∘ K` (`dxhModels`, from the composition with the second
  derivatives, `mt`) times the exact models of `ΔK`, as one `dotModel`;
* `DΔK · s₁ω*`: the frequency models times the derivative models of `ΔK`.

The three are added by `addMixed`, whose sums merge the coefficients of equal key, so the Newton
cancellation between `E` and `DX_H ΔK − DΔK ω` happens on the coefficients, before any norm.

* `invarianceModel_encloses_at`: the landed invariance enclosure at any scale `s₁`;
* `linModel`, `linModel_encloses`, `linOk`, `linNewError_le` (`(S5)`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.CertificateSharp.Hybrid

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp CertArith Matrix
open KAM.CertificateSharp.V2.L1 (ble_le)

variable {n : ℕ} {α : Type} [CertArith α]

/-- The model of coordinate `a` of `Ẽ` at `s₁ω*`: `ms` is the composition of `checkInvariance`
(first derivatives of `H`), `mt` the composition of `checkTorsion` (with the second derivatives). -/
def linModel (c : TorusCertificate n α) (s₁ : ℚ) (dK : CertEmbedding α)
    (ms mt : List (CertModel α)) (a : ℕ) : CertModel α :=
  CertModel.addMixed c.weight c.piEnc
    (CertModel.addMixed c.weight c.piEnc
      (invarianceModel n c.emb c.freqBox s₁ c.weight c.cfgFull c.piEnc ms a)
      (dotModel c.weight c.cfgFull c.piEnc (n + n) (fun b => modelMatrixEntry (dxhModels n mt) a b)
        (fun b => stepModel n dK b)))
    (dotModel c.weight c.cfgFull c.piEnc n (fun l => freqModel n c.freqBox s₁ l)
      (fun l => dstepModel n c.weight c.piEnc dK a l)).negM

/-- `‖Ẽ‖ ≤ lE` on the strip of `W1` from the models. -/
def linOk (c : TorusCertificate n α) (W1 : CertWeight) (s₁ : ℚ) (dK : CertEmbedding α)
    (ms mt : List (CertModel α)) (lE : ℚ) : Bool :=
  decide (0 ≤ lE) && (List.finRange (n + n)).all fun a =>
    ble ((linModel c s₁ dK ms mt a.val).supBound W1) (ofRatDown lE)

variable [LawfulCertArith α]

/-- The coordinates of the invariance error at the scale `s₁` (the proof of the landed
`checkInvariance_sound_of`, at any scale). -/
theorem invarianceModel_encloses_at {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hnv : c.ham.NonvanishingOn c.D)
    (hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D) {ms : List (CertModel α)}
    (hc : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) = some ms)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) (s₁ : ℚ) (x : Fin n ⊕ Fin n) :
    (invarianceModel n c.emb c.freqBox s₁ c.weight c.cfgFull c.piEnc ms
      (phaseNat x)).Encloses n c.weight.rho
      (fun θ => sumVec n (invarianceError c.H c.K ((s₁ : ℝ) • ωstar) θ) x) := by
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
  have hdk := (dkFreqModel_encloses S.hW c.cfgFull S.hpe c.emb hω s₁ x).negM
  have hfun : ∀ θ, sumVec n (invarianceError c.H c.K ((s₁ : ℝ) • ωstar) θ) x =
      hamSign x * fderiv ℂ c.H (c.K θ) (phaseBasis x.swap) +
        -∑ l, ((((s₁ : ℝ) • ωstar) l : ℝ) : ℂ) * tangentMat (c.emb.eval n) θ x l := by
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

/-- **The model of `Ẽ`.** -/
theorem linModel_encloses {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hnv : c.ham.NonvanishingOn c.D)
    (hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D) {ms mt : List (CertModel α)}
    (hc : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) = some ms)
    (ht : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
      (torsionSlots n c.ham.jet) = some mt)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) (s₁ : ℚ) (dK : CertEmbedding α)
    (x : Fin n ⊕ Fin n) :
    (linModel c s₁ dK ms mt (phaseNat x)).Encloses n c.weight.rho
      (fun θ => sumVec n (KAM.Sharp2.Hybrid.linNewError c.H c.K (stepFun n dK)
        ((s₁ : ℝ) • ωstar) θ) x) := by
  have S := checkStatic_sound hs
  have hD := isOpen_certDomain n c.weightH.rho c.centre c.radius
  have hE := invarianceModel_encloses_at hs hnv hKD hc hω s₁ x
  -- `DX_H(K) ΔK`
  have hms : SlotsEnclose n c.ham c.emb c.weight.rho mt := by
    have := Slp.compose_sound c.ham.jet.prog c.emb c.wit S.hW c.cfgLow S.hpe _ ht
    exact ⟨this.1, this.2⟩
  have hdx := dxhModels_encloses hD hnv hKD hms
  have hP := dotModel_encloses S.hW c.cfgFull S.hpe (n + n)
    (a := fun b => modelMatrixEntry (dxhModels n mt) (phaseNat x) b)
    (b := fun b => stepModel n dK b)
    (fa := fun b θ => linMat c.H c.K θ x (finSumFinEquiv.symm b))
    (fb := fun b θ => sumVec n (stepFun n dK θ) (finSumFinEquiv.symm b))
    (fun b => by
      have := hdx x (finSumFinEquiv.symm b)
      rwa [phaseNat_finSumFinEquiv_symm] at this)
    (fun b => by
      have := stepModel_encloses dK c.weight.rho (finSumFinEquiv.symm b)
      rwa [phaseNat_finSumFinEquiv_symm] at this)
  -- `DΔK · s₁ω*`
  have hQ := dotModel_encloses S.hW c.cfgFull S.hpe n
    (a := fun l => freqModel n c.freqBox s₁ l) (b := fun l => dstepModel n c.weight c.piEnc dK
      (phaseNat x) l)
    (fa := fun l _ => ((((s₁ : ℝ) • ωstar) l : ℝ) : ℂ))
    (fb := fun l θ => tangentMat (stepFun n dK) θ x l)
    (fun l => freqModel_encloses hω s₁ l) (fun l => dstepModel_encloses S.hW S.hpe dK x l)
  have hsum := (hE.addMixed S.hW S.hpe hP).addMixed S.hW S.hpe hQ.negM
  refine hsum.of_eq_fun fun θ => ?_
  have h1 : ∑ b : Fin (n + n), linMat c.H c.K θ x (finSumFinEquiv.symm b) *
      sumVec n (stepFun n dK θ) (finSumFinEquiv.symm b) =
      sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ c.H) (c.K θ) (stepFun n dK θ)) x := by
    rw [← sqMat_mulVec]
    rw [Equiv.sum_comp finSumFinEquiv.symm (fun y => linMat c.H c.K θ x y *
      sumVec n (stepFun n dK θ) y)]
    rfl
  have h2 : ∑ l, ((((s₁ : ℝ) • ωstar) l : ℝ) : ℂ) * tangentMat (stepFun n dK) θ x l =
      sumVec n (fderiv ℂ (stepFun n dK) θ (fun i => ((((s₁ : ℝ) • ωstar) i : ℝ) : ℂ))) x :=
    (sumVec_fderiv_apply _ θ _ x).symm
  simp only [Pi.add_apply]
  rw [h1, h2]
  simp only [KAM.Sharp2.Hybrid.linNewError, map_add, map_sub, Pi.add_apply, Pi.sub_apply]
  ring

/-- **`(S5)`: `‖Ẽ‖ ≤ ℓ_E` on `T_{ρ₁}`.** -/
theorem linNewError_le {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hnv : c.ham.NonvanishingOn c.D)
    (hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D) {ms mt : List (CertModel α)}
    (hc : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) = some ms)
    (ht : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
      (torsionSlots n c.ham.jet) = some mt)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) {W1 : CertWeight} {s' N' : ℕ}
    (hW1 : checkWeight W1 s' N' = true) (hρ : W1.rho ≤ c.weight.rho) {s₁ : ℚ}
    {dK : CertEmbedding α} {lE : ℚ} (h : linOk c W1 s₁ dK ms mt lE = true) :
    ∀ θ ∈ complexStrip n W1.rho, ‖KAM.Sharp2.Hybrid.linNewError c.H c.K (stepFun n dK)
      ((s₁ : ℝ) • ωstar) θ‖ ≤ lE := by
  intro θ hθ
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  refine norm_pair_le (by exact_mod_cast h.1) fun x => ?_
  have hb := h.2 (finSumFinEquiv x)
  rw [fin_of_phase] at hb
  have hm := linModel_encloses hs hnv hKD hc ht hω s₁ dK x
  have hm' : (linModel c s₁ dK ms mt (phaseNat x)).Encloses n W1.rho
      (fun θ => sumVec n (KAM.Sharp2.Hybrid.linNewError c.H c.K (stepFun n dK)
        ((s₁ : ℝ) • ωstar) θ) x) := fun θ' hθ' =>
    hm θ' (fun i => (hθ' i).trans_le (by exact_mod_cast hρ))
  exact (CertModel.norm_le_supBound hW1 hm' hθ).trans (ble_le hb)

end KAM.CertificateSharp.Hybrid

end
