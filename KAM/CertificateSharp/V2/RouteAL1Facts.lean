/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAL1Bridge
public import KAM.CertificateSharp.V2.Engine
public import KAM.CertificateSharp.Frame.Majorants
public import KAM.Certificate.Sound.Invariance
public import KAM.Apost.Periodicity
public import KAM.Apost.Frame
public import KAM.Iso.Linear.Tools
public import KAM.Torus.FrozenAgreement
public import KAM.Sharp2.L1.NormsProduct

/-!
# The ℓ¹ data of the torus from the certificate's own models (package C6L1)

`checkL1Claim c L` computes, from the models the certifier builds, weighted ℓ¹ bounds of the
objects of the ℓ¹ entry on the strip `T_{ρ'}`, `ρ' = L.W1.rho < ρ` (the torsion on
`T_{L.WT.rho}`), and compares them with the claim `L`:

* the coordinates of `E = X_H ∘ K - DK sω` (the models of `checkInvariance`, one composition);
* the entries of `L = DK` (`dkModels`) and of `N = Ω₀ L G⁻¹` (C4's `frameNModels`, from the Gram
  witness), as column sums (for `Lᵀ Ω₀`, `Nᵀ Ω₀`) and row sums (the frame certificate);
* the entries of the torsion block of `torsionModels`, as row sums.

Each bound is `l1Up`: the polynomial part exactly, the remainder times `cothPowUp n (ρ - ρ')`
(C5CORE's `Encloses.toL1`). `checkL1Claim_sound` turns a passing check into `L1Facts`, statements
on the objects of `c` at `sω*` with no smallness. `ηᴺ = Lᵀ Ω₀ E` and `ηᴸ = -Nᵀ Ω₀ E` are then
bounded by Wiener products (`KAM.Sharp2.L1.L1Mat.mulVec`) in `V2/RouteAL1.lean`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.CertificateSharp.V2.L1

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp CertArith KAM.Sharp2.L1 Matrix

variable {n : ℕ} {α : Type} [CertArith α]

/-- The claimed ℓ¹ bounds: `E` coordinatewise (`aE`), the column sums of `L` (`aLt`) and of `N`
(`aNt`), the row sums of `L` (`nuK`) and of `N` (`nuN`) on `T_{W1.rho}`, and the row sums of the
torsion (`t1`) on `T_{WT.rho}`. -/
structure L1Claim where
  /-- The weight of the strip of the entry. -/
  W1 : CertWeight
  /-- The weight of the strip of the torsion. -/
  WT : CertWeight
  aE : ℚ
  aLt : ℚ
  aNt : ℚ
  nuK : ℚ
  nuN : ℚ
  t1 : ℚ

/-- The column sums (`col = true`) or the row sums of a `2n × n` matrix of ℓ¹ bounds. -/
def sumsOk (lv : ℕ → ℕ → α) (b : ℚ) (col : Bool) : Bool :=
  if col then (List.finRange n).all fun j =>
      ble (sumUp (fun a : Fin (n + n) => lv a.val j.val) (List.finRange (n + n))) (ofRatDown b)
  else (List.finRange (n + n)).all fun a =>
      ble (sumUp (fun j : Fin n => lv a.val j.val) (List.finRange n)) (ofRatDown b)

/-- The ℓ¹ bounds of `L = DK`. -/
def checkL1L (c : TorusCertificate n α) (L : L1Claim) : Bool :=
  let lv : ℕ → ℕ → α := fun a j => l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
    (modelMatrixEntry (dkModels n c.emb c.weight c.piEnc) a j)
  sumsOk (n := n) lv L.aLt true && sumsOk (n := n) lv L.nuK false

/-- The ℓ¹ bounds of `N`. -/
def checkL1N (c : TorusCertificate n α) (L : L1Claim) : Bool :=
  match frameGram c with
  | some δβ =>
    match gramInvRadius δβ with
    | some eps =>
      let lv : ℕ → ℕ → α := fun a j => l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
        (modelMatrixEntry (frameNModels n c.emb c.gramInv eps c.weight c.cfgLow c.piEnc) a j)
      sumsOk (n := n) lv L.aNt true && sumsOk (n := n) lv L.nuN false
    | none => false
  | none => false

/-- The ℓ¹ bounds of the torsion block. -/
def checkL1T (c : TorusCertificate n α) (L : L1Claim) : Bool :=
  match frameGram c with
  | some δβ =>
    match torsionModels n c.ham c.emb c.wit c.gramInv δβ c.freqBox c.params.s c.weight c.cfgLow
        c.piEnc with
    | some T => (List.finRange n).all fun i =>
        ble (sumUp (fun j : Fin n => l1Up L.WT (cothPowUp n (c.params.rho - L.WT.rho))
          (modelMatrixEntry T i.val j.val)) (List.finRange n)) (ofRatDown L.t1)
    | none => false
  | none => false

/-- The ℓ¹ bounds of the coordinates of the invariance error. -/
def checkL1E (c : TorusCertificate n α) (L : L1Claim) : Bool :=
  match Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) with
  | some ms => (List.finRange (n + n)).all fun a =>
      ble (l1Up L.W1 (cothPowUp n (c.params.rho - L.W1.rho))
        (invarianceModel n c.emb c.freqBox c.params.s c.weight c.cfgFull c.piEnc ms a.val))
        (ofRatDown L.aE)
  | none => false

/-- **The ℓ¹ check.** -/
def checkL1Claim (c : TorusCertificate n α) (L : L1Claim) : Bool :=
  checkWeight L.W1 c.expHalvings c.expOrder && checkWeight L.WT c.expHalvings c.expOrder &&
    decide (L.W1.rho < c.params.rho) && decide (L.WT.rho < c.params.rho) &&
    checkL1L c L && checkL1N c L && checkL1T c L && checkL1E c L

/-- The ℓ¹ data of `c` at `ω*`, on `T_{W1.rho}` (the torsion on `T_{WT.rho}`). -/
structure L1Facts (c : TorusCertificate n α) (L : L1Claim) (ωstar : Fin n → ℝ) : Prop where
  rho1 : (0 : ℝ) < L.W1.rho ∧ (L.W1.rho : ℝ) < c.params.rho
  rhoT : (0 : ℝ) < L.WT.rho
  err : L1Vec (L.W1.rho : ℝ)
    (fun θ => sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ)) L.aE
  lt : L1Mat (L.W1.rho : ℝ) (fun θ => (tangentMat c.K θ)ᵀ * omegaZeroMatrix n) L.aLt
  nt : L1Mat (L.W1.rho : ℝ) (fun θ => (normalMat c.K θ)ᵀ * omegaZeroMatrix n) L.aNt
  nuK : L1Mat (L.W1.rho : ℝ) (tangentMat c.K) L.nuK
  nuN : L1Mat (L.W1.rho : ℝ) (normalMat c.K) L.nuN
  tors : L1Mat (L.WT.rho : ℝ) (torsion c.H c.K ((c.params.s : ℝ) • ωstar)) L.t1

/-! ### Sums and entries -/

section Lemmas

variable [LawfulCertArith α]

theorem ble_le {x : α} {b : ℚ} (h : ble x (ofRatDown b) = true) : val x ≤ b :=
  (LawfulCertArith.ble_sound _ _ h).trans (LawfulCertArith.ofRatDown_le _)

/-- A sum over the phase indices of a checked bound. -/
theorem sum_phase_le {g : ℕ → α} {b : ℚ}
    (h : ble (sumUp (fun a : Fin (n + n) => g a.val) (List.finRange (n + n))) (ofRatDown b) = true)
    {f : Fin n ⊕ Fin n → ℝ} (hf : ∀ a, f a ≤ val (g (phaseNat a))) : ∑ a, f a ≤ b := by
  have e : ∑ a : Fin n ⊕ Fin n, f a = ∑ k : Fin (n + n), f (finSumFinEquiv.symm k) :=
    (Equiv.sum_comp finSumFinEquiv.symm f).symm
  rw [e, Fin.sum_univ_def]
  refine (List.sum_le_sum fun k _ => ?_).trans ((sumUp_ge _ _).trans (ble_le h))
  have := hf (finSumFinEquiv.symm k)
  rwa [phaseNat_finSumFinEquiv_symm] at this

/-- A sum over `Fin n` of a checked bound. -/
theorem sum_fin_le {g : ℕ → α} {b : ℚ}
    (h : ble (sumUp (fun j : Fin n => g j.val) (List.finRange n)) (ofRatDown b) = true)
    {f : Fin n → ℝ} (hf : ∀ j, f j ≤ val (g j.val)) : ∑ j, f j ≤ b := by
  rw [Fin.sum_univ_def]
  exact (List.sum_le_sum fun j _ => hf j).trans ((sumUp_ge _ _).trans (ble_le h))

theorem sumsOk_col {lv : ℕ → ℕ → α} {b : ℚ} (h : sumsOk (n := n) lv b true = true) (j : Fin n)
    {f : Fin n ⊕ Fin n → ℝ} (hf : ∀ a, f a ≤ val (lv (phaseNat a) j.val)) : ∑ a, f a ≤ b := by
  simp only [sumsOk, ite_true, List.all_eq_true, List.mem_finRange, true_implies] at h
  exact sum_phase_le (g := fun k => lv k j.val) (h j) hf

theorem sumsOk_row {lv : ℕ → ℕ → α} {b : ℚ} (h : sumsOk (n := n) lv b false = true)
    (a : Fin n ⊕ Fin n) {f : Fin n → ℝ} (hf : ∀ j, f j ≤ val (lv (phaseNat a) j.val)) :
    ∑ j, f j ≤ b := by
  simp only [sumsOk, Bool.false_eq_true, ite_false, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  have := h (finSumFinEquiv a)
  have e : (finSumFinEquiv a).val = phaseNat a := by
    simpa using (phaseNat_finSumFinEquiv_symm (finSumFinEquiv a)).symm
  rw [e] at this
  exact sum_fin_le (g := fun k => lv (phaseNat a) k) this hf

/-- The certified ℓ¹ bound of an entry of an entrywise-enclosed matrix. -/
theorem entry_l1 {ι κ : Type*} [Fintype ι] [Fintype κ] {M : ModelMatrix α} {ri : ι → ℕ}
    {ci : κ → ℕ} {F : (Fin n → ℂ) → Matrix ι κ ℂ} {ρ : ℚ} (hM : M.EntryEncloses n ρ ri ci F)
    (hFd : DifferentiableOn ℂ F (complexStrip n ρ)) (hFp : IsPeriodicOn F ρ) {W' : CertWeight}
    {s N : ℕ} (hW' : checkWeight W' s N = true) (hρ : W'.rho < ρ) (i : ι) (j : κ) :
    Fourier.SummableWeighted (2 * Real.pi * W'.rho)
        (torusCoeff fun x => F (fun l => (x l : ℂ)) i j) ∧
      Fourier.weightedNorm (2 * Real.pi * W'.rho)
        (torusCoeff fun x => F (fun l => (x l : ℂ)) i j) ≤
        val (l1Up W' (cothPowUp n (ρ - W'.rho)) (modelMatrixEntry M (ri i) (ci j))) := by
  have hd : DifferentiableOn ℂ (fun z => F z i j) (complexStrip n ρ) :=
    differentiableOn_entry hFd i j
  have hp : IsPeriodicOn (fun z => F z i j) ρ := fun l z hz => by
    show F (z + Pi.single l 1) i j = F z i j
    rw [hFp l z hz]
  have hm : (modelMatrixEntry M (ri i) (ci j)).Encloses n ρ (fun z => F z i j) := hM i j
  exact weightedNorm_le_l1Up (C := cothPowUp n (ρ - W'.rho)) (f := fun z => F z i j)
    (m := modelMatrixEntry M (ri i) (ci j)) hW' hρ (le_refl _) hd hp hm

/-- `L1Mat` from entrywise bounds with checked row sums. -/
theorem l1Mat_of {ι κ : Type*} [Fintype κ] {r A : ℝ} {M : (Fin n → ℂ) → Matrix ι κ ℂ}
    {b : ι → κ → ℝ} (hA : 0 ≤ A)
    (hb : ∀ i j, Fourier.SummableWeighted (2 * Real.pi * r)
        (torusCoeff fun x => M (fun l => (x l : ℂ)) i j) ∧
      Fourier.weightedNorm (2 * Real.pi * r) (torusCoeff fun x => M (fun l => (x l : ℂ)) i j) ≤
        b i j)
    (hrow : ∀ i, ∑ j, b i j ≤ A) : L1Mat r M A :=
  ⟨hA, fun i j => (hb i j).1, fun i => (Finset.sum_le_sum fun j _ => (hb i j).2).trans (hrow i)⟩

/-- `L1Mat` of `Fᵀ Ω₀` from entrywise bounds of `F` with bounded column sums. -/
theorem l1Mat_transpose_omega {r A : ℝ} {F : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}
    {b : Fin n ⊕ Fin n → Fin n → ℝ} (hA : 0 ≤ A)
    (hb : ∀ a j, Fourier.SummableWeighted (2 * Real.pi * r)
        (torusCoeff fun x => F (fun l => (x l : ℂ)) a j) ∧
      Fourier.weightedNorm (2 * Real.pi * r) (torusCoeff fun x => F (fun l => (x l : ℂ)) a j) ≤
        b a j)
    (hcol : ∀ j, ∑ a, b a j ≤ A) : L1Mat r (fun θ => (F θ)ᵀ * omegaZeroMatrix n) A := by
  have hl : ∀ (j i : Fin n), (torusCoeff fun x => ((F fun l => (x l : ℂ))ᵀ * omegaZeroMatrix n)
      j (Sum.inl i)) = torusCoeff fun x => F (fun l => (x l : ℂ)) (Sum.inr i) j := fun j i => by
    simp only [mul_omegaZeroMatrix_apply_inl, Matrix.transpose_apply]
  have hr : ∀ (j i : Fin n), (torusCoeff fun x => ((F fun l => (x l : ℂ))ᵀ * omegaZeroMatrix n)
      j (Sum.inr i)) = fun k => -torusCoeff (fun x => F (fun l => (x l : ℂ)) (Sum.inl i) j) k :=
    fun j i => by
      funext k
      simp only [mul_omegaZeroMatrix_apply_inr, Matrix.transpose_apply]
      exact torusCoeff_neg' _ k
  refine ⟨hA, fun j c => ?_, fun j => ?_⟩
  · rcases c with i | i
    · rw [hl]; exact (hb _ _).1
    · rw [hr]; exact summableWeighted_neg (hb _ _).1
  · rw [Fintype.sum_sum_type]
    simp only [hl, hr, weightedNorm_neg]
    refine le_trans ?_ (hcol j)
    rw [Fintype.sum_sum_type, add_comm]
    exact add_le_add (Finset.sum_le_sum fun i _ => (hb _ _).2)
      (Finset.sum_le_sum fun i _ => (hb _ _).2)

end Lemmas

end KAM.CertificateSharp.V2.L1

end
