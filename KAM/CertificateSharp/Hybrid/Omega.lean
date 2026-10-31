/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.Lin

/-!
# The local data `Ω_K`, `Ω_{K₁}` and the linearised energy error (package C8c)

* `lagModel`, `lagModel_encloses`: `Ω_M = Mᵀ Ω₀ M` entrywise from entry models of `M`, with
  `(Ω₀ M)_{a j} = ∓ M_{swap a, j}`; one merged `dotModel` per entry (exact polynomial products
  when the entries of `M` are exact, as for a polynomial embedding);
* `dkM`, `dk1M`: the entry models of `DK` (`dkModels`) and of `D(K + ΔK) = DK + DΔK`;
* `omegaOk`, `lagrangeMat_le`, `lagrangeMat_real_le`: `‖Ω‖ ≤ o` on a strip and on the real torus
  (`(S6)`, `(S7)`: `o₀`, `o₀ᴿ` for `K`, `o₁`, `o₁ᴿ` for `K₁`);
* `enModel`, `energyLinOk`, `linNewEnergy_le`: `|⟨H∘K⟩ - E₀ + ⟨DH(K)ΔK⟩| ≤ ℓ_H` (iso), the zero
  mode of one merged model of `H∘K - E₀ + DH(K)ΔK` plus its radius.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.CertificateSharp.Hybrid

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp CertArith Matrix
open KAM.CertificateSharp.V2.L1 (ble_le sum_fin_le)

variable {n : ℕ} {α : Type} [CertArith α]

/-! ### `Ω_M = Mᵀ Ω₀ M` -/

/-- The entry `(a, j)` of `Ω₀ M` from entry models of `M` (phase rows): `-M_{n+i, j}` on the
angle rows, `M_{i, j}` on the action rows. -/
def omegaRow (n : ℕ) (Mm : ℕ → ℕ → CertModel α) (a j : ℕ) : CertModel α :=
  if a < n then (Mm (a + n) j).negM else Mm (a - n) j

/-- The entry `(i, j)` of `Mᵀ Ω₀ M`. -/
def lagModel (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (Mm : ℕ → ℕ → CertModel α) (i j : ℕ) : CertModel α :=
  dotModel W cfg pe (n + n) (fun a => Mm a i) (fun a => omegaRow n Mm a j)

/-- The entry models of `DK`, built at the weight `W` (exact for a polynomial embedding; the
weight only enters the rounding radii, so it is the weight of the strip to be bounded). -/
def dkM (c : TorusCertificate n α) (W : CertWeight) : ℕ → ℕ → CertModel α :=
  fun a j => modelMatrixEntry (dkModels n c.emb W c.piEnc) a j

/-- The entry models of `D(K + ΔK)`, at the weight `W`. -/
def dk1M (c : TorusCertificate n α) (W : CertWeight) (dK : CertEmbedding α) :
    ℕ → ℕ → CertModel α :=
  fun a j => CertModel.addMixed W c.piEnc (dkM c W a j) (dstepModel n W c.piEnc dK a j)

/-- `‖Ω‖ ≤ o` from the row sums of the entry bounds at the weight `Wb`. -/
def omegaOk (W Wb : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (Mm : ℕ → ℕ → CertModel α) (o : ℚ) : Bool :=
  decide (0 ≤ o) && (List.finRange n).all fun i =>
    ble (sumUp (fun j : Fin n => (lagModel (n := n) W cfg pe Mm i.val j.val).supBound Wb)
      (List.finRange n)) (ofRatDown o)

variable [LawfulCertArith α]

/-- Soundness of `lagModel`. -/
theorem lagModel_encloses {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (cfg : ModelConfig α) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    {Mm : ℕ → ℕ → CertModel α} {M : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}
    (hM : ∀ x (j : Fin n), (Mm (phaseNat x) j.val).Encloses n W.rho (fun θ => M θ x j))
    (i j : Fin n) :
    (lagModel (n := n) W cfg pe Mm i.val j.val).Encloses n W.rho
      (fun θ => ((M θ)ᵀ * omegaZeroMatrix n * M θ) i j) := by
  have hrow : ∀ x : Fin n ⊕ Fin n, (omegaRow n Mm (phaseNat x) j.val).Encloses n W.rho
      (fun θ => (omegaZeroMatrix n * M θ) x j) := by
    intro x
    rcases x with k | k
    · have hlt : phaseNat (Sum.inl k : Fin n ⊕ Fin n) < n := k.isLt
      have e : phaseNat (Sum.inl k : Fin n ⊕ Fin n) + n = phaseNat (Sum.inr k : Fin n ⊕ Fin n) := by
        simp [phaseNat, add_comm]
      simp only [omegaRow, hlt, ↓reduceIte, e]
      exact (hM (Sum.inr k) j).negM.of_eq_fun fun θ => by
        rw [omegaZeroMatrix_mul_apply_inl]
    · have hlt : ¬(phaseNat (Sum.inr k : Fin n ⊕ Fin n) < n) := by simp [phaseNat]
      have e : phaseNat (Sum.inr k : Fin n ⊕ Fin n) - n = phaseNat (Sum.inl k : Fin n ⊕ Fin n) := by
        simp [phaseNat]
      simp only [omegaRow, hlt, ↓reduceIte, e]
      exact (hM (Sum.inl k) j).of_eq_fun fun θ => by
        rw [omegaZeroMatrix_mul_apply_inr]
  have h := dotModel_encloses hW cfg hpe (n + n) (a := fun a => Mm a i.val)
    (b := fun a => omegaRow n Mm a j.val)
    (fa := fun a θ => M θ (finSumFinEquiv.symm a) i)
    (fb := fun a θ => (omegaZeroMatrix n * M θ) (finSumFinEquiv.symm a) j)
    (fun a => by
      have := hM (finSumFinEquiv.symm a) i
      rwa [phaseNat_finSumFinEquiv_symm] at this)
    (fun a => by
      have := hrow (finSumFinEquiv.symm a)
      rwa [phaseNat_finSumFinEquiv_symm] at this)
  refine h.of_eq_fun fun θ => ?_
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rw [Equiv.sum_comp finSumFinEquiv.symm (fun x => M θ x i * (omegaZeroMatrix n * M θ) x j)]
  rfl

theorem dkM_encloses {c : TorusCertificate n α} (hs : checkStatic c = true) {W : CertWeight}
    {s N : ℕ} (hW : checkWeight W s N = true) (x : Fin n ⊕ Fin n) (j : Fin n) :
    (dkM c W (phaseNat x) j.val).Encloses n W.rho (fun θ => tangentMat c.K θ x j) := by
  have S := checkStatic_sound hs
  exact dkModels_encloses hW S.hpe c.emb x j

theorem dk1M_encloses {c : TorusCertificate n α} (hs : checkStatic c = true) {W : CertWeight}
    {s N : ℕ} (hW : checkWeight W s N = true) (dK : CertEmbedding α) (x : Fin n ⊕ Fin n)
    (j : Fin n) : (dk1M c W dK (phaseNat x) j.val).Encloses n W.rho
      (fun θ => tangentMat (c.K + stepFun n dK) θ x j) := by
  have S := checkStatic_sound hs
  refine ((dkM_encloses hs hW x j).addMixed hW S.hpe
    (dstepModel_encloses hW S.hpe dK x j)).of_eq_fun fun θ => ?_
  have e : tangentMat (c.K + stepFun n dK) θ = tangentMat c.K θ + tangentMat (stepFun n dK) θ :=
    KAM.Sharp2.Hybrid.tangentMat_add_step ((c.emb.differentiable_eval n) θ)
      ((differentiable_stepFun dK) θ)
  simp only [Pi.add_apply]
  rw [e]
  rfl

/-- **`‖Mᵀ Ω₀ M‖ ≤ o` on the strip of `W'`** (`W'.rho ≤ W.rho`). -/
theorem lagrangeMat_le {W W' : CertWeight} {s N s' N' : ℕ} (hW : checkWeight W s N = true)
    (hW' : checkWeight W' s' N' = true) (hρ : W'.rho ≤ W.rho) (cfg : ModelConfig α)
    {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) {Mm : ℕ → ℕ → CertModel α}
    {M : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}
    (hM : ∀ x (j : Fin n), (Mm (phaseNat x) j.val).Encloses n W.rho (fun θ => M θ x j)) {o : ℚ}
    (h : omegaOk (n := n) W W' cfg pe Mm o = true) :
    ∀ θ ∈ complexStrip n W'.rho, ‖(M θ)ᵀ * omegaZeroMatrix n * M θ‖ ≤ o := by
  intro θ hθ
  simp only [omegaOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  refine (norm_le_iff_forall_rowSum (by exact_mod_cast h.1)).2 fun i => ?_
  refine sum_fin_le (g := fun j => (lagModel (n := n) W cfg pe Mm i.val j).supBound W') (h.2 i)
    fun j => ?_
  exact CertModel.norm_le_supBound hW' (fun θ' hθ' => lagModel_encloses hW cfg hpe hM i j θ'
    (fun l => (hθ' l).trans_le (by exact_mod_cast hρ))) hθ

/-- **`‖Mᵀ Ω₀ M‖ ≤ o` on the real torus.** -/
theorem lagrangeMat_real_le {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (cfg : ModelConfig α) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    {Mm : ℕ → ℕ → CertModel α} {M : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}
    (hM : ∀ x (j : Fin n), (Mm (phaseNat x) j.val).Encloses n W.rho (fun θ => M θ x j)) {o : ℚ}
    (h : omegaOk (n := n) W realWeight cfg pe Mm o = true) (y : Fin n → ℝ) :
    ‖(M fun l => (y l : ℂ))ᵀ * omegaZeroMatrix n * M fun l => (y l : ℂ)‖ ≤ o := by
  simp only [omegaOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  refine (norm_le_iff_forall_rowSum (by exact_mod_cast h.1)).2 fun i => ?_
  refine sum_fin_le (g := fun j => (lagModel (n := n) W cfg pe Mm i.val j).supBound realWeight)
    (h.2 i) fun j => ?_
  exact CertModel.norm_le_supBound_real (CertWeight.rho_pos hW)
    (lagModel_encloses hW cfg hpe hM i j) y

end KAM.CertificateSharp.Hybrid

end
