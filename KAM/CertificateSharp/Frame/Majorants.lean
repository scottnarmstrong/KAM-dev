/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Corner.Checks
public import KAM.Certificate.Sound.Torsion

/-!
# Majorants of the frame objects

The v2 hypotheses of the sharp theorem bound the frame objects of the certified torus by their
*measured* sizes instead of the derived ones (design study §2.7). This module certifies, with the
corner passes of C1 on the models the landed checker already builds, bounds on the strip `T_ρ`:

* `|Lᵀ|`: every column sum `Σ_r |DK_{rj}|` of `L = DK`;
* `|N|`, `|Nᵀ|`: row sums and column sums of `N = Ω₀ L G⁻¹`, from `modelMatMul [4,0] L (G⁻¹ model)`
  (`G⁻¹` is the Gram witness with the radius `δβ/(1-δ)` of `gramCheck`);
* `sup|T|`: row sums of the torsion block of `torsionModels` (the bordered matrix, top-left block);
* `|ω*|` from the frequency box.

`FrameBounds` carries the claimed rational bounds; `checkFrameMajorants` checks them;
`checkFrameMajorants_sound` states the bounds on the real objects `tangentMat`, `normalMat` and
`KAM.Iso.extendedTorsion`. The premises are the contracts of the landed static, Hamiltonian,
embedding and Gram checks: nothing conclusion-shaped.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Torus KAM.Certificate CertArith

/-- Claimed rational majorants: `bL ≥ |Lᵀ|`, `bN ≥ |N|`, `bNt ≥ |Nᵀ|`, `bT ≥ sup |T|`,
`bOm ≥ |ω*|`. -/
structure FrameBounds where
  bL : ℚ
  bN : ℚ
  bNt : ℚ
  bT : ℚ
  bOm : ℚ

/-- An upper bound of the sup norm of a vector in the box: `max_i (|c_i| + r_i)`. -/
def freqNormUp (box : FreqBox) : ℚ := box.foldr (fun b acc => max (|b.1| + b.2) acc) 0

theorem abs_add_le_freqNormUp (box : FreqBox) (i : ℕ) :
    |(box.getD i (0, 0)).1| + (box.getD i (0, 0)).2 ≤ freqNormUp box := by
  induction box generalizing i with
  | nil => simp [freqNormUp]
  | cons b box ih =>
    cases i with
    | zero => exact le_max_left _ _
    | succ i =>
      simp only [freqNormUp, List.foldr_cons]
      exact (ih i).trans (le_max_right _ _)

theorem freqNormUp_nonneg (box : FreqBox) : 0 ≤ freqNormUp box := by
  induction box with
  | nil => simp [freqNormUp]
  | cons b box ih => exact ih.trans (le_max_right _ _)

theorem norm_le_freqNormUp {n : ℕ} {box : FreqBox} {ω : Fin n → ℝ} (h : FreqEncloses n box ω) :
    ‖ω‖ ≤ (freqNormUp box : ℝ) := by
  refine (pi_norm_le_iff_of_nonneg (by exact_mod_cast freqNormUp_nonneg box)).2 fun i => ?_
  have h1 := h i
  have h2 : ((|(box.getD i.val (0, 0)).1| + (box.getD i.val (0, 0)).2 : ℚ) : ℝ) ≤
      (freqNormUp box : ℝ) := by exact_mod_cast abs_add_le_freqNormUp box i.val
  push_cast at h2
  rw [Real.norm_eq_abs]
  calc |ω i| = |(ω i - (box.getD i.val (0, 0)).1) + (box.getD i.val (0, 0)).1| := by ring_nf
    _ ≤ |ω i - (box.getD i.val (0, 0)).1| + |((box.getD i.val (0, 0)).1 : ℝ)| := abs_add_le _ _
    _ ≤ _ := by
      have : |((box.getD i.val (0, 0)).1 : ℝ)| = ((|(box.getD i.val (0, 0)).1| : ℚ) : ℝ) := by
        push_cast; rfl
      linarith

/-! ### Sums over index lists -/

variable {α : Type} [CertArith α] [LawfulCertArith α]

/-- The joint corner bound for the list of values `F x θ`, `x ∈ L`, enclosed by `m x`. -/
theorem list_norm_sum_le {ι : Type} {n : ℕ} {W : CertWeight} {s N N' : ℕ}
    (hW : checkWeight W s N = true) (L : List ι) (m : ι → CertModel α)
    (F : ι → (Fin n → ℂ) → ℂ) (hm : ∀ x ∈ L, (m x).Encloses n W.rho (F x)) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) {b : α}
    (h : rowCornerLeq W (wloOf W N') n (L.map m) b = true) :
    (L.map fun x => ‖F x θ‖).sum ≤ val b := by
  have := sum_norm_le_of_rowCornerLeq (N' := N') hW (L.map fun x => (m x, F x))
    (by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      exact hm x hx) hθ (by simpa [List.map_map, Function.comp_def] using h)
  simpa [List.map_map, Function.comp_def] using this

/-- Transfer along `Fin (n+n) ≃ Fin n ⊕ Fin n`: the entry of index `phaseNat a` is the entry of
`(finSumFinEquiv a).val`. -/
theorem phaseNat_symm_eq {n : ℕ} (k : Fin (n + n)) :
    phaseNat (finSumFinEquiv.symm k) = k.val := phaseNat_finSumFinEquiv_symm k

/-! ### The models of `N` -/

/-- `N = Ω₀ (L G⁻¹)` (`2n × n`) as models: `G⁻¹` is the Gram witness with radius `eps`. -/
def frameNModels (n : ℕ) (K : CertEmbedding α) (Binv : List (List (CertPoly α))) (eps : α)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) : ModelMatrix α :=
  modelMatOmega n n (modelMatMul W cfg pe [4, 0] (n + n) n n (dkModels n K W pe)
    (gramInvModels n Binv eps))

theorem frameNModels_encloses {n : ℕ} (hn : 1 ≤ n) {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (K : CertEmbedding α) (Binv : List (List (CertPoly α)))
    (cfg : ModelConfig α) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) {σBμ : ℚ}
    {δβ : α × α} (hG : gramCheck n K Binv W cfg pe σBμ = some δβ) {eps : α}
    (heps : gramInvRadius δβ = some eps) :
    (frameNModels n K Binv eps W cfg pe).EntryEncloses n W.rho phaseNat Fin.val
      (fun θ => omegaZeroMatrix n * (tangentMat (K.eval n) θ * (gramMatrix (K.eval n) θ)⁻¹)) := by
  obtain ⟨-, hGs⟩ := gramCheck_sound hn K Binv hW cfg hpe σBμ hG
  have hfin : ∀ j : Fin n, j.val < n := fun j => j.isLt
  have hL := dkModels_encloses (n := n) hW hpe K
  have hGi : (gramInvModels n Binv eps).EntryEncloses n W.rho Fin.val Fin.val
      (fun θ => (gramMatrix (K.eval n) θ)⁻¹) :=
    gramInvModels_encloses Binv fun θ hθ => (hGs θ hθ).2.2.trans (gramInvRadius_spec heps)
  have he1 : ∀ k : Fin n, (Equiv.refl (Fin n) k).val = k.val := fun _ => rfl
  exact (hL.modelMul hW cfg hpe [4, 0] phaseNat_lt_add hfin (Equiv.refl _) he1 hGi).modelOmega
    hfin

variable {n : ℕ}

/-- The gram certificate of the certificate (as in `checkTorsion`). -/
def frameGram (c : TorusCertificate n α) : Option (α × α) :=
  gramCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc (c.params.σB - c.params.μ)

/-- `|Lᵀ| ≤ bL`: every column sum of `DK`, by the joint corner bound. -/
def checkFrameL (c : TorusCertificate n α) (b : ℚ) : Bool :=
  (List.finRange n).all fun j =>
    rowCornerLeq c.weight (wloOf c.weight c.expOrder) n
      ((List.finRange (n + n)).map fun r => modelMatrixEntry (dkModels n c.emb c.weight c.piEnc)
        r.val j.val) (ofRatDown b)

/-- `|N| ≤ bN` (row sums) and `|Nᵀ| ≤ bNt` (column sums) of `N = Ω₀ L G⁻¹`. -/
def checkFrameN (c : TorusCertificate n α) (bN bNt : ℚ) : Bool :=
  match frameGram c with
  | some δβ =>
    match gramInvRadius δβ with
    | some eps =>
      let M := frameNModels n c.emb c.gramInv eps c.weight c.cfgLow c.piEnc
      (List.finRange (n + n)).all (fun r =>
        rowCornerLeq c.weight (wloOf c.weight c.expOrder) n
          ((List.finRange n).map fun j => modelMatrixEntry M r.val j.val) (ofRatDown bN)) &&
      (List.finRange n).all (fun j =>
        rowCornerLeq c.weight (wloOf c.weight c.expOrder) n
          ((List.finRange (n + n)).map fun r => modelMatrixEntry M r.val j.val) (ofRatDown bNt))
    | none => false
  | none => false

/-- `sup_{T_ρ} |T| ≤ bT`: row sums of the torsion block of the models of `torsionModels`. -/
def checkFrameT (c : TorusCertificate n α) (b : ℚ) : Bool :=
  match frameGram c with
  | some δβ =>
    match torsionModels n c.ham c.emb c.wit c.gramInv δβ c.freqBox c.params.s c.weight c.cfgLow
        c.piEnc with
    | some T =>
      (List.finRange n).all fun i =>
        rowCornerLeq c.weight (wloOf c.weight c.expOrder) n
          ((List.finRange n).map fun j => modelMatrixEntry T i.val j.val) (ofRatDown b)
    | none => false
  | none => false

/-- `|ω*| ≤ bOm` from the box. -/
def checkFrameOmega (c : TorusCertificate n α) (b : ℚ) : Bool := decide (freqNormUp c.freqBox ≤ b)

/-- All four frame checks. -/
def checkFrameMajorants (c : TorusCertificate n α) (b : FrameBounds) : Bool :=
  checkFrameL c b.bL && checkFrameN c b.bN b.bNt && checkFrameT c b.bT && checkFrameOmega c b.bOm

/-! ### Soundness -/

section Sound

/-- The real statement of the frame majorants on the strip `T_ρ`. -/
def FrameMajorants (c : TorusCertificate n α) (b : FrameBounds) (ω : Fin n → ℝ) : Prop :=
  (∀ θ ∈ complexStrip n c.params.rho, ∀ j : Fin n,
      ∑ r : Fin n ⊕ Fin n, ‖tangentMat c.K θ r j‖ ≤ b.bL) ∧
  (∀ θ ∈ complexStrip n c.params.rho, ∀ r : Fin n ⊕ Fin n,
      ∑ j : Fin n, ‖normalMat c.K θ r j‖ ≤ b.bN) ∧
  (∀ θ ∈ complexStrip n c.params.rho, ∀ j : Fin n,
      ∑ r : Fin n ⊕ Fin n, ‖normalMat c.K θ r j‖ ≤ b.bNt) ∧
  (∀ θ ∈ complexStrip n c.params.rho, ∀ i : Fin n, ∑ j : Fin n,
      ‖KAM.Iso.extendedTorsion c.H c.K ((c.params.s : ℝ) • ω) θ (Sum.inl i) (Sum.inl j)‖ ≤ b.bT) ∧
  ‖ω‖ ≤ b.bOm

variable {W : CertWeight} {sw Nw N' : ℕ}

/-- A column sum of an entrywise-enclosed `2n × n` matrix, by the joint corner bound. -/
theorem col_sum_le {M : ModelMatrix α} {F : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}
    (hM : M.EntryEncloses n W.rho phaseNat Fin.val F) (hW : checkWeight W sw Nw = true)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) (j : Fin n) {b : α}
    (h : rowCornerLeq W (wloOf W N') n
      ((List.finRange (n + n)).map fun r => modelMatrixEntry M r.val j.val) b = true) :
    ∑ a : Fin n ⊕ Fin n, ‖F θ a j‖ ≤ val b := by
  have := list_norm_sum_le (N' := N') hW (List.finRange (n + n))
    (fun r => modelMatrixEntry M r.val j.val)
    (fun r θ => F θ (finSumFinEquiv.symm r) j)
    (by
      intro r _
      have := hM (finSumFinEquiv.symm r) j
      rwa [phaseNat_symm_eq] at this) hθ h
  rw [← Equiv.sum_comp finSumFinEquiv.symm (fun a : Fin n ⊕ Fin n => ‖F θ a j‖),
    Fin.sum_univ_def]
  exact this

/-- A row sum of an entrywise-enclosed `2n × n` matrix, by the joint corner bound. -/
theorem row_sum_le {M : ModelMatrix α} {F : (Fin n → ℂ) → Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}
    (hM : M.EntryEncloses n W.rho phaseNat Fin.val F) (hW : checkWeight W sw Nw = true)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) (a : Fin n ⊕ Fin n) {b : α}
    (h : ∀ r : Fin (n + n), rowCornerLeq W (wloOf W N') n
      ((List.finRange n).map fun j => modelMatrixEntry M r.val j.val) b = true) :
    ∑ j : Fin n, ‖F θ a j‖ ≤ val b := by
  have hr := h (finSumFinEquiv a)
  have := list_norm_sum_le (N' := N') hW (List.finRange n)
    (fun j => modelMatrixEntry M (finSumFinEquiv a).val j.val) (fun j θ => F θ a j)
    (by
      intro j _
      have := hM a j
      have e : phaseNat a = (finSumFinEquiv a).val := by
        simpa using phaseNat_symm_eq (finSumFinEquiv a)
      rwa [e] at this) hθ hr
  rw [Fin.sum_univ_def]
  exact this

/-- **Soundness of the frame majorants.** With the contracts of the landed static, Hamiltonian,
embedding and Gram checks, a passing `checkFrameMajorants` bounds `|Lᵀ|`, `|N|`, `|Nᵀ|`,
`sup |T|` on `T_ρ` and `|ω*|` by the claimed rationals. -/
theorem checkFrameMajorants_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {b : FrameBounds} (h : checkFrameMajorants c b = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) : FrameMajorants c b ωstar := by
  have S := checkStatic_sound hs
  have hn : 1 ≤ n := le_trans (by norm_num) S.hn
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  have hstrip : ∀ θ ∈ complexStrip n c.params.rho, θ ∈ complexStrip n c.weight.rho := by
    intro θ hθ; rw [S.hrho]; exact hθ
  simp only [checkFrameMajorants, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hL, hN⟩, hT⟩, hOm⟩ := h
  have hdb : ∀ x : ℚ, val (ofRatDown x : α) ≤ x := fun x => LawfulCertArith.ofRatDown_le x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- |Lᵀ|
    intro θ hθ j
    unfold checkFrameL at hL
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at hL
    exact (col_sum_le (N' := c.expOrder) (dkModels_encloses (n := n) S.hW S.hpe c.emb) S.hW
      (hstrip θ hθ) j (hL j)).trans (hdb b.bL)
  · -- |N|
    intro θ hθ r
    unfold checkFrameN frameGram at hN
    split at hN
    · rename_i δβ hG
      split at hN
      · rename_i eps heps
        simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hN
        have hM := frameNModels_encloses hn S.hW c.emb c.gramInv c.cfgLow S.hpe hG heps
        have := row_sum_le (N' := c.expOrder) hM S.hW (hstrip θ hθ) r hN.1
        have e : normalMat c.K θ = omegaZeroMatrix n * (tangentMat (c.emb.eval n) θ *
            (gramMatrix (c.emb.eval n) θ)⁻¹) := by
          simp [normalMat, TorusCertificate.K, Matrix.mul_assoc]
        rw [e]
        exact this.trans (hdb b.bN)
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
        have := col_sum_le (N' := c.expOrder) hM S.hW (hstrip θ hθ) j (hN.2 j)
        have e : normalMat c.K θ = omegaZeroMatrix n * (tangentMat (c.emb.eval n) θ *
            (gramMatrix (c.emb.eval n) θ)⁻¹) := by
          simp [normalMat, TorusCertificate.K, Matrix.mul_assoc]
        rw [e]
        exact this.trans (hdb b.bNt)
      · exact absurd hN (by simp)
    · exact absurd hN (by simp)
  · -- sup |T|
    intro θ hθ i
    unfold checkFrameT frameGram at hT
    split at hT
    · rename_i δβ hG
      split at hT
      · rename_i T hTm
        obtain ⟨-, hTe, -⟩ := torsionModels_sound hn (isOpen_certDomain _ _ _ _) hH.1 S.hW hKD
          c.wit c.gramInv c.cfgLow S.hpe hG c.freqBox c.params.s hTm hω
        simp only [List.all_eq_true, List.mem_finRange, true_implies] at hT
        have := list_norm_sum_le (N' := c.expOrder) S.hW (List.finRange n)
          (fun j => modelMatrixEntry T i.val j.val)
          (fun j θ => KAM.Iso.extendedTorsion c.H c.K ((c.params.s : ℝ) • ωstar) θ
            (Sum.inl i) (Sum.inl j))
          (by
            intro j _
            obtain ⟨m, hm, henc⟩ := hTe (Sum.inl i) (Sum.inl j)
            simp only [torsionIdx, Sum.elim_inl] at hm
            have : modelMatrixEntry T i.val j.val = m := by
              simp [modelMatrixEntry, hm]
            rw [this]
            exact henc) (hstrip θ hθ) (hT i)
        rw [Fin.sum_univ_def]
        exact this.trans (hdb b.bT)
      · exact absurd hT (by simp)
    · exact absurd hT (by simp)
  · -- |ω*|
    unfold checkFrameOmega at hOm
    simp only [decide_eq_true_eq] at hOm
    exact (norm_le_freqNormUp hω).trans (by exact_mod_cast hOm)

end Sound

end KAM.CertificateSharp
