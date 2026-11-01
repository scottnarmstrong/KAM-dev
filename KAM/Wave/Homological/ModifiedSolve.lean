/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ModifiedReweight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The solution with modified divisors (`bpW:w5:w4-modified` (i), class membership)

Off-frontier, source-faithful infrastructure (W5-MODIFIED, blueprint `bpW:w5:w4-modified`); the
dependency graph is still being built.

`homModSolveTaylor … R` is the function `F` of `bpW:w5:w4-modified`, defined by the formulas of
`bpW:w4:lemma1` from `R ∈ 𝒯_s` (`p̄ = p+1`) and read in the class `𝒯_{s-σ}` with gradient weight
`p₊`:
* the components `a, b` are the W4 solves of `a, b`;
* `c^±, P, P'` are the W4 solves of the components of `homReweight R` (the inclusion
  `ℓ^N_{a,p+1} ⊂ ℓ^N_{a,p₊}` commutes with the diagonal and Hadamard multipliers);
* `Q, Q^T` are the solves of `R.Q, R.Qt` (`p+1`-weighted matrices) with the twisted Hadamard
  multipliers `ρ_i/(iδ^Q_{k,ij})`, `ρ_i/(iδ^Q_{k,ji})` (step `m-sup`): their `p₊`-weighted
  matrices are the Hadamard images `(ρ_i d_ij R̂_ij)`, i.e. the true matrix entries are
  `d_ij (R_Q)_ij` (`homModSolve_entry`).
The multiplier norm and Lipschitz bounds (`norm_homModT*_le`, `norm_homModT*_sub_le`) feed the
solve lemmas of `bpW:w4:solve`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

/-- The diagonal multiplier of `c^+`. -/
def homModTdp (hm : HomModMultBounds a p pb τ α w W) (k : Fin 2 → ℤ) : HomOp :=
  weightedDiagCLM (homMultDp w W k) (hm.dp k)

/-- The diagonal multiplier of `c^-`. -/
def homModTdm (hm : HomModMultBounds a p pb τ α w W) (k : Fin 2 → ℤ) : HomOp :=
  weightedDiagCLM (homMultDm w W k) (hm.dm k)

/-- The Hadamard multiplier of `P`. -/
def homModTP (hm : HomModMultBounds a p pb τ α w W) (k : Fin 2 → ℤ) : HomOp →L[ℂ] HomOp :=
  homHadamardCLM (hm.P k)

/-- The Hadamard multiplier of `P'`. -/
def homModTP' (hm : HomModMultBounds a p pb τ α w W) (k : Fin 2 → ℤ) : HomOp →L[ℂ] HomOp :=
  homHadamardCLM (hm.P' k)

/-- The twisted Hadamard multiplier of `Q`. -/
def homModTQ (hm : HomModMultBounds a p pb τ α w W) (k : Fin 2 → ℤ) : HomOp →L[ℂ] HomOp :=
  homHadamardCLM (hm.Q k)

/-- The twisted Hadamard multiplier of `Q^T`. -/
def homModTQt (hm : HomModMultBounds a p pb τ α w W) (k : Fin 2 → ℤ) : HomOp →L[ℂ] HomOp :=
  homHadamardCLM (hm.Qt k)

section norms

variable (hm : HomModMultBounds a p pb τ α w W) (k : Fin 2 → ℤ)

theorem norm_homModTdp_le : ‖homModTdp hm k‖ ≤ 1 * waveA τ k / α := norm_diagCLM_le _ _

theorem norm_homModTdm_le : ‖homModTdm hm k‖ ≤ 1 * waveA τ k / α := norm_diagCLM_le _ _

theorem norm_homModTP_le : ‖homModTP hm k‖ ≤ homKS * waveA τ k / α := by
  refine (norm_homHadamardCLM_le (hm.P k)).trans (le_of_eq ?_); ring

theorem norm_homModTP'_le : ‖homModTP' hm k‖ ≤ homKS * waveA τ k / α := by
  refine (norm_homHadamardCLM_le (hm.P' k)).trans (le_of_eq ?_); ring

theorem norm_homModTQ_le : ‖homModTQ hm k‖ ≤ homKS * waveA τ k / α := by
  refine (norm_homHadamardCLM_le (hm.Q k)).trans (le_of_eq ?_); ring

theorem norm_homModTQt_le : ‖homModTQt hm k‖ ≤ homKS * waveA τ k / α := by
  refine (norm_homHadamardCLM_le (hm.Qt k)).trans (le_of_eq ?_); ring

include hm in
theorem norm_homModTscal_le : ‖homTscal w k‖ ≤ 1 * waveA τ k / α :=
  ((norm_smul (homMultA0 w k) (ContinuousLinearMap.id ℂ ℂ)).le.trans
    (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _))).trans
    (by simpa using hm.a0 k)

include hm in
theorem norm_homModTvec_le : ‖homTvec w k‖ ≤ 1 * waveA τ k / α :=
  ((norm_smul (homMultA0 w k) (ContinuousLinearMap.id ℂ (Fin 2 → ℂ))).le.trans
    (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _))).trans
    (by simpa using hm.a0 k)

end norms

section lipnorms

variable {M d : ℝ} {w₁ w₂ : Fin 2 → ℝ} {W₁ W₂ : ℕ+ → ℝ}
  (hm₁ : HomModMultBounds a p pb τ α w₁ W₁) (hm₂ : HomModMultBounds a p pb τ α w₂ W₂)
  (hL : HomModMultLip a p pb τ α M d w₁ W₁ w₂ W₂) (k : Fin 2 → ℤ)
include hL

theorem norm_homModTscal_sub_le :
    ‖homTscal w₁ k - homTscal w₂ k‖ ≤
      2 * 1 * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  have : homTscal w₁ k - homTscal w₂ k =
      (homMultA0 w₁ k - homMultA0 w₂ k) • ContinuousLinearMap.id ℂ ℂ := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [homTscal, sub_mul]
  rw [this]
  refine ((norm_smul _ _).le.trans (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
    (norm_nonneg _))).trans ?_
  have := hL.a0 k
  unfold homLipC at this
  linarith

theorem norm_homModTvec_sub_le :
    ‖homTvec w₁ k - homTvec w₂ k‖ ≤
      2 * 1 * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  have : homTvec w₁ k - homTvec w₂ k =
      (homMultA0 w₁ k - homMultA0 w₂ k) • ContinuousLinearMap.id ℂ (Fin 2 → ℂ) := by
    refine ContinuousLinearMap.ext fun v => ?_
    ext j
    simp [homTvec, sub_mul]
  rw [this]
  refine ((norm_smul _ _).le.trans (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
    (norm_nonneg _))).trans ?_
  have := hL.a0 k
  unfold homLipC at this
  linarith

theorem norm_homModTdp_sub_le :
    ‖homModTdp hm₁ k - homModTdp hm₂ k‖ ≤
      2 * 1 * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  have hb : ∀ j, ‖homMultDp w₁ W₁ k j - homMultDp w₂ W₂ k j‖ ≤ homLipC τ α M d k :=
    fun j => hL.dp k j
  have : homModTdp hm₁ k - homModTdp hm₂ k =
      weightedDiagCLM (fun j => homMultDp w₁ W₁ k j - homMultDp w₂ W₂ k j) hb := by
    refine ContinuousLinearMap.ext fun v => ?_
    ext j
    simp [homModTdp, weightedDiagCLM_apply, sub_mul]
  rw [this]
  refine (norm_diagCLM_le _ hb).trans ?_
  unfold homLipC; linarith

theorem norm_homModTdm_sub_le :
    ‖homModTdm hm₁ k - homModTdm hm₂ k‖ ≤
      2 * 1 * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  have hb : ∀ j, ‖homMultDm w₁ W₁ k j - homMultDm w₂ W₂ k j‖ ≤ homLipC τ α M d k :=
    fun j => hL.dm k j
  have : homModTdm hm₁ k - homModTdm hm₂ k =
      weightedDiagCLM (fun j => homMultDm w₁ W₁ k j - homMultDm w₂ W₂ k j) hb := by
    refine ContinuousLinearMap.ext fun v => ?_
    ext j
    simp [homModTdm, weightedDiagCLM_apply, sub_mul]
  rw [this]
  refine (norm_diagCLM_le _ hb).trans ?_
  unfold homLipC; linarith

theorem norm_homModTP_sub_le :
    ‖homModTP hm₁ k - homModTP hm₂ k‖ ≤
      2 * homKS * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  refine (norm_hadSub_le (hm₁.P k) (hm₂.P k) (hL.P k)).trans (le_of_eq ?_)
  unfold homLipC; ring

theorem norm_homModTP'_sub_le :
    ‖homModTP' hm₁ k - homModTP' hm₂ k‖ ≤
      2 * homKS * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  refine (norm_hadSub_le (hm₁.P' k) (hm₂.P' k) (hL.P' k)).trans (le_of_eq ?_)
  unfold homLipC; ring

theorem norm_homModTQ_sub_le :
    ‖homModTQ hm₁ k - homModTQ hm₂ k‖ ≤
      2 * homKS * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  refine (norm_hadSub_le (hm₁.Q k) (hm₂.Q k) (hL.Q k)).trans (le_of_eq ?_)
  unfold homLipC; ring

theorem norm_homModTQt_sub_le :
    ‖homModTQt hm₁ k - homModTQt hm₂ k‖ ≤
      2 * homKS * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d := by
  refine (norm_hadSub_le (hm₁.Qt k) (hm₂.Qt k) (hL.Qt k)).trans (le_of_eq ?_)
  unfold homLipC; ring

end lipnorms

/-- **Entries of a twisted Hadamard solve** (step `m-sup`): if the multipliers are
`ρ_i d_k(i,j)`, the true matrix entries (weights `(p,p₊)`) of the solve are the scalar solves with
the multipliers `d_k(i,j)` of the true matrix entries (weights `(p,p+1)`) of the data. -/
theorem homModSolve_entry {s σ m κ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ) (hσ : 0 < σ)
    (hσs : σ < s) {D d : (Fin 2 → ℤ) → ℕ+ → ℕ+ → ℂ} {c : (Fin 2 → ℤ) → ℝ}
    (hD : ∀ k, HomHadamardBound (D k) (c k))
    (hDd : ∀ k i j, D k i j = (homModRatio a p pb i : ℂ) * d k i j)
    (hT : ∀ k, ‖homHadamardCLM (hD k)‖ ≤ κ * waveA τ k / α) {u : (Fin 2 → ℂ) → HomOp}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (i j : ℕ+) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) :
    homNormalEntry_gen a p pb (homSolve (fun k => homHadamardCLM (hD k)) u θ) i j =
      homSolve (fun k => d k i j • ContinuousLinearMap.id ℂ ℂ)
        (fun z => homNormalEntry_gen a p (p + 1) (u z) i j) θ := by
  have hs : 0 < s := hσ.trans hσs
  obtain ⟨hsum, -⟩ := homSolve_spec hτ hα hκ hσ hσs hT hu hp hm
  have := homSolve_intertwine (T' := fun k => d k i j • ContinuousLinearMap.id ℂ ℂ) (ρ := s - σ)
    hs (homNormEntryCLM_gen a p (p + 1) i j) (homNormEntryCLM_gen a p pb i j)
    (fun k => by
      refine ContinuousLinearMap.ext fun A => ?_
      simp only [ContinuousLinearMap.comp_apply, homNormEntryCLM_apply_gen, homHadamardCLM_apply,
        homNormalEntry_hadamard_gen, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, hDd]
      unfold homNormalEntry_gen homModRatio homWt
      have h1 : (ellWeight a pb (i + 2) : ℂ) ≠ 0 := ellWeight_cast_ne_zero a pb (i + 2)
      have h2 : (ellWeight a (p + 1) (i + 2) : ℂ) ≠ 0 := ellWeight_cast_ne_zero a (p + 1) (i + 2)
      push_cast
      field_simp) hu hsum hθ
  simpa only [homNormEntryCLM_apply_gen] using this

/-- **The solution `F ∈ 𝒯_{s-σ}`** of `bpW:w5:w4-modified` (i), with gradient weight `p₊`: the
formulas of `bpW:w4:lemma1` applied to `R ∈ 𝒯_s` (`p̄ = p+1`), the `Q`-division with the
modified divisors read as a bounded operator `ℓ^N_{a,p} → ℓ^N_{a,p₊}` (step `m-sup`). -/
def homModSolveTaylor {s σ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hc : pb ≤ p + 1) (hm : HomModMultBounds a p pb τ α w W) (R : HomTaylor_gen a p (p + 1) s) :
    HomTaylor_gen a p pb (s - σ) where
  a0 := homSolve (homTscal w) R.a0
  b := homSolve (homTvec w) R.b
  cp := homSolve (homModTdp hm) (homReweight hc R).cp
  cm := homSolve (homModTdm hm) (homReweight hc R).cm
  P := homSolve (homModTP hm) (homReweight hc R).P
  P' := homSolve (homModTP' hm) (homReweight hc R).P'
  Q := homSolve (homModTQ hm) R.Q
  Qt := homSolve (homModTQt hm) R.Qt
  comp_a0 := isHomComp_solve hτ hα le_rfl hσ hσs (norm_homModTscal_le hm) R.comp_a0
  comp_b := isHomComp_solve hτ hα le_rfl hσ hσs (norm_homModTvec_le hm) R.comp_b
  comp_cp := isHomComp_solve hτ hα le_rfl hσ hσs (norm_homModTdp_le hm) (homReweight hc R).comp_cp
  comp_cm := isHomComp_solve hτ hα le_rfl hσ hσs (norm_homModTdm_le hm) (homReweight hc R).comp_cm
  comp_P := isHomComp_solve hτ hα one_le_homKS hσ hσs (norm_homModTP_le hm)
    (homReweight hc R).comp_P
  comp_P' := isHomComp_solve hτ hα one_le_homKS hσ hσs (norm_homModTP'_le hm)
    (homReweight hc R).comp_P'
  comp_Q := isHomComp_solve hτ hα one_le_homKS hσ hσs (norm_homModTQ_le hm) R.comp_Q
  comp_Qt := isHomComp_solve hτ hα one_le_homKS hσ hσs (norm_homModTQt_le hm) R.comp_Qt
  symP := fun θ hθ i j =>
    homSolve_entry_symm_gen (a := a) (p := p) hτ hα one_le_homKS hσ hσs hm.P hm.P
      (norm_homModTP_le hm) (norm_homModTP_le hm) (homReweight hc R).comp_P
      (homReweight hc R).comp_P i j (fun k => homDP_symm w W k i j)
      (fun z hz => (homReweight hc R).symP z hz i j) hθ
  symP' := fun θ hθ i j =>
    homSolve_entry_symm_gen (a := a) (p := p) hτ hα one_le_homKS hσ hσs hm.P' hm.P'
      (norm_homModTP'_le hm) (norm_homModTP'_le hm) (homReweight hc R).comp_P'
      (homReweight hc R).comp_P' i j (fun k => homDP'_symm w W k i j)
      (fun z hz => (homReweight hc R).symP' z hz i j) hθ
  transQ := fun θ hθ i j => by
    obtain ⟨hQd, hQp, mQ, hQm⟩ := R.comp_Q
    obtain ⟨hTd, hTp, mT, hTm⟩ := R.comp_Qt
    have hs : 0 < s := hσ.trans hσs
    show homNormalEntry_gen a p pb (homSolve (fun k => homHadamardCLM (hm.Qt k)) R.Qt θ) i j =
      homNormalEntry_gen a p pb (homSolve (fun k => homHadamardCLM (hm.Q k)) R.Q θ) j i
    rw [homModSolve_entry (d := fun k i j => homDQ w W k j i) hτ hα one_le_homKS hσ hσs hm.Qt
        (fun k i j => rfl) (norm_homModTQt_le hm) hTd hTp hTm i j hθ,
      homModSolve_entry (d := fun k i j => homDQ w W k i j) hτ hα one_le_homKS hσ hσs hm.Q
        (fun k i j => rfl) (norm_homModTQ_le hm) hQd hQp hQm j i hθ]
    exact congrArg (fun f => f θ) (homSolve_congr hs
      (fun k => homDQ w W k j i • ContinuousLinearMap.id ℂ ℂ) (fun z hz => R.transQ z hz i j))

end KAM.Wave
