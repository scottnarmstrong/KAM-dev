/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneEquation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The normal form correction `N̂` (`bpW:w4:lemma1` (iv))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

`N̂ = ⟨ω̂,y⟩ + ∑ Ω̂_j z_j \\bar z_j` is a Taylor Hamiltonian with constant components
(`homNhatTaylor R`: `b = [b]`, `Q = Q^T` the diagonal of `[Q]`); `homNhatTaylor_val` identifies its
value with `homNhat`. Bounds: `|ω̂| ≤ 2πε`, `(j+2)^{p_+-p}|Ω̂_j| ≤ ε` (`homNhat_coeff_bounds`) and
`|X_{N̂}|_r ≤ 2ε` (`homNhat_fieldBound`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

theorem kamEntry_diagCLM (A : HomOp) (i j : ℕ+) :
    kamEntry (kamEntryDiagCLM A) i j = if i = j then kamEntry A i i else 0 := by
  by_cases hij : i = j
  · subst hij; simp [kamEntry, kamEntryDiagCLM, weightedDiagCLM_apply, kamBasis]
  · simp [kamEntry, kamEntryDiagCLM, weightedDiagCLM_apply, kamBasis, hij]

theorem isHomComp_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℝ) (c : E) :
    IsHomComp s (fun _ : Fin 2 → ℂ => c) :=
  ⟨differentiableOn_const _, fun _ _ _ => rfl, ‖c‖, fun _ _ => le_rfl⟩

/-- **`N̂` as a Taylor Hamiltonian**: `a = 0`, `b = [b]`, `c^± = P = P' = 0`,
`Q = Q^T = diag([Q]_{jj})`. -/
def homNhatTaylor (R : HomTaylor a p pb s) : HomTaylor a p pb s where
  a0 := fun _ => 0
  b := fun _ => homCoeff R.b 0
  cp := fun _ => 0
  cm := fun _ => 0
  P := fun _ => 0
  P' := fun _ => 0
  Q := fun _ => kamEntryDiagCLM (homCoeff R.Q 0)
  Qt := fun _ => kamEntryDiagCLM (homCoeff R.Q 0)
  comp_a0 := isHomComp_const s _
  comp_b := isHomComp_const s _
  comp_cp := isHomComp_const s _
  comp_cm := isHomComp_const s _
  comp_P := isHomComp_const s _
  comp_P' := isHomComp_const s _
  comp_Q := isHomComp_const s _
  comp_Qt := isHomComp_const s _
  symP := fun _ _ i j => by simp [homNormalEntry, kamEntry]
  symP' := fun _ _ i j => by simp [homNormalEntry, kamEntry]
  transQ := fun _ _ i j => by
    by_cases hij : i = j
    · subst hij; rfl
    · simp [homNormalEntry, kamEntry_diagCLM, hij, Ne.symm hij]

/-- The value of the Taylor polynomial `homNhatTaylor R` is `N̂`. -/
theorem homNhatTaylor_val {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (R : HomTaylor a p
    pb s)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) :
    homRval ha hp hpb (homNhatTaylor R) θ y z zb = homNhat R y z zb := by
  unfold homRval homNhat
  simp only [homNhatTaylor, homPairRep_eq, map_zero, ContinuousLinearMap.zero_apply,
    Finset.sum_const_zero, zero_add, add_zero, zero_mul]
  congr 1
  show ∑' j : ℕ+, (homLamDiag ha (homPP hp hpb) ((kamEntryDiagCLM (homCoeff R.Q 0)) z) j : ℂ) * (zb
      j : ℂ) = _
  refine tsum_congr fun j => ?_
  have h1 := homLam_entry_eq ha hp hpb (homCoeff R.Q 0) j j
  rw [kamEntry_homLamCLM] at h1
  have hw : (homWt a p j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p j).ne'
  have h2 : homNormalEntry a p pb (homCoeff R.Q 0) j j =
      homLamD a p pb j * kamEntry (homCoeff R.Q 0) j j * ((homWt a p j : ℂ) * (homWt a p j : ℂ)) :=
          by
    rw [h1]; field_simp
  rw [homLamDiag_apply, h2]
  simp only [kamEntryDiagCLM, weightedDiagCLM_apply]
  field_simp


theorem homPartial_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : E)
    (i : Fin 2) (θ : Fin 2 → ℂ) : homPartial i (fun _ : Fin 2 → ℂ => c) θ = 0 := by
  simp [homPartial]

/-- **Lemma 1 (iv), coefficients**: `|ω̂| ≤ 2πε`, `‖[Q]‖ ≤ ε`, `(j+2)^{p_+-p}|Ω̂_j| ≤ ε`. -/
theorem homNhat_coeff_bounds {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr
    : 0 < r)
    (hs : 0 < s) (R : HomTaylor a p pb s) (hX : HomFieldBound ha hp hpb r ε R) :
    ‖homCoeff R.b 0‖ ≤ 2 * Real.pi * ε ∧ ‖homCoeff R.Q 0‖ ≤ ε ∧
      ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) * ‖homNormalEntry a p pb (homCoeff R.Q 0) j j‖ ≤ ε := by
  have hfirst := fun z (hz : z ∈ complexStrip 2 s) => homComp_first ha hp hpb hr R hX hz
  have hb := norm_homCoeff_le hs R.comp_b.1 R.comp_b.2.1 (m := 2 * Real.pi * ε)
    (fun z hz => (hfirst z hz).1) 0
  have hQ := norm_homCoeff_le hs R.comp_Q.1 R.comp_Q.2.1 (m := ε)
    (fun z hz => (hfirst z hz).2.2.2.2.1) 0
  simp only [Fourier.modeSize, Pi.zero_apply, Int.cast_zero, abs_zero, Finset.sum_const_zero,
    mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one] at hb hQ
  refine ⟨hb, hQ, fun j => (homDiagonal_bound a p pb _ j).trans hQ⟩

/-- **Lemma 1 (iv), the field of `N̂`**: `|X_{N̂}|_r ≤ 2ε` on `D(s,r)`. -/
theorem homNhat_fieldBound {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr :
    0 < r)
    (hs : 0 < s) (R : HomTaylor a p pb s) (hX : HomFieldBound ha hp hpb r ε R) :
    HomFieldBound ha hp hpb r (2 * ε) (homNhatTaylor R) := by
  obtain ⟨hb, hQ, -⟩ := homNhat_coeff_bounds ha hp hpb hr hs R hX
  intro θ y z zb hdom
  have hε : 0 ≤ ε := (norm_nonneg _).trans hQ
  have hDm : ‖kamEntryDiagCLM (homCoeff R.Q 0)‖ ≤ ε := (norm_kamEntryDiagCLM_le _).trans hQ
  set Dm := kamEntryDiagCLM (homCoeff R.Q 0) with hDmdef
  have hRz : homRz (homNhatTaylor R) θ z zb = Dm zb := by simp [homRz, homNhatTaylor, hDmdef]
  have hRzb : homRzb (homNhatTaylor R) θ z zb = Dm z := by simp [homRzb, homNhatTaylor, hDmdef]
  have hRu : homRu (homNhatTaylor R) θ z zb = Dm (homU z zb) := by
    rw [homRu, hRz, hRzb, homU, map_smul, map_add, add_comm]
  have hRv : homRv (homNhatTaylor R) θ z zb = Dm (homV z zb) := by
    rw [homRv, hRz, hRzb, homV, map_smul, map_sub]
    ext j
    simp only [lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hRθ : (fun i => homRtheta ha hp hpb (homNhatTaylor R) i θ y z zb) = 0 := by
    funext i
    simp [homRtheta, homNhatTaylor, homPartial_const, homPairRep_eq]
  unfold homXnorm
  rw [hRθ, hRu, hRv]
  have e1 : (2 * Real.pi)⁻¹ * ‖homRy (homNhatTaylor R) θ‖ ≤ ε := by
    have : ‖homRy (homNhatTaylor R) θ‖ ≤ 2 * Real.pi * ε := hb
    calc _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * ε) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε := by field_simp
  have e2 : ‖Dm (homU z zb)‖ + ‖Dm (homV z zb)‖ ≤ ε * r := by
    have h1 := Dm.le_opNorm (homU z zb)
    have h2 := Dm.le_opNorm (homV z zb)
    nlinarith [norm_nonneg (homU z zb), norm_nonneg (homV z zb), hdom.2.2, norm_nonneg Dm]
  have e3 : r⁻¹ * (‖Dm (homU z zb)‖ + ‖Dm (homV z zb)‖) ≤ ε := by
    calc _ ≤ r⁻¹ * (ε * r) := mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = ε := by field_simp
  simp only [norm_zero, mul_zero, add_zero]
  linarith


/-- **Lemma 1 (i), vanishing of the resonant modes**: `â_{F,0} = 0`, `\hat b_{F,0} = 0`,
`(Q̂_{F,0})_{jj} = 0`. -/
theorem homLemma1_zero_modes {a p pb s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ} (hτ : 0 ≤ τ)
    (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hm : HomMultBounds τ α w W) (R : HomTaylor a p pb s) :
    homCoeff (homSolveTaylor hτ hα hσ hσs hm R).a0 0 = 0 ∧
      homCoeff (homSolveTaylor hτ hα hσ hσs hm R).b 0 = 0 ∧
      ∀ j : ℕ+, kamEntry (homCoeff (homSolveTaylor hτ hα hσ hσs hm R).Q 0) j j = 0 := by
  refine ⟨?_, ?_, fun j => ?_⟩
  · have := (homSolve_spec hτ hα le_rfl hσ hσs (norm_homTscal_le hm) R.comp_a0.1 R.comp_a0.2.1
      R.comp_a0.2.2.choose_spec).2.2.2.2.2 0
    show homCoeff (homSolve (homTscal w) R.a0) 0 = 0
    rw [this]; simp [homTscal, homMultA0]
  · have := (homSolve_spec hτ hα le_rfl hσ hσs (norm_homTvec_le hm) R.comp_b.1 R.comp_b.2.1
      R.comp_b.2.2.choose_spec).2.2.2.2.2 0
    show homCoeff (homSolve (homTvec w) R.b) 0 = 0
    rw [this]; simp [homTvec, homMultA0]
  · have := (homSolve_spec hτ hα one_le_homKS hσ hσs (norm_homTQ_le hm) R.comp_Q.1 R.comp_Q.2.1
      R.comp_Q.2.2.choose_spec).2.2.2.2.2 0
    show kamEntry (homCoeff (homSolve (homTQ hm) R.Q) 0) j j = 0
    rw [this]
    simp only [homTQ, homHadamardCLM_apply, homHadamard_entry]
    simp [homDQ]

end KAM.Wave
