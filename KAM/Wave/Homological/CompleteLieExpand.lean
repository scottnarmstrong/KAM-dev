/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.CompleteLie
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The finite expansion of `L_N F` for a general `F` (`bpW:w4:lie` (iii))

Off-frontier, source-faithful infrastructure (W4-COMPLETE); the dependency graph is still
being built. Blueprint label: `bpW:w4:lie` (iii), step `stepW:w4:liecoef`.

For `F ∈ 𝒯_s`, `θ ∈ T_s` and `z, \bar z` supported in a finite set `S` (true coordinates
`z_j = homTrueCoord a p z j`):

* `homRval_fin_true_gen`: `F = a + ∑_k b_k y_k + ∑_j c^+_j z_j + ∑_j c^-_j \bar z_j
  + ∑_{ij} P_{ij} z_j z_i + ∑_{ij} Q_{ij} z_j \bar z_i + ∑_{ij} P'_{ij} \bar z_j \bar z_i`
  (the finite expression `bpW:w4:R`);
* `homLieN_fin_expansion_gen`: `L_N F` is that expression with every coefficient function `g`
  replaced by `homLieComp w λ g = (2π)⁻¹⟨ω,∂_θ g⟩ - iλ g`, where `λ = 0, 0, Ω_j, -Ω_j,
  Ω_i+Ω_j, Ω_j-Ω_i, -(Ω_i+Ω_j)` for `a, b, c^+, c^-, P, Q, P'`.

The pairings of `L_N` are the source-domain ones (`homLieN_gen`, any carrier evidence).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

theorem homTrueCoord_mul_eq (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (c z : HomL2) (j : ℕ+) :
    homTrueCoord a pb c j * homTrueCoord a p z j = homLamDiag_gen ha (homPP hp hpb) c j * z j := by
  rw [homLamDiag_apply_gen]
  unfold homTrueCoord homLamD_gen
  have h1 : (homWt a p j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p j).ne'
  have h2 : (homWt a pb j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a pb j).ne'
  push_cast
  field_simp

theorem homNormalEntry_mul_eq (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (M : HomOp)
    (z z' : HomL2) (i j : ℕ+) :
    homNormalEntry_gen a p pb M i j * homTrueCoord a p z j * homTrueCoord a p z' i =
      homSent_gen ha hp hpb M i j * z j * z' i := by
  unfold homSent_gen
  rw [homLam_entry_eq_gen ha hp hpb]
  unfold homTrueCoord
  have h1 : (homWt a p j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p j).ne'
  have h2 : (homWt a p i : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p i).ne'
  field_simp

/-- **The value of `F` as the finite expression `bpW:w4:R`** in true coordinates and true matrix
entries, for finitely supported `z, \bar z`. -/
theorem homRval_fin_true_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (F : HomTaylor_gen a p pb s)
    (θ y : Fin 2 → ℂ) {S : Finset ℕ+} {z zb : HomL2} (hz : ∀ j ∉ S, z j = 0)
    (hzb : ∀ j ∉ S, zb j = 0) :
    homRval_gen ha hp hpb F θ y z zb = F.a0 θ + ∑ k, F.b θ k * y k
      + ∑ j ∈ S, homTrueCoord a pb (F.cp θ) j * homTrueCoord a p z j
      + ∑ j ∈ S, homTrueCoord a pb (F.cm θ) j * homTrueCoord a p zb j
      + ∑ i ∈ S, ∑ j ∈ S, homNormalEntry_gen a p pb (F.P θ) i j * homTrueCoord a p z j *
          homTrueCoord a p z i
      + ∑ i ∈ S, ∑ j ∈ S, homNormalEntry_gen a p pb (F.Q θ) i j * homTrueCoord a p z j *
          homTrueCoord a p zb i
      + ∑ i ∈ S, ∑ j ∈ S, homNormalEntry_gen a p pb (F.P' θ) i j * homTrueCoord a p zb j *
          homTrueCoord a p zb i := by
  rw [homRval_fin_gen ha hp hpb hz hzb F θ y]
  simp only [homTrueCoord_mul_eq ha hp hpb, homNormalEntry_mul_eq ha hp hpb]

section terms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem homPartial_trueCoord {q : ℝ} {f : (Fin 2 → ℂ) → HomL2} (hf : IsHomComp s f)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) (l : Fin 2) (j : ℕ+) :
    homPartial l (fun θ => homTrueCoord a q (f θ) j) θ = homTrueCoord a q (homPartial l f θ) j := by
  rw [homTrueCoord_fun_eq, homPartial_clm _ (hf.1.differentiableAt
    ((isOpen_complexStrip 2 s).mem_nhds hθ)) l, homTrueCoordCLM_apply]

theorem homPartial_normalEntry {f : (Fin 2 → ℂ) → HomOp} (hf : IsHomComp s f)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) (l : Fin 2) (i j : ℕ+) :
    homPartial l (fun θ => homNormalEntry_gen a p pb (f θ) i j) θ =
      homNormalEntry_gen a p pb (homPartial l f θ) i j := by
  rw [homNormalEntry_fun_eq, homPartial_clm _ (hf.1.differentiableAt
    ((isOpen_complexStrip 2 s).mem_nhds hθ)) l]
  rfl

theorem homPartial_proj {f : (Fin 2 → ℂ) → (Fin 2 → ℂ)} (hf : IsHomComp s f)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) (l m : Fin 2) :
    homPartial l (fun θ => f θ m) θ = homPartial l f θ m := by
  have := homPartial_clm (ContinuousLinearMap.proj m : (Fin 2 → ℂ) →L[ℂ] ℂ)
    (hf.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hθ)) l
  simpa using this

/-- One vector term: `homLieComp w λ (c_j) · z_j = 𝔏(D ∂c)_j ẑ_j - iλ (Dc)_j ẑ_j`. -/
theorem homLieComp_vec_term (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    {f : (Fin 2 → ℂ) → HomL2} (hf : IsHomComp s f) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (w : Fin 2 → ℝ) (lam : ℝ) (z : HomL2) (j : ℕ+) :
    homLieComp w lam (fun θ => homTrueCoord a pb (f θ) j) θ * homTrueCoord a p z j =
      homLop w (fun l => homLamDiag_gen ha (homPP hp hpb) (homPartial l f θ) j) * z j
        - Complex.I * (lam : ℂ) * (homLamDiag_gen ha (homPP hp hpb) (f θ) j * z j) := by
  have e0 := homTrueCoord_mul_eq ha hp hpb (homPartial 0 f θ) z j
  have e1 := homTrueCoord_mul_eq ha hp hpb (homPartial 1 f θ) z j
  have e2 := homTrueCoord_mul_eq ha hp hpb (f θ) z j
  unfold homLieComp homLop
  simp only [homPartial_trueCoord hf hθ, Fin.sum_univ_two]
  linear_combination ((2 * Real.pi : ℂ)⁻¹ * (w 0 : ℂ)) * e0 + ((2 * Real.pi : ℂ)⁻¹ * (w 1 : ℂ)) * e1
    - Complex.I * (lam : ℂ) * e2

/-- One matrix term:
`homLieComp w λ (M_ij) · z_j z'_i = 𝔏 S(∂M)_ij ẑ_j ẑ'_i - iλ S(M)_ij ẑ_j ẑ'_i`. -/
theorem homLieComp_mat_term (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    {f : (Fin 2 → ℂ) → HomOp} (hf : IsHomComp s f) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (w : Fin 2 → ℝ) (lam : ℝ) (z z' : HomL2) (i j : ℕ+) :
    homLieComp w lam (fun θ => homNormalEntry_gen a p pb (f θ) i j) θ * homTrueCoord a p z j *
        homTrueCoord a p z' i =
      homLop w (fun l => homSent_gen ha hp hpb (homPartial l f θ) i j) * z j * z' i
        - Complex.I * (lam : ℂ) * (homSent_gen ha hp hpb (f θ) i j * z j * z' i) := by
  have e0 := homNormalEntry_mul_eq ha hp hpb (homPartial 0 f θ) z z' i j
  have e1 := homNormalEntry_mul_eq ha hp hpb (homPartial 1 f θ) z z' i j
  have e2 := homNormalEntry_mul_eq ha hp hpb (f θ) z z' i j
  unfold homLieComp homLop
  simp only [homPartial_normalEntry hf hθ, Fin.sum_univ_two]
  linear_combination ((2 * Real.pi : ℂ)⁻¹ * (w 0 : ℂ)) * e0 + ((2 * Real.pi : ℂ)⁻¹ * (w 1 : ℂ)) * e1
    - Complex.I * (lam : ℂ) * e2

end terms

section blocks

theorem homSum2_swap_sym (S : Finset ℕ+) (SF : ℕ+ → ℕ+ → ℂ) (hsym : ∀ i j, SF i j = SF j i)
    (W : ℕ+ → ℝ) (z : ℕ+ → ℂ) :
    ∑ i ∈ S, ∑ j ∈ S, (W j : ℂ) * SF i j * z j * z i =
      ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * SF i j * z j * z i := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym j i]; ring

theorem homSum2_swap_trans (S : Finset ℕ+) (SF SQt : ℕ+ → ℕ+ → ℂ)
    (hQt : ∀ i j, SQt i j = SF j i) (W : ℕ+ → ℝ) (z zb : ℕ+ → ℂ) :
    ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * SQt i j * zb j * z i =
      ∑ i ∈ S, ∑ j ∈ S, (W j : ℂ) * SF i j * z j * zb i := by
  simp only [hQt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end blocks

section expansion

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {W : ℕ+ → ℝ}
  (hC : HomOmegaCarrier ha hp hpb W) (w : Fin 2 → ℝ) (F : HomTaylor_gen a p pb s)
  {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) (y : Fin 2 → ℂ) {S : Finset ℕ+} {z zb : HomL2}
  (hz : ∀ j ∉ S, z j = 0) (hzb : ∀ j ∉ S, zb j = 0)
include hθ hz hzb

/-- **`L_N F` for finitely supported `z, \bar z`** (`bpW:w4:lie` (iii), step `stepW:w4:liecoef`;
general `F ∈ 𝒯_s`, `θ ∈ T_s`): `L_N F` is the finite expression `bpW:w4:R` for `F`
(`homRval_fin_true_gen`) with each coefficient function `g` replaced by
`homLieComp w λ g = (2π)⁻¹⟨ω,∂_θ g⟩ - iλ g` (`λ = 0` for `a_F, b_F`; `Ω_j`, `-Ω_j` for
`c^±_{F,j}`; `Ω_i + Ω_j`, `Ω_j - Ω_i`, `-(Ω_i + Ω_j)` for `P_{F,ij}`, `Q_{F,ij}`, `P'_{F,ij}`). -/
theorem homLieN_fin_expansion_gen :
    homLieN_gen ha hp hpb hC w F θ y z zb =
      homLieComp w 0 F.a0 θ
      + ∑ k, homLieComp w 0 (fun θ => F.b θ k) θ * y k
      + ∑ j ∈ S, homLieComp w (W j) (fun θ => homTrueCoord a pb (F.cp θ) j) θ *
          homTrueCoord a p z j
      + ∑ j ∈ S, homLieComp w (-W j) (fun θ => homTrueCoord a pb (F.cm θ) j) θ *
          homTrueCoord a p zb j
      + ∑ i ∈ S, ∑ j ∈ S, homLieComp w (W i + W j)
          (fun θ => homNormalEntry_gen a p pb (F.P θ) i j) θ *
          homTrueCoord a p z j * homTrueCoord a p z i
      + ∑ i ∈ S, ∑ j ∈ S, homLieComp w (W j - W i)
          (fun θ => homNormalEntry_gen a p pb (F.Q θ) i j) θ *
          homTrueCoord a p z j * homTrueCoord a p zb i
      + ∑ i ∈ S, ∑ j ∈ S, homLieComp w (-(W i + W j))
          (fun θ => homNormalEntry_gen a p pb (F.P' θ) i j) θ *
          homTrueCoord a p zb j * homTrueCoord a p zb i := by
  -- the left side, expanded as in `homLemma1_equation_gen`
  show homLieNRaw_gen ha hp hpb w W F θ y z zb = _
  have hLop : (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homRtheta_gen ha hp hpb F l θ y z zb) =
      homLop w (fun l => homRtheta_gen ha hp hpb F l θ y z zb) := rfl
  unfold homLieNRaw_gen
  rw [homPairOmega_Rz_gen ha hp hpb hz hzb W F θ, homPairOmega_Rzb_gen ha hp hpb hz hzb W F θ,
    hLop]
  simp only [homRtheta_fin_gen ha hp hpb hz hzb, homLop_add, homLop_sumK, homLop_sum1,
    homLop_sum2]
  -- the blocks of the right side
  have hA : homLieComp w 0 F.a0 θ = homLop w (fun l => homPartial l F.a0 θ) := by
    unfold homLieComp homLop; simp
  have hB : ∑ k, homLieComp w 0 (fun θ => F.b θ k) θ * y k =
      ∑ k, homLop w (fun l => homPartial l F.b θ k) * y k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold homLieComp homLop
    simp [homPartial_proj F.comp_b hθ]
  have hCp : ∑ j ∈ S, homLieComp w (W j) (fun θ => homTrueCoord a pb (F.cp θ) j) θ *
        homTrueCoord a p z j =
      ∑ j ∈ S, homLop w (fun l => homLamDiag_gen ha (homPP hp hpb) (homPartial l F.cp θ) j) * z j
        - Complex.I * ∑ j ∈ S, homLamDiag_gen ha (homPP hp hpb) (F.cp θ) j * (W j : ℂ) * z j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [homLieComp_vec_term ha hp hpb F.comp_cp hθ]
    ring
  have hCm : ∑ j ∈ S, homLieComp w (-W j) (fun θ => homTrueCoord a pb (F.cm θ) j) θ *
        homTrueCoord a p zb j =
      ∑ j ∈ S, homLop w (fun l => homLamDiag_gen ha (homPP hp hpb) (homPartial l F.cm θ) j) * zb j
        + Complex.I * ∑ j ∈ S, homLamDiag_gen ha (homPP hp hpb) (F.cm θ) j * (W j : ℂ) * zb j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [homLieComp_vec_term ha hp hpb F.comp_cm hθ]
    push_cast
    ring
  have hsymP : ∀ i j, homSent_gen ha hp hpb (F.P θ) i j = homSent_gen ha hp hpb (F.P θ) j i :=
    fun i j => homLam_entry_symm_gen ha hp hpb (F.symP θ hθ) i j
  have hsymP' : ∀ i j, homSent_gen ha hp hpb (F.P' θ) i j = homSent_gen ha hp hpb (F.P' θ) j i :=
    fun i j => homLam_entry_symm_gen ha hp hpb (F.symP' θ hθ) i j
  have hQt : ∀ i j, homSent_gen ha hp hpb (F.Qt θ) i j = homSent_gen ha hp hpb (F.Q θ) j i := by
    intro i j
    unfold homSent_gen
    rw [homLam_entry_eq_gen ha hp hpb, homLam_entry_eq_gen ha hp hpb, F.transQ θ hθ i j,
      mul_comm (homWt a p i : ℂ)]
  have hP : ∑ i ∈ S, ∑ j ∈ S, homLieComp w (W i + W j)
        (fun θ => homNormalEntry_gen a p pb (F.P θ) i j) θ *
        homTrueCoord a p z j * homTrueCoord a p z i =
      ∑ i ∈ S, ∑ j ∈ S, homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.P θ) i j) *
          z j * z i
        - Complex.I * (2 * ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * homSent_gen ha hp hpb (F.P θ) i j *
          z j * z i) := by
    have e : ∀ i j, homLieComp w (W i + W j) (fun θ => homNormalEntry_gen a p pb (F.P θ) i j) θ *
        homTrueCoord a p z j * homTrueCoord a p z i =
        homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.P θ) i j) * z j * z i
          - Complex.I * ((W i : ℂ) * homSent_gen ha hp hpb (F.P θ) i j * z j * z i)
          - Complex.I * ((W j : ℂ) * homSent_gen ha hp hpb (F.P θ) i j * z j * z i) := by
      intro i j
      rw [homLieComp_mat_term ha hp hpb F.comp_P hθ]
      push_cast
      ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [homSum2_swap_sym S _ hsymP W z]
    ring
  have hQ : ∑ i ∈ S, ∑ j ∈ S, homLieComp w (W j - W i)
        (fun θ => homNormalEntry_gen a p pb (F.Q θ) i j) θ *
        homTrueCoord a p z j * homTrueCoord a p zb i =
      ∑ i ∈ S, ∑ j ∈ S, homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.Q θ) i j) *
          z j * zb i
        - Complex.I * ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * homSent_gen ha hp hpb (F.Qt θ) i j *
          zb j * z i
        + Complex.I * ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * homSent_gen ha hp hpb (F.Q θ) i j *
          z j * zb i := by
    have e : ∀ i j, homLieComp w (W j - W i) (fun θ => homNormalEntry_gen a p pb (F.Q θ) i j) θ *
        homTrueCoord a p z j * homTrueCoord a p zb i =
        homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.Q θ) i j) * z j * zb i
          - Complex.I * ((W j : ℂ) * homSent_gen ha hp hpb (F.Q θ) i j * z j * zb i)
          + Complex.I * ((W i : ℂ) * homSent_gen ha hp hpb (F.Q θ) i j * z j * zb i) := by
      intro i j
      rw [homLieComp_mat_term ha hp hpb F.comp_Q hθ]
      push_cast
      ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [homSum2_swap_trans S _ _ hQt W z zb]
  have hP' : ∑ i ∈ S, ∑ j ∈ S, homLieComp w (-(W i + W j))
        (fun θ => homNormalEntry_gen a p pb (F.P' θ) i j) θ *
        homTrueCoord a p zb j * homTrueCoord a p zb i =
      ∑ i ∈ S, ∑ j ∈ S, homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.P' θ) i j) *
          zb j * zb i
        + Complex.I * (2 * ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * homSent_gen ha hp hpb (F.P' θ) i j *
          zb j * zb i) := by
    have e : ∀ i j, homLieComp w (-(W i + W j))
        (fun θ => homNormalEntry_gen a p pb (F.P' θ) i j) θ *
        homTrueCoord a p zb j * homTrueCoord a p zb i =
        homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.P' θ) i j) * zb j * zb i
          + Complex.I * ((W i : ℂ) * homSent_gen ha hp hpb (F.P' θ) i j * zb j * zb i)
          + Complex.I * ((W j : ℂ) * homSent_gen ha hp hpb (F.P' θ) i j * zb j * zb i) := by
      intro i j
      rw [homLieComp_mat_term ha hp hpb F.comp_P' hθ]
      push_cast
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [homSum2_swap_sym S _ hsymP' W zb]
    ring
  rw [hA, hB, hCp, hCm, hP, hQ, hP']
  ring

end expansion

section headline

variable {a p pb s : ℝ}

/-- **Lemma `bpW:w4:lie` (iii), the Lie-coefficient rule** (step `stepW:w4:liecoef`; general
`F ∈ 𝒯_s`, general `p_+`, any carrier evidence for the pairings of `L_N`): for finitely
supported `z, \bar z` and `θ ∈ T_s`, `L_N F` is the finite expression `bpW:w4:R` for `F` with
each coefficient function replaced by `homLieComp w λ g`, and the `k`-th Fourier coefficient of
each replaced component is `iδ` times that of the component of `F`, with `δ = ⟨k,ω⟩` for `a_F`,
`b_F`, `δ^+_{k,j}` for `c^+_{F,j}`, `δ^-_{k,j}` for `c^-_{F,j}`, `δ^P_{k,ij}` for `P_{F,ij}`,
`δ^Q_{k,ij}` for `Q_{F,ij}` and `δ^{P'}_{k,ij}` for `P'_{F,ij}`. -/
theorem homLemma_lie_iii_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {W : ℕ+ → ℝ}
    (hC : HomOmegaCarrier ha hp hpb W) (w : Fin 2 → ℝ) (F : HomTaylor_gen a p pb s)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) (y : Fin 2 → ℂ) {S : Finset ℕ+}
    {z zb : HomL2} (hz : ∀ j ∉ S, z j = 0) (hzb : ∀ j ∉ S, zb j = 0) :
    (homLieN_gen ha hp hpb hC w F θ y z zb =
      homLieComp w 0 F.a0 θ
      + ∑ k, homLieComp w 0 (fun θ => F.b θ k) θ * y k
      + ∑ j ∈ S, homLieComp w (W j) (fun θ => homTrueCoord a pb (F.cp θ) j) θ *
          homTrueCoord a p z j
      + ∑ j ∈ S, homLieComp w (-W j) (fun θ => homTrueCoord a pb (F.cm θ) j) θ *
          homTrueCoord a p zb j
      + ∑ i ∈ S, ∑ j ∈ S, homLieComp w (W i + W j)
          (fun θ => homNormalEntry_gen a p pb (F.P θ) i j) θ *
          homTrueCoord a p z j * homTrueCoord a p z i
      + ∑ i ∈ S, ∑ j ∈ S, homLieComp w (W j - W i)
          (fun θ => homNormalEntry_gen a p pb (F.Q θ) i j) θ *
          homTrueCoord a p z j * homTrueCoord a p zb i
      + ∑ i ∈ S, ∑ j ∈ S, homLieComp w (-(W i + W j))
          (fun θ => homNormalEntry_gen a p pb (F.P' θ) i j) θ *
          homTrueCoord a p zb j * homTrueCoord a p zb i) ∧
    (∀ k, homCoeff (homLieComp w 0 F.a0) k =
      Complex.I * (homDelta0 w k : ℂ) * homCoeff F.a0 k) ∧
    (∀ k m, homCoeff (homLieComp w 0 fun θ => F.b θ m) k =
      Complex.I * (homDelta0 w k : ℂ) * homCoeff F.b k m) ∧
    (∀ k j, homCoeff (homLieComp w (W j) fun θ => homTrueCoord a pb (F.cp θ) j) k =
      Complex.I * (homDeltaPlus w W k j : ℂ) * homTrueCoord a pb (homCoeff F.cp k) j) ∧
    (∀ k j, homCoeff (homLieComp w (-W j) fun θ => homTrueCoord a pb (F.cm θ) j) k =
      Complex.I * (homDeltaMinus w W k j : ℂ) * homTrueCoord a pb (homCoeff F.cm k) j) ∧
    (∀ k i j, homCoeff (homLieComp w (W i + W j)
        fun θ => homNormalEntry_gen a p pb (F.P θ) i j) k =
      Complex.I * (homDeltaP w W k i j : ℂ) * homNormalEntry_gen a p pb (homCoeff F.P k) i j) ∧
    (∀ k i j, homCoeff (homLieComp w (W j - W i)
        fun θ => homNormalEntry_gen a p pb (F.Q θ) i j) k =
      Complex.I * (homDeltaQ w W k i j : ℂ) * homNormalEntry_gen a p pb (homCoeff F.Q k) i j) ∧
    (∀ k i j, homCoeff (homLieComp w (-(W i + W j))
        fun θ => homNormalEntry_gen a p pb (F.P' θ) i j) k =
      Complex.I * (homDeltaP' w W k i j : ℂ) *
        homNormalEntry_gen a p pb (homCoeff F.P' k) i j) := by
  have hs : 0 < s := lt_of_le_of_lt (abs_nonneg _) (hθ 0)
  exact ⟨homLieN_fin_expansion_gen ha hp hpb hC w F hθ y hz hzb,
    homLieComp_coeff_a hs F w, fun k m => homLieComp_coeff_b hs F w k m,
    homLieComp_coeff_cp hs F w W, homLieComp_coeff_cm hs F w W, homLieComp_coeff_P hs F w W,
    homLieComp_coeff_Q hs F w W, homLieComp_coeff_P' hs F w W⟩

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ : ℝ}

/-- **Lemma `bpW:w4:lie` (iii), the Lie-coefficient rule, `p_+ = p + 1`** (step
`stepW:w4:liecoef`; the original W4 setting): under the frequency hypotheses `HomFreqHyp` at
`ξ ∈ Π` (which supply the carrier of the pairings of `L_N`), for every `F ∈ 𝒯_s`, `θ ∈ T_s` and
finitely supported `z, \bar z`, the statement of `homLemma_lie_iii_gen` with `ω = ω(ξ)`,
`Ω = Ω(ξ)`. -/
theorem homLemma_lie_iii (h : HomFreqHyp Par ω Ω M0 Mω MΩ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (F : HomTaylor a p s) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (y : Fin 2 → ℂ) {S : Finset ℕ+} {z zb : HomL2}
    (hz : ∀ j ∉ S, z j = 0) (hzb : ∀ j ∉ S, zb j = 0) :
    (homLieN_gen ha hp (homPlusOne_le p)
        (homOmegaCarrier_of_bound ha hp (homPlusOne_le p) (by linarith)
          (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ)) (ω ξ) F θ y z zb =
      homLieComp (ω ξ) 0 F.a0 θ
      + ∑ k, homLieComp (ω ξ) 0 (fun θ => F.b θ k) θ * y k
      + ∑ j ∈ S, homLieComp (ω ξ) (Ω ξ j) (fun θ => homTrueCoord a (p + 1) (F.cp θ) j) θ *
          homTrueCoord a p z j
      + ∑ j ∈ S, homLieComp (ω ξ) (-Ω ξ j) (fun θ => homTrueCoord a (p + 1) (F.cm θ) j) θ *
          homTrueCoord a p zb j
      + ∑ i ∈ S, ∑ j ∈ S, homLieComp (ω ξ) (Ω ξ i + Ω ξ j)
          (fun θ => homNormalEntry a p (F.P θ) i j) θ *
          homTrueCoord a p z j * homTrueCoord a p z i
      + ∑ i ∈ S, ∑ j ∈ S, homLieComp (ω ξ) (Ω ξ j - Ω ξ i)
          (fun θ => homNormalEntry a p (F.Q θ) i j) θ *
          homTrueCoord a p z j * homTrueCoord a p zb i
      + ∑ i ∈ S, ∑ j ∈ S, homLieComp (ω ξ) (-(Ω ξ i + Ω ξ j))
          (fun θ => homNormalEntry a p (F.P' θ) i j) θ *
          homTrueCoord a p zb j * homTrueCoord a p zb i) ∧
    (∀ k, homCoeff (homLieComp (ω ξ) 0 F.a0) k =
      Complex.I * (homDelta0 (ω ξ) k : ℂ) * homCoeff F.a0 k) ∧
    (∀ k m, homCoeff (homLieComp (ω ξ) 0 fun θ => F.b θ m) k =
      Complex.I * (homDelta0 (ω ξ) k : ℂ) * homCoeff F.b k m) ∧
    (∀ k j, homCoeff (homLieComp (ω ξ) (Ω ξ j) fun θ => homTrueCoord a (p + 1) (F.cp θ) j) k =
      Complex.I * (homDeltaPlus (ω ξ) (Ω ξ) k j : ℂ) *
        homTrueCoord a (p + 1) (homCoeff F.cp k) j) ∧
    (∀ k j, homCoeff (homLieComp (ω ξ) (-Ω ξ j) fun θ => homTrueCoord a (p + 1) (F.cm θ) j) k =
      Complex.I * (homDeltaMinus (ω ξ) (Ω ξ) k j : ℂ) *
        homTrueCoord a (p + 1) (homCoeff F.cm k) j) ∧
    (∀ k i j, homCoeff (homLieComp (ω ξ) (Ω ξ i + Ω ξ j)
        fun θ => homNormalEntry a p (F.P θ) i j) k =
      Complex.I * (homDeltaP (ω ξ) (Ω ξ) k i j : ℂ) * homNormalEntry a p (homCoeff F.P k) i j) ∧
    (∀ k i j, homCoeff (homLieComp (ω ξ) (Ω ξ j - Ω ξ i)
        fun θ => homNormalEntry a p (F.Q θ) i j) k =
      Complex.I * (homDeltaQ (ω ξ) (Ω ξ) k i j : ℂ) * homNormalEntry a p (homCoeff F.Q k) i j) ∧
    (∀ k i j, homCoeff (homLieComp (ω ξ) (-(Ω ξ i + Ω ξ j))
        fun θ => homNormalEntry a p (F.P' θ) i j) k =
      Complex.I * (homDeltaP' (ω ξ) (Ω ξ) k i j : ℂ) *
        homNormalEntry a p (homCoeff F.P' k) i j) :=
  homLemma_lie_iii_gen ha hp (homPlusOne_le p) _ (ω ξ) F hθ y hz hzb

end headline

end KAM.Wave
