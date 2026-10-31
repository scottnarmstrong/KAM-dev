/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneEq
public import KAM.Wave.Homological.LemmaOneFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The entrywise equations of the seven components (`bpW:w4:lemma1`, step *The equation*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

For `F = homSolveTaylor_gen … R` and `θ ∈ T_{s-σ}` (writing `Δ_l = ∂_{θ_l}`, `𝔏 g = (2π)⁻¹ ∑_l ω_l
    Δ_l
    g`):
* `homEq_a`: `𝔏 a_F = a - â₀`; `homEq_b`: `𝔏 b_{F,k} = b_k - \hat b_{0,k}`;
* `homEq_cp_gen`, `homEq_cm_gen`: `𝔏 (Dc^±_F)_j ∓ iΩ_j (Dc^±_F)_j = (Dc^±)_j`;
* `homEq_P_gen`, `homEq_P'_gen`: `𝔏 S(P_F)_ij ∓ i(Ω_i+Ω_j) S(P_F)_ij = S(P)_ij`;
* `homEq_Q_gen`: `𝔏 S(Q_F)_ij - i(Ω_j - Ω_i) S(Q_F)_ij = S(Q)_ij - δ_{ij} S(Q̂₀)_ij`,
with `S(M)_ij = homSent_gen M i j = D_i M̂_ij`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

theorem HomHadamardBound.norm_le' {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c)
    (i j : ℕ+) : ‖d i j‖ ≤ c := by
  by_cases hij : i = j
  · subst hij; exact h.diag i
  · refine (h.off i j hij).trans ?_
    have h1 : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
      have : (i : ℤ) ≠ j := by exact_mod_cast hij
      have h2 : (1 : ℤ) ≤ |(i : ℤ) - j| := Int.one_le_abs (sub_ne_zero.mpr this)
      have h3 : (1 : ℝ) ≤ |((i : ℤ) - j : ℤ)| := by exact_mod_cast h2
      simpa using h3
    exact div_le_self h.homNonneg h1

theorem homInv_resonance {δ lam kz : ℝ} (hδ : δ ≠ 0) (h : δ = kz - lam) :
    Complex.I * ((kz : ℂ) - lam) * homInv δ = 1 := by
  unfold homInv
  have : ((kz : ℂ) - lam) = (δ : ℂ) := by rw [h]; push_cast; ring
  rw [this]
  have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ
  field_simp

variable {a p pb s σ τ α r ε : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

section fam

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 <
    σ)
  (hσs : σ < s) (hm : HomMultBounds τ α w W) (R : HomTaylor_gen a p pb s)
  (hX : HomFieldBound_gen ha hp hpb r ε R) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
include ha hp hpb hr hτ hα hσ hσs hm hX hθ

theorem homEq_a :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homPartial l
        (homSolveTaylor_gen hτ hα hσ hσs hm R).a0 θ) =
      R.a0 θ - homCoeff R.a0 0 := by
  obtain ⟨C, hC⟩ := R.comp_a0.2.2
  have := homFamily_eq hτ hα le_rfl le_rfl hσ hσs w 0 (ContinuousLinearMap.id ℂ ℂ)
    (T := homTscal w) (homMultA0 w) (norm_homTscal_le hm) (fun k => by simp [homTscal])
    hm.a0
    (fun k hk => by
      rw [homMultA0, if_neg hk]
      exact homInv_resonance (hm.nz0 k hk) (by simp [homDelta0]))
    R.comp_a0.1 R.comp_a0.2.1 hC (mΛ := C) (fun z hz => by simpa using hC z hz)
    (mΛ' := 2 * Real.pi * r ^ 2 * ε)
    (fun i z hz => by simpa using homAngle_a_gen ha hp hpb hr R hX hz i) hθ
  simpa [homSolveTaylor_gen] using this

theorem homEq_b (k : Fin 2) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homPartial l
        (homSolveTaylor_gen hτ hα hσ hσs hm R).b θ k) =
      R.b θ k - homCoeff R.b 0 k := by
  obtain ⟨C, hC⟩ := R.comp_b.2.2
  have hbd : ∀ (l : Fin 2) z, z ∈ complexStrip 2 s →
      ‖homPartial l (fun z => (ContinuousLinearMap.proj k : (Fin 2 → ℂ) →L[ℂ] ℂ) (R.b z)) z‖ ≤
        2 * Real.pi * ε := by
    intro l z hz
    rw [homPartial_clm _ (R.comp_b.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz)) l]
    have h1 := (homAngle_b_gen ha hp hpb hr R hX hz l)
    have h2 : ‖homPartial l R.b z k‖ ≤ ∑ k', ‖homPartial l R.b z k'‖ :=
      Finset.single_le_sum (f := fun k' => ‖homPartial l R.b z k'‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ k)
    simpa using h2.trans h1
  have := homFamily_eq hτ hα le_rfl le_rfl hσ hσs w 0 (ContinuousLinearMap.proj k)
    (T := homTvec w) (homMultA0 w) (norm_homTvec_le hm)
    (fun k' => by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [homTvec])
    hm.a0
    (fun k' hk => by
      rw [homMultA0, if_neg hk]
      exact homInv_resonance (hm.nz0 k' hk) (by simp [homDelta0]))
    R.comp_b.1 R.comp_b.2.1 hC (mΛ := ‖(ContinuousLinearMap.proj k : (Fin 2 → ℂ) →L[ℂ] ℂ)‖ * C)
    (fun z hz => ((ContinuousLinearMap.proj k : (Fin 2 → ℂ) →L[ℂ] ℂ).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    hbd hθ
  have hc' : homCoeff (fun z => R.b z k) 0 = homCoeff R.b 0 k := by
    simpa using homCoeff_clm (hσ.trans hσs) R.comp_b.1 (ContinuousLinearMap.proj k) 0
  simpa [homSolveTaylor_gen, hc'] using this


theorem homEq_cp_gen (j : ℕ+) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homLamDiag_gen ha (homPP hp hpb) (homPartial l
        (homSolveTaylor_gen hτ hα hσ hσs hm R).cp θ) j)
      - Complex.I * (W j : ℝ) * homLamDiag_gen ha (homPP hp hpb)
        ((homSolveTaylor_gen hτ hα hσ hσs hm R).cp θ) j = homLamDiag_gen ha (homPP hp hpb) (R.cp θ)
            j := by
  obtain ⟨C, hC⟩ := R.comp_cp.2.2
  set Λ : HomL2 →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j).comp (homLamDiag_gen ha (homPP hp
      hpb))
      with hΛdef
  have hΛ : ∀ x : HomL2, Λ x = homLamDiag_gen ha (homPP hp hpb) x j := fun x => rfl
  have := homFamily_eq_nonres hτ hα le_rfl le_rfl hσ hσs w (W j) Λ
    (T := homTdp hm) (fun k => homMultDp w W k j) (norm_homTdp_le hm)
    (fun k => by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.comp_apply, hΛ, homTdp, weightedDiagCLM_apply,
          homLamDiag_apply_gen,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      ring)
    (fun k => by simpa using hm.dp k j)
    (fun k => homInv_resonance (hm.nzp k j) (by simp [homDeltaPlus]))
    R.comp_cp.1 R.comp_cp.2.1 hC (mΛ := ‖Λ‖ * C)
    (fun z hz => (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε)
    (fun i z hz => by
      rw [homPartial_clm Λ (R.comp_cp.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz)) i,
        hΛ]
      refine (lp.norm_apply_le_norm (by norm_num) _ j).trans ?_
      exact (fun z hz i => (homComp_angle_gen ha hp hpb hr R hX hz i).2.2.1) z hz i) hθ
  simpa [hΛ, homSolveTaylor_gen] using this

theorem homEq_cm_gen (j : ℕ+) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homLamDiag_gen ha (homPP hp hpb) (homPartial l
        (homSolveTaylor_gen hτ hα hσ hσs hm R).cm θ) j)
      - Complex.I * (-W j : ℝ) * homLamDiag_gen ha (homPP hp hpb)
        ((homSolveTaylor_gen hτ hα hσ hσs hm R).cm θ) j = homLamDiag_gen ha (homPP hp hpb) (R.cm θ)
            j := by
  obtain ⟨C, hC⟩ := R.comp_cm.2.2
  set Λ : HomL2 →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j).comp (homLamDiag_gen ha (homPP hp
      hpb))
      with hΛdef
  have hΛ : ∀ x : HomL2, Λ x = homLamDiag_gen ha (homPP hp hpb) x j := fun x => rfl
  have := homFamily_eq_nonres hτ hα le_rfl le_rfl hσ hσs w (-W j) Λ
    (T := homTdm hm) (fun k => homMultDm w W k j) (norm_homTdm_le hm)
    (fun k => by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.comp_apply, hΛ, homTdm, weightedDiagCLM_apply,
          homLamDiag_apply_gen,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      ring)
    (fun k => by simpa using hm.dm k j)
    (fun k => homInv_resonance (hm.nzm k j) (by simp [homDeltaMinus]))
    R.comp_cm.1 R.comp_cm.2.1 hC (mΛ := ‖Λ‖ * C)
    (fun z hz => (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε)
    (fun i z hz => by
      rw [homPartial_clm Λ (R.comp_cm.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz)) i,
        hΛ]
      refine (lp.norm_apply_le_norm (by norm_num) _ j).trans ?_
      exact (fun z hz i => (homComp_angle_gen ha hp hpb hr R hX hz i).2.2.2.1) z hz i) hθ
  simpa [hΛ, homSolveTaylor_gen] using this


theorem homEq_P_gen (i j : ℕ+) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homSent_gen ha hp hpb (homPartial l
        (homSolveTaylor_gen hτ hα hσ hσs hm R).P θ) i j)
      - Complex.I * (W i + W j : ℝ) * homSent_gen ha hp hpb
        ((homSolveTaylor_gen hτ hα hσ hσs hm R).P θ) i j = homSent_gen ha hp hpb (R.P θ) i j := by
  obtain ⟨C, hC⟩ := R.comp_P.2.2
  set Λ : HomOp →L[ℂ] ℂ := (homEntryCLM i j).comp (homLamCLM_gen ha (homPP hp hpb)) with hΛdef
  have hΛ : ∀ A : HomOp, Λ A = homSent_gen ha hp hpb A i j := fun A => rfl
  have := homFamily_eq_nonres hτ hα one_le_homKS le_rfl hσ hσs w (W i + W j) Λ
    (T := homTP hm) (fun k => homDP w W k i j) (norm_homTP_le hm)
    (fun k => by
      refine ContinuousLinearMap.ext fun A => ?_
      simp only [ContinuousLinearMap.comp_apply, hΛ, homTP, homHadamardCLM_apply, homSent_gen,
        ← homHadamardOp_lam_gen ha (homPP hp hpb) (hm.P k), homHadamard_entry,
            kamEntry_homLamCLM_gen,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      )
    (fun k => by simpa using (hm.P k).norm_le' i j)
    (fun k => homInv_resonance (hm.nzP k i j) (by simp [homDeltaP]; ring))
    R.comp_P.1 R.comp_P.2.1 hC (mΛ := ‖Λ‖ * C)
    (fun z hz => (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    (mΛ' := 4 * Real.pi * ε)
    (fun l z hz => by
      rw [homPartial_clm Λ (R.comp_P.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz)) l,
        hΛ]
      exact (norm_kamEntry_le _ i j).trans ((fun z hz l => (homComp_angle_gen ha hp hpb hr R hX hz
          l).2.2.2.2.1) z hz l)) hθ
  simpa [hΛ, homSolveTaylor_gen] using this

theorem homEq_P'_gen (i j : ℕ+) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homSent_gen ha hp hpb (homPartial l
        (homSolveTaylor_gen hτ hα hσ hσs hm R).P' θ) i j)
      - Complex.I * (-(W i + W j) : ℝ) * homSent_gen ha hp hpb
        ((homSolveTaylor_gen hτ hα hσ hσs hm R).P' θ) i j = homSent_gen ha hp hpb (R.P' θ) i j := by
  obtain ⟨C, hC⟩ := R.comp_P'.2.2
  set Λ : HomOp →L[ℂ] ℂ := (homEntryCLM i j).comp (homLamCLM_gen ha (homPP hp hpb)) with hΛdef
  have hΛ : ∀ A : HomOp, Λ A = homSent_gen ha hp hpb A i j := fun A => rfl
  have := homFamily_eq_nonres hτ hα one_le_homKS le_rfl hσ hσs w (-(W i + W j)) Λ
    (T := homTP' hm) (fun k => homDP' w W k i j) (norm_homTP'_le hm)
    (fun k => by
      refine ContinuousLinearMap.ext fun A => ?_
      simp only [ContinuousLinearMap.comp_apply, hΛ, homTP', homHadamardCLM_apply, homSent_gen,
        ← homHadamardOp_lam_gen ha (homPP hp hpb) (hm.P' k), homHadamard_entry,
            kamEntry_homLamCLM_gen,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      )
    (fun k => by simpa using (hm.P' k).norm_le' i j)
    (fun k => homInv_resonance (hm.nzP' k i j) (by simp [homDeltaP']; ring))
    R.comp_P'.1 R.comp_P'.2.1 hC (mΛ := ‖Λ‖ * C)
    (fun z hz => (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    (mΛ' := 4 * Real.pi * ε)
    (fun l z hz => by
      rw [homPartial_clm Λ (R.comp_P'.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz)) l,
        hΛ]
      exact (norm_kamEntry_le _ i j).trans ((fun z hz l => (homComp_angle_gen ha hp hpb hr R hX hz
          l).2.2.2.2.2.1) z hz l)) hθ
  simpa [hΛ, homSolveTaylor_gen] using this


theorem homEq_Q_gen (i j : ℕ+) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homSent_gen ha hp hpb (homPartial l
        (homSolveTaylor_gen hτ hα hσ hσs hm R).Q θ) i j)
      - Complex.I * ((W j - W i : ℝ) : ℂ) * homSent_gen ha hp hpb
        ((homSolveTaylor_gen hτ hα hσ hσs hm R).Q θ) i j =
      homSent_gen ha hp hpb (R.Q θ) i j -
        (if i = j then homSent_gen ha hp hpb (homCoeff R.Q 0) i j else 0) := by
  obtain ⟨C, hC⟩ := R.comp_Q.2.2
  set Λ : HomOp →L[ℂ] ℂ := (homEntryCLM i j).comp (homLamCLM_gen ha (homPP hp hpb)) with hΛdef
  have hΛ : ∀ A : HomOp, Λ A = homSent_gen ha hp hpb A i j := fun A => rfl
  have hres : ∀ k : Fin 2 → ℤ, k ≠ 0 →
      Complex.I * ((homPairZ k w : ℂ) - ((W j - W i : ℝ) : ℂ)) * homDQ w W k i j = 1 := by
    intro k hk
    rw [homDQ, if_neg (fun h => hk h.1)]
    exact homInv_resonance (hm.nzQ k i j (Or.inl hk)) (by simp [homDeltaQ]; ring)
  have := homFamily_eq hτ hα one_le_homKS le_rfl hσ hσs w (W j - W i) Λ
    (T := homTQ hm) (fun k => homDQ w W k i j) (norm_homTQ_le hm)
    (fun k => by
      refine ContinuousLinearMap.ext fun A => ?_
      simp only [ContinuousLinearMap.comp_apply, hΛ, homTQ, homHadamardCLM_apply, homSent_gen,
        ← homHadamardOp_lam_gen ha (homPP hp hpb) (hm.Q k), homHadamard_entry,
            kamEntry_homLamCLM_gen,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul])
    (fun k => by simpa using (hm.Q k).norm_le' i j) hres
    R.comp_Q.1 R.comp_Q.2.1 hC (mΛ := ‖Λ‖ * C)
    (fun z hz => (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    (mΛ' := 16 * Real.pi * ε)
    (fun l z hz => by
      rw [homPartial_clm Λ (R.comp_Q.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz)) l,
        hΛ]
      exact (norm_kamEntry_le _ i j).trans (homComp_angle_gen ha hp hpb hr R hX hz l).2.2.2.2.2.2)
          hθ
  have hs : 0 < s := hσ.trans hσs
  have hc : homCoeff (fun z => Λ (R.Q z)) 0 = homSent_gen ha hp hpb (homCoeff R.Q 0) i j := by
    rw [homCoeff_clm hs R.comp_Q.1 Λ 0, hΛ]
  have he : (1 + Complex.I * ((W j - W i : ℝ) : ℂ) * homDQ w W 0 i j) =
      if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst hij; simp
    · simp only [hij, if_false]
      have h0 : Complex.I * (((homPairZ 0 w : ℝ) : ℂ) - ((W j - W i : ℝ) : ℂ)) * homDQ w W 0 i j =
          1 := by
        rw [homDQ, if_neg (fun h => hij h.2)]
        exact homInv_resonance (hm.nzQ 0 i j (Or.inr hij)) (by simp [homDeltaQ, homPairZ] <;> ring)
      have hz : (homPairZ 0 w : ℂ) = 0 := by simp [homPairZ]
      rw [hz] at h0
      linear_combination -h0
  rw [hc, he] at this
  simp only [hΛ] at this
  have e : ∀ x : ℂ, (if i = j then (1 : ℂ) else 0) * x = if i = j then x else 0 := fun x => by
    split_ifs <;> simp
  rw [e] at this
  simpa [homSolveTaylor_gen] using this

end fam

end KAM.Wave
