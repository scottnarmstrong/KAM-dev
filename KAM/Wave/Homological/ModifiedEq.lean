/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ModifiedSolve
public import KAM.Wave.Homological.LemmaOneEquation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The entrywise equations with modified divisors (`bpW:w5:w4-modified` (i), the equation)

Off-frontier, source-faithful infrastructure (W5-MODIFIED, blueprint `bpW:w5:w4-modified`); the
dependency graph is still being built.

For `F = homModSolveTaylor … R` and `θ ∈ T_{s-σ}` the entrywise equations of W4's step *The
equation* hold with `R` replaced by its reweighting `R' = homReweight R` (same entries, same
pairings), `𝔏 g = (2π)⁻¹ ∑_l ω_l ∂_{θ_l} g`:
* `homModEq_a`, `homModEq_b`, `homModEq_cp`, `homModEq_cm`, `homModEq_P`, `homModEq_P'`: as in W4
  (the multipliers of `c^±, P, P'` act on the reweighted data);
* `homModEq_Q`: `𝔏 S(Q_F)_ij - i(Ω_j - Ω_i) S(Q_F)_ij = S(R'.Q)_ij - δ_ij S([R'.Q])_ij` for the
  twisted `Q`-solve, via `homFamily_eq_two` (two functionals `Λ₁ ∘ T_k = μ_k Λ₀`: the sent entries
  of the `p₊`-weighted matrix of the twisted Hadamard image are `d_ij` times the sent entries of the
  `p+1`-weighted matrix of the data).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

section two

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem homSolve_image_eq_two {s σ m κ α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ)
    (hσ : 0 < σ) (hσs : σ < s) {T : (Fin 2 → ℤ) → E →L[ℂ] E} {T' : (Fin 2 → ℤ) → ℂ →L[ℂ] ℂ}
    (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α) (Λ₀ Λ₁ : E →L[ℂ] ℂ)
    (hΛ : ∀ k, Λ₁.comp (T k) = (T' k).comp Λ₀) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    Λ₁ (homSolve T u θ) = homSolve T' (fun z => Λ₀ (u z)) θ := by
  have hs : 0 < s := hσ.trans hσs
  obtain ⟨hsum, -⟩ := homSolve_spec hτ hα hκ hσ hσs hT hu hp hm
  exact homSolve_intertwine (T' := T') (ρ := s - σ) hs Λ₀ Λ₁ hΛ hu hsum hθ

theorem homSolve_partial_image_eq_two {s σ m κ α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ)
    (hσ : 0 < σ) (hσs : σ < s) {T : (Fin 2 → ℤ) → E →L[ℂ] E} {T' : (Fin 2 → ℤ) → ℂ →L[ℂ] ℂ}
    (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α) (Λ₀ Λ₁ : E →L[ℂ] ℂ)
    (hΛ : ∀ k, Λ₁.comp (T k) = (T' k).comp Λ₀) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (i : Fin 2) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) :
    Λ₁ (homPartial i (homSolve T u) θ) =
      homPartial i (homSolve T' (fun z => Λ₀ (u z))) θ := by
  have hopen := isOpen_complexStrip 2 (s - σ)
  have hFd : DifferentiableOn ℂ (homSolve T u) (complexStrip 2 (s - σ)) :=
    (homSolve_spec hτ hα hκ hσ hσs hT hu hp hm).2.2.2.1
  have hev : (fun z => Λ₁ (homSolve T u z)) =ᶠ[nhds θ] homSolve T' (fun z => Λ₀ (u z)) :=
    Filter.eventually_of_mem (hopen.mem_nhds hθ) fun z hz =>
      homSolve_image_eq_two hτ hα hκ hσ hσs hT Λ₀ Λ₁ hΛ hu hp hm hz
  have hd : DifferentiableAt ℂ (homSolve T u) θ := hFd.differentiableAt (hopen.mem_nhds hθ)
  have h1 : Λ₁ (homPartial i (homSolve T u) θ) =
      homPartial i (fun z => Λ₁ (homSolve T u z)) θ := by
    unfold homPartial
    have := (Λ₁.hasFDerivAt.comp θ hd.hasFDerivAt).fderiv
    rw [show (fun z => Λ₁ (homSolve T u z)) = Λ₁ ∘ homSolve T u from rfl, this]
    rfl
  rw [h1]
  unfold homPartial; rw [hev.fderiv_eq]

/-- `homFamily_eq` with two functionals: `Λ₁ ∘ T_k = μ_k Λ₀`. -/
theorem homFamily_eq_two {s σ m mΛ mΛ' κ κ' α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ)
    (hκ' : 1 ≤ κ') (hσ : 0 < σ) (hσs : σ < s) (ω : Fin 2 → ℝ) (lam : ℝ) (Λ₀ Λ₁ : E →L[ℂ] ℂ)
    {T : (Fin 2 → ℤ) → E →L[ℂ] E} (mu : (Fin 2 → ℤ) → ℂ)
    (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α)
    (hΛ : ∀ k, Λ₁.comp (T k) = (mu k • ContinuousLinearMap.id ℂ ℂ).comp Λ₀)
    (hmu : ∀ k, ‖mu k‖ ≤ κ' * waveA τ k / α)
    (hres : ∀ k, k ≠ 0 → Complex.I * ((homPairZ k ω : ℂ) - lam) * mu k = 1)
    {u : (Fin 2 → ℂ) → E} (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (hmΛ : ∀ z ∈ complexStrip 2 s, ‖Λ₀ (u z)‖ ≤ mΛ)
    (hmΛ' : ∀ i : Fin 2, ∀ z ∈ complexStrip 2 s, ‖homPartial i (fun z => Λ₀ (u z)) z‖ ≤ mΛ')
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ i, (ω i : ℂ) * Λ₁ (homPartial i (homSolve T u) θ))
      - Complex.I * lam * Λ₁ (homSolve T u θ) =
      Λ₀ (u θ) - (1 + Complex.I * lam * mu 0) * homCoeff (fun z => Λ₀ (u z)) 0 := by
  have hΛu : DifferentiableOn ℂ (fun z => Λ₀ (u z)) (complexStrip 2 s) :=
    Λ₀.differentiable.comp_differentiableOn hu
  have hΛp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → Λ₀ (u (z + Pi.single i 1)) = Λ₀ (u z) :=
    fun i z hz => by rw [hp i z hz]
  have h1 : ∀ i : Fin 2, Λ₁ (homPartial i (homSolve T u) θ) = homPartial i
      (homSolve (fun k => mu k • ContinuousLinearMap.id ℂ ℂ) (fun z => Λ₀ (u z))) θ := fun i =>
    homSolve_partial_image_eq_two hτ hα hκ hσ hσs hT Λ₀ Λ₁ hΛ hu hp hm i hθ
  have h2 := homSolve_image_eq_two hτ hα hκ hσ hσs hT Λ₀ Λ₁ hΛ hu hp hm hθ
  simp only [h1, h2]
  exact homCohEq_scalar hτ hα hκ' hσ hσs ω lam mu hmu hres hΛu hΛp hmΛ hmΛ' hθ

end two

variable {a p pb s σ τ α r ε : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

section fam

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1) (hr : 0 < r) (hτ : 0 ≤ τ)
  (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hm : HomModMultBounds a p pb τ α w W)
  (R : HomTaylor_gen a p (p + 1) s)
  (hX : HomFieldBound_gen ha hp (homModPP1 p) r ε R) {θ : Fin 2 → ℂ}
  (hθ : θ ∈ complexStrip 2 (s - σ))
include ha hp hpb hr hτ hα hσ hσs hm hX hθ

theorem homModEq_a :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homPartial l
        (homModSolveTaylor hτ hα hσ hσs hc hm R).a0 θ) =
      R.a0 θ - homCoeff R.a0 0 := by
  obtain ⟨C, hC⟩ := R.comp_a0.2.2
  have := homFamily_eq hτ hα le_rfl le_rfl hσ hσs w 0 (ContinuousLinearMap.id ℂ ℂ)
    (T := homTscal w) (homMultA0 w) (norm_homModTscal_le hm) (fun k => by simp [homTscal])
    hm.a0
    (fun k hk => by
      rw [homMultA0, ite_eq_right hk]
      exact homInv_resonance (hm.nz0 k hk) (by simp [homDelta0]))
    R.comp_a0.1 R.comp_a0.2.1 hC (mΛ := C) (fun z hz => by simpa using hC z hz)
    (mΛ' := 2 * Real.pi * r ^ 2 * ε)
    (fun i z hz => by simpa using homAngle_a_gen ha hp (homModPP1 p) hr R hX hz i) hθ
  simpa [homModSolveTaylor] using this

theorem homModEq_b (k : Fin 2) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homPartial l
        (homModSolveTaylor hτ hα hσ hσs hc hm R).b θ k) =
      R.b θ k - homCoeff R.b 0 k := by
  obtain ⟨C, hC⟩ := R.comp_b.2.2
  have hbd : ∀ (l : Fin 2) z, z ∈ complexStrip 2 s →
      ‖homPartial l (fun z => (ContinuousLinearMap.proj k : (Fin 2 → ℂ) →L[ℂ] ℂ) (R.b z)) z‖ ≤
        2 * Real.pi * ε := by
    intro l z hz
    rw [homPartial_clm _ (R.comp_b.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz)) l]
    have h1 := (homAngle_b_gen ha hp (homModPP1 p) hr R hX hz l)
    have h2 : ‖homPartial l R.b z k‖ ≤ ∑ k', ‖homPartial l R.b z k'‖ :=
      Finset.single_le_sum (f := fun k' => ‖homPartial l R.b z k'‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ k)
    simpa using h2.trans h1
  have := homFamily_eq hτ hα le_rfl le_rfl hσ hσs w 0 (ContinuousLinearMap.proj k)
    (T := homTvec w) (homMultA0 w) (norm_homModTvec_le hm)
    (fun k' => by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [homTvec])
    hm.a0
    (fun k' hk => by
      rw [homMultA0, ite_eq_right hk]
      exact homInv_resonance (hm.nz0 k' hk) (by simp [homDelta0]))
    R.comp_b.1 R.comp_b.2.1 hC (mΛ := ‖(ContinuousLinearMap.proj k : (Fin 2 → ℂ) →L[ℂ] ℂ)‖ * C)
    (fun z hz => ((ContinuousLinearMap.proj k : (Fin 2 → ℂ) →L[ℂ] ℂ).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    hbd hθ
  have hc' : homCoeff (fun z => R.b z k) 0 = homCoeff R.b 0 k := by
    simpa using homCoeff_clm (hσ.trans hσs) R.comp_b.1 (ContinuousLinearMap.proj k) 0
  simpa [homModSolveTaylor, hc'] using this

theorem homModEq_cp (j : ℕ+) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homLamDiag_gen ha (homPP hp hpb) (homPartial l
        (homModSolveTaylor hτ hα hσ hσs hc hm R).cp θ) j)
      - Complex.I * (W j : ℝ) * homLamDiag_gen ha (homPP hp hpb)
        ((homModSolveTaylor hτ hα hσ hσs hc hm R).cp θ) j =
      homLamDiag_gen ha (homPP hp hpb) ((homReweight hc R).cp θ) j := by
  have hX' := homFieldBound_reweight ha hp hpb hc hr R hX
  set R' := homReweight hc R with hR'
  obtain ⟨C, hC⟩ := R'.comp_cp.2.2
  set Λ : HomL2 →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j).comp
    (homLamDiag_gen ha (homPP hp hpb)) with hΛdef
  have hΛ : ∀ x : HomL2, Λ x = homLamDiag_gen ha (homPP hp hpb) x j := fun x => rfl
  have := homFamily_eq_nonres hτ hα le_rfl le_rfl hσ hσs w (W j) Λ
    (T := homModTdp hm) (fun k => homMultDp w W k j) (norm_homModTdp_le hm)
    (fun k => by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.comp_apply, hΛ, homModTdp, weightedDiagCLM_apply,
        homLamDiag_apply_gen, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul]
      ring)
    (fun k => by simpa using hm.dp k j)
    (fun k => homInv_resonance (hm.nzp k j) (by simp [homDeltaPlus]))
    R'.comp_cp.1 R'.comp_cp.2.1 hC (mΛ := ‖Λ‖ * C)
    (fun z hz => (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε)
    (fun i z hz => by
      rw [homPartial_clm Λ (R'.comp_cp.1.differentiableAt
        ((isOpen_complexStrip 2 s).mem_nhds hz)) i, hΛ]
      refine (lp.norm_apply_le_norm (by norm_num) _ j).trans ?_
      exact (homComp_angle_gen ha hp hpb hr R' hX' hz i).2.2.1) hθ
  simpa [hΛ, homModSolveTaylor] using this

theorem homModEq_cm (j : ℕ+) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homLamDiag_gen ha (homPP hp hpb) (homPartial l
        (homModSolveTaylor hτ hα hσ hσs hc hm R).cm θ) j)
      - Complex.I * (-W j : ℝ) * homLamDiag_gen ha (homPP hp hpb)
        ((homModSolveTaylor hτ hα hσ hσs hc hm R).cm θ) j =
      homLamDiag_gen ha (homPP hp hpb) ((homReweight hc R).cm θ) j := by
  have hX' := homFieldBound_reweight ha hp hpb hc hr R hX
  set R' := homReweight hc R with hR'
  obtain ⟨C, hC⟩ := R'.comp_cm.2.2
  set Λ : HomL2 →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j).comp
    (homLamDiag_gen ha (homPP hp hpb)) with hΛdef
  have hΛ : ∀ x : HomL2, Λ x = homLamDiag_gen ha (homPP hp hpb) x j := fun x => rfl
  have := homFamily_eq_nonres hτ hα le_rfl le_rfl hσ hσs w (-W j) Λ
    (T := homModTdm hm) (fun k => homMultDm w W k j) (norm_homModTdm_le hm)
    (fun k => by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.comp_apply, hΛ, homModTdm, weightedDiagCLM_apply,
        homLamDiag_apply_gen, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul]
      ring)
    (fun k => by simpa using hm.dm k j)
    (fun k => homInv_resonance (hm.nzm k j) (by simp [homDeltaMinus]))
    R'.comp_cm.1 R'.comp_cm.2.1 hC (mΛ := ‖Λ‖ * C)
    (fun z hz => (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε)
    (fun i z hz => by
      rw [homPartial_clm Λ (R'.comp_cm.1.differentiableAt
        ((isOpen_complexStrip 2 s).mem_nhds hz)) i, hΛ]
      refine (lp.norm_apply_le_norm (by norm_num) _ j).trans ?_
      exact (homComp_angle_gen ha hp hpb hr R' hX' hz i).2.2.2.1) hθ
  simpa [hΛ, homModSolveTaylor] using this

theorem homModEq_P (i j : ℕ+) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homSent_gen ha hp hpb (homPartial l
        (homModSolveTaylor hτ hα hσ hσs hc hm R).P θ) i j)
      - Complex.I * (W i + W j : ℝ) * homSent_gen ha hp hpb
        ((homModSolveTaylor hτ hα hσ hσs hc hm R).P θ) i j =
      homSent_gen ha hp hpb ((homReweight hc R).P θ) i j := by
  have hX' := homFieldBound_reweight ha hp hpb hc hr R hX
  set R' := homReweight hc R with hR'
  obtain ⟨C, hC⟩ := R'.comp_P.2.2
  set Λ : HomOp →L[ℂ] ℂ := (homEntryCLM i j).comp (homLamCLM_gen ha (homPP hp hpb)) with hΛdef
  have hΛ : ∀ A : HomOp, Λ A = homSent_gen ha hp hpb A i j := fun A => rfl
  have := homFamily_eq_nonres hτ hα one_le_homKS le_rfl hσ hσs w (W i + W j) Λ
    (T := homModTP hm) (fun k => homDP w W k i j) (norm_homModTP_le hm)
    (fun k => by
      refine ContinuousLinearMap.ext fun A => ?_
      simp only [ContinuousLinearMap.comp_apply, hΛ, homModTP, homHadamardCLM_apply, homSent_gen,
        ← homHadamardOp_lam_gen ha (homPP hp hpb) (hm.P k), homHadamard_entry,
        kamEntry_homLamCLM_gen, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul])
    (fun k => by simpa using (hm.P k).norm_le' i j)
    (fun k => homInv_resonance (hm.nzP k i j) (by simp [homDeltaP]; ring))
    R'.comp_P.1 R'.comp_P.2.1 hC (mΛ := ‖Λ‖ * C)
    (fun z hz => (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    (mΛ' := 4 * Real.pi * ε)
    (fun l z hz => by
      rw [homPartial_clm Λ (R'.comp_P.1.differentiableAt
        ((isOpen_complexStrip 2 s).mem_nhds hz)) l, hΛ]
      exact (norm_kamEntry_le _ i j).trans (homComp_angle_gen ha hp hpb hr R' hX' hz
        l).2.2.2.2.1) hθ
  simpa [hΛ, homModSolveTaylor] using this

theorem homModEq_P' (i j : ℕ+) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homSent_gen ha hp hpb (homPartial l
        (homModSolveTaylor hτ hα hσ hσs hc hm R).P' θ) i j)
      - Complex.I * (-(W i + W j) : ℝ) * homSent_gen ha hp hpb
        ((homModSolveTaylor hτ hα hσ hσs hc hm R).P' θ) i j =
      homSent_gen ha hp hpb ((homReweight hc R).P' θ) i j := by
  have hX' := homFieldBound_reweight ha hp hpb hc hr R hX
  set R' := homReweight hc R with hR'
  obtain ⟨C, hC⟩ := R'.comp_P'.2.2
  set Λ : HomOp →L[ℂ] ℂ := (homEntryCLM i j).comp (homLamCLM_gen ha (homPP hp hpb)) with hΛdef
  have hΛ : ∀ A : HomOp, Λ A = homSent_gen ha hp hpb A i j := fun A => rfl
  have := homFamily_eq_nonres hτ hα one_le_homKS le_rfl hσ hσs w (-(W i + W j)) Λ
    (T := homModTP' hm) (fun k => homDP' w W k i j) (norm_homModTP'_le hm)
    (fun k => by
      refine ContinuousLinearMap.ext fun A => ?_
      simp only [ContinuousLinearMap.comp_apply, hΛ, homModTP', homHadamardCLM_apply,
        homSent_gen, ← homHadamardOp_lam_gen ha (homPP hp hpb) (hm.P' k), homHadamard_entry,
        kamEntry_homLamCLM_gen, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul])
    (fun k => by simpa using (hm.P' k).norm_le' i j)
    (fun k => homInv_resonance (hm.nzP' k i j) (by simp [homDeltaP']; ring))
    R'.comp_P'.1 R'.comp_P'.2.1 hC (mΛ := ‖Λ‖ * C)
    (fun z hz => (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    (mΛ' := 4 * Real.pi * ε)
    (fun l z hz => by
      rw [homPartial_clm Λ (R'.comp_P'.1.differentiableAt
        ((isOpen_complexStrip 2 s).mem_nhds hz)) l, hΛ]
      exact (norm_kamEntry_le _ i j).trans (homComp_angle_gen ha hp hpb hr R' hX' hz
        l).2.2.2.2.2.1) hθ
  simpa [hΛ, homModSolveTaylor] using this

/-- **The `Q`-equation with modified divisors**: the twisted solve satisfies W4's entrywise
equation for the reweighted data. -/
theorem homModEq_Q (i j : ℕ+) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homSent_gen ha hp hpb (homPartial l
        (homModSolveTaylor hτ hα hσ hσs hc hm R).Q θ) i j)
      - Complex.I * ((W j - W i : ℝ) : ℂ) * homSent_gen ha hp hpb
        ((homModSolveTaylor hτ hα hσ hσs hc hm R).Q θ) i j =
      homSent_gen ha hp hpb ((homReweight hc R).Q θ) i j -
        (if i = j then homSent_gen ha hp hpb (homCoeff (homReweight hc R).Q 0) i j else 0) := by
  have hp1 : p ≤ p + 1 := by linarith
  have hs : 0 < s := hσ.trans hσs
  obtain ⟨C, hC⟩ := R.comp_Q.2.2
  set Λ₁ : HomOp →L[ℂ] ℂ := (homEntryCLM i j).comp (homLamCLM_gen ha (homPP hp hpb)) with hΛ₁def
  set Λ₀ : HomOp →L[ℂ] ℂ := (homEntryCLM i j).comp (homLamCLM_gen ha (homPP hp hp1)) with hΛ₀def
  have hΛ₁ : ∀ A : HomOp, Λ₁ A = homSent_gen ha hp hpb A i j := fun A => rfl
  have hΛ₀ : ∀ A : HomOp, Λ₀ A = homSent_gen ha hp hp1 A i j := fun A => rfl
  have hres : ∀ k : Fin 2 → ℤ, k ≠ 0 →
      Complex.I * ((homPairZ k w : ℂ) - ((W j - W i : ℝ) : ℂ)) * homDQ w W k i j = 1 := by
    intro k hk
    rw [homDQ, ite_eq_right (fun h => hk h.1)]
    exact homInv_resonance (hm.nzQ k i j (Or.inl hk)) (by simp [homDeltaQ]; ring)
  have hentry : ∀ k (A : HomOp), Λ₁ (homModTQ hm k A) = homDQ w W k i j * Λ₀ A := by
    intro k A
    rw [hΛ₁, hΛ₀]
    unfold homSent_gen
    simp only [homModTQ, homHadamardCLM_apply, kamEntry_homLamCLM_gen, homHadamard_entry,
      homModDQ]
    rw [← homLamD_rho (a := a) (p := p) (pb := pb) i]
    ring
  have hρ := homModRatio_pos a p pb i
  have hρ1 := homModRatio_le_one (a := a) hc i
  have hκ' : 1 ≤ (homModRatio a p pb i)⁻¹ := one_le_inv₀ hρ |>.mpr hρ1
  have hbound : ∀ k, ‖homDQ w W k i j‖ ≤ (homModRatio a p pb i)⁻¹ * waveA τ k / α := by
    intro k
    have h1 := (hm.Q k).norm_le' i j
    rw [homModDQ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at h1
    rw [mul_div_assoc, ← div_eq_inv_mul, le_div_iff₀ hρ]
    linarith [mul_comm (homModRatio a p pb i) ‖homDQ w W k i j‖]
  have hΛ : ∀ k, Λ₁.comp (homModTQ hm k) =
      (homDQ w W k i j • ContinuousLinearMap.id ℂ ℂ).comp Λ₀ := fun k => by
    refine ContinuousLinearMap.ext fun A => ?_
    simp only [ContinuousLinearMap.comp_apply, hentry, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul]
  have hX₀ := fun z (hz : z ∈ complexStrip 2 s) l => homComp_angle_gen ha hp hp1 hr R hX hz l
  have := homFamily_eq_two hτ hα one_le_homKS hκ' hσ hσs w (W j - W i) Λ₀ Λ₁
    (T := homModTQ hm) (fun k => homDQ w W k i j) (norm_homModTQ_le hm) hΛ hbound hres
    R.comp_Q.1 R.comp_Q.2.1 hC (mΛ := ‖Λ₀‖ * C)
    (fun z hz => (Λ₀.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
    (mΛ' := 16 * Real.pi * ε)
    (fun l z hz => by
      rw [homPartial_clm Λ₀ (R.comp_Q.1.differentiableAt
        ((isOpen_complexStrip 2 s).mem_nhds hz)) l, hΛ₀]
      exact (norm_kamEntry_le _ i j).trans (hX₀ z hz l).2.2.2.2.2.2) hθ
  have hc0 : homCoeff (fun z => Λ₀ (R.Q z)) 0 =
      homSent_gen ha hp hpb (homCoeff (homReweight hc R).Q 0) i j := by
    rw [homCoeff_clm hs R.comp_Q.1 Λ₀ 0, hΛ₀]
    have : homCoeff (homReweight hc R).Q 0 = (homModRho a p pb hc).comp (homCoeff R.Q 0) := by
      show homCoeff (fun z => homModRhoL a p pb hc (R.Q z)) 0 = _
      rw [homCoeff_clm hs R.comp_Q.1]
      rfl
    rw [this]
    unfold homSent_gen
    rw [homLamCLM_rho ha hp hpb hc]
  have hR0 : Λ₀ (R.Q θ) = homSent_gen ha hp hpb ((homReweight hc R).Q θ) i j := by
    rw [hΛ₀]
    unfold homSent_gen
    show _ = kamEntry (homLamCLM_gen ha (homPP hp hpb) ((homModRho a p pb hc).comp (R.Q θ))) i j
    rw [homLamCLM_rho ha hp hpb hc]
  have he : (1 + Complex.I * ((W j - W i : ℝ) : ℂ) * homDQ w W 0 i j) =
      if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst hij; simp
    · simp only [hij, ite_false]
      have h0 : Complex.I * (((homPairZ 0 w : ℝ) : ℂ) - ((W j - W i : ℝ) : ℂ)) * homDQ w W 0 i j =
          1 := by
        rw [homDQ, ite_eq_right (fun h => hij h.2)]
        exact homInv_resonance (hm.nzQ 0 i j (Or.inr hij)) (by simp [homDeltaQ, homPairZ])
      have hz : (homPairZ 0 w : ℂ) = 0 := by simp [homPairZ]
      rw [hz] at h0
      linear_combination -h0
  rw [hc0, he, hR0] at this
  simp only [hΛ₁] at this
  have e : ∀ x : ℂ, (if i = j then (1 : ℂ) else 0) * x = if i = j then x else 0 := fun x => by
    split_ifs <;> simp
  rw [e] at this
  simpa [homModSolveTaylor] using this

end fam

end KAM.Wave
