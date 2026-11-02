/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneF
public import KAM.Wave.Homological.LemmaOneAssembly
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Component bounds of `F` (`bpW:w4:lemma1`, step *Component bounds of F*)

`homF_compBounds_gen`: if `|X_R|_r ≤ ε` on `D(s,r)` then the components of `F = homSolveTaylor_gen
    … R`
satisfy `HomCompBounds_gen` on `T_{s-σ}` with the scale `E₀ = B^W_σ ε/α` and `K = K_S`, by
`bpW:w4:components`, `bpW:w4:solve` (i), (iii), (iv) and the image bounds of `SolveImage`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

theorem waveBW_nonneg (τ σ : ℝ) : 0 ≤ waveBW τ σ := by
  unfold waveBW
  refine tsum_nonneg fun k => ?_
  have := Fourier.modeSize_nonneg k
  have := waveA_ge_one (τ := τ) k
  positivity

/-- A continuous linear map commutes with `∂_{θ_i}`. -/
theorem homPartial_clm {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (Λ : E →L[ℂ] G) {u : (Fin 2 → ℂ) → E}
    {z : Fin 2 → ℂ} (hu : DifferentiableAt ℂ u z) (i : Fin 2) :
    homPartial i (fun z => Λ (u z)) z = Λ (homPartial i u z) := by
  unfold homPartial
  have := (Λ.hasFDerivAt.comp z hu.hasFDerivAt).fderiv
  rw [show (fun z => Λ (u z)) = Λ ∘ u from rfl, this]
  rfl

variable {a p pb s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

theorem homLamDiag_comm_homTdp_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hm :
    HomMultBounds τ α w W)
    (k : Fin 2 → ℤ) : (homLamDiag_gen ha (homPP hp hpb)).comp (homTdp hm k) = (homTdp hm k).comp
        (homLamDiag_gen ha (homPP hp hpb))
        := by
  refine ContinuousLinearMap.ext fun v => ?_
  ext j
  simp [homTdp, homLamDiag_apply_gen]
  ring

theorem homLamDiag_comm_homTdm_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hm :
    HomMultBounds τ α w W)
    (k : Fin 2 → ℤ) : (homLamDiag_gen ha (homPP hp hpb)).comp (homTdm hm k) = (homTdm hm k).comp
        (homLamDiag_gen ha (homPP hp hpb))
        := by
  refine ContinuousLinearMap.ext fun v => ?_
  ext j
  simp [homTdm, homLamDiag_apply_gen]
  ring

theorem homLam_comm_hadamard_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {d : ℕ+ → ℕ+
    →
    ℂ} {c : ℝ}
    (h : HomHadamardBound d c) :
    (homLamCLM_gen ha (homPP hp hpb)).comp (homHadamardCLM h) = (homHadamardCLM h).comp
        (homLamCLM_gen ha
        (homPP hp hpb)) := by
  refine ContinuousLinearMap.ext fun A => ?_
  simp only [ContinuousLinearMap.comp_apply, homHadamardCLM_apply]
  exact (homHadamardOp_lam_gen ha (homPP hp hpb) h A).symm

theorem norm_sum_mul_le_of_sum_norm (β y : Fin 2 → ℂ) :
    ‖∑ k, β k * y k‖ ≤ (∑ k, ‖β k‖) * ‖y‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y k) (norm_nonneg _)

/-- **Component bounds of `F`** (`bpW:w4:lemma1`, step *Component bounds of F*). -/
theorem homF_compBounds_gen {a p pb s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ} (ha : 0 ≤ a) (hp : 0
    ≤ p)
    (hpb : p ≤ pb)
    {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hm : HomMultBounds τ α w W) (R : HomTaylor_gen a p pb s) (hX : HomFieldBound_gen ha hp hpb r ε
        R)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    HomCompBounds_gen ha hp hpb r homKS (waveBW τ σ * ε / α) (homSolveTaylor_gen hτ hα hσ hσs hm R)
        θ := by
  have hs : 0 < s := hσ.trans hσs
  have hsub : complexStrip 2 (s - σ) ⊆ complexStrip 2 s := fun z hz j => by
    have := hz j; linarith
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := hsub hθ
    exact (homXnorm_nonneg_gen ha hp hpb hr R θ 0 0 0).trans
      (hX θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  have hB := waveBW_nonneg τ σ
  have hfirst := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R hX hz
  have hang := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R hX hz i
  have hK1 := one_le_homKS
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- b
    have := (homSolve_spec hτ hα le_rfl hσ hσs (norm_homTvec_le hm) R.comp_b.1 R.comp_b.2.1
      (m := 2 * Real.pi * ε) (fun z hz => (hfirst z hz).1)).2.2.1 θ hθ
    refine this.trans (le_of_eq ?_); ring
  · have := (homSolve_spec hτ hα le_rfl hσ hσs (norm_homTdp_le hm) R.comp_cp.1 R.comp_cp.2.1
      (m := r * ε / Real.sqrt 2) (fun z hz => (hfirst z hz).2.1)).2.2.1 θ hθ
    refine this.trans (le_of_eq ?_); ring
  · have := (homSolve_spec hτ hα le_rfl hσ hσs (norm_homTdm_le hm) R.comp_cm.1 R.comp_cm.2.1
      (m := r * ε / Real.sqrt 2) (fun z hz => (hfirst z hz).2.2.1)).2.2.1 θ hθ
    refine this.trans (le_of_eq ?_); ring
  · -- P
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hP2 : ∀ z ∈ complexStrip 2 s, ‖R.P z‖ ≤ ε / 2 := fun z hz => by
      have := (hfirst z hz).2.2.2.1
      rw [norm_smul, h2] at this; linarith
    have := (homSolve_spec hτ hα one_le_homKS hσ hσs (norm_homTP_le hm) R.comp_P.1 R.comp_P.2.1
      (m := ε / 2) hP2).2.2.1 θ hθ
    show ‖(2 : ℂ) • homSolve (homTP hm) R.P θ‖ ≤ _
    rw [norm_smul, h2]
    calc 2 * ‖homSolve (homTP hm) R.P θ‖ ≤ 2 * (homKS * waveBW τ σ * (ε / 2) / α) := by gcongr
      _ = _ := by ring
  · have := (homSolve_spec hτ hα one_le_homKS hσ hσs (norm_homTQ_le hm) R.comp_Q.1 R.comp_Q.2.1
      (m := ε) (fun z hz => (hfirst z hz).2.2.2.2.1)).2.2.1 θ hθ
    refine this.trans (le_of_eq ?_); ring
  · have := (homSolve_spec hτ hα one_le_homKS hσ hσs (norm_homTQt_le hm) R.comp_Qt.1
      R.comp_Qt.2.1 (m := ε) (fun z hz => (hfirst z hz).2.2.2.2.2.1)).2.2.1 θ hθ
    refine this.trans (le_of_eq ?_); ring
  · have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hP2 : ∀ z ∈ complexStrip 2 s, ‖R.P' z‖ ≤ ε / 2 := fun z hz => by
      have := (hfirst z hz).2.2.2.2.2.2
      rw [norm_smul, h2] at this; linarith
    have := (homSolve_spec hτ hα one_le_homKS hσ hσs (norm_homTP'_le hm) R.comp_P'.1
      R.comp_P'.2.1 (m := ε / 2) hP2).2.2.1 θ hθ
    show ‖(2 : ℂ) • homSolve (homTP' hm) R.P' θ‖ ≤ _
    rw [norm_smul, h2]
    calc 2 * ‖homSolve (homTP' hm) R.P' θ‖ ≤ 2 * (homKS * waveBW τ σ * (ε / 2) / α) := by gcongr
      _ = _ := by ring
  · -- da
    intro i
    obtain ⟨C, hC⟩ := R.comp_a0.2.2
    have := homSolve_image_partial_bound (T' := homTscal w) hτ hα le_rfl le_rfl hσ hσs
      (norm_homTscal_le hm) (norm_homTscal_le hm) (ContinuousLinearMap.id ℂ ℂ)
      (fun k => by simp) R.comp_a0.1 R.comp_a0.2.1 hC (mΛ := C) (fun z hz => by simpa using hC z hz)
      i (fun z hz => by simpa using (hang z hz i).1) hθ
    refine (by simpa using this : ‖homPartial i (homSolve (homTscal w) R.a0) θ‖ ≤ _).trans
      (le_of_eq ?_)
    ring
  · -- db
    intro i y
    set Λy : (Fin 2 → ℂ) →L[ℂ] ℂ := ∑ k, (y k) • ContinuousLinearMap.proj k with hΛydef
    have hΛy : ∀ b : Fin 2 → ℂ, Λy b = ∑ k, b k * y k := fun b => by
      simp [hΛydef, mul_comm]
    obtain ⟨C, hC⟩ := R.comp_b.2.2
    have := homSolve_image_partial_bound (T' := homTscal w) hτ hα le_rfl le_rfl hσ hσs
      (norm_homTvec_le hm) (norm_homTscal_le hm) Λy
      (fun k => by
        refine ContinuousLinearMap.ext fun b => ?_
        simp [homTvec, homTscal, map_smul]) R.comp_b.1 R.comp_b.2.1 hC
      (mΛ := ‖Λy‖ * C)
      (fun z hz => (Λy.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
      i (mΛ' := 2 * Real.pi * ε * ‖y‖)
      (fun z hz => by
        rw [homPartial_clm Λy (R.comp_b.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz))
            i,
          hΛy]
        exact (norm_sum_mul_le_of_sum_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hang z hz i).2.1 (norm_nonneg y))) hθ
    rw [hΛy] at this
    refine this.trans (le_of_eq ?_); ring
  · -- dcp
    intro i
    obtain ⟨C, hC⟩ := R.comp_cp.2.2
    have := homSolve_image_partial_bound (T' := homTdp hm) hτ hα le_rfl le_rfl hσ hσs
      (norm_homTdp_le hm) (norm_homTdp_le hm) (homLamDiag_gen ha (homPP hp hpb))
      (homLamDiag_comm_homTdp_gen ha hp hpb hm) R.comp_cp.1 R.comp_cp.2.1 hC (mΛ := C)
      (fun z hz => (homDualNorm_le_gen ha (homPP hp hpb) _).trans (hC z hz)) i
      (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε)
      (fun z hz => by
        rw [homPartial_clm _ (R.comp_cp.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz))
            i]
        exact (hang z hz i).2.2.1) hθ
    refine (this : homDualNorm_gen ha (homPP hp hpb) (homPartial i (homSolve (homTdp hm) R.cp) θ) ≤
        _).trans
      (le_of_eq ?_)
    ring
  · -- dcm
    intro i
    obtain ⟨C, hC⟩ := R.comp_cm.2.2
    have := homSolve_image_partial_bound (T' := homTdm hm) hτ hα le_rfl le_rfl hσ hσs
      (norm_homTdm_le hm) (norm_homTdm_le hm) (homLamDiag_gen ha (homPP hp hpb))
      (homLamDiag_comm_homTdm_gen ha hp hpb hm) R.comp_cm.1 R.comp_cm.2.1 hC (mΛ := C)
      (fun z hz => (homDualNorm_le_gen ha (homPP hp hpb) _).trans (hC z hz)) i
      (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε)
      (fun z hz => by
        rw [homPartial_clm _ (R.comp_cm.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz))
            i]
        exact (hang z hz i).2.2.2.1) hθ
    refine (this : homDualNorm_gen ha (homPP hp hpb) (homPartial i (homSolve (homTdm hm) R.cm) θ) ≤
        _).trans
      (le_of_eq ?_)
    ring
  · -- dP
    intro i
    obtain ⟨C, hC⟩ := R.comp_P.2.2
    have := homSolve_image_partial_bound (T' := homTP hm) hτ hα one_le_homKS one_le_homKS hσ hσs
      (norm_homTP_le hm) (norm_homTP_le hm) (homLamCLM_gen ha (homPP hp hpb))
      (fun k => homLam_comm_hadamard_gen ha hp hpb (hm.P k)) R.comp_P.1 R.comp_P.2.1 hC (mΛ := C)
      (fun z hz => (norm_homLamCLM_apply_le_gen ha (homPP hp hpb) _).trans (hC z hz)) i
      (mΛ' := 4 * Real.pi * ε)
      (fun z hz => by
        rw [homPartial_clm _ (R.comp_P.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz))
            i]
        exact (hang z hz i).2.2.2.2.1) hθ
    refine this.trans (le_of_eq ?_); ring
  · -- dP'
    intro i
    obtain ⟨C, hC⟩ := R.comp_P'.2.2
    have := homSolve_image_partial_bound (T' := homTP' hm) hτ hα one_le_homKS one_le_homKS hσ hσs
      (norm_homTP'_le hm) (norm_homTP'_le hm) (homLamCLM_gen ha (homPP hp hpb))
      (fun k => homLam_comm_hadamard_gen ha hp hpb (hm.P' k)) R.comp_P'.1 R.comp_P'.2.1 hC (mΛ := C)
      (fun z hz => (norm_homLamCLM_apply_le_gen ha (homPP hp hpb) _).trans (hC z hz)) i
      (mΛ' := 4 * Real.pi * ε)
      (fun z hz => by
        rw [homPartial_clm _ (R.comp_P'.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz))
            i]
        exact (hang z hz i).2.2.2.2.2.1) hθ
    refine this.trans (le_of_eq ?_); ring
  · -- dQ
    intro i
    obtain ⟨C, hC⟩ := R.comp_Q.2.2
    have := homSolve_image_partial_bound (T' := homTQ hm) hτ hα one_le_homKS one_le_homKS hσ hσs
      (norm_homTQ_le hm) (norm_homTQ_le hm) (homLamCLM_gen ha (homPP hp hpb))
      (fun k => homLam_comm_hadamard_gen ha hp hpb (hm.Q k)) R.comp_Q.1 R.comp_Q.2.1 hC (mΛ := C)
      (fun z hz => (norm_homLamCLM_apply_le_gen ha (homPP hp hpb) _).trans (hC z hz)) i
      (mΛ' := 16 * Real.pi * ε)
      (fun z hz => by
        rw [homPartial_clm _ (R.comp_Q.1.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz))
            i]
        exact (hang z hz i).2.2.2.2.2.2) hθ
    refine this.trans (le_of_eq ?_); ring

/-- CONDITIONAL helper for Lemma 1 (iii), uniform bound: assumes the intermediate gate
`HomMultBounds`. The source-premise export is `homLemma1_fieldBound_gen`. -/
theorem homLemma1_fieldBound_of_gates_gen {a p pb s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ} (ha : 0
  ≤ a)
    (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs
        : σ < s)
    (hm : HomMultBounds τ α w W) (R : HomTaylor_gen a p pb s) (hX : HomFieldBound_gen ha hp hpb r ε
        R) :
    HomFieldBound_gen ha hp hpb r ((7 + 10 * homKS) * (waveBW τ σ * ε / α))
      (homSolveTaylor_gen hτ hα hσ hσs hm R) := by
  intro θ y z zb hdom
  have hs : 0 < s := hσ.trans hσs
  have hsub : complexStrip 2 (s - σ) ⊆ complexStrip 2 s := fun z hz j => by
    have := hz j; linarith
  have hε : 0 ≤ ε := by
    have hθ' : θ ∈ complexStrip 2 s := hsub hdom.1
    exact (homXnorm_nonneg_gen ha hp hpb hr R θ 0 0 0).trans
      (hX θ 0 0 0 (homDomain_y hθ' hr (by simpa using pow_pos hr 2)))
  have hE0 : 0 ≤ waveBW τ σ * ε / α := by
    have := waveBW_nonneg τ σ; positivity
  exact homXnorm_le_of_components_gen ha hp hpb hr one_le_homKS hE0 _
    (homF_compBounds_gen ha hp hpb hr hτ hα hσ hσs hm R hX hdom.1) hdom.2.1.le hdom.2.2

/-- **Lemma 1 (iii), uniform bound** (`bpW:w4:lemma1` (iii)) from the source premises
(`HomFreqHyp`, `HomMelnikov`, positivity, `ξ ∈ Π`): `|X_F|_r ≤ C₁ B^W_σ ε/α` on `D(s-σ,r)`,
`C₁ = 7 + 10K_S`. -/
theorem homLemma1_fieldBound_gen {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) {a p pb s σ : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor_gen a p pb s)
    (hX : HomFieldBound_gen ha hp hpb r ε R) :
    HomFieldBound_gen ha hp hpb r ((7 + 10 * homKS) * (waveBW τ σ * ε / α))
      (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) :=
  homLemma1_fieldBound_of_gates_gen ha hp hpb hr hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R hX

end KAM.Wave
