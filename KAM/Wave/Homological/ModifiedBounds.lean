/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ModifiedSolve
public import KAM.Wave.Homological.ModifiedAct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The field bound with modified divisors (`bpW:w5:w4-modified` (i))

* `homModF_compBounds`: the component bounds of `F = homModSolveTaylor … R` at one `θ ∈ T_{s-σ}`,
  with `K = K_S` and `E₀ = B^W_σ ε/α` (W4's step *Component bounds of F*), the `c^±, P, P'` parts
  from the reweighted data `homReweight R` (field bound `ε` in the `p₊` norm), the `Q, Q^T` parts
  from the twisted multipliers (step `m-sup`), and the `Q`-part of `∂_θ F` from step `m-act`:
  `‖Λ∂_{θ_i}Q_F‖_bil ≤ ‖∂_{θ_i}Q_F‖_{ℓ^N_{a,p} → ℓ^N_{a,p₊}} ≤ 2πK_S B^W_σ ε/α ≤ 16πK_S B^W_σ ε/α`;
* `homModLemma_fieldBound`: **`|X_F|_{p₊,r} ≤ C₁ B^W_σ ε/α` on `D(s-σ,r)`**, `C₁ = 7 + 10K_S`
  (assembly of W4, step `m-ass`), from the source premises.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

theorem homLamDiag_comm_homModTdp (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (hm : HomModMultBounds a p pb τ α w W) (k : Fin 2 → ℤ) :
    (homLamDiag_gen ha (homPP hp hpb)).comp (homModTdp hm k) =
      (homModTdp hm k).comp (homLamDiag_gen ha (homPP hp hpb)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  ext j
  simp [homModTdp, homLamDiag_apply_gen]
  ring

theorem homLamDiag_comm_homModTdm (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (hm : HomModMultBounds a p pb τ α w W) (k : Fin 2 → ℤ) :
    (homLamDiag_gen ha (homPP hp hpb)).comp (homModTdm hm k) =
      (homModTdm hm k).comp (homLamDiag_gen ha (homPP hp hpb)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  ext j
  simp [homModTdm, homLamDiag_apply_gen]
  ring

/-- **Component bounds of `F`** (`bpW:w5:w4-modified`, steps `m-sup`, `m-other`, `m-act`). -/
theorem homModF_compBounds (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1)
    {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hm : HomModMultBounds a p pb τ α w W) (R : HomTaylor_gen a p (p + 1) s)
    (hX : HomFieldBound_gen ha hp (homModPP1 p) r ε R)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    HomCompBounds_gen ha hp hpb r homKS (waveBW τ σ * ε / α)
      (homModSolveTaylor hτ hα hσ hσs hc hm R) θ := by
  have hs : 0 < s := hσ.trans hσs
  set R' := homReweight hc R with hR'
  have hX' : HomFieldBound_gen ha hp hpb r ε R' := homFieldBound_reweight ha hp hpb hc hr R hX
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX
  have hB := waveBW_nonneg τ σ
  have hfirst := fun z (hz : z ∈ complexStrip 2 s) => homComp_first_gen ha hp hpb hr R' hX' hz
  have hfirstR := fun z (hz : z ∈ complexStrip 2 s) =>
    homComp_first_gen ha hp (homModPP1 p) hr R hX hz
  have hang := fun z (hz : z ∈ complexStrip 2 s) i => homComp_angle_gen ha hp hpb hr R' hX' hz i
  have hK1 := one_le_homKS
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- b
    have := (homSolve_spec hτ hα le_rfl hσ hσs (norm_homModTvec_le hm) R'.comp_b.1 R'.comp_b.2.1
      (m := 2 * Real.pi * ε) (fun z hz => (hfirst z hz).1)).2.2.1 θ hθ
    refine this.trans (le_of_eq ?_); ring
  · have := (homSolve_spec hτ hα le_rfl hσ hσs (norm_homModTdp_le hm) R'.comp_cp.1 R'.comp_cp.2.1
      (m := r * ε / Real.sqrt 2) (fun z hz => (hfirst z hz).2.1)).2.2.1 θ hθ
    refine this.trans (le_of_eq ?_); ring
  · have := (homSolve_spec hτ hα le_rfl hσ hσs (norm_homModTdm_le hm) R'.comp_cm.1 R'.comp_cm.2.1
      (m := r * ε / Real.sqrt 2) (fun z hz => (hfirst z hz).2.2.1)).2.2.1 θ hθ
    refine this.trans (le_of_eq ?_); ring
  · -- P
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hP2 : ∀ z ∈ complexStrip 2 s, ‖R'.P z‖ ≤ ε / 2 := fun z hz => by
      have := (hfirst z hz).2.2.2.1
      rw [norm_smul, h2] at this; linarith
    have := (homSolve_spec hτ hα one_le_homKS hσ hσs (norm_homModTP_le hm) R'.comp_P.1
      R'.comp_P.2.1 (m := ε / 2) hP2).2.2.1 θ hθ
    show ‖(2 : ℂ) • homSolve (homModTP hm) R'.P θ‖ ≤ _
    rw [norm_smul, h2]
    calc 2 * ‖homSolve (homModTP hm) R'.P θ‖ ≤ 2 * (homKS * waveBW τ σ * (ε / 2) / α) := by gcongr
      _ = _ := by ring
  · -- Q (twisted, from the `p+1` bound of `R.Q`)
    have := (homSolve_spec hτ hα one_le_homKS hσ hσs (norm_homModTQ_le hm) R.comp_Q.1 R.comp_Q.2.1
      (m := ε) (fun z hz => (hfirstR z hz).2.2.2.2.1)).2.2.1 θ hθ
    refine this.trans (le_of_eq ?_); ring
  · have := (homSolve_spec hτ hα one_le_homKS hσ hσs (norm_homModTQt_le hm) R.comp_Qt.1
      R.comp_Qt.2.1 (m := ε) (fun z hz => (hfirstR z hz).2.2.2.2.2.1)).2.2.1 θ hθ
    refine this.trans (le_of_eq ?_); ring
  · have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hP2 : ∀ z ∈ complexStrip 2 s, ‖R'.P' z‖ ≤ ε / 2 := fun z hz => by
      have := (hfirst z hz).2.2.2.2.2.2
      rw [norm_smul, h2] at this; linarith
    have := (homSolve_spec hτ hα one_le_homKS hσ hσs (norm_homModTP'_le hm) R'.comp_P'.1
      R'.comp_P'.2.1 (m := ε / 2) hP2).2.2.1 θ hθ
    show ‖(2 : ℂ) • homSolve (homModTP' hm) R'.P' θ‖ ≤ _
    rw [norm_smul, h2]
    calc 2 * ‖homSolve (homModTP' hm) R'.P' θ‖ ≤ 2 * (homKS * waveBW τ σ * (ε / 2) / α) := by
          gcongr
      _ = _ := by ring
  · -- da
    intro i
    obtain ⟨C, hC⟩ := R'.comp_a0.2.2
    have := homSolve_image_partial_bound (T' := homTscal w) hτ hα le_rfl le_rfl hσ hσs
      (norm_homModTscal_le hm) (norm_homModTscal_le hm) (ContinuousLinearMap.id ℂ ℂ)
      (fun k => by simp) R'.comp_a0.1 R'.comp_a0.2.1 hC (mΛ := C)
      (fun z hz => by simpa using hC z hz)
      i (fun z hz => by simpa using (hang z hz i).1) hθ
    refine (by simpa using this : ‖homPartial i (homSolve (homTscal w) R'.a0) θ‖ ≤ _).trans
      (le_of_eq ?_)
    ring
  · -- db
    intro i y
    set Λy : (Fin 2 → ℂ) →L[ℂ] ℂ := ∑ k, (y k) • ContinuousLinearMap.proj k with hΛydef
    have hΛy : ∀ b : Fin 2 → ℂ, Λy b = ∑ k, b k * y k := fun b => by
      simp [hΛydef, mul_comm]
    obtain ⟨C, hC⟩ := R'.comp_b.2.2
    have := homSolve_image_partial_bound (T' := homTscal w) hτ hα le_rfl le_rfl hσ hσs
      (norm_homModTvec_le hm) (norm_homModTscal_le hm) Λy
      (fun k => by
        refine ContinuousLinearMap.ext fun b => ?_
        simp [homTvec, homTscal, map_smul]) R'.comp_b.1 R'.comp_b.2.1 hC
      (mΛ := ‖Λy‖ * C)
      (fun z hz => (Λy.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)))
      i (mΛ' := 2 * Real.pi * ε * ‖y‖)
      (fun z hz => by
        rw [homPartial_clm Λy (R'.comp_b.1.differentiableAt
            ((isOpen_complexStrip 2 s).mem_nhds hz)) i, hΛy]
        exact (norm_sum_mul_le_of_sum_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hang z hz i).2.1 (norm_nonneg y))) hθ
    rw [hΛy] at this
    refine this.trans (le_of_eq ?_); ring
  · -- dcp
    intro i
    obtain ⟨C, hC⟩ := R'.comp_cp.2.2
    have := homSolve_image_partial_bound (T' := homModTdp hm) hτ hα le_rfl le_rfl hσ hσs
      (norm_homModTdp_le hm) (norm_homModTdp_le hm) (homLamDiag_gen ha (homPP hp hpb))
      (homLamDiag_comm_homModTdp ha hp hpb hm) R'.comp_cp.1 R'.comp_cp.2.1 hC (mΛ := C)
      (fun z hz => (homDualNorm_le_gen ha (homPP hp hpb) _).trans (hC z hz)) i
      (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε)
      (fun z hz => by
        rw [homPartial_clm _ (R'.comp_cp.1.differentiableAt
            ((isOpen_complexStrip 2 s).mem_nhds hz)) i]
        exact (hang z hz i).2.2.1) hθ
    refine (this : homDualNorm_gen ha (homPP hp hpb)
        (homPartial i (homSolve (homModTdp hm) R'.cp) θ) ≤ _).trans (le_of_eq ?_)
    ring
  · -- dcm
    intro i
    obtain ⟨C, hC⟩ := R'.comp_cm.2.2
    have := homSolve_image_partial_bound (T' := homModTdm hm) hτ hα le_rfl le_rfl hσ hσs
      (norm_homModTdm_le hm) (norm_homModTdm_le hm) (homLamDiag_gen ha (homPP hp hpb))
      (homLamDiag_comm_homModTdm ha hp hpb hm) R'.comp_cm.1 R'.comp_cm.2.1 hC (mΛ := C)
      (fun z hz => (homDualNorm_le_gen ha (homPP hp hpb) _).trans (hC z hz)) i
      (mΛ' := 2 * Real.sqrt 2 * Real.pi * r * ε)
      (fun z hz => by
        rw [homPartial_clm _ (R'.comp_cm.1.differentiableAt
            ((isOpen_complexStrip 2 s).mem_nhds hz)) i]
        exact (hang z hz i).2.2.2.1) hθ
    refine (this : homDualNorm_gen ha (homPP hp hpb)
        (homPartial i (homSolve (homModTdm hm) R'.cm) θ) ≤ _).trans (le_of_eq ?_)
    ring
  · -- dP
    intro i
    obtain ⟨C, hC⟩ := R'.comp_P.2.2
    have := homSolve_image_partial_bound (T' := homModTP hm) hτ hα one_le_homKS one_le_homKS hσ
      hσs (norm_homModTP_le hm) (norm_homModTP_le hm) (homLamCLM_gen ha (homPP hp hpb))
      (fun k => homLam_comm_hadamard_gen ha hp hpb (hm.P k)) R'.comp_P.1 R'.comp_P.2.1 hC
      (mΛ := C) (fun z hz => (norm_homLamCLM_apply_le_gen ha (homPP hp hpb) _).trans (hC z hz)) i
      (mΛ' := 4 * Real.pi * ε)
      (fun z hz => by
        rw [homPartial_clm _ (R'.comp_P.1.differentiableAt
            ((isOpen_complexStrip 2 s).mem_nhds hz)) i]
        exact (hang z hz i).2.2.2.2.1) hθ
    refine this.trans (le_of_eq ?_); ring
  · -- dP'
    intro i
    obtain ⟨C, hC⟩ := R'.comp_P'.2.2
    have := homSolve_image_partial_bound (T' := homModTP' hm) hτ hα one_le_homKS one_le_homKS hσ
      hσs (norm_homModTP'_le hm) (norm_homModTP'_le hm) (homLamCLM_gen ha (homPP hp hpb))
      (fun k => homLam_comm_hadamard_gen ha hp hpb (hm.P' k)) R'.comp_P'.1 R'.comp_P'.2.1 hC
      (mΛ := C) (fun z hz => (norm_homLamCLM_apply_le_gen ha (homPP hp hpb) _).trans (hC z hz)) i
      (mΛ' := 4 * Real.pi * ε)
      (fun z hz => by
        rw [homPartial_clm _ (R'.comp_P'.1.differentiableAt
            ((isOpen_complexStrip 2 s).mem_nhds hz)) i]
        exact (hang z hz i).2.2.2.2.2.1) hθ
    refine this.trans (le_of_eq ?_); ring
  · -- dQ: step `m-act` (operator norm `ℓ^N_{a,p} → ℓ^N_{a,p₊}`)
    intro i
    have h1 := norm_homPartial_homSolve_le hτ hα one_le_homKS hσ hσs (norm_homModTQ_le hm)
      R.comp_Q.1 R.comp_Q.2.1 (m := ε) (fun z hz => (hfirstR z hz).2.2.2.2.1) i hθ
    refine (norm_homLamCLM_apply_le_gen ha (homPP hp hpb) _).trans (h1.trans ?_)
    have hπ := Real.pi_pos
    have : 0 ≤ homKS * waveBW τ σ * ε / α := by positivity
    calc 2 * Real.pi * homKS * waveBW τ σ * ε / α = 2 * Real.pi * (homKS * waveBW τ σ * ε / α) := by
          ring
      _ ≤ 16 * Real.pi * (homKS * waveBW τ σ * ε / α) := by nlinarith
      _ = _ := by ring

/-- CONDITIONAL helper for `bpW:w5:w4-modified` (i), field bound: assumes the gate
`HomModMultBounds`. The source-premise export is `homModLemma_fieldBound`. -/
theorem homModLemma_fieldBound_of_gates (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (hc : pb ≤ p + 1) {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ)
    (hσs : σ < s) (hm : HomModMultBounds a p pb τ α w W) (R : HomTaylor_gen a p (p + 1) s)
    (hX : HomFieldBound_gen ha hp (homModPP1 p) r ε R) :
    HomFieldBound_gen ha hp hpb r ((7 + 10 * homKS) * (waveBW τ σ * ε / α))
      (homModSolveTaylor hτ hα hσ hσs hc hm R) := by
  intro θ y z zb hdom
  have hs : 0 < s := hσ.trans hσs
  have hε : 0 ≤ ε := homFieldBound_nonneg_gen hr hs hX
  have hE0 : 0 ≤ waveBW τ σ * ε / α := by
    have := waveBW_nonneg τ σ; positivity
  exact homXnorm_le_of_components_gen ha hp hpb hr one_le_homKS hE0 _
    (homModF_compBounds ha hp hpb hc hr hτ hα hσ hσs hm R hX hdom.1) hdom.2.1.le hdom.2.2

/-- **`bpW:w5:w4-modified` (i), field bound** from the source premises (modified Melnikov
conditions `HomMelnikovMod` with `0 ≤ β ≤ p+1-p₊`, `α > 0`, `ξ ∈ Π`): for `R ∈ 𝒯_s` (`p̄ = p+1`)
with `|X_R|_{p+1,r} ≤ ε` on `D(s,r)`, the solution `F` with modified divisors satisfies
`|X_F|_{p₊,r} ≤ C₁ B^W_σ ε/α` on `D(s-σ,r)`, `C₁ = 7 + 10K_S`. -/
theorem homModLemma_fieldBound {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {β : ℝ} (hH : HomMelnikovMod τ α β Par ω Ω) (hβ0 : 0 ≤ β)
    (hβ : β ≤ p + 1 - pb) (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0 < r)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    (R : HomTaylor_gen a p (p + 1) s)
    (hX : HomFieldBound_gen ha hp (homModPP1 p) r ε R) :
    HomFieldBound_gen ha hp hpb r ((7 + 10 * homKS) * (waveBW τ σ * ε / α))
      (homModSolveTaylor hτ hα hσ hσs (homMod_pb_le hβ0 hβ)
        (homModMultBounds_of hα hβ0 hβ hH hξ) R) :=
  homModLemma_fieldBound_of_gates ha hp hpb (by linarith) hr hτ hα hσ hσs
    (homModMultBounds_of hα hβ0 hβ hH hξ) R hX

end KAM.Wave
