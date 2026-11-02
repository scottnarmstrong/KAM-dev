/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ModifiedSolve
public import KAM.Wave.Homological.RealF
public import KAM.Wave.Homological.NhatTaylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The other claims of W4 (i) for the modified divisors (`bpW:w5:w4-modified` (i))

* `homModSolveTaylor_cp`, `_cm`, `_P`, `_P'`: the components `c^±, P, P'` of `F` are the W4 solves
  of `c^±, P, P'` (in `ℓ^N_{a,p+1}`, resp. bounded `ℓ^N_{a,p} → ℓ^N_{a,p+1}`), read in the
  `p₊`-weighted class through the inclusion `D_ρ` ("all other components as in W4");
* `homModLemma_zero_modes`: `â_{F,0} = 0`, `b̂_{F,0} = 0`, `(Q̂_{F,0})_{jj} = 0`;
* `homReweight_isReal`, `homModSolveTaylor_isReal`: if `R` is real, so is `F` (and `N̂`, by W4's
  `homNhatTaylor_isReal_gen` applied to `R`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM
open scoped ComplexConjugate

variable {a p pb s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

theorem homModRhoL_comm_hadamard (hc : pb ≤ p + 1) {d : ℕ+ → ℕ+ → ℂ} {c : ℝ}
    (h : HomHadamardBound d c) :
    (homModRhoL a p pb hc).comp (homHadamardCLM h) =
      (homHadamardCLM h).comp (homModRhoL a p pb hc) := by
  refine ContinuousLinearMap.ext fun A => homOp_ext_entries fun i j => ?_
  simp only [ContinuousLinearMap.comp_apply, homModRhoL_apply, homHadamardCLM_apply,
    kamEntry_homModRho_comp, homHadamard_entry]
  ring

section asW4

variable (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hc : pb ≤ p + 1)
  (hm : HomModMultBounds a p pb τ α w W) (R : HomTaylor_gen a p (p + 1) s) {θ : Fin 2 → ℂ}
  (hθ : θ ∈ complexStrip 2 (s - σ))
include hθ

theorem homModSolveTaylor_cp :
    (homModSolveTaylor hτ hα hσ hσs hc hm R).cp θ =
      homModRho a p pb hc (homSolve (homModTdp hm) R.cp θ) := by
  refine (homSolve_image_eq (T' := homModTdp hm) hτ hα le_rfl hσ hσs (norm_homModTdp_le hm)
    (homModRho a p pb hc) (fun k => ?_) R.comp_cp.1 R.comp_cp.2.1 R.comp_cp.2.2.choose_spec
    hθ).symm
  refine ContinuousLinearMap.ext fun v => ?_
  ext j
  simp [homModTdp, homModRho_apply]
  ring

theorem homModSolveTaylor_P :
    (homModSolveTaylor hτ hα hσ hσs hc hm R).P θ =
      homModRhoL a p pb hc (homSolve (homModTP hm) R.P θ) :=
  (homSolve_image_eq (T' := homModTP hm) hτ hα one_le_homKS hσ hσs (norm_homModTP_le hm)
    (homModRhoL a p pb hc) (fun k => homModRhoL_comm_hadamard hc (hm.P k)) R.comp_P.1
    R.comp_P.2.1 R.comp_P.2.2.choose_spec hθ).symm

end asW4

/-- **Vanishing of the resonant modes** (`bpW:w4:lemma1` (i) for the modified divisors):
`â_{F,0} = 0`, `b̂_{F,0} = 0`, `(Q̂_{F,0})_{jj} = 0`. -/
theorem homModLemma_zero_modes (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hc : pb ≤ p + 1) (hm : HomModMultBounds a p pb τ α w W) (R : HomTaylor_gen a p (p + 1) s) :
    homCoeff (homModSolveTaylor hτ hα hσ hσs hc hm R).a0 0 = 0 ∧
      homCoeff (homModSolveTaylor hτ hα hσ hσs hc hm R).b 0 = 0 ∧
      ∀ j : ℕ+, kamEntry (homCoeff (homModSolveTaylor hτ hα hσ hσs hc hm R).Q 0) j j = 0 := by
  refine ⟨?_, ?_, fun j => ?_⟩
  · have := (homSolve_spec hτ hα le_rfl hσ hσs (norm_homModTscal_le hm) R.comp_a0.1
      R.comp_a0.2.1 R.comp_a0.2.2.choose_spec).2.2.2.2.2 0
    show homCoeff (homSolve (homTscal w) R.a0) 0 = 0
    rw [this]; simp [homTscal, homMultA0]
  · have := (homSolve_spec hτ hα le_rfl hσ hσs (norm_homModTvec_le hm) R.comp_b.1 R.comp_b.2.1
      R.comp_b.2.2.choose_spec).2.2.2.2.2 0
    show homCoeff (homSolve (homTvec w) R.b) 0 = 0
    rw [this]; simp [homTvec, homMultA0]
  · have := (homSolve_spec hτ hα one_le_homKS hσ hσs (norm_homModTQ_le hm) R.comp_Q.1
      R.comp_Q.2.1 R.comp_Q.2.2.choose_spec).2.2.2.2.2 0
    show kamEntry (homCoeff (homSolve (homModTQ hm) R.Q) 0) j j = 0
    rw [this]
    simp only [homModTQ, homHadamardCLM_apply, homHadamard_entry]
    simp [homModDQ, homDQ]

/-- The reweighting preserves reality. -/
theorem homReweight_isReal (hc : pb ≤ p + 1) (R : HomTaylor_gen a p (p + 1) s)
    (hR : R.isRealTaylor) : (homReweight hc R).isRealTaylor := by
  intro x
  obtain ⟨hra, hrb, hrc, hrp, hrq⟩ := hR x
  refine ⟨hra, hrb, fun j => ?_, fun i j => ?_, fun i j => ?_⟩
  · show homModRho a p pb hc (R.cm _) j = conj (homModRho a p pb hc (R.cp _) j)
    rw [homModRho_apply, homModRho_apply, hrc j, map_mul, Complex.conj_ofReal]
  · show homNormalEntry_gen a p pb ((homModRho a p pb hc).comp (R.P' _)) i j =
      conj (homNormalEntry_gen a p pb ((homModRho a p pb hc).comp (R.P _)) i j)
    rw [homNormalEntry_rho, homNormalEntry_rho, hrp i j]
  · show homNormalEntry_gen a p pb ((homModRho a p pb hc).comp (R.Qt _)) i j =
      conj (homNormalEntry_gen a p pb ((homModRho a p pb hc).comp (R.Q _)) i j)
    rw [homNormalEntry_rho, homNormalEntry_rho, hrq i j]

/-- **Reality** (`bpW:w4:lemma1` (i) for the modified divisors): if `R` is real, so is `F`. -/
theorem homModSolveTaylor_isReal (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hc : pb ≤ p + 1) (hm : HomModMultBounds a p pb τ α w W) (R : HomTaylor_gen a p (p + 1) s)
    (hR : R.isRealTaylor) : (homModSolveTaylor hτ hα hσ hσs hc hm R).isRealTaylor := by
  have hs : 0 < s := hσ.trans hσs
  set R' := homReweight hc R with hR'def
  have hR' : R'.isRealTaylor := homReweight_isReal hc R hR
  set F := homModSolveTaylor hτ hα hσ hσs hc hm R with hF
  intro x
  set θ : Fin 2 → ℂ := fun j => (x j : ℂ) with hθdef
  have hθs : θ ∈ complexStrip 2 (s - σ) := ofReal_mem_complexStrip (by linarith) x
  refine ⟨?_, fun k => ?_, fun j => ?_, fun i j => ?_, fun i j => ?_⟩
  · -- a0
    have h := homSolve_conj_real (u := R.a0) (v := R.a0)
      (fun y => by
        have := (hR y).1
        exact ((Complex.conj_eq_iff_im).mpr this).symm) (homMultA0 w) (homMultA0 w)
      (fun k => (homMultA0_conj w k).symm) x
    have h2 : conj (F.a0 θ) = F.a0 θ := h
    exact (Complex.conj_eq_iff_im).mp h2
  · -- b
    have e : ∀ z ∈ complexStrip 2 (s - σ), F.b z k =
        homSolve (fun k' => homMultA0 w k' • ContinuousLinearMap.id ℂ ℂ)
          (fun z => R.b z k) z := fun z hz => by
      have := homSolve_image_eq (T' := fun k' => homMultA0 w k' • ContinuousLinearMap.id ℂ ℂ)
        hτ hα le_rfl hσ hσs (norm_homModTvec_le hm) (ContinuousLinearMap.proj k)
        (fun k' => by
          refine ContinuousLinearMap.ext fun v => ?_
          simp [homTvec]) R.comp_b.1 R.comp_b.2.1 R.comp_b.2.2.choose_spec hz
      exact this
    rw [e θ hθs]
    have h := homSolve_conj_real (u := fun z => R.b z k) (v := fun z => R.b z k)
      (fun y => ((Complex.conj_eq_iff_im).mpr ((hR y).2.1 k)).symm) (homMultA0 w) (homMultA0 w)
      (fun k' => (homMultA0_conj w k').symm) x
    exact (Complex.conj_eq_iff_im).mp h
  · -- c
    have ecp : ∀ z ∈ complexStrip 2 (s - σ), F.cp z j =
        homSolve (fun k => homMultDp w W k j • ContinuousLinearMap.id ℂ ℂ)
          (fun z => R'.cp z j) z :=
      fun z hz => by
        have := homSolve_image_eq (T' := fun k => homMultDp w W k j • ContinuousLinearMap.id ℂ ℂ)
          hτ hα le_rfl hσ hσs (norm_homModTdp_le hm) (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j)
          (fun k => by
            refine ContinuousLinearMap.ext fun v => ?_
            simp [homModTdp]; rfl) R'.comp_cp.1 R'.comp_cp.2.1
          R'.comp_cp.2.2.choose_spec hz
        exact this
    have ecm : ∀ z ∈ complexStrip 2 (s - σ), F.cm z j =
        homSolve (fun k => homMultDm w W k j • ContinuousLinearMap.id ℂ ℂ)
          (fun z => R'.cm z j) z :=
      fun z hz => by
        have := homSolve_image_eq (T' := fun k => homMultDm w W k j • ContinuousLinearMap.id ℂ ℂ)
          hτ hα le_rfl hσ hσs (norm_homModTdm_le hm) (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j)
          (fun k => by
            refine ContinuousLinearMap.ext fun v => ?_
            simp [homModTdm]; rfl) R'.comp_cm.1 R'.comp_cm.2.1
          R'.comp_cm.2.2.choose_spec hz
        exact this
    have h := homSolve_conj_real (u := fun z => R'.cp z j) (v := fun z => R'.cm z j)
      (fun y => (hR' y).2.2.1 j) (fun k => homMultDp w W k j) (fun k => homMultDm w W k j)
      (fun k => (homMultDp_conj w W k j).symm) x
    rw [ecm θ hθs, ecp θ hθs]
    exact h.symm
  · -- P'
    have eP : ∀ z ∈ complexStrip 2 (s - σ), homNormalEntry_gen a p pb (F.P z) i j =
        homSolve (fun k => homDP w W k i j • ContinuousLinearMap.id ℂ ℂ)
          (fun z => homNormalEntry_gen a p pb (R'.P z) i j) z := fun z hz =>
      homSolve_hadamard_entry_gen a p pb hτ hα one_le_homKS hσ hσs hm.P (norm_homModTP_le hm)
        R'.comp_P.1 R'.comp_P.2.1 R'.comp_P.2.2.choose_spec i j hz
    have eP' : ∀ z ∈ complexStrip 2 (s - σ), homNormalEntry_gen a p pb (F.P' z) i j =
        homSolve (fun k => homDP' w W k i j • ContinuousLinearMap.id ℂ ℂ)
          (fun z => homNormalEntry_gen a p pb (R'.P' z) i j) z := fun z hz =>
      homSolve_hadamard_entry_gen a p pb hτ hα one_le_homKS hσ hσs hm.P' (norm_homModTP'_le hm)
        R'.comp_P'.1 R'.comp_P'.2.1 R'.comp_P'.2.2.choose_spec i j hz
    have h := homSolve_conj_real (u := fun z => homNormalEntry_gen a p pb (R'.P z) i j)
      (v := fun z => homNormalEntry_gen a p pb (R'.P' z) i j)
      (fun y => (hR' y).2.2.2.1 i j) (fun k => homDP w W k i j) (fun k => homDP' w W k i j)
      (fun k => (homDP_conj w W k i j).symm) x
    rw [eP' θ hθs, eP θ hθs]
    exact h.symm
  · -- Qt
    obtain ⟨hQd, hQp, mQ, hQm⟩ := R.comp_Q
    have eQ : ∀ i j : ℕ+, ∀ z ∈ complexStrip 2 (s - σ), homNormalEntry_gen a p pb (F.Q z) i j =
        homSolve (fun k => homDQ w W k i j • ContinuousLinearMap.id ℂ ℂ)
          (fun z => homNormalEntry_gen a p (p + 1) (R.Q z) i j) z := fun i j z hz =>
      homModSolve_entry (d := fun k i j => homDQ w W k i j) hτ hα one_le_homKS hσ hσs hm.Q
        (fun k i j => rfl) (norm_homModTQ_le hm) hQd hQp hQm i j hz
    have h := homSolve_conj_real (u := fun z => homNormalEntry_gen a p (p + 1) (R.Q z) i j)
      (v := fun z => homNormalEntry_gen a p (p + 1) (R.Q z) j i)
      (fun y => by
        have h1 := (hR y).2.2.2.2 i j
        rw [R.transQ _ (ofReal_mem_complexStrip hs y) i j] at h1
        exact h1)
      (fun k => homDQ w W k i j) (fun k => homDQ w W k j i)
      (fun k => (homDQ_conj w W k i j).symm) x
    rw [F.transQ θ hθs i j, eQ j i θ hθs, eQ i j θ hθs]
    exact h.symm

end KAM.Wave
