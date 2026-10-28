/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.Partial.Constants
public import KAM.Nekhoroshev.Partial.Domain
public import KAM.Nekhoroshev.Partial.Hessian
public import KAM.Nekhoroshev.ResonanceGeometry.Covering
public import KAM.Nekhoroshev.ResonanceGeometry.Projection
public import KAM.Nekhoroshev.Stability.ResonantStabilityHess
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Part 11 (N11-G): the block data from the covering lemma (`bpN:p11:block-data`)

`block_data` applies the Part 8 covering lemma `KAM.Nekhoroshev.covering` and the cutoff corollary
`KAM.Nekhoroshev.cutoffs` to the singleton `{Ic}` and the frequency of the signed Hamiltonian
`signedH a σ`, with parameters `(9/8, 1/32, r₀, M₁, m₁, K, A)` (`A = 40 M_c/m`). The covering step
(`stepN:p11:bd-cover`) excludes the full lattice by the lower frequency bound `g₁`, the cutoff step
(`stepN:p11:bd-24`) supplies the divisor bound on the `ℓ¹` ball of radius `K/√n`, the strict
resonance closeness and the Lipschitz bound, and the last step (`stepN:p11:bd-5`) is the
arithmetic of `ε = m₁ r_Θ² / 2¹⁴`.
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`, lemma `bpN:p11:block-data`.
-/

@[expose] public noncomputable section

open Set Metric
open KAM.Weighted KAM.NormalForm KAM.Stability

namespace KAM.Nekhoroshev

variable {n k : ℕ}

private theorem bd_coth_pos {x : ℝ} (hx : 0 < x) : 0 < coth x :=
  div_pos (Real.cosh_pos x) (Real.sinh_pos_iff.2 hx)

/-- Positivity of the constants and `m ≤ Mc`, from the selected definiteness witness. -/
private theorem bd_basic (a : PartialData n k) (hne : a.G.Nonempty) {σ : ℝ}
    (hσ : DefiniteSign a σ) : 0 < a.g ∧ 0 < a.m ∧ a.m ≤ a.Mc := by
  obtain ⟨hg, hm, _⟩ := a.definite
  exact ⟨hg, hm, (hessian_at_sign a hne hσ).1⟩

private theorem bd_eps_pos (a : PartialData n k) {μ : ℝ} (hμ : 0 < μ) :
    0 < (constants a).eps μ := by
  have hs : 0 < (constants a).s := by
    simp only [PartialConstants.s, constants]; have := a.hρ; positivity
  have hc := bd_coth_pos (mul_pos Real.pi_pos hs)
  unfold PartialConstants.eps PartialConstants.kappaC
  positivity

private theorem bd_eps0_pos (a : PartialData n k) {σ : ℝ} (hne : a.G.Nonempty)
    (hσ : DefiniteSign a σ) : 0 < (constants a).eps0 := by
  obtain ⟨hg, hm, hmM⟩ := bd_basic a hne hσ
  have hρ := a.hρ
  have hπ := Real.pi_pos
  have hm1 : 0 < (constants a).m1 := by simp only [PartialConstants.m1, constants]; positivity
  have hr0 : 0 < (constants a).r0 := by
    simp only [PartialConstants.r0, constants]; exact lt_min (by positivity) (by positivity)
  have hA : 0 < (constants a).A := by
    simp only [PartialConstants.A, constants]; have := hm.trans_le hmM; positivity
  unfold PartialConstants.eps0
  positivity

private theorem bd_K_pow (a : PartialData n k) {σ μ : ℝ} (hne : a.G.Nonempty)
    (hσ : DefiniteSign a σ) (hμ : 0 < μ) :
    ((constants a).K μ) ^ (2 * n) * (constants a).eps μ = (constants a).eps0 := by
  have hn : 1 ≤ n := by have := a.hn; omega
  have he := bd_eps_pos a hμ
  have he0 := bd_eps0_pos a hne hσ
  have hx : 0 ≤ (constants a).eps0 / (constants a).eps μ := (div_pos he0 he).le
  have h1 : ((constants a).K μ) ^ (2 * n) = (constants a).eps0 / (constants a).eps μ := by
    unfold PartialConstants.K
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    have : (1 / (2 * (n:ℝ))) * ((2 * n : ℕ) : ℝ) = 1 := by
      push_cast
      have : (0:ℝ) < n := by exact_mod_cast hn
      field_simp
    rw [show (constants a).n = n from rfl, this, Real.rpow_one]
  rw [h1]
  field_simp

private theorem bd_one_le_K (a : PartialData n k) {μ : ℝ} (hμ : 0 < μ) (hε : (constants a).eps μ ≤ (constants a).eps0) :
    1 ≤ (constants a).K μ := by
  have he := bd_eps_pos a hμ
  unfold PartialConstants.K
  exact Real.one_le_rpow ((one_le_div he).2 hε) (by positivity)

/-- The frequency of the signed Hamiltonian is the rescaled frequency of `h`. -/
private theorem bd_freq_signed (a : PartialData n k) (σ : ℝ) (I : Fin n → ℝ) :
    KAM.frequencyMap (signedH a σ) I = (σ/(2*Real.pi)) • KAM.frequencyMap a.h I := by
  funext i
  have e : (fun J : Fin n → ℝ => (signedH a σ (fun j => (J j : ℂ))).re) =
      (σ/(2*Real.pi)) • realPart a.h := by
    funext J
    have : signedH a σ (fun i => (J i : ℂ)) =
        ((σ/(2*Real.pi):ℝ):ℂ) * a.h (fun i => (J i : ℂ)) := by
      simp only [signedH]; push_cast; ring
    simp only [realPart, this, Complex.re_ofReal_mul, Pi.smul_apply, smul_eq_mul]
  have e2 : (fun J : Fin n → ℝ => (a.h (fun j => (J j : ℂ))).re) = realPart a.h := rfl
  simp only [KAM.frequencyMap, e, e2, fderiv_const_smul_field, Pi.smul_apply]
  rfl

private theorem bd_g1_le (a : PartialData n k) {σ : ℝ} (hσ : DefiniteSign a σ) {Ic : Fin n → ℝ}
    (hIc : Ic ∈ a.G) : (constants a).g1 ≤ ‖KAM.frequencyMap (signedH a σ) Ic‖ := by
  have hπ' : (0:ℝ) < 2*Real.pi := by positivity
  have hI : KAM.realInclusion n Ic ∈ KAM.actionNbhd a.G' a.ρ :=
    ⟨Ic, a.collar Ic hIc (mem_closedBall_self a.hρ.le), by
      rw [show KAM.realInclusion n Ic = fun i => (Ic i:ℂ) from rfl, sub_self, norm_zero]
      exact a.hρ⟩
  rw [bd_freq_signed, norm_smul, Real.norm_eq_abs]
  have hab : |σ / (2*Real.pi)| = 1 / (2*Real.pi) := by
    rw [abs_div, abs_of_pos hπ']
    rcases hσ.1 with rfl | rfl <;> simp
  rw [hab]
  have := (hσ.2 _ hI).1
  simp only [PartialConstants.g1, constants]
  calc a.g / (2*Real.pi) = 1 / (2*Real.pi) * a.g := by ring
    _ ≤ 1 / (2*Real.pi) * ‖KAM.frequencyMap a.h Ic‖ := by gcongr

/-- Complex Hessian column bound in the form used for the frequency Lipschitz bound. -/
private theorem bd_hess_form {U : Set (Fin n → ℂ)} (hU : IsOpen U) {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h U) {M : ℝ}
    (hess : ∀ I ∈ U, ∀ v : Fin n → ℂ,
      euclid (fun i => fderiv ℂ (fderiv ℂ h) I (Pi.single i 1) v) ≤ M * euclid v)
    {I : Fin n → ℂ} (hI : I ∈ U) (v : Fin n → ℂ) :
    euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ M * euclid v := by
  have hdh : DifferentiableAt ℂ (fderiv ℂ h) I :=
    ((KAM.holomorphic_regularity_of_finiteDimensional hU hh).1).differentiableAt
      (hU.mem_nhds hI)
  have key : ∀ i : Fin n, fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1) =
      fderiv ℂ (fderiv ℂ h) I (Pi.single i 1) v := fun i => by
    have := hdh.hasFDerivAt.clm_apply (hasFDerivAt_const v I)
    rw [this.fderiv]
    simp
  simp only [key]
  exact hess I hI v

end KAM.Nekhoroshev

end
