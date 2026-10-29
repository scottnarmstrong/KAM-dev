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

private theorem bd_one_le_K (a : PartialData n k) {μ : ℝ} (hμ : 0 < μ)
    (hε : (constants a).eps μ ≤ (constants a).eps0) :
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

private theorem bd_dotC_real (k : Fin n → ℤ) (w : Fin n → ℝ) :
    dotC k (KAM.realInclusion n w) = ((integerReal k ⬝ᵥ w : ℝ) : ℂ) := by
  simp [dotC, integerReal, dotProduct]

/-- `ε = m₁ r_Θ² / 2¹⁴` (`stepN:p11:bd-5`). -/
private theorem bd_eps_eq (a : PartialData n k) {σ μ : ℝ} (hne : a.G.Nonempty)
    (hσ : DefiniteSign a σ) (hμ : 0 < μ) (hε : (constants a).eps μ ≤ (constants a).eps0) :
    (constants a).eps μ =
      (constants a).m1 * ((constants a).rTheta μ) ^ 2 / 2 ^ 14 := by
  obtain ⟨hg, hm, hmM⟩ := bd_basic a hne hσ
  have hK1 := bd_one_le_K a hμ hε
  have hK2 := bd_K_pow a hne hσ hμ
  have hKpos : 0 < (constants a).K μ := by linarith
  have hA : 0 < (constants a).A := by
    simp only [PartialConstants.A, constants]; have := a.hMc; positivity
  have h1 : (constants a).eps μ = (constants a).eps0 / ((constants a).K μ) ^ (2 * n) := by
    rw [eq_div_iff (pow_pos hKpos _).ne', mul_comm]; exact hK2
  have h2 : (((constants a).A * (constants a).K μ) ^ n) ^ 2 =
      (constants a).A ^ (2 * n) * ((constants a).K μ) ^ (2 * n) := by
    rw [← pow_mul, mul_pow, show n * 2 = 2 * n by ring]
  unfold PartialConstants.rTheta
  rw [show (constants a).n = n from rfl, div_pow, h2, h1]
  unfold PartialConstants.eps0
  rw [show (constants a).n = n from rfl]
  field_simp

theorem block_data (a : PartialData n k) (hne : a.G.Nonempty) {μ σ : ℝ} (hμ : 0 < μ)
    (hε : (constants a).eps μ ≤ (constants a).eps0) (hσ : DefiniteSign a σ)
    (hκ : 6 ≤ (constants a).kappa μ) {Ic : Fin n → ℝ} (hIc : Ic ∈ a.G) :
    let c := constants a
    ∃ Λ : AddSubgroup (Fin n → ℤ), ∃ r : ℝ,
      Λ ≠ ⊤ ∧ c.rTheta μ ≤ r ∧ r ≤ c.R0/c.K μ ∧ 0 < r ∧
      IsNonresonant {KAM.realInclusion n Ic} (c.K μ/Real.sqrt n) ((9/8)*c.M1*c.K μ*r)
        (Λ:Set (Fin n → ℤ)) (signedH a σ) ∧
      (∃ δ : ℝ, 0 ≤ δ ∧ δ < c.m1*r/32 ∧ NearResonance (Λ:Set (Fin n → ℤ)) (signedH a σ) Ic δ) ∧
      FreqLipschitz {KAM.realInclusion n Ic} r (Real.sqrt n*c.M1) (signedH a σ) ∧
      c.eps μ ≤ c.m1*r^2/2^14 ∧
      c.eps μ ≤ ((9/8)*c.M1*c.K μ*r)*r/(2^7*9*(c.K μ/Real.sqrt n)) := by
  intro c
  have _hκ := hκ
  obtain ⟨hg, hm, hmM⟩ := bd_basic a hne hσ
  have hπ := Real.pi_pos
  have hρ := a.hρ
  have hn1 : 1 ≤ n := by have := a.hn; omega
  have hm1 : 0 < c.m1 := by simp only [c, PartialConstants.m1, constants]; positivity
  have hM1 : 0 < c.M1 := by
    simp only [c, PartialConstants.M1, constants]; have := a.hMc; positivity
  have hm1M1 : c.m1 ≤ c.M1 := by
    simp only [c, PartialConstants.m1, PartialConstants.M1, constants]
    exact div_le_div_of_nonneg_right hmM (by positivity)
  have hr0 : 0 < c.r0 := by
    simp only [c, PartialConstants.r0, constants]; exact lt_min (by positivity) (by positivity)
  have hr0le : c.r0 ≤ 32 * a.g / a.m := min_le_right _ _
  have hMm : 1 ≤ a.Mc / a.m := (one_le_div hm).2 hmM
  have hAeq : c.A = 40 * (a.Mc / a.m) := by
    simp only [c, PartialConstants.A, constants]; ring
  have hA1 : 1 ≤ c.A := by rw [hAeq]; linarith
  have hK1 := bd_one_le_K a hμ hε
  have hKpos : 0 < c.K μ := by linarith
  have hsn1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast hn1)
  have hsn0 : 0 < Real.sqrt n := by linarith
  have hKaK : c.K μ / Real.sqrt n ≤ c.K μ := div_le_self hKpos.le hsn1
  let cp : CoverParams n := ⟨9/8, 1/32, c.r0, c.M1, c.m1, c.K μ, c.A⟩
  have hcp : cp.Valid := by
    refine ⟨hn1, by norm_num, by norm_num, hr0, hM1, hm1, hK1, ?_⟩
    show (9/8:ℝ) * c.M1 / ((1/32) * c.m1) + Real.sqrt 2 ≤ c.A
    have e1 : (9/8:ℝ) * c.M1 / ((1/32) * c.m1) = 36 * (a.Mc / a.m) := by
      simp only [c, PartialConstants.M1, PartialConstants.m1, constants]
      field_simp; ring
    have h2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    rw [e1, hAeq]; linarith
  obtain ⟨-, hcov, -⟩ := covering cp hcp ({Ic} : Set (Fin n → ℝ))
    (KAM.frequencyMap (signedH a σ))
  obtain ⟨Λ, hΛ, hIΛ⟩ := hcov Ic rfl
  have hw : KAM.frequencyMap (signedH a σ) Ic ∈ blocks cp.K cp.lam Λ := hIΛ.2
  have hrb := hcp.radius_bounds hΛ
  have hcut := cutoffs cp hcp (Ka := c.K μ / Real.sqrt n) (by positivity)
  have hrT : c.rTheta μ = cp.radius (⊥ : Lattice n) := (CoverParams.radius_bot cp).symm
  have hrTpos : 0 < c.rTheta μ := by
    unfold PartialConstants.rTheta; positivity
  have hrpos : 0 < cp.radius Λ := lt_of_lt_of_le hrTpos (hrT ▸ hrb.1)
  -- the full lattice is excluded by `g₁` (`stepN:p11:bd-cover`)
  have htop : Λ ≠ ⊤ := by
    intro hT
    subst hT
    have hlt := hcut.2.2.2.1 ⊤ hΛ _ hw
    have hlat : lattice (⊤ : Lattice n) = ⊤ :=
      Submodule.eq_top_of_finrank_eq ((latticeDim_top).trans (Module.finrank_fin_fun ℝ).symm)
    have hrd : resonanceDistance (⊤ : Lattice n) (KAM.frequencyMap (signedH a σ) Ic) =
        euclid (KAM.frequencyMap (signedH a σ) Ic) := by
      unfold resonanceDistance
      rw [hlat, (proj_spec (⊤ : Submodule ℝ (Fin n → ℝ))).2.2 _ Submodule.mem_top]
    rw [hrd] at hlt
    have hdel : cp.delta (⊤ : Lattice n) = (1/32) * c.m1 * c.r0 := by
      show (1/32:ℝ) * c.m1 * cp.radius (⊤ : Lattice n) = _
      rw [CoverParams.radius_top hcp]
    rw [hdel] at hlt
    have hg1 := bd_g1_le a hσ hIc
    have hnorm := (norm_le_euclid (KAM.frequencyMap (signedH a σ) Ic)).1
    have hπ' : (0:ℝ) < 2 * Real.pi := by positivity
    have hle : (1/32:ℝ) * c.m1 * c.r0 ≤ c.g1 := by
      have e1 : c.m1 = a.m / (2 * Real.pi) := rfl
      have e2 : c.g1 = a.g / (2 * Real.pi) := rfl
      rw [e1, e2]
      have h32 : c.r0 ≤ 32 * a.g / a.m := hr0le
      have : a.m / (2 * Real.pi) * c.r0 ≤ a.m / (2 * Real.pi) * (32 * a.g / a.m) := by
        gcongr
      have e : a.m / (2 * Real.pi) * (32 * a.g / a.m) = 32 * (a.g / (2 * Real.pi)) := by
        field_simp
      linarith
    linarith
  -- fast convexity on the block ball
  have hrr : cp.radius Λ ≤ c.r0 := hrb.2.1
  have fc := (hessian_at_sign a hne hσ).2 Ic hIc (cp.radius Λ) hrpos hrr
  have fc0 := (hessian_at_sign a hne hσ).2 Ic hIc c.r0 hr0 le_rfl
  have hcpx : cpx ({Ic} : Set (Fin n → ℝ)) = {KAM.realInclusion n Ic} := Set.image_singleton
  refine ⟨Λ, cp.radius Λ, htop, ?_, ?_, hrpos, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrT]; exact hrb.1
  · refine (hrb.2.2 htop).trans_eq ?_
    show c.r0 / (c.A * c.K μ) = c.R0 / c.K μ
    simp only [PartialConstants.R0]; rw [div_div]
  · -- divisor bound (`stepN:p11:bd-24`)
    have hfreq : freq (signedH a σ) (KAM.realInclusion n Ic) =
        KAM.realInclusion n (KAM.frequencyMap (signedH a σ) Ic) := by
      refine freq_realInclusion (D := {Ic}) (r := c.r0) ?_ ?_ ?_
      · rw [hcpx]; exact fc0.hol
      · intro I hI
        obtain ⟨J, hJ, hlt⟩ := hI
        rw [mem_singleton_iff] at hJ; subst hJ
        exact fc0.real I ⟨KAM.realInclusion n J, rfl, by
          rw [← map_sub, KAM.norm_realInclusion]; exact hlt⟩
      · exact ⟨Ic, rfl, by simpa using hr0⟩
    rintro I hI k ⟨hk, hkΛ⟩
    rw [mem_singleton_iff] at hI; subst hI
    rw [hfreq, bd_dotC_real, Complex.norm_real, Real.norm_eq_abs]
    exact hcut.2.2.1 hKaK Λ hΛ _ hw k hk hkΛ
  · -- strict closeness
    refine ⟨resonanceDistance Λ (KAM.frequencyMap (signedH a σ) Ic), euclid_nonneg' _, ?_, ?_⟩
    · have := hcut.2.2.2.1 Λ hΛ _ hw
      have hd : cp.delta Λ = (1/32) * c.m1 * cp.radius Λ := rfl
      rw [hd] at this; linarith
    · intro v hv
      set w := KAM.frequencyMap (signedH a σ) Ic with hwdef
      have h0 := (projection (lattice Λ)).2.2.2.1 w v hv
      have hsplit : w ⬝ᵥ v = proj (lattice Λ) w ⬝ᵥ v := by
        have : w = proj (lattice Λ) w + compProj (lattice Λ) w := by simp [compProj]
        conv_lhs => rw [this]
        rw [add_dotProduct, h0, add_zero]
      have := abs_dot_le_euclid (proj (lattice Λ) w) v
      rw [← hsplit] at this
      exact this
  · -- Lipschitz bound
    have hU := isOpen_polyNbhd (cpx ({Ic} : Set (Fin n → ℝ))) (cp.radius Λ)
    rw [hcpx] at hU
    have := freqLipschitz_of_complex (D := {Ic}) (r := cp.radius Λ) (M := c.M1)
      hM1.le (by rw [hcpx]; exact fc.hol) (fun I hI v => by
        rw [hcpx] at hI
        exact bd_hess_form hU fc.hol fc.hessian hI v)
    rw [hcpx] at this
    exact this
  · -- `ε ≤ m₁ r² / 2¹⁴`
    rw [bd_eps_eq a hne hσ hμ hε]
    have : c.rTheta μ ≤ cp.radius Λ := by rw [hrT]; exact hrb.1
    gcongr
  · have e := bd_eps_eq a hne hσ hμ hε
    have hrT' : c.rTheta μ ≤ cp.radius Λ := by rw [hrT]; exact hrb.1
    have h1 : c.eps μ ≤ c.m1 * cp.radius Λ ^ 2 / 2 ^ 14 := by
      rw [e]; gcongr
    have h2 : (9/8 * c.M1 * c.K μ * cp.radius Λ) * cp.radius Λ /
        (2 ^ 7 * 9 * (c.K μ / Real.sqrt n)) =
        Real.sqrt n * c.M1 * cp.radius Λ ^ 2 / 2 ^ 10 := by
      field_simp; ring
    rw [h2]
    refine h1.trans ?_
    have hr2 : 0 ≤ cp.radius Λ ^ 2 := sq_nonneg _
    have : c.m1 ≤ Real.sqrt n * c.M1 * 2 ^ 4 := by nlinarith
    calc c.m1 * cp.radius Λ ^ 2 / 2 ^ 14
        ≤ (Real.sqrt n * c.M1 * 2 ^ 4) * cp.radius Λ ^ 2 / 2 ^ 14 := by gcongr
      _ = Real.sqrt n * c.M1 * cp.radius Λ ^ 2 / 2 ^ 10 := by ring

end KAM.Nekhoroshev

end
