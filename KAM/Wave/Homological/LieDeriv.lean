/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.Lemma1
public import KAM.Wave.Homological.Lie
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The guarded derivative of `N` along `X_F` (`bpW:w4:lie` (iv))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

Phase space carrier: `homPhase = ℂ² × ℂ² × HomL2 × HomL2` for `(θ, y, z, \bar z)`, the last two
factors being the weighted `lp` carrier `ℓ²` of `ℓ^N_{a,p}` (representatives
`ẑ_j = ω_{a,p}(j+2) z_j`, as in `KAM/Wave/Seq`). Under the guard
`HomGuard a p γ` (`(j+2)/ω_{a,p}(j+2)² ≤ γ`) the form `N_Ω(z,\bar z) = ∑ Ω_j z_j \bar z_j` is a
bounded bilinear form on `HomL2` (`homNOmegaCLM`), `N = ⟨ω,y⟩ + N_Ω` is a continuous polynomial
(`homNfun`), it is Fréchet differentiable with
`DN(w)(Θ,Y,Z,\bar Z) = ⟨ω,Y⟩ + N_Ω(Z,\bar z) + N_Ω(z,\bar Z)` (`homNfun_hasFDerivAt`), and along the
field `X_F(w) = (·, -(1/2π)F_θ, -i F_{\bar z}, i F_z)` (the normal components embedded
`ℓ^N_{a,p_+} ⊂ ℓ^N_{a,p}`, `homEmbed_gen`):
`DN(w) X_F(w) = -L_N F(w)` (`homLemma_lie_iv_gen`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

/-- The phase space `(θ, y, z, \bar z)` of the normal-form Hamiltonian (carrier of `KAM/Wave/Seq`).
    -/
abbrev HomPhase : Type := (Fin 2 → ℂ) × (Fin 2 → ℂ) × HomL2 × HomL2

/-- The embedding `ℓ^N_{a,p_+} ⊂ ℓ^N_{a,p}` (`p ≤ p_+ = pb`) on representatives:
`ĉ_j ↦ ĉ_j ω_{a,p}(j+2)/ω_{a,p_+}(j+2)`. -/
def homEmbedCoef_gen (a p pb : ℝ) (j : ℕ+) : ℂ := ((homWt a p j / homWt a pb j : ℝ) : ℂ)

theorem norm_homEmbedCoef_le_gen {a p pb : ℝ} (hpb : p ≤ pb) (j : ℕ+) :
    ‖homEmbedCoef_gen a p pb j‖ ≤ 1 := by
  unfold homEmbedCoef_gen
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 : (1 : ℝ) ≤ ((j : ℝ) + 2) := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    linarith
  have e : homWt a p j / homWt a pb j = ((j : ℝ) + 2) ^ (p - pb) := by
    unfold homWt
    rw [ellWeight_div_ellWeight]
    congr 1
    push_cast
    ring
  rw [e, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)

/-- The embedding as a bounded diagonal operator. -/
def homEmbed_gen (a p pb : ℝ) (hpb : p ≤ pb) : HomOp :=
  weightedDiagCLM (homEmbedCoef_gen a p pb) (norm_homEmbedCoef_le_gen hpb)

/-- The coefficients `Ω_j/ω_{a,p}(j+2)²` of the form `N_Ω` in the representative coordinates. -/
def homNcoef (a p : ℝ) (Ω : ℕ+ → ℝ) (j : ℕ+) : ℂ := (Ω j : ℂ) / ((homWt a p j : ℝ) : ℂ) ^ 2

theorem norm_homNcoef_le {a p γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (j : ℕ+) : ‖homNcoef a p Ω j‖ ≤ K0 * γ := by
  have hw := homWt_pos a p j
  have h1 : ((j : ℝ) + 2) / homWt a p j ^ 2 ≤ γ := hG j
  unfold homNcoef
  rw [norm_div, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hw, div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at h1
  calc |Ω j| ≤ K0 * ((j : ℝ) + 2) := hΩ j
    _ ≤ K0 * (γ * homWt a p j ^ 2) := mul_le_mul_of_nonneg_left h1 hK0
    _ = _ := by ring

/-- The bounded bilinear form `N_Ω(z, \bar z) = ∑ Ω_j z_j \bar z_j` on the carrier. -/
def homNOmegaCLM {a p γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) : HomL2 →L[ℂ] HomL2 →L[ℂ] ℂ :=
  homPairL2.comp (weightedDiagCLM (homNcoef a p Ω) (norm_homNcoef_le hG hK0 hΩ))

theorem homNOmegaCLM_apply {a p γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (z zb : HomL2) :
    homNOmegaCLM hG hK0 hΩ z zb = ∑' j : ℕ+, homNcoef a p Ω j * z j * zb j := by
  show homPairF (weightedDiagCLM (homNcoef a p Ω) (norm_homNcoef_le hG hK0 hΩ) z) zb = _
  unfold homPairF
  exact tsum_congr fun j => by simp [weightedDiagCLM_apply, mul_assoc]

/-- Termwise form of `N_Ω(ĉ-embedded, z) = ⟨c, Ωz⟩₀`. -/
theorem homNOmega_embed_term {a p γ : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {Ω : ℕ+ → ℝ}
    (c z : HomL2) (j : ℕ+) :
    homNcoef a p Ω j * homEmbed_gen a p pb hpb c j * z j =
      homLamDiag_gen ha (homPP hp hpb) c j * (Ω j : ℂ) * z j := by
  have hw : (homWt a p j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p j).ne'
  have hj : ((j : ℂ) + 2) ≠ 0 := by
    have : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    exact_mod_cast this.ne'
  have hw2 : (homWt a pb j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a pb j).ne'
  simp only [homEmbed_gen, weightedDiagCLM_apply, homEmbedCoef_gen, homNcoef, homLamDiag_apply_gen,
      homLamD_gen]
  push_cast
  field_simp

/-- `N_Ω(ĉ-embedded, z) = ⟨c, Ωz⟩₀` (the pairing of `bpW:w4:lie`). -/
theorem homNOmega_embed_gen {a p γ K0 : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {Ω : ℕ+ → ℝ}
    (hG : HomGuard a p γ) (hK0 : 0 ≤ K0) (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2))
    (c z : HomL2) : homNOmegaCLM hG hK0 hΩ (homEmbed_gen a p pb hpb c) z =
      homPairOmegaRaw_gen ha hp hpb Ω c z := by
  rw [homNOmegaCLM_apply]
  unfold homPairOmegaRaw_gen
  exact tsum_congr fun j => homNOmega_embed_term (γ := γ) ha hp hpb c z j

/-- **Carrier evidence from the guard (G)**. -/
theorem homOmegaCarrier_of_guard {a p γ K0 : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) : HomOmegaCarrier ha hp hpb Ω := fun c z => by
  have := homPairF_summable
    (weightedDiagCLM (homNcoef a p Ω) (norm_homNcoef_le hG hK0 hΩ) (homEmbed_gen a p pb hpb c)) z
  refine this.congr fun j => ?_
  simp only [weightedDiagCLM_apply]
  exact homNOmega_embed_term (γ := γ) ha hp hpb c z j

theorem homNOmega_comm {a p γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (z zb : HomL2) :
    homNOmegaCLM hG hK0 hΩ z zb = homNOmegaCLM hG hK0 hΩ zb z := by
  rw [homNOmegaCLM_apply, homNOmegaCLM_apply]
  exact tsum_congr fun j => by ring

section deriv

variable {γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
  (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ)

/-- The pairing `y ↦ ⟨ω, y⟩` on `ℂ²`. -/
def homLomega (ω : Fin 2 → ℝ) : (Fin 2 → ℂ) →L[ℂ] ℂ :=
  ∑ k, (ω k : ℂ) • ContinuousLinearMap.proj k

theorem homLomega_apply (ω : Fin 2 → ℝ) (y : Fin 2 → ℂ) :
    homLomega ω y = ∑ k, (ω k : ℂ) * y k := by simp [homLomega]

/-- The projection of the phase space to `(z, \bar z)`. -/
def homPrZ : HomPhase →L[ℂ] HomL2 × HomL2 :=
  (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
    (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2))

/-- The projection to `y`. -/
def homPrY : HomPhase →L[ℂ] (Fin 2 → ℂ) :=
  (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
    (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2))

/-- **The normal form `N = ⟨ω,y⟩ + N_Ω(z,\bar z)`** as a function on the phase space. -/
def homNfun (ω : Fin 2 → ℝ) (w : HomPhase) : ℂ :=
  homLomega ω (homPrY w) + homNOmegaCLM hG hK0 hΩ (homPrZ w).1 (homPrZ w).2

/-- The candidate derivative `DN(w)`. -/
def homDN (w : HomPhase) : HomPhase →L[ℂ] ℂ :=
  (homLomega ω).comp homPrY +
    (((homNOmegaCLM hG hK0 hΩ).isBoundedBilinearMap).deriv (homPrZ w)).comp homPrZ

/-- **`N` is Fréchet differentiable** (`bpW:w4:lie` (iv)), with the displayed derivative. -/
theorem homNfun_hasFDerivAt (w : HomPhase) : HasFDerivAt (homNfun hG hK0 hΩ ω) (homDN hG hK0 hΩ ω
    w) w := by
  have h1 : HasFDerivAt (fun w : HomPhase => homLomega ω (homPrY w))
      ((homLomega ω).comp homPrY) w :=
    ((homLomega ω).comp homPrY).hasFDerivAt
  have h2 := (((homNOmegaCLM hG hK0 hΩ).isBoundedBilinearMap).hasFDerivAt (homPrZ w)).comp w
    (homPrZ).hasFDerivAt
  exact h1.add h2

theorem homDN_apply (w X : HomPhase) :
    homDN hG hK0 hΩ ω w X = ∑ k, (ω k : ℂ) * X.2.1 k +
      (homNOmegaCLM hG hK0 hΩ (homPrZ w).1 X.2.2.2 + homNOmegaCLM hG hK0 hΩ X.2.2.1 (homPrZ w).2)
          := by
  simp [homDN, homLomega_apply, homPrY, homPrZ, IsBoundedBilinearMap.deriv_apply]

/-- **`bpW:w4:lie` (iv)**: along the Hamiltonian field `X_F` of `F = T`,
`DN(w)·X_F(w) = -L_N F(w)` (equal to the weak bracket `⟨⟨N,F⟩⟩` of (ii)); the `y`-component of
`X_F` is `-(1/2π)F_θ` and the normal components are `(-iF_{\bar z}, iF_z)` embedded in
`ℓ^N_{a,p}`. -/
theorem homLemma_lie_iv_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    (θ y :
    Fin 2 → ℂ)
    (z zb : HomL2) :
    homDN hG hK0 hΩ ω (θ, y, z, zb)
        ((0 : Fin 2 → ℂ), (fun i => -(2 * Real.pi : ℂ)⁻¹ * homRtheta_gen ha hp hpb T i θ y z zb),
          (-Complex.I) • homEmbed_gen a p pb hpb (homRzb_gen T θ z zb),
          Complex.I • homEmbed_gen a p pb hpb (homRz_gen T θ z zb)) =
      -homLieN_gen ha hp hpb (homOmegaCarrier_of_guard (γ := γ) ha hp hpb hG hK0 hΩ) ω T θ y z
        zb := by
  show _ = -homLieNRaw_gen ha hp hpb ω Ω T θ y z zb
  rw [homDN_apply]
  simp only [homPrZ, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_snd', map_smul, smul_apply, smul_eq_mul]
  rw [homNOmega_comm hG hK0 hΩ z, homNOmega_embed_gen ha hp hpb hG hK0 hΩ,
    homNOmega_embed_gen ha hp hpb hG hK0 hΩ]
  unfold homLieNRaw_gen
  have : ∑ k, (ω k : ℂ) * (-(2 * Real.pi : ℂ)⁻¹ * homRtheta_gen ha hp hpb T k θ y z zb) =
      -((2 * Real.pi : ℂ)⁻¹ * ∑ k, (ω k : ℂ) * homRtheta_gen ha hp hpb T k θ y z zb) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  ring

end deriv


section guard

theorem homWt_eq (a p : ℝ) (j : ℕ+) :
    homWt a p j = ((j : ℝ) + 2) ^ p * Real.exp (a * ((j : ℝ) + 2)) := by
  unfold homWt ellWeight
  push_cast
  rfl

/-- **(G) holds if `a > 0` or `p ≥ 1/2`** (`bpW:w4:lie`, discussion of (G); `a, p ≥ 0`). -/
theorem homGuard_of_cond {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (h : 0 < a ∨ 1 / 2 ≤ p) :
    ∃ γ, HomGuard a p γ := by
  have hJ : ∀ j : ℕ+, (1 : ℝ) ≤ (j : ℝ) + 2 := fun j => by
    have : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    linarith
  have hsq : ∀ j : ℕ+, homWt a p j ^ 2 =
      ((j : ℝ) + 2) ^ (2 * p) * Real.exp (2 * a * ((j : ℝ) + 2)) := fun j => by
    rw [homWt_eq, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith [hJ j])]
    rw [← Real.exp_nat_mul]
    congr 2 <;> push_cast <;> ring
  rcases h with ha' | hp'
  · refine ⟨1 / (2 * a), fun j => ?_⟩
    have h1 : (1 : ℝ) ≤ ((j : ℝ) + 2) ^ (2 * p) := Real.one_le_rpow (hJ j) (by linarith)
    have h2 : 2 * a * ((j : ℝ) + 2) ≤ Real.exp (2 * a * ((j : ℝ) + 2)) := by
      linarith [Real.add_one_le_exp (2 * a * ((j : ℝ) + 2))]
    rw [hsq j, div_le_div_iff₀ (by have := hJ j; positivity) (by positivity)]
    have := hJ j
    have hE := Real.exp_pos (2 * a * ((j : ℝ) + 2))
    nlinarith [mul_le_mul h1 h2 (by positivity) (by positivity)]
  · refine ⟨1, fun j => ?_⟩
    have h1 : ((j : ℝ) + 2) ≤ ((j : ℝ) + 2) ^ (2 * p) := by
      have := Real.rpow_le_rpow_of_exponent_le (hJ j) (show (1 : ℝ) ≤ 2 * p by linarith)
      simpa using this
    have h2 : (1 : ℝ) ≤ Real.exp (2 * a * ((j : ℝ) + 2)) :=
      Real.one_le_exp (by have := hJ j; positivity)
    rw [hsq j, div_le_one (by have := hJ j; positivity)]
    nlinarith [mul_le_mul h1 h2 (by norm_num) (by positivity)]

/-- **(G) fails for `a = 0`, `p < 1/2`**: the guard is equivalent to `a > 0 ∨ p ≥ 1/2`. -/
theorem not_homGuard_of_lt {p : ℝ} (hp : p < 1 / 2) (γ : ℝ) : ¬ HomGuard 0 p γ := by
  intro hG
  have hq : 0 < 1 - 2 * p := by linarith
  set X : ℝ := max 1 (|γ| + 1) ^ (1 / (1 - 2 * p)) with hX
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 X)
  have hj : (0 : ℕ) < n + 1 := Nat.succ_pos n
  set j : ℕ+ := ⟨n + 1, hj⟩ with hjdef
  have hJ : max 1 X < (j : ℝ) + 2 := by
    have : (j : ℝ) = n + 1 := by simp [hjdef]
    rw [this]; linarith
  have hJ1 : (1 : ℝ) < (j : ℝ) + 2 := lt_of_le_of_lt (le_max_left _ _) hJ
  have hJX : X < (j : ℝ) + 2 := lt_of_le_of_lt (le_max_right _ _) hJ
  have h0 := hG j
  rw [homWt_eq] at h0
  simp only [zero_mul, Real.exp_zero, mul_one] at h0
  have e : ((j : ℝ) + 2) / (((j : ℝ) + 2) ^ p) ^ 2 = ((j : ℝ) + 2) ^ (1 - 2 * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.rpow_sub (by linarith),
      Real.rpow_one]
    congr 2; push_cast; ring
  rw [e] at h0
  have hM : (max 1 (|γ| + 1)) ^ (1 / (1 - 2 * p) * (1 - 2 * p)) < ((j : ℝ) + 2) ^ (1 - 2 * p) := by
    rw [Real.rpow_mul (by positivity)]
    exact Real.rpow_lt_rpow (by positivity) hJX hq
  rw [one_div_mul_cancel hq.ne', Real.rpow_one] at hM
  have := le_max_right 1 (|γ| + 1)
  linarith [abs_nonneg γ, le_abs_self γ]

end guard

end KAM.Wave
