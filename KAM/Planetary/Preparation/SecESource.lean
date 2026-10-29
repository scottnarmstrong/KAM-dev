/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SecEDefs
public import KAM.Planetary.Preparation.SecDSource

/-!
# Source objects of Step E (`bpP:p11:sec-E#data`, package P-SEC)

The literal objects of `§ Step E` of blueprint-P Part 11 and their identifications on the full
complex source domain `E` (`p11SecE`):

* `p11RhoTilde0 = (2πε, …, 2πε)`; `A_ε = p11Rescale` is `(θ, J₀ + εr, ζ, ε(2π𝟏 + ρ'))`
  (`p11Rescale_snd`), commutes with all angle shifts, and is an `ε`-chart:
  `A_ε^*(dJ∧dθ + dρ̃∧dζ) = ε(dr∧dθ + dρ'∧dζ)` (`p11Rescale_symplFormC`);
* `A_ε(E) ⊆ T_{σ₃/6} × V₂/2` when `2ε ≤ s₂/2` (`p11Rescale_mem_half`);
* the complex Hamiltonian `H₂ = H ∘ Φ¹_ε ∘ Θ̂ ∘ Ψ₂` (`p11H2`, `H` in its holomorphic secular
  chart `p11WorkingH`, `Θ̂ = (id, Π) = p11PolarC`), `Ĥ_ε = H₂ ∘ A_ε/ε` (`p11HHat`), and the full
  complex identity `Ĥ_ε = N_ε + P_ε` on `E` for the chosen datum (`P11SlowSpecOf.hHat_eq`);
* the domain table entry for `K_ε + 3ϑ` (`p11Rescale_cauchy_box`) and `s_* = σ₃/6 = σ_F/72`;
* the frequency map `ω̂_ε = ∇N_ε = (∂_J h, ∂_ρ̃ h) ∘ A_ε` (`P11SlowSpecOf.preparedFreq_eq`) and the
  normalized source formulas `ω̂^{(1)} = ω + ε∂_J Ĝ₀ + ∂_J g₂`,
  `ω̂^{(2)} = Ω̃ + ∂_ρ̃ Ẑ + ε⁻¹ ∂_ρ̃ g₂` (`P11SlowSpecOf.freq_source`).
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section SecE

variable {n : ℕ}

/-- `ρ̃₀ = (2πε, …, 2πε)`. -/
def p11RhoTilde0 (n : ℕ) (eps : ℝ) : P11CVec n := fun _ => (2 * Real.pi * eps : ℂ)

theorem p11SlowCenter_eq (C : P11SecularData n) (eps : ℝ) :
    p11SlowCenter C eps = Fin.append (KAM.realInclusion n C.J0) (p11RhoTilde0 n eps) := rfl

/-- `A_ε(θ, r, ζ, ρ') = (θ, J₀ + εr, ζ, ε(2π𝟏 + ρ'))`: angles unchanged. -/
theorem p11Rescale_fst (J0 : P11Vec n) (eps : ℝ) (z : P11Phase (n + n)) :
    (p11Rescale J0 eps z).1 = z.1 := rfl

/-- The actions of `A_ε`: `(J₀, ρ̃₀) + ε (r, ρ')`. -/
theorem p11Rescale_snd (J0 : P11Vec n) (eps : ℝ) (z : P11Phase (n + n)) :
    (p11Rescale J0 eps z).2 =
      Fin.append (KAM.realInclusion n J0) (p11RhoTilde0 n eps) + (eps : ℂ) • z.2 := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [p11Rescale, Fin.append_left]
  · simp [p11Rescale, p11RhoTilde0, Fin.append_right]; ring

/-- `A_ε` commutes with all angle shifts. -/
theorem p11Rescale_shift (J0 : P11Vec n) (eps : ℝ) (z : P11Phase (n + n))
    (a : P11CVec (n + n)) :
    p11Rescale J0 eps (z.1 + a, z.2) = p11Rescale J0 eps z + (a, 0) := by
  ext i <;> simp [p11Rescale]

/-- The derivative of `A_ε`: `(u_θ, u_I) ↦ (u_θ, ε u_I)`. -/
theorem p11Rescale_hasFDerivAt (J0 : P11Vec n) (eps : ℝ) (z : P11Phase (n + n)) :
    HasFDerivAt (p11Rescale J0 eps)
      ((ContinuousLinearMap.fst ℂ _ _).prod
        ((eps : ℂ) • ContinuousLinearMap.snd ℂ (P11CVec (n + n)) (P11CVec (n + n)))) z := by
  have hf : p11Rescale J0 eps = fun w : P11Phase (n + n) =>
      ((0 : P11CVec (n + n)), Fin.append (KAM.realInclusion n J0) (p11RhoTilde0 n eps)) +
        ((ContinuousLinearMap.fst ℂ _ _).prod
          ((eps : ℂ) • ContinuousLinearMap.snd ℂ (P11CVec (n + n)) (P11CVec (n + n)))) w := by
    funext w
    ext i
    · simp [p11Rescale]
    · rw [p11Rescale_snd]; simp [add_comm]
  rw [hf]
  exact ContinuousLinearMap.hasFDerivAt.const_add _ |>.congr_fderiv rfl

/-- `A_ε` is an `ε`-chart: `A_ε^*(dJ∧dθ + dρ̃∧dζ) = ε (dr∧dθ + dρ'∧dζ)`. -/
theorem p11Rescale_symplFormC (J0 : P11Vec n) (eps : ℝ) (z : P11Phase (n + n))
    (u v : P11Phase (n + n)) :
    KAM.Canonical.symplFormC (fderiv ℂ (p11Rescale J0 eps) z u)
        (fderiv ℂ (p11Rescale J0 eps) z v) = eps * KAM.Canonical.symplFormC u v := by
  rw [(p11Rescale_hasFDerivAt J0 eps z).fderiv]
  simp only [KAM.Canonical.symplFormC, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_snd',
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Half box `V₂/2` and box `V₂` of the slow stage. -/
theorem p11Rescale_sub_center (C : P11SecularData n) (eps : ℝ) (z : P11Phase (n + n)) :
    (p11Rescale C.J0 eps z).2 - p11SlowCenter C eps = (eps : ℂ) • z.2 := by
  rw [p11Rescale_snd, p11SlowCenter_eq]; abel

theorem p11_norm_eps_smul_apply {eps : ℝ} (heps : 0 < eps) (x : P11CVec (n + n))
    (j : Fin (n + n)) : ‖((eps : ℂ) • x) j‖ = eps * ‖x j‖ := by
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg heps.le]

/-- `A_ε` maps the action polydisc `{|r|<2, |ρ'|<π/2}` into `V₂/2` when `2ε ≤ s₂/2`. -/
theorem p11Rescale_mem_half (C : P11SecularData n) {nu eps : ℝ} (heps : 0 < eps)
    (h2 : 2 * eps ≤ p11s2 C nu eps / 2) {z : P11Phase (n + n)} (hz : z.2 ∈ p11SecEPolydisc n) :
    (p11Rescale C.J0 eps z).2 ∈
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) := by
  have hd := p11Rescale_sub_center C eps z
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h := congrFun hd (Fin.castAdd n i)
    rw [Pi.sub_apply] at h
    rw [h, p11_norm_eps_smul_apply heps]
    have := hz.1 i
    simp only [Pi.zero_apply, sub_zero] at this
    nlinarith
  · have h := congrFun hd (Fin.natAdd n i)
    rw [Pi.sub_apply] at h
    rw [h, p11_norm_eps_smul_apply heps]
    have := hz.2 i
    simp only [Pi.zero_apply, sub_zero] at this
    have : eps * ‖z.2 (Fin.natAdd n i)‖ < eps * (Real.pi / 2) := mul_lt_mul_of_pos_left this heps
    linarith

/-- `s_* = σ₃/6 = σ_F/72`. -/
theorem p11Sigma3_div_six (C : P11SecularData n) : p11Sigma3 C / 6 = C.sigma / 72 := by
  unfold p11Sigma3; ring

/-- `A_ε(E) ⊆ T_{σ₃/6} × V₂/2` when `2ε ≤ s₂/2`. -/
theorem p11Rescale_mapsTo_half (C : P11SecularData n) {nu eps : ℝ} (heps : 0 < eps)
    (h2 : 2 * eps ≤ p11s2 C nu eps / 2) :
    MapsTo (p11Rescale C.J0 eps) (p11SecE C) (KAM.complexStrip (n + n) (p11Sigma3 C / 6) ×ˢ
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2)) := by
  intro z hz
  refine ⟨?_, p11Rescale_mem_half C heps h2 hz.2⟩
  rw [p11Rescale_fst, p11Sigma3_div_six]
  exact hz.1

/-- Complex `H₂ = H ∘ Φ¹_ε ∘ Θ̂ ∘ Ψ₂`, with `H` the holomorphic secular Hamiltonian
`h̃ + εF` (`p11WorkingH`) and `Θ̂ = (id, Π) = p11PolarC`. -/
def p11H2 (C : P11SecularData n) (Fast : P11FastData n) (A : P11SlowData n) (eps : ℝ)
    (w : P11Phase (n + n)) : ℂ :=
  p11WorkingH C eps (Fast.map (p11PolarC (A.Psi w)))

/-- `Ĥ_ε = H₂ ∘ A_ε / ε`. -/
def p11HHat (C : P11SecularData n) (Fast : P11FastData n) (A : P11SlowData n) (eps : ℝ)
    (z : P11Phase (n + n)) : ℂ :=
  p11H2 C Fast A eps (p11Rescale C.J0 eps z) / eps

/-- `N_ε(r, ρ') = (h₀ + g₂)(J₀ + εr, ε(2π𝟏 + ρ'))/ε` and `P_ε = f₃ ∘ A_ε/ε` (definitional). -/
theorem p11PreparedCoreOf_NP (C : P11SecularData n) (Fast : P11FastData n) (A : P11SlowData n)
    (eps : ℝ) (W : P11Vec (n + n) → P11Vec (n + n)) (z : P11Phase (n + n)) :
    (p11PreparedCoreOf C Fast A eps W).N z.2 =
        (A.h0 (p11Rescale C.J0 eps z).2 + A.g2 (p11Rescale C.J0 eps z).2) / eps ∧
      (p11PreparedCoreOf C Fast A eps W).P z = A.f3 (p11Rescale C.J0 eps z) / eps :=
  ⟨rfl, rfl⟩

/-- The full complex identity `H₂ ∘ A_ε = h₀ + g₂ + f₃` on `A_ε(E)`, hence
`Ĥ_ε = H₂ ∘ A_ε/ε = N_ε + P_ε` on all of `E` (`2ε ≤ s₂/2`). -/
theorem P11SlowSpecOf.hHat_eq {C : P11SecularData n} {Fast : P11FastData n} {nu eps c : ℝ}
    {A : P11SlowData n} (hA : P11SlowSpecOf C Fast nu eps c A) (heps : 0 < eps)
    (h2 : 2 * eps ≤ p11s2 C nu eps / 2) (W : P11Vec (n + n) → P11Vec (n + n))
    {z : P11Phase (n + n)} (hz : z ∈ p11SecE C) :
    p11H2 C Fast A eps (p11Rescale C.J0 eps z) =
        A.h0 (p11Rescale C.J0 eps z).2 + A.g2 (p11Rescale C.J0 eps z).2 +
          A.f3 (p11Rescale C.J0 eps z) ∧
      p11HHat C Fast A eps z =
        (p11PreparedCoreOf C Fast A eps W).N z.2 + (p11PreparedCoreOf C Fast A eps W).P z := by
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmaps, -, -, -, -, hconj, -⟩ :=
    hA
  have hy := p11Rescale_mapsTo_half C heps h2 hz
  have hH : p11H2 C Fast A eps (p11Rescale C.J0 eps z) =
      A.h0 (p11Rescale C.J0 eps z).2 + A.g2 (p11Rescale C.J0 eps z).2 +
        A.f3 (p11Rescale C.J0 eps z) := by
    rw [p11H2, ← h1 _ (hmaps hy), hconj _ hy]
  refine ⟨hH, ?_⟩
  obtain ⟨hN, hP⟩ := p11PreparedCoreOf_NP C Fast A eps W z
  rw [p11HHat, hH, hN, hP]
  have : (eps : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 heps.ne'
  field_simp

/-- Domain table: a point of `K_ε + 3ϑ` (`|y|_∞ < 5/4`) is sent to an action with
`|J - J₀| < 5ε/4`, `|ρ̃_j - 2πε| < 5ε/4`, and for `5ε < s₂` the Cauchy box of radii `s₂/4`
(in `J`) and `ε/4` (in `ρ̃`) around it lies in `V₂/2`. -/
theorem p11Rescale_cauchy_box (C : P11SecularData n) {nu eps : ℝ} (heps : 0 < eps)
    (h5 : 5 * eps < p11s2 C nu eps) {I : P11CVec (n + n)} (hI : ∀ j, ‖I j‖ < 5 / 4) :
    (p11Rescale C.J0 eps (0, I)).2 ∈ p11Box (p11SlowCenter C eps) (5 / 4 * eps) (5 / 4 * eps) ∧
      p11Box (p11Rescale C.J0 eps (0, I)).2 (p11s2 C nu eps / 4) (eps / 4) ⊆
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) := by
  have hd := p11Rescale_sub_center C eps (0, I)
  have hc : ∀ j, ‖(p11Rescale C.J0 eps (0, I)).2 j - p11SlowCenter C eps j‖ < 5 / 4 * eps :=
    fun j => by
      have h := congrFun hd j
      rw [Pi.sub_apply] at h
      rw [h, p11_norm_eps_smul_apply heps]
      have := mul_lt_mul_of_pos_left (hI j) heps
      linarith
  refine ⟨⟨fun i => hc _, fun i => hc _⟩, fun w hw => ⟨fun i => ?_, fun i => ?_⟩⟩
  · have := norm_sub_le_norm_sub_add_norm_sub (w (Fin.castAdd n i))
      ((p11Rescale C.J0 eps (0, I)).2 (Fin.castAdd n i)) (p11SlowCenter C eps (Fin.castAdd n i))
    linarith [hw.1 i, hc (Fin.castAdd n i)]
  · have := norm_sub_le_norm_sub_add_norm_sub (w (Fin.natAdd n i))
      ((p11Rescale C.J0 eps (0, I)).2 (Fin.natAdd n i)) (p11SlowCenter C eps (Fin.natAdd n i))
    have hp := mul_lt_mul_of_pos_left Real.pi_gt_three heps
    linarith [hw.2 i, hc (Fin.natAdd n i)]

end SecE

end KAM.Planetary

end
