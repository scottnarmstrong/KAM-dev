/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Family
public import KAM.Wave.Measure.Slab

/-!
# W7: estimates for one frequency pair (blueprint `bpW:w7:sep`, `bpW:w7:largek`, `bpW:w7:zone`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

For a frequency pair `(D, ω, Ω)` satisfying (H1)–(H2): the drift bounds, normal separation
(`bpW:w7:sep`), the largeness of `|k|` on nonempty zones (`bpW:w7:largek`), the Lipschitz bound of
`⟨l, Ω⟩` in the frequency coordinate, and the zone estimate (`bpW:w7:zone`).
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

section alpha

variable (m : ℝ) (hm : 0 < m)

theorem measAlphaM_pos : 0 < min (min (1 / 27) (measBetaStar m / 4))
    (measTheta m hm * measCX m hm / (4 * measKstar m hm * (measKstar m hm + 4))) := by
  have h1 := measBetaStar_pos hm
  have h2 := measTheta_pos m hm
  have h3 := measCX_pos m hm
  have h4 := measKstar_pos m hm
  refine lt_min (lt_min (by norm_num) (by positivity)) (by positivity)

/-- Facts on `α`, `α̂`, `α̌` from `0 < α ≤ α₀` (blueprint `bpW:w7:constdef` (C4), (C6)). -/
theorem alpha_facts {α : ℝ} (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) :
    0 < alphaCheck α ∧ alphaCheck α ≤ α ∧ α ≤ alphaHat α ∧ alphaHat α ≤ 1 / 27 ∧
      alphaHat α ≤ measBetaStar m / 4 ∧
      alphaHat α ≤ measTheta m hm * measCX m hm / (4 * measKstar m hm * (measKstar m hm + 4)) := by
  set M := min (min (1 / 27) (measBetaStar m / 4))
    (measTheta m hm * measCX m hm / (4 * measKstar m hm * (measKstar m hm + 4))) with hM
  have hMpos : 0 < M := measAlphaM_pos m hm
  have hM1 : M ≤ 1 / 27 := (min_le_left _ _).trans (min_le_left _ _)
  have hMβ : M ≤ measBetaStar m / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hMc : M ≤ measTheta m hm * measCX m hm / (4 * measKstar m hm * (measKstar m hm + 4)) :=
    min_le_right _ _
  have hMle1 : M ≤ 1 := by linarith
  have hα0' : α ≤ M ^ (47 / 44 : ℝ) := hα0
  have hαM : α ≤ M := hα0'.trans (by
    calc M ^ (47 / 44 : ℝ) ≤ M ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hMpos hMle1 (by norm_num)
      _ = M := Real.rpow_one M)
  have hα1 : α ≤ 1 := by linarith
  have hhat : alphaHat α ≤ M := by
    unfold alphaHat
    calc α ^ (44 / 47 : ℝ) ≤ (M ^ (47 / 44 : ℝ)) ^ (44 / 47 : ℝ) :=
          Real.rpow_le_rpow hα.le hα0' (by norm_num)
      _ = M := by rw [← Real.rpow_mul hMpos.le]; norm_num
  have hα_hat : α ≤ alphaHat α := by
    unfold alphaHat
    calc α = α ^ (1 : ℝ) := (Real.rpow_one α).symm
      _ ≤ α ^ (44 / 47 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  have hchk : alphaCheck α ≤ α := by
    unfold alphaCheck
    calc α ^ (48 / 47 : ℝ) ≤ α ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
      _ = α := Real.rpow_one α
  exact ⟨Real.rpow_pos_of_pos hα _, hchk, hα_hat, hhat.trans hM1, hhat.trans hMβ, hhat.trans hMc⟩

theorem theta_mul_LA_le {θ : ℝ} (hθ : θ ≤ measTheta0 m hm) : θ * measLA m hm ≤ 1 / 8 := by
  have hLA := measLA_pos m hm
  unfold measTheta0 at hθ
  have h1 : θ * measLA m hm ≤ (measLA m hm)⁻¹ * min (1 / 8) (measSigmaX m hm / (2 * (measKstar m hm
      + 2))) *
      measLA m hm := mul_le_mul_of_nonneg_right hθ hLA.le
  have h2 : (measLA m hm)⁻¹ * min (1 / 8) (measSigmaX m hm / (2 * (measKstar m hm + 2))) *
      measLA m hm = min (1 / 8) (measSigmaX m hm / (2 * (measKstar m hm + 2))) := by
    field_simp
  rw [h2] at h1
  exact h1.trans (min_le_left _ _)

end alpha

section pair

variable (m : ℝ) (hm : 0 < m)
variable {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {D : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ → ℝ} {εω ε1 ε2 θ : ℝ}

theorem linF_sub (l : ℕ →₀ ℤ) (f g : ℕ → ℝ) :
    linF l f - linF l g = l.sum fun ν v => (v : ℝ) * (f ν - g ν) := by
  unfold linF Finsupp.sum
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ν _ => by ring

theorem linF_sub' (l : ℕ →₀ ℤ) (f g : ℕ → ℝ) :
    linF l (fun ν => f ν - g ν) = linF l f - linF l g := by
  rw [linF_sub]
  rfl

theorem abs_linF_le_absWt (l : ℕ →₀ ℤ) (f : ℕ → ℝ) (b : ℕ → ℝ)
    (hf : ∀ ν, |f ν| ≤ b ν) :
    |l.sum fun ν v => (v : ℝ) * f ν| ≤ l.sum fun ν v => |(v : ℝ)| * b ν := by
  unfold Finsupp.sum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hf ν) (abs_nonneg _)

theorem normLab_inv_eq (ν : ℕ) : (normLab ν)⁻¹ = normLab ν ^ (-1 : ℝ) := by
  rw [Real.rpow_neg_one]

/-- Drift of `⟨l, Ω⟩` from `⟨l, Ω⁰⟩` (blueprint `bpW:w7:sep`, step "Drift"). -/
theorem IsFreqPair.drift_le (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ D) (l : ℕ →₀ ℤ) :
    |linF l (Ω ξ) - linF l (omegaNor m hm ξ)| ≤ ε1 * absWt l (-1) + ε2 * absWt l (-(1 / 2 : ℝ)) :=
        by
  rw [linF_sub]
  have := abs_linF_le_absWt l (fun ν => Ω ξ ν - omegaNor m hm ξ ν)
    (fun ν => ε1 * normLab ν ^ (-1 : ℝ) + ε2 * normLab ν ^ (-(1 / 2 : ℝ) : ℝ)) (fun ν => by
      have h := hP.h2_sup ξ hξ ν
      rw [normLab_inv_eq] at h
      simpa using h)
  refine this.trans (le_of_eq ?_)
  unfold absWt Finsupp.sum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ν _ => by ring

theorem IsFreqPair.drift_le_two (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ D) {l : ℕ →₀ ℤ} (hl : IsLam l) :
    |linF l (Ω ξ) - linF l (omegaNor m hm ξ)| ≤ 2 * (ε1 + ε2) := by
  have h := hP.drift_le m hm hξ l
  have a1 := absWt_le_two hl (δ := -1) (by norm_num)
  have a2 := absWt_le_two hl (δ := -(1 / 2 : ℝ)) (by norm_num)
  have e1 := hP.ε1_mem.1
  have e2 := hP.ε2_mem.1
  nlinarith

/-- The tangential frequency of a pair is bounded by `W`. -/
theorem IsFreqPair.norm_omega_le (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ)
    (hsub : ∀ ξ ∈ Pi, ‖ξ‖ ≤ 1 / 2) (hαs : α ≤ 1 / 27) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ D) :
    ‖ω ξ‖ ≤ measW m hm := by
  have h1 := norm_omegaTan_le m hm (hsub ξ (hP.sub hξ))
  have h2 := hP.h1_sup ξ hξ
  have h3 := hP.εω_mem.2
  have : ω ξ = omegaTan m hm ξ + (ω ξ - omegaTan m hm ξ) := by abel
  unfold measW
  calc ‖ω ξ‖ = ‖omegaTan m hm ξ + (ω ξ - omegaTan m hm ξ)‖ := by rw [← this]
    _ ≤ ‖omegaTan m hm ξ‖ + ‖ω ξ - omegaTan m hm ξ‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem abs_sum_k_mul_le (k : Fin 2 → ℤ) (v : Fin 2 → ℝ) :
    |∑ i, (k i : ℝ) * v i| ≤ ‖v‖ * kAbs k := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold kAbs
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm v i) (abs_nonneg _)

/-- Lipschitz bound of `⟨l, Ω⟩` in the frequency coordinate (blueprint `bpW:w7:zone`, step
"The admissible `ψ`"). -/
theorem IsFreqPair.linF_lip (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ) {ξ ξ' : Fin 2 → ℝ}
    (hξ : ξ ∈ D) (hξ' : ξ' ∈ D) (l : ℕ →₀ ℤ) :
    |linF l (Ω ξ) - linF l (Ω ξ')| ≤
      measCLam m hm * absWt l (-(1 / 2 : ℝ)) * ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ := by
  have hθ := theta_mul_LA_le m hm hP.θ_mem.2
  have hθ0 := hP.θ_mem.1
  have hLA := measLA_pos m hm
  have hdist := norm_sub_le_measLA_mul m hm ξ ξ'
  have hnn := norm_nonneg (omegaTan m hm ξ - omegaTan m hm ξ')
  have hw1 : absWt l (-1) ≤ absWt l (-(1 / 2 : ℝ)) := absWt_mono (by norm_num)
  have hw0 := absWt_nonneg l (-(1 / 2 : ℝ))
  have e : linF l (Ω ξ) - linF l (Ω ξ') =
      (linF l (omegaNor m hm ξ) - linF l (omegaNor m hm ξ')) +
      (l.sum fun ν v => (v : ℝ) * ((Ω ξ ν - omegaNor m hm ξ ν) - (Ω ξ' ν - omegaNor m hm ξ' ν))) :=
          by
    rw [← linF_sub l (fun ν => (Ω ξ ν - omegaNor m hm ξ ν))
      (fun ν => (Ω ξ' ν - omegaNor m hm ξ' ν))]
    simp only [linF_sub']
    ring
  have h2 : |l.sum fun ν v => (v : ℝ) * ((Ω ξ ν - omegaNor m hm ξ ν) - (Ω ξ' ν - omegaNor m hm ξ'
      ν))| ≤
      θ * absWt l (-(1 / 2 : ℝ)) * ‖ξ - ξ'‖ := by
    have := abs_linF_le_absWt l (fun ν => (Ω ξ ν - omegaNor m hm ξ ν) - (Ω ξ' ν - omegaNor m hm ξ'
        ν))
      (fun ν => θ * normLab ν ^ (-(1 / 2 : ℝ) : ℝ) * ‖ξ - ξ'‖) (fun ν => by
        simpa using hP.h2_lip ξ hξ ξ' hξ' ν)
    refine this.trans (le_of_eq ?_)
    unfold absWt Finsupp.sum
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have h3 : θ * absWt l (-(1 / 2 : ℝ)) * ‖ξ - ξ'‖ ≤
      absWt l (-(1 / 2 : ℝ)) * ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ := by
    have : θ * ‖ξ - ξ'‖ ≤ ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ := by
      calc θ * ‖ξ - ξ'‖ ≤ θ * (measLA m hm * ‖omegaTan m hm ξ - omegaTan m hm ξ'‖) :=
            mul_le_mul_of_nonneg_left hdist hθ0
        _ = (θ * measLA m hm) * ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ := by ring
        _ ≤ 1 * ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ := by
            apply mul_le_mul_of_nonneg_right (by linarith) hnn
        _ = _ := one_mul _
    calc θ * absWt l (-(1 / 2 : ℝ)) * ‖ξ - ξ'‖ = absWt l (-(1 / 2 : ℝ)) * (θ * ‖ξ - ξ'‖) := by ring
      _ ≤ absWt l (-(1 / 2 : ℝ)) * ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ :=
          mul_le_mul_of_nonneg_left this hw0
  have h1 := abs_linF_omegaNor_sub_le m hm l ξ ξ'
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have hc : 4 / 7 * (lamTan m hm 0 + lamTan m hm 1) * absWt l (-1) *
      ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤
      4 / 7 * (lamTan m hm 0 + lamTan m hm 1) * absWt l (-(1 / 2 : ℝ)) *
      ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ := by
    have := lamTan_pos m hm 0
    have := lamTan_pos m hm 1
    gcongr
  unfold measCLam
  nlinarith

end pair

end KAM.Wave

end
