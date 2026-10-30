/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Quantitative.Interface
public import KAM.Russmann.Bounds

/-!
# Track R: track P's data and hypotheses from R-HEAD's hypotheses

* `russmannData`: the datum `QuantitativeData n` used in R-HEAD's proof (`ρ = 1`, `τ = n μ`).
* `russmannData_valid`: its validity (`QuantitativeData.Valid`) from the numerical choices.
* `russmannData_input`: `QuantitativeInput` for this datum from R-HEAD's hypotheses on `h` and `f`,
  the finite-type estimate of Rüssmann's lemma on `K`, and the compactness bounds of
  `KAM.Russmann.Bounds`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Russmann

open KAM KAM.Planetary

variable {n : ℕ}

/-- The datum of track P's quantitative theorem chosen in R-HEAD's proof: order `μ`, `ρ = 1`,
Diophantine exponent `τ = n μ`, thickness `ϑ`, strip `s`, amount `β`, bounds `M, M₀, C₁`, loss
`ε*` and compact parameter set `K`. -/
def russmannData (n μ : ℕ) (ϑ s β M M0 C1 εs : ℝ) (K : Set (Fin n → ℝ)) :
    QuantitativeData n :=
  { mu := μ, rho := 1, tau := (n : ℝ) * μ, vartheta := ϑ, s := s, beta := β, M := M, M0 := M0,
    C1 := C1, epsLoss := εs, K := K }

theorem russmannData_valid {μ : ℕ} (hn : 1 ≤ n) (hμ : 1 ≤ μ) {ϑ s β M M0 C1 εs : ℝ}
    {K : Set (Fin n → ℝ)} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hC1 : 1 ≤ C1) (hM0 : 0 < M0) (hβ0 : 0 < β) (hβM : β ≤ M) (hβ1 : β ≤ 1)
    (hK : IsCompact K) (hεs : 0 < εs) (hεK : ENNReal.ofReal εs < volume K) :
    (russmannData n μ ϑ s β M M0 C1 εs K).Valid := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hμ' : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
  refine ⟨⟨hn, hμ, Or.inl rfl, ?_, ?_, hϑ0, hϑ1, hs0, hs1, hC1, hM0, hβ0, hβM, hK, hεs, hεK⟩,
    ?_, hβ1⟩
  · simp only [russmannData, Nat.cast_one, div_one]; linarith
  · simp only [russmannData]; positivity
  · simp only [russmannData]; nlinarith

/-- `QuantitativeInput` for `russmannData` from R-HEAD's hypotheses on `h` and `f` (restricted
from `complexStrip n s₀ ×ˢ actionNbhd B r₀`), the finite-type estimate with amount `β₀ ≥ β` on
`K`, a bound `A` on `‖D^j ∇h‖` (`j ≤ μ + 1`) over the Euclidean `ϑ`-thickening of `K`, and a
bound `C` on the complex Hessian over `actionNbhd K (2ϑ)`. -/
theorem russmannData_input {μ : ℕ} {ϑ s β M M0 C1 εs : ℝ} {K B : Set (Fin n → ℝ)}
    {s₀ r₀ : ℝ} (hKB : K ⊆ B) (hϑ : 0 < ϑ) (hϑr : 2 * ϑ < r₀) (hss : s ≤ s₀)
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h (actionNbhd B r₀))
    (hh_real : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B r₀ →
      (h fun i => (I i : ℂ)).im = 0)
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀))
    (hf_per : ∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
      f (z.1 + (fun i => (k i : ℂ)), z.2) = f z)
    (hf_real : ∀ θ I : Fin n → ℝ,
      ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ →
      (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    {β₀ : ℝ} (hββ : β ≤ β₀)
    (hfin : ∀ c : Fin n → ℝ, KAM.Nekhoroshev.euclid c = 1 → ∀ y ∈ K,
      ∃ j ≤ μ, ∃ v : Fin n → ℝ, KAM.Nekhoroshev.euclid v = 1 ∧
        β₀ ≤ |iteratedFDeriv ℝ j (p11c_scalar 1 (frequencyMap h) c) y (fun _ => v)|)
    {A : ℝ} (hA : ∀ j ≤ μ + 1, ∀ y ∈ {y : Fin n → ℝ | ∃ x ∈ K, KAM.Nekhoroshev.euclid (y - x) ≤ ϑ},
      ‖iteratedFDeriv ℝ j (frequencyMap h) y‖ ≤ A)
    (hM : n * A ≤ M) (hM0 : Real.sqrt n * A ≤ M0)
    {C : ℝ} (hC : ∀ y ∈ actionNbhd K (2 * ϑ),
      ‖fderiv ℂ (fun x : Fin n → ℂ => fun i => fderiv ℂ h x (Pi.single i 1)) y‖ ≤ C)
    (hC1 : C ≤ C1) :
    QuantitativeInput (russmannData n μ ϑ s β M M0 C1 εs K) h f := by
  have hU : actionNbhd K (2 * ϑ) ⊆ actionNbhd B r₀ := by
    rintro I ⟨J, hJ, hI⟩
    exact ⟨J, hKB hJ, hI.trans hϑr⟩
  have hS : complexStrip n s ⊆ complexStrip n s₀ := fun θ hθ i => (hθ i).trans_le hss
  have hP : complexStrip n s ×ˢ actionNbhd K (2 * ϑ) ⊆ complexStrip n s₀ ×ˢ actionNbhd B r₀ :=
    prod_mono hS hU
  have hthick := euclidThick_subset_realNbhd (B := B) hKB (show ϑ < r₀ by linarith)
  have hω := analyticOnNhd_frequencyMap hh
  have hcd : ∀ y ∈ {y : Fin n → ℝ | ∃ x ∈ K, KAM.Nekhoroshev.euclid (y - x) ≤ ϑ},
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (frequencyMap h) y :=
    fun y hy => (hω y (hthick hy)).contDiffAt
  refine ⟨hh.mono hU, hf.mono hP, fun z hz k => hf_per z (hP hz) k,
    fun y hy => hh_real y (hU hy), fun z hz => hf_real z.1 z.2 (hP hz), ?_, ?_, ?_, ?_⟩
  · intro c hc y hy
    obtain ⟨j, hj, v, hv, hge⟩ := hfin c hc y hy
    exact ⟨j, hj, v, hv, hββ.trans hge⟩
  · intro c hc j _ hj2 y hy v hv
    refine (abs_iteratedFDeriv_scalar_le (hcd y hy) hc j hv).trans (le_trans ?_ hM)
    exact mul_le_mul_of_nonneg_left (hA j hj2 y hy) (Nat.cast_nonneg n)
  · intro y hy
    exact (hC y hy).trans hC1
  · intro j hj y hy v hv
    refine (euclid_iteratedFDeriv_le y j hv).trans (le_trans ?_ hM0)
    exact mul_le_mul_of_nonneg_left (hA j (by have : j ≤ μ := hj; omega) y hy)
      (Real.sqrt_nonneg _)

end KAM.Russmann

end
