/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.Schedule
public import KAM.Planetary.WeakKAM.Cutoff
public import KAM.Planetary.WeakKAM.StripBudget

/-! # P11B weak-KAM admissible parameters

The explicit admissible constants (`adm-params`), the scalar admissibility inequalities A1--A6
(`adm-choice`) and the radius adapted to `ε` (`free-radius`). The initial-remainder inequality A7
is the separate `initial` theorem and is not part of `SelectionAdmissibility`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

/-- Constant formulas consume no perturbation and introduce no new upstream theorem. -/
def selectionM₀ (d : SelectionData n) : ℝ :=
  sSup {v | ∃ j ≤ d.μ, ∃ y ∈ selectionThick d.K d.ϑ,
    v = selectionDGVector j (frequencyMap d.h) y}
def selectionChat (d : SelectionData n) : ℝ :=
  let diam := Metric.diam d.K
  let gap := (d.ρ : ℝ) * (d.τ + 1) / d.μ - n
  2 ^ (n + 2) * d.μ * (Real.sqrt n * diam) ^ (n - 1) *
    (1 + (4 + d.ϑ⁻¹) * Real.sqrt n * diam) * d.M *
    (n : ℝ) ^ ((d.ρ : ℝ) / (2 * d.μ)) * 2 * 3 ^ (n - 1) * (1 + gap⁻¹)
def selectionCDio (d : SelectionData n) : ℝ :=
  selectionChat d * d.β ^ (-1 - (d.μ : ℝ)⁻¹)
def selectionGamma (d : SelectionData n) : ℝ :=
  min ((1 / 2 : ℝ) * (Real.sqrt n)⁻¹ * (d.β / 4) ^ ((d.ρ : ℝ)⁻¹))
    ((d.loss / selectionCDio d) ^ ((d.μ : ℝ) / d.ρ)) / 2

def selectionT₀ (d : SelectionData n) : ℝ := max 1 (16 / (π * d.strip) *
  (Real.log (16 * selectionCN n / selectionVarpi n d.μ d.τ) +
    n * Real.log (32 * n / d.strip)))
def selectiont₀ (d : SelectionData n) : ℝ :=
  min (d.ϑ / Real.sqrt n) (selectionGamma d * selectionT₀ d ^ (-d.τ - 1) / (4 * d.C₁))
def selectionXi (d : SelectionData n) : ℝ :=
  (2 : ℝ) ^ (d.τ + 1) * (1 + selectiont₀ d / (d.strip / 24) +
    (d.strip / 24) / selectiont₀ d + selectionT₀ d * (d.strip / 24))
def selectionThetaMax (d : SelectionData n) : ℝ :=
  if d.ρ = 1 then d.β / 2 else
    min d.β (d.β / (2 ^ (d.μ + 1) * (2 * selectionM₀ d + d.β)))
def selectionLambdaMax (d : SelectionData n) : ℝ := min (d.C₁ * selectiont₀ d / 8)
  (min ((min (selectionVarpi n d.μ d.τ / 2) ((2 : ℝ)⁻¹ ^ 10 / selectionXi d)) *
    (π * selectionGamma d * (d.strip / 24) ^ (n + 1) /
      (selectionCQ n * 2 ^ n * selectionT₀ d ^ d.τ)))
    (selectionThetaMax d * selectiont₀ d ^ d.μ / (4 * selectionExtensionC n d.μ)))
def selectionAdmissible (d : SelectionData n) : ℝ := selectionLambdaMax d ^ 2 / (2 * n * d.C₁)
def adm_params (d : SelectionData n) (ε : ℝ) : SelectionSchedule n :=
  let s₀ := selectionLambdaMax d / (n * d.C₁)
  ⟨d.μ, d.τ, selectionGamma d, d.strip, selectionT₀ d, selectiont₀ d,
    s₀, ε + n / 2 * d.C₁ * s₀ ^ 2⟩
def selectionAdapted (d : SelectionData n) (ε : ℝ) : SelectionSchedule n :=
  ⟨d.μ, d.τ, selectionGamma d, d.strip, selectionT₀ d, selectiont₀ d,
    Real.sqrt (2 * ε / (n * d.C₁)), 2 * ε⟩

/-- Exact scalar A1--A6; A7 remains the separate `initial` theorem. -/
structure SelectionAdmissibility (d : SelectionData n) (a : SelectionSchedule n) : Prop where
  t_pos : 0 < a.t₀
  t_le : a.t₀ ≤ d.ϑ / Real.sqrt n
  collar : 4 * d.C₁ * a.t₀ ≤ a.γ * a.T₀ ^ (-a.τ - 1)
  increment : 8 * (a.ε₀ / a.s₀) ≤ d.C₁ * a.t₀
  radius : a.s₀ ≤ a.t₀ / (8 * n)
  quadratic : selectionQ₀ a ≤ selectionVarpi n a.μ a.τ / 2
  weighted : selectionQ₀ a * selectionXi d ≤ (2 : ℝ)⁻¹ ^ 10
  closeness : 4 * selectionExtensionC n a.μ * (a.ε₀ / a.s₀) / a.t₀ ^ a.μ
    ≤ selectionThetaMax d
  cutoff_ge : 1 ≤ a.T₀
  cutoff_loss : 16 / (π * d.strip) *
    (Real.log (16 * selectionCN n / selectionVarpi n d.μ d.τ) +
      n * Real.log (32 * n / d.strip)) ≤ a.T₀


theorem selectionCN_pos (hn : 1 ≤ n) : 0 < selectionCN n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold selectionCN
  positivity

theorem selectionDGVector_nonneg (j : ℕ) (g : SelectionR n → SelectionR n) (y : SelectionR n) :
    0 ≤ selectionDGVector j g y := by
  unfold selectionDGVector
  refine Real.sSup_nonneg ?_
  rintro v ⟨a, -, rfl⟩
  exact Real.sqrt_nonneg _

theorem selectionM₀_nonneg (d : SelectionData n) : 0 ≤ selectionM₀ d := by
  unfold selectionM₀
  refine Real.sSup_nonneg ?_
  rintro v ⟨j, -, y, -, rfl⟩
  exact selectionDGVector_nonneg _ _ _

theorem selectionAdm_diam_pos (d : SelectionData n) : 0 < Metric.diam d.K := by
  refine Metric.diam_pos ?_ d.compact.isBounded
  by_contra h
  rw [Set.not_nontrivial_iff] at h
  haveI : Nonempty (Fin n) := ⟨⟨0, d.n_pos⟩⟩
  have := h.measure_zero volume
  exact (lt_irrefl _ (this ▸ d.positive_measure))

theorem selectionChat_pos (d : SelectionData n) : 0 < selectionChat d := by
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have hμ : (0 : ℝ) < d.μ := by exact_mod_cast d.μ_pos
  have hρ : (0 : ℝ) < d.ρ := by rcases d.rho_mem with h | h <;> simp [h]
  have hdiam := selectionAdm_diam_pos d
  have hθ := d.theta_pos
  have hM : 0 < d.M := lt_of_lt_of_le d.beta_pos d.beta_le
  have hgap : 0 < (d.ρ : ℝ) * (d.τ + 1) / d.μ - n := by
    have h1 := d.tau_gap
    rw [sub_pos, lt_div_iff₀ hμ]
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hρ] at h1
    nlinarith
  unfold selectionChat
  dsimp only
  positivity

theorem selectionCDio_pos (d : SelectionData n) : 0 < selectionCDio d := by
  have := selectionChat_pos d
  have := d.beta_pos
  unfold selectionCDio
  positivity

theorem selectionGamma_pos (d : SelectionData n) : 0 < selectionGamma d := by
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have := selectionCDio_pos d
  have := d.beta_pos
  have := d.loss_pos
  unfold selectionGamma
  positivity

theorem selectionT₀_pos (d : SelectionData n) : 1 ≤ selectionT₀ d := le_max_left _ _

theorem selectiont₀_pos (d : SelectionData n) : 0 < selectiont₀ d := by
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have hT : 0 < selectionT₀ d := lt_of_lt_of_le one_pos (selectionT₀_pos d)
  have := selectionGamma_pos d
  have := d.theta_pos
  have := d.hessian_normalized
  unfold selectiont₀
  refine lt_min (by positivity) ?_
  have : 0 < d.C₁ := by linarith
  positivity

theorem selectionXi_pos (d : SelectionData n) : 0 < selectionXi d := by
  have hT : 0 < selectionT₀ d := lt_of_lt_of_le one_pos (selectionT₀_pos d)
  have := selectiont₀_pos d
  have := d.strip_pos
  unfold selectionXi
  positivity

theorem selectionThetaMax_pos (d : SelectionData n) : 0 < selectionThetaMax d := by
  have := d.beta_pos
  have := selectionM₀_nonneg d
  unfold selectionThetaMax
  split_ifs
  · positivity
  · exact lt_min d.beta_pos (by positivity)

theorem selectionLambdaMax_pos (d : SelectionData n) : 0 < selectionLambdaMax d := by
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have hT : 0 < selectionT₀ d := lt_of_lt_of_le one_pos (selectionT₀_pos d)
  have := selectiont₀_pos d
  have := selectionGamma_pos d
  have := selectionXi_pos d
  have := selectionThetaMax_pos d
  have := d.strip_pos
  have := d.hessian_normalized
  have hC : 0 < d.C₁ := by linarith
  have hCN := selectionCN_pos d.n_pos
  have hE := selectionExtensionC_pos d.n_pos d.μ
  have hv := (selectionVarpi_pos_le_one n d.μ d.tau_nonneg).1
  have hQ : 0 < selectionCQ n := by unfold selectionCQ; positivity
  unfold selectionLambdaMax
  refine lt_min (by positivity) (lt_min ?_ (by positivity))
  exact mul_pos (lt_min (by positivity) (by positivity)) (by positivity)

theorem selectionAdmissible_pos (d : SelectionData n) : 0 < selectionAdmissible d := by
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have := selectionLambdaMax_pos d
  have := d.hessian_normalized
  unfold selectionAdmissible
  positivity

/-- Conditional helper (distinct name): the scalar inequalities A1--A6 for any initial pair
`(s₀, ε₀)` whose ratio and radius are controlled by `λ_max`. -/
theorem selectionAdmissibility_of_bounds (d : SelectionData n) (s₀ ε₀ : ℝ) (hs : 0 < s₀)
    (hlam : ε₀ / s₀ ≤ selectionLambdaMax d) (hsr : s₀ ≤ selectionLambdaMax d / (n * d.C₁)) :
    SelectionAdmissibility d
      ⟨d.μ, d.τ, selectionGamma d, d.strip, selectionT₀ d, selectiont₀ d, s₀, ε₀⟩ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have hT : 0 < selectionT₀ d := lt_of_lt_of_le one_pos (selectionT₀_pos d)
  have ht0 := selectiont₀_pos d
  have hγ := selectionGamma_pos d
  have hXi := selectionXi_pos d
  have hΘ := selectionThetaMax_pos d
  have hσ := d.strip_pos
  have hC : 0 < d.C₁ := by linarith [d.hessian_normalized]
  have hCN := selectionCN_pos d.n_pos
  have hE := selectionExtensionC_pos d.n_pos d.μ
  have hv := (selectionVarpi_pos_le_one n d.μ d.tau_nonneg).1
  have hQ : 0 < selectionCQ n := by unfold selectionCQ; positivity
  have hL1 : selectionLambdaMax d ≤ d.C₁ * selectiont₀ d / 8 := min_le_left _ _
  have hL2 : selectionLambdaMax d ≤ (min (selectionVarpi n d.μ d.τ / 2)
      ((2 : ℝ)⁻¹ ^ 10 / selectionXi d)) *
      (π * selectionGamma d * (d.strip / 24) ^ (n + 1) /
        (selectionCQ n * 2 ^ n * selectionT₀ d ^ d.τ)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hL3 : selectionLambdaMax d ≤ selectionThetaMax d * selectiont₀ d ^ d.μ /
      (4 * selectionExtensionC n d.μ) :=
    (min_le_right _ _).trans (min_le_right _ _)
  set D : ℝ := π * selectionGamma d * (d.strip / 24) ^ (n + 1) /
    (selectionCQ n * 2 ^ n * selectionT₀ d ^ d.τ) with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  have hQ0 : selectionQ₀ (n := n) ⟨d.μ, d.τ, selectionGamma d, d.strip, selectionT₀ d,
      selectiont₀ d, s₀, ε₀⟩ = (ε₀ / s₀) / D := by
    unfold selectionQ₀
    dsimp only
    rw [hD]
    field_simp
  refine ⟨ht0, min_le_left _ _, ?_, ?_, ?_, ?_, ?_, ?_, selectionT₀_pos d, le_max_right _ _⟩
  · dsimp only
    have : selectiont₀ d ≤ selectionGamma d * selectionT₀ d ^ (-d.τ - 1) / (4 * d.C₁) :=
      min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  · dsimp only
    linarith
  · dsimp only
    calc s₀ ≤ selectionLambdaMax d / (n * d.C₁) := hsr
      _ ≤ (d.C₁ * selectiont₀ d / 8) / (n * d.C₁) := by gcongr
      _ = selectiont₀ d / (8 * n) := by field_simp
  · rw [hQ0, div_le_iff₀ hDpos]
    exact hlam.trans (hL2.trans (by gcongr; exact min_le_left _ _))
  · rw [hQ0]
    have h1 : (ε₀ / s₀) / D ≤ (2 : ℝ)⁻¹ ^ 10 / selectionXi d := by
      rw [div_le_iff₀ hDpos]
      exact hlam.trans (hL2.trans (by gcongr; exact min_le_right _ _))
    calc (ε₀ / s₀) / D * selectionXi d ≤ (2 : ℝ)⁻¹ ^ 10 / selectionXi d * selectionXi d := by
          gcongr
      _ = (2 : ℝ)⁻¹ ^ 10 := by field_simp
  · dsimp only
    rw [div_le_iff₀ (pow_pos ht0 _)]
    rw [le_div_iff₀ (by positivity)] at hL3
    nlinarith

theorem adm_choice (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    0 < selectionAdmissible d ∧ SelectionAdmissibility d (adm_params d ε) ∧
    (adm_params d ε).ε₀ / (adm_params d ε).s₀ ≤ selectionLambdaMax d := by
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have hC : 0 < d.C₁ := by linarith [d.hessian_normalized]
  have hm : 0 < (n : ℝ) * d.C₁ := by positivity
  have hL := selectionLambdaMax_pos d
  set L := selectionLambdaMax d with hLdef
  have hs : 0 < L / (n * d.C₁) := by positivity
  have hε : ε * (2 * n * d.C₁) ≤ L ^ 2 := by
    have := hsmall
    unfold selectionAdmissible at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hratio : (ε + n / 2 * d.C₁ * (L / (n * d.C₁)) ^ 2) / (L / (n * d.C₁)) ≤ L := by
    rw [div_le_iff₀ hs]
    have h1 : n / 2 * d.C₁ * (L / (n * d.C₁)) ^ 2 = L * (L / (n * d.C₁)) / 2 := by
      field_simp
    have h2 : ε ≤ L * (L / (n * d.C₁)) / 2 := by
      rw [show L * (L / (n * d.C₁)) / 2 = L ^ 2 / (2 * n * d.C₁) by field_simp,
        le_div_iff₀ (by positivity)]
      exact hε
    rw [h1]
    linarith
  refine ⟨selectionAdmissible_pos d, ?_, hratio⟩
  exact selectionAdmissibility_of_bounds d _ _ hs hratio le_rfl

theorem free_radius (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    SelectionAdmissibility d (selectionAdapted d ε) ∧
    0 < (selectionAdapted d ε).s₀ ∧
    (selectionAdapted d ε).s₀ ≤ (adm_params d ε).s₀ ∧
    (selectionAdapted d ε).ε₀ = ε + n / 2 * d.C₁ * (selectionAdapted d ε).s₀ ^ 2 ∧
    (selectionAdapted d ε).ε₀ / (selectionAdapted d ε).s₀ = Real.sqrt (2 * n * d.C₁ * ε) ∧
    (selectionAdapted d ε).ε₀ / (selectionAdapted d ε).s₀ ≤ selectionLambdaMax d := by
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have hC : 0 < d.C₁ := by linarith [d.hessian_normalized]
  have hm : 0 < (n : ℝ) * d.C₁ := by positivity
  have hL := selectionLambdaMax_pos d
  set L := selectionLambdaMax d with hLdef
  have hε : ε * (2 * n * d.C₁) ≤ L ^ 2 := by
    have := hsmall
    unfold selectionAdmissible at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hq : 0 < 2 * ε / (n * d.C₁) := by positivity
  have hs : 0 < Real.sqrt (2 * ε / (n * d.C₁)) := Real.sqrt_pos.2 hq
  have hsq : Real.sqrt (2 * ε / (n * d.C₁)) ^ 2 = 2 * ε / (n * d.C₁) := Real.sq_sqrt hq.le
  have hsle : Real.sqrt (2 * ε / (n * d.C₁)) ≤ L / (n * d.C₁) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, div_le_div_iff₀ hm (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hε hm.le]
  have hprod : Real.sqrt (2 * ε / (n * d.C₁)) * Real.sqrt (2 * n * d.C₁ * ε) = 2 * ε := by
    rw [← Real.sqrt_mul hq.le]
    rw [show 2 * ε / (n * d.C₁) * (2 * n * d.C₁ * ε) = (2 * ε) ^ 2 by field_simp]
    exact Real.sqrt_sq (by linarith)
  have hratio : 2 * ε / Real.sqrt (2 * ε / (n * d.C₁)) = Real.sqrt (2 * n * d.C₁ * ε) := by
    rw [div_eq_iff hs.ne']
    linarith [hprod]
  have hle : Real.sqrt (2 * n * d.C₁ * ε) ≤ L := by
    rw [Real.sqrt_le_iff]
    exact ⟨hL.le, by nlinarith⟩
  refine ⟨?_, hs, hsle, ?_, hratio, hratio.le.trans hle⟩
  · exact selectionAdmissibility_of_bounds d _ _ hs (hratio.le.trans hle) hsle
  · show 2 * ε = ε + n / 2 * d.C₁ * Real.sqrt (2 * ε / (n * d.C₁)) ^ 2
    rw [hsq]
    field_simp
    ring

end KAM.Planetary
