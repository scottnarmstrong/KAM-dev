/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Application.LambdaDrift.LieRemainder
public import KAM.Planetary.Exponential.Lift

/-!
# The order-2 Lie remainder identity in LP's chart

Design `docs/campaign/design/HD11964-PILOT.md` §6.2–§6.3. The identity of `LieRemainder.lean` for
the original Hamiltonian of the bridge: `H = liftChartHam ν μ` (the moving Hamiltonian through LP's
Poincaré chart), split as the Kepler part `h = hProd 1 ν` (`−Σ ν_i³ / (2 Λ_i²)`, independent of
every angle) plus `P = H − h` (`chartPert`). The action is `Λ_i = w.2 (Fin.castAdd n i)`; its angle
is `λ_i`.

`chartRate_approxIntegral₂` rewrites the bridge's rate `fderiv ℝ (F i) w (X_H w)` of `F i =
approxIntegral₂ (Fin.castAdd n i) χ₁ χ₂` as the five terms of the identity, on any open `O ⊆
chartSafe ν` where the generators are smooth. `chartRate_bound` turns term bounds on a set `R ⊆ O`
into the bridge's `hη`. `approxIntegral₂_sub_fast` is the bridge's `F i − Λ_i`.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Planetary
open scoped ContDiff

namespace KAM.Application.LambdaDrift

variable {n : ℕ}

/-- The perturbation `P = H ∘ Ψ − h(Λ)` of LP's chart Hamiltonian. -/
def chartPert (ν : Fin n → ℝ) (μ : ℝ) : Phase (n + n) → ℝ :=
  fun y => liftChartHam ν μ y - hProd 1 ν y

/-- A function constant along a line has zero derivative along it. -/
theorem fderiv_apply_eq_zero_of_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {y u : E} (hconst : ∀ t : ℝ, f (y + t • u) = f y) : fderiv ℝ f y u = 0 := by
  by_cases hf : DifferentiableAt ℝ f y
  · have hline : HasDerivAt (fun t : ℝ => y + t • u) ((1 : ℝ) • u) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add y
    have h1 : HasDerivAt (fun t : ℝ => f (y + t • u)) (fderiv ℝ f y ((1 : ℝ) • u)) 0 :=
      hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
    have h2 : HasDerivAt (fun t : ℝ => f (y + t • u)) 0 0 := by
      have : (fun t : ℝ => f (y + t • u)) = fun _ => f y := funext hconst
      rw [this]
      exact hasDerivAt_const _ _
    have := h1.unique h2
    rwa [one_smul] at this
  · rw [fderiv_zero_of_not_differentiableAt hf]
    rfl

/-- The Kepler part does not depend on any angle. -/
theorem fderiv_hProd_angleDir (ν : Fin n → ℝ) (k : Fin (n + n)) (y : Phase (n + n)) :
    fderiv ℝ (hProd 1 ν) y (angleDir k) = 0 :=
  fderiv_apply_eq_zero_of_line fun t => by simp [hProd, angleDir, fast]

/-- The Kepler part is smooth on the chart domain. -/
theorem contDiffOn_hProd (ν : Fin n → ℝ) : ContDiffOn ℝ ∞ (hProd 1 ν) (poincareProdDom n) := by
  intro y hy
  have hne : ∀ i, fast y.2 i ≠ 0 := fun i => by
    have h0 : (planetBlock y i).2 0 = fast y.2 i := by simp [planetBlock]
    rw [← h0]
    exact (hy i).1.ne'
  have hlin : ∀ i, ContDiff ℝ ∞ (fun w : Phase (n + n) => fast w.2 i) := fun i => by
    unfold fast
    fun_prop
  have hd : ContDiffAt ℝ ∞ (hProd 1 ν) y := by
    unfold hProd
    refine ContDiffAt.neg (ContDiffAt.sum fun i _ => ?_)
    exact contDiffAt_const.div (contDiffAt_const.mul ((hlin i).contDiffAt.pow 2))
      (by have := hne i; positivity)
  exact hd.contDiffWithinAt

/-- `H ∘ Ψ` is smooth on `chartSafe ν`. -/
theorem contDiffOn_liftChartHam {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ) :
    ContDiffOn ℝ ∞ (liftChartHam ν μ) (chartSafe ν) := fun y hy =>
  ((analyticOnNhd_liftChartHam hν μ) y hy).contDiffAt.contDiffWithinAt

/-- **The order-2 identity for the bridge's rate in LP's chart.** On an open `O ⊆ chartSafe ν`
where `χ₁, χ₂` are smooth, the rate of `F i = approxIntegral₂ (Fin.castAdd n i) χ₁ χ₂` along the
original Hamiltonian `H = liftChartHam ν μ` is the five-term right side of `pb_approxIntegral₂`, for
`h = hProd 1 ν` and `P = chartPert ν μ`. -/
theorem chartRate_approxIntegral₂ {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ) (i : Fin n)
    {χ₁ χ₂ : Phase (n + n) → ℝ} {O : Set (Phase (n + n))} (hO : IsOpen O)
    (hOs : O ⊆ chartSafe ν) (h₁ : ContDiffOn ℝ ∞ χ₁ O) (h₂ : ContDiffOn ℝ ∞ χ₂ O)
    {w : Phase (n + n)} (hw : w ∈ O) :
    fderiv ℝ (approxIntegral₂ (Fin.castAdd n i) χ₁ χ₂) w
        (hamiltonianVectorField (liftChartHam ν μ) w) =
      -dirDeriv (angleDir (Fin.castAdd n i)) (residual₁ (hProd 1 ν) (chartPert ν μ) χ₁) w -
        dirDeriv (angleDir (Fin.castAdd n i))
          (residual₂ (hProd 1 ν) (chartPert ν μ) χ₁ χ₂) w +
        pb (dirDeriv (angleDir (Fin.castAdd n i))
          (residual₁ (hProd 1 ν) (chartPert ν μ) χ₁)) χ₁ w +
        pb (dirDeriv (angleDir (Fin.castAdd n i)) χ₂) (chartPert ν μ) w -
        pb (pb (dirDeriv (angleDir (Fin.castAdd n i)) χ₁) χ₁) (chartPert ν μ) w / 2 := by
  have hH : liftChartHam ν μ = fun y => hProd 1 ν y + chartPert ν μ y := by
    funext y
    simp only [chartPert]
    ring
  have hhs : ContDiffOn ℝ ∞ (hProd 1 ν) O :=
    (contDiffOn_hProd ν).mono fun y hy => chartSafe_subset_dom ν (hOs hy)
  have hPs : ContDiffOn ℝ ∞ (chartPert ν μ) O :=
    ((contDiffOn_liftChartHam hν μ).mono hOs).sub hhs
  show pb _ (liftChartHam ν μ) w = _
  rw [hH]
  exact pb_approxIntegral₂ hO (fderiv_hProd_angleDir ν _) hhs hPs h₁ h₂ hw

/-- **The bridge's `hη` from term bounds** (the cell check's soundness target): bounds on the five
terms of the identity at every point of `R ⊆ O` bound `|dF_i (X_H)|` on `R`. -/
theorem chartRate_bound {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ) (i : Fin n)
    {χ₁ χ₂ : Phase (n + n) → ℝ} {O R : Set (Phase (n + n))} (hO : IsOpen O)
    (hOs : O ⊆ chartSafe ν) (h₁ : ContDiffOn ℝ ∞ χ₁ O) (h₂ : ContDiffOn ℝ ∞ χ₂ O) (hRO : R ⊆ O)
    {a₁ a₂ a₃ a₄ a₅ : ℝ}
    (b₁ : ∀ w ∈ R, |dirDeriv (angleDir (Fin.castAdd n i))
      (residual₁ (hProd 1 ν) (chartPert ν μ) χ₁) w| ≤ a₁)
    (b₂ : ∀ w ∈ R, |dirDeriv (angleDir (Fin.castAdd n i))
      (residual₂ (hProd 1 ν) (chartPert ν μ) χ₁ χ₂) w| ≤ a₂)
    (b₃ : ∀ w ∈ R, |pb (dirDeriv (angleDir (Fin.castAdd n i))
      (residual₁ (hProd 1 ν) (chartPert ν μ) χ₁)) χ₁ w| ≤ a₃)
    (b₄ : ∀ w ∈ R, |pb (dirDeriv (angleDir (Fin.castAdd n i)) χ₂) (chartPert ν μ) w| ≤ a₄)
    (b₅ : ∀ w ∈ R,
      |pb (pb (dirDeriv (angleDir (Fin.castAdd n i)) χ₁) χ₁) (chartPert ν μ) w| ≤ a₅) :
    ∀ w ∈ R, |fderiv ℝ (approxIntegral₂ (Fin.castAdd n i) χ₁ χ₂) w
      (hamiltonianVectorField (liftChartHam ν μ) w)| ≤ a₁ + a₂ + a₃ + a₄ + a₅ / 2 := by
  intro w hw
  rw [chartRate_approxIntegral₂ hν μ i hO hOs h₁ h₂ (hRO hw)]
  have c₁ := abs_le.1 (b₁ w hw)
  have c₂ := abs_le.1 (b₂ w hw)
  have c₃ := abs_le.1 (b₃ w hw)
  have c₄ := abs_le.1 (b₄ w hw)
  have c₅ := abs_le.1 (b₅ w hw)
  rw [abs_le]
  constructor <;> linarith [c₁.1, c₁.2, c₂.1, c₂.2, c₃.1, c₃.2, c₄.1, c₄.2, c₅.1, c₅.2]

/-- The bridge's `F i − Λ_i` for `F i = approxIntegral₂ (Fin.castAdd n i) χ₁ χ₂`. -/
theorem approxIntegral₂_sub_fast (i : Fin n) (χ₁ χ₂ : Phase (n + n) → ℝ) (y : Phase (n + n)) :
    approxIntegral₂ (Fin.castAdd n i) χ₁ χ₂ y - fast y.2 i =
      dirDeriv (angleDir (Fin.castAdd n i)) χ₁ y + dirDeriv (angleDir (Fin.castAdd n i)) χ₂ y -
        pb (dirDeriv (angleDir (Fin.castAdd n i)) χ₁) χ₁ y / 2 :=
  approxIntegral₂_sub (Fin.castAdd n i) χ₁ χ₂ y

end KAM.Application.LambdaDrift

end
