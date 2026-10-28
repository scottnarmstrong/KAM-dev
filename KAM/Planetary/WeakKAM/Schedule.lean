/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.Data

/-! # P11B weak-KAM schedule

The constants of the geometric schedule (`schedule-consts`, `schedule-ratios`), the geometric
recursion (`geom-recursion`), the schedule record `SelectionSchedule` and its scalar sequences
(`schedule`), and the raw chain carrier `SelectionChain` with the shell and retained-set
definitions and the two prefix predicates `SelectionExtensionChain` / `SelectionFiniteChain`
(`sec-retained#data`). No inequality about the schedule is assumed in any definition.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ τ : ℝ}

/-- Upstream p11a2 formula, not an invented Fourier representation. -/
def selectionCN (n : ℕ) : ℝ :=
  2 * (1 + 1 / π) * (3 * n / (Real.exp 1 * π)) ^ (n - 1)
def selectionCutoffError (n : ℕ) (T d : ℝ) : ℝ :=
  selectionCN n * (1 + d⁻¹ ^ n) * Real.exp (-π * T * d)
def selectionExponent (n μ : ℕ) (τ : ℝ) : ℝ := 2 * (τ + 1) * (μ + 1) + n + 4
def selectionVarpi (n μ : ℕ) (τ : ℝ) : ℝ := (2 : ℝ) ^ (-2 * selectionExponent n μ τ)
def selectionQ (n μ : ℕ) (τ : ℝ) : ℝ := Real.sqrt (selectionVarpi n μ τ) / 4
def selectionVarrho (n μ : ℕ) (τ : ℝ) : ℝ := selectionVarpi n μ τ / selectionQ n μ τ
def selectionCQ (n : ℕ) : ℝ := 18 * n * (4 * n + 5)
def selectionG (n μ : ℕ) (τ : ℝ) : Fin 4 → ℝ :=
  let v := selectionVarrho n μ τ
  ![v * (2 : ℝ) ^ τ * 2 ^ (n + 1), v * (2 : ℝ) ^ (τ + 1),
    v * (2 : ℝ) ^ ((τ + 1) * μ), v * (2 : ℝ) ^ (2 * τ) * 2 ^ (n + 1)]
def schedule_consts (n μ : ℕ) (τ : ℝ) : ℝ × ℝ × ℝ :=
  (selectionVarpi n μ τ, selectionQ n μ τ, selectionVarrho n μ τ)

theorem schedule_ratios (hn : 1 ≤ n) (hμ : 1 ≤ μ) (hτ : 0 ≤ τ) :
    0 < selectionQ n μ τ ∧ selectionQ n μ τ ≤ (2 : ℝ)⁻¹ ^ 5 ∧
    2 * selectionQ n μ τ ^ 2 = selectionVarpi n μ τ / 8 ∧
    (∀ i, selectionG n μ τ i ≤ (2 : ℝ)⁻¹ ^ 5) ∧
    selectionVarrho n μ τ ≤ (2 : ℝ) ^ (-(τ + 1)) / 32 := sorry

theorem geom_recursion {v c P p : ℝ} (hv : 0 < v) (hv1 : v < 1)
    (hc0 : 0 ≤ c) (hc : c ≤ 3 * v / 8) (hP : 0 < P) (hp : 0 < p)
    (hpv : p * v ≤ 1) (x : ℕ → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hzero : P * x 0 ≤ v / 2)
    (hrec : ∀ j, x (j + 1) ≤ x j * (c + P * p ^ j * x j)) :
    ∀ j, x j ≤ x 0 * v ^ j ∧ P * p ^ j * x j ≤ v / 2 ∧
      x (j + 1) ≤ 7 * v * x j / 8 := by
  have hpv0 : 0 ≤ p * v := by positivity
  have aux : ∀ j, x j ≤ x 0 * v ^ j → P * p ^ j * x j ≤ v / 2 := by
    intro j hj
    have h1 : (p * v) ^ j ≤ 1 := pow_le_one₀ hpv0 hpv
    calc P * p ^ j * x j ≤ P * p ^ j * (x 0 * v ^ j) := by gcongr
      _ = P * x 0 * (p * v) ^ j := by rw [mul_pow]; ring
      _ ≤ P * x 0 * 1 := by gcongr; exact mul_nonneg hP.le (hx 0)
      _ ≤ v / 2 := by simpa using hzero
  have step : ∀ j, x j ≤ x 0 * v ^ j → x (j + 1) ≤ 7 * v * x j / 8 := by
    intro j hj
    have h2 := aux j hj
    calc x (j + 1) ≤ x j * (c + P * p ^ j * x j) := hrec j
      _ ≤ x j * (3 * v / 8 + v / 2) := by gcongr; exact hx j
      _ = 7 * v * x j / 8 := by ring
  have ind : ∀ j, x j ≤ x 0 * v ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := step j ih
      calc x (j + 1) ≤ 7 * v * x j / 8 := this
        _ ≤ v * x j := by nlinarith [hx j]
        _ ≤ v * (x 0 * v ^ j) := by gcongr
        _ = x 0 * v ^ (j + 1) := by ring
  exact fun j => ⟨ind j, aux j (ind j), step j (ind j)⟩

/-- Formula inputs; no inequalities or iteration conclusions are hidden here. -/
structure SelectionSchedule (n : ℕ) where
  μ : ℕ
  τ : ℝ
  γ : ℝ
  strip : ℝ
  T₀ : ℝ
  t₀ : ℝ
  s₀ : ℝ
  ε₀ : ℝ

def selectionT (a : SelectionSchedule n) (j : ℕ) : ℝ := a.T₀ * 2 ^ j
def selectionD (a : SelectionSchedule n) (j : ℕ) : ℝ := a.γ * selectionT a j ^ (-a.τ)
def selectiont (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  a.t₀ * (2 : ℝ) ^ (-(a.τ + 1) * j)
def selectionε (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  a.ε₀ * selectionVarpi n a.μ a.τ ^ j
def selections (a : SelectionSchedule n) (j : ℕ) : ℝ := a.s₀ * selectionQ n a.μ a.τ ^ j
def selectionσ (a : SelectionSchedule n) (j : ℕ) : ℝ := a.strip / 24 * (2 : ℝ)⁻¹ ^ j
def selectiond (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  (Real.log (16 * selectionCN n / selectionVarpi n a.μ a.τ) +
    n * Real.log (π * selectionT a j)) / (π * selectionT a j)
def selectionr (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  a.strip - ∑ i ∈ Finset.range j, (selectiond a i + 3 * selectionσ a i)
def selectionell (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  2 * selectionε a j / selections a j
def selectionTail (a : SelectionSchedule n) (m : ℕ) : ℝ := ∑' j, selectionell a (j + m)
def selectionQsharp (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  selectionCQ n * (2 / selectionσ a j) ^ n * selectionε a j /
    (π * selectionD a j * selections a j * selectionσ a j)
def selectionQ₀ (a : SelectionSchedule n) : ℝ :=
  selectionCQ n * 2 ^ n * a.T₀ ^ a.τ * (a.ε₀ / a.s₀) /
    (π * a.γ * (a.strip / 24) ^ (n + 1))
def schedule (a : SelectionSchedule n) := a

/-- Chain carrier is raw data; all chain properties are returned by the construction. -/
structure SelectionChain (n : ℕ) where
  K : ℕ → Set (SelectionR n)
  Δω : ℕ → SelectionC n → SelectionC n
  Δh : ℕ → SelectionC n → ℂ
  X : ℕ → SelectionC n → SelectionPhaseC n → SelectionPhaseC n
  R : ℕ → SelectionPoint n → ℂ

def selectionFrequency (d : SelectionData n) (c : SelectionChain n)
    (j : ℕ) (b : SelectionC n) : SelectionC n :=
  (fun i => fderiv ℂ d.h b (Pi.single i 1)) + ∑ i ∈ Finset.range j, c.Δω i b
def selectionEnergy (c : SelectionChain n) (j : ℕ) (b : SelectionC n) : ℂ :=
  ∑ i ∈ Finset.range j, c.Δh i b
def selectionCompose (c : SelectionChain n) (b : SelectionC n) : ℕ →
    SelectionPhaseC n → SelectionPhaseC n
  | 0 => id
  | j + 1 => selectionCompose c b j ∘ c.X j b

def selectionModeLength (k : Fin n → ℤ) : ℝ := ∑ i, |(k i : ℝ)|
def selectionShell (a : SelectionSchedule n) (j : ℕ) : Set (Fin n → ℤ) :=
  {k | 0 < selectionModeLength k ∧ selectionModeLength k ≤ selectionT a j ∧
    (j = 0 ∨ selectionT a (j - 1) < selectionModeLength k)}
/-- Explicit representative of the unique shell index for nonzero modes and T0≥1. -/
def selectionModeStage (a : SelectionSchedule n) (k : Fin n → ℤ) : ℕ :=
  ⌈Real.log (selectionModeLength k / a.T₀) / Real.log 2⌉₊
def selectionExtendedFrequency (d : SelectionData n) (c : SelectionChain n)
    (χ : ℕ → SelectionR n → ℝ) (ν : ℕ) (y : SelectionR n) : SelectionR n :=
  frequencyMap d.h y + ∑ j ∈ Finset.range ν,
    χ j y • selectionRe (c.Δω j (selectionReal y))

def selectionRetained (a : SelectionSchedule n) (d : SelectionData n)
    (c : SelectionChain n) (j : ℕ) : Set (SelectionR n) :=
  {b ∈ c.K j | ∀ k ∈ selectionShell a j,
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      ‖∑ i, (k i : ℂ) * selectionFrequency d c j (selectionReal b) i‖}
/-- Analytic nested-prefix premises of finite-extension; no resonance tests are required. -/
structure SelectionExtensionChain (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) : Prop where
  initial : c.K 0 = d.K
  compact : ∀ j ≤ ν, IsCompact (c.K j)
  nonempty : ∀ j ≤ ν, (c.K j).Nonempty
  nested : ∀ j < ν, c.K (j + 1) ⊆ c.K j
  holomorphic : ∀ j < ν, DifferentiableOn ℂ (c.Δω j) (actionNbhd (c.K j) (selectiont a j))
  real : ∀ j < ν, ∀ b : SelectionR n,
    selectionReal b ∈ actionNbhd (c.K j) (selectiont a j) →
    c.Δω j (selectionReal b) = selectionReal (selectionRe (c.Δω j (selectionReal b)))
  bound : ∀ j < ν, ∀ b ∈ actionNbhd (c.K j) (selectiont a j),
    ‖c.Δω j b‖ ≤ selectionell a j

/-- Retained prefixes additionally satisfy the shell tests used by divisor and measure estimates.
The generated `toSelectionExtensionChain` projection supplies finite-extension's weaker input. -/
structure SelectionFiniteChain (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) : Prop extends SelectionExtensionChain d a c ν where
  retained : ∀ j < ν, c.K (j + 1) = selectionRetained a d c j

def sec_retained_data (c : SelectionChain n) := c

end KAM.Planetary
