/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.CohData
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Small-divisor constants at a bite (v2)

`SDConst` (blueprint `bp:p2s2sd:const`) is a small-divisor constant at one bite `δ` on a set `Ω` of
frequencies; `sdSum`, `sdFinite`, `shellConst`, `sdTail`, `sdEps`, `cohConstC`, `cohConstF` are the
quantities of `bp:p2s2sd:classical` and `bp:p2s2sd:freq`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2

open KAM.Torus KAM.Apost

/-- Blueprint `bp:p2s2sd:const`: `c` is a small-divisor constant at the bite `δ` on the frequency set `Ω`
(exponent `κ`, Diophantine scale `γ`): the solution and a-priori clauses of `KAM.Sharp.CohData` at this one bite, for
every `ω ∈ Ω`. -/
structure SDConst (n : ℕ) (κ γ δ c : ℝ) (Ω : Set (Fin n → ℝ)) : Prop where
  c_pos : 0 < c
  delta_pos : 0 < δ
  sol : ∀ ω ∈ Ω, ∀ {r : ℝ}, δ < r → ∀ {p : ℕ} (g : (Fin n → ℂ) → Fin p → ℂ) (H : ℝ),
    DifferentiableOn ℂ g (complexStrip n r) → IsPeriodicOn g r →
    (∀ θ ∈ complexStrip n r, ‖g θ‖ ≤ H) → avg g = 0 →
    ∀ θ ∈ complexStrip n (r - δ), ‖cohR ω g θ‖ ≤ c * γ⁻¹ * δ ^ (-κ) * H
  apriori : ∀ ω ∈ Ω, ∀ {r : ℝ}, δ < r → ∀ {p q : ℕ} (u : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ) (H : ℝ),
    DifferentiableOn ℂ u (complexStrip n r) → IsPeriodicOn u r → avg u = 0 →
    (∀ θ ∈ complexStrip n r, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) →
    ∀ θ ∈ complexStrip n (r - δ), ‖u θ‖ ≤ c * γ⁻¹ * δ ^ (-κ) * H
  /-- the solution clause at real points, for every strip `r ≥ δ` (the bite may be the whole strip) -/
  real : ∀ ω ∈ Ω, ∀ {r : ℝ}, δ ≤ r → ∀ {p : ℕ} (g : (Fin n → ℂ) → Fin p → ℂ) (H : ℝ),
    DifferentiableOn ℂ g (complexStrip n r) → IsPeriodicOn g r →
    (∀ θ ∈ complexStrip n r, ‖g θ‖ ≤ H) → avg g = 0 →
    ∀ θ : Fin n → ℝ, ‖cohR ω g (fun i => (θ i : ℂ))‖ ≤ c * γ⁻¹ * δ ^ (-κ) * H

/-- The ray `{s ω* : s ≥ 1}`. -/
def ray {n : ℕ} (ωstar : Fin n → ℝ) : Set (Fin n → ℝ) := {ω | ∃ s : ℝ, 1 ≤ s ∧ ω = s • ωstar}

/-- `S(ω, b) = Σ_{k ≠ 0} |k·ω|⁻² e^{-4π b |k|₁}` (value in `[0, ∞]` as a `tsum` of nonnegative reals;
`0` if not summable, so every use carries a summability or finite-part hypothesis). -/
def sdSum {n : ℕ} (ω : Fin n → ℝ) (b : ℝ) : ℝ :=
  ∑' k : Fin n → ℤ, if k = 0 then 0 else
    (|∑ i, (k i : ℝ) * ω i|)⁻¹ ^ 2 * Real.exp (-4 * Real.pi * b * ∑ i, |(k i : ℝ)|)

/-- The finite part `Σ_{0 < |k|₁ ≤ N} |k·ω|⁻² e^{-4π b |k|₁}` (a finite sum: the certificate's object). -/
def sdFinite {n : ℕ} (ω : Fin n → ℝ) (b : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(N : ℤ)) N),
    if k = 0 ∨ N < ∑ i, (k i).natAbs then 0 else
      (|∑ i, (k i : ℝ) * ω i|)⁻¹ ^ 2 * Real.exp (-4 * Real.pi * b * ∑ i, |(k i : ℝ)|)

/-- `A_τ = 2^{2τ+1} ζ(2, 2^τ)` with `ζ(2, a) = Σ_{j ≥ 0} (a + j)⁻²` (`bp:p2s2sd:shell`). -/
def shellConst (τ : ℝ) : ℝ := 2 ^ (2 * τ + 1) * ∑' j : ℕ, ((2 : ℝ) ^ τ + j)⁻¹ ^ 2

/-- The classical tail `T_N(b) = (1 - e^{-4πb}) A_τ γ⁻² Σ_{M > N} M^{2τ} e^{-4π b M}` (`bp:p2s2sd:abel`). -/
def sdTail (τ γ b : ℝ) (N : ℕ) : ℝ :=
  (1 - Real.exp (-4 * Real.pi * b)) * shellConst τ * γ⁻¹ ^ 2 *
    ∑' M : ℕ, if M ≤ N then 0 else (M : ℝ) ^ (2 * τ) * Real.exp (-4 * Real.pi * b * M)

/-- `ε_τ(x) = x (2τ/e)^{2τ} / Γ(2τ+1)`. -/
def sdEps (τ x : ℝ) : ℝ := x * (2 * τ / Real.exp 1) ^ (2 * τ) / Real.Gamma (2 * τ + 1)

/-- The classical constant `c♮(n, τ, δ)` of `bp:p2s2sd:classical`. -/
def cohConstC (n : ℕ) (τ δ : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n * (shellConst τ * Real.Gamma (2 * τ + 1) * (1 + sdEps τ (4 * Real.pi * δ)))) *
    (4 * Real.pi) ^ (-τ)

/-- The frequency-specific constant `c_{ω*}(δ; N, Ŝ)` of `bp:p2s2sd:freq`. -/
def cohConstF (n : ℕ) (τ γ δ : ℝ) (N : ℕ) (Shat : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * γ * δ ^ τ * Real.sqrt (2 ^ n * (Shat + sdTail τ γ δ N))

end KAM.Sharp2

end
