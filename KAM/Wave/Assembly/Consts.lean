/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieApp
public import KAM.Wave.Homological.Wave
public import KAM.Wave.Recon2.Functionals
public import KAM.Wave.Measure.Consts
public import KAM.Wave.Measure.Shells
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# W8: constants and shells (blueprint `bpW:w8:const`, `bpW:w8:shells`)

Blueprint labels `bpW:w8:const`, `bpW:w8:shells` (milestone W8).

The W8 constants are formulas in constants of W3 (`C_*`, `C_F`, `ρ₁`, `C'_K`), W4 (`M`), W2 (`M_m`),
W7 (`α₀`), the absolute `c_A = 2200` of W5, and four constants of W5–W6 that have no Lean
definition yet: W6's `γ`, `γ₁` (Definition `bpW:w6:constants`) and W5's `c_F`, `c^♮_F`
(`bpW:w5:ledger`). Those four enter through the record `KAM.Wave.W8UpstreamConsts` (the numbers
and their signs, which their definitions give at once); once W5–W6 define them, the W8 constants
are these formulas evaluated at them. Every other constant is the landed Lean definition.

Shells (`bpW:w8:shells`): `t_n = 2^{-n} t₀` and `R_n` are W7's `shellT (1/2) t₀ n`,
`shellSet (1/2) t₀ n`; the trimmed shell `Π_n = {ξ ∈ R_n : dist(ξ, ℝ² ∖ R_n) > α_n}` uses
`Metric.infDist`. The shell objects take `t₀` as an argument; the W8 instance is
`t₀ = w8T0 m hm u`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

/-- The W5–W6 constants used by `bpW:w8:const` that have no Lean definition yet: W6's `γ`, `γ₁`
(Definition `bpW:w6:constants`) and W5's `c_F`, `c^♮_F` (`bpW:w5:ledger`), with their signs
(`γ > 0`, `γ₁ > 0`, `c_F > 0`, `c^♮_F > 0` by their definitions). -/
structure W8UpstreamConsts where
  /-- W6's `γ`. -/
  gam : ℝ
  /-- W6's `γ₁`. -/
  gam1 : ℝ
  /-- W5's `c_F = 9 C₁ b_W(τ)`. -/
  cF : ℝ
  /-- W5's `c^♮_F = 9 C₁ b^♮(τ)`. -/
  cFnat : ℝ
  gam_pos : 0 < gam
  gam1_pos : 0 < gam1
  cF_pos : 0 < cF
  cFnat_pos : 0 < cFnat

/-! ### Constants of the standing data (W2–W7) -/

/-- W5's `c_A = 2200` (Lemma `bpW:w5:action-angle`). -/
def w8cA : ℝ := 2200

/-- W3's `C_* = K_{p+1/2}²/π` at `p = 1`. -/
def w8CStar : ℝ := waveCubicConst 1

/-- W3's `C_F(m) = C_*/δ_*` at `p = 1`. -/
def w8CF (m : ℝ) : ℝ := birkCF m 1

/-- W3's `ρ₁(m) = ½ (40 C_F)^{-1/2}`. -/
def w8Rho1 (m : ℝ) : ℝ := 1 / (2 * Real.sqrt (40 * w8CF m))

/-- W3's `C'_K(m) = 66 C_* C_F`. -/
def w8CKp (m : ℝ) : ℝ := 66 * w8CStar * w8CF m

/-- W4's `M = M_ω + M_Ω` (Lemma `bpW:w4:wave` (i)). -/
def w8M (m : ℝ) (hm : 0 < m) : ℝ := waveMomega m hm + waveMOmega m hm

/-- W6's `σ_P = s/40`, `s = 1/8`. -/
def w8SigmaP : ℝ := 1 / 8 / 40

/-- W6's `σ₀ = s₀/40`, `s₀ = 7/64`. -/
def w8Sigma0 : ℝ := 7 / 64 / 40

/-! ### The W8 constants (`bpW:w8:const`) -/

/-- `E₁ = 1 + 2 C_* + 6 (2 c_A)^{5/2} C'_K` (blueprint `bpW:w8:const`). -/
def w8E1 (m : ℝ) : ℝ := 1 + 2 * w8CStar + 6 * (2 * w8cA) ^ (5 / 2 : ℝ) * w8CKp m

/-- `E₃ = (1 + 8/M) E₁` (blueprint `bpW:w8:const`). -/
def w8E3 (m : ℝ) (hm : 0 < m) : ℝ := (1 + 8 / w8M m hm) * w8E1 m

/-- `E₄ = c^♮_F γ σ_P^{-52} + 5 c_F γ₁ σ₀^{-51}` (blueprint `bpW:w8:const`). -/
def w8E4 (u : W8UpstreamConsts) : ℝ :=
  u.cFnat * u.gam * (w8SigmaP ^ 52)⁻¹ + 5 * u.cF * u.gam1 * (w8Sigma0 ^ 51)⁻¹

/-- `E₅ = E₃ E₄ / γ` (blueprint `bpW:w8:const`). -/
def w8E5 (m : ℝ) (hm : 0 < m) (u : W8UpstreamConsts) : ℝ := w8E3 m hm * w8E4 u / u.gam

/-- `E₆ = 6 √2 C_F (2 c_A)^{3/2}` (blueprint `bpW:w8:const`). -/
def w8E6 (m : ℝ) : ℝ := 6 * Real.sqrt 2 * w8CF m * (2 * w8cA) ^ (3 / 2 : ℝ)

/-- `E₇ = 162 E₅ + E₆` (blueprint `bpW:w8:const`). -/
def w8E7 (m : ℝ) (hm : 0 < m) (u : W8UpstreamConsts) : ℝ := 162 * w8E5 m hm u + w8E6 m

/-- `t₀ = min {4^{-64}, α₀^{64/95}, ρ₁²/(8 c_A), (γ/E₃)^{64}, (7/(256 E₅))^{64}}`
(blueprint `bpW:w8:const`). -/
def w8T0 (m : ℝ) (hm : 0 < m) (u : W8UpstreamConsts) : ℝ :=
  min (min (min (min ((1 / 4 : ℝ) ^ 64) (measAlpha0 m hm ^ (64 / 95 : ℝ)))
    (w8Rho1 m ^ 2 / (8 * w8cA))) ((u.gam / w8E3 m hm) ^ 64)) ((7 / (256 * w8E5 m hm u)) ^ 64)

/-- `τ = 24` (blueprint `bpW:w8:const`). -/
def w8Tau : ℝ := 24

/-- `r₀ = √(2 t₀)` (blueprint `bpW:w8:const`). -/
def w8R0 (m : ℝ) (hm : 0 < m) (u : W8UpstreamConsts) : ℝ := Real.sqrt (2 * w8T0 m hm u)

/-- `C₃ = 4 √c_A` (blueprint `bpW:w8:const`). -/
def w8C3 : ℝ := 4 * Real.sqrt w8cA

/-- `C = max(1, M_m) C₃` (blueprint `bpW:w8:const`). -/
def w8C (m : ℝ) : ℝ := max 1 (reconWaveBound m) * w8C3

/-- `η(r) = 2^{33/64} E₇ r^{1/32}` (blueprint `bpW:w8:const`). -/
def w8Eta (m : ℝ) (hm : 0 < m) (u : W8UpstreamConsts) (r : ℝ) : ℝ :=
  (2 : ℝ) ^ (33 / 64 : ℝ) * w8E7 m hm u * r ^ (1 / 32 : ℝ)

/-! ### Shells (`bpW:w8:shells`) -/

/-- `t_n = 2^{-n} t₀` (blueprint `bpW:w8:shells`; W7's `shellT` with `q = 1/2`). -/
def w8tn (t0 : ℝ) (n : ℕ) : ℝ := shellT (1 / 2) t0 n

/-- `R_n = (0, t_n)² ∖ (0, t_{n+1})²` (blueprint `bpW:w8:shells`). -/
def w8Rn (t0 : ℝ) (n : ℕ) : Set (Fin 2 → ℝ) := shellSet (1 / 2) t0 n

/-- `α_n = t_n^{95/64}` (blueprint `bpW:w8:shells`). -/
def w8alpha (t0 : ℝ) (n : ℕ) : ℝ := w8tn t0 n ^ (95 / 64 : ℝ)

/-- `r_n = t_n^{3/4}` (blueprint `bpW:w8:shells`). -/
def w8rn (t0 : ℝ) (n : ℕ) : ℝ := w8tn t0 n ^ (3 / 4 : ℝ)

/-- `ρ_{ξ,n} = α_n/2` (blueprint `bpW:w8:shells`). -/
def w8rhoXi (t0 : ℝ) (n : ℕ) : ℝ := w8alpha t0 n / 2

/-- `ρ_n = (c_A (t_n + r_n²))^{1/2}` (blueprint `bpW:w8:shells`). -/
def w8rho (t0 : ℝ) (n : ℕ) : ℝ := Real.sqrt (w8cA * (w8tn t0 n + w8rn t0 n ^ 2))

/-- `ε^♯_n = E₃ t_n^{3/2}` (blueprint `bpW:w8:shells`). -/
def w8epsSharp (m : ℝ) (hm : 0 < m) (t0 : ℝ) (n : ℕ) : ℝ :=
  w8E3 m hm * w8tn t0 n ^ (3 / 2 : ℝ)

/-- `κ_n = ε^♯_n / (γ α_n)` (blueprint `bpW:w8:shells`). -/
def w8kappa (m : ℝ) (hm : 0 < m) (u : W8UpstreamConsts) (t0 : ℝ) (n : ℕ) : ℝ :=
  w8epsSharp m hm t0 n / (u.gam * w8alpha t0 n)

/-- `ε_{0,n} = κ_n^{4/3} γ₁ α̌_n`, `α̌_n = α_n^{48/47}` (blueprint `bpW:w8:shells`). -/
def w8eps0 (m : ℝ) (hm : 0 < m) (u : W8UpstreamConsts) (t0 : ℝ) (n : ℕ) : ℝ :=
  w8kappa m hm u t0 n ^ (4 / 3 : ℝ) * u.gam1 * alphaCheck (w8alpha t0 n)

/-- `α̂_n = α_n^{44/47}` (blueprint `bpW:w8:shells`). -/
def w8alphaHat (t0 : ℝ) (n : ℕ) : ℝ := alphaHat (w8alpha t0 n)

/-- The trimmed shell `Π_n = U_{-α_n} R_n = {ξ ∈ R_n : dist(ξ, ℝ² ∖ R_n) > α_n}`
(blueprint `bpW:w8:shells`). -/
def w8Pi (t0 : ℝ) (n : ℕ) : Set (Fin 2 → ℝ) :=
  {ξ | ξ ∈ w8Rn t0 n ∧ w8alpha t0 n < Metric.infDist ξ (w8Rn t0 n)ᶜ}

/-- `κ_n = (E₃/γ) t_n^{1/64}` for `t_n > 0` (blueprint `bpW:w8:shells`). -/
theorem w8kappa_eq (m : ℝ) (hm : 0 < m) (u : W8UpstreamConsts) {t0 : ℝ} (ht : 0 < t0) (n : ℕ) :
    w8kappa m hm u t0 n = w8E3 m hm / u.gam * w8tn t0 n ^ (1 / 64 : ℝ) := by
  have htn : 0 < w8tn t0 n := shellT_pos (by norm_num) ht n
  have h : w8tn t0 n ^ (3 / 2 : ℝ) = w8tn t0 n ^ (1 / 64 : ℝ) * w8alpha t0 n := by
    rw [w8alpha, ← Real.rpow_add htn]; norm_num
  have hα : 0 < w8alpha t0 n := Real.rpow_pos_of_pos htn _
  have hg := u.gam_pos
  rw [w8kappa, w8epsSharp, h]
  field_simp

end KAM.Wave

end
