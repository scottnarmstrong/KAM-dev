# Handoff HD11964-HOLO (phase 2: the complex extension of `P`, `G₂`; the tail of `T₃`)

Worker kamx-hd11964, branch `hd11964-p2`. Task from the orchestrator (2 November 2026), while the audit of CHI-FIX + ROT
(`f5fcee29..4cf155a0`) runs:
1. the obligation found in HD11964-ROT: the complex extension of `P` (and `G₂`) on the anisotropic strip —
   holomorphic, `1`-periodic in `θ`, equal to `P` at real points — which needs the moving Hamiltonian free of collisions
   on the complex strip. **Scope it first**: the exact Lean statements and the margin (min `Re` of the complexified
   distance² over the strip and the cells, numerically); then prove it if the margin is comfortable;
2. the tail of `T₃ = {D_i r₁, χ₁}`.

Statements first. Nothing pushed.

**Status: SCOPE AND STATEMENTS** (proofs to follow).

## (1) Scope: what has to be holomorphic

- **Only the mutual distance needs a branch.** On the chart domain,
  `liftChartHam = hProd + μ fMov(Ψ)` (`lpChart_hamiltonian`), so `P = μ fMov(Ψ)` with
  `fMov = |p_c + p_b|²/2 − ν_c ν_b/|q_c − q_b|`. Its continuation to complex angles is
  `P_C = μ((p_c + p_b)·(p_c + p_b)/2 − ν_c ν_b (d²)^{−1/2})`, with bilinear (not Hermitian) squares and
  `d² = (q_c − q_b)·(q_c − q_b)`. It is holomorphic where:
  - **(K)** the chart is holomorphic: the complex Kepler equation `F − v₀ sin F + v₁ cos F = λ` has a holomorphic
    solution. The core's `KAM.Kepler.KeplerData` / `keplerSol y₀` gives it under two inequalities:
    `|Im λ| + (|Re v₀| + |Re v₁|) sinh y₀ + (|Im v₀| + |Im v₁|) cosh y₀ < y₀` and `(|v₀| + |v₁|) cosh y₀ ≤ κ < 1`;
  - **(R)** the radicand `(1 − Γ/(2Λ))/Λ` has `Re > 0`; it is about 15 here;
  - **(D)** `Re d² > 0`. Then `(d²)^{−1/2}` is the principal branch, holomorphic and nonzero.
- **No collision with the star is possible.** Bilinearly, `q_j·q_j = a_j²(1 − v·c)²` holds for complex angles too
  (`k² + v·v = 1` and `c·c = 1`), and `|v·c| ≤ κ < 1`. Only the mutual distance can vanish.
- **LP's `poincareC` does not reach this domain.** It is holomorphic on `poincareNbhd`: `|Im λ| < 1/4` and
  `‖ξ‖, ‖η‖ < √Λ/16`, i.e. `e ≲ 0.06`. Here `e_c ≤ 0.65` and `|Im λ_b|` reaches `0.94`. Hence `planetChartC`:
  LP's formula with `keplerSol y₀` and a chosen strip `y₀`.

**The margins** (`scripts/holo_margin.py` on the plan's cells, and `scripts/holo_domain.py` on R(1/500); estimated,
floating point, sampled).
- `Re d²` is pluriharmonic in the angles, so its minimum over the strip is attained at `Im λ_j = ±2πρ_j`; that is
  where it is sampled.
- On the cells: 3⁶ cell points × 48² real angle pairs × 4 imaginary signs.

| domain | strip `(ρ_c, ρ_b)` | Kepler `c`: best slack (κ ≤ 0.95) | Kepler `b` | min `Re d²` |
|---|---|---:|---:|---:|
| cells, real slow variables | (0.03, 0.15) | 0.026 (cell 49, `e_c` 0.66) | ≥ 0.54 | 3.32 |
| cells, real slow variables | **(0.025, 0.15)** | **0.057** | ≥ 0.54 | **3.40** |
| cells, complex polydisc `‖u‖ ≤ 1` | (0.03, 0.15) | −0.020 (fails) | ≥ 0.10 | 2.63 |
| cells, complex polydisc `‖u‖ ≤ 1` | (0.025, 0.15) | 0.011 | ≥ 0.10 | 2.72 |
| R(1/500), `|η_c| ≤ 1/500` | (0.025, 0.15) | — | — | **3.30** |
| R(1/500), `|η_c| ≤ 1/500` | (0.025, 0.10) | — | — | 4.95 |
| ℓ¹ eccentricities `≤ (0.68, 0.17)`, any orientation, no AMD budget | (0.025, 0.15) | — | — | 0.19 |

**Reading.**
- **The strip.** I use `ρ = (0.025, 0.15)` rather than `(0.03, 0.15)`.
  - At `ρ_c = 0.03` the Kepler slack for planet `c` on the worst cell is 0.026; that is not comfortable.
  - At 0.025 it is 0.057.
  - The tails stay inside the budget at `(0.025, 0.15)`: HD11964-ROT measured `T_c ≤ 1.5e-7` and `T_b ≤ 1.6e-9`.
- **The domain.** The claimed real domain is `R(1/500)` with planet `c` rotation-reduced (`|η_c| ≤ 1/500`):
  - that is where the tails are consumed (the representatives);
  - the AMD budget `Γ_c + Γ_b ≤ 0.014` keeps `e_c` and `e_b` from being large together.

  Without the budget, the margin collapses to 0.19 (last row).
- **(D) is comfortable numerically: `min Re d² ≈ 3.3`, against `a_b² ≈ 10`.**
- **(D) is not comfortable with an elementary proof chain.**
  - The chain `Re d² ≥ Re(q_b·q_b) − |q_c·q_c| − 2‖q_c‖‖q_b‖`, with `y₀`-based bounds
    (`‖c‖ ≤ √cosh 2y₀`, `|v·c| ≤ ē cosh y₀`), fails by a factor of about 2. With the sampled sup norms in place of
    the bounds it gives ≥ 1.76.
  - The polar form (`q_c·q_b = r_c r_b cos(φ_c − φ_b)`) is worse.
  - The real margin comes from correlations the chain cannot see.
- **The complex polydisc in the cell variables is not comfortable** (Kepler slack ≤ 0.011, or negative). The tail
  theorems use the extension only at real slow variables, so the claim is made there. Cauchy estimates in the cell
  variables, which the layer needs, would use a thin complex neighbourhood of the real cell, not the unit polydisc.

**Recommendation for (D).**
- Certify `Re d² > 0` from the layer's certified model of `d²`: the enclosure `|d² − D| ≤ r_D` with `Re D − r_D > 0` on
  `stripA ρ` × the cell. This is the same data as its `sqrt`/`inv` witness of the pair potential.
- Lean then gets (1b) by a two-line lemma, and proves (1a) and (1c) analytically, with (1b) as a distinctly named
  premise.
- An analytic proof of (1b) would need a sharper argument than any I have found, or an interval subdivision in the
  kernel. It is not proposed.

**Constants** (all with margin):
- planet `c`, `y₀ = 4/5`, `ē_c = 0.68`: invariance `0.157 + 0.68 sinh 0.8 = 0.761 < 0.8`, and
  `0.68 cosh 0.8 = 0.909 ≤ κ_c = 0.95`;
- planet `b`, `y₀ = 13/10`, `ē_b = 0.18`: `0.942 + 0.18 sinh 1.3 = 1.248 < 1.3`, and `0.18 cosh 1.3 = 0.355 ≤ 0.5`.

## (2) Scope: the tail of `T₃ = {D_i r₁, χ₁}`

- **The coordinate formula** (`pb_eq_sum`) gives `|T₃| ≤ Σ_k |∂_{x_k} D_i r₁| |∂_{y_k} χ₁| + |∂_{y_k} D_i r₁| |∂_{x_k} χ₁|`.
- **Every first derivative of the tail is a tail.**
  - For an angle direction, `∂_{λ_j} Π_S = Π_S ∂_{λ_j}`, since `(∂_{λ_j} Q)^_k = i k_j Q̂_k` by integration by parts on
    the slice.
  - For a slow direction, differentiation under the integral sign.
  - With the symmetry of second derivatives, `D_v D_i (Q − Π_S Q) = D_i (D_v Q − Π_S D_v Q)`.
- **The bound.** `abs_dirDeriv_sub_projS_le_of_coeff` (HD11964-ROT) applies to `Q' = D_v P`, with coefficient bounds
  for `D_v P`. The layer gets them from the derivative of its model of `P`: exact on the polynomial part, Cauchy for
  the remainder. The isotropic or anisotropic cell forms supply them as before.
- **`χ₁`'s derivatives** are bounded by the generator's enclosure (2b of HD11964-ROT) and Cauchy. They are
  hypotheses `B_v` here.

## The statements (type-checked as `Prop`s; scratch `lake env lean`, exit 0)

The file is also at `~/kam-data/hd11964/lemmas/HoloDraft.lean`.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.TailAniso
public import KAM.Kepler.EquationComplex
public import KAM.Planetary.StrongAMD.PlanarDictionary

/-!
# DRAFT (HD11964-HOLO): statements of the complex extension of `P`, `G₂`, and of the tail of `T₃`

Statements only, as `Prop`s (type-checked, no proofs), for the handoff.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real ContDiff

namespace HD11964.Cover

/-! ## (1) Definitions -/

/-- One planet's complexified Poincaré chart (`κ = 1`) with the Kepler strip `y₀`: positions and
momenta at the complex mean longitude `lam` and slow variables `(Λ, ξ, η)`. It is LP's
`poincareC m 1` with `KAM.Kepler.keplerSol y₀` in place of `keplerLongC` (whose strip is `1`). -/
def planetChartC (y₀ m : ℝ) (lam Λ ξ η : ℂ) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  let Γ := (ξ ^ 2 + η ^ 2) / 2
  let k := 1 - Γ / Λ
  let v : Fin 2 → ℂ := ((1 - Γ / (2 * Λ)) / Λ) ^ (1 / 2 : ℂ) • ![ξ, η]
  let F := KAM.Kepler.keplerSol y₀ (v 0) (v 1) lam
  let c : Fin 2 → ℂ := ![Complex.cos F, Complex.sin F]
  let vc := v 0 * c 0 + v 1 * c 1
  ((Λ ^ 2 / ((m ^ 2 : ℝ) : ℂ)) • (k • c - v + (vc / (1 + k)) • v),
    (((m ^ 2 : ℝ) : ℂ) / (Λ * (1 - vc))) • (![-c 1, c 0] - (vc / (1 + k)) • ![-v 1, v 0]))

/-- Planet `j`'s complexified chart at the real chart state `w` with complex angles `θ = λ/2π`. -/
def chartQPC (y : Fin 2 → ℝ) (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) (j : Fin 2) :
    (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  planetChartC (y j) (nu j) (2 * π * θ j) (fast w.2 j) (slow w.1 j) (slow w.2 j)

/-- **The complexified mutual distance squared** (bilinear, not Hermitian):
`d² = (q_c - q_b)·(q_c - q_b)`. -/
def distSqC (y : Fin 2 → ℝ) (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) : ℂ :=
  ((chartQPC y w θ 0).1 0 - (chartQPC y w θ 1).1 0) ^ 2 +
    ((chartQPC y w θ 0).1 1 - (chartQPC y w θ 1).1 1) ^ 2

/-- **The complexified perturbation** `P_C = μ (|p_c + p_b|²/2 - ν_c ν_b (d²)^{-1/2})` (bilinear
squares, principal branch). -/
def chartPertC (y : Fin 2 → ℝ) (w : Phase (2 + 2)) (θ : Fin 2 → ℂ) : ℂ :=
  (mu : ℂ) * ((((chartQPC y w θ 0).2 0 + (chartQPC y w θ 1).2 0) ^ 2 +
    ((chartQPC y w θ 0).2 1 + (chartQPC y w θ 1).2 1) ^ 2) / 2 -
    (nu 0 : ℂ) * (nu 1 : ℂ) * distSqC y w θ ^ (-(1 / 2 : ℂ)))

/-- The strip widths (`θ = λ/2π`): `ρ = (1/40, 3/20)`. -/
def rhoHolo : Fin 2 → ℝ := ![1 / 40, 3 / 20]

/-- The Kepler strips `y₀ = (4/5, 13/10)` and contraction constants `κ = (19/20, 1/2)`. -/
def yHolo : Fin 2 → ℝ := ![4 / 5, 13 / 10]

def kappaHolo : Fin 2 → ℝ := ![19 / 20, 1 / 2]

/-- The bounds on the ℓ¹ eccentricity vectors `|v₀| + |v₁|` that the proof derives on `holoDomHD`:
`ē = (0.68, 0.18)` (sampled maxima 0.665, 0.176). -/
def eBar : Fin 2 → ℝ := ![17 / 25, 9 / 50]

/-- **The real chart states of the claim**: the certificate region `R(1/500)` with planet `c`
rotation-reduced, `|η_c| ≤ 1/500` (every representative of the fitted plan's cover is in it; the
plan's cells have `|η_c| ≤ 0.002`). -/
def holoDomHD : Set (Phase (2 + 2)) := {w | w ∈ region (1 / 500) ∧ |slow w.2 0| ≤ 1 / 500}

/-! ## (1) Statements -/

/-- (1a) **The Kepler contraction on the strip** (`KAM.Kepler.KeplerData`, coefficients constant in
`λ`): for `w ∈ holoDomHD` and each planet, `|Im λ| < 2πρ_j` lies in the parameter set of a
`KeplerData` with strip `y_j` and constant `κ_j`. -/
def KeplerDataHD : Prop :=
  ∀ (j : Fin 2), ∀ w ∈ holoDomHD,
    KAM.Kepler.KeplerData {lam : ℂ | |lam.im| < 2 * π * rhoHolo j}
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.1 j : ℝ) : ℂ))
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.2 j : ℝ) : ℂ))
      (fun lam => lam) (yHolo j) (kappaHolo j)

/-- (1b) **No complex collision**: on `holoDomHD` × `stripA ρ`, `Re d² > 0` (so `(d²)^{-1/2}` is the
principal branch, holomorphic and nonzero). -/
def NoComplexCollisionHD : Prop :=
  ∀ w ∈ holoDomHD, ∀ θ ∈ stripA rhoHolo, 0 < (distSqC yHolo w θ).re

/-- (1c) **The complex extension of `P`**: at every `w ∈ holoDomHD`, `θ ↦ P_C(w, θ)` is holomorphic
and `1`-periodic on `stripA ρ`, and equals `P(withAngles w (2πt))` at real `θ = t`. -/
def ChartPertExtHD : Prop :=
  ∀ w ∈ holoDomHD,
    DifferentiableOn ℂ (chartPertC yHolo w) (stripA rhoHolo) ∧
    (∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA rhoHolo →
      chartPertC yHolo w (θ + Pi.single j 1) = chartPertC yHolo w θ) ∧
    ∀ t : Fin 2 → ℝ,
      chartPertC yHolo w (fun j => (t j : ℂ)) = (chartPert nu mu (withAngles w fun j => 2 * π * t j) : ℂ)

/-- (1d) **The complex extension of `G₂`** (existence form, what `tails_HD_of_cell_aniso` consumes
per point): the slice of `G₂ = {P - ½ Π_S P, χ₁}` at `w ∈ holoDomHD` extends holomorphically
and `1`-periodically to `stripA ρ`. -/
def G2ExtHD : Prop :=
  ∀ w ∈ holoDomHD, ∃ Gc : (Fin 2 → ℂ) → ℂ,
    DifferentiableOn ℂ Gc (stripA rhoHolo) ∧
    (∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA rhoHolo → Gc (θ + Pi.single j 1) = Gc θ) ∧
    ∀ t : Fin 2 → ℝ, Gc (fun j => (t j : ℂ)) = (G2HD (withAngles w fun j => 2 * π * t j) : ℂ)

/-! ## (2) The tail of `T₃ = {D_i r₁, χ₁}` -/

/-- (2a) **The bracket by coordinates**:
`|{a, b}| ≤ Σ_k |∂_{x_k} a| |∂_{y_k} b| + |∂_{y_k} a| |∂_{x_k} b|`. -/
def AbsPbLe : Prop :=
  ∀ (d : ℕ) (a b : Phase d → ℝ) (w : Phase d),
    |pb a b w| ≤ ∑ k, (|fderiv ℝ a w (Pi.single k 1, 0)| * |fderiv ℝ b w (0, Pi.single k 1)| +
      |fderiv ℝ a w (0, Pi.single k 1)| * |fderiv ℝ b w (Pi.single k 1, 0)|)

/-- A direction that does not move the fast angles. -/
def IsSlowDir (v : Phase (2 + 2)) : Prop := ∀ j : Fin 2, v.1 (Fin.castAdd 2 j) = 0

/-- (2b) **Slow derivatives commute with the Fourier coefficients and with `Π_S`** (differentiation
under the integral). -/
def SlowDerivComm : Prop :=
  ∀ (U : Set (Phase (2 + 2))) (Q : Phase (2 + 2) → ℝ) (S : Finset (Fin 2 → ℤ)) (v : Phase (2 + 2)),
    IsOpen U → IsAngleSaturated U → ContDiffOn ℝ ∞ Q U → IsSlowDir v → ∀ w ∈ U,
      (∀ k, chartCoeff (dirDeriv v Q) k w = fderiv ℝ (fun y => chartCoeff Q k y) w v) ∧
      dirDeriv v (projS S Q) w = projS S (dirDeriv v Q) w

/-- (2c) **Angle derivatives commute with `Π_S`**: `(∂_{λ_j} Q)^_k = i k_j Q̂_k` for `Q` periodic in
the angles, so `∂_{λ_j} Π_S Q = Π_S ∂_{λ_j} Q`. -/
def AngleDerivComm : Prop :=
  ∀ (U : Set (Phase (2 + 2))) (Q : Phase (2 + 2) → ℝ) (S : Finset (Fin 2 → ℤ)) (j : Fin 2),
    IsOpen U → IsAngleSaturated U → ContDiffOn ℝ ∞ Q U → IsAnglePeriodicOn U Q → ∀ w ∈ U,
      (∀ k, chartCoeff (dirDeriv (angleDir (Fin.castAdd 2 j)) Q) k w =
        Complex.I * (k j : ℂ) * chartCoeff Q k w) ∧
      dirDeriv (angleDir (Fin.castAdd 2 j)) (projS S Q) w =
        projS S (dirDeriv (angleDir (Fin.castAdd 2 j)) Q) w

/-- (2d) **Every first derivative of a tail is a tail**: for a slow or angle direction `v`,
`D_v D_i (Q - Π_S Q) = D_i (D_v Q - Π_S D_v Q)` at points of `U`. -/
def TailDerivComm : Prop :=
  ∀ (U : Set (Phase (2 + 2))) (Q : Phase (2 + 2) → ℝ) (S : Finset (Fin 2 → ℤ)) (i : Fin 2)
    (v : Phase (2 + 2)), IsOpen U → IsAngleSaturated U → ContDiffOn ℝ ∞ Q U →
    IsAnglePeriodicOn U Q → (IsSlowDir v ∨ ∃ j, v = angleDir (Fin.castAdd 2 j)) → ∀ w ∈ U,
      dirDeriv v (dirDeriv (angleDir (Fin.castAdd 2 i)) (fun y => Q y - projS S Q y)) w =
        dirDeriv (angleDir (Fin.castAdd 2 i)) (fun y => dirDeriv v Q y - projS S (dirDeriv v Q) y) w

/-- (2e) **The tail of `T₃` at a point**, from bounds on the Fourier coefficients of the eight
first derivatives `D_v P` (`v` the coordinate directions `(e_k, 0)`, `(0, e_k)`) and on the first
derivatives of `χ₁`: `|{D_i r₁, χ₁}(w)| ≤ Σ_k A_{(e_k,0)} B_{(0,e_k)} + A_{(0,e_k)} B_{(e_k,0)}`, with
`A_v = Σ_{T_v \ S} |κ_i| |a^v_κ| + Σ_{κ ∉ S} |κ_i| d^v_κ` (the bound of
`abs_dirDeriv_sub_projS_le_of_coeff` for `D_v P`). -/
def T3TailBound : Prop :=
  ∀ (ν : Fin 2 → ℝ) (U : Set (Phase (2 + 2))) (S : Finset (Fin 2 → ℤ)) (P : Phase (2 + 2) → ℝ)
    (i : Fin 2) (w : Phase (2 + 2)) (T : Phase (2 + 2) → Finset (Fin 2 → ℤ))
    (a : Phase (2 + 2) → (Fin 2 → ℤ) → ℂ) (d : Phase (2 + 2) → (Fin 2 → ℤ) → ℝ)
    (B : Phase (2 + 2) → ℝ),
    IsOpen U → IsAngleSaturated U → U ⊆ poincareProdDom 2 → ContDiffOn ℝ ∞ P U →
    IsAnglePeriodicOn U P → IsModeSet S (keplerFreq ν) U → w ∈ U →
    (∀ v, ∀ κ, ‖chartCoeff (dirDeriv v P) κ w - (if κ ∈ T v then a v κ else 0)‖ ≤ d v κ) →
    (∀ v, Summable fun κ : Fin 2 → ℤ => |(κ i : ℝ)| * d v κ) →
    (∀ v, |dirDeriv v (chiStar S (keplerFreq ν) P) w| ≤ B v) →
    let A : Phase (2 + 2) → ℝ := fun v =>
      ∑ κ ∈ T v \ S, |(κ i : ℝ)| * ‖a v κ‖ + ∑' κ, if κ ∈ S then 0 else |(κ i : ℝ)| * d v κ
    |pb (dirDeriv (angleDir (Fin.castAdd 2 i)) (residual₁ (hProd 1 ν) P (chiStar S (keplerFreq ν) P)))
        (chiStar S (keplerFreq ν) P) w| ≤
      ∑ k, (A (Pi.single k 1, 0) * B (0, Pi.single k 1) + A (0, Pi.single k 1) * B (Pi.single k 1, 0))

end HD11964.Cover

end
```
