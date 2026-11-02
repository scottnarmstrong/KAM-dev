# Handoff HD11964-LEMMAS (phase 2, "build pieces only": the Lean side of the cell check)

Worker kamx-hd11964, branch `hd11964-p2`. Owner decision (Scott, 2 November 2026), relayed by the orchestrator:
HD 11964 = "Build pieces only" (no full run; a 2-cell rehearsal at the end). My Lean pieces:
1. the Cauchy bound for the slow-variable derivatives the cell check needs;
2. a certified remainder for the exact generator `χ* = Π_S P/(ik·ω)` (polynomial centre plus remainder, as the
   producer's data);
3. the link from kamx-hd-layer's per-cell model `F θ x` to the chart function in `noCrossing_of_regionBounds`
   (consumer glue, with the `ℂ` `cellMap` two-line lemma).

New files, additive; **statements in the handoff first** (this section). Nothing pushed.

STATUS: STATEMENTS (proofs to follow in `applications/hd11964/HD11964/{CellCauchy,Generator,Glue}.lean`)

## Design

**Where.** Three new modules of the application package, importing `HD11964.Cover`:
- `CellCauchy` (piece 1);
- `Generator` (piece 2);
- `Glue` (piece 3).

No core file changes.

**`PackedTF` is not on this branch** (only on `hd-layer`, not on `main`). So the glue mirrors the two `PackedTF`
definitions it needs, with the same bodies:
- `polyDiscC d s = {u | ∀ j, ‖u j‖ ≤ s}` mirrors `PackedTF.polyDisc`;
- `cellMapC c Mx u = fun i => c i + Σ_j Mx i j · u j` mirrors `PackedTF.cellMap`.

Both identify by `rfl` once the branches meet. `complexStrip` (frozen) is shared.

**(1) Cauchy.**
- On the polydisc, a function bounded by `r` on radius `s₀` has `j`-th partial derivatives bounded by `r/(s₀ − s)`
  on radius `s` (1a). Applied to a model's remainder `f − p`, it bounds `∂_j f − ∂_j p` (1b), the remainder of the
  derivative of a model, which the bracket terms need.
- The chain rule through the inverse cell map (`AffineCell.coord`, matrix `invMx`) turns cell-variable partials
  into the physical slow derivatives `∂/∂Λ_i`, `∂/∂ξ_i`, `∂/∂η_i` (1c).

**(2) The generator.**
- `chiStar S ω P` is the exact `χ* = Re Σ_{k∈S} P̂_k/(i k·ω(Λ)) e^{i k·λ}` on the chart. It is global, with Fourier
  coefficients over the fast angles. It is the Lean `χ₁` (with `P`) and `χ₂` (with `G₂`) of `approxIntegral₂`.
- `genChi S om Pc` is its per-cell form in kamx-hd-layer's variables `(θ = λ/2π, u)`, for a complex function `Pc`
  on the strip × polydisc.
- (2a) The certified remainder. Given models of `Pc` (centre `p`, remainder `r_P`) and of `1/(i k·ω)` (polynomial
  `q_k`, remainder `ε_k`, bound `B_k`), the producer's centre `c` is within
  `Σ_{k∈S} e^{2πρ|k|₁} (r_P B_k + ‖p_k‖₁ ε_k + ‖p_k q_k − c_k‖₁)`.
  - Every quantity is either data or an ℓ¹ norm of rational polynomials, computable by the kernel.
  - The proof: the Fourier coefficient of `Pc − p` is bounded by `r_P` (real `θ` lies in the strip, and the torus
    has volume 1); the characters are orthogonal; `|e(k·θ)| ≤ e^{2πρ|k|₁}` on the strip; and a three-term split.
- (2b) The link. If `Pc` agrees with `P` at real points of the cell and `om` with `ω(Λ)`, then
  `chiStar = Re genChi` there.

**(3) Glue.**
- (3a) The two-line `cellMap` lemma.
- (3b) Bracket and (3c) range. From:
  - the per-cell bounds kamx-hd-layer's `TFModel.bound_of_cell` gives, taken at real `θ`;
  - the cover (`CoversReps`, HD11964-COVERLEMMA);
  - the link of the layer's function `G` to the chart rate (resp. `F − Λ_i`) on the representatives;
  - `F`'s rotation invariance `hFrot`, **an explicit premise; open, as ruled**;

  they give the bridge's `hη` (resp. `hG`) on `R(d)`.
- (3d) The assembled statement: `noCrossing_of_regionBounds` with both region hypotheses discharged per planet.
- The links are hypotheses, with distinct names. They are discharged by whoever defines `G`: the composed chart
  functions of the layer.

## The statements (type-checked as `Prop`s; scratch `lake env lean`, exit 0)

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.Cover

/-!
# DRAFT (HD11964-LEMMAS): statements of the three Lean pieces

Statements only, as `Prop`s (type-checked, no proofs), for the handoff.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real

namespace HD11964.Cover

/-! ## (1) The Cauchy bound for the slow-variable derivatives -/

/-- The closed polydisc `{u | ∀ j, ‖u j‖ ≤ s}` (kamx-hd-layer's `PackedTF.polyDisc`). -/
def polyDiscC (d : ℕ) (s : ℝ) : Set (Fin d → ℂ) := {u | ∀ j, ‖u j‖ ≤ s}

/-- (1a) **Cauchy bound for a coordinate derivative on the polydisc**: a function complex
differentiable on the closed polydisc of radius `s₀` and bounded there by `r` has its `j`-th
partial derivative bounded by `r / (s₀ - s)` on the polydisc of radius `s < s₀`. -/
def CauchyPolyDisc : Prop :=
  ∀ (d : ℕ) (g : (Fin d → ℂ) → ℂ) (s₀ s r : ℝ), DifferentiableOn ℂ g (polyDiscC d s₀) →
    (∀ u ∈ polyDiscC d s₀, ‖g u‖ ≤ r) → s < s₀ → ∀ u ∈ polyDiscC d s, ∀ j : Fin d,
      ‖fderiv ℂ g u (Pi.single j 1)‖ ≤ r / (s₀ - s)

/-- (1b) **The model form**: if `f` and the model `p` are complex differentiable on the polydisc of
radius `s₀` and `‖f - p‖ ≤ r` there, the partial derivatives differ by at most `r / (s₀ - s)` on
the polydisc of radius `s` (the derivative of a model's remainder). -/
def CauchyModel : Prop :=
  ∀ (d : ℕ) (f p : (Fin d → ℂ) → ℂ) (s₀ s r : ℝ), DifferentiableOn ℂ f (polyDiscC d s₀) →
    DifferentiableOn ℂ p (polyDiscC d s₀) → (∀ u ∈ polyDiscC d s₀, ‖f u - p u‖ ≤ r) → s < s₀ →
    ∀ u ∈ polyDiscC d s, ∀ j : Fin d,
      ‖fderiv ℂ f u (Pi.single j 1) - fderiv ℂ p u (Pi.single j 1)‖ ≤ r / (s₀ - s)

/-- The cell variables of a real point `x` (the inverse of `AffineCell.map` for a well-formed
cell). -/
def AffineCell.coord (k : AffineCell) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![(x 0 - k.c 0) / k.h 0, (x 1 - k.c 1) / k.h 1, (x 2 - k.c 2) / k.h 2,
    (x 3 - k.c 3) / k.h 3, (k.a * (x 4 - k.c 4) + k.b * (x 5 - k.c 5)) / k.h 4,
    (-k.b * (x 4 - k.c 4) + k.a * (x 5 - k.c 5)) / k.h 5]

/-- `∂u_j/∂x_i`, the inverse cell matrix (row `j`, column `i`). -/
def AffineCell.invMx (k : AffineCell) : Fin 6 → Fin 6 → ℚ :=
  ![![1 / k.h 0, 0, 0, 0, 0, 0], ![0, 1 / k.h 1, 0, 0, 0, 0], ![0, 0, 1 / k.h 2, 0, 0, 0],
    ![0, 0, 0, 1 / k.h 3, 0, 0], ![0, 0, 0, 0, k.a / k.h 4, k.b / k.h 4],
    ![0, 0, 0, 0, -k.b / k.h 5, k.a / k.h 5]]

/-- (1c) **The physical slow derivatives**: the derivative of `x ↦ g (u(x))` along the physical
coordinate `x_i` (`Λ_c, Λ_b, ξ_c, η_c, ξ_b, η_b`) is bounded by `Σ_j |∂u_j/∂x_i| B_j` when the
cell-variable partials of `g` are bounded by `B_j`. -/
def CauchyPhysical : Prop :=
  ∀ (k : AffineCell) (g : (Fin 6 → ℂ) → ℂ) (x : Fin 6 → ℝ),
    DifferentiableAt ℂ g (fun j => (k.coord x j : ℂ)) → ∀ B : Fin 6 → ℝ,
    (∀ j, ‖fderiv ℂ g (fun j => (k.coord x j : ℂ)) (Pi.single j 1)‖ ≤ B j) → ∀ i : Fin 6,
      ‖fderiv ℝ (fun y : Fin 6 → ℝ => g (fun j => (k.coord y j : ℂ))) x (Pi.single i 1)‖ ≤
        ∑ j, |(k.invMx j i : ℝ)| * B j

/-! ## (2) The exact generator `χ* = Π_S P / (i k·ω)` and its certified remainder -/

/-- The character `e(k·θ) = exp (2πi k·θ)` (kamx-hd-layer's convention `θ = λ/2π`). -/
def charE (k : Fin 2 → ℤ) (θ : Fin 2 → ℂ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ i, (k i : ℂ) * θ i)

/-- The Fourier coefficient in `θ` over the real torus `[0, 1]²`, at the cell variables `u`. -/
def fourierCoeff2 (P : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ) (k : Fin 2 → ℤ) (u : Fin 6 → ℂ) : ℂ :=
  ∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1,
    P ![(t₀ : ℂ), (t₁ : ℂ)] u * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)]

/-- **The generator in the cell variables**: `χ(θ, u) = Σ_{k ∈ S} P̂_k(u) / (i k·ω(u)) e(k·θ)`,
`om u` the frequency vector at the cell variables `u`. -/
def genChi (S : Finset (Fin 2 → ℤ)) (om : (Fin 6 → ℂ) → Fin 2 → ℂ)
    (P : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ) (θ : Fin 2 → ℂ) (u : Fin 6 → ℂ) : ℂ :=
  ∑ k ∈ S, fourierCoeff2 P k u * (Complex.I * ∑ i, (k i : ℂ) * om u i)⁻¹ * charE k θ

/-- A Taylor × Fourier polynomial: finitely many modes, each with a polynomial coefficient in the
cell variables (the producer's data). -/
abbrev TFPoly := (Fin 2 → ℤ) →₀ MvPolynomial (Fin 6) ℂ

/-- Its value. -/
def TFPoly.eval (p : TFPoly) (θ : Fin 2 → ℂ) (u : Fin 6 → ℂ) : ℂ :=
  p.sum fun k q => MvPolynomial.eval u q * charE k θ

/-- The ℓ¹ norm of a polynomial's coefficients (its bound on the unit polydisc). -/
def l1 (q : MvPolynomial (Fin 6) ℂ) : ℝ := ∑ m ∈ q.support, ‖q.coeff m‖

/-- (2a) **The certified remainder of the generator.** Given
* a model of `P`: centre `p`, remainder `r_P` on the strip of width `ρ` times the unit polydisc,
  with `P` continuous in real `θ`;
* for each `k ∈ S`, a model of `1/(i k·ω(u))`: polynomial `q k`, remainder `ε k`, bound `B k`;
* the producer's centre `c`, supported on `S`;
the generator is the centre up to an explicit remainder: the sum over `S` of
`e^{2πρ|k|₁} (r_P B_k + ‖p_k‖₁ ε_k + ‖p_k q_k - c_k‖₁)`. -/
def GenChiModel : Prop :=
  ∀ (S : Finset (Fin 2 → ℤ)) (om : (Fin 6 → ℂ) → Fin 2 → ℂ) (P : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ)
    (ρ rP : ℝ) (p c : TFPoly) (q : (Fin 2 → ℤ) → MvPolynomial (Fin 6) ℂ) (ε B : (Fin 2 → ℤ) → ℝ),
    0 < ρ → (∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖P θ u - p.eval θ u‖ ≤ rP) →
    (∀ u ∈ polyDiscC 6 1, Continuous fun t : Fin 2 → ℝ => P (fun i => (t i : ℂ)) u) →
    (∀ k ∈ S, ∀ u ∈ polyDiscC 6 1,
      ‖(Complex.I * ∑ i, (k i : ℂ) * om u i)⁻¹ - MvPolynomial.eval u (q k)‖ ≤ ε k) →
    (∀ k ∈ S, ∀ u ∈ polyDiscC 6 1, ‖(Complex.I * ∑ i, (k i : ℂ) * om u i)⁻¹‖ ≤ B k) →
    (↑c.support ⊆ (S : Set (Fin 2 → ℤ))) →
    ∀ θ ∈ complexStrip 2 ρ, ∀ u ∈ polyDiscC 6 1, ‖genChi S om P θ u - c.eval θ u‖ ≤
      ∑ k ∈ S, Real.exp (2 * π * ρ * ∑ i, |(k i : ℝ)|) *
        (rP * B k + l1 (p k) * ε k + l1 (p k * q k - c k))

/-- The chart state `w` with its fast angles replaced by `λ`. -/
def withAngles (w : Phase (2 + 2)) (lam : Fin 2 → ℝ) : Phase (2 + 2) :=
  assemble (fast w.2) lam (slow w.2) (slow w.1)

/-- The Fourier coefficient of a chart function in the fast angles `λ = 2πt`, at the slow
variables and actions of `w`. -/
def chartCoeff (P : Phase (2 + 2) → ℝ) (k : Fin 2 → ℤ) (w : Phase (2 + 2)) : ℂ :=
  ∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1,
    (P (withAngles w ![2 * π * t₀, 2 * π * t₁]) : ℂ) * charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)]

/-- **The exact generator on the chart**: `χ*(w) = Re Σ_{k ∈ S} P̂_k / (i k·ω(Λ)) e^{i k·λ}`, a
global function (the Lean `χ₁`, `χ₂` of `approxIntegral₂`, with `P` resp. `G₂`). -/
def chiStar (S : Finset (Fin 2 → ℤ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (P : Phase (2 + 2) → ℝ)
    (w : Phase (2 + 2)) : ℝ :=
  (∑ k ∈ S, chartCoeff P k w * (Complex.I * ∑ i, (k i : ℂ) * ω (fast w.2) i)⁻¹ *
    charE k (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ))).re

/-- (2b) **The link**: on a cell, if the complex function `Pc` agrees with `P` at real points and
`om` with `ω(Λ)`, the global generator is the real part of the cell generator. -/
def ChiStarEqGenChi : Prop :=
  ∀ (k : AffineCell) (S : Finset (Fin 2 → ℤ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (P : Phase (2 + 2) → ℝ) (Pc : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ) (om : (Fin 6 → ℂ) → Fin 2 → ℂ),
    (∀ w ∈ k.toSet, ∀ t : Fin 2 → ℝ,
      Pc (fun i => (t i : ℂ)) (fun j => (k.coord (cellCoord w) j : ℂ)) =
        (P (withAngles w (fun i => 2 * π * t i)) : ℂ)) →
    (∀ w ∈ k.toSet,
      om (fun j => (k.coord (cellCoord w) j : ℂ)) = fun i => (ω (fast w.2) i : ℂ)) →
    ∀ w ∈ k.toSet, chiStar S ω P w =
      (genChi S om Pc (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ))
        (fun j => (k.coord (cellCoord w) j : ℂ))).re

/-! ## (3) The consumer glue -/

/-- kamx-hd-layer's `PackedTF.cellMap` (the same body), over `ℂ`. -/
def cellMapC {d : ℕ} (c : Fin d → ℚ) (Mx : Fin d → Fin d → ℚ) (u : Fin d → ℂ) : Fin d → ℂ :=
  fun i => (c i : ℂ) + ∑ j, (Mx i j : ℂ) * u j

/-- The angles of a chart state in kamx-hd-layer's convention `θ = λ/2π`. -/
def chartAngle (w : Phase (2 + 2)) : Fin 2 → ℂ := fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ)

/-- (3a) **The two-line lemma**: at real cell variables, `cellMap` is the cast of
`AffineCell.map`. -/
def CellMapOfReal : Prop :=
  ∀ (k : AffineCell) (u : Fin 6 → ℝ),
    cellMapC k.c k.toMx (fun j => (u j : ℂ)) = fun i => ((k.map u i : ℝ) : ℂ)

/-- (3b) **Bracket glue**: per-cell bounds on the layer's function `G` (from
`TFModel.bound_of_cell` at real `θ`), the cover, `G`'s link to the chart rate, and `F`'s rotation
invariance (`hFrot`, an explicit premise, open) give the bridge's `hη` on `R(d)`. -/
def BracketGlue : Prop :=
  ∀ (F : Phase (2 + 2) → ℝ) (O : Set (Phase (2 + 2))), IsOpen O → O ⊆ chartSafe nu →
    DifferentiableOn ℝ F O → (∀ θ, ∀ w ∈ O, chartRot θ w ∈ O ∧ F (chartRot θ w) = F w) →
    ∀ (d : ℝ), region d ⊆ O → ∀ cells : List AffineCell, CoversReps cells d →
    ∀ (G : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ) (η : ℝ),
    (∀ w ∈ repSet cells d, fderiv ℝ F w (hamiltonianVectorField (liftChartHam nu mu) w) =
      (G (chartAngle w) (fun i => (cellCoord w i : ℂ))).re) →
    (∀ k ∈ cells, ∀ θ : Fin 2 → ℝ, ∀ u : Fin 6 → ℝ, (∀ j, |u j| ≤ 1) →
      ‖G (fun i => (θ i : ℂ)) (cellMapC k.c k.toMx (fun j => (u j : ℂ)))‖ ≤ η) →
    ∀ w ∈ region d, |fderiv ℝ F w (hamiltonianVectorField (liftChartHam nu mu) w)| ≤ η

/-- (3c) **Range glue**: the same for `lo ≤ F - Λ_i ≤ hi`, from a centred per-cell bound
`‖G - c₀‖ ≤ η` (so `lo = c₀ - η`, `hi = c₀ + η`). -/
def RangeGlue : Prop :=
  ∀ (F : Phase (2 + 2) → ℝ) (O : Set (Phase (2 + 2))),
    (∀ θ, ∀ w ∈ O, F (chartRot θ w) = F w) → ∀ (d : ℝ), region d ⊆ O →
    ∀ cells : List AffineCell, CoversReps cells d → ∀ (i : Fin 2)
    (G : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ) (c₀ η : ℝ),
    (∀ w ∈ repSet cells d,
      F w - fast w.2 i = (G (chartAngle w) (fun j => (cellCoord w j : ℂ))).re) →
    (∀ k ∈ cells, ∀ θ : Fin 2 → ℝ, ∀ u : Fin 6 → ℝ, (∀ j, |u j| ≤ 1) →
      ‖G (fun i => (θ i : ℂ)) (cellMapC k.c k.toMx (fun j => (u j : ℂ))) - c₀‖ ≤ η) →
    ∀ w ∈ region d, c₀ - η ≤ F w - fast w.2 i ∧ F w - fast w.2 i ≤ c₀ + η

/-- (3d) **The assembled statement**: `noCrossing_of_regionBounds` with its two region hypotheses
discharged by (3b) and (3c), per planet `i`. -/
def NoCrossingOfCells : Prop :=
  ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
    ∀ (D : DriftData 2), D.ok = true → (D.r : ℝ) = rTube →
    ∀ (F : Fin 2 → Phase (2 + 2) → ℝ) (O : Set (Phase (2 + 2))), IsOpen O → region D.d ⊆ O →
      O ⊆ chartSafe nu → (∀ i, DifferentiableOn ℝ (F i) O) →
      (∀ i θ, ∀ w ∈ O, chartRot θ w ∈ O ∧ F i (chartRot θ w) = F i w) →
    ∀ cells : List AffineCell, CoversReps cells D.d →
    ∀ (G Gr : Fin 2 → (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ),
    (∀ i, ∀ w ∈ repSet cells D.d,
      fderiv ℝ (F i) w (hamiltonianVectorField (liftChartHam nu mu) w) =
        (G i (chartAngle w) (fun j => (cellCoord w j : ℂ))).re) →
    (∀ i, ∀ w ∈ repSet cells D.d,
      F i w - fast w.2 i = (Gr i (chartAngle w) (fun j => (cellCoord w j : ℂ))).re) →
    (∀ i, ∀ k ∈ cells, ∀ θ : Fin 2 → ℝ, ∀ u : Fin 6 → ℝ, (∀ j, |u j| ≤ 1) →
      ‖G i (fun i => (θ i : ℂ)) (cellMapC k.c k.toMx (fun j => (u j : ℂ)))‖ ≤ D.eta i) →
    (∀ i, ∀ k ∈ cells, ∀ θ : Fin 2 → ℝ, ∀ u : Fin 6 → ℝ, (∀ j, |u j| ≤ 1) →
      ‖Gr i (fun i => (θ i : ℂ)) (cellMapC k.c k.toMx (fun j => (u j : ℂ))) -
        ((D.lo i + D.hi i : ℚ) / 2 : ℝ)‖ ≤ ((D.hi i - D.lo i : ℚ) / 2 : ℝ)) →
    ∀ z₀ : Phase (2 * 2), IsPhysicalState nu z₀ →
      (∀ i, lamLo i ≤ keplerAction nu z₀ i ∧ keplerAction nu z₀ i ≤ lamHi i) →
      strongAMD nu z₀ ≤ cBar → 0 < totalMomentum z₀ →
      ∃ z : ℝ → Phase (2 * 2), z 0 = z₀ ∧
        IsMovingSolutionOn nu mu (Icc (-(D.T : ℝ)) D.T) z ∧
        MovingUniqueOn nu mu (Icc (-(D.T : ℝ)) D.T) z ∧
        ∀ t ∈ Icc (-(D.T : ℝ)) D.T,
          (∀ i, dStar ≤
            keplerAxis nu (z t) i * (1 - planeLength (keplerEccVector nu (z t) i))) ∧
          (∀ a : AdjIdx 2, dPair ≤ keplerAxis nu (z t) a.upperIdx *
              (1 - planeLength (keplerEccVector nu (z t) a.upperIdx)) -
            keplerAxis nu (z t) a.1 * (1 + planeLength (keplerEccVector nu (z t) a.1))) ∧
          (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
          (∀ i j, i ≠ j →
            dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j))

end HD11964.Cover

end
```

## Proof plan

- **(1a)** The 1-variable slice `z ↦ g (update u j z)` is `DiffContOnCl` on the ball of radius `s₀ − s` around
  `u j`, which stays inside the polydisc of radius `s₀`. Then `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`
  applies, and the chain rule identifies `deriv` with `fderiv g u (Pi.single j 1)`.
  - (1b) is (1a) applied to `f − p`.
  - (1c) is the chain rule `fderiv (g ∘ ofReal ∘ coord) = (fderiv g).restrictScalars ℝ ∘ ofReal ∘ invMx`, then the
    triangle inequality.
- **(2a)**
  - The orthogonality of `charE` over `[0,1]²` uses iterated interval integrals and `∫₀¹ e^{2πinx} = [n = 0]`.
  - `‖∫∫ f‖ ≤ sup ‖f‖` holds on unit intervals.
  - The model's Fourier coefficients are `p_k(u)`.
  - Then the three-term split per `k`, and `‖eval u q‖ ≤ l1 q` on the unit polydisc.
- **(2b)** The integrands agree at real points: `cellCoord (withAngles w λ) = cellCoord w`.
- **(3a)** `funext` plus `Fin.sum_univ_six`, `push_cast`, `ring`.
- **(3b)–(3d)**
  - `bracket_bound_of_rotation` / `range_bound_of_rotation` with `R = region d` and `S = repSet cells d`;
  - `hRS_of_coversReps`;
  - membership in a cell gives `u` with `cellCoord w = k.map u`, and (3a) moves it to `cellMapC`;
  - `|Re z| ≤ ‖z‖`;
  - for (3d), `noCrossing_of_regionBounds`.
