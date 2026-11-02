/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.Cover

/-!
# HD 11964: the consumer glue (HD11964-LEMMAS, piece 3)

From kamx-hd-layer's per-cell bounds to the region bounds of `noCrossing_of_regionBounds`.

The layer's models live in the cell variables: `TFModel.bound_of_cell` bounds a function
`G θ x` at the points `x = cellMap c Mx u`, `|u_j| ≤ 1`, of each cell. Here:

* `cellMapC`: the layer's `PackedTF.cellMap` (the same body; `PackedTF` is not on this branch);
  `cellMapC_ofReal`: at real cell variables it is the cast of `AffineCell.map`.
* `bracket_bound_of_cellBounds`, `range_bound_of_cellBounds`: per-cell bounds on the layer's
  function, the cover (`CoversReps`), the link of that function to the chart rate (resp. `F - Λ_i`)
  on the representatives, and `F`'s rotation invariance give the bridge's `hη` (resp. `hG`).
* `noCrossing_of_cellBounds`: `noCrossing_of_regionBounds` with both discharged, per planet.

**Explicit premises.** The links (`hlink`) are discharged by whoever defines the layer's function
(the composed chart functions). `F`'s rotation invariance (`hFrot`) is open (AUDIT-HD11964-COVER-1).
The angles follow the layer's convention `θ = λ/2π` (`chartAngle`).
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real

namespace HD11964.Cover

/-- kamx-hd-layer's `PackedTF.cellMap` (the same body), over `ℂ`. -/
def cellMapC {d : ℕ} (c : Fin d → ℚ) (Mx : Fin d → Fin d → ℚ) (u : Fin d → ℂ) : Fin d → ℂ :=
  fun i => (c i : ℂ) + ∑ j, (Mx i j : ℂ) * u j

/-- The angles of a chart state in kamx-hd-layer's convention `θ = λ/2π`. -/
def chartAngle (w : Phase (2 + 2)) : Fin 2 → ℂ := fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ)

/-- **The two-line lemma**: at real cell variables, `cellMap` is the cast of `AffineCell.map`. -/
theorem cellMapC_ofReal (k : AffineCell) (u : Fin 6 → ℝ) :
    cellMapC k.c k.toMx (fun j => (u j : ℂ)) = fun i => ((k.map u i : ℝ) : ℂ) := by
  funext i
  rw [AffineCell.map_eq_cellMap]
  push_cast [cellMapC]
  rfl

/-- A representative in a cell: its cell coordinates are `cellMap` at real cell variables with
`|u_j| ≤ 1`. -/
theorem exists_cellMapC_of_mem_repSet {cells : List AffineCell} {d : ℝ} {w : Phase (2 + 2)}
    (hw : w ∈ repSet cells d) : ∃ k ∈ cells, ∃ u : Fin 6 → ℝ, (∀ j, |u j| ≤ 1) ∧
      (fun i => (cellCoord w i : ℂ)) = cellMapC k.c k.toMx (fun j => (u j : ℂ)) := by
  obtain ⟨-, k, hk, u, hu, hx⟩ := hw
  exact ⟨k, hk, u, hu, by rw [cellMapC_ofReal, hx]⟩

/-- **Bracket glue.** Per-cell bounds `‖G‖ ≤ η` on the layer's function (at real `θ`), the cover,
`G`'s link to the chart rate on the representatives, and `F`'s rotation invariance (`hFrot`, an
explicit premise) give the bridge's `hη` on `R(d)`. -/
theorem bracket_bound_of_cellBounds {F : Phase (2 + 2) → ℝ} {O : Set (Phase (2 + 2))}
    (hO : IsOpen O) (hOs : O ⊆ chartSafe nu) (hF : DifferentiableOn ℝ F O)
    (hFrot : ∀ θ, ∀ w ∈ O, chartRot θ w ∈ O ∧ F (chartRot θ w) = F w) {d : ℝ}
    (hRO : region d ⊆ O) {cells : List AffineCell} (hcov : CoversReps cells d)
    (G : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ) {η : ℝ}
    (hlink : ∀ w ∈ repSet cells d,
      fderiv ℝ F w (hamiltonianVectorField (liftChartHam nu mu) w) =
        (G (chartAngle w) (fun i => (cellCoord w i : ℂ))).re)
    (hcell : ∀ k ∈ cells, ∀ θ : Fin 2 → ℝ, ∀ u : Fin 6 → ℝ, (∀ j, |u j| ≤ 1) →
      ‖G (fun i => (θ i : ℂ)) (cellMapC k.c k.toMx (fun j => (u j : ℂ)))‖ ≤ η) :
    ∀ w ∈ region d, |fderiv ℝ F w (hamiltonianVectorField (liftChartHam nu mu) w)| ≤ η := by
  refine bracket_bound_of_rotation nu_pos mu hO hOs hF hFrot hRO
    (hRS_of_coversReps cells d hcov) ?_
  intro w hw
  obtain ⟨k, hk, u, hu, hx⟩ := exists_cellMapC_of_mem_repSet hw
  rw [hlink w hw, hx]
  exact (Complex.abs_re_le_norm _).trans (hcell k hk (fun i => fast w.1 i / (2 * π)) u hu)

/-- **Range glue.** The same for `lo ≤ F - Λ_i ≤ hi`, from centred per-cell bounds
`‖G - c₀‖ ≤ η`: `lo = c₀ - η`, `hi = c₀ + η`. -/
theorem range_bound_of_cellBounds {F : Phase (2 + 2) → ℝ} {O : Set (Phase (2 + 2))}
    (hFrot : ∀ θ, ∀ w ∈ O, F (chartRot θ w) = F w) {d : ℝ} (hRO : region d ⊆ O)
    {cells : List AffineCell} (hcov : CoversReps cells d) (i : Fin 2)
    (G : (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ) {c₀ η : ℝ}
    (hlink : ∀ w ∈ repSet cells d,
      F w - fast w.2 i = (G (chartAngle w) (fun j => (cellCoord w j : ℂ))).re)
    (hcell : ∀ k ∈ cells, ∀ θ : Fin 2 → ℝ, ∀ u : Fin 6 → ℝ, (∀ j, |u j| ≤ 1) →
      ‖G (fun i => (θ i : ℂ)) (cellMapC k.c k.toMx (fun j => (u j : ℂ))) - c₀‖ ≤ η) :
    ∀ w ∈ region d, c₀ - η ≤ F w - fast w.2 i ∧ F w - fast w.2 i ≤ c₀ + η := by
  refine range_bound_of_rotation hFrot hRO (hRS_of_coversReps cells d hcov) i ?_
  intro w hw
  obtain ⟨k, hk, u, hu, hx⟩ := exists_cellMapC_of_mem_repSet hw
  have hb := hcell k hk (fun i => fast w.1 i / (2 * π)) u hu
  have hre := (Complex.abs_re_le_norm _).trans hb
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  have e : F w - fast w.2 i =
      (G (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ))
        (cellMapC k.c k.toMx (fun j => (u j : ℂ)))).re := by
    rw [hlink w hw, hx]
    rfl
  rw [e]
  constructor <;> linarith [(abs_le.mp hre).1, (abs_le.mp hre).2]

/-- **The assembled statement**: `noCrossing_of_regionBounds` with its two region hypotheses
discharged, per planet `i`, by the per-cell bounds on the layer's functions `G i` (the rate) and
`Gr i` (`F_i - Λ_i`), centred at `(lo_i + hi_i)/2` with radius `(hi_i - lo_i)/2`. The links and
`F`'s rotation invariance are explicit premises. -/
theorem noCrossing_of_cellBounds :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      ∀ (D : DriftData 2), D.ok = true → (D.r : ℝ) = rTube →
      ∀ (F : Fin 2 → Phase (2 + 2) → ℝ) (O : Set (Phase (2 + 2))), IsOpen O →
        region D.d ⊆ O → O ⊆ chartSafe nu → (∀ i, DifferentiableOn ℝ (F i) O) →
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
          (((D.lo i + D.hi i) / 2 : ℚ) : ℝ)‖ ≤ (((D.hi i - D.lo i) / 2 : ℚ) : ℝ)) →
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
              dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) := by
  obtain ⟨dS, dP, hdS, hdP, hmain⟩ := noCrossing_of_regionBounds
  refine ⟨dS, dP, hdS, hdP, fun D hD hr F O hO hRO hOs hF hFrot cells hcov G Gr hG hGr hcG hcGr =>
    hmain D hD hr F O hO hRO hF (fun i => ?_) (fun i => ?_)⟩
  · exact bracket_bound_of_cellBounds hO hOs (hF i) (hFrot i) hRO hcov (G i) (hG i) (hcG i)
  · intro w hw
    have h := range_bound_of_cellBounds (fun θ w hw => (hFrot i θ w hw).2) hRO hcov i (Gr i)
      (hGr i) (hcGr i) w hw
    have e1 : ((((D.lo i + D.hi i) / 2 : ℚ) : ℝ) - (((D.hi i - D.lo i) / 2 : ℚ) : ℝ)) =
        (D.lo i : ℝ) := by push_cast; ring
    have e2 : ((((D.lo i + D.hi i) / 2 : ℚ) : ℝ) + (((D.hi i - D.lo i) / 2 : ℚ) : ℝ)) =
        (D.hi i : ℝ) := by push_cast; ring
    rw [e1, e2] at h
    exact h

end HD11964.Cover

end
