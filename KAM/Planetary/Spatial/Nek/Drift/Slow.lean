/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Nek.Perturbation
public import KAM.Planetary.Spatial.ChartLift.Lift
public import KAM.Planetary.StrongAMD.Modulus

/-!
# The sharpened slow bound and the `V_j`-form of the solution premise

Source: `LP:MAIN L14 (477–483)` and `LP:MAIN L18 (595–597)`
as planned in `docs/tracks/LP/lp3/LP3-PLAN.md` §2.4 steps 4–6 and §2.5 (`k = n + n`), track LP,
non-frozen.

* `spatialNek_sharp_slow_bound`: on the stopped interval the strong AMD is below the local sharp
  level, `C(z u) < B(c_j) − 3δ/8` (the curvature step; the whole-ball bound `C ≤ B(I⁰) − δ/4` of
  `spLift_strongAMD_le_of_stopped` leaves no collar below `A_j`);
* `spatialNek_chart_amd_lt`: the same bound for the chart deficit `spatialChartAMD (w u)` along an
  aligned chart lift (`spatialChartAMD_eq_of_aligned`);
* `spatialNek_slow_mem_innerCore`: slow erosion for `2n` slow pairs (`stopped_slow_erosion` at
  `n + n`), landing in the inner core of `D_j`;
* `spatialNek_isSolutionOn_of_region`: the `V_j`-form of the solution premise: a curve in `V_j`
  solving the chart field of `spLiftChartHam ν μ` solves the field of `h(fast) + (B₀μ) Re P`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary KAM.Planetary.StrongAMD Set

variable {n : ℕ}

/-- **The sharpened slow bound** (`LP3-PLAN` §2.4 step 4; `LP:MAIN L14 (480)`). Let the lift data
have radius `r ≤ 4 r_g` over the shared tube, the initial action lie in the level set, and `c` be a
level-set centre within `η/2` of it. On the stopped interval the strong AMD satisfies
`C(z u) < B(c) − 3δ/8`. -/
theorem spatialNek_sharp_slow_bound {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg R r : ℝ}
    (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hg : IsSharedTube ν L δ rg) {z₀ : Phase (n * 3)}
    (hd : SpatialLiftData ν (sharedTube ν L δ rg) z₀ δ r) (hr4 : r ≤ 4 * rg)
    (hI0 : spatialActionVector ν z₀ ∈ strongLevelSet ν L δ) {c : Fin n → ℝ}
    (hc : c ∈ strongLevelSet ν L δ) (hcl : ‖spatialActionVector ν z₀ - c‖ < nekEta rg R / 2)
    {z : ℝ → Phase (n * 3)} {t : ℝ} (hs : SpatialStoppedOn ν z₀ δ r z t) {u : ℝ}
    (hu : u ∈ uIcc 0 t) :
    spatialStrongAMD ν (z u) < strongThreshold ν c - 3 * δ / 8 := by
  obtain ⟨-, hr, hC⟩ := hs u hu
  have h0 : spatialActionVector ν z₀ ∈ sharedTube ν L δ rg :=
    hd.ball _ (by simpa using hd.r_pos.le)
  have h1 : |strongThreshold ν (spatialActionVector ν (z u)) -
      strongThreshold ν (spatialActionVector ν z₀)| ≤ δ / 16 :=
    (abs_strongThreshold_sub_le_modulus hν hn hg.compact hg.subset_chamber (hd.ball _ hr.le) h0
      (r := 4 * rg) (hr.le.trans hr4)).trans hg.modulus
  have h2 := nekCell_threshold_bound_of_close hν hn hg hI0 hc hcl
  have h1' := (abs_le.1 h1).2
  have h2' := (abs_le.1 h2).2
  linarith

/-- The same bound for the chart deficit along an aligned chart lift: if `Ψ w = z u` and the
physical state is aligned (`L = |L| e₃`), then `spatialChartAMD w = C(z u)`. -/
theorem spatialNek_chart_amd_lt {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {w : Phase (n + (n + n))}
    (hw : w ∈ spLiftChartSafe ν) {z : Phase (n * 3)} (hp : spatialPoincareProd ν w = z)
    (hal : angularMomentum3 z = spaceLength (angularMomentum3 z) • e₃) {A : ℝ}
    (hC : spatialStrongAMD ν z < A) : spatialChartAMD w < A := by
  have hdom := spLiftChartSafe_subset_dom ν hw
  rw [← hp] at hal hC
  rw [spatialChartAMD_eq_of_aligned hν hdom hal]
  exact hC

/-- **Slow erosion for `2n` slow pairs** (`LP3-PLAN` §2.4 step 5): a chart point with deficit
`< B(c) − 3δ/8` has its slow pair in the max-norm erosion of `D_j` of radius `r`, provided
`√(2 A′) + √(2 · 2n) r < √(2 A_j)` (the gap `exists_spatialNekSlowGap`). -/
theorem spatialNek_slow_mem_innerCore {ν : Fin n → ℝ} {δ r : ℝ} {c : Fin n → ℝ} (hr0 : 0 ≤ r)
    (hgap : Real.sqrt (2 * (strongThreshold ν c - 3 * δ / 8)) +
        Real.sqrt (2 * ((n + n : ℕ) : ℝ)) * r < Real.sqrt (2 * nekCellLevel ν δ c))
    {w : Phase (n + (n + n))} (hw : spatialChartAMD w < strongThreshold ν c - 3 * δ / 8) :
    (slow (a := n) w.1, slow (a := n) w.2) ∈
      KAM.Nekhoroshev.innerCore (spatialNekCellSlow ν δ c) r :=
  stopped_slow_erosion (n := n + n) hr0 hgap hw

/-- **The `V_j`-form of the solution premise** (`LP3-PLAN` §2.3, §2.4 step 6): on the open region
`V_j` the field of `h(fast) + (B₀ μ) Re P` is that of `spLiftChartHam ν μ`, so a curve in `V_j`
with fast actions in `G` that solves the latter on `K` solves the former
(`IsSolutionOn`, frozen). The field identity is a hypothesis in the shape supplied by
`exists_spatialNekPerturbation`. -/
theorem spatialNek_isSolutionOn_of_region {ν : Fin n → ℝ} {δ rg R B0 μ : ℝ} {c : Fin n → ℝ}
    {P : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ}
    (hfield : ∀ w ∈ spatialNekCellRegion rg R ν δ c,
      DifferentiableAt ℝ (degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
        (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ)) w ∧
      KAM.hamiltonianVectorField
        (degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
          (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ)) w =
        KAM.hamiltonianVectorField (spLiftChartHam ν μ) w)
    {K : Set ℝ} {G : Set (Fin n → ℝ)} {w : ℝ → Phase (n + (n + n))}
    (hG : ∀ u ∈ K, fast (b := n + n) (w u).2 ∈ G)
    (hw : ∀ u ∈ K, w u ∈ spatialNekCellRegion rg R ν δ c ∧
      HasDerivAt w (KAM.hamiltonianVectorField (spLiftChartHam ν μ) (w u)) u) :
    KAM.Nekhoroshev.IsSolutionOn (degenerateHamiltonian
      (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
      (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) (B0 * μ))
      {I | fast (b := n + n) I ∈ G} K w := by
  intro u hu
  obtain ⟨hV, hder⟩ := hw u hu
  obtain ⟨hdiff, hfe⟩ := hfield _ hV
  refine ⟨hG u hu, hdiff, ?_⟩
  rw [hfe]
  exact hder

end KAM.Planetary.Spatial

end
