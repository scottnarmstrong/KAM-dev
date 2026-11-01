/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.ChartLift
public import KAM.Planetary.StrongAMD.Nek.Cells
public import KAM.Planetary.StrongAMD.Nek.Cover
public import KAM.Planetary.StrongAMD.Nek.Perturbation

/-!
# The stopped drift on one cell (the cellwise core of LP3-DRIFT)

Package LP3-DRIFT, MAIN Lemma 14 (`LP:MAIN L14 (468–500)`, steps 1–7 of `LP3-PLAN` §2.4), track LP,
non-frozen.  The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

For a physical segment that is stopped (`StoppedOn`) and whose initial action lies within `η/2` of
the centre `c` of a cell:

* `isSharedTube_of_le`: the shared tube is monotone in the radius;
* `nek_sharp_slow_bound` (step 4, the curvature step): along the stopped interval
  `strongAMD < B(c) - 3δ/8`, sharper than the whole-ball bound `C ≤ B(I⁰) - δ/4`;
* `nekNHam`: the N-Hamiltonian `h(fast) + ε Re P` of the frozen theorem for `h = planetaryKeplerC ν`;
* `nek_isSolutionOn_cell` (step 6): the `V_j`-form of the solution premise;
* `nek_stopped_drift_core` (steps 1–7): the cell conclusion, with the lifted solution and the
  erosion premises derived from `StoppedOn`.  The cell data (the field identity on `V_j`, the
  frozen conclusion for the cell) are hypotheses here, and are supplied by `Nek/Drift`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open Set Metric KAM.Nekhoroshev

variable {n : ℕ}

/-- The shared tube is monotone in the radius: a smaller positive radius still satisfies
`IsSharedTube` (compactness, chamber and modulus transfer to the smaller thickening). -/
theorem isSharedTube_of_le {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {L : Set (Fin n → ℝ)} {δ r r' : ℝ} (hg : IsSharedTube ν L δ r) (hr' : 0 < r') (hle : r' ≤ r) :
    IsSharedTube ν L δ r' := by
  have hsub : cthickening (4 * r') (strongLevelSet ν L δ) ⊆
      cthickening (4 * r) (strongLevelSet ν L δ) := cthickening_mono (by linarith) _
  refine ⟨hr', hg.compact.of_isClosed_subset isClosed_cthickening hsub,
    hsub.trans hg.subset_chamber, ?_⟩
  calc strongThresholdModulus ν (cthickening (4 * r') (strongLevelSet ν L δ)) (4 * r')
      ≤ strongThresholdModulus ν (cthickening (4 * r) (strongLevelSet ν L δ)) (4 * r') :=
        strongThresholdModulus_mono_set hν hn hsub hg.compact hg.subset_chamber _
    _ ≤ strongThresholdModulus ν (cthickening (4 * r) (strongLevelSet ν L δ)) (4 * r) :=
        strongThresholdModulus_mono hν hn hg.compact hg.subset_chamber (by linarith)
    _ ≤ δ / 16 := hg.modulus

/-- **The sharpened slow bound** (`LP:MAIN L14 (468–500)`, `LP3-PLAN` §2.4 step 4).  Along the
stopped interval the strong AMD is below `B(c) - 3δ/8`, where `c ∈ 𝓛_δ` is a cell centre within
`η/2` of the initial action: `B` moves by at most `δ/16` from `Λ(z u)` to `I⁰` and from `I⁰` to
`c` (shared-tube modulus), and `C < B(Λ(z u)) - δ/2` on the stopped interval. -/
theorem nek_sharp_slow_bound {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {L : Set (Fin n → ℝ)} {δ rg R r : ℝ} (hg : IsSharedTube ν L δ rg)
    {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ) {z₀ : Phase (n * 2)}
    (hd : LiftData ν (sharedTube ν L δ rg) z₀ δ r)
    (hI0 : actionVector ν z₀ ∈ strongLevelSet ν L δ)
    (hclose : ‖actionVector ν z₀ - c‖ < nekEta rg R / 2) (hr4 : r ≤ 4 * rg)
    {z : ℝ → Phase (n * 2)} {t : ℝ} (hs : StoppedOn ν z₀ δ r z t) {u : ℝ}
    (hu : u ∈ uIcc 0 t) :
    strongAMD ν (z u) < strongThreshold ν c - 3 * δ / 8 := by
  obtain ⟨-, hr, hC⟩ := hs u hu
  have hΛu : actionVector ν (z u) ∈ sharedTube ν L δ rg := hd.actionVector_mem hr.le
  have hΛ0 : actionVector ν z₀ ∈ sharedTube ν L δ rg :=
    hd.ball _ (by simpa using hd.r_pos.le)
  have h1 := (abs_strongThreshold_sub_le_modulus hν hn hg.compact hg.subset_chamber hΛu hΛ0
    (r := 4 * rg) (hr.le.trans hr4)).trans hg.modulus
  have h2 := nekCell_threshold_bound_of_close (R := R) hν hn hg hI0 hc hclose
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- The N-Hamiltonian `h(fast) + ε Re P` of the frozen theorem, for the Kepler part
`h = planetaryKeplerC ν` and the planar slow dimension `n`. -/
def nekNHam (ν : Fin n → ℝ) (P : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ) → ℂ) (ε : ℝ) :
    Phase (n + n) → ℝ :=
  degenerateHamiltonian (KAM.Nekhoroshev.realPart (planetaryKeplerC ν))
    (fun _ x => (P (KAM.Nekhoroshev.complexifyPhase x)).re) ε

/-- **The `V_j`-form of the solution premise** (`LP3-PLAN` §2.4 step 6): a chart solution of the
`liftChartHam ν μ` field that stays in the open region `V_j` with fast actions in the cell `G_j`
solves the N-system `nekNHam ν P ε` in the sense of the frozen `IsSolutionOn`, provided the two
fields agree on `V_j`. -/
theorem nek_isSolutionOn_cell {ν : Fin n → ℝ} {δ rg R μ ε : ℝ}
    {P : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ) → ℂ} {c : Fin n → ℝ} {w : ℝ → Phase (n + n)}
    {t : ℝ} {I : Set ℝ} (hsub : uIcc 0 t ⊆ I)
    (hw : ∀ u ∈ I, w u ∈ chartSafe ν ∧
      HasDerivAt w (KAM.hamiltonianVectorField (liftChartHam ν μ) (w u)) u)
    (hreg : ∀ u ∈ uIcc 0 t, w u ∈ nekCellRegion rg R ν δ c)
    (hfield : ∀ x ∈ nekCellRegion rg R ν δ c, DifferentiableAt ℝ (nekNHam ν P ε) x ∧
      KAM.hamiltonianVectorField (nekNHam ν P ε) x =
        KAM.hamiltonianVectorField (liftChartHam ν μ) x)
    (hinner : ∀ u ∈ uIcc 0 t, fast (b := n) (w u).2 ∈ nekCellInner rg R c) :
    IsSolutionOn (nekNHam ν P ε) {I | fast (b := n) I ∈ nekCellInner rg R c} (uIcc 0 t) w := by
  intro u hu
  obtain ⟨hdiff, hfeq⟩ := hfield _ (hreg u hu)
  refine ⟨hinner u hu, hdiff, ?_⟩
  rw [hfeq]
  exact (hw u (hsub hu)).2

/-- **The stopped drift on one cell** (`LP:MAIN L14 (468–500)`, `LP3-PLAN` §2.4 steps 1–7).  Let
`z` be a moving solution on `J ∋ 0` from `z₀`, stopped on `uIcc 0 t` with radius
`r = ε^{b_n}`, and let the cell centre `c ∈ 𝓛_δ` lie within `η/2` of the initial action.  If the
frozen cell conclusion `hcell` and the field identity `hfield` on `V_j` hold, and
`r ≤ η/4`, `√(2(B(c) - 3δ/8)) + √(2n) r < √(2 A_j)`, then the drift is at most `r/2`.
The hypotheses `hfield`, `hcell` are cell data produced by `Nek/Drift`, not source premises. -/
theorem nek_stopped_drift_core {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {L : Set (Fin n → ℝ)} {δ rg R μ ε : ℝ} (hR : 0 < R) (hg : IsSharedTube ν L δ rg)
    {P : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ) → ℂ}
    {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ) {z₀ : Phase (n * 2)}
    (hd : LiftData ν (sharedTube ν L δ rg) z₀ δ (ε ^ partialDriftExponent n))
    (hI0 : actionVector ν z₀ ∈ strongLevelSet ν L δ)
    (hclose : ‖actionVector ν z₀ - c‖ < nekEta rg R / 2)
    (hrη : ε ^ partialDriftExponent n ≤ nekEta rg R / 4)
    (hgap : Real.sqrt (2 * (strongThreshold ν c - 3 * δ / 8)) +
      Real.sqrt (2 * n) * ε ^ partialDriftExponent n < Real.sqrt (2 * nekCellLevel ν δ c))
    (hfield : ∀ x ∈ nekCellRegion rg R ν δ c, DifferentiableAt ℝ (nekNHam ν P ε) x ∧
      KAM.hamiltonianVectorField (nekNHam ν P ε) x =
        KAM.hamiltonianVectorField (liftChartHam ν μ) x)
    (hcell : ∀ (w : ℝ → Phase (n + n)) (t : ℝ),
      |t| ≤ ε⁻¹ * Real.exp (ε ^ (-partialTimeExponent n)) →
      IsSolutionOn (nekNHam ν P ε) {I | fast (b := n) I ∈ nekCellInner rg R c} (uIcc 0 t) w →
      fast (b := n) (w 0).2 ∈
        KAM.Nekhoroshev.innerCore (nekCellInner rg R c) (ε ^ partialDriftExponent n) →
      (∀ u ∈ uIcc 0 t, (slow (a := n) (w u).1, slow (a := n) (w u).2) ∈
        KAM.Nekhoroshev.innerCore (nekCellSlow ν δ c) (ε ^ partialDriftExponent n)) →
      ‖fast (b := n) (w t).2 - fast (b := n) (w 0).2‖ ≤ ε ^ partialDriftExponent n / 2)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → Phase (n * 2)}
    (hz : IsMovingSolutionOn ν μ J z) (hz0 : z 0 = z₀) {t : ℝ} (ht : t ∈ J)
    (htT : |t| ≤ ε⁻¹ * Real.exp (ε ^ (-partialTimeExponent n)))
    (hs : StoppedOn ν z₀ δ (ε ^ partialDriftExponent n) z t) :
    ‖actionVector ν (z t) - actionVector ν z₀‖ ≤ ε ^ partialDriftExponent n / 2 := by
  have hr0 : 0 < ε ^ partialDriftExponent n := hd.r_pos
  have hη : 0 < nekEta rg R := by
    have := lt_of_le_of_lt (norm_nonneg _) hclose
    linarith
  have hrg := hg.pos
  have hr4 : ε ^ partialDriftExponent n ≤ 4 * rg := by
    have := nekEta_le (rg := rg) (R := R)
    linarith
  obtain ⟨w, I, -, -, hsub, hw, hΨ, hw0⟩ := hd.lpChartLift_of_stopped hJ h0 hz hz0 ht hs
  -- the dictionary: chart actions and AMD along the lift
  have hact : ∀ u ∈ uIcc 0 t, fast (b := n) (w u).2 = actionVector ν (z u) := by
    intro u hu
    funext i
    have := lpChart_action hν (hw u (hsub hu)).1.1 i
    rw [hΨ u hu] at this
    exact this.symm
  have hamd : ∀ u ∈ uIcc 0 t, chartAMD (w u) = strongAMD ν (z u) := by
    intro u hu
    rw [← lpChart_strongAMD hν (hw u (hsub hu)).1.1, hΨ u hu]
  -- erosion premises
  have hslow : ∀ u ∈ uIcc 0 t, (slow (a := n) (w u).1, slow (a := n) (w u).2) ∈
      KAM.Nekhoroshev.innerCore (nekCellSlow ν δ c) (ε ^ partialDriftExponent n) := by
    intro u hu
    refine stopped_slow_erosion (A₁ := strongThreshold ν c - 3 * δ / 8) hr0.le hgap ?_
    show chartAMD (w u) < _
    rw [hamd u hu]
    exact nek_sharp_slow_bound hν hn hg hc hd hI0 hclose hr4 hs hu
  have hinner : ∀ u ∈ uIcc 0 t, fast (b := n) (w u).2 ∈ nekCellInner rg R c := by
    intro u hu
    rw [hact u hu]
    exact nekCell_mem_of_close hclose hrη (hs u hu).2.1.le hη
  have hreg : ∀ u ∈ uIcc 0 t, w u ∈ nekCellRegion rg R ν δ c := fun u hu =>
    ⟨nekCellInner_subset_outer rg R hrg hR c (hinner u hu), (hslow u hu).1⟩
  have hsol := nek_isSolutionOn_cell hsub hw hreg hfield hinner
  have hfast0 : fast (b := n) (w 0).2 ∈
      KAM.Nekhoroshev.innerCore (nekCellInner rg R c) (ε ^ partialDriftExponent n) := by
    rw [hw0]
    exact nekCell_mem_innerCore hclose hrη hη hr0.le
  have hN := hcell w t htT hsol hfast0 hslow
  rw [hact t right_mem_uIcc, hw0] at hN
  exact hN

end KAM.Planetary.StrongAMD

end
