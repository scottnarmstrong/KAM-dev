/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Confinement
public import KAM.Planetary.Spatial.Product

/-!
# The spatial stopped interval: aligned prograde states and the whole-ball bound

Source: MAIN Lemma 14 (`LP:MAIN L14 (468–500)`, lines 477–480) with the spatial
Lemma 18 alignment (`LP:MAIN L18 (595–597)`, `d = 3`) and amendments N2, N6; track LP,
non-frozen.

On the stopped interval (MAIN's stopped conditions (40), in the strict form of the spatial confinement
helper `hstop`) every physical state is a barrier state with margin `δ/2`, its angular momentum
stays aligned with `e₃`, and the projections `L_i · e₃ ≥ δ/2 > 0` put it in the image of the
spatial product chart (`spatialPoincareProd_image`); the strong AMD is the fixed-plane deficit
and satisfies the whole-ball bound `C ≤ B(I⁰) - δ/4` (MAIN (47)).

* `SpatialLiftData`: source data (standing assumptions, the budget, the initial state, the
  alignment `L(z₀) = |L(z₀)| e₃`); no drift or confinement conclusion.
* `SpatialStoppedOn`: the strict stopped conditions, literally the antecedent of the spatial confinement's
  `hstop`.
* `spLiftSecularBall`: the ball (47) in physical slow coordinates `Phase (n + n)`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary KAM.Planetary.StrongAMD Set

variable {n : ℕ}

/-- The ball (47), in physical slow coordinates
`(q, p) ∈ Phase (n + n)` (`2n` slow pairs): `Σ_k (q_k² + p_k²)/2 ≤ B(I⁰) - δ/4`
(`LP:MAIN L18 (47)`). -/
def spLiftSecularBall (ν : Fin n → ℝ) (δ : ℝ) (I0 : Fin n → ℝ) : Set (Phase (n + n)) :=
  {y | ∑ k, (y.1 k ^ 2 + y.2 k ^ 2) / 2 ≤ strongThreshold ν I0 - δ / 4}

/-- The data of MAIN Lemma 14 for `d = 3` (`LP:MAIN L14 (468–500)`, `LP:MAIN L18 (595–597)`, N2):
positive masses, `2 ≤ n`, the shared compact `U ⊆ 𝒬`, `0 < δ`, `0 < r` with the budget
`n r + Ω_B(r) ≤ δ/4`, a physical initial state `z₀` whose closed `r`-action ball lies in `U`,
`C(z₀) ≤ B(Λ z₀) - δ`, and the alignment of its angular momentum with `e₃`
(MAIN L18, "after aligning `e₃` with the initial total angular momentum").  Only source premises
and typing data. -/
structure SpatialLiftData (ν : Fin n → ℝ) (U : Set (Fin n → ℝ)) (z₀ : Phase (n * 3))
    (δ r : ℝ) : Prop where
  pos_mass : ∀ i, 0 < ν i
  two_le : 2 ≤ n
  compact : IsCompact U
  subset_chamber : U ⊆ chamber ν
  delta_pos : 0 < δ
  r_pos : 0 < r
  budget : n * r + strongThresholdModulus ν U r ≤ δ / 4
  physical : SpatialNegativeEnergy ν z₀
  ball : ∀ I, ‖I - spatialActionVector ν z₀‖ ≤ r → I ∈ U
  amd : spatialStrongAMD ν z₀ ≤ strongThreshold ν (spatialActionVector ν z₀) - δ
  aligned : angularMomentum3 z₀ = spaceLength (angularMomentum3 z₀) • e₃

/-- The strict stopped conditions (`LP:MAIN L14 (40)`, N6) on `uIcc 0 t`: literally the antecedent
of the `hstop` hypothesis of the spatial confinement's `spatialStrongFirstExit_of_stopped_drift`. -/
def SpatialStoppedOn (ν : Fin n → ℝ) (z₀ : Phase (n * 3)) (δ r : ℝ) (z : ℝ → Phase (n * 3))
    (t : ℝ) : Prop :=
  ∀ u ∈ uIcc 0 t, SpatialNegativeEnergy ν (z u) ∧
    ‖spatialActionVector ν (z u) - spatialActionVector ν z₀‖ < r ∧
    spatialStrongAMD ν (z u) < strongThreshold ν (spatialActionVector ν (z u)) - δ / 2

namespace SpatialLiftData

variable {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} {z₀ : Phase (n * 3)} {δ r : ℝ}

theorem spLift_n_mul_r_pos (hd : SpatialLiftData ν U z₀ δ r) : 0 < (n : ℝ) * r := by
  have : (0 : ℝ) < n := by
    have := hd.two_le
    exact_mod_cast (by omega : 0 < n)
  exact mul_pos this hd.r_pos

/-- Within the `r`-ball the threshold moves by at most `δ/4 - n r` (the budget). -/
theorem spLift_abs_threshold_sub_le (hd : SpatialLiftData ν U z₀ δ r) {I : Fin n → ℝ}
    (hI : ‖I - spatialActionVector ν z₀‖ ≤ r) :
    |strongThreshold ν I - strongThreshold ν (spatialActionVector ν z₀)| ≤ δ / 4 - n * r := by
  have h0 : spatialActionVector ν z₀ ∈ U := hd.ball _ (by simpa using hd.r_pos.le)
  have := abs_strongThreshold_sub_le_modulus hd.pos_mass hd.two_le hd.compact hd.subset_chamber
    (hd.ball _ hI) h0 hI
  linarith [hd.budget]

/-- The AMD level of the whole ball: `B(I⁰) - δ/4 ≤ B(I) - n r` for `‖I - I⁰‖ ≤ r`. -/
theorem spLift_threshold_ball_le (hd : SpatialLiftData ν U z₀ δ r) {I : Fin n → ℝ}
    (hI : ‖I - spatialActionVector ν z₀‖ ≤ r) :
    strongThreshold ν (spatialActionVector ν z₀) - δ / 4 ≤ strongThreshold ν I - n * r := by
  have := (abs_le.1 (hd.spLift_abs_threshold_sub_le hI)).1
  linarith

/-- (`LP:MAIN L14 (480)`) Whole-ball bound on the stopped interval:
`C(z u) < B(Λ) - δ/2 ≤ B(I⁰) + Ω(r) - δ/2 ≤ B(I⁰) - δ/4`. -/
theorem spLift_strongAMD_le_of_stopped (hd : SpatialLiftData ν U z₀ δ r) {z : ℝ → Phase (n * 3)}
    {t : ℝ} (hs : SpatialStoppedOn ν z₀ δ r z t) {u : ℝ} (hu : u ∈ uIcc 0 t) :
    spatialStrongAMD ν (z u) ≤ strongThreshold ν (spatialActionVector ν z₀) - δ / 4 := by
  obtain ⟨-, hr, hC⟩ := hs u hu
  have := (abs_le.1 (hd.spLift_abs_threshold_sub_le hr.le)).2
  linarith [hd.spLift_n_mul_r_pos]

/-- The alignment of a state with `e₃` is `L = |L| e₃`; an aligned nonzero `L` has unit direction
`e₃`. -/
theorem spatialUnit_of_aligned {L : Fin 3 → ℝ} (hL : L = spaceLength L • e₃) (hne : L ≠ 0) :
    spatialUnit L = e₃ := by
  have hpos : 0 < spaceLength L := spaceLength_pos_iff.2 hne
  show (spaceLength L)⁻¹ • L = e₃
  calc (spaceLength L)⁻¹ • L = (spaceLength L)⁻¹ • (spaceLength L • e₃) := congrArg _ hL
    _ = e₃ := by rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

/-- (`LP:MAIN L14 (477–480)`, `LP:MAIN L18 (595–597)`, `LP:MAIN L3`) **Items 1–2, the state
part.**  On the stopped interval every state is a barrier state with margin `δ/2`, its angular
momentum is `|L| e₃` (conservation of `L` plus the alignment of `z₀`), its projections satisfy
`L_i · e₃ ≥ δ/2` (`proj_margin` with `m = δ/2`), and it lies in the image region of the product
chart. -/
theorem spLift_prograde_of_stopped (hd : SpatialLiftData ν U z₀ δ r) {μ : ℝ} {J : Set ℝ}
    (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → Phase (n * 3)}
    (hz : IsSpatialMovingSolutionOn ν μ J z) (hz0 : z 0 = z₀) {t : ℝ} (ht : t ∈ J)
    (hs : SpatialStoppedOn ν z₀ δ r z t) :
    ∀ u ∈ uIcc 0 t, SpatialBarrierState ν U (δ / 2) (z u) ∧
      angularMomentum3 (z u) = spaceLength (angularMomentum3 (z u)) • e₃ ∧
      (∀ i, δ / 2 ≤ planetAngularMomentum3 (z u) i ⬝ᵥ e₃) ∧
      z u ∈ spatialRegionProd ν := by
  intro u hu
  have huJ : u ∈ J := hJ.uIcc_subset h0 ht hu
  obtain ⟨hphys, hr, hC⟩ := hs u hu
  have hLc : angularMomentum3 (z u) = angularMomentum3 z₀ := by
    rw [angularMomentum3_const hJ hz 0 h0 u huJ, hz0]
  have hal : angularMomentum3 (z u) = spaceLength (angularMomentum3 (z u)) • e₃ := by
    rw [hLc]; exact hd.aligned
  have hmargin : ∀ i, spatialStrongAMD ν (z u) ≤ spatialKeplerAction ν (z u) i - δ / 2 :=
    fun i => by
      have := strongThreshold_le_action ν (spatialActionVector ν (z u)) i
      have h2 : spatialActionVector ν (z u) i = spatialKeplerAction ν (z u) i := rfl
      linarith
  have hproj : ∀ i, angularMomentum3 (z u) ≠ 0 ∧ δ / 2 ≤ planetAngularMomentum3 (z u) i ⬝ᵥ e₃ :=
    fun i => by
      obtain ⟨hne, hm⟩ := proj_margin hphys (half_pos hd.delta_pos) hmargin i
      refine ⟨hne, ?_⟩
      rwa [spatialUnit_of_aligned hal hne, spaceDot_eq_dotProduct] at hm
  refine ⟨⟨hphys, hd.ball _ hr.le, by linarith⟩, hal, fun i => (hproj i).2, fun i => ?_⟩
  refine ⟨?_, ?_⟩
  · rw [← spatialKeplerEnergy_eq_spatialEnergy]; exact (hphys i).2.2
  · have := (hproj i).2
    rw [planetAngularMomentum3_eq_cross] at this
    linarith [half_pos hd.delta_pos]

end SpatialLiftData

end KAM.Planetary.Spatial

end
