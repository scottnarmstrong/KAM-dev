/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Geometry
public import KAM.Planetary.StrongAMD.Modulus
public import KAM.Planetary.StrongAMD.Momentum
public import KAM.Planetary.StrongAMD.PlanarDictionary

/-!
# The stopped interval: prograde states and the whole-ball bound

Package LP-LIFT, MAIN Lemma 14 (`LP:MAIN L14 (468–500)`, lines 477–480, with amendments N2, N6),
track LP, non-frozen.

On the stopped interval (MAIN's stopped conditions (40), in the strict form of the LP-CONF
helper `hstop`) every physical point is prograde and a barrier state with margin `δ/2`
(`LiftData.prograde_of_stopped`), and it satisfies the whole-ball bound
`C ≤ B(I⁰) - δ/4` (`LiftData.strongAMD_le_of_stopped`, MAIN line 480).

* `LiftData`: the source data (standing assumptions, the budget, the initial state, the orientation
  `0 < L(z₀)`); no drift or confinement conclusion.
* `StoppedOn`: the strict stopped conditions, literally the antecedent of LP-CONF's `hstop`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set

variable {n : ℕ}

/-- The data of MAIN Lemma 14 (`LP:MAIN L14 (468–500)`, N2): positive masses, `2 ≤ n`, the shared
compact `U ⊆ 𝒬`, `0 < δ`, `0 < r` with the budget `n r + Ω_B(r) ≤ δ/4`, a physical initial state
`z₀` whose closed `r`-action ball lies in `U`, `C(z₀) ≤ B(Λ z₀) - δ`, and the orientation
`0 < L(z₀)` (MAIN Theorem 15, reflection). Only source premises and typing data. -/
structure LiftData (ν : Fin n → ℝ) (U : Set (Fin n → ℝ)) (z₀ : Phase (n * 2)) (δ r : ℝ) :
    Prop where
  pos_mass : ∀ i, 0 < ν i
  two_le : 2 ≤ n
  compact : IsCompact U
  subset_chamber : U ⊆ chamber ν
  delta_pos : 0 < δ
  r_pos : 0 < r
  budget : n * r + strongThresholdModulus ν U r ≤ δ / 4
  physical : IsPhysicalState ν z₀
  ball : ∀ I, ‖I - actionVector ν z₀‖ ≤ r → I ∈ U
  amd : strongAMD ν z₀ ≤ strongThreshold ν (actionVector ν z₀) - δ
  orient : 0 < totalMomentum z₀

/-- The strict stopped conditions (`LP:MAIN L14 (40)`, N6) on `uIcc 0 t`: literally the antecedent
of the `hstop` hypothesis of LP-CONF's `strongFirstExit_of_stopped_drift`. -/
def StoppedOn (ν : Fin n → ℝ) (z₀ : Phase (n * 2)) (δ r : ℝ) (z : ℝ → Phase (n * 2)) (t : ℝ) :
    Prop :=
  ∀ u ∈ uIcc 0 t, IsPhysicalState ν (z u) ∧
    ‖actionVector ν (z u) - actionVector ν z₀‖ < r ∧
    strongAMD ν (z u) < strongThreshold ν (actionVector ν (z u)) - δ / 2

namespace LiftData

variable {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} {z₀ : Phase (n * 2)} {δ r : ℝ}

theorem n_mul_r_pos (hd : LiftData ν U z₀ δ r) : 0 < (n : ℝ) * r := by
  have : (0 : ℝ) < n := by
    have := hd.two_le
    exact_mod_cast (by omega : 0 < n)
  exact mul_pos this hd.r_pos

theorem actionVector_mem (hd : LiftData ν U z₀ δ r) {z : Phase (n * 2)}
    (h : ‖actionVector ν z - actionVector ν z₀‖ ≤ r) : actionVector ν z ∈ U :=
  hd.ball _ h

/-- Within the `r`-ball the threshold moves by at most `δ/4 - n r` (the budget). -/
theorem abs_threshold_sub_le (hd : LiftData ν U z₀ δ r) {I : Fin n → ℝ}
    (hI : ‖I - actionVector ν z₀‖ ≤ r) :
    |strongThreshold ν I - strongThreshold ν (actionVector ν z₀)| ≤ δ / 4 - n * r := by
  have h0 : actionVector ν z₀ ∈ U := hd.ball _ (by simpa using hd.r_pos.le)
  have := abs_strongThreshold_sub_le_modulus hd.pos_mass hd.two_le hd.compact hd.subset_chamber
    (hd.ball _ hI) h0 hI
  linarith [hd.budget]

/-- The AMD level of the whole ball: `B(I⁰) - δ/4 ≤ B(I) - n r` for `‖I - I⁰‖ ≤ r`. -/
theorem threshold_ball_le (hd : LiftData ν U z₀ δ r) {I : Fin n → ℝ}
    (hI : ‖I - actionVector ν z₀‖ ≤ r) :
    strongThreshold ν (actionVector ν z₀) - δ / 4 ≤ strongThreshold ν I - n * r := by
  have := (abs_le.1 (hd.abs_threshold_sub_le hI)).1
  linarith

/-- (`LP:MAIN L14 (480)`) Whole-ball membership: along the stopped interval,
`C(z u) ≤ B(I⁰) - δ/4`; indeed `C < B(Λ) - δ/2 ≤ B(I⁰) + Ω(r) - δ/2`. -/
theorem strongAMD_le_of_stopped (hd : LiftData ν U z₀ δ r) {z : ℝ → Phase (n * 2)} {t : ℝ}
    (hs : StoppedOn ν z₀ δ r z t) {u : ℝ} (hu : u ∈ uIcc 0 t) :
    strongAMD ν (z u) ≤ strongThreshold ν (actionVector ν z₀) - δ / 4 := by
  obtain ⟨-, hr, hC⟩ := hs u hu
  have := (abs_le.1 (hd.abs_threshold_sub_le hr.le)).2
  linarith [hd.n_mul_r_pos]

/-- Item 1 (`LP:MAIN L14 (477–480)`, `LP:MAIN L3`): on the stopped interval every state is
prograde elliptic (conservation of `L`, `cross_sign_and_margin` with `m = δ/2`) and a barrier
state with margin `δ/2`. -/
theorem prograde_of_stopped (hd : LiftData ν U z₀ δ r) {μ : ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    (h0 : (0 : ℝ) ∈ J) {z : ℝ → Phase (n * 2)} (hz : IsMovingSolutionOn ν μ J z)
    (hz0 : z 0 = z₀) {t : ℝ} (ht : t ∈ J) (hs : StoppedOn ν z₀ δ r z t) :
    ∀ u ∈ uIcc 0 t, ProgradeElliptic ν (z u) ∧ BarrierState ν U (δ / 2) (z u) := by
  intro u hu
  have huJ : u ∈ J := hJ.uIcc_subset h0 ht hu
  obtain ⟨hphys, hr, hC⟩ := hs u hu
  have hL : 0 < totalMomentum (z u) := by
    rw [totalMomentum_const hJ hz 0 h0 u huJ, hz0]
    exact hd.orient
  have hmargin : ∀ i, strongAMD ν (z u) ≤ keplerAction ν (z u) i - δ / 2 := fun i => by
    have := strongThreshold_le_action ν (actionVector ν (z u)) i
    have h2 : actionVector ν (z u) i = keplerAction ν (z u) i := rfl
    linarith
  refine ⟨fun i => ?_, hphys, hd.actionVector_mem hr.le, by linarith⟩
  obtain ⟨-, hpos, -⟩ := cross_sign_and_margin (hphys.orbital hd.pos_mass) (half_pos hd.delta_pos)
    hmargin i
  exact ⟨hd.pos_mass i, (hphys i).1, (hphys i).2, pos_of_mul_pos_left hpos hL.le⟩

end LiftData

end KAM.Planetary.StrongAMD

end
