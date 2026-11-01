/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Orbital
public import KAM.Planetary.AMD.AngularMomentum
public import KAM.Frozen.Planetary.Defs.TotalMomentum
public import KAM.Frozen.Planetary.Defs.PhysicalAMD
public import KAM.Frozen.Planetary.StrongAMD.Defs.StrongAMD

/-!
# The strong AMD and exact angular momentum, planar

Package LP-MOM, `LP:MAIN L3 (130–139)`, definition `LP:MAIN §1 (2) (26–45)`; track LP,
non-frozen; the statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

`strongAMD ν z = Σ Λ_i - |L|` with the absolute value of the total angular momentum.  Items:
conservation of `L` and the AMD identity (13) along a moving solution; `0 ≤ C`; `C < Λ_k ⇒ L ≠ 0`;
the projection bounds and the margin corollary; the eccentricity-deficit bound; the bridge to the
signed `physicalAMD` when `0 ≤ L`.

All per-planet statements assume `0 < ν i`, `0 < |q_i|`, `E_i < 0` for every `i` (the
negative-energy region), packaged as
`hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary
open scoped BigOperators

variable {n : ℕ}

private theorem abs_cross_le_action {ν : Fin n → ℝ} {z : Phase (n * 2)}
    (hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0) (i : Fin n) :
    |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| ≤ keplerAction ν z i :=
  (orbital_identities i (hz i)).2.2.2.2.2.2.1

private theorem action_nonneg {ν : Fin n → ℝ} {z : Phase (n * 2)}
    (hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0) (i : Fin n) :
    0 ≤ keplerAction ν z i :=
  (orbital_identities i (hz i)).2.1.le

private theorem abs_totalMomentum_le (z : Phase (n * 2)) :
    |totalMomentum z| ≤ ∑ i, |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| :=
  Finset.abs_sum_le_sum_abs _ _

/-- Lemma 3, conservation: `L` is constant along a moving solution on an order-connected set
(`LP:MAIN L3 (130–139)`). -/
theorem totalMomentum_const {ν : Fin n → ℝ} {μ : ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    {z : ℝ → Phase (n * 2)} (hz : IsMovingSolutionOn ν μ J z) :
    ∀ s ∈ J, ∀ t ∈ J, totalMomentum (z t) = totalMomentum (z s) :=
  ang_mom hJ hz

/-- Lemma 3, (13) identity (`LP:MAIN L3 (130–139)`): along a moving solution the change of the
strong AMD is the change of the action sum.  (No energy sign is needed for this identity.) -/
theorem strongAMD_sub_eq_sum {ν : Fin n → ℝ} {μ : ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    {z : ℝ → Phase (n * 2)} (hz : IsMovingSolutionOn ν μ J z) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    strongAMD ν (z t) - strongAMD ν (z s) =
      ∑ i, (keplerAction ν (z t) i - keplerAction ν (z s) i) := by
  unfold strongAMD
  rw [totalMomentum_const hJ hz s hs t ht, Finset.sum_sub_distrib]
  ring

/-- Lemma 3: `0 ≤ C` in the negative-energy region (`LP:MAIN L3 (130–139)`). -/
theorem strongAMD_nonneg {ν : Fin n → ℝ} {z : Phase (n * 2)}
    (hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0) :
    0 ≤ strongAMD ν z := by
  unfold strongAMD
  have h1 := abs_totalMomentum_le z
  have h2 : ∑ i, |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| ≤ ∑ i, keplerAction ν z i :=
    Finset.sum_le_sum fun i _ => abs_cross_le_action hz i
  linarith

/-- `C = Σ_i (Λ_i - L_i)` when `0 ≤ L`. -/
theorem strongAMD_eq_sum_sub_of_nonneg {ν : Fin n → ℝ} {z : Phase (n * 2)}
    (hL : 0 ≤ totalMomentum z) :
    strongAMD ν z = ∑ i, (keplerAction ν z i -
      planeCross (bodyVector z.1 i) (bodyVector z.2 i)) := by
  unfold strongAMD
  rw [abs_of_nonneg hL, Finset.sum_sub_distrib]
  rfl

/-- `C = Σ_i (Λ_i + L_i)` when `L ≤ 0`. -/
theorem strongAMD_eq_sum_add_of_nonpos {ν : Fin n → ℝ} {z : Phase (n * 2)}
    (hL : totalMomentum z ≤ 0) :
    strongAMD ν z = ∑ i, (keplerAction ν z i +
      planeCross (bodyVector z.1 i) (bodyVector z.2 i)) := by
  unfold strongAMD
  rw [abs_of_nonpos hL, Finset.sum_add_distrib]
  simp [totalMomentum]

/-- Lemma 3: `C < Λ_k` for some `k` forces `L ≠ 0` (`LP:MAIN L3 (130–139)`). -/
theorem totalMomentum_ne_zero_of_strongAMD_lt {ν : Fin n → ℝ} {z : Phase (n * 2)}
    (hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0)
    {k : Fin n} (hk : strongAMD ν z < keplerAction ν z k) : totalMomentum z ≠ 0 := by
  intro h0
  have : strongAMD ν z = ∑ i, keplerAction ν z i := by
    unfold strongAMD; rw [h0]; simp
  have hle : keplerAction ν z k ≤ ∑ i, keplerAction ν z i :=
    Finset.single_le_sum (fun i _ => action_nonneg hz i) (Finset.mem_univ k)
  linarith

/-- Lemma 3, projection bound for `0 < L`: `Λ_i - C ≤ L_i` (`LP:MAIN L3 (130–139)`). -/
theorem action_sub_strongAMD_le_cross_of_pos {ν : Fin n → ℝ} {z : Phase (n * 2)}
    (hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0)
    (hL : 0 < totalMomentum z) (i : Fin n) :
    keplerAction ν z i - strongAMD ν z ≤ planeCross (bodyVector z.1 i) (bodyVector z.2 i) := by
  rw [strongAMD_eq_sum_sub_of_nonneg hL.le]
  have hle : keplerAction ν z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i) ≤
      ∑ j, (keplerAction ν z j - planeCross (bodyVector z.1 j) (bodyVector z.2 j)) := by
    refine Finset.single_le_sum (f := fun j => keplerAction ν z j -
      planeCross (bodyVector z.1 j) (bodyVector z.2 j)) (fun j _ => ?_) (Finset.mem_univ i)
    have h1 := abs_cross_le_action hz j
    have h2 := le_abs_self (planeCross (bodyVector z.1 j) (bodyVector z.2 j))
    linarith
  linarith

/-- Lemma 3, projection bound for `L < 0`: `Λ_i - C ≤ -L_i` (`LP:MAIN L3 (130–139)`). -/
theorem action_sub_strongAMD_le_neg_cross_of_neg {ν : Fin n → ℝ} {z : Phase (n * 2)}
    (hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0)
    (hL : totalMomentum z < 0) (i : Fin n) :
    keplerAction ν z i - strongAMD ν z ≤ -planeCross (bodyVector z.1 i) (bodyVector z.2 i) := by
  rw [strongAMD_eq_sum_add_of_nonpos hL.le]
  have hle : keplerAction ν z i + planeCross (bodyVector z.1 i) (bodyVector z.2 i) ≤
      ∑ j, (keplerAction ν z j + planeCross (bodyVector z.1 j) (bodyVector z.2 j)) := by
    refine Finset.single_le_sum (f := fun j => keplerAction ν z j +
      planeCross (bodyVector z.1 j) (bodyVector z.2 j)) (fun j _ => ?_) (Finset.mem_univ i)
    have h1 := abs_cross_le_action hz j
    have h2 := neg_abs_le (planeCross (bodyVector z.1 j) (bodyVector z.2 j))
    linarith
  linarith

/-- Lemma 3, margin corollary in MAIN's form (`LP:MAIN L3 (130–139)`): if `C ≤ Λ_i - m` for all
`i` with `0 < m`, then `L ≠ 0`, every `L_i` has the sign of `L`, and `m ≤ |L_i|`. -/
theorem cross_sign_and_margin {ν : Fin n → ℝ} {z : Phase (n * 2)}
    (hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0)
    {m : ℝ} (hm : 0 < m) (hC : ∀ i, strongAMD ν z ≤ keplerAction ν z i - m) (i : Fin n) :
    totalMomentum z ≠ 0 ∧
      0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i) * totalMomentum z ∧
      m ≤ |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| := by
  have hne : totalMomentum z ≠ 0 :=
    totalMomentum_ne_zero_of_strongAMD_lt hz (k := i) (by linarith [hC i])
  refine ⟨hne, ?_⟩
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h := action_sub_strongAMD_le_neg_cross_of_neg hz hneg i
    have hLi : m ≤ -planeCross (bodyVector z.1 i) (bodyVector z.2 i) := by linarith [hC i]
    exact ⟨by nlinarith, by rw [abs_of_neg (by linarith)]; exact hLi⟩
  · have h := action_sub_strongAMD_le_cross_of_pos hz hpos i
    have hLi : m ≤ planeCross (bodyVector z.1 i) (bodyVector z.2 i) := by linarith [hC i]
    exact ⟨by nlinarith, by rw [abs_of_pos (by linarith)]; exact hLi⟩

/-- Lemma 3, (13) deficit bound (`LP:MAIN L3 (130–139)`):
`Σ_i Λ_i (1 - √(1 - e_i²)) ≤ C`. -/
theorem sum_action_mul_eccDeficit_le_strongAMD {ν : Fin n → ℝ} {z : Phase (n * 2)}
    (hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0) :
    ∑ i, keplerAction ν z i * (1 - Real.sqrt (1 - planeLength (keplerEccVector ν z i) ^ 2)) ≤
      strongAMD ν z := by
  have hterm : ∀ i, keplerAction ν z i *
      (1 - Real.sqrt (1 - planeLength (keplerEccVector ν z i) ^ 2)) =
        keplerAction ν z i - |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| := fun i => by
    rw [(orbital_identities i (hz i)).2.2.2.2.2.1]; ring
  simp only [hterm]
  rw [Finset.sum_sub_distrib]
  unfold strongAMD
  linarith [abs_totalMomentum_le z]

/-- Bridge: for `0 ≤ L` the strong AMD is the signed `physicalAMD` (`LP:MAIN §1 (2)`). -/
theorem strongAMD_eq_physicalAMD {ν : Fin n → ℝ} {z : Phase (n * 2)} (hL : 0 ≤ totalMomentum z) :
    strongAMD ν z = physicalAMD ν z := by
  unfold strongAMD physicalAMD
  rw [abs_of_nonneg hL]

end KAM.Planetary.StrongAMD

end
