/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.Assemble
public import KAM.Frozen.Planetary.Defs.Fast
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Frozen.Planetary.Defs.Slow
public import KAM.ODE.Lipschitz
public import KAM.Planetary.Exponential.Setting

/-!
# P14 package E8: uniform data on the compact fast cylinder

Blueprint P, Part 14 (`bpP:p14:uniform-data`, `stepP:p14:ud-cell`, `stepP:p14:ud-transl`): the
radian-period generalization of `KAM.ODE.gen_uniform_periodic`.  A `C¹` field on an open set `W`
that is `2π`-periodic in the fast angles has uniform data on the cylinder over a compact set `Q`
of zero fast angles, with radius `δ ≤ π`.  The compact cell `[-π, 3π]ⁿ` is the closed `π`-fattening
of one fundamental domain `[0, 2π)ⁿ`; translation by `fastShift ⌊λ / 2π⌋` moves every ball into it.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators ContDiff NNReal

namespace KAM.Planetary

variable {n : ℕ}

/-- The angle-zeroing map `w ↦ assemble (fast w.2) 0 (slow w.2) (slow w.1)`, componentwise. -/
theorem udZero_fst (w : Phase (n + n)) (i : Fin n) :
    (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)).1 (Fin.castAdd n i) = 0 := by
  simp [assemble]

theorem udZero_fst_natAdd (w : Phase (n + n)) (i : Fin n) :
    (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)).1 (Fin.natAdd n i) =
      w.1 (Fin.natAdd n i) := by
  simp [assemble, slow]

theorem udZero_snd (w : Phase (n + n)) :
    (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (n + n)).2 = w.2 := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [assemble, fast, slow]

/-- Angle-lattice translates of a point: the fast part of `fastShift k` is `2π k`. -/
theorem udShift_fst_castAdd (k : Fin n → ℤ) (i : Fin n) :
    (fastShift (b := n) k : Phase (n + n)).1 (Fin.castAdd n i) = 2 * Real.pi * (k i : ℝ) := by
  simp [fastShift]

theorem udShift_fst_natAdd (k : Fin n → ℤ) (i : Fin n) :
    (fastShift (b := n) k : Phase (n + n)).1 (Fin.natAdd n i) = 0 := by
  simp [fastShift]

theorem udShift_snd (k : Fin n → ℤ) : (fastShift (b := n) k : Phase (n + n)).2 = 0 := by
  simp [fastShift]

/-- Adding a fast angle block `lam` to the first component. -/
def udAngle (lam : Fin n → ℝ) : Phase (n + n) := (Fin.append lam (0 : Fin n → ℝ), 0)

theorem udAngle_continuous :
    Continuous (fun p : (Fin n → ℝ) × Phase (n + n) => p.2 + udAngle p.1) := by
  refine continuous_snd.add (Continuous.prodMk ?_ continuous_const)
  refine continuous_pi fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.append_left]; exact (continuous_apply i).comp continuous_fst
  · simp only [Fin.append_right]; exact continuous_const

/-- `stepP:p14:ud-cell`: the compact cell over `Q` with fast angles in `[-π, 3π]`. -/
theorem udCell_isCompact {Q : Set (Phase (n + n))} (hQ : IsCompact Q) :
    IsCompact ((fun p : (Fin n → ℝ) × Phase (n + n) => p.2 + udAngle p.1) ''
      (Icc (fun _ : Fin n => -Real.pi) (fun _ => 3 * Real.pi) ×ˢ Q)) :=
  (isCompact_Icc.prod hQ).image udAngle_continuous

theorem uniform_data {W Q : Set (Phase (n+n))} (hW : IsOpen W)
    {F : Phase (n+n) → Phase (n+n)} (hF : ContDiffOn ℝ 1 F W)
    (hWp : ∀ k : Fin n → ℤ, ∀ w, w ∈ W ↔ w + fastShift k ∈ W)
    (hFp : ∀ k : Fin n → ℤ, ∀ w ∈ W, F (w + fastShift k) = F w)
    (hQ : IsCompact Q) (hQ0 : ∀ w ∈ Q, fast w.1 = 0)
    (hQW : ∀ w : Phase (n+n),
      assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ Q → w ∈ W) :
    ∃ (delta M : ℝ) (L : ℝ≥0), KAM.ODE.UniformData F W
      {w | assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ Q} delta M L ∧ delta ≤ Real.pi := by
  set C := (fun p : (Fin n → ℝ) × Phase (n + n) => p.2 + udAngle p.1) ''
      (Icc (fun _ : Fin n => -Real.pi) (fun _ => 3 * Real.pi) ×ˢ Q) with hC
  have hCc : IsCompact C := udCell_isCompact hQ
  -- every point of the cell has its zeroed-angle point in `Q`, hence lies in `W`
  have hCW : C ⊆ W := by
    rintro y ⟨⟨lam, z⟩, ⟨-, hz⟩, rfl⟩
    refine hQW _ ?_
    have h0 := hQ0 z hz
    convert hz using 1
    ext j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have := congrFun h0 i
        simp [assemble, udAngle, fast] at this ⊢
        exact this.symm
      · simp [assemble, udAngle, slow]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [assemble, udAngle, fast, slow]
  obtain ⟨δ₀, hδ₀, hsub⟩ := hCc.exists_cthickening_subset_open hW hCW
  have hδpos : 0 < min δ₀ Real.pi := lt_min hδ₀ Real.pi_pos
  have hδπ : min δ₀ Real.pi ≤ Real.pi := min_le_right _ _
  set δ := min δ₀ Real.pi with hδ
  have hDW : cthickening δ C ⊆ W := (cthickening_mono (min_le_left _ _) C).trans hsub
  have hDc : IsCompact (cthickening δ C) := hCc.cthickening
  obtain ⟨⟨M, hM0, hM⟩, L, hL⟩ := KAM.ODE.gen_lip hW hF hDc hDW
  have hmemC : ∀ w : Phase (n + n), (∀ i, w.1 (Fin.castAdd n i) ∈ Icc (-Real.pi) (3 * Real.pi)) →
      assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ Q → w ∈ C := by
    intro w hw hwQ
    refine ⟨(fast w.1, assemble (fast w.2) 0 (slow w.2) (slow w.1)),
      ⟨⟨fun i => (hw i).1, fun i => (hw i).2⟩, hwQ⟩, ?_⟩
    ext j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [assemble, udAngle, fast, slow]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [assemble, udAngle, fast, slow]
  -- `stepP:p14:ud-transl`: translating by the lattice shift moves each ball into the cell's thickening
  have key : ∀ x : Phase (n + n), assemble (fast x.2) 0 (slow x.2) (slow x.1) ∈ Q →
      ∀ y ∈ closedBall x δ,
        y - fastShift (fun i => ⌊x.1 (Fin.castAdd n i) / (2 * Real.pi)⌋) ∈ cthickening δ C := by
    intro x hx y hy
    set k : Fin n → ℤ := fun i => ⌊x.1 (Fin.castAdd n i) / (2 * Real.pi)⌋ with hk
    have hpi := Real.pi_pos
    have hx' : x - fastShift k ∈ C := by
      apply hmemC
      · intro i
        have h1 := Int.floor_le (x.1 (Fin.castAdd n i) / (2 * Real.pi))
        have h2 := Int.lt_floor_add_one (x.1 (Fin.castAdd n i) / (2 * Real.pi))
        rw [le_div_iff₀ (by positivity)] at h1
        rw [div_lt_iff₀ (by positivity)] at h2
        simp only [Prod.fst_sub, Pi.sub_apply, udShift_fst_castAdd]
        constructor <;> nlinarith [h1, h2]
      · convert hx using 1
        ext j
        · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
            simp [assemble, slow, fastShift]
        · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
            simp [assemble, slow, fastShift]
    refine mem_cthickening_of_dist_le (y - fastShift k) (x - fastShift k) δ C hx' ?_
    rw [dist_sub_right]
    exact mem_closedBall.1 hy
  have hW' : ∀ x : Phase (n + n), assemble (fast x.2) 0 (slow x.2) (slow x.1) ∈ Q →
      ∀ y ∈ closedBall x δ, y ∈ W ∧
        F y = F (y - fastShift (fun i => ⌊x.1 (Fin.castAdd n i) / (2 * Real.pi)⌋)) := by
    intro x hx y hy
    set k : Fin n → ℤ := fun i => ⌊x.1 (Fin.castAdd n i) / (2 * Real.pi)⌋
    have hyW := hDW (key x hx y hy)
    have hyW' : y ∈ W := by
      have := (hWp k (y - fastShift k)).1 hyW
      rwa [sub_add_cancel] at this
    refine ⟨hyW', ?_⟩
    have := hFp k _ hyW
    rwa [sub_add_cancel] at this
  refine ⟨δ, M, L, ⟨hδpos, hM0, fun x hx y hy => (hW' x hx y hy).1, fun x hx y hy => ?_,
    fun x hx => ?_⟩, hδπ⟩
  · rw [(hW' x hx y hy).2]
    exact hM _ (key x hx y hy)
  · intro a ha b hb
    rw [(hW' x hx a ha).2, (hW' x hx b hb).2]
    have := hL (key x hx a ha) (key x hx b hb)
    simpa [edist_sub_right] using this

end KAM.Planetary

end
