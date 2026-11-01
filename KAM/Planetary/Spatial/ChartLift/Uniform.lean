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

/-!
# Uniform data on the compact fast cylinder, for `a` fast and `b` slow coordinates

Package LP-SP-LIFT, MAIN Lemma 14 for `d = 3` (`LP:MAIN L14 (468–500)`), track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

Re-typing of track P's `KAM.Planetary.uniform_data` (stated for `Phase (n + n)`) to
`Phase (a + b)`, as needed for the spatial chart `Phase (n + (n + n))` (`a = n`, `b = n + n`;
cf. amendment N12).  A `C¹` field on an open set `W` that is `2π`-periodic in the fast angles has
uniform data on the cylinder over a compact set `Q` of zero fast angles, with radius `δ ≤ π`.
-/

@[expose] public noncomputable section

open Set Metric KAM KAM.Planetary
open scoped BigOperators ContDiff NNReal

namespace KAM.Planetary.Spatial

variable {a b : ℕ}

theorem udZeroFstCastAdd (w : Phase (a + b)) (i : Fin a) :
    (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (a + b)).1 (Fin.castAdd b i) = 0 := by
  simp [assemble]

theorem udZeroSnd (w : Phase (a + b)) :
    (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (a + b)).2 = w.2 := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [assemble, fast, slow]

theorem udZeroFstNatAdd (w : Phase (a + b)) (i : Fin b) :
    (assemble (fast w.2) 0 (slow w.2) (slow w.1) : Phase (a + b)).1 (Fin.natAdd a i) =
      w.1 (Fin.natAdd a i) := by
  simp [assemble, slow]

theorem udShiftFstCastAdd (k : Fin a → ℤ) (i : Fin a) :
    (fastShift (b := b) k : Phase (a + b)).1 (Fin.castAdd b i) = 2 * Real.pi * (k i : ℝ) := by
  simp [fastShift]

/-- Adding a fast angle block `lam` to the first component. -/
def udAngleNM (lam : Fin a → ℝ) : Phase (a + b) := (Fin.append lam (0 : Fin b → ℝ), 0)

theorem udAngleNM_continuous :
    Continuous (fun p : (Fin a → ℝ) × Phase (a + b) => p.2 + udAngleNM p.1) := by
  refine continuous_snd.add (Continuous.prodMk ?_ continuous_const)
  refine continuous_pi fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.append_left]; exact (continuous_apply i).comp continuous_fst
  · simp only [Fin.append_right]; exact continuous_const

theorem udCellNM_isCompact {Q : Set (Phase (a + b))} (hQ : IsCompact Q) :
    IsCompact ((fun p : (Fin a → ℝ) × Phase (a + b) => p.2 + udAngleNM p.1) ''
      (Icc (fun _ : Fin a => -Real.pi) (fun _ => 3 * Real.pi) ×ˢ Q)) :=
  (isCompact_Icc.prod hQ).image udAngleNM_continuous

/-- Re-typed `uniform_data`: uniform data on the cylinder over a compact set of zero angles. -/
theorem uniformDataNM {W Q : Set (Phase (a + b))} (hW : IsOpen W)
    {F : Phase (a + b) → Phase (a + b)} (hF : ContDiffOn ℝ 1 F W)
    (hWp : ∀ k : Fin a → ℤ, ∀ w, w ∈ W ↔ w + fastShift k ∈ W)
    (hFp : ∀ k : Fin a → ℤ, ∀ w ∈ W, F (w + fastShift k) = F w)
    (hQ : IsCompact Q) (hQ0 : ∀ w ∈ Q, fast w.1 = 0)
    (hQW : ∀ w : Phase (a + b),
      assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ Q → w ∈ W) :
    ∃ (delta M : ℝ) (L : ℝ≥0), KAM.ODE.UniformData F W
      {w | assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ Q} delta M L ∧ delta ≤ Real.pi := by
  set C := (fun p : (Fin a → ℝ) × Phase (a + b) => p.2 + udAngleNM p.1) ''
      (Icc (fun _ : Fin a => -Real.pi) (fun _ => 3 * Real.pi) ×ˢ Q) with hC
  have hCc : IsCompact C := udCellNM_isCompact hQ
  have hCW : C ⊆ W := by
    rintro y ⟨⟨lam, z⟩, ⟨-, hz⟩, rfl⟩
    refine hQW _ ?_
    have h0 := hQ0 z hz
    convert hz using 1
    ext j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have := congrFun h0 i
        simp [assemble, udAngleNM, fast] at this ⊢
        exact this.symm
      · simp [assemble, udAngleNM, slow]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [assemble, udAngleNM, fast, slow]
  obtain ⟨δ₀, hδ₀, hsub⟩ := hCc.exists_cthickening_subset_open hW hCW
  have hδpos : 0 < min δ₀ Real.pi := lt_min hδ₀ Real.pi_pos
  have hδπ : min δ₀ Real.pi ≤ Real.pi := min_le_right _ _
  set δ := min δ₀ Real.pi with hδ
  have hDW : cthickening δ C ⊆ W := (cthickening_mono (min_le_left _ _) C).trans hsub
  have hDc : IsCompact (cthickening δ C) := hCc.cthickening
  obtain ⟨⟨M, hM0, hM⟩, L, hL⟩ := KAM.ODE.gen_lip hW hF hDc hDW
  have hmemC : ∀ w : Phase (a + b),
      (∀ i, w.1 (Fin.castAdd b i) ∈ Icc (-Real.pi) (3 * Real.pi)) →
      assemble (fast w.2) 0 (slow w.2) (slow w.1) ∈ Q → w ∈ C := by
    intro w hw hwQ
    refine ⟨(fast w.1, assemble (fast w.2) 0 (slow w.2) (slow w.1)),
      ⟨⟨fun i => (hw i).1, fun i => (hw i).2⟩, hwQ⟩, ?_⟩
    ext j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [assemble, udAngleNM, fast, slow]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [assemble, udAngleNM, fast, slow]
  have key : ∀ x : Phase (a + b), assemble (fast x.2) 0 (slow x.2) (slow x.1) ∈ Q →
      ∀ y ∈ closedBall x δ,
        y - fastShift (fun i => ⌊x.1 (Fin.castAdd b i) / (2 * Real.pi)⌋) ∈ cthickening δ C := by
    intro x hx y hy
    set k : Fin a → ℤ := fun i => ⌊x.1 (Fin.castAdd b i) / (2 * Real.pi)⌋ with hk
    have hpi := Real.pi_pos
    have hx' : x - fastShift k ∈ C := by
      apply hmemC
      · intro i
        have h1 := Int.floor_le (x.1 (Fin.castAdd b i) / (2 * Real.pi))
        have h2 := Int.lt_floor_add_one (x.1 (Fin.castAdd b i) / (2 * Real.pi))
        rw [le_div_iff₀ (by positivity)] at h1
        rw [div_lt_iff₀ (by positivity)] at h2
        simp only [Prod.fst_sub, Pi.sub_apply, udShiftFstCastAdd]
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
  have hW' : ∀ x : Phase (a + b), assemble (fast x.2) 0 (slow x.2) (slow x.1) ∈ Q →
      ∀ y ∈ closedBall x δ, y ∈ W ∧
        F y = F (y - fastShift (fun i => ⌊x.1 (Fin.castAdd b i) / (2 * Real.pi)⌋)) := by
    intro x hx y hy
    set k : Fin a → ℤ := fun i => ⌊x.1 (Fin.castAdd b i) / (2 * Real.pi)⌋
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
  · intro a' ha' b' hb'
    rw [(hW' x hx a' ha').2, (hW' x hx b' hb').2]
    have := hL (key x hx a' ha') (key x hx b' hb')
    simpa [edist_sub_right] using this

end KAM.Planetary.Spatial

end
