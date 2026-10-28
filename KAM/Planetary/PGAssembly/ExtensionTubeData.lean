/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ExtensionTube

/-!
# P Part 5: the thin periodic complexification (`stepP:p5:ext-loc`, `stepP:p5:ext-glue`)

`PGTube d`: a holomorphic bounded `F` on the thin tube `actionNbhd (pgX d) rho` around the packed
period box, real-analytic complexification of `pgF d` on the real points of the tube, with the
shift identities `F x = F (x - ι (pgShift m))` for `|m_i| ≤ 1`.
Proof: `compact_real_complexification` (P5-CG) on `pgX d`, the identity theorem for the finitely
many shifts (`exists_delta_shift_eq`, using `hperiod` on the open packed cylinder) and `tube_glue`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-EX.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology Function

namespace KAM.Planetary

variable {a b : ℕ}

/-- The packed real shift by `2π m` in the fast angles. -/
def pgShift (a b : ℕ) (m : Fin a → ℤ) : Fin ((a + b) + (a + b) + 1) → ℝ :=
  packVec (0 : ℝ) (fastShift (b := b) m)

/-- The packed closed cylinder over the parameter interval. -/
def pgK (d : PGData a b) : Set (Fin ((a + b) + (a + b) + 1) → ℝ) :=
  {y | (unpackL (a + b) y).1 ∈ Icc 0 d.mu0 ∧
    (unpackL (a + b) y).2 ∈ closure (cylinder d.V d.r0 : Set (Phase (a + b)))}

/-- The open packed cylinder over the open parameter interval. -/
def pgG (d : PGData a b) : Set (Fin ((a + b) + (a + b) + 1) → ℝ) :=
  {y | (unpackL (a + b) y).1 ∈ Ioo 0 d.mu0 ∧
    (unpackL (a + b) y).2 ∈ (cylinder d.V d.r0 : Set (Phase (a + b)))}

theorem packVec_mem_pgK (d : PGData a b) {mu : ℝ} {w : Phase (a + b)} (hmu : mu ∈ Icc 0 d.mu0)
    (hw : w ∈ closure (cylinder d.V d.r0 : Set (Phase (a + b)))) : packVec mu w ∈ pgK d := by
  simp only [pgK, mem_ofPred_eq, unpackL_packVec]
  exact ⟨hmu, hw⟩

theorem pgX_subset_pgK (d : PGData a b) : pgX d ⊆ pgK d := by
  rintro _ ⟨⟨mu, w⟩, ⟨hmu, hw⟩, rfl⟩
  exact packVec_mem_pgK d hmu (pgWbox_subset_closure d hw)

theorem analyticOnNhd_pgF (d : PGData a b) : AnalyticOnNhd ℝ (pgF d) (pgK d) := by
  have h := d.hP.comp (s := pgK d) (f := unpackL (a + b))
    ((unpackL (a + b)).analyticOnNhd _) (fun y hy => ⟨hy.1, hy.2⟩)
  exact h

theorem isOpen_pgG (d : PGData a b) : IsOpen (pgG d) := by
  have := (isOpen_Ioo (a := (0 : ℝ)) (b := d.mu0)).prod (isOpen_cylinder (b := b) d.V d.hV d.r0)
  exact this.preimage (unpackL (a + b)).continuous

theorem pgX_subset_closure_pgG (d : PGData a b) : pgX d ⊆ closure (pgG d) := by
  rintro _ ⟨⟨mu, w⟩, ⟨hmu, hw⟩, rfl⟩
  set Gp : Set (ℝ × Phase (a + b)) := Ioo 0 d.mu0 ×ˢ cylinder d.V d.r0 with hGp
  have hcl : (mu, w) ∈ closure Gp := by
    rw [hGp, closure_prod_eq, closure_Ioo d.hmu0.ne]
    exact ⟨hmu, pgWbox_subset_closure d hw⟩
  have h1 := image_closure_subset_closure_image continuous_packVec_real ⟨_, hcl, rfl⟩
  refine closure_mono ?_ h1
  rintro _ ⟨⟨mu', z⟩, hz, rfl⟩
  simp only [pgG, mem_ofPred_eq, unpackL_packVec]
  exact hz

/-- The finite set of packed shifts with `|m_i| ≤ 1`. -/
def pgShiftSet (a b : ℕ) : Finset (Fin ((a + b) + (a + b) + 1) → ℝ) :=
  (Fintype.piFinset fun _ : Fin a => Finset.Icc (-1 : ℤ) 1).image (pgShift a b)

theorem pgShift_mem (m : Fin a → ℤ) (hm : ∀ i, |m i| ≤ 1) : pgShift a b m ∈ pgShiftSet a b := by
  refine Finset.mem_image.2 ⟨m, ?_, rfl⟩
  refine Fintype.mem_piFinset.2 fun i => ?_
  rw [Finset.mem_Icc]
  exact abs_le.1 (hm i)

theorem packVec_sub_pgShift (mu : ℝ) (z : Phase (a + b)) (m : Fin a → ℤ) :
    packVec mu z - pgShift a b m = packVec mu (z - fastShift m) := by
  rw [pgShift, packVec_sub, sub_zero]

theorem exists_pg_delta (d : PGData a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ pgShiftSet a b, ∀ y : Fin ((a + b) + (a + b) + 1) → ℝ,
      (∃ J ∈ pgX d, dist y J < δ) → pgF d (y - s) = pgF d y := by
  have hana := analyticOnNhd_pgF d
  refine exists_delta_shift_eq (isCompact_pgX d) (pgShiftSet a b) (isOpen_pgG d)
    (pgX_subset_closure_pgG d) (fun x hx => hana x (pgX_subset_pgK d hx)) ?_ ?_
  · intro x hx s hs
    obtain ⟨⟨mu, w⟩, ⟨hmu, hw⟩, rfl⟩ := hx
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hs
    show AnalyticAt ℝ (pgF d) (packVec mu w - pgShift a b m)
    rw [packVec_sub_pgShift]
    exact hana _ (packVec_mem_pgK d hmu
      (closure_cylinder_sub_fastShift (pgWbox_subset_closure d hw) m))
  · intro y hy s hs
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hs
    have hy' := packVec_unpackL y
    set mu := (unpackL (a + b) y).1
    set z := (unpackL (a + b) y).2
    have hyeq : y = packVec mu z := hy'.symm
    rw [hyeq, packVec_sub_pgShift, pgF_packVec, pgF_packVec]
    have hz := cylinder_sub_fastShift hy.2 m
    have := d.hperiod mu (Ioo_subset_Icc_self hy.1) _ hz m
    rw [sub_add_cancel] at this
    exact this.symm

/-- The thin periodic complexification of the packed real function. -/
structure PGTube (d : PGData a b) where
  rho : ℝ
  M : ℝ
  F : (Fin ((a + b) + (a + b) + 1) → ℂ) → ℂ
  rho_pos : 0 < rho
  rho_le : rho ≤ 1 / 2
  hF : DifferentiableOn ℂ F (KAM.actionNbhd (pgX d) rho)
  hbd : ∀ x ∈ KAM.actionNbhd (pgX d) rho, ‖F x‖ ≤ M
  hreal : ∀ y : Fin ((a + b) + (a + b) + 1) → ℝ,
    KAM.realInclusion _ y ∈ KAM.actionNbhd (pgX d) rho →
      F (KAM.realInclusion _ y) = (pgF d y : ℂ)
  hglue : ∀ m : Fin a → ℤ, (∀ i, |m i| ≤ 1) → ∀ x ∈ KAM.actionNbhd (pgX d) rho,
    x - KAM.realInclusion _ (pgShift a b m) ∈ KAM.actionNbhd (pgX d) rho →
      F x = F (x - KAM.realInclusion _ (pgShift a b m))

theorem pgTube_exists (d : PGData a b) : Nonempty (PGTube d) := by
  obtain ⟨rho0, M, F, hrho0, hM, hF, hreal, hbd⟩ :=
    compact_real_complexification (isCompact_pgX d) ((analyticOnNhd_pgF d).mono (pgX_subset_pgK d))
  obtain ⟨δ, hδ, hper⟩ := exists_pg_delta d
  set rho := min (rho0 / 3) (min δ (1 / 2)) with hrho
  have hr0 : 0 < rho := lt_min (by positivity) (lt_min hδ (by norm_num))
  have hr1 : rho ≤ rho0 / 3 := min_le_left _ _
  have hr2 : rho ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : rho ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : ∀ z ∈ KAM.actionNbhd (pgX d) rho, z ∈ KAM.actionNbhd (pgX d) rho0 := fun z hz =>
    mem_actionNbhd_mono (by linarith) hz
  refine ⟨⟨rho, M, F, hr0, hr3, hF.mono hsub, fun x hx => hbd x (hsub x hx),
    fun y hy => hreal y (hsub _ hy), ?_⟩⟩
  intro m hm x hx hxs
  exact tube_glue hr0 (by linarith) hF hreal
    (fun y hy => hper _ (pgShift_mem m hm) y (by
      obtain ⟨J, hJ, hyJ⟩ := hy
      exact ⟨J, hJ, hyJ.trans_le hr2⟩)) hx hxs

end KAM.Planetary

end
