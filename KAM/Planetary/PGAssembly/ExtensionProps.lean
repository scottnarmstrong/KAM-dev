/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ExtensionTubeP

/-!
# P Part 5: properties of the periodized extension

For `delta ≤ T.rho`: every point of `extensionDomain d delta` admits a valid shift; `tubeP` is
holomorphic, jointly continuous, periodic, bounded, and agrees with `d.P` at real points of the
closed cylinder (`stepP:p5:ext-per`, `bpP:p5:ext`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-EX.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology Function

namespace KAM.Planetary

variable {a b : ℕ}

theorem PGTube.exists_valid {d : PGData a b} (T : PGTube d) {delta : ℝ} (hδ : delta ≤ T.rho)
    {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {z : PGComplexPhase (a + b)}
    (hz : z ∈ extensionDomain d delta) : ∃ k, T.Valid mu z k := by
  obtain ⟨w, hw1, hw2, hw3⟩ := hz
  have hpi := Real.pi_pos
  set k : Fin a → ℤ := fun i => ⌊w.1 (Fin.castAdd b i) / (2 * Real.pi)⌋ with hk
  have hw' : w - fastShift k ∈ pgWbox d := by
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have h := Int.floor_le (w.1 (Fin.castAdd b i) / (2 * Real.pi))
      have h' := Int.lt_floor_add_one (w.1 (Fin.castAdd b i) / (2 * Real.pi))
      rw [le_div_iff₀ (by positivity)] at h
      rw [div_lt_iff₀ (by positivity)] at h'
      simp only [Prod.fst_sub, Pi.sub_apply, fastShift_fst_castAdd]
      constructor <;> nlinarith [h, h']
    · have : blockFast (w - fastShift (b := b) k).2 = blockFast w.2 := by
        funext i; simp [blockFast, fastShift]
      rw [this]; exact hw1
    · have h1 : blockSlow (w - fastShift (b := b) k).2 = blockSlow w.2 := by
        funext i; simp [blockSlow, fastShift]
      have h2 : blockSlow (w - fastShift (b := b) k).1 = blockSlow w.1 := by
        funext i; simp [blockSlow, fastShift]
      rw [h1, h2]; exact hw2
  refine ⟨k, mem_actionNbhd_iff.2 ⟨packVec mu (w - fastShift k),
    ⟨(mu, w - fastShift k), ⟨hmu, hw'⟩, rfl⟩, ?_⟩⟩
  rw [realInclusion_packVec, packVec_sub, sub_self]
  have : z - KAM.realInclusion₂ (a + b) (fastShift k) -
      KAM.realInclusion₂ (a + b) (w - fastShift k) = z - KAM.realInclusion₂ (a + b) w := by
    rw [map_sub]; abel
  rw [this]
  exact (norm_packVec_zero_le _).trans_lt (hw3.trans_le hδ)

theorem PGTube.P_bound {d : PGData a b} (T : PGTube d) {delta : ℝ} (hδ : delta ≤ T.rho)
    {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {z : PGComplexPhase (a + b)}
    (hz : z ∈ extensionDomain d delta) : ‖T.P mu z‖ ≤ T.M := by
  obtain ⟨k, hk⟩ := T.exists_valid hδ hmu hz
  rw [T.P_eq hk]
  exact T.hbd _ hk

theorem PGTube.P_periodic {d : PGData a b} (T : PGTube d) {delta : ℝ} (hδ : delta ≤ T.rho)
    {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {z : PGComplexPhase (a + b)}
    (hz : z ∈ extensionDomain d delta) (m : Fin a → ℤ) :
    T.P mu (z + KAM.realInclusion₂ (a + b) (fastShift m)) = T.P mu z := by
  obtain ⟨k, hk⟩ := T.exists_valid hδ hmu hz
  have hk' : T.Valid mu (z + KAM.realInclusion₂ (a + b) (fastShift m)) (k + m) := by
    unfold PGTube.Valid
    have : z + KAM.realInclusion₂ (a + b) (fastShift m) -
        KAM.realInclusion₂ (a + b) (fastShift (k + m)) =
        z - KAM.realInclusion₂ (a + b) (fastShift k) := by
      rw [fastShift_add, map_add]; abel
    rw [this]; exact hk
  rw [T.P_eq hk', T.P_eq hk]
  congr 2
  rw [fastShift_add, map_add]; abel

theorem PGTube.P_holo {d : PGData a b} (T : PGTube d) {delta : ℝ} (hδ : delta ≤ T.rho)
    {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) :
    DifferentiableOn ℂ (T.P mu) (extensionDomain d delta) := by
  intro z hz
  obtain ⟨k, hk⟩ := T.exists_valid hδ hmu hz
  set c := KAM.realInclusion₂ (a + b) (fastShift k)
  set U := {z' : PGComplexPhase (a + b) | T.Valid mu z' k} with hU
  have hUo : IsOpen U :=
    (isOpen_actionNbhd (pgX d) T.rho).preimage
      ((continuous_packVec_sub c).comp (continuous_const.prodMk continuous_id))
  have hdiff : DifferentiableOn ℂ (fun z' => T.F (packVec (mu : ℂ) (z' - c))) U :=
    T.hF.comp (differentiable_packVec_sub (mu : ℂ) c).differentiableOn fun z' hz' => hz'
  have h2 : DifferentiableOn ℂ (T.P mu) U := hdiff.congr fun z' hz' => T.P_eq hz'
  exact (h2.differentiableAt (hUo.mem_nhds hk)).differentiableWithinAt

theorem PGTube.P_continuous {d : PGData a b} (T : PGTube d) {delta : ℝ} (hδ : delta ≤ T.rho) :
    ContinuousOn (fun p : ℝ × PGComplexPhase (a + b) => T.P p.1 p.2)
      (Icc 0 d.mu0 ×ˢ extensionDomain d delta) := by
  rintro ⟨mu, z⟩ ⟨hmu, hz⟩
  obtain ⟨k, hk⟩ := T.exists_valid hδ hmu hz
  set c := KAM.realInclusion₂ (a + b) (fastShift k)
  set U := {p : ℝ × PGComplexPhase (a + b) | T.Valid p.1 p.2 k} with hU
  have hUo : IsOpen U := (isOpen_actionNbhd (pgX d) T.rho).preimage (continuous_packVec_sub c)
  have hcont : ContinuousOn (fun p : ℝ × PGComplexPhase (a + b) =>
      T.F (packVec (p.1 : ℂ) (p.2 - c))) U :=
    T.hF.continuousOn.comp (continuous_packVec_sub c).continuousOn fun p hp => hp
  have h2 : ContinuousOn (fun p : ℝ × PGComplexPhase (a + b) => T.P p.1 p.2) U :=
    hcont.congr fun p hp => T.P_eq hp
  exact (h2.continuousAt (hUo.mem_nhds hk)).continuousWithinAt

theorem pg_period_closure (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {w : Phase (a + b)} (hw : w ∈ closure (cylinder d.V d.r0 : Set (Phase (a + b))))
    (k : Fin a → ℤ) : d.P mu (w - fastShift k) = d.P mu w := by
  have hcont : ∀ z ∈ closure (cylinder d.V d.r0 : Set (Phase (a + b))),
      ContinuousAt (fun z : Phase (a + b) => d.P mu z) z := by
    intro z hz
    have h := (d.hP (mu, z) ⟨hmu, hz⟩).continuousAt
    exact h.comp (f := fun z : Phase (a + b) => (mu, z)) (x := z) (by fun_prop)
  have hcont' : ∀ z ∈ closure (cylinder d.V d.r0 : Set (Phase (a + b))),
      ContinuousAt (fun z : Phase (a + b) => d.P mu (z - fastShift k)) z := by
    intro z hz
    exact (hcont _ (closure_cylinder_sub_fastShift hz k)).comp
      (f := fun z : Phase (a + b) => z - fastShift k) (x := z) (by fun_prop)
  have heq : EqOn (fun z : Phase (a + b) => d.P mu (z - fastShift k))
      (fun z => d.P mu z) (cylinder d.V d.r0) := by
    intro z hz
    have := d.hperiod mu hmu _ (cylinder_sub_fastShift hz k) k
    rw [sub_add_cancel] at this
    exact this.symm
  exact heq.of_subset_closure (fun z hz => (hcont' z hz).continuousWithinAt)
    (fun z hz => (hcont z hz).continuousWithinAt) subset_closure subset_rfl hw

theorem PGTube.P_agrees {d : PGData a b} (T : PGTube d) {delta : ℝ} (hδ : delta ≤ T.rho)
    {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {w : Phase (a + b)}
    (hw : w ∈ closure (cylinder d.V d.r0 : Set (Phase (a + b))))
    (hwd : KAM.realInclusion₂ (a + b) w ∈ extensionDomain d delta) :
    T.P mu (KAM.realInclusion₂ (a + b) w) = (d.P mu w : ℂ) := by
  obtain ⟨k, hk⟩ := T.exists_valid hδ hmu hwd
  have hk' : KAM.realInclusion _ (packVec mu (w - fastShift k)) ∈
      KAM.actionNbhd (pgX d) T.rho := by
    rw [realInclusion_packVec, map_sub]; exact hk
  rw [T.P_eq hk, ← map_sub, ← realInclusion_packVec, T.hreal _ hk', pgF_packVec,
    pg_period_closure d hmu hw k]

end KAM.Planetary

end
