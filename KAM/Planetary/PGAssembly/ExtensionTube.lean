/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ExtensionPack
public import KAM.Planetary.PGAssembly.ExtensionPeriodic

/-!
# P Part 5: the compact period box and the packed real function (`stepP:p5:ext-loc`)

The compact one-period box `pgX d ⊆ ℝ^(n+n+1)` (parameter in `[0, mu0]`, fast angles in `[0, 2π]`,
fast action in `closure V`, slow part of norm at most `r0/2`), the packed real function `pgF d`,
and the real-analytic input needed for the complexification:
`pgF d` is analytic on the packed closed cylinder and shift-periodic near `pgX d`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-EX.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology Function

namespace KAM.Planetary

variable {a b : ℕ}

/-- One period of the real phase points over the closed action set, with slow part `≤ r0/2`. -/
def pgWbox (d : PGData a b) : Set (Phase (a + b)) :=
  {w | (∀ i : Fin a, w.1 (Fin.castAdd b i) ∈ Icc (0 : ℝ) (2 * Real.pi)) ∧
    blockFast w.2 ∈ closure d.V ∧ ‖(blockSlow w.2, blockSlow w.1)‖ ≤ d.r0 / 2}

/-- The compact packed box `[0, mu0] × pgWbox`. -/
def pgX (d : PGData a b) : Set (Fin ((a + b) + (a + b) + 1) → ℝ) :=
  (fun p : ℝ × Phase (a + b) => packVec p.1 p.2) '' (Icc 0 d.mu0 ×ˢ pgWbox d)

/-- The packed real function. -/
def pgF (d : PGData a b) (y : Fin ((a + b) + (a + b) + 1) → ℝ) : ℝ :=
  d.P (unpackL (a + b) y).1 (unpackL (a + b) y).2

theorem pgF_packVec (d : PGData a b) (mu : ℝ) (z : Phase (a + b)) :
    pgF d (packVec mu z) = d.P mu z := by
  simp [pgF, unpackL_packVec]

theorem continuous_blockFast_real :
    Continuous fun v : Fin (a + b) → ℝ => blockFast (b := b) v := by
  refine continuous_pi fun i => ?_
  exact continuous_apply _

theorem continuous_blockSlow_real :
    Continuous fun v : Fin (a + b) → ℝ => blockSlow (a := a) v := by
  refine continuous_pi fun i => ?_
  exact continuous_apply _

theorem isClosed_pgWbox (d : PGData a b) : IsClosed (pgWbox d) := by
  have h1 : IsClosed {w : Phase (a + b) | ∀ i : Fin a,
      w.1 (Fin.castAdd b i) ∈ Icc (0 : ℝ) (2 * Real.pi)} := by
    rw [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_Icc.preimage ((continuous_apply _).comp continuous_fst)
  have h2 : IsClosed {w : Phase (a + b) | blockFast w.2 ∈ closure d.V} :=
    isClosed_closure.preimage (continuous_blockFast_real.comp continuous_snd)
  have h3 : IsClosed {w : Phase (a + b) | ‖(blockSlow w.2, blockSlow w.1)‖ ≤ d.r0 / 2} :=
    isClosed_le (continuous_norm.comp ((continuous_blockSlow_real.comp continuous_snd).prodMk
        (continuous_blockSlow_real.comp continuous_fst))) continuous_const
  exact h1.inter (h2.inter h3)

theorem isBounded_pgWbox (d : PGData a b) : Bornology.IsBounded (pgWbox d) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin a → ℝ)).1
    d.hVb.closure
  refine (Metric.isBounded_iff_subset_closedBall 0).2
    ⟨max (max (2 * Real.pi) (R)) (d.r0 / 2), fun w hw => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hw
  have hR' : ‖blockFast w.2‖ ≤ R := by simpa using hR h2
  have hpq := h3
  rw [Prod.norm_def] at hpq
  have hp : ‖blockSlow w.2‖ ≤ d.r0 / 2 := (le_max_left _ _).trans (by simpa using hpq)
  have hq : ‖blockSlow w.1‖ ≤ d.r0 / 2 := (le_max_right _ _).trans (by simpa using hpq)
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (le_max_of_le_left
      (by positivity)))).2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := h1 i
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [this.1, show (0:ℝ) ≤ max (max (2 * Real.pi) R) (d.r0 / 2) from
        le_max_of_le_left (le_max_of_le_left (by positivity))],
        this.2.trans ((le_max_left _ _).trans (le_max_left _ _))⟩
    · exact (norm_le_pi_norm (blockSlow w.1) i).trans (hq.trans (le_max_right _ _))
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (le_max_of_le_left
      (by positivity)))).2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact (norm_le_pi_norm (blockFast w.2) i).trans (hR'.trans' le_rfl |>.trans
        ((le_max_right _ _).trans (le_max_left _ _)))
    · exact (norm_le_pi_norm (blockSlow w.2) i).trans (hp.trans (le_max_right _ _))

theorem isCompact_pgWbox (d : PGData a b) : IsCompact (pgWbox d) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_pgWbox d) (isBounded_pgWbox d)

theorem isCompact_pgX (d : PGData a b) : IsCompact (pgX d) :=
  ((isCompact_Icc).prod (isCompact_pgWbox d)).image continuous_packVec_real

theorem mem_actionNbhd_mono {N : ℕ} {X : Set (Fin N → ℝ)} {r r' : ℝ} (h : r ≤ r')
    {z : Fin N → ℂ} (hz : z ∈ KAM.actionNbhd X r) : z ∈ KAM.actionNbhd X r' :=
  mem_actionNbhd_iff.2 (let ⟨J, hJ, hz⟩ := mem_actionNbhd_iff.1 hz; ⟨J, hJ, hz.trans_le h⟩)

theorem isOpen_actionNbhd {N : ℕ} (X : Set (Fin N → ℝ)) (r : ℝ) :
    IsOpen (KAM.actionNbhd X r) := by
  have : KAM.actionNbhd X r = ⋃ J ∈ X, ball (KAM.realInclusion N J) r := by
    ext z
    simp only [mem_actionNbhd_iff, mem_iUnion, mem_ball_iff_norm, exists_prop]
  rw [this]
  exact isOpen_biUnion fun _ _ => isOpen_ball

theorem cylinder_sub_fastShift {V : Set (Fin a → ℝ)} {r : ℝ} {z : Phase (a + b)}
    (hz : z ∈ (cylinder V r : Set (Phase (a + b)))) (k : Fin a → ℤ) :
    z - fastShift k ∈ (cylinder V r : Set (Phase (a + b))) := by
  simpa [cylinder, fast, slow, fastShift] using hz

theorem closure_cylinder_sub_fastShift {V : Set (Fin a → ℝ)} {r : ℝ} {z : Phase (a + b)}
    (hz : z ∈ closure (cylinder V r : Set (Phase (a + b)))) (k : Fin a → ℤ) :
    z - fastShift k ∈ closure (cylinder V r : Set (Phase (a + b))) := by
  have hc : Continuous fun z : Phase (a + b) => z - fastShift k := continuous_sub_right _
  have := image_closure_subset_closure_image hc ⟨z, hz, rfl⟩
  exact closure_mono (by rintro _ ⟨w, hw, rfl⟩; exact cylinder_sub_fastShift hw k) this

theorem isOpen_cylinder (V : Set (Fin a → ℝ)) (hV : IsOpen V) (r : ℝ) :
    IsOpen (cylinder V r : Set (Phase (a + b))) := by
  have h1 : IsOpen {z : Phase (a + b) | fast z.2 ∈ V} :=
    hV.preimage ((show Continuous fun v : Fin (a + b) → ℝ => fast (b := b) v from
      continuous_pi fun i => continuous_apply _).comp continuous_snd)
  have h2 : IsOpen {z : Phase (a + b) |
      ∀ j : Fin b, (slow z.2 j) ^ 2 + (slow z.1 j) ^ 2 < r ^ 2} := by
    rw [ofPred_forall]
    refine isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
    have h : ∀ v : Fin (a + b) → ℝ,
        Continuous fun z : Phase (a + b) => slow (a := a) (b := b) z.2 j := by
      intro v; exact (continuous_apply _).comp continuous_snd
    have h' : Continuous fun z : Phase (a + b) => slow (a := a) (b := b) z.1 j :=
      (continuous_apply _).comp continuous_fst
    exact ((h 0).pow 2).add (h'.pow 2)
  exact h1.inter h2

theorem pgWbox_subset_closure (d : PGData a b) {w : Phase (a + b)} (hw : w ∈ pgWbox d) :
    w ∈ closure (cylinder d.V d.r0 : Set (Phase (a + b))) := by
  obtain ⟨-, h2, h3⟩ := hw
  set φ : (Fin a → ℝ) → Phase (a + b) := fun I => (w.1, Fin.append I (blockSlow w.2)) with hφ
  have hcont : Continuous φ := by
    refine continuous_const.prodMk (continuous_pi fun j => ?_)
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [Fin.append_left, Fin.append_right]
    · exact continuous_apply i
    · exact continuous_const
  have hsub : φ '' d.V ⊆ cylinder d.V d.r0 := by
    rintro _ ⟨I, hI, rfl⟩
    have hf : fast (Fin.append I (blockSlow w.2)) = I := funext fun i => Fin.append_left _ _ i
    refine ⟨by show fast (Fin.append I (blockSlow w.2)) ∈ d.V; rw [hf]; exact hI, fun j => ?_⟩
    have hpq := h3
    rw [Prod.norm_def] at hpq
    have hp : |blockSlow w.2 j| ≤ d.r0 / 2 :=
      (norm_le_pi_norm (blockSlow w.2) j).trans' (by simp) |>.trans ((le_max_left _ _).trans hpq)
    have hq : |blockSlow w.1 j| ≤ d.r0 / 2 :=
      (norm_le_pi_norm (blockSlow w.1) j).trans' (by simp) |>.trans ((le_max_right _ _).trans hpq)
    have hr := d.hr0
    have h1 : (blockSlow w.2 j) ^ 2 ≤ (d.r0 / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hp 2
    have h2' : (blockSlow w.1 j) ^ 2 ≤ (d.r0 / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hq 2
    simp only [φ, slow, Fin.append_right]
    change (blockSlow w.2 j) ^ 2 + (blockSlow w.1 j) ^ 2 < d.r0 ^ 2
    nlinarith
  have hw : w = φ (blockFast w.2) := by
    refine Prod.ext rfl ?_
    show w.2 = Fin.append (blockFast w.2) (blockSlow w.2)
    exact (Fin.append_castAdd_natAdd (f := w.2)).symm
  rw [hw]
  exact closure_mono hsub (image_closure_subset_closure_image hcont ⟨_, h2, rfl⟩)

end KAM.Planetary

end
