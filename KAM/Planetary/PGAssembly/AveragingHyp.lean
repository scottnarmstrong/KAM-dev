/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingSmall
public import KAM.Planetary.PGAssembly.AveragingReal

/-!
# P Part 5: the source hypotheses of oscillator averaging (`bpP:p5:avg`)

`pg_osc_hyp` assembles the record `OscHyp` for the normalized data: holomorphy, periodicity and
reality of `pgOscE • pgOscP` on the P2 domain, its weighted bound, the divisor and smallness
conditions.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ}

theorem strip_mono {N : ℕ} {S S' : ℝ} (h : S ≤ S') {θ : Fin N → ℂ}
    (hθ : θ ∈ KAM.complexStrip N S) : θ ∈ KAM.complexStrip N S' :=
  fun i => (hθ i).trans_le h

theorem normalize_eq_assemble (z : CPhase (a+b)) :
    pgOscNormalize z = assembleComplex (blockFast z.2) ((2*Real.pi:ℂ) • blockFast z.1)
      ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.2) ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.1) :=
  rfl

theorem normalize_mem_extensionDomain (h : admissible d (pgRstar d) r mu) {s' S : ℝ}
    (hs' : s' ≤ (pgExtension d).delta/2) (hS : S ≤ pgOscWidth d) {z : CPhase (a+b)}
    (hz : z ∈ oscDom (checkedCore d r mu) s' (pgOscEpsilon d) (pgOscEpsilon d) S) :
    pgOscNormalize z ∈ extensionDomain d (pgExtension d).delta := by
  obtain ⟨z1, z2, z3, z4⟩ := mem_oscDom_pg.1 hz
  have hs := sqrt_two_pi_pos
  have hpi := Real.pi_pos
  have hδ := (pgExtension d).delta_pos
  rw [normalize_eq_assemble]
  have hI : blockFast z.2 ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2) := by
    obtain ⟨J, hJ, hIJ⟩ := z2
    exact ⟨J, subset_closure (checkedCore_subset_V d r mu hJ), hIJ.trans_le hs'⟩
  have hε : ∀ v : Fin b → ℂ, ‖v‖ < pgOscEpsilon d →
      ‖(Real.sqrt (2*Real.pi):ℂ) • v‖ < (pgExtension d).delta/4 := by
    intro v hv
    rw [norm_real_smul_lt_iff hs]
    refine hv.trans_le ?_
    unfold pgOscEpsilon
    exact div_le_div_of_nonneg_right (pgOscRadius_le_delta d) hs.le
  have hx : ‖((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.1, (Real.sqrt (2*Real.pi):ℂ) • blockSlow z.2)‖ <
      (pgExtension d).delta/4 := by
    rw [Prod.norm_def]; exact max_lt (hε _ z4) (hε _ z3)
  refine strip_mem_extensionDomain d hδ hI hx (strip_mono ?_ z1)
  unfold pgOscWidth at hS
  have : pgWidth d/(2*Real.pi) ≤ (pgExtension d).delta/(2*Real.pi) :=
    div_le_div_of_nonneg_right (by rw [pgWidth_eq]; linarith) (by positivity)
  exact hS.trans this

theorem pgOscNormalize_real (x : Phase (a+b)) :
    pgOscNormalize (KAM.realInclusion₂ (a+b) x) = KAM.realInclusion₂ (a+b)
      (Fin.append ((2*Real.pi) • blockFast x.1) ((Real.sqrt (2*Real.pi)) • blockSlow x.1),
       Fin.append (blockFast x.2) ((Real.sqrt (2*Real.pi)) • blockSlow x.2)) := by
  refine Prod.ext ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [pgOscNormalize, blockFast, blockSlow]

theorem natAdd_ne_castAdd (k : Fin b) (j : Fin a) : Fin.natAdd a k ≠ Fin.castAdd b j := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := j.isLt
  simp at h1
  omega

theorem pgOscNormalize_shift (z : CPhase (a+b)) (j : Fin a) :
    pgOscNormalize (z.1 + Pi.single (Fin.castAdd b j) 1, z.2) =
      pgOscNormalize z + KAM.realInclusion₂ (a+b) (fastShift (Pi.single j (1:ℤ))) := by
  have hna := natAdd_ne_castAdd (a := a) (b := b)
  refine Prod.ext ?_ ?_ <;> funext i <;> refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · by_cases hk : k = j
    · subst hk
      simp [pgOscNormalize, blockFast, blockSlow, fastShift]
      ring
    · simp [pgOscNormalize, blockFast, blockSlow, fastShift, hk, Pi.single_apply,
        Fin.castAdd_inj]
  · simp [pgOscNormalize, blockFast, blockSlow, fastShift, Pi.single_apply, hna k j]
  · simp [pgOscNormalize, blockFast, blockSlow, fastShift]
  · simp [pgOscNormalize, blockFast, blockSlow, fastShift]

end KAM.Planetary

end
