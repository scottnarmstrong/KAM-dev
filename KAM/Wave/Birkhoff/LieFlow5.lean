/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieMulti
public import KAM.Wave.Birkhoff.LieFlow3
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The flow `Γ_t`: joint `C¹` regularity (blueprint-W `bpW:w3:flow` (i))

Package W3-FLOW, blueprint label `bpW:w3:flow` (audit finding F3).

Each term `(t, w) ↦ t^k φ_k(w)` is `C^∞` over `ℝ` (`contDiff_lieTerm`), so its Fréchet derivative
`lieTermD` is continuous (`continuous_lieTermD`); the derivative series is locally uniformly
dominated (`exists_lieTermD_majorant`), hence continuous (`continuousOn_tsum_lieTermD`), and
`(t, w) ↦ Γ_t(w)` is `C¹` on `{|t| < 2, 40 C ‖w‖² < 1}` (`contDiffOn_lieGamma`).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : ContinuousMultilinearMap ℂ
  (fun _ : Fin 3 => E) E)

theorem contDiff_lieSeq (k : ℕ) : ContDiff ℂ ⊤ fun w : E => lieSeq T w k := by
  have : (fun w : E => lieSeq T w k) = fun w => lieMulti T k (fun _ => w) :=
    funext fun w => (lieMulti_const T w k).symm
  rw [this]
  exact (ContinuousMultilinearMap.contDiff (lieMulti T k)).comp (contDiff_pi.2 fun _ => contDiff_id)

theorem contDiff_lieTerm (k : ℕ) :
    ContDiff ℝ 1 fun p : ℝ × E => (p.1 ^ k) • lieSeq T p.2 k := by
  have h : ContDiff ℝ 1 fun w : E => lieSeq T w k :=
    ((contDiff_lieSeq T k).restrict_scalars ℝ).of_le le_top
  exact (contDiff_fst.pow k).smul (h.comp contDiff_snd)

theorem continuous_lieTermD (k : ℕ) : Continuous fun p : ℝ × E => lieTermD T k p := by
  have h := (contDiff_lieTerm T k).continuous_fderiv one_ne_zero
  have e : (fun p : ℝ × E => lieTermD T k p) =
      fderiv ℝ fun p : ℝ × E => (p.1 ^ k) • lieSeq T p.2 k :=
    funext fun p => (hasFDerivAt_lieTerm T k p).fderiv.symm
  rw [e]; exact h

variable [CompleteSpace E] {C : ℝ} (hC : 0 ≤ C) (hT : ∀ v : Fin 3 → E, ‖T v‖ ≤ C * ∏ i, ‖v i‖)

include hC hT in
/-- (`bpW:w3:flow` (i)) `(t, w) ↦ Γ_t(w)` is `C¹` on `{|t| < 2, 40 C ‖w‖² < 1}`: the termwise
derivative series is continuous there. -/
theorem contDiffOn_lieGamma (hCp : 0 < C) :
    ContDiffOn ℝ 1 (fun z : ℝ × E => lieGamma T z.1 z.2)
      {z : ℝ × E | |z.1| < 2 ∧ 40 * C * ‖z.2‖ ^ 2 < 1} := by
  intro z hz
  refine ContDiffAt.contDiffWithinAt ?_
  rw [contDiffAt_one_iff]
  have hopen : IsOpen {z : ℝ × E | |z.1| < 2 ∧ 40 * C * ‖z.2‖ ^ 2 < 1} :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_const.mul ((continuous_norm.comp continuous_snd).pow 2))
        continuous_const)
  obtain ⟨s, u, hsopen, -, hmem, -, hus, hbound⟩ :=
    exists_lieTermD_majorant T hC hT hCp z.1 z.2 hz.1 hz.2
  refine ⟨fun p => ∑' k, lieTermD T k p,
    s ∩ {z : ℝ × E | |z.1| < 2 ∧ 40 * C * ‖z.2‖ ^ 2 < 1}, ?_, ?_, ?_⟩
  · exact (hsopen.inter hopen).mem_nhds ⟨hmem, hz⟩
  · exact (continuousOn_tsum (fun k => (continuous_lieTermD T k).continuousOn) hus
      (fun k p hp => hbound k p hp)).mono Set.inter_subset_left
  · rintro ⟨t, w⟩ ⟨-, ht, hw⟩
    exact (hasFDerivAt_lieGamma T hC hT hCp t w ht hw).1

end KAM.Wave

end
