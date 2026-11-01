/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorBoundA0
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Taylor polynomial `R ∈ 𝒯_s` (blueprint-W `bpW:w5:taylor` (i))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepTaylorOf`: for a smoothing pair `(P, X)` on `D(s,r)` with `P` periodic and `|X|_r ≤ ε`, the
element `R ∈ 𝒯_s` (W4's class, `HomTaylor_gen a p pb s`) whose components are those of
`bpW:w5:taylor`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ} {P : KamPhase → ℂ} {X : KamPhase → KamPhase}

theorem stepDX_symm_pp (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (hP : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P X) {w : KamPhase}
    (hw : w ∈ kamDomain s r) (u v : KamPhase) :
    stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (fderiv ℂ X w u) v =
      stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (fderiv ℂ X w v) u := by
  rw [stepSymp_comm_weights ha (homPP hp hpb) (by linarith),
    stepSymp_comm_weights ha (homPP hp hpb) (by linarith)]
  exact stepSymp_dX_symm ha _ hP hw u v

/-- **The Taylor polynomial `R ∈ 𝒯_s`** of a smoothing pair (`bpW:w5:taylor` (i)). -/
def stepTaylorOf (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s) (hr : 0 < r)
    (hP : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P X)
    (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) {ε : ℝ}
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) : HomTaylor_gen a p pb s where
  a0 := tA0 P
  b := tB X
  cp := tCp X
  cm := tCm X
  P := tP X
  P' := tP' X
  Q := tQ X
  Qt := tQt X
  comp_a0 := ⟨tA0_differentiableOn ha _ hr hP,
    fun i θ hθ => tA0_periodic ha _ hr hP hper i hθ, tA0_bounded ha _ hs hr hP hper hb⟩
  comp_b := ⟨tB_differentiableOn ha _ hr hP,
    fun i θ hθ => by
      funext j
      simp only [tB, tX_periodic ha _ hr hP hper i hθ],
    2 * Real.pi * ε, fun θ hθ => norm_tB_le hr hb hθ⟩
  comp_cp := ⟨tCp_differentiableOn ha _ hr hP,
    fun i θ hθ => by simp only [tCp, tX_periodic ha _ hr hP hper i hθ],
    r * ε, fun θ hθ => norm_tCp_le hr hb hθ⟩
  comp_cm := ⟨tCm_differentiableOn ha _ hr hP,
    fun i θ hθ => by simp only [tCm, tX_periodic ha _ hr hP hper i hθ],
    r * ε, fun θ hθ => norm_tCm_le hr hb hθ⟩
  comp_P := ⟨tBlock_differentiableOn ha _ hr hP stepZb stepIotaZ (-Complex.I / 2),
    fun i θ hθ => by simp only [tP, blockP, tDX_periodic ha _ hr hP hper i hθ],
    2 * ε, fun θ hθ => norm_tP_le hr hP.holoX hb
      ((kamNorm_nonneg hr.le _).trans (hb _ (stepW0L_mem hr hθ))) hθ⟩
  comp_P' := ⟨tBlock_differentiableOn ha _ hr hP stepZ stepIotaZb (Complex.I / 2),
    fun i θ hθ => by simp only [tP', blockP', tDX_periodic ha _ hr hP hper i hθ],
    2 * ε, fun θ hθ => norm_tP'_le hr hP.holoX hb
      ((kamNorm_nonneg hr.le _).trans (hb _ (stepW0L_mem hr hθ))) hθ⟩
  comp_Q := ⟨tBlock_differentiableOn ha _ hr hP stepZ stepIotaZ Complex.I,
    fun i θ hθ => by simp only [tQ, blockQ, tDX_periodic ha _ hr hP hper i hθ],
    2 * ε, fun θ hθ => norm_tQ_le hr hP.holoX hb
      ((kamNorm_nonneg hr.le _).trans (hb _ (stepW0L_mem hr hθ))) hθ⟩
  comp_Qt := ⟨tBlock_differentiableOn ha _ hr hP stepZb stepIotaZb (-Complex.I),
    fun i θ hθ => by simp only [tQt, blockQt, tDX_periodic ha _ hr hP hper i hθ],
    2 * ε, fun θ hθ => norm_tQt_le hr hP.holoX hb
      ((kamNorm_nonneg hr.le _).trans (hb _ (stepW0L_mem hr hθ))) hθ⟩
  symP := fun θ hθ i j => by
    refine homNormalEntry_symm_of_pr ha hp hpb (fun x y => ?_) i j
    show stepPr ha (homPP hp hpb) (blockP _ x) y = stepPr ha (homPP hp hpb) (blockP _ y) x
    rw [stepPr_blockP, stepPr_blockP, stepDX_symm_pp ha hp hpb hP (stepW0L_mem hr hθ)]
  symP' := fun θ hθ i j => by
    refine homNormalEntry_symm_of_pr ha hp hpb (fun x y => ?_) i j
    show stepPr ha (homPP hp hpb) (blockP' _ x) y = stepPr ha (homPP hp hpb) (blockP' _ y) x
    rw [stepPr_blockP', stepPr_blockP', stepDX_symm_pp ha hp hpb hP (stepW0L_mem hr hθ)]
  transQ := fun θ hθ i j => by
    refine homNormalEntry_symm_of_pr ha hp hpb (fun x y => ?_) i j
    show stepPr ha (homPP hp hpb) (blockQt _ x) y = stepPr ha (homPP hp hpb) (blockQ _ y) x
    rw [stepPr_blockQt, stepPr_blockQ, stepDX_symm_pp ha hp hpb hP (stepW0L_mem hr hθ)]

end KAM.Wave
