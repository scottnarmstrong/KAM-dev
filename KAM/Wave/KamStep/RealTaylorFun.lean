/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.RealTaylorOf
public import KAM.Wave.KamStep.TaylorField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A real Taylor Hamiltonian is real at real points, and so is its field (blueprint-W `bpW:w5:solve`)

Off-frontier, source-faithful infrastructure (W5-REAL, item 1); the dependency graph is still being
built.

For `T ∈ 𝒯_s` real in the sense of W4 (`HomTaylor_gen.isRealTaylor`):

* `stepFun_real`: the function `T(θ, y, z, \bar z)` is real at every real point (`θ, y` real,
  `u, v` real, so `\bar z = \overline z`);
* `stepField_real`: its field `X_T = stepField T` is real at every real point. Proof:
  `DT(w)c = ϖ(X_T(w), c)` is real for real `c` (derivative of a real function along a real line,
  `fderiv_im_of_real`), and the real coordinate directions detect every coordinate of `X_T(w)`
  (`stepReal_of_symp`).

Helpers: `stepPr_star` (the weighted pairing commutes with conjugation), `homOp_star_of_entries`
(an operator whose matrix is the conjugate of another's maps `\overline x` to `\overline{Ax}`),
`kamEntry_conj_of_normal` (conjugate true entries give conjugate representative entries).
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

/-- The weighted pairing commutes with conjugation (real weights). -/
theorem stepPr_star (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (c z : HomL2) :
    stepPr ha hpp (star c) (star z) = conj (stepPr ha hpp c z) := by
  rw [stepPr_eq_homPairL2, stepPr_eq_homPairL2, homPairL2_apply, homPairL2_apply]
  unfold homPairF
  rw [Complex.conj_tsum]
  refine tsum_congr fun j => ?_
  simp only [homLamDiag_apply_gen, lp.star_apply, homLamD_gen, map_mul, Complex.conj_ofReal,
    Complex.star_def]

/-- An operator whose matrix is the conjugate of the matrix of `A` maps `\overline x` to
`\overline{A x}`. -/
theorem homOp_star_of_entries {A A' : HomOp} (h : ∀ i j, kamEntry A' i j = conj (kamEntry A i j))
    (x : HomL2) : A' (star x) = star (A x) := by
  ext i
  rw [lp.star_apply, Complex.star_def]
  have h1 := homOp_hasSum A' (star x) i
  have h2 := (Complex.hasSum_conj' (L := SummationFilter.unconditional ℕ+)).mpr (homOp_hasSum A x i)
  refine h1.unique (h2.congr_fun fun j => ?_)
  rw [h i j, lp.star_apply, Complex.star_def, map_mul]

/-- Conjugate true entries give conjugate representative entries. -/
theorem kamEntry_conj_of_normal {A A' : HomOp} {i j : ℕ+}
    (h : homNormalEntry_gen a p pb A' i j = conj (homNormalEntry_gen a p pb A i j)) :
    kamEntry A' i j = conj (kamEntry A i j) := by
  unfold homNormalEntry_gen at h
  rw [map_mul, Complex.conj_ofReal] at h
  have hc : ((ellWeight a p (j + 2) / ellWeight a pb (i + 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos (ellWeight_pos a p (j + 2)) (ellWeight_pos a pb (i + 2))).ne'
  exact mul_left_cancel₀ hc h

/-- At a real point, `\bar z = \overline z`. -/
theorem stepZb_eq_star {w : KamPhase} (hw : StepReal w) : stepZb w = star (stepZ w) := by
  obtain ⟨θ, y, u, v⟩ := w
  obtain ⟨-, -, hu, hv⟩ := hw
  rw [stepZ_apply, stepZb_apply]
  ext j
  have hu' := complex_eq_ofReal_re (hu j)
  have hv' := complex_eq_ofReal_re (hv j)
  simp only [lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    smul_eq_mul, lp.star_apply, Complex.star_def] at hu' hv' ⊢
  rw [hu', hv']
  simp only [map_mul, map_add, Complex.conj_I, Complex.conj_ofReal, conj_homSqrt2_inv]
  ring

/-- **A real Taylor Hamiltonian is real at real points.** -/
theorem stepFun_real (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s)
    (T : HomTaylor_gen a p pb s) (hT : T.isRealTaylor) {w : KamPhase} (hw : StepReal w) :
    (waveStepFun ha (homPP hp hpb) T w).im = 0 := by
  obtain ⟨θ, y, u, v⟩ := w
  have hθ : θ = fun j => ((θ j).re : ℂ) := funext fun j => complex_eq_ofReal_re (hw.1 j)
  have hy : ∀ k, y k = ((y k).re : ℂ) := fun k => complex_eq_ofReal_re (hw.2.1 k)
  obtain ⟨ha0, hb, hc, hP', hQt⟩ := hT fun j => (θ j).re
  rw [← hθ] at ha0 hb hc hP' hQt
  have hθs : θ ∈ complexStrip 2 s := by rw [hθ]; exact real_mem_complexStrip hs _
  have hzb : stepZb (θ, y, u, v) = star (stepZ (θ, y, u, v)) := stepZb_eq_star hw
  have hcs : star (T.cp θ) = T.cm θ := by
    ext j; rw [lp.star_apply, Complex.star_def, hc j]
  have hPs : ∀ x, T.P' θ (star x) = star (T.P θ x) := homOp_star_of_entries fun i j =>
    kamEntry_conj_of_normal (hP' i j)
  have hP's : ∀ x, T.P θ (star x) = star (T.P' θ x) := homOp_star_of_entries fun i j => by
    rw [kamEntry_conj_of_normal (hP' i j), Complex.conj_conj]
  have hQs : ∀ x, T.Qt θ (star x) = star (T.Q θ x) := homOp_star_of_entries fun i j =>
    kamEntry_conj_of_normal (hQt i j)
  set z := stepZ (θ, y, u, v) with hz
  have hsw := stepPr_swap ha hp hpb (A := T.Q θ) (A' := T.Qt θ)
    (fun i j => (T.transQ θ hθs j i).symm) z (star z)
  set B := stepPr ha (homPP hp hpb) with hB
  have t1 : conj (B (T.cp θ) z) = B (T.cm θ) (star z) := by rw [← stepPr_star, hcs]
  have t2 : conj (B (T.cm θ) (star z)) = B (T.cp θ) z := by
    rw [← stepPr_star, ← hcs, star_star, star_star]
  have t3 : conj (B (T.P θ z) z) = B (T.P' θ (star z)) (star z) := by rw [← stepPr_star, ← hPs]
  have t4 : conj (B (T.Q θ z) (star z)) = B (T.Q θ z) (star z) := by
    rw [← stepPr_star, star_star, ← hQs, hsw]
  have t5 : conj (B (T.P' θ (star z)) (star z)) = B (T.P θ z) z := by
    rw [← stepPr_star, star_star, ← hP's, star_star]
  have hbs : conj (∑ k, T.b θ k * y k) = ∑ k, T.b θ k * y k := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Complex.conj_eq_iff_im.mpr (hb k), hy k, Complex.conj_ofReal]
  rw [← Complex.conj_eq_iff_im]
  show conj (T.a0 θ + ∑ k, T.b θ k * y k + B (T.cp θ) z + B (T.cm θ) (stepZb (θ, y, u, v))
    + B (T.P θ z) z + B (T.Q θ z) (stepZb (θ, y, u, v))
    + B (T.P' θ (stepZb (θ, y, u, v))) (stepZb (θ, y, u, v))) = _
  rw [hzb]
  simp only [map_add, t1, t2, t3, t4, t5, hbs, Complex.conj_eq_iff_im.mpr ha0]
  show _ = T.a0 θ + ∑ k, T.b θ k * y k + B (T.cp θ) z + B (T.cm θ) (stepZb (θ, y, u, v))
    + B (T.P θ z) z + B (T.Q θ z) (stepZb (θ, y, u, v))
    + B (T.P' θ (stepZb (θ, y, u, v))) (stepZb (θ, y, u, v))
  rw [hzb]
  ring

/-- **A real vector is detected by the symplectic pairing**: if `ϖ_{q,q'}(Y, c)` is real for every
real `c`, then `Y` is real. -/
theorem stepReal_of_symp {q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') {Y : KamPhase}
    (hY : ∀ c : KamPhase, StepReal c → (stepSymp (q := q) (q' := q') ha hqq' Y c).im = 0) :
    StepReal Y := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  refine ⟨fun i => ?_, fun i => ?_, fun j => (stepNormal_real_of_symp ha hqq' hY j).1,
    fun j => (stepNormal_real_of_symp ha hqq' hY j).2⟩
  · have h := hY ((0 : Fin 2 → ℂ), (Pi.single i 1 : Fin 2 → ℂ), (0 : HomL2), (0 : HomL2))
      ⟨fun k => by simp, fun k => by by_cases hk : k = i <;> simp [hk],
        fun j => by simp, fun j => by simp⟩
    have e : stepSymp (q := q) (q' := q') ha hqq' Y
        ((0 : Fin 2 → ℂ), (Pi.single i 1 : Fin 2 → ℂ), (0 : HomL2), (0 : HomL2)) =
        ((2 * Real.pi : ℝ) : ℂ) * Y.1 i := by
      simp [stepSymp, Pi.single_apply]
    rw [e, Complex.im_ofReal_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hpi
  · have h := hY ((Pi.single i 1 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), (0 : HomL2), (0 : HomL2))
      ⟨fun k => by by_cases hk : k = i <;> simp [hk], fun k => by simp,
        fun j => by simp, fun j => by simp⟩
    have e : stepSymp (q := q) (q' := q') ha hqq' Y
        ((Pi.single i 1 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), (0 : HomL2), (0 : HomL2)) =
        -(((2 * Real.pi : ℝ) : ℂ) * Y.2.1 i) := by
      simp [stepSymp, Pi.single_apply]
    rw [e, Complex.neg_im, neg_eq_zero, Complex.im_ofReal_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hpi

/-- **The field of a real Taylor Hamiltonian is real at real points.** -/
theorem stepField_real (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s)
    (T : HomTaylor_gen a p pb s) (hT : T.isRealTaylor) {w : KamPhase} (hw : StepReal w) :
    StepReal (stepField ha hp hpb T w) := by
  set V : Set KamPhase := {w | w.1 ∈ complexStrip 2 s} with hV
  have hVo : IsOpen V := (isOpen_complexStrip 2 s).preimage continuous_fst
  have hwV : w ∈ V := by
    show w.1 ∈ complexStrip 2 s
    have : w.1 = fun j => ((w.1 j).re : ℂ) := funext fun j => complex_eq_ofReal_re (hw.1 j)
    rw [this]; exact real_mem_complexStrip hs _
  have hdiff : DifferentiableOn ℂ (waveStepFun ha (homPP hp hpb) T) V := fun z hz =>
    (stepFun_field ha hp hpb T hz).choose_spec.1.differentiableAt.differentiableWithinAt
  obtain ⟨D, hD, hDW⟩ := stepFun_field ha hp hpb T hwV
  refine stepReal_of_symp (q := p) (q' := pb) ha (homPP hp hpb) fun c hc => ?_
  rw [← hDW, ← hD.fderiv]
  exact fderiv_im_of_real hVo hdiff (fun z _ hz => stepFun_real ha hp hpb hs T hT hz) hwV hw hc

end KAM.Wave
