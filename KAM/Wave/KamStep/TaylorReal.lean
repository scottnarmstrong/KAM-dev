/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.RealCalc
public import KAM.Wave.KamStep.StepSolve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Reality of the Taylor polynomial (blueprint-W `bpW:w5:taylor` (i), "`R` is real")

For a real smoothing pair `(P, X)` on `D(s,r)` (`P` real at real points), the components of
`stepTaylorOf` satisfy, at real `θ`: `b(θ) ∈ ℝ²` (`tB_real`) and `Q(θ)_{jj} ∈ ℝ`
(`tQ_entry_real`), and hence their `θ`-averages `[b]`, `[Q]_{jj}` are real
(`homCoeff_b_real`, `homCoeff_Q_real`). These are the coefficients of `N̂`, so `N̂` has real
frequencies `ω̂ = [b]`, `Ω̂_j = [Q]_{jj}` (`stepOmegaHat`, `stepOmegaTail` are their real parts).
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ} {P : KamPhase → ℂ} {X : KamPhase → KamPhase}

/-! ### Averages -/

theorem homCoeff_zero_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : (Fin 2 → ℂ) → E) :
    homCoeff f 0 = ∫ x in Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1),
      f fun j => (x j : ℂ) := by
  unfold homCoeff torusCoeffW torusAverage
  refine MeasureTheory.setIntegral_congr_fun (by measurability) fun x _ => ?_
  simp [character]

/-- The average of a function that is real on the real torus is real (in any real functional). -/
theorem homCoeff_zero_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (L : E →L[ℝ] ℝ) {f : (Fin 2 → ℂ) → E}
    (hf : ∀ x : Fin 2 → ℝ, L (f fun j => (x j : ℂ)) = 0) : L (homCoeff f 0) = 0 := by
  rw [homCoeff_zero_eq]
  exact integral_clm_eq_zero (μ := MeasureTheory.volume.restrict _) L hf

/-! ### The real functionals -/

theorem kamEntry_smul_real (t : ℝ) (A : HomOp) (i j : ℕ+) :
    kamEntry (t • A) i j = (t : ℂ) * kamEntry A i j := by
  simp [kamEntry, Complex.real_smul]

/-- `A ↦ c · im (A_{jj})` as a real-continuous functional on operators. -/
def entryImCLM (c : ℝ) (j : ℕ+) : HomOp →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun A => c * (kamEntry A j j).im
      map_add' := fun A B => by simp [kamEntry, mul_add]
      map_smul' := fun t A => by
        rw [RingHom.id_apply, smul_eq_mul, kamEntry_smul_real, Complex.im_ofReal_mul]; ring } |c|
    (fun A => by
      show |c * (kamEntry A j j).im| ≤ |c| * ‖A‖
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((Complex.abs_im_le_norm _).trans (norm_kamEntry_le A j j)) (abs_nonneg c))

theorem entryImCLM_apply (c : ℝ) (j : ℕ+) (A : HomOp) :
    entryImCLM c j A = c * (kamEntry A j j).im := by
  simp [entryImCLM]

/-- `y ↦ im (y_k)` as a real functional on `ℂ²`. -/
def coordImCLM (k : Fin 2) : (Fin 2 → ℂ) →L[ℝ] ℝ :=
  Complex.imCLM.comp (((ContinuousLinearMap.proj k : (Fin 2 → ℂ) →L[ℂ] ℂ)).restrictScalars ℝ)

theorem coordImCLM_apply (k : Fin 2) (y : Fin 2 → ℂ) : coordImCLM k y = (y k).im := rfl

theorem real_mem_complexStrip (hs : 0 < s) (x : Fin 2 → ℝ) :
    (fun j => (x j : ℂ)) ∈ complexStrip 2 s := fun j => by simpa using hs

theorem stepReal_w0 (x : Fin 2 → ℝ) : StepReal (stepW0L fun j => (x j : ℂ)) :=
  ⟨fun i => by simp [stepW0L_apply], fun i => by simp [stepW0L_apply],
    fun j => by simp [stepW0L_apply], fun j => by simp [stepW0L_apply]⟩

/-! ### The components at real `θ` -/

theorem stepReal_basis_u (j : ℕ+) :
    StepReal ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), kamBasis ℂ j, (0 : HomL2)) :=
  ⟨fun i => by simp, fun i => by simp,
    fun l => by by_cases h : l = j <;> simp [kamBasis, lp.single_apply, Pi.single_apply, h],
    fun l => by simp⟩

theorem stepReal_basis_v (j : ℕ+) :
    StepReal ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), (0 : HomL2), kamBasis ℂ j) :=
  ⟨fun i => by simp, fun i => by simp, fun l => by simp,
    fun l => by by_cases h : l = j <;> simp [kamBasis, lp.single_apply, Pi.single_apply, h]⟩

section comps

variable (ha : 0 ≤ a) (hqq : 0 ≤ pb + p) (hr : 0 < r) (hs : 0 < s)
  (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X)
  (hreal : ∀ w ∈ kamDomain s r, StepReal w → (P w).im = 0)

include hr hs hP hreal

/-- `b(θ)` is real at real `θ`. -/
theorem tB_real (x : Fin 2 → ℝ) (k : Fin 2) :
    (tB X (fun j => (x j : ℂ)) k).im = 0 := by
  have h := stepSymp_field_im ha hqq (kamDomain_isOpen s r) hP hreal
    (stepW0L_mem hr (real_mem_complexStrip hs x)) (stepReal_w0 x)
    (c := ((0 : Fin 2 → ℂ), (Pi.single k 1 : Fin 2 → ℂ), (0 : HomL2), (0 : HomL2)))
    ⟨fun i => by simp, fun i => by by_cases hik : i = k <;> simp [Pi.single_apply, hik],
      fun j => by simp, fun j => by simp⟩
  have e : stepSymp (q := pb) (q' := p) ha hqq (X (stepW0L fun j => (x j : ℂ)))
      ((0 : Fin 2 → ℂ), (Pi.single k 1 : Fin 2 → ℂ), (0 : HomL2), (0 : HomL2)) =
      tB X (fun j => (x j : ℂ)) k := by
    simp [stepSymp, tB, Pi.single_apply]
  rwa [e] at h

omit hr hs in
/-- `ϖ_{p,p_+}(DX c, c')` is real for real directions. -/
theorem stepSymp_dfield_im' (hp : 0 ≤ p) (hpb : p ≤ pb) {w c c' : KamPhase}
    (hw : w ∈ kamDomain s r) (hwr : StepReal w) (hcr : StepReal c) (hcr' : StepReal c') :
    (stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (fderiv ℂ X w c) c').im = 0 := by
  rw [stepSymp_comm_weights ha (homPP hp hpb) hqq]
  exact stepSymp_dfield_im ha hqq (kamDomain_isOpen s r) hP hreal hw hwr hcr hcr'

/-- `Q(θ)_{jj}` is real at real `θ`. -/
theorem tQ_entry_real (hp : 0 ≤ p) (hpb : p ≤ pb) (x : Fin 2 → ℝ) (j : ℕ+) :
    (homNormalEntry_gen a p pb (tQ X (fun l => (x l : ℂ))) j j).im = 0 := by
  set w0 := stepW0L fun l => (x l : ℂ) with hw0
  have hw : w0 ∈ kamDomain s r := stepW0L_mem hr (real_mem_complexStrip hs x)
  have hwr : StepReal w0 := stepReal_w0 x
  set A := fderiv ℂ X w0 with hA
  set cu : KamPhase := ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), kamBasis ℂ j, (0 : HomL2)) with hcu
  set cv : KamPhase := ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), (0 : HomL2), kamBasis ℂ j) with hcv
  have hsy : stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A cu) cv =
      stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A cv) cu :=
    stepDX_symm_pp ha hp hpb hP hw cu cv
  have e1 : stepIotaZ (kamBasis ℂ j) = homSqrt2⁻¹ • cu + (-Complex.I * homSqrt2⁻¹) • cv := by
    rw [stepIotaZ_apply]; refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [hcu, hcv]
  have e2 : stepIotaZb (kamBasis ℂ j) = homSqrt2⁻¹ • cu + (Complex.I * homSqrt2⁻¹) • cv := by
    rw [stepIotaZb_apply]; refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [hcu, hcv]
  have hq : stepPr ha (homPP hp hpb) (blockQ A (kamBasis ℂ j)) (kamBasis ℂ j) =
      (1 / 2 : ℂ) * (stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A cu) cu +
        stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A cv) cv) := by
    rw [stepPr_blockQ, e1, e2]
    have hb := homSqrt2_inv_sq
    simp only [map_add, map_smul, ← sympK_apply (q := p) (q' := pb) ha (homPP hp hpb)]
    simp only [sympK_apply, add_apply, smul_apply,
      smul_eq_mul]
    rw [hsy]
    linear_combination (stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A cu) cu +
      stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A cv) cv) * hb -
      (homSqrt2⁻¹ ^ 2 * stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A cv) cv) * Complex.I_sq
  have him : (stepPr ha (homPP hp hpb) (blockQ A (kamBasis ℂ j)) (kamBasis ℂ j)).im = 0 := by
    rw [hq]
    have u1 : (stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A cu) cu).im = 0 :=
      stepSymp_dfield_im' ha hqq hP hreal hp hpb hw hwr
      (stepReal_basis_u j) (stepReal_basis_u j)
    have u2 : (stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (A cv) cv).im = 0 :=
      stepSymp_dfield_im' ha hqq hP hreal hp hpb hw hwr
      (stepReal_basis_v j) (stepReal_basis_v j)
    simp [Complex.mul_im, Complex.add_im, u1, u2]
  rw [homNormalEntry_eq_pr ha hp hpb]
  show (((homWt a p j * homWt a p j : ℝ) : ℂ) * stepPr ha (homPP hp hpb)
    (blockQ A (kamBasis ℂ j)) (kamBasis ℂ j)).im = 0
  rw [Complex.im_ofReal_mul, him, mul_zero]

end comps

section avg

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hqq : 0 ≤ pb + p) (hs : 0 < s) (hr : 0 < r)
  (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X)
  (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) {ε : ℝ}
  (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε)
  (hreal : ∀ w ∈ kamDomain s r, StepReal w → (P w).im = 0)

include hreal

/-- **`[b]` is real** (`bpW:w5:taylor` (i): `R` is real; the frequency `ω̂ = [b]`). -/
theorem homCoeff_b_real (k : Fin 2) :
    (homCoeff (stepTaylorOf ha hp hpb hs hr hP hper hb).b 0 k).im = 0 := by
  have := homCoeff_zero_clm (coordImCLM k) (f := (stepTaylorOf ha hp hpb hs hr hP hper hb).b)
    (fun x => by
      rw [coordImCLM_apply]
      exact tB_real ha hqq hr hs hP hreal x k)
  simpa [coordImCLM_apply] using this

/-- **`[Q]_{jj}` is real** (the frequency `Ω̂_j`). -/
theorem homCoeff_Q_real (j : ℕ+) :
    (homNormalEntry_gen a p pb
      (homCoeff (stepTaylorOf ha hp hpb hs hr hP hper hb).Q 0) j j).im = 0 := by
  set c : ℝ := ellWeight a p (j + 2) / ellWeight a pb (j + 2) with hc
  have := homCoeff_zero_clm (entryImCLM c j) (f := (stepTaylorOf ha hp hpb hs hr hP hper hb).Q)
    (fun x => by
      refine (entryImCLM_apply c j _).trans ?_
      have h := tQ_entry_real ha hqq hr hs hP hreal hp hpb x j
      have e : homNormalEntry_gen a p pb (tQ X (fun l => (x l : ℂ))) j j =
          (c : ℂ) * kamEntry (tQ X (fun l => (x l : ℂ))) j j := rfl
      rw [e, Complex.im_ofReal_mul] at h
      exact h)
  have this' := (entryImCLM_apply c j _).symm.trans this
  have e : homNormalEntry_gen a p pb
      (homCoeff (stepTaylorOf ha hp hpb hs hr hP hper hb).Q 0) j j =
      (c : ℂ) * kamEntry (homCoeff (stepTaylorOf ha hp hpb hs hr hP hper hb).Q 0) j j := rfl
  rw [e, Complex.im_ofReal_mul]
  exact this'

end avg

end KAM.Wave
