/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorReal
public import KAM.Wave.Homological.RealF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Taylor polynomial of a real Hamiltonian is real (blueprint-W `bpW:w5:taylor` (i))

`stepTaylorOf_isRealTaylor`: for a smoothing pair `(P, X)` on `D(s,r)` with `P` real at real points,
the Taylor polynomial `R = stepTaylorOf …` is real in the sense of W4
(`HomTaylor_gen.isRealTaylor`): at real `θ`, `a(θ), b(θ)` are real, `c^- = \overline{c^+}`,
`P' = \overline P`, `Q^T = \overline Q` (true matrix entries). The landed `TaylorReal` gives `a`,
`b` and `Q_{jj}`; here the remaining components:

* `stepX_w0_normal_real`: the normal components of `X(θ,0,0,0)` are real (test `ϖ(X, ·)` against
  the real coordinate directions, `stepNormal_real_of_symp`);
* `tCm_eq_conj_tCp`: `c^- = \overline{c^+}`;
* `stepBilin_iota_conj`: for a bilinear form real on real vectors, the values on the complex
  directions `ι_z e_j`, `ι_{\bar z} e_j` are exchanged by conjugation; hence
  `tP'_entry_eq_conj`, `tQt_entry_eq_conj`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ} {P : KamPhase → ℂ} {X : KamPhase → KamPhase}

/-- The weighted pairing against a coordinate vector. -/
theorem stepPairCLM_kamBasis {q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (c : HomL2) (j : ℕ+) :
    stepPairCLM ha hqq' c (kamBasis ℂ j) = stepWinv a q q' j * c j := by
  show homPairL2 (weightedDiagCLM (stepWinv a q q') (norm_stepWinv_le ha hqq') c) (kamBasis ℂ j) = _
  rw [homPairL2_single_right, weightedDiagCLM_apply]

theorem im_stepWinv_mul (a q q' : ℝ) (j : ℕ+) (z : ℂ) :
    (stepWinv a q q' j * z).im = ((homWt a q j * homWt a q' j)⁻¹ : ℝ) * z.im := by
  unfold stepWinv
  rw [Complex.im_ofReal_mul]

/-- A complex number with zero imaginary part is the image of its real part. -/
theorem complex_eq_ofReal_re {z : ℂ} (hz : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [hz])

/-- **The normal components of a real field are real**: if `ϖ_{q,q'}(Y, c)` is real for every
real `c`, then `Y_u` and `Y_v` are real. -/
theorem stepNormal_real_of_symp {q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') {Y : KamPhase}
    (hY : ∀ c : KamPhase, StepReal c → (stepSymp (q := q) (q' := q') ha hqq' Y c).im = 0)
    (j : ℕ+) : (Y.2.2.1 j).im = 0 ∧ (Y.2.2.2 j).im = 0 := by
  have hpos : (0 : ℝ) < homWt a q j * homWt a q' j := mul_pos (homWt_pos a q j) (homWt_pos a q' j)
  constructor
  · have h := hY _ (stepReal_basis_v j)
    have e : stepSymp (q := q) (q' := q') ha hqq' Y
        ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), (0 : HomL2), kamBasis ℂ j) =
        stepWinv a q q' j * Y.2.2.1 j := by
      simp [stepSymp, stepPairCLM_kamBasis]
    rw [e, im_stepWinv_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_pos.mpr hpos).ne'
  · have h := hY _ (stepReal_basis_u j)
    have e : stepSymp (q := q) (q' := q') ha hqq' Y
        ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), kamBasis ℂ j, (0 : HomL2)) =
        -(stepWinv a q q' j * Y.2.2.2 j) := by
      simp [stepSymp, stepPairCLM_kamBasis]
    rw [e, Complex.neg_im, neg_eq_zero, im_stepWinv_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_pos.mpr hpos).ne'

theorem conj_homSqrt2_inv : conj homSqrt2⁻¹ = homSqrt2⁻¹ := by
  unfold homSqrt2
  rw [map_inv₀, Complex.conj_ofReal]

/-- `c^- = \overline{c^+}` when `Y = X(θ,0,0,0)` has real normal components. -/
theorem stepCm_eq_conj_cp {Y : KamPhase} (hu : ∀ j, (Y.2.2.1 j).im = 0)
    (hv : ∀ j, (Y.2.2.2 j).im = 0) (j : ℕ+) :
    (Complex.I • stepZ Y) j = conj (((-Complex.I) • stepZb Y) j) := by
  obtain ⟨θ, y, u, v⟩ := Y
  rw [stepZ_apply, stepZb_apply]
  have hu' := complex_eq_ofReal_re (hu j)
  have hv' := complex_eq_ofReal_re (hv j)
  simp only [lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    smul_eq_mul] at hu' hv' ⊢
  rw [hu', hv']
  simp only [map_mul, map_neg, map_sub, Complex.conj_I, Complex.conj_ofReal, conj_homSqrt2_inv]
  ring

/-- **Conjugation exchanges `ι_z` and `ι_{\bar z}`** for a bilinear form `B` that is real on real
vectors: with `u_k, v_k` real, `κ ∈ ℂ`,
`\overline{B(s u₁ + κ₁ s v₁, s u₂ + κ₂ s v₂)} = B(s u₁ + \bar κ₁ s v₁, s u₂ + \bar κ₂ s v₂)`,
`s = 1/√2`. -/
theorem stepBilin_iota_conj (B : KamPhase →L[ℂ] KamPhase →L[ℂ] ℂ)
    (hB : ∀ c c' : KamPhase, StepReal c → StepReal c' → (B c c').im = 0)
    {u₁ v₁ u₂ v₂ : KamPhase} (hu₁ : StepReal u₁) (hv₁ : StepReal v₁) (hu₂ : StepReal u₂)
    (hv₂ : StepReal v₂) (κ₁ κ₂ : ℂ) :
    conj (B (homSqrt2⁻¹ • u₁ + (κ₁ * homSqrt2⁻¹) • v₁) (homSqrt2⁻¹ • u₂ + (κ₂ * homSqrt2⁻¹) • v₂)) =
      B (homSqrt2⁻¹ • u₁ + (conj κ₁ * homSqrt2⁻¹) • v₁)
        (homSqrt2⁻¹ • u₂ + (conj κ₂ * homSqrt2⁻¹) • v₂) := by
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  rw [complex_eq_ofReal_re (hB u₁ u₂ hu₁ hu₂), complex_eq_ofReal_re (hB u₁ v₂ hu₁ hv₂),
    complex_eq_ofReal_re (hB v₁ u₂ hv₁ hu₂), complex_eq_ofReal_re (hB v₁ v₂ hv₁ hv₂)]
  simp only [map_add, map_mul, Complex.conj_ofReal, conj_homSqrt2_inv]

theorem stepIotaZ_eq (z : HomL2) :
    stepIotaZ z = homSqrt2⁻¹ • ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), z, (0 : HomL2)) +
      (-Complex.I * homSqrt2⁻¹) • ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), (0 : HomL2), z) := by
  rw [stepIotaZ_apply]; refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp

theorem stepIotaZb_eq (z : HomL2) :
    stepIotaZb z = homSqrt2⁻¹ • ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), z, (0 : HomL2)) +
      (Complex.I * homSqrt2⁻¹) • ((0 : Fin 2 → ℂ), (0 : Fin 2 → ℂ), (0 : HomL2), z) := by
  rw [stepIotaZb_apply]; refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp

section comps

variable (ha : 0 ≤ a) (hqq : 0 ≤ pb + p) (hr : 0 < r) (hs : 0 < s)
  (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X)
  (hreal : ∀ w ∈ kamDomain s r, StepReal w → (P w).im = 0)

include hr hs hP hreal

/-- The normal components of `X(θ, 0, 0, 0)` are real at real `θ`. -/
theorem stepX_w0_normal_real (x : Fin 2 → ℝ) (j : ℕ+) :
    ((X (stepW0L fun l => (x l : ℂ))).2.2.1 j).im = 0 ∧
      ((X (stepW0L fun l => (x l : ℂ))).2.2.2 j).im = 0 :=
  stepNormal_real_of_symp (q := pb) (q' := p) ha hqq (fun _ hc =>
    stepSymp_field_im ha hqq (kamDomain_isOpen s r) hP hreal
      (stepW0L_mem hr (real_mem_complexStrip hs x)) (stepReal_w0 x) hc) j

/-- `c^-(θ) = \overline{c^+(θ)}` at real `θ`. -/
theorem tCm_eq_conj_tCp (x : Fin 2 → ℝ) (j : ℕ+) :
    tCm X (fun l => (x l : ℂ)) j = conj (tCp X (fun l => (x l : ℂ)) j) :=
  stepCm_eq_conj_cp (fun j => (stepX_w0_normal_real ha hqq hr hs hP hreal x j).1)
    (fun j => (stepX_w0_normal_real ha hqq hr hs hP hreal x j).2) j

omit hr hs in
/-- The bilinear form `(c, c') ↦ ϖ_{p,p_+}(DX(w) c, c')` is real on real vectors at real `w`. -/
theorem stepDXForm_real (hp : 0 ≤ p) (hpb : p ≤ pb) {w : KamPhase} (hw : w ∈ kamDomain s r)
    (hwr : StepReal w) (c c' : KamPhase) (hc : StepReal c) (hc' : StepReal c') :
    (((sympK (q := p) (q' := pb) ha (homPP hp hpb)).comp (fderiv ℂ X w)) c c').im = 0 := by
  rw [ContinuousLinearMap.comp_apply, sympK_apply]
  exact stepSymp_dfield_im' ha hqq hP hreal hp hpb hw hwr hc hc'

/-- `P'(θ) = \overline{P(θ)}` entrywise (true entries) at real `θ`. -/
theorem tP'_entry_eq_conj (hp : 0 ≤ p) (hpb : p ≤ pb) (x : Fin 2 → ℝ) (i j : ℕ+) :
    homNormalEntry_gen a p pb (tP' X fun l => (x l : ℂ)) i j =
      conj (homNormalEntry_gen a p pb (tP X fun l => (x l : ℂ)) i j) := by
  set w0 := stepW0L fun l => (x l : ℂ)
  set B := (sympK (q := p) (q' := pb) ha (homPP hp hpb)).comp (fderiv ℂ X w0) with hBdef
  have hB := stepDXForm_real ha hqq hP hreal hp hpb (stepW0L_mem hr (real_mem_complexStrip hs x))
    (stepReal_w0 x)
  have key := stepBilin_iota_conj B hB (stepReal_basis_u j) (stepReal_basis_v j)
    (stepReal_basis_u i) (stepReal_basis_v i) (-Complex.I) (-Complex.I)
  rw [map_neg, Complex.conj_I, neg_neg] at key
  rw [homNormalEntry_eq_pr ha hp hpb, homNormalEntry_eq_pr ha hp hpb]
  show _ * stepPr ha (homPP hp hpb) (blockP' (fderiv ℂ X w0) (kamBasis ℂ j)) (kamBasis ℂ i) =
    conj (_ * stepPr ha (homPP hp hpb) (blockP (fderiv ℂ X w0) (kamBasis ℂ j)) (kamBasis ℂ i))
  rw [stepPr_blockP', stepPr_blockP, stepIotaZ_eq, stepIotaZ_eq, stepIotaZb_eq, stepIotaZb_eq]
  have e1 : ∀ c c', stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (fderiv ℂ X w0 c) c' = B c c' :=
    fun c c' => rfl
  rw [e1, e1, map_mul, map_mul, Complex.conj_ofReal, key]
  rw [show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by rw [map_div₀, map_one, map_ofNat]]

/-- `Q^T(θ) = \overline{Q(θ)}` entrywise (true entries) at real `θ`. -/
theorem tQt_entry_eq_conj (hp : 0 ≤ p) (hpb : p ≤ pb) (x : Fin 2 → ℝ) (i j : ℕ+) :
    homNormalEntry_gen a p pb (tQt X fun l => (x l : ℂ)) i j =
      conj (homNormalEntry_gen a p pb (tQ X fun l => (x l : ℂ)) i j) := by
  set w0 := stepW0L fun l => (x l : ℂ)
  set B := (sympK (q := p) (q' := pb) ha (homPP hp hpb)).comp (fderiv ℂ X w0) with hBdef
  have hB := stepDXForm_real ha hqq hP hreal hp hpb (stepW0L_mem hr (real_mem_complexStrip hs x))
    (stepReal_w0 x)
  have key := stepBilin_iota_conj B hB (stepReal_basis_u j) (stepReal_basis_v j)
    (stepReal_basis_u i) (stepReal_basis_v i) (-Complex.I) Complex.I
  rw [map_neg, Complex.conj_I, neg_neg] at key
  rw [homNormalEntry_eq_pr ha hp hpb, homNormalEntry_eq_pr ha hp hpb]
  show _ * stepPr ha (homPP hp hpb) (blockQt (fderiv ℂ X w0) (kamBasis ℂ j)) (kamBasis ℂ i) =
    conj (_ * stepPr ha (homPP hp hpb) (blockQ (fderiv ℂ X w0) (kamBasis ℂ j)) (kamBasis ℂ i))
  rw [stepPr_blockQt, stepPr_blockQ, stepIotaZ_eq, stepIotaZ_eq, stepIotaZb_eq, stepIotaZb_eq]
  have e1 : ∀ c c', stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (fderiv ℂ X w0 c) c' = B c c' :=
    fun c c' => rfl
  rw [e1, e1, map_mul, Complex.conj_ofReal, key]

end comps

/-- **The Taylor polynomial of a real Hamiltonian is real** (`bpW:w5:taylor` (i), "`R` is real";
W4's notion `HomTaylor_gen.isRealTaylor`). -/
theorem stepTaylorOf_isRealTaylor (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s)
    (hr : 0 < r) (hP : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P X)
    (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) {ε : ℝ}
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε)
    (hreal : ∀ w ∈ kamDomain s r, StepReal w → (P w).im = 0) :
    (stepTaylorOf ha hp hpb hs hr hP hper hb).isRealTaylor := by
  have hqq : 0 ≤ pb + p := by linarith
  intro x
  refine ⟨?_, fun k => ?_, fun j => ?_, fun i j => ?_, fun i j => ?_⟩
  · exact hreal _ (stepW0L_mem hr (real_mem_complexStrip hs x)) (stepReal_w0 x)
  · exact tB_real ha hqq hr hs hP hreal x k
  · exact tCm_eq_conj_tCp ha hqq hr hs hP hreal x j
  · exact tP'_entry_eq_conj ha hqq hr hs hP hreal hp hpb x i j
  · exact tQt_entry_eq_conj ha hqq hr hs hP hreal hp hpb x i j

end KAM.Wave
