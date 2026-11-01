/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ActionAngle
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The action–angle substitution: the derivative (blueprint-W `bpW:w5:action-angle` (iii))

Off-frontier, source-faithful infrastructure (W5-AA); the dependency graph is still being built.
Blueprint label `bpW:w5:action-angle` (iii), step `a-der`.

Write `s_i = √(ξ_i + y_i)`, `E_{±,i} = e^{∓2πiθ_i}` (`aaS`, `aaE`). For `Re(ξ_i + y_i) > 0`:

* `aaDer a q ξ w : 𝒫 →L 𝔚` is `D𝒜_ξ(w)` read on `q`-representatives:
  `(D𝒜 W)_{±i} = (Y_i/(2 s_i) ∓ 2πi s_i Θ_i) E_{±,i}`, `(D𝒜 W)_{±J} = (U_{J-2} ± i V_{J-2})/√2`
  (`aaDerTanL`, `aaDer_tan`, `aaDer_nor_true`, `aaDer_nor_false`); at `q = p` it is the Fréchet
  derivative of `w ↦ 𝒜_ξ(w)` (`hasFDerivAt_aaMap`).
* `aaDerInv a q ξ w : 𝔚 →L 𝒫` is the inverse of the blueprint:
  `Θ_i = (W_{-i} E_{+,i} - W_i E_{-,i})/(4πi s_i)`, `Y_i = s_i (W_i E_{-,i} + W_{-i} E_{+,i})`,
  `U = (Ŵ_+ + Ŵ_-)/√2`, `V = (Ŵ_+ - Ŵ_-)/(i√2)` (actual coordinates `W_l` at weight `q`);
  `aaDerInv_aaDer`, `aaDer_aaDerInv`: `D𝒜_ξ(w)` is a linear bijection `𝒫^q → 𝔚^q` for every `q`.
* `birkOmegaMix a q q'`: the form `Ω(W, W') = i Σ_l sgn(l) W_l W'_{-l}` for `W ∈ 𝔚^q`, `W' ∈ 𝔚^{q'}`
  (`= birkOmega` for `q = q'`, `birkOmegaMix_eq_birkOmega`), and `aaDer_symp`:
  `Ω(D𝒜 W, D𝒜 W') = ϖ(W, W')` for `W ∈ 𝒫^q`, `W' ∈ 𝒫^{q'}`, `q + q' ≥ 0`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Complex

/-! ### Building blocks -/

/-- `s_i = √(ξ_i + y_i)`. -/
def aaS (ξ : Fin 2 → ℂ) (w : KamPhase) (i : Fin 2) : ℂ := aaSqrt (ξ i + w.2.1 i)

/-- `E_{±,i} = e^{∓2πiθ_i}` (`b = true` is `+`). -/
def aaE (w : KamPhase) (b : Bool) (i : Fin 2) : ℂ :=
  cexp (-(birkSgn (b, modeIdx i)) * (2 * Real.pi * I * w.1 i))

theorem aaTanCoord_eq (ξ : Fin 2 → ℂ) (w : KamPhase) (b : Bool) (i : Fin 2) :
    aaTanCoord ξ w b i = aaS ξ w i * aaE w b i := rfl

theorem aaE_mul (w : KamPhase) (i : Fin 2) : aaE w true i * aaE w false i = 1 := by
  unfold aaE
  rw [← Complex.exp_add]
  simp [birkSgn]

theorem aaE_ne_zero (w : KamPhase) (b : Bool) (i : Fin 2) : aaE w b i ≠ 0 := Complex.exp_ne_zero _

theorem aaS_ne_zero {ξ : Fin 2 → ℂ} {w : KamPhase} {i : Fin 2} (h : 0 < (ξ i + w.2.1 i).re) :
    aaS ξ w i ≠ 0 := aaSqrt_ne_zero (ne_zero_of_re_pos h)

theorem aaS_mul_self (ξ : Fin 2 → ℂ) (w : KamPhase) (i : Fin 2) :
    aaS ξ w i * aaS ξ w i = ξ i + w.2.1 i := aaSqrt_mul_self _

/-- The tangential part `Σ_{i,±} ω_{a,q}(i) c_{±,i} e_{±i}` of a point of `𝔚` with actual tangential
coordinates `c`. -/
def aaTanBuild (a q : ℝ) (c : Bool → Fin 2 → ℂ) : BirkSpace :=
  ∑ i : Fin 2, ∑ b : Bool, lp.single 2 (b, modeIdx i) ((ellWeight a q (modeIdx i) : ℂ) * c b i)

theorem aaTanBuild_tan (a q : ℝ) (c : Bool → Fin 2 → ℂ) (b : Bool) (i : Fin 2) :
    aaTanBuild a q c (b, modeIdx i) = (ellWeight a q (modeIdx i) : ℂ) * c b i := by
  simp only [aaTanBuild, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  have hinj := modeIdx_injective (N := 2)
  fin_cases i <;> cases b <;> simp [Prod.ext_iff, hinj.eq_iff]

theorem aaTanBuild_nor (a q : ℝ) (c : Bool → Fin 2 → ℂ) (b : Bool) (j : ℕ+) :
    aaTanBuild a q c (b, j + 2) = 0 := by
  simp only [aaTanBuild, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b' _ => ?_
  exact ite_eq_right_iff.2 fun h => absurd (congrArg Prod.snd h).symm (modeIdx_ne_add_two i j)

/-- The tangential derivative functional `W ↦ (Y_i/(2s_i) ∓ 2πi s_i Θ_i) E_{±,i}`. -/
def aaDerTanL (ξ : Fin 2 → ℂ) (w : KamPhase) (b : Bool) (i : Fin 2) : KamPhase →L[ℂ] ℂ :=
  (aaE w b i / (2 * aaS ξ w i)) • ((ContinuousLinearMap.proj i).comp
      ((ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
        (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2)))) -
    (birkSgn (b, modeIdx i) * (2 * Real.pi * I) * aaS ξ w i * aaE w b i) •
      ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2)))

theorem aaDerTanL_apply (ξ : Fin 2 → ℂ) (w : KamPhase) (b : Bool) (i : Fin 2) (W : KamPhase) :
    aaDerTanL ξ w b i W = (W.2.1 i / (2 * aaS ξ w i) -
      birkSgn (b, modeIdx i) * (2 * Real.pi * I) * aaS ξ w i * W.1 i) * aaE w b i := by
  simp only [aaDerTanL, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- **`D𝒜_ξ(w)` on `q`-representatives** (`bpW:w5:action-angle` (iii)). -/
def aaDer (a q : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) : KamPhase →L[ℂ] BirkSpace :=
  (∑ i : Fin 2, ∑ b : Bool, (aaDerTanL ξ w b i).smulRight
    (lp.single 2 (b, modeIdx i) (ellWeight a q (modeIdx i) : ℂ) : BirkSpace)) + aaNormal

theorem aaDer_apply (a q : ℝ) (ξ : Fin 2 → ℂ) (w W : KamPhase) :
    aaDer a q ξ w W = aaTanBuild a q (fun b i => aaDerTanL ξ w b i W) + aaNormal W := by
  simp only [aaDer, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.smulRight_apply, aaTanBuild]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← lp.single_smul, smul_eq_mul, mul_comm]

theorem aaDer_tan (a q : ℝ) (ξ : Fin 2 → ℂ) (w W : KamPhase) (b : Bool) (i : Fin 2) :
    aaDer a q ξ w W (b, modeIdx i) = (ellWeight a q (modeIdx i) : ℂ) * aaDerTanL ξ w b i W := by
  rw [aaDer_apply, lp.coeFn_add, Pi.add_apply, aaTanBuild_tan, aaNormal_tan, add_zero]

theorem aaNormal_nor_true (w : KamPhase) (j : ℕ+) :
    aaNormal w (true, j + 2) = (w.2.2.1 j + I * w.2.2.2 j) / birkSqrt2 := by
  simp only [aaNormal_apply, aaShiftFun_add_two, birkSgn, ite_true, one_mul]

theorem aaNormal_nor_false (w : KamPhase) (j : ℕ+) :
    aaNormal w (false, j + 2) = (w.2.2.1 j - I * w.2.2.2 j) / birkSqrt2 := by
  simp only [aaNormal_apply, aaShiftFun_add_two, birkSgn, Bool.false_eq_true, ite_false]
  ring

theorem aaDer_nor_true (a q : ℝ) (ξ : Fin 2 → ℂ) (w W : KamPhase) (j : ℕ+) :
    aaDer a q ξ w W (true, j + 2) = (W.2.2.1 j + I * W.2.2.2 j) / birkSqrt2 := by
  rw [aaDer_apply, lp.coeFn_add, Pi.add_apply, aaTanBuild_nor, zero_add, aaNormal_nor_true]

theorem aaDer_nor_false (a q : ℝ) (ξ : Fin 2 → ℂ) (w W : KamPhase) (j : ℕ+) :
    aaDer a q ξ w W (false, j + 2) = (W.2.2.1 j - I * W.2.2.2 j) / birkSqrt2 := by
  rw [aaDer_apply, lp.coeFn_add, Pi.add_apply, aaTanBuild_nor, zero_add, aaNormal_nor_false]

/-! ### `D𝒜` is the derivative -/

theorem hasFDerivAt_aaS {ξ : Fin 2 → ℂ} {w : KamPhase} {i : Fin 2}
    (h : 0 < (ξ i + w.2.1 i).re) :
    HasFDerivAt (fun w : KamPhase => aaS ξ w i) ((1 / (2 * aaS ξ w i)) •
      ((ContinuousLinearMap.proj i).comp
        ((ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
          (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2))))) w := by
  set L : KamPhase →L[ℂ] ℂ := (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) (HomL2 × HomL2)).comp
      (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2)))
  have hlin : HasFDerivAt (fun w : KamPhase => ξ i + w.2.1 i) L w :=
    (L.hasFDerivAt).const_add (ξ i)
  have hz := ne_zero_of_re_pos h
  have hd := (Complex.hasStrictDerivAt_cpow_const (c := (2⁻¹ : ℂ))
    (mem_slitPlane_of_re_pos h)).hasDerivAt
  have hc := hd.comp_hasFDerivAt w hlin
  have hs := aaS_ne_zero h
  have hss := aaS_mul_self ξ w i
  refine hc.congr_fderiv ?_
  congr 1
  have e : (ξ i + w.2.1 i) ^ ((2⁻¹ : ℂ) - 1) = aaS ξ w i / (ξ i + w.2.1 i) := by
    rw [Complex.cpow_sub _ _ hz, Complex.cpow_one]; rfl
  rw [e, ← hss]
  field_simp

theorem hasFDerivAt_aaE (w : KamPhase) (b : Bool) (i : Fin 2) :
    HasFDerivAt (fun w : KamPhase => aaE w b i)
      ((-(birkSgn (b, modeIdx i)) * (2 * Real.pi * I) * aaE w b i) •
        ((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2)))) w := by
  set L : KamPhase →L[ℂ] ℂ := (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2))
  have h1 : HasFDerivAt (fun w : KamPhase => -(birkSgn (b, modeIdx i)) * (2 * Real.pi * I * w.1 i))
      ((-(birkSgn (b, modeIdx i)) * (2 * Real.pi * I)) • L) w := by
    have := (L.hasFDerivAt (x := w)).const_mul (-(birkSgn (b, modeIdx i)) * (2 * Real.pi * I))
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp [L]
    ring
  have := h1.cexp
  refine this.congr_fderiv ?_
  unfold aaE
  rw [smul_smul]
  ring_nf

theorem hasFDerivAt_aaTanCoord {ξ : Fin 2 → ℂ} {w : KamPhase} {i : Fin 2}
    (h : 0 < (ξ i + w.2.1 i).re) (b : Bool) :
    HasFDerivAt (fun w : KamPhase => aaTanCoord ξ w b i) (aaDerTanL ξ w b i) w := by
  have hp := (hasFDerivAt_aaS h).mul (hasFDerivAt_aaE w b i)
  refine hp.congr_fderiv (ContinuousLinearMap.ext fun W => ?_)
  rw [aaDerTanL_apply]
  simp
  ring

/-- (`bpW:w5:action-angle` (iii)) `D𝒜_ξ(w) = aaDer a p ξ w` (on `p`-representatives). -/
theorem hasFDerivAt_aaMap (a p : ℝ) {ξ : Fin 2 → ℂ} {w : KamPhase}
    (hw : ∀ i, 0 < (ξ i + w.2.1 i).re) :
    HasFDerivAt (aaMap a p ξ) (aaDer a p ξ w) w := by
  have hfun : aaMap a p ξ = fun w => (∑ i : Fin 2, ∑ b : Bool, aaTanCoord ξ w b i •
      (lp.single 2 (b, modeIdx i) (ellWeight a p (modeIdx i) : ℂ) : BirkSpace)) + aaNormal w := by
    funext z
    unfold aaMap aaTan
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← lp.single_smul, smul_eq_mul, mul_comm]
  rw [hfun]
  refine HasFDerivAt.add ?_ aaNormal.hasFDerivAt
  refine HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun b _ => ?_
  exact (hasFDerivAt_aaTanCoord (hw i) b).smul_const _

/-! ### The inverse -/

/-- The sequence `j ↦ x_{j+2}`. -/
theorem memℓp_aaUnshift (x : HomL2) : Memℓp (fun j : ℕ+ => x (j + 2)) 2 := by
  refine memℓp_gen ?_
  have h := ((lp_two_hasSum_sq x).summable.comp_injective aaIdx_injective)
  norm_num
  exact h

/-- The restriction `x ↦ (x_{j+2})_j`, a left inverse of `aaShift`. -/
def aaUnshift : HomL2 →L[ℂ] HomL2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun j => x (j + 2), memℓp_aaUnshift x⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
    1 (fun x => by
      rw [one_mul]
      have h1 := lp_two_hasSum_sq (⟨fun j => x (j + 2), memℓp_aaUnshift x⟩ : HomL2)
      have h2 := lp_two_hasSum_sq x
      have hle : ‖(⟨fun j => x (j + 2), memℓp_aaUnshift x⟩ : HomL2)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
        rw [← h1.tsum_eq, ← h2.tsum_eq]
        exact (h2.summable.comp_injective aaIdx_injective).tsum_le_tsum_of_inj _ aaIdx_injective
          (fun _ _ => by positivity) (fun _ => le_rfl) h2.summable
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hle)

@[simp] theorem aaUnshift_apply (x : HomL2) (j : ℕ+) : aaUnshift x j = x (j + 2) := rfl

/-- Evaluation at `l ∈ BirkIdx`. -/
abbrev aaEv (l : BirkIdx) : BirkSpace →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : BirkIdx => ℂ) 2 l

theorem aaEv_apply (l : BirkIdx) (V : BirkSpace) : aaEv l V = V l := rfl

/-- The `Θ_i`-functional `W ↦ (W_{-i} E_{+,i} - W_i E_{-,i})/(4πi s_i)` (actual coordinates at
`q`). -/
def aaInvTheta (a q : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (i : Fin 2) : BirkSpace →L[ℂ] ℂ :=
  (aaE w true i / (4 * Real.pi * I * aaS ξ w i * ellWeight a q (modeIdx i))) •
      aaEv (false, modeIdx i) -
    (aaE w false i / (4 * Real.pi * I * aaS ξ w i * ellWeight a q (modeIdx i))) •
      aaEv (true, modeIdx i)

/-- The `Y_i`-functional `W ↦ s_i (W_i E_{-,i} + W_{-i} E_{+,i})`. -/
def aaInvY (a q : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (i : Fin 2) : BirkSpace →L[ℂ] ℂ :=
  (aaS ξ w i * aaE w false i / ellWeight a q (modeIdx i)) • aaEv (true, modeIdx i) +
    (aaS ξ w i * aaE w true i / ellWeight a q (modeIdx i)) • aaEv (false, modeIdx i)

/-- **`D𝒜_ξ(w)⁻¹` on `q`-representatives** (`bpW:w5:action-angle` (iii)). -/
def aaDerInv (a q : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) : BirkSpace →L[ℂ] KamPhase :=
  (ContinuousLinearMap.pi fun i => aaInvTheta a q ξ w i).prod
    ((ContinuousLinearMap.pi fun i => aaInvY a q ξ w i).prod
      ((aaUnshift.comp ((ContinuousLinearMap.fst ℂ _ _).comp birkZinv)).prod
        (aaUnshift.comp ((ContinuousLinearMap.snd ℂ _ _).comp birkZinv))))

theorem aaDerInv_theta (a q : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (V : BirkSpace) (i : Fin 2) :
    (aaDerInv a q ξ w V).1 i = (V (false, modeIdx i) * aaE w true i - V (true, modeIdx i) *
      aaE w false i) / (4 * Real.pi * I * aaS ξ w i * ellWeight a q (modeIdx i)) := by
  simp only [aaDerInv, aaInvTheta, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, aaEv_apply,
    smul_eq_mul]
  ring

theorem aaDerInv_y (a q : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (V : BirkSpace) (i : Fin 2) :
    (aaDerInv a q ξ w V).2.1 i = aaS ξ w i * (V (true, modeIdx i) * aaE w false i +
      V (false, modeIdx i) * aaE w true i) / ellWeight a q (modeIdx i) := by
  simp only [aaDerInv, aaInvY, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, aaEv_apply,
    smul_eq_mul]
  ring

theorem aaDerInv_u (a q : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (V : BirkSpace) (j : ℕ+) :
    (aaDerInv a q ξ w V).2.2.1 j = (V (true, j + 2) + V (false, j + 2)) / birkSqrt2 := rfl

theorem aaDerInv_v (a q : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) (V : BirkSpace) (j : ℕ+) :
    (aaDerInv a q ξ w V).2.2.2 j = (V (true, j + 2) - V (false, j + 2)) / (I * birkSqrt2) := rfl

/-- (`bpW:w5:action-angle` (iii)) `D𝒜_ξ(w)⁻¹ D𝒜_ξ(w) = id` on `𝒫^q`. -/
theorem aaDerInv_aaDer (a q : ℝ) {ξ : Fin 2 → ℂ} {w : KamPhase}
    (hw : ∀ i, 0 < (ξ i + w.2.1 i).re) (W : KamPhase) :
    aaDerInv a q ξ w (aaDer a q ξ w W) = W := by
  have h2 := birkSqrt2_ne
  have hs2 := birkSqrt2_sq
  have hI := Complex.I_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_)
    (Prod.ext (lp.ext (funext fun j => ?_)) (lp.ext (funext fun j => ?_))))
  · rw [aaDerInv_theta, aaDer_tan, aaDer_tan, aaDerTanL_apply, aaDerTanL_apply]
    have hs := aaS_ne_zero (hw i)
    have hE := aaE_mul w i
    have hω : (ellWeight a q (modeIdx i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (ellWeight_ne_zero a q (modeIdx i))
    have hEf : aaE w false i = (aaE w true i)⁻¹ := eq_inv_of_mul_eq_one_right hE
    have hE0 := aaE_ne_zero w true i
    simp only [birkSgn_true, birkSgn_false, hEf]
    field_simp
    ring
  · rw [aaDerInv_y, aaDer_tan, aaDer_tan, aaDerTanL_apply, aaDerTanL_apply]
    have hs := aaS_ne_zero (hw i)
    have hE := aaE_mul w i
    have hω : (ellWeight a q (modeIdx i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (ellWeight_ne_zero a q (modeIdx i))
    have hEf : aaE w false i = (aaE w true i)⁻¹ := eq_inv_of_mul_eq_one_right hE
    have hE0 := aaE_ne_zero w true i
    simp only [birkSgn_true, birkSgn_false, hEf]
    field_simp
    ring
  · rw [aaDerInv_u, aaDer_nor_true, aaDer_nor_false]
    field_simp
    linear_combination (-(W.2.2.1 j : ℂ)) * hs2
  · rw [aaDerInv_v, aaDer_nor_true, aaDer_nor_false]
    field_simp
    linear_combination (-((W.2.2.2 j : ℂ) * I)) * hs2

/-- (`bpW:w5:action-angle` (iii)) `D𝒜_ξ(w) D𝒜_ξ(w)⁻¹ = id` on `𝔚^q`. -/
theorem aaDer_aaDerInv (a q : ℝ) {ξ : Fin 2 → ℂ} {w : KamPhase}
    (hw : ∀ i, 0 < (ξ i + w.2.1 i).re) (V : BirkSpace) :
    aaDer a q ξ w (aaDerInv a q ξ w V) = V := by
  have h2 := birkSqrt2_ne
  have hs2 := birkSqrt2_sq
  have hI := Complex.I_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  ext ⟨b, J⟩
  rcases modeIdx_cases J with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [aaDer_tan, aaDerTanL_apply, aaDerInv_theta, aaDerInv_y]
    have hs := aaS_ne_zero (hw i)
    have hE := aaE_mul w i
    have hω : (ellWeight a q (modeIdx i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (ellWeight_ne_zero a q (modeIdx i))
    have hEf : aaE w false i = (aaE w true i)⁻¹ := eq_inv_of_mul_eq_one_right hE
    have hE0 := aaE_ne_zero w true i
    cases b
    · simp only [birkSgn_false, hEf]
      field_simp
      ring
    · simp only [birkSgn_true, hEf]
      field_simp
      ring
  · cases b
    · rw [aaDer_nor_false, aaDerInv_u, aaDerInv_v]
      field_simp
      linear_combination (-(V (false, j + 2))) * hs2
    · rw [aaDer_nor_true, aaDerInv_u, aaDerInv_v]
      field_simp
      linear_combination (-(V (true, j + 2))) * hs2

end KAM.Wave

end
