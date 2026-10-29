/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.RealFlow
public import KAM.Planetary.MaximalStep.Homological
public import KAM.Planetary.MaximalStep.Divisor
public import KAM.Strip.FourierBasic

/-!
# The angle map on the reals: the literal nodes (P11A-C7)

Unsigned literal exports of `stepP:p11a:rl-const` and `bpP:p11a:real-lipschitz` for a real
`1`-periodic trigonometric polynomial `φ₁ : ℝᴺ → ℝᴺ` of degree `≤ T` (`RealTrigPolyDeg`):

* `rl_const_node`: `Λ := sup ‖Dφ₁‖ ≤ 2πT max_i ∑_{0<|k|₁≤T} |φ̂_{1,i,k}|`, and under the decay
  bound of `homological-maximal (e)`, this is `≤ 2 T M₁ Λ_{r*} / D`;
* `real_lipschitz_node`: for `|t| ≤ 1`, `‖DΘᵗ - 1‖ ≤ e^Λ - 1`, `Θᵗ(θ + k) = Θᵗ(θ) + k`,
  `‖Θᵗ(θ) - θ‖ ≤ sup‖φ₁‖`, together with both clauses of `rl_const_node`.

The coefficients `φ̂_{1,i,k}` are `KAM.torusCoeff` of the components of `φ₁`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- A real trigonometric polynomial `φ : ℝᴺ → ℝᴺ` of degree `≤ T`: every component is a finite
Fourier sum over the modes `|k|₁ ≤ T`. -/
def RealTrigPolyDeg {n : ℕ} (T : ℝ) (φ : P11Vec n → P11Vec n) : Prop :=
  ∀ i : Fin n, ∃ a : (Fin n → ℤ) → ℂ, (∀ k, T < KAM.Fourier.modeSize k → a k = 0) ∧
    ∀ x : P11Vec n, (φ x i : ℂ) = KAM.fourierSum a (fun j => (x j : ℂ))

section Trig
variable {n : ℕ} {T : ℝ} {φ : P11Vec n → P11Vec n}

theorem rtp_support {a : (Fin n → ℤ) → ℂ} (ha : ∀ k, T < KAM.Fourier.modeSize k → a k = 0)
    {k : Fin n → ℤ} (hk : k ∉ hmModes n T) : a k = 0 := by
  refine ha k ?_
  by_contra hc
  exact hk (mem_hmModes_of_le (not_lt.1 hc))

/-- The Fourier coefficients of a real trigonometric polynomial are its defining coefficients. -/
theorem rtp_coeff {a : (Fin n → ℤ) → ℂ} (ha : ∀ k, T < KAM.Fourier.modeSize k → a k = 0)
    {i : Fin n} (hi : ∀ x : P11Vec n, (φ x i : ℂ) = KAM.fourierSum a (fun j => (x j : ℂ)))
    (k : Fin n → ℤ) : KAM.torusCoeff (fun x => (φ x i : ℂ)) k = a k := by
  have : (fun x => (φ x i : ℂ)) = fun x => KAM.fourierSum a (fun j => (x j : ℂ)) := funext hi
  rw [this]
  exact torusCoeff_fourierSum_finset (S := hmModes n T) (fun k hk => rtp_support ha hk) k

theorem rtp_entire {a : (Fin n → ℤ) → ℂ} (ha : ∀ k, T < KAM.Fourier.modeSize k → a k = 0) :
    Differentiable ℂ (KAM.fourierSum a) :=
  differentiable_fourierSum_finset (S := hmModes n T) fun _ hk => rtp_support ha hk

theorem rtp_contDiff (hφ : RealTrigPolyDeg T φ) : ContDiff ℝ 2 φ := by
  refine contDiff_pi.2 fun i => ?_
  obtain ⟨a, ha, hi⟩ := hφ i
  have e : (fun x => φ x i) = fun x => (KAM.fourierSum a (fun j => (x j : ℂ))).re := by
    funext x
    have := congrArg Complex.re (hi x)
    simpa using this
  rw [e]
  have h1 : ContDiff ℝ 2 (KAM.fourierSum a) :=
    ((contDiffOn_univ.1 (KAM.holomorphic_regularity_of_finiteDimensional isOpen_univ
      (rtp_entire ha).differentiableOn).2.2.1).restrict_scalars ℝ).of_le (by simp)
  exact Complex.reCLM.contDiff.comp (h1.comp (KAM.realInclusion n).contDiff)

theorem rtp_periodic (hφ : RealTrigPolyDeg T φ) (x : P11Vec n) (m : Fin n → ℤ) :
    φ (x + fun i => (m i : ℝ)) = φ x := by
  refine KAM.periodic_intVec (v := φ) (fun j y => ?_) m x
  funext i
  obtain ⟨a, ha, hi⟩ := hφ i
  have h1 : (φ (y + Pi.single j 1) i : ℂ) = (φ y i : ℂ) := by
    rw [hi, hi]
    have : (fun l => (((y + Pi.single j 1 : P11Vec n) l : ℝ) : ℂ)) =
        (fun l => (y l : ℂ)) + Pi.single j 1 := by
      ext l; by_cases h : l = j <;> simp [h]
    rw [this, KAM.fourierSum_add_single]
  exact_mod_cast h1

theorem rtp_value_le (hφ : RealTrigPolyDeg T φ) (x : P11Vec n) :
    ‖φ x‖ ≤ ∑ i, ∑ k ∈ hmModes n T, ‖(Classical.choose (hφ i)) k‖ := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => norm_nonneg _)).2 fun i => ?_
  obtain ⟨ha, hi⟩ := Classical.choose_spec (hφ i)
  set a := Classical.choose (hφ i)
  have h1 : ‖φ x i‖ = ‖(φ x i : ℂ)‖ := by simp
  rw [h1, hi x, fourierSum_finset (S := hmModes n T) fun k hk => rtp_support ha hk]
  refine (norm_sum_le _ _).trans ?_
  have hmem : ∑ k ∈ hmModes n T, ‖a k‖ ≤ ∑ i, ∑ k ∈ hmModes n T, ‖(Classical.choose (hφ i)) k‖ :=
    Finset.single_le_sum (f := fun i => ∑ k ∈ hmModes n T, ‖(Classical.choose (hφ i)) k‖)
      (fun i _ => Finset.sum_nonneg fun k _ => norm_nonneg _) (Finset.mem_univ i)
  refine le_trans (le_of_eq ?_) hmem
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, KAM.norm_character_real, mul_one]

/-- The derivative of a Fourier sum with finitely many modes at a real point, in a real
direction: `|Dφ(x) v| ≤ 2πT ‖v‖ ∑_{0<|k|₁≤T} |a_k|`. -/
theorem rtp_fderiv_le (hT : 0 ≤ T) {a : (Fin n → ℤ) → ℂ}
    (ha : ∀ k, T < KAM.Fourier.modeSize k → a k = 0) (x v : P11Vec n) :
    ‖fderiv ℂ (KAM.fourierSum a) (KAM.realInclusion n x) (KAM.realInclusion n v)‖ ≤
      2 * Real.pi * T * ‖v‖ *
        ∑ k ∈ (hmModes n T).filter (fun k => k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T), ‖a k‖ := by
  rw [fderiv_fourierSum_finset (S := hmModes n T) fun k hk => rtp_support ha hk]
  have hv : ‖KAM.realInclusion n v‖ ≤ ‖v‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by simpa using norm_le_pi_norm v j
  have h2π : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul]; simp
  have hterm : ∀ k ∈ hmModes n T,
      ‖a k * (2 * Real.pi * Complex.I * p11dotC k (KAM.realInclusion n v)) *
        KAM.character k (KAM.realInclusion n x)‖ ≤
      if k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T then ‖a k‖ * (2 * Real.pi * T * ‖v‖) else 0 := by
    intro k _
    by_cases hk0 : k = 0
    · simp [hk0, p11dotC]
    by_cases hkT : KAM.Fourier.modeSize k ≤ T
    · simp only [ne_eq, hk0, not_false_eq_true, hkT, and_self, ite_true]
      have hdot : ‖p11dotC k (KAM.realInclusion n v)‖ ≤ T * ‖v‖ :=
        (p11_norm_dotC_le k _).trans (mul_le_mul hkT hv (norm_nonneg _) hT)
      have hch : ‖KAM.character k (KAM.realInclusion n x)‖ = 1 := KAM.norm_character_real k x
      rw [norm_mul, norm_mul, norm_mul, hch, h2π, mul_one]
      calc ‖a k‖ * (2 * Real.pi * ‖p11dotC k (KAM.realInclusion n v)‖)
          ≤ ‖a k‖ * (2 * Real.pi * (T * ‖v‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdot (by positivity))
              (norm_nonneg _)
        _ = ‖a k‖ * (2 * Real.pi * T * ‖v‖) := by ring
    · have : a k = 0 := ha k (not_le.1 hkT)
      simp [this]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  ring

/-- The row-sum constant `∑_{0<|k|₁≤T} |φ̂_{1,i,k}|`. -/
def rtpRowSum (T : ℝ) (φ : P11Vec n → P11Vec n) (i : Fin n) : ℝ :=
  ∑ k ∈ (hmModes n T).filter (fun k => k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T),
    ‖KAM.torusCoeff (fun x => (φ x i : ℂ)) k‖

theorem rtpRowSum_nonneg (i : Fin n) : 0 ≤ rtpRowSum T φ i :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem rtp_row_le_iSup (i : Fin n) : rtpRowSum T φ i ≤ ⨆ j, rtpRowSum T φ j :=
  le_ciSup (Finite.bddAbove_range _) i

theorem iSup_rtpRowSum_nonneg : 0 ≤ ⨆ j, rtpRowSum T φ j :=
  Real.iSup_nonneg fun j => rtpRowSum_nonneg j

theorem rtp_fderiv_norm_le (hT : 0 ≤ T) (hφ : RealTrigPolyDeg T φ) (x : P11Vec n) :
    ‖fderiv ℝ φ x‖ ≤ 2 * Real.pi * T * ⨆ j, rtpRowSum T φ j := by
  have hC : 0 ≤ 2 * Real.pi * T * ⨆ j, rtpRowSum T φ j := by
    have := iSup_rtpRowSum_nonneg (T := T) (φ := φ); positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by have := norm_nonneg v; positivity)).2 fun i => ?_
  obtain ⟨a, ha, hi⟩ := hφ i
  have hd : DifferentiableAt ℝ φ x := ((rtp_contDiff hφ).differentiable (by norm_num)) x
  have h1 := hasFDerivAt_pi'.1 hd.hasFDerivAt i
  have hf := ((rtp_entire ha).differentiableAt (x := KAM.realInclusion n x)).hasFDerivAt
    |>.restrictScalars ℝ
  have h2 := Complex.reCLM.hasFDerivAt.comp x (hf.comp x (KAM.realInclusion n).hasFDerivAt)
  have h3 := h1.unique (by
    have e : (fun y => φ y i) = fun y => (KAM.fourierSum a (fun j => (y j : ℂ))).re := by
      funext y
      have := congrArg Complex.re (hi y)
      simpa using this
    rw [e]
    exact h2)
  have h4 := congrArg (fun L => L v) h3
  have e5 : fderiv ℝ φ x v i = (fderiv ℂ (KAM.fourierSum a) (KAM.realInclusion n x)
      (KAM.realInclusion n v)).re := by
    have := h4
    simpa using this
  rw [e5]
  refine ((Real.norm_eq_abs _).le.trans (Complex.abs_re_le_norm _)).trans ?_
  refine (rtp_fderiv_le hT ha x v).trans ?_
  have hrow : ∑ k ∈ (hmModes n T).filter (fun k => k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T), ‖a k‖ =
      rtpRowSum T φ i := by
    unfold rtpRowSum
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rtp_coeff ha hi]
  rw [hrow]
  have := rtp_row_le_iSup (T := T) (φ := φ) i
  have h0 : 0 ≤ 2 * Real.pi * T * ‖v‖ := by positivity
  calc 2 * Real.pi * T * ‖v‖ * rtpRowSum T φ i ≤ 2 * Real.pi * T * ‖v‖ * ⨆ j, rtpRowSum T φ j :=
        mul_le_mul_of_nonneg_left this h0
    _ = _ := by ring

theorem iSup_fderiv_le (hT : 0 ≤ T) (hφ : RealTrigPolyDeg T φ) :
    (⨆ x, ‖fderiv ℝ φ x‖) ≤ 2 * Real.pi * T * ⨆ j, rtpRowSum T φ j := by
  have := iSup_rtpRowSum_nonneg (T := T) (φ := φ)
  exact Real.iSup_le (fun x => rtp_fderiv_norm_le hT hφ x) (by positivity)

theorem fderiv_bddAbove (hT : 0 ≤ T) (hφ : RealTrigPolyDeg T φ) :
    BddAbove (Set.range fun x => ‖fderiv ℝ φ x‖) :=
  ⟨_, by rintro _ ⟨x, rfl⟩; exact rtp_fderiv_norm_le hT hφ x⟩

theorem value_bddAbove (hφ : RealTrigPolyDeg T φ) : BddAbove (Set.range fun x => ‖φ x‖) :=
  ⟨_, by rintro _ ⟨x, rfl⟩; exact rtp_value_le hφ x⟩

/-- `stepP:p11a:rl-const`: `Λ ≤ 2πT max_i ∑_{0<|k|₁≤T} |φ̂_{1,i,k}|`, and under the decay bound
`|φ̂_{1,i,k}| ≤ M₁ e^{-2π|k|₁ r_*}/(πD)` this is `≤ 2 T M₁ Λ_{r_*}/D`.
The degree-zero (constant) case `T = 0` is included. The premise `0 ≤ M₁` is a candidate source
erratum (orchestrator ruling OVERNIGHT 03:15, owner to review; audit 1, F1): the standalone
source statement needs it, as `M₁ < 0` with a vacuous decay hypothesis is a counterexample. -/
theorem rl_const_node {n : ℕ} {T rs D M1 : ℝ} (hT : 0 ≤ T) (hrs : 0 < rs) (hD : 0 < D)
    (hM1 : 0 ≤ M1) {φ : P11Vec n → P11Vec n} (hφ : RealTrigPolyDeg T φ) :
    (⨆ x, ‖fderiv ℝ φ x‖) ≤ 2 * Real.pi * T * ⨆ i : Fin n,
        ∑ k ∈ (hmModes n T).filter (fun k => k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T),
          ‖KAM.torusCoeff (fun x => (φ x i : ℂ)) k‖ ∧
    ((∀ (i : Fin n) (k : Fin n → ℤ), k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
        ‖KAM.torusCoeff (fun x => (φ x i : ℂ)) k‖ ≤
          M1 * Real.exp (-2 * Real.pi * KAM.Fourier.modeSize k * rs) / (Real.pi * D)) →
      2 * Real.pi * T * ⨆ i : Fin n,
        ∑ k ∈ (hmModes n T).filter (fun k => k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T),
          ‖KAM.torusCoeff (fun x => (φ x i : ℂ)) k‖ ≤ 2 * T * M1 * p11Lambda n rs / D) := by
  refine ⟨iSup_fderiv_le hT hφ, fun hdec => ?_⟩
  have hΛ : 0 ≤ p11Lambda n rs := by
    have := sum_exp_le_lambda (n := n) hrs (∅ : Finset (Fin n → ℤ)) (by simp)
    simpa using this
  have hrow : ∀ i, rtpRowSum T φ i ≤ M1 * p11Lambda n rs / (Real.pi * D) := by
    intro i
    have hs := sum_exp_le_lambda hrs ((hmModes n T).filter
      fun k => k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T) (fun k hk => (Finset.mem_filter.1 hk).2.1)
    calc rtpRowSum T φ i
        ≤ ∑ k ∈ (hmModes n T).filter (fun k => k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T),
            M1 / (Real.pi * D) * Real.exp (-2 * Real.pi * rs * KAM.Fourier.modeSize k) := by
          refine Finset.sum_le_sum fun k hk => ?_
          obtain ⟨-, hk0, hkT⟩ := Finset.mem_filter.1 hk
          refine (hdec i k hk0 hkT).trans (le_of_eq ?_)
          rw [show -2 * Real.pi * rs * KAM.Fourier.modeSize k =
            -2 * Real.pi * KAM.Fourier.modeSize k * rs by ring]
          ring
      _ = M1 / (Real.pi * D) * ∑ k ∈ (hmModes n T).filter
            (fun k => k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T),
            Real.exp (-2 * Real.pi * rs * KAM.Fourier.modeSize k) := by rw [Finset.mul_sum]
      _ ≤ M1 / (Real.pi * D) * p11Lambda n rs :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have hsup : (⨆ i : Fin n, rtpRowSum T φ i) ≤ M1 * p11Lambda n rs / (Real.pi * D) :=
    Real.iSup_le hrow (by positivity)
  calc 2 * Real.pi * T * ⨆ i : Fin n, rtpRowSum T φ i
      ≤ 2 * Real.pi * T * (M1 * p11Lambda n rs / (Real.pi * D)) :=
        mul_le_mul_of_nonneg_left hsup (by positivity)
    _ = 2 * T * M1 * p11Lambda n rs / D := by field_simp

/-- `bpP:p11a:real-lipschitz`: for a real `1`-periodic trigonometric polynomial `φ₁` of degree
`≤ T` (`0 ≤ T`, including constants; `0 ≤ M₁` as in `rl_const_node`, ruling OVERNIGHT 03:15),
with `Λ = sup ‖Dφ₁‖` and `Θᵗ` the flow, for `|t| ≤ 1`: `‖DΘᵗ - 1‖ ≤ e^Λ - 1`,
`Θᵗ(θ + k) = Θᵗ(θ) + k`, `‖Θᵗ(θ) - θ‖ ≤ sup‖φ₁‖`; and the two clauses of `rl_const_node`. -/
theorem real_lipschitz_node {n : ℕ} {T rs D M1 : ℝ} (hT : 0 ≤ T) (hrs : 0 < rs) (hD : 0 < D)
    (hM1 : 0 ≤ M1) {φ : P11Vec n → P11Vec n} (hφ : RealTrigPolyDeg T φ) :
    (∀ t ∈ Icc (-1 : ℝ) 1, ∀ θ : P11Vec n,
      ‖fderiv ℝ (p11RealFlow φ t) θ - ContinuousLinearMap.id ℝ _‖ ≤
        Real.exp (⨆ x, ‖fderiv ℝ φ x‖) - 1 ∧
      (∀ k : Fin n → ℤ, p11RealFlow φ t (θ + fun i => (k i : ℝ)) =
        p11RealFlow φ t θ + fun i => (k i : ℝ)) ∧
      ‖p11RealFlow φ t θ - θ‖ ≤ ⨆ x, ‖φ x‖) ∧
    (⨆ x, ‖fderiv ℝ φ x‖) ≤ 2 * Real.pi * T * ⨆ i : Fin n,
        ∑ k ∈ (hmModes n T).filter (fun k => k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T),
          ‖KAM.torusCoeff (fun x => (φ x i : ℂ)) k‖ ∧
    ((∀ (i : Fin n) (k : Fin n → ℤ), k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
        ‖KAM.torusCoeff (fun x => (φ x i : ℂ)) k‖ ≤
          M1 * Real.exp (-2 * Real.pi * KAM.Fourier.modeSize k * rs) / (Real.pi * D)) →
      2 * Real.pi * T * ⨆ i : Fin n,
        ∑ k ∈ (hmModes n T).filter (fun k => k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T),
          ‖KAM.torusCoeff (fun x => (φ x i : ℂ)) k‖ ≤ 2 * T * M1 * p11Lambda n rs / D) := by
  refine ⟨fun t ht θ => ?_, rl_const_node hT hrs hD hM1 hφ⟩
  have hM : 0 ≤ ⨆ x, ‖φ x‖ := Real.iSup_nonneg fun x => norm_nonneg _
  have hL : 0 ≤ ⨆ x, ‖fderiv ℝ φ x‖ := Real.iSup_nonneg fun x => norm_nonneg _
  have key := real_lipschitz (rtp_contDiff hφ) hM hL
    (fun x => le_ciSup (value_bddAbove hφ) x) (fun x => le_ciSup (fderiv_bddAbove hT hφ) x)
    (fun x k => rtp_periodic hφ x k) t ht θ
  exact ⟨key.1, key.2.2, key.2.1⟩

end Trig

end KAM.Planetary

end
