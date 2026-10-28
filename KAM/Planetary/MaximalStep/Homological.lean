/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.FourierSeriesVector
public import KAM.Weighted.Projections
public import KAM.Weighted.Parametric
public import KAM.Planetary.MaximalStep.Constants
public import KAM.Planetary.MaximalStep.Parameter

/-!
# Maximal homological equation (P11A-C5, `bpP:p11a:homological-maximal`)

The solution `p11Solve T w P` of `ω(b)·∂_θ φ = P - ⟨P⟩` is the explicit finite trigonometric sum
`∑_{0<|k|₁≤T} P̂_k(b) / (2πi k·ω(b)) χ_k(θ)`. Here `hmCoef` is its coefficient family and
`hmCut` the coefficient family of the truncated datum; every statement is read off from the finite
Fourier sums (`stepP:p11a:hm-coeff`, `hm-a`, `hm-bc`, `hm-d`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- The generator is defined from existing scalar truncation; no Diophantine premise. -/
def p11Solve {n : ℕ} (T : ℝ) (w : P11CVec n → P11CVec n)
    (P : P11CVec n × P11CVec n → ℂ) (theta b : P11CVec n) : ℂ :=
  ∑' k : Fin n → ℤ, if k=0 ∨ T < KAM.Fourier.modeSize k then 0 else
    KAM.Weighted.coeff P b k / (2*Real.pi*Complex.I*p11dotC k (w b)) * KAM.character k theta
def p11AngleClass {n : ℕ} (r : ℝ) (B : Set (P11CVec n))
    (P : P11CVec n × P11CVec n → ℂ) : Prop :=
  DifferentiableOn ℂ P (KAM.complexStrip n r ×ˢ B) ∧
    ∀ j : Fin n, ∀ z ∈ KAM.complexStrip n r ×ˢ B, P (z.1+Pi.single j 1,z.2)=P z
def p11AngleAverage {n : ℕ} (P : P11CVec n × P11CVec n → ℂ) (b : P11CVec n) : ℂ :=
  KAM.Weighted.coeff P b 0

/-! ### Finite trigonometric sums -/

/-- The coefficients of `p11Solve T w P ·  b`. -/
def hmCoef {n : ℕ} (T : ℝ) (w : P11CVec n → P11CVec n) (P : P11CVec n × P11CVec n → ℂ)
    (b : P11CVec n) (k : Fin n → ℤ) : ℂ :=
  if k=0 ∨ T < KAM.Fourier.modeSize k then 0 else
    KAM.Weighted.coeff P b k / (2*Real.pi*Complex.I*p11dotC k (w b))

/-- The coefficients of the truncation `T_T P`. -/
def hmCut {n : ℕ} (T : ℝ) (P : P11CVec n × P11CVec n → ℂ) (b : P11CVec n)
    (k : Fin n → ℤ) : ℂ :=
  if KAM.Fourier.modeSize k ≤ T then KAM.Weighted.coeff P b k else 0

/-- The finite set of modes `|k|₁ ≤ T`. -/
def hmModes (n : ℕ) (T : ℝ) : Finset (Fin n → ℤ) := KAM.modeCutoff n ⌈T⌉₊

theorem mem_hmModes {n : ℕ} {T : ℝ} {k : Fin n → ℤ} :
    k ∈ hmModes n T ↔ KAM.Fourier.modeSize k ≤ ⌈T⌉₊ := KAM.mem_modeCutoff

theorem mem_hmModes_of_le {n : ℕ} {T : ℝ} {k : Fin n → ℤ} (h : KAM.Fourier.modeSize k ≤ T) :
    k ∈ hmModes n T := mem_hmModes.2 (h.trans (Nat.le_ceil T))

theorem p11Solve_eq {n : ℕ} (T : ℝ) (w : P11CVec n → P11CVec n)
    (P : P11CVec n × P11CVec n → ℂ) (theta b : P11CVec n) :
    p11Solve T w P theta b = KAM.fourierSum (hmCoef T w P b) theta := by
  unfold p11Solve KAM.fourierSum hmCoef
  refine tsum_congr fun k => ?_
  split_ifs <;> simp

theorem truncate_eq {n : ℕ} (T : ℝ) (P : P11CVec n × P11CVec n → ℂ) (theta b : P11CVec n) :
    KAM.Weighted.truncate T P (theta, b) = KAM.fourierSum (hmCut T P b) theta := by
  unfold KAM.Weighted.truncate KAM.Weighted.projMode KAM.fourierSum hmCut
  refine tsum_congr fun k => ?_
  by_cases h : KAM.Fourier.modeSize k ≤ T <;> simp [Set.indicator, h]

theorem hmCoef_eq_zero {n : ℕ} {T : ℝ} {w : P11CVec n → P11CVec n}
    {P : P11CVec n × P11CVec n → ℂ} {b : P11CVec n} {k : Fin n → ℤ}
    (h : k ∉ hmModes n T) : hmCoef T w P b k = 0 := by
  have : T < KAM.Fourier.modeSize k := by
    by_contra hc
    exact h (mem_hmModes_of_le (not_lt.1 hc))
  simp [hmCoef, this]

theorem hmCut_eq_zero {n : ℕ} {T : ℝ} {P : P11CVec n × P11CVec n → ℂ} {b : P11CVec n}
    {k : Fin n → ℤ} (h : k ∉ hmModes n T) : hmCut T P b k = 0 := by
  have : ¬ KAM.Fourier.modeSize k ≤ T := fun hc => h (mem_hmModes_of_le hc)
  simp [hmCut, this]

/-- A finitely supported coefficient family. -/
theorem fourierSum_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) (theta : Fin n → ℂ) :
    KAM.fourierSum a theta = ∑ k ∈ S, a k * KAM.character k theta :=
  tsum_eq_sum fun k hk => by simp [hS k hk]

theorem summableWeighted_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) (s : ℝ) : KAM.Fourier.SummableWeighted s a :=
  summable_of_ne_finset_zero (s := S) fun k hk => by simp [hS k hk]

theorem torusCoeff_fourierSum_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) (k : Fin n → ℤ) :
    KAM.torusCoeff (fun x => KAM.fourierSum a (fun j => (x j : ℂ))) k = a k :=
  KAM.torusCoeff_fourierSum (le_refl 0) (by simpa using summableWeighted_finset hS _) k

theorem hasFDerivAt_fourierSum_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) (theta : Fin n → ℂ) :
    HasFDerivAt (KAM.fourierSum a)
      (∑ k ∈ S, a k • (KAM.character k theta • ((2*Real.pi*Complex.I : ℂ) • KAM.modeForm k)))
      theta := by
  have hfun : KAM.fourierSum a = fun x => ∑ k ∈ S, a k * KAM.character k x := by
    funext x; exact fourierSum_finset hS x
  rw [hfun]
  refine HasFDerivAt.fun_sum fun k _ => ?_
  exact ((KAM.hasFDerivAt_character k theta).const_mul (a k))

theorem fderiv_fourierSum_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) (theta v : Fin n → ℂ) :
    fderiv ℂ (KAM.fourierSum a) theta v =
      ∑ k ∈ S, a k * (2*Real.pi*Complex.I*p11dotC k v) * KAM.character k theta := by
  rw [(hasFDerivAt_fourierSum_finset hS theta).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    KAM.modeForm_apply, p11dotC]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem differentiable_fourierSum_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) : Differentiable ℂ (KAM.fourierSum a) := fun theta =>
  (hasFDerivAt_fourierSum_finset hS theta).differentiableAt

/-! ### Coefficients of the datum -/

section Coeff
variable {n : ℕ} {r M : ℝ} {B : Set (P11CVec n)} {P : P11CVec n × P11CVec n → ℂ}

/-- `bp:p1:decay` for the datum, uniformly in the parameter. -/
theorem norm_coeff_le (hr : 0 < r) (hP : p11AngleClass r B P)
    (hb : p11Bound (KAM.complexStrip n r ×ˢ B) P M) {b : P11CVec n} (hbB : b ∈ B)
    (k : Fin n → ℤ) :
    ‖KAM.Weighted.coeff P b k‖ ≤ Real.exp (-(2*Real.pi*r*KAM.Fourier.modeSize k)) * M := by
  have hd : DifferentiableOn ℂ (fun θ => P (θ, b)) (KAM.complexStrip n r) :=
    hP.1.comp (differentiableOn_id.prodMk (differentiableOn_const b)) fun θ hθ => ⟨hθ, hbB⟩
  exact KAM.norm_torusCoeff_le hr hd (fun i z hz => hP.2 i (z, b) ⟨hz, hbB⟩)
    (fun z hz => hb (z, b) ⟨hz, hbB⟩) k

/-- The Fourier coefficients are holomorphic in the parameter (`hm-coeff`, parametric integral). -/
theorem differentiableOn_coeff (hr : 0 < r) (hB : IsOpen B)
    (hP : DifferentiableOn ℂ P (KAM.complexStrip n r ×ˢ B)) (k : Fin n → ℤ) :
    DifferentiableOn ℂ (fun b => KAM.Weighted.coeff P b k) B := by
  have hQ : IsCompact (Set.pi Set.univ fun _ : Fin n => Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hU : IsOpen (KAM.complexStrip n r ×ˢ B) := (KAM.isOpen_complexStrip n r).prod hB
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional hU hP
  have hrealc : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hmem : ∀ x : Fin n → ℝ, ∀ b ∈ B, ((fun j => (x j : ℂ)), b) ∈ KAM.complexStrip n r ×ˢ B :=
    fun x b hb => ⟨KAM.ofReal_mem_complexStrip hr x, hb⟩
  have hmaps : MapsTo (fun y : (Fin n → ℝ) × P11CVec n => ((fun j => (y.1 j : ℂ)), y.2))
      (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1) ×ˢ B) (KAM.complexStrip n r ×ˢ B) :=
    fun y hy => hmem y.1 y.2 hy.2
  have hmapc : Continuous fun y : (Fin n → ℝ) × P11CVec n => ((fun j => (y.1 j : ℂ)), y.2) :=
    (hrealc.comp continuous_fst).prodMk continuous_snd
  have hchar : Continuous fun y : (Fin n → ℝ) × P11CVec n =>
      KAM.character (-k) (fun j => (y.1 j : ℂ)) :=
    ((KAM.differentiable_character (-k)).continuous.comp hrealc).comp continuous_fst
  have hGd : ∀ x : Fin n → ℝ, DifferentiableOn ℂ
      (fun I => KAM.character (-k) (fun j => (x j : ℂ)) * P ((fun j => (x j : ℂ)), I)) B := by
    intro x
    have hmI : MapsTo (fun I : P11CVec n => ((fun j => (x j : ℂ)), I)) B
        (KAM.complexStrip n r ×ˢ B) := fun I hI => hmem x I hI
    exact ((hP.comp (differentiableOn_const _ |>.prodMk differentiableOn_id) hmI)).const_mul _
  have hfd : ∀ x : Fin n → ℝ, ∀ I ∈ B,
      fderiv ℂ (fun I => KAM.character (-k) (fun j => (x j : ℂ)) *
        P ((fun j => (x j : ℂ)), I)) I =
      KAM.character (-k) (fun j => (x j : ℂ)) •
        (fderiv ℂ P ((fun j => (x j : ℂ)), I)).comp
          (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (Fin n → ℂ)) := by
    intro x I hI
    have hz := hmem x I hI
    have hud : HasFDerivAt P (fderiv ℂ P ((fun j => (x j : ℂ)), I))
        ((fun j => (x j : ℂ)), I) :=
      (hP.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    exact ((hud.comp I (hasFDerivAt_prodMk_right (𝕜 := ℂ) (fun j => (x j : ℂ)) I)).const_mul
      _).fderiv
  refine (KAM.Weighted.holomorphic_parametric_integral (W := ℂ) hQ hB
    (G := fun x I => KAM.character (-k) (fun j => (x j : ℂ)) * P ((fun j => (x j : ℂ)), I))
    ?_ (fun x _ => hGd x) ?_).1
  · exact hchar.continuousOn.mul (hP.continuousOn.comp hmapc.continuousOn hmaps)
  · refine ContinuousOn.congr ?_ (fun y hy => hfd y.1 y.2 hy.2)
    refine hchar.continuousOn.smul ?_
    exact ContinuousOn.clm_comp (hreg.1.continuousOn.comp hmapc.continuousOn hmaps)
      continuousOn_const

end Coeff

/-! ### The bound of the solution (`hm-a`) -/

/-- The finite lattice sum is bounded by `p11Lambda` (also for `n = 0`, where it is empty). -/
theorem sum_exp_le_lambda {n : ℕ} {delta : ℝ} (hd : 0 < delta) (F : Finset (Fin n → ℤ))
    (hF : ∀ k ∈ F, k ≠ 0) :
    ∑ k ∈ F, Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k) ≤ p11Lambda n delta := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : F = ∅ := Finset.eq_empty_of_forall_notMem fun k hk =>
      hF k hk (Subsingleton.elim _ _)
    simp [this, p11Lambda]
  · obtain ⟨hs, htsum, -, -⟩ := p11_lambda_spec hn hd
    calc ∑ k ∈ F, Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k)
        = ∑ x ∈ F.subtype (fun k => k ≠ 0),
            Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize x.val) :=
          (Finset.sum_subtype_of_mem (fun k => Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k))
            hF).symm
      _ ≤ ∑' x : {k : Fin n → ℤ // k ≠ 0},
            Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize x.val) :=
          hs.sum_le_tsum _ fun _ _ => (Real.exp_pos _).le
      _ = p11Lambda n delta := htsum

section Bound
variable {n : ℕ} {r M T D : ℝ} {B : Set (P11CVec n)} {P : P11CVec n × P11CVec n → ℂ}
  {w : P11CVec n → P11CVec n}

theorem norm_hmCoef_le (hD : 0 < D) (hr : 0 < r) (hP : p11AngleClass r B P)
    (hb : p11Bound (KAM.complexStrip n r ×ˢ B) P M) {b : P11CVec n} (hbB : b ∈ B)
    (hdiv : ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    {k : Fin n → ℤ} (hk : k ≠ 0) (hkT : KAM.Fourier.modeSize k ≤ T) :
    ‖hmCoef T w P b k‖ ≤ Real.exp (-(2*Real.pi*r*KAM.Fourier.modeSize k)) * M / (Real.pi*D) := by
  have hcond : ¬ (k = 0 ∨ T < KAM.Fourier.modeSize k) := by
    rintro (h | h)
    · exact hk h
    · exact absurd hkT (not_le.2 h)
  rw [hmCoef]
  simp only [hcond, ite_false]
  rw [norm_div]
  have h2 : ‖(2*Real.pi*Complex.I : ℂ)‖ = 2*Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  have hc : Real.pi*D ≤ ‖2*Real.pi*Complex.I*p11dotC k (w b)‖ := by
    rw [norm_mul, h2]
    nlinarith [hdiv k hk hkT, Real.pi_pos]
  have hcoef := norm_coeff_le hr hP hb hbB k
  exact div_le_div₀ ((norm_nonneg _).trans hcoef) hcoef (by positivity) hc

/-- `hm-a`: the pointwise bound of the generator, `Λ_δ M/(πD)`. -/
theorem norm_solve_le {delta : ℝ} (hd : 0 < delta) (hD : 0 < D) (hr : 0 < r) (hM : 0 ≤ M)
    (hP : p11AngleClass r B P) (hb : p11Bound (KAM.complexStrip n r ×ˢ B) P M)
    {b : P11CVec n} (hbB : b ∈ B)
    (hdiv : ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    {theta : P11CVec n} (hθ : theta ∈ KAM.complexStrip n (r-delta)) :
    ‖p11Solve T w P theta b‖ ≤ p11Lambda n delta*M/(Real.pi*D) := by
  rw [p11Solve_eq]
  set F : Finset (Fin n → ℤ) :=
    (hmModes n T).filter fun k => k ≠ 0 ∧ KAM.Fourier.modeSize k ≤ T with hF
  have hS : ∀ k ∉ F, hmCoef T w P b k = 0 := by
    intro k hk
    by_cases h0 : k = 0
    · simp [hmCoef, h0]
    · by_cases hT : KAM.Fourier.modeSize k ≤ T
      · exact absurd (Finset.mem_filter.2 ⟨mem_hmModes_of_le hT, h0, hT⟩) hk
      · simp [hmCoef, not_le.1 hT]
  rw [fourierSum_finset hS]
  have hterm : ∀ k ∈ F, ‖hmCoef T w P b k * KAM.character k theta‖ ≤
      M/(Real.pi*D) * Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k) := by
    intro k hk
    obtain ⟨-, hk0, hkT⟩ := Finset.mem_filter.1 hk
    rw [norm_mul]
    have h1 := norm_hmCoef_le hD hr hP hb hbB hdiv hk0 hkT
    have h2 := KAM.norm_character_le k hθ
    calc ‖hmCoef T w P b k‖ * ‖KAM.character k theta‖
        ≤ (Real.exp (-(2*Real.pi*r*KAM.Fourier.modeSize k)) * M / (Real.pi*D)) *
          Real.exp (2*Real.pi*(r-delta)*KAM.Fourier.modeSize k) :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = M/(Real.pi*D) * Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k) := by
          have : Real.exp (-(2*Real.pi*r*KAM.Fourier.modeSize k)) *
              Real.exp (2*Real.pi*(r-delta)*KAM.Fourier.modeSize k) =
              Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k) := by
            rw [← Real.exp_add]; congr 1; ring
          calc _ = M/(Real.pi*D) * (Real.exp (-(2*Real.pi*r*KAM.Fourier.modeSize k)) *
              Real.exp (2*Real.pi*(r-delta)*KAM.Fourier.modeSize k)) := by ring
            _ = _ := by rw [this]
  calc ‖∑ k ∈ F, hmCoef T w P b k * KAM.character k theta‖
      ≤ ∑ k ∈ F, ‖hmCoef T w P b k * KAM.character k theta‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ F, M/(Real.pi*D) * Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k) :=
        Finset.sum_le_sum hterm
    _ = M/(Real.pi*D) * ∑ k ∈ F, Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ M/(Real.pi*D) * p11Lambda n delta :=
        mul_le_mul_of_nonneg_left (sum_exp_le_lambda hd F fun k hk =>
          (Finset.mem_filter.1 hk).2.1) (by positivity)
    _ = p11Lambda n delta*M/(Real.pi*D) := by ring

end Bound

/-! ### Smoothness, the equation and uniqueness (`hm-coeff`) -/

section Equation
variable {n : ℕ} {r M T D : ℝ} {B : Set (P11CVec n)} {P : P11CVec n × P11CVec n → ℂ}
  {w : P11CVec n → P11CVec n}

theorem differentiableOn_dotC (k : Fin n → ℤ) (hw : DifferentiableOn ℂ w B) :
    DifferentiableOn ℂ (fun b => p11dotC k (w b)) B := by
  unfold p11dotC
  refine DifferentiableOn.fun_sum fun i _ => ?_
  exact (differentiableOn_const _).mul (differentiableOn_pi.1 hw i)

theorem differentiableOn_hmCoef (hr : 0 < r) (hB : IsOpen B) (hD : 0 < D)
    (hP : DifferentiableOn ℂ P (KAM.complexStrip n r ×ˢ B)) (hw : DifferentiableOn ℂ w B)
    (hdiv : ∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    (k : Fin n → ℤ) : DifferentiableOn ℂ (fun b => hmCoef T w P b k) B := by
  by_cases hk : k = 0 ∨ T < KAM.Fourier.modeSize k
  · have : (fun b => hmCoef T w P b k) = fun _ => 0 := by
      funext b; simp [hmCoef, hk]
    rw [this]; exact differentiableOn_const _
  · have hk0 : k ≠ 0 := fun h => hk (Or.inl h)
    have hkT : KAM.Fourier.modeSize k ≤ T := not_lt.1 fun h => hk (Or.inr h)
    have : (fun b => hmCoef T w P b k) =
        fun b => KAM.Weighted.coeff P b k * (2*Real.pi*Complex.I*p11dotC k (w b))⁻¹ := by
      funext b; simp [hmCoef, hk, div_eq_mul_inv]
    rw [this]
    refine (differentiableOn_coeff hr hB hP k).mul
      (((differentiableOn_dotC k hw).const_mul (2*(Real.pi : ℂ)*Complex.I)).inv fun b hb => ?_)
    show 2*(Real.pi : ℂ)*Complex.I*p11dotC k (w b) ≠ 0
    have h1 := hdiv b hb k hk0 hkT
    have h2 : p11dotC k (w b) ≠ 0 := norm_pos_iff.1 (by linarith)
    simp [h2, Real.pi_ne_zero, Complex.I_ne_zero]

theorem differentiableOn_solve (hr : 0 < r) (hB : IsOpen B) (hD : 0 < D)
    (hP : DifferentiableOn ℂ P (KAM.complexStrip n r ×ˢ B)) (hw : DifferentiableOn ℂ w B)
    (hdiv : ∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖) :
    DifferentiableOn ℂ (fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2)
      (Set.univ ×ˢ B) := by
  have hfun : (fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2) = fun z =>
      ∑ k ∈ hmModes n T, hmCoef T w P z.2 k * KAM.character k z.1 := by
    funext z
    rw [p11Solve_eq, fourierSum_finset fun k hk => hmCoef_eq_zero hk]
  rw [hfun]
  refine DifferentiableOn.fun_sum fun k _ => ?_
  refine DifferentiableOn.mul ?_ ?_
  · exact (differentiableOn_hmCoef hr hB hD hP hw hdiv k).comp differentiableOn_snd
      fun z hz => hz.2
  · exact ((KAM.differentiable_character k).comp differentiable_fst).differentiableOn

theorem hmCut_zero (hT : 0 ≤ T) (b : P11CVec n) :
    hmCut T P b 0 = KAM.Weighted.coeff P b 0 := by
  simp [hmCut, KAM.Fourier.modeSize, hT]

theorem hmCoef_zero (b : P11CVec n) : hmCoef T w P b 0 = 0 := by simp [hmCoef]

/-- The equation: `ω·∂_θ φ = T_T P - ⟨P⟩`, termwise in the Fourier modes. -/
theorem fderiv_solve (hT : 0 ≤ T) {b : P11CVec n}
    (hdiv : ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖) (hD : 0 < D)
    (theta : P11CVec n) :
    fderiv ℂ (fun x => p11Solve T w P x b) theta (w b) =
      KAM.Weighted.truncate T P (theta, b) - KAM.Weighted.coeff P b 0 := by
  have hfun : (fun x => p11Solve T w P x b) = KAM.fourierSum (hmCoef T w P b) :=
    funext fun x => p11Solve_eq T w P x b
  rw [hfun, fderiv_fourierSum_finset (S := hmModes n T) fun k hk => hmCoef_eq_zero hk,
    truncate_eq, fourierSum_finset (S := hmModes n T) fun k hk => hmCut_eq_zero hk]
  have h0mem : (0 : Fin n → ℤ) ∈ hmModes n T :=
    mem_hmModes_of_le (by simp [KAM.Fourier.modeSize, hT])
  have hc0 : KAM.Weighted.coeff P b 0 =
      ∑ k ∈ hmModes n T, (if k = 0 then hmCut T P b 0 else 0) * KAM.character k theta := by
    rw [Finset.sum_eq_single_of_mem 0 h0mem]
    · simp [hmCut_zero hT, KAM.character_zero]
    · intro k _ hk; simp [hk]
  rw [hc0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = 0
  · subst hk; simp [hmCoef_zero]
  · by_cases hkT : KAM.Fourier.modeSize k ≤ T
    · have h2 : p11dotC k (w b) ≠ 0 := norm_pos_iff.1 (by linarith [hdiv k hk hkT])
      have hcond : ¬ (k = 0 ∨ T < KAM.Fourier.modeSize k) := by
        rintro (h | h)
        · exact hk h
        · exact absurd hkT (not_le.2 h)
      have e1 : hmCoef T w P b k =
          KAM.Weighted.coeff P b k / (2*Real.pi*Complex.I*p11dotC k (w b)) := by
        unfold hmCoef; simp only [hcond, ite_false]
      have e2 : hmCut T P b k = KAM.Weighted.coeff P b k := by simp [hmCut, hkT]
      rw [e1, e2]
      simp only [hk, ite_false, zero_mul, sub_zero]
      field_simp
    · have hcond : k = 0 ∨ T < KAM.Fourier.modeSize k := Or.inr (not_le.1 hkT)
      simp [hmCoef, hmCut, hk, hkT]

theorem coeff_solve (T : ℝ) (w : P11CVec n → P11CVec n) (P : P11CVec n × P11CVec n → ℂ)
    (b : P11CVec n) (k : Fin n → ℤ) :
    KAM.Weighted.coeff (fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2) b k =
      hmCoef T w P b k := by
  have h : KAM.Weighted.coeff (fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2) b k =
      KAM.torusCoeff (fun x => KAM.fourierSum (hmCoef T w P b) (fun j => (x j : ℂ))) k := by
    simp only [KAM.Weighted.coeff, p11Solve_eq]; rfl
  rw [h]
  exact torusCoeff_fourierSum_finset (fun k hk => hmCoef_eq_zero hk) k

theorem torusCoeff_zero (k : Fin n → ℤ) :
    KAM.torusCoeff (fun _ : Fin n → ℝ => (0 : ℂ)) k = 0 := by
  simp [KAM.torusCoeff, KAM.torusAverage]

end Equation

/-! ### Uniqueness and the main statement -/

section Main
variable {n : ℕ} {r M T D : ℝ} {B : Set (P11CVec n)} {P : P11CVec n × P11CVec n → ℂ}
  {w : P11CVec n → P11CVec n}

/-- Uniqueness among truncated, mean-zero solutions: all coefficients agree (`hm-coeff`). -/
theorem solve_unique {delta : ℝ} (hT : 0 ≤ T) (hD : 0 < D) (hdr : 0 < r - delta)
    (hpoly : ∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T P z = P z)
    (hdiv : ∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    (u : P11CVec n × P11CVec n → ℂ)
    (hup : ∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T u z = u z)
    (hu0 : ∀ b ∈ B, p11AngleAverage u b = 0)
    (hue : ∀ theta ∈ KAM.complexStrip n (r-delta), ∀ b ∈ B,
      fderiv ℂ (fun x => u (x, b)) theta (w b) = P (theta, b) - p11AngleAverage P b) :
    ∀ z ∈ Set.univ ×ˢ B, u z = p11Solve T w P z.1 z.2 := by
  rintro ⟨theta, b⟩ ⟨-, hb⟩
  have hu : ∀ x, u (x, b) = KAM.fourierSum (hmCut T u b) x := fun x => by
    rw [← truncate_eq, hup (x, b) ⟨trivial, hb⟩]
  have hfun : (fun x => u (x, b)) = KAM.fourierSum (hmCut T u b) := funext hu
  have hSu : ∀ k ∉ hmModes n T, hmCut T u b k = 0 := fun k hk => hmCut_eq_zero hk
  -- the coefficient families agree
  have hg : ∀ k, (hmCut T u b k - hmCoef T w P b k) * (2*Real.pi*Complex.I*p11dotC k (w b)) = 0 := by
    set g : (Fin n → ℤ) → ℂ := fun k =>
      (hmCut T u b k - hmCoef T w P b k) * (2*Real.pi*Complex.I*p11dotC k (w b)) with hgdef
    have hgS : ∀ k ∉ hmModes n T, g k = 0 := fun k hk => by
      simp [hgdef, hSu k hk, hmCoef_eq_zero hk]
    have hzero : ∀ x : Fin n → ℝ, KAM.fourierSum g (fun j => (x j : ℂ)) = 0 := by
      intro x
      have hx := hue (fun j => (x j : ℂ)) (KAM.ofReal_mem_complexStrip hdr x) b hb
      rw [hfun, fderiv_fourierSum_finset (S := hmModes n T) hSu] at hx
      have h2 := fderiv_solve (P := P) hT (hdiv b hb) hD (fun j => (x j : ℂ))
      rw [(funext fun x => p11Solve_eq T w P x b : (fun x => p11Solve T w P x b) = _),
        fderiv_fourierSum_finset (S := hmModes n T) fun k hk => hmCoef_eq_zero hk,
        hpoly (fun j => (x j : ℂ), b) ⟨trivial, hb⟩] at h2
      have hsplit : ∑ k ∈ hmModes n T, g k * KAM.character k (fun j => (x j : ℂ)) =
          ∑ k ∈ hmModes n T, hmCut T u b k * (2*Real.pi*Complex.I*p11dotC k (w b)) *
            KAM.character k (fun j => (x j : ℂ)) -
          ∑ k ∈ hmModes n T, hmCoef T w P b k * (2*Real.pi*Complex.I*p11dotC k (w b)) *
            KAM.character k (fun j => (x j : ℂ)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hgdef]; ring
      rw [fourierSum_finset hgS, hsplit, hx, h2]
      simp [p11AngleAverage]
    have hgk : ∀ k, g k = 0 := fun k => by
      have h1 := torusCoeff_fourierSum_finset (a := g) hgS k
      have h2 : (fun x : Fin n → ℝ => KAM.fourierSum g (fun j => (x j : ℂ))) =
          fun _ => 0 := funext hzero
      rw [h2, torusCoeff_zero] at h1
      exact h1.symm
    exact hgk
  have hcoef : ∀ k, hmCut T u b k = hmCoef T w P b k := by
    intro k
    by_cases hk : k ∈ hmModes n T
    · by_cases h0 : k = 0
      · subst h0
        rw [hmCut_zero hT, hmCoef_zero]
        exact hu0 b hb
      · by_cases hkT : KAM.Fourier.modeSize k ≤ T
        · have h2 : 2*Real.pi*Complex.I*p11dotC k (w b) ≠ 0 := by
            have := hdiv b hb k h0 hkT
            have h3 : p11dotC k (w b) ≠ 0 := norm_pos_iff.1 (by linarith)
            simp [h3, Real.pi_ne_zero, Complex.I_ne_zero]
          exact sub_eq_zero.1 ((mul_eq_zero.1 (hg k)).resolve_right h2)
        · have : T < KAM.Fourier.modeSize k := not_le.1 hkT
          simp [hmCut, hmCoef, hkT, this]
    · rw [hmCut_eq_zero hk, hmCoef_eq_zero hk]
  have hcut : hmCut T u b = hmCoef T w P b := funext hcoef
  show u (theta, b) = p11Solve T w P theta b
  rw [hu, hcut, p11Solve_eq]

/-- `bpP:p11a:homological-maximal`. -/
theorem homological_maximal {n : ℕ} (hn : 1 ≤ n) {r delta T D M : ℝ}
    (hr : 0 < r) (hd : 0 < delta) (hdr : delta < r) (hT : 0 < T)
    (hD : 0 < D) (hM : 0 ≤ M) {B : Set (P11CVec n)} (hB : IsOpen B)
    (w : P11CVec n → P11CVec n) (hw : DifferentiableOn ℂ w B)
    (hdiv : ∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    (P : P11CVec n × P11CVec n → ℂ) (hP : p11AngleClass r B P)
    (hpoly : ∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T P z=P z)
    (hb : p11Bound (KAM.complexStrip n r ×ˢ B) P M) :
    let phi := fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2
    p11AngleClass (r-delta) B phi ∧
    DifferentiableOn ℂ phi (Set.univ ×ˢ B) ∧
    (∀ z, KAM.Weighted.truncate T phi z=phi z) ∧
    DifferentiableOn ℂ (p11AngleAverage P) B ∧
    (∀ b ∈ B, p11AngleAverage phi b=0) ∧
    (∀ theta ∈ KAM.complexStrip n (r-delta), ∀ b ∈ B,
      fderiv ℂ (fun x => phi (x,b)) theta (w b)=P (theta,b)-p11AngleAverage P b) ∧
    p11Bound (KAM.complexStrip n (r-delta) ×ˢ B) phi (p11Lambda n delta*M/(Real.pi*D)) ∧
    (∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      ‖KAM.Weighted.coeff phi b k‖ ≤ M*Real.exp (-2*Real.pi*KAM.Fourier.modeSize k*r)/(Real.pi*D)) ∧
    (∀ b ∈ B, ‖p11AngleAverage P b‖ ≤ M) ∧
    ∀ u, p11AngleClass (r-delta) B u →
      (∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T u z=u z) →
      (∀ b ∈ B, p11AngleAverage u b=0) →
      (∀ theta ∈ KAM.complexStrip n (r-delta), ∀ b ∈ B,
        fderiv ℂ (fun x => u (x,b)) theta (w b)=P (theta,b)-p11AngleAverage P b) →
      EqOn u phi (KAM.complexStrip n (r-delta) ×ˢ B) := by
  intro phi
  have hdr' : 0 < r - delta := by linarith
  have hdiff : DifferentiableOn ℂ phi (Set.univ ×ˢ B) :=
    differentiableOn_solve hr hB hD hP.1 hw hdiv
  have hsub : KAM.complexStrip n (r-delta) ×ˢ B ⊆ Set.univ ×ˢ B := fun z hz => ⟨trivial, hz.2⟩
  refine ⟨⟨hdiff.mono hsub, fun j z _ => ?_⟩, hdiff, fun z => ?_,
    differentiableOn_coeff hr hB hP.1 0, fun b _ => ?_, fun theta _ b hbB => ?_,
    fun z hz => norm_solve_le hd hD hr hM hP hb hz.2 (hdiv z.2 hz.2) hz.1, ?_,
    fun b hbB => ?_, ?_⟩
  · show p11Solve T w P (z.1 + Pi.single j 1) z.2 = p11Solve T w P z.1 z.2
    rw [p11Solve_eq, p11Solve_eq, KAM.fourierSum_add_single]
  · obtain ⟨theta, b⟩ := z
    show KAM.Weighted.truncate T phi (theta, b) = p11Solve T w P theta b
    rw [truncate_eq, p11Solve_eq]
    congr 1
    funext k
    by_cases hk : KAM.Fourier.modeSize k ≤ T
    · simp [hmCut, hk, phi, coeff_solve]
    · have : T < KAM.Fourier.modeSize k := not_le.1 hk
      simp [hmCut, hk, hmCoef, this]
  · show KAM.Weighted.coeff phi b 0 = 0
    rw [show phi = fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2 from rfl,
      coeff_solve, hmCoef_zero]
  · rw [fderiv_solve hT.le (hdiv b hbB) hD theta, hpoly (theta, b) ⟨trivial, hbB⟩]
    rfl
  · intro b hbB k hk hkT
    rw [show phi = fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2 from rfl, coeff_solve]
    have := norm_hmCoef_le hD hr hP hb hbB (hdiv b hbB) hk hkT
    convert this using 2
    · rw [mul_comm]; congr 2; ring
  · have := norm_coeff_le hr hP hb hbB 0
    simpa [KAM.Fourier.modeSize, p11AngleAverage] using this
  · intro u hu hup hu0 hue z hz
    exact solve_unique hT.le hD hdr' hpoly hdiv u hup hu0 hue z ⟨trivial, hz.2⟩

end Main

/-! ### Reality (`hm-d`) -/

section Real
variable {n : ℕ}

theorem conj_character_real (k : Fin n → ℤ) (x : Fin n → ℝ) :
    starRingEnd ℂ (KAM.character k (fun j => (x j : ℂ))) =
      KAM.character (-k) (fun j => (x j : ℂ)) := by
  unfold KAM.character
  rw [← Complex.exp_conj]
  congr 1
  have h1 : ∑ j, (((-k) j : ℤ) : ℂ) * (x j : ℂ) = -∑ j, ((k j : ℤ) : ℂ) * (x j : ℂ) := by
    simp [Finset.sum_neg_distrib]
  rw [h1]
  simp only [map_mul, map_sum, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  have h2 : starRingEnd ℂ (2 : ℂ) = 2 := Complex.conj_eq_iff_im.2 (by simp)
  rw [h2]
  ring

theorem coeff_neg_conj {P : P11CVec n × P11CVec n → ℂ} {b : P11CVec n}
    (hP : ∀ x : Fin n → ℝ, (P (fun j => (x j : ℂ), b)).im = 0) (k : Fin n → ℤ) :
    KAM.Weighted.coeff P b (-k) = starRingEnd ℂ (KAM.Weighted.coeff P b k) := by
  unfold KAM.Weighted.coeff KAM.torusCoeffW KAM.torusAverage
  rw [← integral_conj]
  refine setIntegral_congr_fun ?_ fun x _ => ?_
  · exact (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
  · simp only [smul_eq_mul, map_mul, conj_character_real, neg_neg]
    rw [Complex.conj_eq_iff_im.2 (hP x)]

theorem hmCoef_neg_conj {T : ℝ} {w : P11CVec n → P11CVec n} {P : P11CVec n × P11CVec n → ℂ}
    {b : P11CVec n} (hP : ∀ x : Fin n → ℝ, (P (fun j => (x j : ℂ), b)).im = 0)
    (hw : ∀ i, (w b i).im = 0) (k : Fin n → ℤ) :
    hmCoef T w P b (-k) = starRingEnd ℂ (hmCoef T w P b k) := by
  have hdot : p11dotC (-k) (w b) = -p11dotC k (w b) := by
    simp [p11dotC, Finset.sum_neg_distrib]
  have hdotc : starRingEnd ℂ (p11dotC k (w b)) = p11dotC k (w b) := by
    unfold p11dotC
    simp only [map_sum, map_mul, map_intCast]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.conj_eq_iff_im.2 (hw i)]
  have hms : KAM.Fourier.modeSize (-k) = KAM.Fourier.modeSize k := by
    simp [KAM.Fourier.modeSize]
  by_cases h : k = 0 ∨ T < KAM.Fourier.modeSize k
  · have h' : -k = 0 ∨ T < KAM.Fourier.modeSize (-k) := by
      rcases h with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by rwa [hms])
    have e1 : hmCoef T w P b (-k) = 0 := by unfold hmCoef; simp only [h', ite_true]
    have e2 : hmCoef T w P b k = 0 := by unfold hmCoef; simp only [h, ite_true]
    rw [e1, e2, map_zero]
  · have h' : ¬ (-k = 0 ∨ T < KAM.Fourier.modeSize (-k)) := by
      rintro (h1 | h1)
      · exact h (Or.inl (neg_eq_zero.1 h1))
      · exact h (Or.inr (by rwa [hms] at h1))
    simp only [hmCoef, h, h', ite_false]
    rw [coeff_neg_conj hP, hdot, map_div₀, map_mul, hdotc]
    have h2 : starRingEnd ℂ (2 : ℂ) = 2 := Complex.conj_eq_iff_im.2 (by simp)
    have : starRingEnd ℂ (2*(Real.pi : ℂ)*Complex.I) = -(2*Real.pi*Complex.I) := by
      simp only [map_mul, h2, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [this]
    ring

end Real

/-- Reality of the maximal homological solution; this supplies the guard used by cs-lip. -/
theorem homological_maximal_real {n : ℕ} {r T D : ℝ} (hr : 0 < r) (hT : 0 < T) (hD : 0 < D)
    {B : Set (P11CVec n)} (hB : IsOpen B) (w : P11CVec n → P11CVec n)
    (hw : DifferentiableOn ℂ w B)
    (hdiv : ∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    (P : P11CVec n × P11CVec n → ℂ) (hP : p11AngleClass r B P)
    (hpoly : ∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T P z=P z)
    (hwr : ∀ b : P11Vec n, KAM.realInclusion n b ∈ B → ∀ i, (w (KAM.realInclusion n b) i).im=0)
    (hpr : ∀ x b : P11Vec n, KAM.realInclusion n b ∈ B →
      (P (KAM.realInclusion n x,KAM.realInclusion n b)).im=0) :
    ∀ x b : P11Vec n, KAM.realInclusion n b ∈ B →
      (p11Solve T w P (KAM.realInclusion n x) (KAM.realInclusion n b)).im=0 := by
  intro x b hbB
  rw [p11Solve_eq]
  set a := hmCoef T w P (KAM.realInclusion n b) with ha
  have hneg : ∀ k, a (-k) = starRingEnd ℂ (a k) := fun k =>
    hmCoef_neg_conj (fun y => hpr y b hbB) (hwr b hbB) k
  have hx : KAM.realInclusion n x = fun j => (x j : ℂ) := funext fun j => rfl
  rw [← Complex.conj_eq_iff_im, hx]
  unfold KAM.fourierSum
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg (Fin n → ℤ)).tsum_eq (fun k => a k * KAM.character k (fun j => (x j : ℂ)))]
  refine tsum_congr fun k => ?_
  simp only [Equiv.neg_apply, map_mul, hneg, conj_character_real, neg_neg]

/-! ### Parameter derivatives (`hm-bc`) -/

/-- `param_cauchy` for scalar-valued maps (the same proof). -/
theorem param_cauchy_scalar {n : ℕ} {E : Set (P11Vec n)} {t tp M : ℝ}
    (htp : 0 < tp) (ht : tp < t)
    {u : P11CVec n → ℂ} (hu : DifferentiableOn ℂ u (KAM.actionNbhd E t))
    (hb : p11Bound (KAM.actionNbhd E t) u M) {j : ℕ} (hj : 1 ≤ j) :
    ∀ b ∈ KAM.actionNbhd E tp, ‖iteratedFDeriv ℂ j u b‖ ≤
      (j : ℝ)^j*M/(t-tp)^j := by
  intro b hb'
  obtain ⟨J, hJ, hbJ⟩ := hb'
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hδ : 0 < (t - tp) / j := div_pos (by linarith) hjpos
  have hball : closedBall b (j * ((t - tp) / j)) ⊆ KAM.actionNbhd E t := by
    intro w hw
    refine ⟨J, hJ, ?_⟩
    have hw' := mem_closedBall_iff_norm.mp hw
    rw [mul_div_cancel₀ _ hjpos.ne'] at hw'
    calc ‖w - fun i => (J i : ℂ)‖ = ‖(w - b) + (b - fun i => (J i : ℂ))‖ := by
          congr 1; abel
      _ ≤ ‖w - b‖ + ‖b - fun i => (J i : ℂ)‖ := norm_add_le _ _
      _ < t := by linarith
  have := p11_norm_iteratedFDeriv_le_of_closedBall (p11_isOpen_actionNbhd E t) hδ j hu hball
    (fun w hw => hb w (hball hw))
  convert this using 1
  rw [div_pow, div_div_eq_mul_div]
  ring

/-- Every-order parameter clause of homological-maximal(c), scalar and average. -/
theorem homological_maximal_param {n : ℕ} {r delta T D M t tp : ℝ}
    (hr : 0 < r) (hd : 0 < delta) (hdr : delta < r) (hT : 0 < T)
    (hD : 0 < D) (hM : 0 ≤ M) {E : Set (P11Vec n)} (htp : 0 < tp) (htt : tp < t)
    (w : P11CVec n → P11CVec n) (hw : DifferentiableOn ℂ w (KAM.actionNbhd E t))
    (hdiv : ∀ b ∈ KAM.actionNbhd E t, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    (P : P11CVec n × P11CVec n → ℂ) (hP : p11AngleClass r (KAM.actionNbhd E t) P)
    (hpoly : ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t,
      KAM.Weighted.truncate T P z=P z)
    (hb : p11Bound (KAM.complexStrip n r ×ˢ KAM.actionNbhd E t) P M)
    {j : ℕ} (hj : 1 ≤ j) :
    ∀ theta ∈ KAM.complexStrip n (r-delta), ∀ b ∈ KAM.actionNbhd E tp,
      ‖iteratedFDeriv ℂ j (p11Solve T w P theta) b‖ ≤
        (j : ℝ)^j*p11Lambda n delta*M/(Real.pi*D*(t-tp)^j) ∧
      ‖iteratedFDeriv ℂ j (p11AngleAverage P) b‖ ≤ (j : ℝ)^j*M/(t-tp)^j := by
  intro theta hθ b hbtp
  have hB := p11_isOpen_actionNbhd E t
  refine ⟨?_, ?_⟩
  · have hdiff : DifferentiableOn ℂ (p11Solve T w P theta) (KAM.actionNbhd E t) := by
      have h1 := differentiableOn_solve hr hB hD hP.1 hw hdiv (T := T)
      exact h1.comp (differentiableOn_const theta |>.prodMk differentiableOn_id)
        fun b hb => ⟨trivial, hb⟩
    have hbd : p11Bound (KAM.actionNbhd E t) (p11Solve T w P theta)
        (p11Lambda n delta*M/(Real.pi*D)) := fun b hbB =>
      norm_solve_le hd hD hr hM hP hb hbB (hdiv b hbB) hθ
    have := param_cauchy_scalar htp htt hdiff hbd hj b hbtp
    refine this.trans (le_of_eq ?_)
    ring
  · have hdiff : DifferentiableOn ℂ (p11AngleAverage P) (KAM.actionNbhd E t) :=
      differentiableOn_coeff hr hB hP.1 0
    have hbd : p11Bound (KAM.actionNbhd E t) (p11AngleAverage P) M := fun b hbB => by
      have := norm_coeff_le hr hP hb hbB 0
      simpa [KAM.Fourier.modeSize, p11AngleAverage] using this
    exact param_cauchy_scalar htp htt hdiff hbd hj b hbtp

end KAM.Planetary
