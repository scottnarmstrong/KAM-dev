/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.StepData
public import KAM.Planetary.MaximalStep.Homological

/-!
# Coefficients of the cutoff (P11A-C8, `stepP:p11a:cs-cutoff`)

The cutoff `R_* = p11Cutoff T R` is affine in the action: `R_* = R_{*0} + R_{*1} · η` with
`R_{*0} = T_T [R(·, 0)]` and `R_{*1,i} = T_T [∂_{η_i} R(·, 0)]`. This file proves the affine
decomposition for parameters in `B` (the decomposition cannot hold for `b ∉ B`, where `R` is
unconstrained), the angle-class, trigonometric-polynomial and sup-norm facts consumed by
`homological_maximal`, and reality of the coefficients.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ}

/-- The zeroth-order coefficient family `R(θ, 0, b)`. -/
def stepF0 (R : P11Family n → ℂ) (u : P11CVec n × P11CVec n) : ℂ := R ((u.1, 0), u.2)

/-- The first-order coefficient family `∂_{η_i} R(θ, 0, b)`. -/
def stepF1 (R : P11Family n → ℂ) (i : Fin n) (u : P11CVec n × P11CVec n) : ℂ :=
  fderiv ℂ (fun η => R ((u.1, η), u.2)) 0 (Pi.single i 1)

theorem coeff_add_sum {b : P11CVec n} {f : P11CVec n × P11CVec n → ℂ}
    {g : Fin n → P11CVec n × P11CVec n → ℂ} (c : Fin n → ℂ)
    (hf : Continuous fun x : Fin n → ℝ => f (fun j => (x j : ℂ), b))
    (hg : ∀ i, Continuous fun x : Fin n → ℝ => g i (fun j => (x j : ℂ), b)) (k : Fin n → ℤ) :
    KAM.Weighted.coeff (fun u => f u + ∑ i, c i * g i u) b k =
      KAM.Weighted.coeff f b k + ∑ i, c i * KAM.Weighted.coeff (g i) b k := by
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp
      (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
  have hint : ∀ f' : P11CVec n × P11CVec n → ℂ,
      Continuous (fun x : Fin n → ℝ => f' (fun j => (x j : ℂ), b)) →
      IntegrableOn (fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) •
        f' (fun j => (x j : ℂ), b)) (Set.pi Set.univ fun _ : Fin n => Icc (0 : ℝ) 1) :=
    fun f' h => KAM.integrableOn_unitCube_of_continuous (hchar.smul h)
  unfold KAM.Weighted.coeff KAM.torusCoeffW KAM.torusAverage
  have e : (fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) •
      (f (fun j => (x j : ℂ), b) + ∑ i, c i * g i (fun j => (x j : ℂ), b))) =
      fun x => KAM.character (-k) (fun j => (x j : ℂ)) • f (fun j => (x j : ℂ), b) +
        ∑ i, c i * (KAM.character (-k) (fun j => (x j : ℂ)) • g i (fun j => (x j : ℂ), b)) := by
    funext x
    simp only [smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  simp only [e]
  rw [integral_add (hint f hf) (integrable_finset_sum _ fun i _ =>
    (hint (g i) (hg i)).const_mul (c i)), integral_finset_sum _ fun i _ =>
    (hint (g i) (hg i)).const_mul (c i)]
  simp only [integral_const_mul]

theorem truncate_add_sum {T : ℝ} {b : P11CVec n} {f : P11CVec n × P11CVec n → ℂ}
    {g : Fin n → P11CVec n × P11CVec n → ℂ} (c : Fin n → ℂ)
    (hf : Continuous fun x : Fin n → ℝ => f (fun j => (x j : ℂ), b))
    (hg : ∀ i, Continuous fun x : Fin n → ℝ => g i (fun j => (x j : ℂ), b)) (θ : P11CVec n) :
    KAM.Weighted.truncate T (fun u => f u + ∑ i, c i * g i u) (θ, b) =
      KAM.Weighted.truncate T f (θ, b) + ∑ i, c i * KAM.Weighted.truncate T (g i) (θ, b) := by
  have hco : ∀ k, hmCut T (fun u => f u + ∑ i, c i * g i u) b k =
      hmCut T f b k + ∑ i, c i * hmCut T (g i) b k := by
    intro k
    by_cases h : KAM.Fourier.modeSize k ≤ T
    · simp only [hmCut, h, ite_true]
      exact coeff_add_sum c hf hg k
    · simp [hmCut, h]
  simp only [truncate_eq]
  rw [fourierSum_finset (S := hmModes n T) (fun k hk => hmCut_eq_zero hk),
    fourierSum_finset (S := hmModes n T) (fun k hk => hmCut_eq_zero hk)]
  have hg' : ∀ i, KAM.fourierSum (hmCut T (g i) b) θ =
      ∑ k ∈ hmModes n T, hmCut T (g i) b k * KAM.character k θ := fun i =>
    fourierSum_finset (S := hmModes n T) (fun k hk => hmCut_eq_zero hk) θ
  simp only [hg', hco, add_mul, Finset.sum_mul, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring)

/-! ### The coefficient families -/

/-- The Taylor part is affine in the action with the coefficients `stepF0`, `stepF1`. -/
theorem taylor_eq (R : P11Family n → ℂ) (θ η b : P11CVec n) :
    p11Taylor R ((θ, η), b) = stepF0 R (θ, b) + ∑ i, η i * stepF1 R i (θ, b) := by
  simp only [p11Taylor, stepF0, stepF1]
  congr 1
  conv_lhs => rw [show η = ∑ i, η i • (Pi.single i (1 : ℂ) : P11CVec n) from by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  simp [smul_eq_mul]

/-- The first-order coefficient through the Taylor part at `(s/2) e_i`. -/
theorem stepF1_eq {s : ℝ} (hs : 0 < s) (R : P11Family n → ℂ) (i : Fin n)
    (u : P11CVec n × P11CVec n) :
    stepF1 R i u = (2 / s : ℂ) * (p11Taylor R ((u.1, ((s / 2 : ℝ) : ℂ) • Pi.single i 1), u.2) -
      stepF0 R u) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [taylor_eq]
  have : ∑ j, (((s / 2 : ℝ) : ℂ) • (Pi.single i (1 : ℂ) : P11CVec n)) j * stepF1 R j u =
      ((s / 2 : ℝ) : ℂ) * stepF1 R i u := by
    simp [Pi.single_apply]
  rw [add_sub_cancel_left, this]
  push_cast
  field_simp

variable {r s : ℝ} {B : Set (P11CVec n)} {R : P11Family n → ℂ}

theorem norm_half_single (hs : 0 < s) (i : Fin n) :
    ‖((s / 2 : ℝ) : ℂ) • (Pi.single i (1 : ℂ) : P11CVec n)‖ < s := by
  have h1 : ‖(Pi.single i (1 : ℂ) : P11CVec n)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  nlinarith

theorem stepF0_diff (hr : 0 < r) (hs : 0 < s) (hR : p11Admissible r s B R) :
    DifferentiableOn ℂ (stepF0 R) (KAM.complexStrip n r ×ˢ B) := by
  refine hR.1.comp (f := fun u : P11CVec n × P11CVec n => ((u.1, (0 : P11CVec n)), u.2))
    (by fun_prop) ?_
  rintro ⟨θ, b⟩ ⟨h1, h2⟩
  exact p11_mem_domain_def.mpr ⟨h1, by simpa using hs, h2⟩

theorem stepF1_diff (hr : 0 < r) (hs : 0 < s) (hB : IsOpen B) (hR : p11Admissible r s B R)
    (i : Fin n) : DifferentiableOn ℂ (stepF1 R i) (KAM.complexStrip n r ×ˢ B) := by
  have hT := (p11_taylor_admissible hs hB hR).1
  have h1 : DifferentiableOn ℂ (fun u : P11CVec n × P11CVec n =>
      p11Taylor R ((u.1, ((s / 2 : ℝ) : ℂ) • Pi.single i 1), u.2)) (KAM.complexStrip n r ×ˢ B) := by
    refine hT.comp (f := fun u : P11CVec n × P11CVec n =>
      ((u.1, ((s / 2 : ℝ) : ℂ) • (Pi.single i (1 : ℂ) : P11CVec n)), u.2)) (by fun_prop) ?_
    rintro ⟨θ, b⟩ ⟨h1, h2⟩
    exact p11_mem_domain_def.mpr ⟨h1, norm_half_single hs i, h2⟩
  have := (h1.sub (stepF0_diff hr hs hR)).const_mul (2 / s : ℂ)
  exact this.congr fun u _ => stepF1_eq hs R i u

theorem stepF0_periodic (hs : 0 < s) (hR : p11Admissible r s B R) (j : Fin n)
    (u : P11CVec n × P11CVec n) (hu : u ∈ KAM.complexStrip n r ×ˢ B) :
    stepF0 R (u.1 + Pi.single j 1, u.2) = stepF0 R u := by
  have hper := hR.2 j ((u.1, 0), u.2) (p11_mem_domain_def.mpr ⟨hu.1, by simpa using hs, hu.2⟩)
  exact hper

theorem stepF1_periodic (hs : 0 < s) (hB : IsOpen B) (hR : p11Admissible r s B R) (j i : Fin n)
    (u : P11CVec n × P11CVec n) (hu : u ∈ KAM.complexStrip n r ×ˢ B) :
    stepF1 R i (u.1 + Pi.single j 1, u.2) = stepF1 R i u := by
  have hTp := (p11_taylor_admissible hs hB hR).2 j
    ((u.1, ((s / 2 : ℝ) : ℂ) • Pi.single i 1), u.2)
    (p11_mem_domain_def.mpr ⟨hu.1, norm_half_single hs i, hu.2⟩)
  rw [stepF1_eq hs, stepF1_eq hs]
  have h0 := stepF0_periodic hs hR j u hu
  simp only at hTp
  rw [hTp, h0]

theorem norm_stepF0_le {eps : ℝ} (hs : 0 < s) (hb : p11Bound (domain_def n r s B) R eps) :
    p11Bound (KAM.complexStrip n r ×ˢ B) (stepF0 R) eps := by
  rintro ⟨θ, b⟩ ⟨h1, h2⟩
  exact hb _ (p11_mem_domain_def.mpr ⟨h1, by simpa using hs, h2⟩)

theorem norm_stepF1_le {eps : ℝ} (hr : 0 < r) (hs : 0 < s) (he : 0 ≤ eps) (hB : IsOpen B)
    (hR : p11Admissible r s B R) (hb : p11Bound (domain_def n r s B) R eps) (i : Fin n) :
    p11Bound (KAM.complexStrip n r ×ˢ B) (stepF1 R i) (eps / s) := by
  rintro ⟨θ, b⟩ ⟨h1, h2⟩
  have hd := (taylor_cutoff (q := 1/2) (M := eps) (r := r) (s := s) (n := n) hr hs he
    (by norm_num) (by norm_num)
    hB hR hb).2.2.2 θ h1 b h2
  have h1' : ‖(Pi.single i (1 : ℂ) : P11CVec n)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  calc ‖stepF1 R i (θ, b)‖ ≤ ‖fderiv ℂ (fun eta => R ((θ, eta), b)) 0‖ *
        ‖(Pi.single i (1 : ℂ) : P11CVec n)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ eps / s := by nlinarith [norm_nonneg (fderiv ℂ (fun eta => R ((θ, eta), b)) 0)]

/-! ### Truncation: idempotence and locality in the parameter -/

theorem truncate_congr_param {T : ℝ} {b : P11CVec n} {u v : P11CVec n × P11CVec n → ℂ}
    (h : ∀ θ, u (θ, b) = v (θ, b)) (θ : P11CVec n) :
    KAM.Weighted.truncate T u (θ, b) = KAM.Weighted.truncate T v (θ, b) := by
  rw [truncate_eq, truncate_eq]
  congr 1
  funext k
  simp only [hmCut, KAM.Weighted.coeff, h]

theorem truncate_truncate {T : ℝ} (P : P11CVec n × P11CVec n → ℂ) (θ b : P11CVec n) :
    KAM.Weighted.truncate T (KAM.Weighted.truncate T P) (θ, b) =
      KAM.Weighted.truncate T P (θ, b) := by
  rw [truncate_eq (P := KAM.Weighted.truncate T P), truncate_eq (P := P)]
  congr 1
  funext k
  have hc : KAM.Weighted.coeff (KAM.Weighted.truncate T P) b k = hmCut T P b k := by
    unfold KAM.Weighted.coeff
    have : (fun x : Fin n → ℝ => KAM.Weighted.truncate T P (fun j => (x j : ℂ), b)) =
        fun x => KAM.fourierSum (hmCut T P b) (fun j => (x j : ℂ)) :=
      funext fun x => truncate_eq T P _ b
    rw [KAM.torusCoeffW_complex, this]
    exact torusCoeff_fourierSum_finset (S := hmModes n T) (fun k hk => hmCut_eq_zero hk) k
  by_cases h : KAM.Fourier.modeSize k ≤ T
  · simp [hmCut, h] at hc ⊢
    exact hc
  · simp [hmCut, h]

/-! ### The decomposition of the cutoff -/

variable {T : ℝ}

theorem continuous_stepF0 (hr : 0 < r) (hs : 0 < s) (hR : p11Admissible r s B R)
    {b : P11CVec n} (hb : b ∈ B) :
    Continuous fun x : Fin n → ℝ => stepF0 R (fun j => (x j : ℂ), b) := by
  have hc := (stepF0_diff hr hs hR).continuousOn
  refine hc.comp_continuous (f := fun x : Fin n → ℝ => ((fun j => (x j : ℂ), b) :
    P11CVec n × P11CVec n)) (by fun_prop) fun x => ⟨KAM.ofReal_mem_complexStrip hr x, hb⟩

theorem continuous_stepF1 (hr : 0 < r) (hs : 0 < s) (hB : IsOpen B) (hR : p11Admissible r s B R)
    (i : Fin n) {b : P11CVec n} (hb : b ∈ B) :
    Continuous fun x : Fin n → ℝ => stepF1 R i (fun j => (x j : ℂ), b) := by
  have hc := (stepF1_diff hr hs hB hR i).continuousOn
  refine hc.comp_continuous (f := fun x : Fin n → ℝ => ((fun j => (x j : ℂ), b) :
    P11CVec n × P11CVec n)) (by fun_prop) fun x => ⟨KAM.ofReal_mem_complexStrip hr x, hb⟩

theorem cutoff_decomp (hr : 0 < r) (hs : 0 < s) (hB : IsOpen B) (hR : p11Admissible r s B R)
    (θ η : P11CVec n) {b : P11CVec n} (hb : b ∈ B) :
    p11Cutoff T R ((θ, η), b) = KAM.Weighted.truncate T (stepF0 R) (θ, b) +
      ∑ i, η i * KAM.Weighted.truncate T (stepF1 R i) (θ, b) := by
  have e : (fun u : P11CVec n × P11CVec n => p11Taylor R ((u.1, η), u.2)) =
      fun u => stepF0 R u + ∑ i, η i * stepF1 R i u := funext fun u => taylor_eq R u.1 η u.2
  have h := truncate_add_sum (T := T) η (continuous_stepF0 hr hs hR hb)
    (fun i => continuous_stepF1 hr hs hB hR i hb) θ
  simp only [p11Cutoff, p11Cut]
  rw [e]
  exact h

theorem cutoff_R0 (θ b : P11CVec n) :
    p11R0 T R (θ, b) = KAM.Weighted.truncate T (stepF0 R) (θ, b) := by
  have e : (fun u : P11CVec n × P11CVec n => p11Taylor R ((u.1, (0 : P11CVec n)), u.2)) =
      stepF0 R := funext fun u => by simp [taylor_eq]
  simp only [p11R0, p11Cutoff, p11Cut]
  rw [e]

theorem cutoff_R1 (hr : 0 < r) (hs : 0 < s) (hB : IsOpen B) (hR : p11Admissible r s B R)
    (θ : P11CVec n) {b : P11CVec n} (hb : b ∈ B) (i : Fin n) :
    p11R1 T R (θ, b) i = KAM.Weighted.truncate T (stepF1 R i) (θ, b) := by
  set A := KAM.Weighted.truncate T (stepF0 R) (θ, b)
  set C : Fin n → ℂ := fun j => KAM.Weighted.truncate T (stepF1 R j) (θ, b)
  set L : P11CVec n →L[ℂ] ℂ := ∑ j, C j • (ContinuousLinearMap.proj j : P11CVec n →L[ℂ] ℂ)
  have hL : ∀ η, L η = ∑ j, η j * C j := fun η => by simp [L, mul_comm]
  have e : (fun η => p11Cutoff T R ((θ, η), b)) = fun η => A + L η := funext fun η => by
    rw [cutoff_decomp hr hs hB hR θ η hb, hL]
  simp only [p11R1]
  rw [e, fderiv_const_add, L.fderiv]
  simp [L, Pi.single_apply, C]

/-! ### The outputs consumed by the step -/

/-- The coefficient families as `η`-independent families. -/
def stepFam0 (R : P11Family n → ℂ) (z : P11Family n) : ℂ := stepF0 R (z.1.1, z.2)

def stepFam1 (R : P11Family n → ℂ) (i : Fin n) (z : P11Family n) : ℂ := stepF1 R i (z.1.1, z.2)

theorem cut_stepFam0 (θ η b : P11CVec n) :
    p11Cut T (stepFam0 R) ((θ, η), b) = KAM.Weighted.truncate T (stepF0 R) (θ, b) := rfl

theorem cut_stepFam1 (i : Fin n) (θ η b : P11CVec n) :
    p11Cut T (stepFam1 R i) ((θ, η), b) = KAM.Weighted.truncate T (stepF1 R i) (θ, b) := rfl

/-- The coefficient facts of the cutoff (the corrected form of `cutoff_coefficients`: the affine
decomposition is asserted only for parameters in `B`, where `R` is regular). -/
theorem p11_cutoff_coeff {n : ℕ} (hn : 1 ≤ n) {r s T d eps : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : 0 ≤ T) (hd : 0 < d) (hdr : d < r)
    (he : 0 ≤ eps) {B : Set (P11CVec n)} (hB : IsOpen B) {R : P11Family n → ℂ}
    (hR : p11Admissible r s B R) (hb : p11Bound (domain_def n r s B) R eps) :
    p11AngleClass (r-d) B (p11R0 T R) ∧
    (∀ i, p11AngleClass (r-d) B (fun z => p11R1 T R z i)) ∧
    (∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T (p11R0 T R) z = p11R0 T R z) ∧
    (∀ i, ∀ z ∈ Set.univ ×ˢ B,
      KAM.Weighted.truncate T (fun z => p11R1 T R z i) z = p11R1 T R z i) ∧
    p11Bound (KAM.complexStrip n (r-d) ×ˢ B) (p11R0 T R) ((1+p11Error n T d)*eps) ∧
    p11Bound (KAM.complexStrip n (r-d) ×ˢ B) (p11R1 T R) ((1+p11Error n T d)*eps/s) ∧
    (∀ z : P11Family n, z.2 ∈ B → p11Cutoff T R z = p11R0 T R (z.1.1, z.2) +
      ∑ i, p11R1 T R (z.1.1, z.2) i * z.1.2 i) := by
  have hs' : 0 < s := hs
  -- admissibility and bounds of the coefficient families
  have hF0 : p11Admissible r s B (stepFam0 R) := by
    refine ⟨?_, fun j z hz => stepF0_periodic hs hR j (z.1.1, z.2) ⟨hz.1.1, hz.2⟩⟩
    refine (stepF0_diff hr hs hR).comp (f := fun z : P11Family n => (z.1.1, z.2))
      (by fun_prop) ?_
    rintro ⟨⟨θ, η⟩, b⟩ hz
    exact ⟨(p11_mem_domain_def.mp hz).1, (p11_mem_domain_def.mp hz).2.2⟩
  have hF1 : ∀ i, p11Admissible r s B (stepFam1 R i) := fun i => by
    refine ⟨?_, fun j z hz => stepF1_periodic hs hB hR j i (z.1.1, z.2) ⟨hz.1.1, hz.2⟩⟩
    refine (stepF1_diff hr hs hB hR i).comp (f := fun z : P11Family n => (z.1.1, z.2))
      (by fun_prop) ?_
    rintro ⟨⟨θ, η⟩, b⟩ hz
    exact ⟨(p11_mem_domain_def.mp hz).1, (p11_mem_domain_def.mp hz).2.2⟩
  have hb0 : p11Bound (domain_def n r s B) (stepFam0 R) eps := by
    rintro ⟨⟨θ, η⟩, b⟩ hz
    exact norm_stepF0_le hs hb (θ, b) ⟨(p11_mem_domain_def.mp hz).1, (p11_mem_domain_def.mp hz).2.2⟩
  have hb1 : ∀ i, p11Bound (domain_def n r s B) (stepFam1 R i) (eps / s) := fun i => by
    rintro ⟨⟨θ, η⟩, b⟩ hz
    exact norm_stepF1_le hr hs he hB hR hb i (θ, b)
      ⟨(p11_mem_domain_def.mp hz).1, (p11_mem_domain_def.mp hz).2.2⟩
  have hfc0 := fourier_cutoff hn hr hs hT hd hdr hB hF0 he hb0
  have hfc1 := fun i => fourier_cutoff hn hr hs hT hd hdr hB (hF1 i)
    (div_nonneg he hs.le) (hb1 i)
  have hsub : ∀ {θ b : P11CVec n}, θ ∈ KAM.complexStrip n (r-d) → b ∈ B →
      ((θ, (0 : P11CVec n)), b) ∈ domain_def n (r-d) s B := fun hθ hb' =>
    p11_mem_domain_def.mpr ⟨hθ, by simpa using hs, hb'⟩
  -- the angle classes through `p11Cut`
  have hcls : ∀ F : P11Family n → ℂ, p11Admissible (r-d) s B (p11Cut T F) →
      p11AngleClass (r-d) B (fun u => p11Cut T F ((u.1, 0), u.2)) := fun F hF => by
    refine ⟨?_, fun j z hz => ?_⟩
    · refine hF.1.comp (f := fun u : P11CVec n × P11CVec n => ((u.1, (0 : P11CVec n)), u.2))
        (by fun_prop) ?_
      rintro ⟨θ, b⟩ ⟨h1, h2⟩
      exact hsub h1 h2
    · exact hF.2 j ((z.1, 0), z.2) (hsub hz.1 hz.2)
  have hR0fun : p11R0 T R = fun u => p11Cut T (stepFam0 R) ((u.1, 0), u.2) :=
    funext fun u => cutoff_R0 u.1 u.2
  have hR1eq : ∀ i, ∀ θ b, b ∈ B → p11R1 T R (θ, b) i = p11Cut T (stepFam1 R i) ((θ, 0), b) :=
    fun i θ b hb' => cutoff_R1 hr hs hB hR θ hb' i
  refine ⟨?_, fun i => ?_, ?_, fun i => ?_, ?_, ?_, ?_⟩
  · rw [hR0fun]; exact hcls _ hfc0.2.1
  · have := hcls _ (hfc1 i).2.1
    refine ⟨this.1.congr fun u hu => hR1eq i u.1 u.2 hu.2, fun j z hz => ?_⟩
    show p11R1 T R (z.1 + Pi.single j 1, z.2) i = p11R1 T R z i
    rw [hR1eq i _ _ hz.2, show p11R1 T R z i = p11R1 T R (z.1, z.2) i from rfl,
      hR1eq i _ _ hz.2]
    exact this.2 j z hz
  · rintro ⟨θ, b⟩ -
    have hf : p11R0 T R = KAM.Weighted.truncate T (stepF0 R) :=
      funext fun u => cutoff_R0 u.1 u.2
    rw [hf]
    exact truncate_truncate (stepF0 R) θ b
  · rintro ⟨θ, b⟩ ⟨-, hbB⟩
    have : ∀ θ', p11R1 T R (θ', b) i = KAM.Weighted.truncate T (stepF1 R i) (θ', b) :=
      fun θ' => cutoff_R1 hr hs hB hR θ' hbB i
    have h1 : KAM.Weighted.truncate T (fun z => p11R1 T R z i) (θ, b) =
        KAM.Weighted.truncate T (KAM.Weighted.truncate T (stepF1 R i)) (θ, b) :=
      truncate_congr_param (u := fun z => p11R1 T R z i)
        (v := KAM.Weighted.truncate T (stepF1 R i)) (fun θ' => this θ') θ
    rw [h1, truncate_truncate, ← this θ]
  · rintro ⟨θ, b⟩ ⟨h1, h2⟩
    rw [hR0fun]
    exact hfc0.2.2.2.1 _ (hsub h1 h2)
  · rintro ⟨θ, b⟩ ⟨h1, h2⟩
    have hE : 0 ≤ p11Error n T d := by
      unfold p11Error; have := p11C_ge_one hn; positivity
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [mul_div_assoc]
    have := (hfc1 i).2.2.2.1 _ (hsub h1 h2)
    simpa [hR1eq i θ b h2] using this
  · rintro ⟨⟨θ, η⟩, b⟩ hbB
    dsimp only
    rw [cutoff_decomp hr hs hB hR θ η hbB, cutoff_R0]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cutoff_R1 hr hs hB hR θ hbB i, mul_comm]

end KAM.Planetary

end
