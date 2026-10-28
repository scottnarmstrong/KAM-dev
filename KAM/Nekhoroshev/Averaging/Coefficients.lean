/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Field
public import KAM.Weighted.Coefficients

/-!
# Part N12: Fourier coefficients of the perturbation (`bpN:p12:coef`)

`avgCoeff` is the existing Bochner torus coefficient `KAM.Weighted.coeff`,
`avgBeta s k = e^{-π s |k|₁}` the decay profile and `avgQ h k I = k · ω(I)` the resonance divisor.
`coef` (steps `co-a` to `co-d`) records: holomorphy of the coefficients on the action tube, the
decay `‖f̂_k‖ ≤ β_k`, the Cauchy bound `2/s β_k` on action derivatives at real actions, the
Fourier series of `f` and of `A = -∂_θ Re f` on the real domain, and summability of the
polynomial weights `(1+|k|₁)³ β_k`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal ContDiff

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

def avgCoeff (f : AvgComplexPhase n → ℂ) (I : Fin n → ℂ) (k : Fin n → ℤ) : ℂ :=
  KAM.Weighted.coeff f I k
def avgBeta (s : ℝ) (k : Fin n → ℤ) : ℝ :=
  Real.exp (-Real.pi * s * KAM.Fourier.modeSize k)
def avgQ (h : (Fin n → ℂ) → ℂ) (k : Fin n → ℤ) (I : Fin n → ℝ) : ℝ :=
  ∑ j, (k j : ℝ) * KAM.frequencyMap h I j

/-- The base of the coefficient tube. -/
private abbrev baseD (n : ℕ) (R : ℝ) : Set (Fin n → ℂ) := KAM.realInclusion n '' actionBall n R

private theorem cast_single (j : Fin n) :
    (fun i => (((Pi.single j 1 : Fin n → ℤ) i : ℤ) : ℂ)) = Pi.single j 1 := by
  ext i
  by_cases hij : i = j <;> simp [hij]

private theorem dom_eq (R s : ℝ) :
    KAM.Weighted.Dom n (baseD n R) s s = complexDomain n R s := by
  unfold KAM.Weighted.Dom complexDomain
  rw [← KAM.Weighted.actionNbhd_eq_polyNbhd]

private theorem inClass (d : AveragingData n R s h f) :
    KAM.Weighted.InClass (baseD n R) s s f := by
  refine ⟨by rw [dom_eq]; exact d.hf.2.1, fun j z hz => ?_⟩
  rw [dom_eq] at hz
  have := d.hf.2.2.2.1 z hz (Pi.single j 1)
  rwa [cast_single] at this

private theorem slice_diff (d : AveragingData n R s h f) {I : Fin n → ℂ}
    (hI : I ∈ KAM.actionNbhd (actionBall n R) s) {ρ : ℝ} (hρ : ρ ≤ s) :
    DifferentiableOn ℂ (fun θ => f (θ, I)) (KAM.complexStrip n ρ) := by
  refine d.hf.2.1.comp (differentiable_id.prodMk (differentiable_const I)).differentiableOn
    fun θ hθ => ⟨fun i => (hθ i).trans_le hρ, hI⟩

private theorem slice_per (d : AveragingData n R s h f) {I : Fin n → ℂ}
    (hI : I ∈ KAM.actionNbhd (actionBall n R) s) {ρ : ℝ} (hρ : ρ ≤ s) (i : Fin n) (θ : Fin n → ℂ)
    (hθ : θ ∈ KAM.complexStrip n ρ) : f (θ + Pi.single i 1, I) = f (θ, I) := by
  have := d.hf.2.2.2.1 (θ, I) ⟨fun i => (hθ i).trans_le hρ, hI⟩ (Pi.single i 1)
  rw [cast_single] at this
  exact this

/-- `co-a`, decay: `‖f̂_k(I)‖ ≤ β_k` on the tube. -/
private theorem coeff_decay (d : AveragingData n R s h f) {I : Fin n → ℂ}
    (hI : I ∈ KAM.actionNbhd (actionBall n R) s) (k : Fin n → ℤ) :
    ‖avgCoeff f I k‖ ≤ avgBeta s k := by
  have h1 := KAM.decay_boundary_radius (A := 1) d.hs (slice_diff d hI le_rfl)
    (fun i θ hθ => slice_per d hI le_rfl i θ hθ)
    (fun θ hθ => by simpa using d.hf.2.2.2.2.2 (θ, I) ⟨hθ, hI⟩) k
  refine (le_of_eq_of_le (by rfl) h1).trans ?_
  rw [mul_one, avgBeta]
  refine Real.exp_le_exp.2 ?_
  have hm : 0 ≤ KAM.Fourier.modeSize k := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have := mul_nonneg (mul_nonneg Real.pi_pos.le d.hs.le) hm
  linarith

/-- `co-b`, Cauchy: `‖D f(θ, I)‖ ≤ 2/s` for `|Im θ| < s/2` and real `I` in the ball. -/
private theorem norm_fderiv_le (d : AveragingData n R s h f) {θ : Fin n → ℂ}
    (hθ : θ ∈ KAM.complexStrip n (s / 2)) {I : Fin n → ℝ} (hI : I ∈ actionBall n R) :
    ‖fderiv ℂ f (θ, KAM.realInclusion n I)‖ ≤ 2 / s := by
  have hs := d.hs
  have hball : closedBall (θ, KAM.realInclusion n I) (s / 2) ⊆ complexDomain n R s := by
    intro w hw
    have hw' : ‖w - (θ, KAM.realInclusion n I)‖ ≤ s / 2 := by
      simpa only [mem_closedBall, dist_eq_norm] using hw
    refine ⟨?_, I, hI, ?_⟩
    · have h1 : w.1 ∈ closedBall θ (s / 2) := by
        rw [mem_closedBall, dist_eq_norm]
        exact (norm_fst_le _).trans hw'
      refine KAM.closedBall_subset_complexStrip (ρ := s) (δ := s / 2) ?_ h1
      intro i
      have := hθ i
      linarith
    · calc ‖w.2 - KAM.realInclusion n I‖ ≤ s / 2 := (norm_snd_le _).trans hw'
        _ < s := by linarith
  have := KAM.norm_fderiv_le_of_closedBall (isOpen_complexDomain R s) d.hf.2.1
    (z := (θ, KAM.realInclusion n I)) (δ := s / 2) (A := 1) (by linarith) hball
    (fun w hw => by simpa using d.hf.2.2.2.2.2 w hw)
  convert this using 1
  field_simp

private theorem realI_mem (d : AveragingData n R s h f) {I : Fin n → ℝ} (hI : I ∈ actionBall n R) :
    KAM.realInclusion n I ∈ KAM.actionNbhd (actionBall n R) s :=
  ⟨I, hI, by
    rw [show (KAM.realInclusion n I - fun i => (I i : ℂ)) = 0 from by ext i; simp, norm_zero]
    exact d.hs⟩

/-- Directional derivative of `f` bounded by `2/s ‖v‖` on slices. -/
private theorem norm_dir_le (d : AveragingData n R s h f) {θ : Fin n → ℂ}
    (hθ : θ ∈ KAM.complexStrip n (s / 2)) {I : Fin n → ℝ} (hI : I ∈ actionBall n R)
    (v : AvgComplexPhase n) :
    ‖fderiv ℂ f (θ, KAM.realInclusion n I) v‖ ≤ 2 / s * ‖v‖ :=
  ((fderiv ℂ f _).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le d hθ hI) (norm_nonneg _))

private theorem norm_single_prod_fst (j : Fin n) :
    ‖((Pi.single j (1 : ℂ), 0) : AvgComplexPhase n)‖ ≤ 1 := by
  simp [Prod.norm_def, Pi.norm_single]

private theorem norm_single_prod_snd (j : Fin n) :
    ‖((0, Pi.single j (1 : ℂ)) : AvgComplexPhase n)‖ ≤ 1 := by
  simp [Prod.norm_def, Pi.norm_single]

/-- Decay of a directional-derivative coefficient on a real slice. -/
private theorem coeff_dir_decay (d : AveragingData n R s h f) {I : Fin n → ℝ}
    (hI : I ∈ actionBall n R) (v : AvgComplexPhase n) (hv : ‖v‖ ≤ 1)
    (hu : KAM.Weighted.InClass (baseD n R) s s (fun z => fderiv ℂ f z v)) (k : Fin n → ℤ) :
    ‖KAM.Weighted.coeff (fun z => fderiv ℂ f z v) (KAM.realInclusion n I) k‖ ≤
      2 / s * avgBeta s k := by
  have hs := d.hs
  have hIn := realI_mem d hI
  have hmem : ∀ θ ∈ KAM.complexStrip n (s / 2),
      (θ, KAM.realInclusion n I) ∈ KAM.Weighted.Dom n (baseD n R) s s := by
    intro θ hθ
    rw [dom_eq]
    exact ⟨fun i => (hθ i).trans (by linarith), hIn⟩
  have h1 := KAM.decay_boundary_radius (A := 2 / s) (ρ := s / 2) (by linarith)
    (u := fun θ => fderiv ℂ f (θ, KAM.realInclusion n I) v)
    (hu.differentiableOn.comp (differentiable_id.prodMk (differentiable_const _)).differentiableOn
      hmem)
    (fun i θ hθ => hu.periodic i _ (hmem θ hθ))
    (fun θ hθ => by
      refine (norm_dir_le d hθ hI v).trans ?_
      have : 0 ≤ 2 / s := by positivity
      simpa using mul_le_mul_of_nonneg_left hv this) k
  refine (le_of_eq_of_le (by rfl) h1).trans ?_
  rw [avgBeta, mul_comm]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
  congr 1
  ring

/-- Fourier series of a slice function at real angles. -/
private theorem hasSum_slice {u : AvgComplexPhase n → ℂ} {I : Fin n → ℂ} {ρ A : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ (fun θ => u (θ, I)) (KAM.complexStrip n ρ))
    (hp : ∀ (i : Fin n) θ, θ ∈ KAM.complexStrip n ρ → u (θ + Pi.single i 1, I) = u (θ, I))
    (hA : ∀ θ ∈ KAM.complexStrip n ρ, ‖u (θ, I)‖ ≤ A) (x : Fin n → ℝ) :
    HasSum (fun k => KAM.Weighted.coeff u I k * KAM.character k (KAM.realInclusion n x))
      (u (KAM.realInclusion n x, I)) := by
  have hx : KAM.realInclusion n x ∈ KAM.complexStrip n ρ := KAM.ofReal_mem_complexStrip hρ x
  have heq := KAM.eq_fourierSumVec_torusCoeffW hρ hd hp hA hx
  obtain ⟨hsum, -⟩ := KAM.summableWeighted_torusCoeffW (half_pos hρ) (by linarith) hd hp hA
  have hx' : KAM.realInclusion n x ∈ KAM.complexStrip n (ρ - ρ / 2) :=
    KAM.ofReal_mem_complexStrip (by linarith) x
  have hterm := KAM.summable_character_smul hsum hx'
  have hS : HasSum (fun k => KAM.character k (KAM.realInclusion n x) •
      KAM.torusCoeffW (fun y : Fin n → ℝ => u (fun j => (y j : ℂ), I)) k)
      (u (KAM.realInclusion n x, I)) := by
    rw [heq]
    exact hterm.hasSum
  convert hS using 2 with k
  rw [smul_eq_mul, mul_comm]
  rfl

/-- `co-d`: the polynomial weights `(1 + |k|₁)³ β_k` are summable. -/
private theorem summable_poly (hs : 0 < s) :
    Summable (fun k : Fin n → ℤ => (1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k) := by
  set c : ℝ := Real.pi * s / 2 with hc
  have hc0 : 0 < c := by positivity
  have hgeo := (KAM.Fourier.hasSum_exp_neg_modeSize n hc0).summable
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (hgeo.mul_left (6 / c ^ 3 * Real.exp c))
  · have hm : 0 ≤ KAM.Fourier.modeSize k := Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact mul_nonneg (by positivity) (Real.exp_pos _).le
  · have hm : 0 ≤ KAM.Fourier.modeSize k := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h1 := Real.pow_div_factorial_le_exp (c * (1 + KAM.Fourier.modeSize k)) (by positivity) 3
    norm_num [Nat.factorial] at h1
    have h2 : (1 + KAM.Fourier.modeSize k) ^ 3 ≤
        6 / c ^ 3 * Real.exp (c * (1 + KAM.Fourier.modeSize k)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : (c * (1 + KAM.Fourier.modeSize k)) ^ 3 ≤
          6 * Real.exp (c * (1 + KAM.Fourier.modeSize k)) := by
        linarith
      calc (1 + KAM.Fourier.modeSize k) ^ 3 * c ^ 3
          = (c * (1 + KAM.Fourier.modeSize k)) ^ 3 := by ring
        _ ≤ _ := this
    calc (1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k
        ≤ 6 / c ^ 3 * Real.exp (c * (1 + KAM.Fourier.modeSize k)) * avgBeta s k :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = 6 / c ^ 3 * Real.exp c * Real.exp (-c * KAM.Fourier.modeSize k) := by
          rw [avgBeta, mul_assoc, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
          congr 2
          rw [hc]; ring

private theorem single_eq (j : Fin n) :
    KAM.realInclusion n (Pi.single j (1 : ℝ)) = (Pi.single j 1 : Fin n → ℂ) := by
  ext i
  by_cases hij : i = j <;> simp [hij]

private theorem iota_mem (d : AveragingData n R s h f) {z : AvgPhase n} (hz : z ∈ avgDomain n R) :
    KAM.realInclusion₂ n z ∈ complexDomain n R s := by
  have hz' := avgDomain_subset_Wdom d hz
  rw [← realInclusion₂_preimage_complexDomain d.hR d.hs] at hz'
  exact hz'

/-- The real partial derivative of `Re (f ∘ ι)` is the complex one, which is real. -/
private theorem real_partial (d : AveragingData n R s h f) {z : AvgPhase n}
    (hz : z ∈ avgDomain n R) (v : AvgPhase n) :
    ((fderiv ℝ (fun y : AvgPhase n => (f (KAM.realInclusion₂ n y)).re) z v : ℝ) : ℂ) =
      fderiv ℂ f (KAM.realInclusion₂ n z) (KAM.realInclusion₂ n v) := by
  have hfd : DifferentiableAt ℂ f (KAM.realInclusion₂ n z) :=
    d.hf.2.1.differentiableAt ((isOpen_complexDomain R s).mem_nhds (iota_mem d hz))
  have hF : HasFDerivAt (fun y : AvgPhase n => f (KAM.realInclusion₂ n y))
      (((fderiv ℂ f (KAM.realInclusion₂ n z)).restrictScalars ℝ).comp (KAM.realInclusion₂ n)) z :=
    (hfd.hasFDerivAt.restrictScalars ℝ).comp z (KAM.realInclusion₂ n).hasFDerivAt
  have hre := (Complex.reCLM.hasFDerivAt.comp z hF).fderiv
  have him := (Complex.imCLM.hasFDerivAt.comp z hF)
  have hev : (fun y : AvgPhase n => (f (KAM.realInclusion₂ n y)).im) =ᶠ[nhds z]
      fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_Wdom (n := n) R s).mem_nhds (avgDomain_subset_Wdom d hz)] with y hy
    have hy2 : y.2 ∈ realActionDomain n R s := by
      rw [realActionDomain_eq d.hR d.hs]; exact hy.2
    exact d.hf.2.2.2.2.1 y.1 y.2 hy2
  have him0 : (Complex.imCLM.comp (((fderiv ℂ f (KAM.realInclusion₂ n z)).restrictScalars ℝ).comp
      (KAM.realInclusion₂ n))) = 0 :=
    him.unique ((hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq hev)
  have hre' : fderiv ℝ (fun y : AvgPhase n => (f (KAM.realInclusion₂ n y)).re) z v =
      (fderiv ℂ f (KAM.realInclusion₂ n z) (KAM.realInclusion₂ n v)).re := by
    exact congrArg (fun L => L v) hre
  have him' : (fderiv ℂ f (KAM.realInclusion₂ n z) (KAM.realInclusion₂ n v)).im = 0 := by
    have := congrArg (fun L => L v) him0
    simpa using this
  rw [hre']
  exact Complex.ext (by simp) (by rw [him']; simp)

private theorem polyNbhd_real (d : AveragingData n R s h f) {I : Fin n → ℝ}
    (hI : I ∈ actionBall n R) : KAM.realInclusion n I ∈ KAM.Weighted.polyNbhd (baseD n R) s := by
  rw [← KAM.Weighted.actionNbhd_eq_polyNbhd]; exact realI_mem d hI

/-- The slice hypotheses of `hasSum_slice` for a class function with an `A`-bounded slice. -/
private theorem hasSum_class_slice (d : AveragingData n R s h f)
    {u : AvgComplexPhase n → ℂ} (hu : KAM.Weighted.InClass (baseD n R) s s u) {A : ℝ}
    {I : Fin n → ℝ} (hI : I ∈ actionBall n R)
    (hA : ∀ θ ∈ KAM.complexStrip n (s / 2), ‖u (θ, KAM.realInclusion n I)‖ ≤ A) (x : Fin n → ℝ) :
    HasSum (fun k => KAM.Weighted.coeff u (KAM.realInclusion n I) k *
      KAM.character k (KAM.realInclusion n x))
      (u (KAM.realInclusion n x, KAM.realInclusion n I)) := by
  have hs := d.hs
  have hmem : ∀ θ ∈ KAM.complexStrip n (s / 2),
      (θ, KAM.realInclusion n I) ∈ KAM.Weighted.Dom n (baseD n R) s s := by
    intro θ hθ
    rw [dom_eq]
    exact ⟨fun i => (hθ i).trans (by linarith), realI_mem d hI⟩
  exact hasSum_slice (by linarith)
    (hu.differentiableOn.comp (differentiable_id.prodMk (differentiable_const _)).differentiableOn
      hmem)
    (fun i θ hθ => hu.periodic i _ (hmem θ hθ)) hA x

theorem coef (d : AveragingData n R s h f) :
    (∀ k : Fin n → ℤ, DifferentiableOn ℂ (fun I => avgCoeff f I k)
      (KAM.actionNbhd (actionBall n R) s)) ∧
    (∀ I ∈ KAM.actionNbhd (actionBall n R) s, ∀ k, ‖avgCoeff f I k‖ ≤ avgBeta s k) ∧
    (∀ I ∈ actionBall n R, ∀ k, ∀ j,
      ‖fderiv ℂ (fun J => avgCoeff f J k) (KAM.realInclusion n I) (Pi.single j 1)‖ ≤
        2 / s * avgBeta s k) ∧
    (∀ z ∈ avgDomain n R, HasSum (fun k : Fin n → ℤ =>
      avgCoeff f (KAM.realInclusion n z.2) k * KAM.character k (KAM.realInclusion n z.1))
        (f (KAM.realInclusion₂ n z))) ∧
    (∀ z ∈ avgDomain n R, HasSum (fun k : Fin n → ℤ => fun j =>
      -2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) *
        avgCoeff f (KAM.realInclusion n z.2) k * KAM.character k (KAM.realInclusion n z.1))
      (KAM.realInclusion n (avgA f z))) ∧
    Summable (fun k : Fin n → ℤ => (1 + KAM.Fourier.modeSize k) ^ 3 * avgBeta s k) := by
  have hu := inClass d
  have hder := KAM.Weighted.coefficients_deriv d.hs hu
  refine ⟨fun k => ?_, fun I hI k => coeff_decay d hI k, fun I hI k j => ?_, fun z hz => ?_,
    fun z hz => ?_, summable_poly d.hs⟩
  · have := KAM.Weighted.coeff_differentiableOn d.hs hu k
    rwa [← KAM.Weighted.actionNbhd_eq_polyNbhd] at this
  · have e := (hder.2 j).2 _ (polyNbhd_real d hI) k
    have hbd := coeff_dir_decay d hI (0, Pi.single j 1) (norm_single_prod_snd j)
      (hder.2 j).1 k
    exact e ▸ hbd
  · have hA : ∀ θ ∈ KAM.complexStrip n (s / 2), ‖f (θ, KAM.realInclusion n z.2)‖ ≤ 1 :=
      fun θ hθ => by
        have := d.hf.2.2.2.2.2 (θ, KAM.realInclusion n z.2)
          ⟨fun i => (hθ i).trans (by linarith [d.hs]), realI_mem d hz.2⟩
        simpa using this
    exact hasSum_class_slice d hu hz.2 hA z.1
  · rw [Pi.hasSum]
    intro j
    have hA : ∀ θ ∈ KAM.complexStrip n (s / 2),
        ‖KAM.Weighted.dtheta j f (θ, KAM.realInclusion n z.2)‖ ≤ 2 / s := fun θ hθ => by
      have := norm_dir_le d hθ hz.2 (Pi.single j 1, 0)
      have h1 := norm_single_prod_fst (n := n) j
      have h0 : 0 ≤ 2 / s := by have := d.hs; positivity
      exact this.trans (by simpa using mul_le_mul_of_nonneg_left h1 h0)
    have hS := (hasSum_class_slice d (hder.1 j).1 hz.2 hA z.1).neg
    have hcoef := fun k => (hder.1 j).2 _ (polyNbhd_real d hz.2) k
    have hreal := real_partial d hz (Pi.single j 1, 0)
    have htarget : (KAM.realInclusion n (avgA f z)) j =
        -KAM.Weighted.dtheta j f (KAM.realInclusion n z.1, KAM.realInclusion n z.2) := by
      have e : KAM.realInclusion₂ n (Pi.single j (1 : ℝ), (0 : Fin n → ℝ)) =
          ((Pi.single j 1 : Fin n → ℂ), 0) := by
        rw [KAM.realInclusion₂_apply, single_eq, map_zero]
      rw [e] at hreal
      simp only [KAM.realInclusion_apply, avgA]
      rw [Complex.ofReal_neg, hreal]
      rfl
    rw [htarget]
    convert hS using 1
    funext k
    rw [hcoef k, smul_eq_mul]
    simp only [avgCoeff]
    ring

end KAM.Nekhoroshev

end
