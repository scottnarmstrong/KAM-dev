/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.Divisor
public import KAM.Planetary.MaximalStep.Homological
public import KAM.Planetary.MaximalStep.StepReal
public import KAM.Planetary.MaximalStep.StepBound

/-!
# The maximal homological equation: the literal nodes (P11A-C5)

Unsigned literal exports of `stepP:p11a:hm-div`, `stepP:p11a:hm-bracket` and
`bpP:p11a:homological-maximal`, from the source premises only (no `0 ≤ L`, no divisor bundle):

* `hm_div_node`: `|k·ω(b)| ≥ D/2` on `B = E + t` (`divisor_perturb` with `0 ≤ L` derived from the
  bound itself at a point of `B`);
* `hm_bracket_node`: for the solutions `φ₀, φ₁ⱼ` (`p11Solve`), `{N_b, φ} = -ω·∂_θ φ = -(P - ⟨P⟩)`;
* `homological_maximal_node`: existence, uniqueness and the clauses (a)–(e) of the proposition, for
  the datum `P₀, P₁ⱼ`, together with the bracket identity (`HmMaxSolution`).

The dimension is arbitrary (`N ≥ 1` is not needed).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- `stepP:p11a:hm-div`: `|k·ω(b)| ≥ D/2` for all `b ∈ B = E + t`, `0 < |k|₁ ≤ T`. -/
theorem hm_div_node {n : ℕ} {E : Set (P11Vec n)} {t T D L : ℝ}
    (ht : 0 < t) (hT : 0 < T) (hD : 0 < D)
    (w : P11CVec n → P11CVec n) (hw : DifferentiableOn ℂ w (KAM.actionNbhd E t))
    (hb : ∀ b ∈ KAM.actionNbhd E t, ‖fderiv ℂ w b‖ ≤ L)
    (hsmall : t*T*L ≤ D/2)
    (hdiv : ∀ b ∈ E, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      D ≤ ‖p11dotC k (w (KAM.realInclusion n b))‖) :
    ∀ b ∈ KAM.actionNbhd E t, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      D/2 ≤ ‖p11dotC k (w b)‖ := fun b hbB =>
  divisor_perturb ht hT hD ((norm_nonneg _).trans (hb b hbB)) w hw hb hsmall hdiv b hbB

/-- Admissible trigonometric polynomial of degree `≤ T` in `θ`, holomorphic on `ℂᴺ × B`, one-
periodic, with zero average. -/
def HmZeroMeanTrig {n : ℕ} (T : ℝ) (B : Set (P11CVec n))
    (u : P11CVec n × P11CVec n → ℂ) : Prop :=
  DifferentiableOn ℂ u (Set.univ ×ˢ B) ∧
  (∀ j : Fin n, ∀ z ∈ Set.univ ×ˢ B, u (z.1 + Pi.single j 1, z.2) = u z) ∧
  (∀ z ∈ Set.univ ×ˢ B, KAM.Weighted.truncate T u z = u z) ∧
  ∀ b ∈ B, p11AngleAverage u b = 0

/-- The conclusion of `bpP:p11a:homological-maximal` for one scalar datum `P` (`P₀` or `P₁ⱼ`):
`φ` is a zero-average trigonometric polynomial solving `ω(b)·∂_θ φ = P - ⟨P⟩` on `B = E + t`,
it is the only one, and the clauses (a)–(e) hold. -/
def HmMaxSolution {n : ℕ} (E : Set (P11Vec n)) (t T D rs delta M : ℝ)
    (w : P11CVec n → P11CVec n) (P phi : P11CVec n × P11CVec n → ℂ) : Prop :=
  HmZeroMeanTrig T (KAM.actionNbhd E t) phi ∧
  (∀ theta : P11CVec n, ∀ b ∈ KAM.actionNbhd E t,
    fderiv ℂ (fun x => phi (x, b)) theta (w b) = P (theta, b) - p11AngleAverage P b) ∧
  (∀ u, HmZeroMeanTrig T (KAM.actionNbhd E t) u →
    (∀ theta : P11CVec n, ∀ b ∈ KAM.actionNbhd E t,
      fderiv ℂ (fun x => u (x, b)) theta (w b) = P (theta, b) - p11AngleAverage P b) →
    ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t, u z = phi z) ∧
  p11Bound (KAM.complexStrip n (rs - delta) ×ˢ KAM.actionNbhd E t) phi
    (p11Lambda n delta * M / (Real.pi * D)) ∧
  (DifferentiableOn ℂ (p11AngleAverage P) (KAM.actionNbhd E t) ∧
    ∀ b ∈ KAM.actionNbhd E t, ‖p11AngleAverage P b‖ ≤ M) ∧
  (∀ tp : ℝ, 0 < tp → tp < t → ∀ j : ℕ, 1 ≤ j →
    ∀ theta ∈ KAM.complexStrip n (rs - delta), ∀ b ∈ KAM.actionNbhd E tp,
      ‖iteratedFDeriv ℂ j (fun b => phi (theta, b)) b‖ ≤
        (j : ℝ)^j * p11Lambda n delta * M / (Real.pi * D * (t - tp)^j) ∧
      ‖iteratedFDeriv ℂ j (p11AngleAverage P) b‖ ≤ (j : ℝ)^j * M / (t - tp)^j) ∧
  ((∀ b : P11Vec n, KAM.realInclusion n b ∈ KAM.actionNbhd E t →
      ∀ i, (w (KAM.realInclusion n b) i).im = 0) →
    (∀ x b : P11Vec n, KAM.realInclusion n b ∈ KAM.actionNbhd E t →
      (P (KAM.realInclusion n x, KAM.realInclusion n b)).im = 0) →
    ∀ x b : P11Vec n, KAM.realInclusion n b ∈ KAM.actionNbhd E t →
      (phi (KAM.realInclusion n x, KAM.realInclusion n b)).im = 0 ∧
        (p11AngleAverage P (KAM.realInclusion n b)).im = 0) ∧
  ∀ b ∈ KAM.actionNbhd E t, ∀ k : Fin n → ℤ, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
    ‖KAM.Weighted.coeff phi b k‖ ≤
      M * Real.exp (-2 * Real.pi * KAM.Fourier.modeSize k * rs) / (Real.pi * D)

/-- No parameters: for `E = ∅` every clause of `HmMaxSolution` is empty. -/
theorem hmMaxSolution_of_empty {n : ℕ} {t T D rs delta M : ℝ} (w : P11CVec n → P11CVec n)
    (P phi : P11CVec n × P11CVec n → ℂ) :
    HmMaxSolution (∅ : Set (P11Vec n)) t T D rs delta M w P phi := by
  have h : KAM.actionNbhd (∅ : Set (P11Vec n)) t = ∅ := by
    ext I; simp [KAM.actionNbhd]
  simp [HmMaxSolution, HmZeroMeanTrig, h]

section Solve
variable {n : ℕ} {E : Set (P11Vec n)} {t T D rs delta M : ℝ} {w : P11CVec n → P11CVec n}
  {P : P11CVec n × P11CVec n → ℂ}

theorem hm_diff_at {B : Set (P11CVec n)} (hr : 0 < rs) (hB : IsOpen B) (hD : 0 < D)
    (hP : DifferentiableOn ℂ P (KAM.complexStrip n rs ×ˢ B)) (hw : DifferentiableOn ℂ w B)
    (hdiv : ∀ b ∈ B, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T → D/2 ≤ ‖p11dotC k (w b)‖)
    {b : P11CVec n} (hbB : b ∈ B) (theta : P11CVec n) :
    DifferentiableAt ℂ (fun x => p11Solve T w P x b) theta := by
  have h1 := differentiableOn_solve hr hB hD hP hw hdiv (T := T)
  have h2 : DifferentiableOn ℂ (fun x : P11CVec n => p11Solve T w P x b) Set.univ :=
    h1.comp (f := fun x : P11CVec n => (x, b))
      (differentiableOn_id.prodMk (differentiableOn_const b)) fun x _ => ⟨trivial, hbB⟩
  exact h2.differentiableAt Filter.univ_mem

/-- The solution `p11Solve` realises every clause of the proposition for one scalar datum. -/
theorem hmMaxSolution_solve (hr : 0 < rs) (hd : 0 < delta) (hdr : delta < rs) (hT : 0 < T)
    (hD : 0 < D) (hM : 0 ≤ M) (ht : 0 < t)
    (hw : DifferentiableOn ℂ w (KAM.actionNbhd E t))
    (hdiv : ∀ b ∈ KAM.actionNbhd E t, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      D/2 ≤ ‖p11dotC k (w b)‖)
    (hP : p11AngleClass rs (KAM.actionNbhd E t) P)
    (hpoly : ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t, KAM.Weighted.truncate T P z = P z)
    (hb : p11Bound (KAM.complexStrip n rs ×ˢ KAM.actionNbhd E t) P M) :
    HmMaxSolution E t T D rs delta M w P (fun z => p11Solve T w P z.1 z.2) := by
  have hB := p11_isOpen_actionNbhd E t
  have hdiff : DifferentiableOn ℂ (fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2)
      (Set.univ ×ˢ KAM.actionNbhd E t) := differentiableOn_solve hr hB hD hP.1 hw hdiv
  have hper : ∀ j : Fin n, ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t,
      p11Solve T w P (z.1 + Pi.single j 1) z.2 = p11Solve T w P z.1 z.2 := fun j z _ => by
    rw [p11Solve_eq, p11Solve_eq, KAM.fourierSum_add_single]
  have htrunc : ∀ z : P11CVec n × P11CVec n,
      KAM.Weighted.truncate T (fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2) z =
        p11Solve T w P z.1 z.2 := by
    rintro ⟨theta, b⟩
    show KAM.Weighted.truncate T _ (theta, b) = p11Solve T w P theta b
    rw [truncate_eq, p11Solve_eq]
    congr 1
    funext k
    by_cases hk : KAM.Fourier.modeSize k ≤ T
    · simp [hmCut, hk, coeff_solve]
    · have : T < KAM.Fourier.modeSize k := not_le.1 hk
      simp [hmCut, hk, hmCoef, this]
  have hzero : ∀ b ∈ KAM.actionNbhd E t,
      p11AngleAverage (fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2) b = 0 :=
    fun b _ => by
      show KAM.Weighted.coeff (fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2) b 0 = 0
      rw [coeff_solve, hmCoef_zero]
  have heq : ∀ theta : P11CVec n, ∀ b ∈ KAM.actionNbhd E t,
      fderiv ℂ (fun x => p11Solve T w P x b) theta (w b) = P (theta, b) - p11AngleAverage P b :=
    fun theta b hbB => by
      rw [fderiv_solve hT.le (hdiv b hbB) hD theta, hpoly (theta, b) ⟨trivial, hbB⟩]
      rfl
  have hstrip : ∀ b ∈ KAM.actionNbhd E t, ∀ k : Fin n → ℤ, k ≠ 0 →
      KAM.Fourier.modeSize k ≤ T → ‖hmCoef T w P b k‖ ≤
        M * Real.exp (-2 * Real.pi * KAM.Fourier.modeSize k * rs) / (Real.pi * D) :=
    fun b hbB k hk hkT => by
      have := norm_hmCoef_le hD hr hP hb hbB (hdiv b hbB) hk hkT
      convert this using 2
      rw [mul_comm]; congr 2; ring
  refine ⟨⟨hdiff, hper, fun z _ => htrunc z, hzero⟩, heq, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro u hu heq' z hz
    refine solve_unique (r := rs) (delta := delta) hT.le hD (by linarith) hpoly hdiv u hu.2.2.1
      hu.2.2.2 (fun theta _ b hbB => heq' theta b hbB) z hz
  · exact fun z hz => norm_solve_le hd hD hr hM hP hb hz.2 (hdiv z.2 hz.2) hz.1
  · exact differentiableOn_coeff hr hB hP.1 0
  · intro b hbB
    have := norm_coeff_le hr hP hb hbB 0
    simpa [KAM.Fourier.modeSize, p11AngleAverage] using this
  · intro tp htp htt j hj theta hθ b hbtp
    exact homological_maximal_param hr hd hdr hT hD hM htp htt w hw hdiv P hP hpoly hb hj
      theta hθ b hbtp
  · intro hwr hpr x b hbB
    refine ⟨?_, ?_⟩
    · exact homological_maximal_real hr hT hD hB w hw hdiv P hP hpoly hwr hpr x b hbB
    · exact coeff_zero_real (P := P) fun x => hpr x b hbB
  · intro b hbB k hk hkT
    show ‖KAM.Weighted.coeff (fun z : P11CVec n × P11CVec n => p11Solve T w P z.1 z.2) b k‖ ≤ _
    rw [coeff_solve]
    exact hstrip b hbB k hk hkT

/-- `hmMaxSolution_solve` without the premise `0 ≤ M` (derived at a point of `B`, or `B = ∅`). -/
theorem hmMaxSolution_solve' (hr : 0 < rs) (hd : 0 < delta) (hdr : delta < rs) (hT : 0 < T)
    (hD : 0 < D) (ht : 0 < t)
    (hw : DifferentiableOn ℂ w (KAM.actionNbhd E t))
    (hdiv : ∀ b ∈ KAM.actionNbhd E t, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      D/2 ≤ ‖p11dotC k (w b)‖)
    (hP : p11AngleClass rs (KAM.actionNbhd E t) P)
    (hpoly : ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t, KAM.Weighted.truncate T P z = P z)
    (hb : p11Bound (KAM.complexStrip n rs ×ˢ KAM.actionNbhd E t) P M) :
    HmMaxSolution E t T D rs delta M w P (fun z => p11Solve T w P z.1 z.2) := by
  rcases E.eq_empty_or_nonempty with rfl | ⟨b0, hb0E⟩
  · exact hmMaxSolution_of_empty _ _ _
  · have hM : 0 ≤ M := by
      have := hb ((fun i => (((0 : Fin n → ℝ) i : ℝ) : ℂ)), fun i => (b0 i : ℂ))
        ⟨KAM.ofReal_mem_complexStrip hr 0, ⟨b0, hb0E, by simpa using ht⟩⟩
      exact (norm_nonneg _).trans this
    exact hmMaxSolution_solve hr hd hdr hT hD hM ht hw hdiv hP hpoly hb

/-- The bracket identity for the solutions `φ₀ = p11Solve P₀`, `φ₁ⱼ = p11Solve P₁ⱼ`. -/
theorem hm_bracket_solve (hr : 0 < rs) (hT : 0 < T) (hD : 0 < D)
    (hw : DifferentiableOn ℂ w (KAM.actionNbhd E t))
    (hdiv : ∀ b ∈ KAM.actionNbhd E t, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      D/2 ≤ ‖p11dotC k (w b)‖)
    (h : P11CVec n → ℂ) (P0 : P11CVec n × P11CVec n → ℂ)
    (P1 : Fin n → P11CVec n × P11CVec n → ℂ)
    (hP0 : p11AngleClass rs (KAM.actionNbhd E t) P0)
    (hP1 : ∀ j, p11AngleClass rs (KAM.actionNbhd E t) (P1 j))
    (hpoly0 : ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t, KAM.Weighted.truncate T P0 z = P0 z)
    (hpoly1 : ∀ j, ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t,
      KAM.Weighted.truncate T (P1 j) z = P1 j z) :
    ∀ b ∈ KAM.actionNbhd E t, ∀ z : P11Phase n,
      KAM.Canonical.poissonBracket (fun y : P11Phase n => h b + ∑ i, w b i * y.2 i)
        (p11Affine (fun theta => p11Solve T w P0 theta b)
          (fun theta i => p11Solve T w (P1 i) theta b)) z =
        -(fderiv ℂ (fun theta => p11Solve T w P0 theta b) z.1 (w b) +
          ∑ i, fderiv ℂ (fun theta => p11Solve T w (P1 i) theta b) z.1 (w b) * z.2 i) ∧
      -(fderiv ℂ (fun theta => p11Solve T w P0 theta b) z.1 (w b) +
          ∑ i, fderiv ℂ (fun theta => p11Solve T w (P1 i) theta b) z.1 (w b) * z.2 i) =
        -((P0 (z.1, b) + ∑ i, P1 i (z.1, b) * z.2 i) -
          (p11AngleAverage P0 b + ∑ i, p11AngleAverage (P1 i) b * z.2 i)) := by
  intro b hbB z
  have hB := p11_isOpen_actionNbhd E t
  have d0 := hm_diff_at hr hB hD hP0.1 hw hdiv hbB z.1
  have d1i : ∀ i, DifferentiableAt ℂ (fun x => p11Solve T w (P1 i) x b) z.1 := fun i =>
    hm_diff_at hr hB hD (hP1 i).1 hw hdiv hbB z.1
  have d1 : DifferentiableAt ℂ (fun theta i => p11Solve T w (P1 i) theta b) z.1 :=
    differentiableAt_pi.2 d1i
  have e0 : fderiv ℂ (fun theta => p11Solve T w P0 theta b) z.1 (w b) =
      P0 (z.1, b) - p11AngleAverage P0 b := by
    rw [fderiv_solve hT.le (hdiv b hbB) hD z.1, hpoly0 (z.1, b) ⟨trivial, hbB⟩]
    rfl
  have e1 : ∀ i, fderiv ℂ (fun theta => p11Solve T w (P1 i) theta b) z.1 (w b) =
      P1 i (z.1, b) - p11AngleAverage (P1 i) b := fun i => by
    rw [fderiv_solve hT.le (hdiv b hbB) hD z.1, hpoly1 i (z.1, b) ⟨trivial, hbB⟩]
    rfl
  have e1' : ∀ i, fderiv ℂ (fun theta i => p11Solve T w (P1 i) theta b) z.1 (w b) i =
      P1 i (z.1, b) - p11AngleAverage (P1 i) b := fun i => by
    rw [fderiv_pi_apply d1]
    exact e1 i
  refine ⟨?_, ?_⟩
  · rw [p11_normal_affine_bracket (h b) (w b) (z := z) d0 d1]
    simp only [e1', e1]
  · simp only [e0, e1, sub_mul, Finset.sum_sub_distrib]
    ring

/-- `stepP:p11a:hm-bracket`: for the solutions `φ₀, φ₁ⱼ` of the homological equations with data
`P₀, P₁ⱼ`, `φ = φ₀ + φ₁·η`, `N_b = h + ω·η`, `P = P₀ + P₁·η`:
`{N_b, φ} = -ω·∂_θ φ = -(P - ⟨P⟩)`. -/
theorem hm_bracket_node {n : ℕ} {E : Set (P11Vec n)} {t T D L rs delta : ℝ}
    (ht : 0 < t) (hT : 0 < T) (hD : 0 < D)
    (w : P11CVec n → P11CVec n) (hw : DifferentiableOn ℂ w (KAM.actionNbhd E t))
    (hL : ∀ b ∈ KAM.actionNbhd E t, ‖fderiv ℂ w b‖ ≤ L) (hsmall : t*T*L ≤ D/2)
    (hdiv : ∀ b ∈ E, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      D ≤ ‖p11dotC k (w (KAM.realInclusion n b))‖)
    (hd : 0 < delta) (hdr : delta < rs)
    (h : P11CVec n → ℂ) (P0 : P11CVec n × P11CVec n → ℂ)
    (P1 : Fin n → P11CVec n × P11CVec n → ℂ)
    (hP0 : p11AngleClass rs (KAM.actionNbhd E t) P0)
    (hP1 : ∀ j, p11AngleClass rs (KAM.actionNbhd E t) (P1 j))
    (hpoly0 : ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t, KAM.Weighted.truncate T P0 z = P0 z)
    (hpoly1 : ∀ j, ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t,
      KAM.Weighted.truncate T (P1 j) z = P1 j z) :
    ∀ b ∈ KAM.actionNbhd E t, ∀ z : P11Phase n,
      KAM.Canonical.poissonBracket (fun y : P11Phase n => h b + ∑ i, w b i * y.2 i)
        (p11Affine (fun theta => p11Solve T w P0 theta b)
          (fun theta i => p11Solve T w (P1 i) theta b)) z =
        -(fderiv ℂ (fun theta => p11Solve T w P0 theta b) z.1 (w b) +
          ∑ i, fderiv ℂ (fun theta => p11Solve T w (P1 i) theta b) z.1 (w b) * z.2 i) ∧
      -(fderiv ℂ (fun theta => p11Solve T w P0 theta b) z.1 (w b) +
          ∑ i, fderiv ℂ (fun theta => p11Solve T w (P1 i) theta b) z.1 (w b) * z.2 i) =
        -((P0 (z.1, b) + ∑ i, P1 i (z.1, b) * z.2 i) -
          (p11AngleAverage P0 b + ∑ i, p11AngleAverage (P1 i) b * z.2 i)) :=
  hm_bracket_solve (by linarith) hT hD hw (hm_div_node ht hT hD w hw hL hsmall hdiv) h P0 P1
    hP0 hP1 hpoly0 hpoly1

/-- `bpP:p11a:homological-maximal`: from the source premises (the divisor bundle `D/2` on `B` is
constructed, not assumed), there are unique zero-average trigonometric polynomials `φ₀, φ₁ⱼ`
solving the equations, with the clauses (a)–(e), and `{N_b, φ} = -(P - ⟨P⟩)`. -/
theorem homological_maximal_node {n : ℕ} {E : Set (P11Vec n)} {t T D L rs delta M0 M1 : ℝ}
    (ht : 0 < t) (hT : 0 < T) (hD : 0 < D)
    (w : P11CVec n → P11CVec n) (hw : DifferentiableOn ℂ w (KAM.actionNbhd E t))
    (hL : ∀ b ∈ KAM.actionNbhd E t, ‖fderiv ℂ w b‖ ≤ L) (hsmall : t*T*L ≤ D/2)
    (hdiv : ∀ b ∈ E, ∀ k, k ≠ 0 → KAM.Fourier.modeSize k ≤ T →
      D ≤ ‖p11dotC k (w (KAM.realInclusion n b))‖)
    (hd : 0 < delta) (hdr : delta < rs)
    (h : P11CVec n → ℂ) (P0 : P11CVec n × P11CVec n → ℂ)
    (P1 : Fin n → P11CVec n × P11CVec n → ℂ)
    (hP0 : p11AngleClass rs (KAM.actionNbhd E t) P0)
    (hP1 : ∀ j, p11AngleClass rs (KAM.actionNbhd E t) (P1 j))
    (hpoly0 : ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t, KAM.Weighted.truncate T P0 z = P0 z)
    (hpoly1 : ∀ j, ∀ z ∈ Set.univ ×ˢ KAM.actionNbhd E t,
      KAM.Weighted.truncate T (P1 j) z = P1 j z)
    (hb0 : p11Bound (KAM.complexStrip n rs ×ˢ KAM.actionNbhd E t) P0 M0)
    (hb1 : ∀ j, p11Bound (KAM.complexStrip n rs ×ˢ KAM.actionNbhd E t) (P1 j) M1) :
    ∃ (phi0 : P11CVec n × P11CVec n → ℂ) (phi1 : Fin n → P11CVec n × P11CVec n → ℂ),
      HmMaxSolution E t T D rs delta M0 w P0 phi0 ∧
      (∀ j, HmMaxSolution E t T D rs delta M1 w (P1 j) (phi1 j)) ∧
      ∀ b ∈ KAM.actionNbhd E t, ∀ z : P11Phase n,
        KAM.Canonical.poissonBracket (fun y : P11Phase n => h b + ∑ i, w b i * y.2 i)
          (p11Affine (fun theta => phi0 (theta, b)) (fun theta i => phi1 i (theta, b))) z =
          -((P0 (z.1, b) + ∑ i, P1 i (z.1, b) * z.2 i) -
            (p11AngleAverage P0 b + ∑ i, p11AngleAverage (P1 i) b * z.2 i)) := by
  have hr : 0 < rs := by linarith
  have hdivB := hm_div_node ht hT hD w hw hL hsmall hdiv
  refine ⟨fun z => p11Solve T w P0 z.1 z.2, fun j z => p11Solve T w (P1 j) z.1 z.2, ?_, ?_, ?_⟩
  · exact hmMaxSolution_solve' hr hd hdr hT hD ht hw hdivB hP0 hpoly0 hb0
  · exact fun j => hmMaxSolution_solve' hr hd hdr hT hD ht hw hdivB (hP1 j) (hpoly1 j) (hb1 j)
  · intro b hbB z
    exact ((hm_bracket_solve hr hT hD hw hdivB h P0 P1 hP0 hP1 hpoly0 hpoly1) b hbB z).1.trans
      ((hm_bracket_solve hr hT hD hw hdivB h P0 P1 hP0 hP1 hpoly0 hpoly1) b hbB z).2

end Solve

end KAM.Planetary

end
