/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Planetary.Poincare.Tube
public import KAM.Frozen.Planetary.Defs.CircularPoint
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Frozen.Planetary.Defs.Assemble

/-!
# Forward tube (P Part 11a, `bpP:p11:forward-tube`)

For physical data `(G, m0, m, a)` and `ζ > 0` there is `δ > 0`, at most a quarter of every
`Λ_i^* = m_i √(G m0 a_i)`, such that every `w` with `|Λ_i - Λ_i^*| ≤ δ` and `Γ_i ≤ δ` lies in the
Poincaré product domain with `‖Ψ^{(n)}(w) - circ(λ/2π)‖ < ζ`.

The statement is proved for raw physical data (`forward_tube_core`); the `P11Physical` packaging
`forward_tube` and `p11PhysicalDelta` of the design is a one-line consequence, to be added where
`P11Physical` is defined.  The proof is the compactness argument of the circular torus: the torus
is compact, `Ψ - circ` vanishes on it, and both are `2π`-periodic in the angles.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM KAM.Kepler

section ForwardTube

variable {n : ℕ}

private theorem ft_cos_fract (x : ℝ) : Real.cos (2 * π * Int.fract x) = Real.cos (2 * π * x) := by
  conv_rhs => rw [← Int.fract_add_floor x]
  rw [mul_add, show 2 * π * ((⌊x⌋ : ℤ) : ℝ) = (⌊x⌋ : ℤ) * (2 * π) by ring]
  exact (Real.cos_add_int_mul_two_pi _ _).symm

private theorem ft_sin_fract (x : ℝ) : Real.sin (2 * π * Int.fract x) = Real.sin (2 * π * x) := by
  conv_rhs => rw [← Int.fract_add_floor x]
  rw [mul_add, show 2 * π * ((⌊x⌋ : ℤ) : ℝ) = (⌊x⌋ : ℤ) * (2 * π) by ring]
  exact (Real.sin_add_int_mul_two_pi _ _).symm

private theorem ft_circularPoint_fract (G m0 : ℝ) (m a : Fin n → ℝ) (φ : Fin n → ℝ) :
    circularPoint G m0 m a (fun i => Int.fract (φ i)) = circularPoint G m0 m a φ := by
  simp only [circularPoint, ft_cos_fract, ft_sin_fract]

private theorem ft_continuous_circularPoint (G m0 : ℝ) (m a : Fin n → ℝ) :
    Continuous (circularPoint G m0 m a) := by
  have h1 : ∀ (j : Fin n) (l : Fin 2), Continuous fun φ : Fin n → ℝ =>
      a j * (![Real.cos (2 * π * φ j), Real.sin (2 * π * φ j)] : Fin 2 → ℝ) l := fun j l => by
    fin_cases l <;> simp <;> fun_prop
  have h2 : ∀ (j : Fin n) (l : Fin 2), Continuous fun φ : Fin n → ℝ =>
      m j * √(G * m0 / a j) *
        (![-Real.sin (2 * π * φ j), Real.cos (2 * π * φ j)] : Fin 2 → ℝ) l := fun j l => by
    fin_cases l <;> simp <;> fun_prop
  exact Continuous.prodMk (continuous_pi fun k => h1 _ _) (continuous_pi fun k => h2 _ _)

private theorem ft_continuous_assemble (I : Fin n → ℝ) :
    Continuous fun φ : Fin n → ℝ =>
      (assemble I (fun i => 2 * π * φ i) (0 : Fin n → ℝ) (0 : Fin n → ℝ) : Phase (n + n)) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [Fin.append_left] <;> fun_prop
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [Fin.append_left] <;> fun_prop

/-- A positive lower bound for finitely many positive numbers. -/
private theorem ft_exists_lower (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ x i := by
  refine ⟨1 / (1 + ∑ i, 1 / x i), ?_, fun i => ?_⟩
  · have : 0 ≤ ∑ i, 1 / x i := Finset.sum_nonneg fun i _ => (one_div_pos.2 (hx i)).le
    positivity
  · have h1 : 1 / x i ≤ ∑ j, 1 / x j :=
      Finset.single_le_sum (f := fun j => 1 / x j) (fun j _ => (one_div_pos.2 (hx j)).le)
        (Finset.mem_univ i)
    rw [div_le_iff₀ (by linarith [h1, one_div_pos.2 (hx i)])]
    have := hx i
    rw [div_le_iff₀ this] at h1
    nlinarith

/-- `bpP:p11:forward-tube`, for raw physical data. -/
theorem forward_tube_core {G m0 : ℝ} {m a : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) (ha : ∀ i, 0 < a i) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i, δ ≤ m i * Real.sqrt (G * m0 * a i) / 4) ∧
      ∀ w : Phase (n + n),
        (∀ i : Fin n, |w.2 (Fin.castAdd n i) - m i * Real.sqrt (G * m0 * a i)| ≤ δ) →
        (∀ i, poincareGamma (planetBlock w i) ≤ δ) →
        w ∈ poincareProdDom n ∧
          ‖poincareProd m (G * m0) w -
            circularPoint G m0 m a (fun i => w.1 (Fin.castAdd n i) / (2 * Real.pi))‖ < ζ := by
  have hκ : 0 < G * m0 := mul_pos hG hm0
  set Λ₀ : Fin n → ℝ := fun i => m i * √(G * m0 * a i) with hΛ₀def
  have hΛ₀ : ∀ i, 0 < Λ₀ i := fun i => by
    have := ha i; have := hm i; simp only [hΛ₀def]; positivity
  -- the compact torus and the open set where `Ψ - circ` is small
  let K : Set (Phase (n + n)) :=
    (fun φ : Fin n → ℝ => (assemble Λ₀ (fun i => 2 * π * φ i) (0 : Fin n → ℝ) (0 : Fin n → ℝ) :
      Phase (n + n))) '' Set.pi univ fun _ => Icc (0 : ℝ) 1
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (ft_continuous_assemble Λ₀)
  let f : Phase (n + n) → Phase (n * 2) := fun w =>
    poincareProd m (G * m0) w -
      circularPoint G m0 m a (fun i => w.1 (Fin.castAdd n i) / (2 * π))
  have hf : ContinuousOn f (poincareProdDom n) := by
    refine ((analyticOnNhd_poincareProd hm hκ).continuousOn).sub ?_
    refine (ft_continuous_circularPoint G m0 m a).comp_continuousOn ?_
    exact (continuous_pi fun i => ((continuous_apply (Fin.castAdd n i)).comp
      continuous_fst).div_const _).continuousOn
  have hUo : IsOpen (poincareProdDom n ∩ f ⁻¹' Metric.ball 0 ζ) :=
    hf.isOpen_inter_preimage (isOpen_poincareProdDom n) Metric.isOpen_ball
  have hKU : K ⊆ poincareProdDom n ∩ f ⁻¹' Metric.ball 0 ζ := by
    rintro _ ⟨φ, -, rfl⟩
    have hw : (assemble Λ₀ (fun i => 2 * π * φ i) (0 : Fin n → ℝ) (0 : Fin n → ℝ) :
        Phase (n + n)) ∈ poincareProdDom n := by
      intro i
      have := hΛ₀ i
      refine ⟨by simpa [assemble, planetBlock, fast, slow, Fin.append_left] using this, ?_⟩
      simpa [poincareGamma, assemble, planetBlock, fast, slow, Fin.append_left,
        Fin.append_right] using this
    refine ⟨hw, ?_⟩
    have hcirc := circularPoint_eq_poincareProd hG hm0 hm ha φ
    have hφ : (fun i : Fin n => (assemble Λ₀ (fun i => 2 * π * φ i) (0 : Fin n → ℝ)
        (0 : Fin n → ℝ) : Phase (n + n)).1 (Fin.castAdd n i) / (2 * π)) = φ := by
      funext i
      simp [assemble, Fin.append_left]
    simp only [mem_preimage, f, hφ, Metric.mem_ball, dist_zero_right]
    rw [hcirc, sub_self, norm_zero]
    exact hζ
  obtain ⟨r, hr, hsub⟩ := hK.exists_cthickening_subset_open hUo hKU
  obtain ⟨c, hc, hcle⟩ := ft_exists_lower (fun i => Λ₀ i / 4) fun i => by
    have := hΛ₀ i; positivity
  refine ⟨min c (min r (r ^ 2 / 2)), lt_min hc (lt_min hr (by positivity)), fun i => ?_,
    fun w hΛ hΓ => ?_⟩
  · exact (min_le_left _ _).trans (hcle i)
  have hδc : min c (min r (r ^ 2 / 2)) ≤ c := min_le_left _ _
  have hδr : min c (min r (r ^ 2 / 2)) ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hδr2 : min c (min r (r ^ 2 / 2)) ≤ r ^ 2 / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  set δ := min c (min r (r ^ 2 / 2)) with hδ
  have hwdom : w ∈ poincareProdDom n := by
    intro i
    have h1 := (abs_le.1 (hΛ i)).1
    have h2 := hcle i
    have h3 := hΓ i
    have := hΛ₀ i
    refine ⟨?_, ?_⟩
    · simp only [planetBlock]
      simp only [fast] at h1 ⊢
      simp only [hΛ₀def] at h2 this
      show 0 < w.2 (Fin.castAdd n i)
      linarith
    · simp only [planetBlock, fast] at h3 ⊢
      simp only [hΛ₀def] at h2 this
      show poincareGamma (planetBlock w i) < w.2 (Fin.castAdd n i)
      simp only [planetBlock, fast]
      linarith
  refine ⟨hwdom, ?_⟩
  -- reduce the angles modulo `2π`
  let k : Fin n → ℤ := fun i => -⌊w.1 (Fin.castAdd n i) / (2 * π)⌋
  obtain ⟨-, hΨ⟩ := poincareProd_lattice hm hκ hwdom k
  have hang : ∀ i, (w + fastShift (a := n) (b := n) k).1 (Fin.castAdd n i) / (2 * π) =
      Int.fract (w.1 (Fin.castAdd n i) / (2 * π)) := by
    intro i
    have h2 : (2 * π) ≠ 0 := by positivity
    simp only [k, Prod.fst_add, Pi.add_apply, fastShift, Fin.append_left, Int.fract]
    field_simp
    push_cast
    ring
  have hcirc : circularPoint G m0 m a (fun i => (w + fastShift (a := n) (b := n) k).1
      (Fin.castAdd n i) / (2 * π)) =
      circularPoint G m0 m a (fun i => w.1 (Fin.castAdd n i) / (2 * π)) := by
    rw [← ft_circularPoint_fract G m0 m a (fun i => w.1 (Fin.castAdd n i) / (2 * π))]
    congr 1
    funext i
    exact hang i
  let z : Phase (n + n) := assemble Λ₀
    (fun i => 2 * π * Int.fract (w.1 (Fin.castAdd n i) / (2 * π))) (0 : Fin n → ℝ) (0 : Fin n → ℝ)
  have hzK : z ∈ K := ⟨fun i => Int.fract (w.1 (Fin.castAdd n i) / (2 * π)),
    fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩
  have hdist : dist (w + fastShift (a := n) (b := n) k) z ≤ r := by
    rw [dist_eq_norm, Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg hr.le).2 fun j => ?_
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have := hang i
        have h2 : (2 * π) ≠ 0 := by positivity
        simp only [Prod.fst_sub, Pi.sub_apply, z, assemble, Fin.append_left, Real.norm_eq_abs]
        rw [show (w + fastShift (a := n) (b := n) k).1 (Fin.castAdd n i) =
          2 * π * Int.fract (w.1 (Fin.castAdd n i) / (2 * π)) by
            rw [← hang i]; field_simp]
        simpa using hr.le
      · have h3 : (w.1 (Fin.natAdd n i) ^ 2 + w.2 (Fin.natAdd n i) ^ 2) / 2 ≤ δ := hΓ i
        have hs : (w.1 (Fin.natAdd n i)) ^ 2 ≤ r ^ 2 := by
          nlinarith [sq_nonneg (w.2 (Fin.natAdd n i))]
        have habs := abs_le.2 (abs_le_of_sq_le_sq' hs hr.le)
        simpa [z, assemble, Fin.append_right, fastShift] using habs
    · refine (pi_norm_le_iff_of_nonneg hr.le).2 fun j => ?_
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Prod.snd_sub, Pi.sub_apply, z, assemble, Fin.append_left, Real.norm_eq_abs,
          Prod.snd_add, Pi.add_apply, fastShift]
        simpa [hΛ₀def] using (hΛ i).trans hδr
      · have h3 : (w.1 (Fin.natAdd n i) ^ 2 + w.2 (Fin.natAdd n i) ^ 2) / 2 ≤ δ := hΓ i
        have hs : (w.2 (Fin.natAdd n i)) ^ 2 ≤ r ^ 2 := by
          nlinarith [sq_nonneg (w.1 (Fin.natAdd n i))]
        have habs := abs_le.2 (abs_le_of_sq_le_sq' hs hr.le)
        simpa [z, assemble, Fin.append_right, fastShift] using habs
  have hmem := hsub (mem_cthickening_of_dist_le _ z r K hzK hdist)
  have h := hmem.2
  simp only [mem_preimage, f, Metric.mem_ball, dist_zero_right] at h
  rw [hΨ, hcirc] at h
  exact h

end ForwardTube

end KAM.Planetary

end
