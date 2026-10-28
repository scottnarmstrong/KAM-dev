/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Continuation
public import KAM.ODE.Uniqueness
public import KAM.Planetary.PlanarTorsion.Setting

/-!
# Planar quartic torsion: energy estimate and existence on `[-1, 1]` (package T9)

Blueprint P, Part 11b (`bpP:p11b:fl-bd`).  For a `C¹` field `F` on `Phase 2` with the cubic bound
`‖F z‖ ≤ C ‖z‖³`, the squared slow length `u = |z|²` of a solution satisfies `u' ≤ 8 C u²`
(`p11cQ_energy_deriv`); a Riccati comparison (`p11cQ_riccati`) gives `u ≤ 2 u(0)` on `[0, T]`
once `8 C T u(0) ≤ 1/4`.  Continuation (`gen_confinement`) then produces the solution on `[-1, 1]`
from every initial point with `|z|² ≤ 1/(32 C)`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped Topology NNReal

namespace KAM.Planetary

open KAM KAM.ODE

/-- Riccati comparison `u' ≤ K u²` on `[0, T]`: `u ≤ 2 u 0` when `K T u 0 ≤ 1/4`. -/
theorem p11cQ_riccati {u u' : ℝ → ℝ} {K T : ℝ} (hK : 0 ≤ K) (hu0 : 0 < u 0)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt u (u' t) t) (hle : ∀ t ∈ Icc 0 T, u' t ≤ K * u t ^ 2)
    (hnn : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hKT : K * T * u 0 ≤ 1 / 4) :
    ∀ t ∈ Icc 0 T, u t ≤ 2 * u 0 := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  set ε := u 0 / 10 with hε
  have hε0 : 0 < ε := by positivity
  have hpos : ∀ s ∈ Icc 0 T, 0 < u s + ε := fun s hs => by linarith [hnn s hs]
  set g : ℝ → ℝ := fun s => -(u s + ε)⁻¹ - K * s with hg
  have hgd : ∀ s ∈ Icc 0 T, HasDerivAt g (u' s / (u s + ε) ^ 2 - K) s := by
    intro s hs
    have h1 := ((hd s hs).add_const ε)
    have h2 := (h1.inv (hpos s hs).ne')
    have h3 := (h2.neg).sub ((hasDerivAt_id s).const_mul K)
    refine h3.congr_deriv ?_
    simp only [mul_one]
    ring
  have hanti : AntitoneOn g (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) ?_ ?_ ?_
    · exact fun s hs => (hgd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hgd s ⟨hs.1.le, hs.2.le⟩).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le⟩
      rw [(hgd s hs').deriv]
      have hp := hpos s hs'
      have : u' s / (u s + ε) ^ 2 ≤ K * u s ^ 2 / (u s + ε) ^ 2 :=
        div_le_div_of_nonneg_right (hle s hs') (by positivity)
      have h2 : K * u s ^ 2 / (u s + ε) ^ 2 ≤ K := by
        rw [div_le_iff₀ (by positivity)]
        have : u s ^ 2 ≤ (u s + ε) ^ 2 := by nlinarith [hnn s hs']
        nlinarith
      linarith
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have key := hanti h0 ht ht.1
  simp only [hg, mul_zero, sub_zero] at key
  have hp := hpos t ht
  have hp0 := hpos 0 h0
  have hKt : K * t ≤ 1 / (4 * u 0) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hK, hu0]
  have h5 : (u t + ε)⁻¹ ≥ (u 0 + ε)⁻¹ - K * t := by linarith
  have h6 : (u 0 + ε)⁻¹ - K * t ≥ (21 / 10 * u 0)⁻¹ := by
    have : (u 0 + ε)⁻¹ = 10 / (11 * u 0) := by rw [hε]; field_simp; ring
    rw [this]
    have h7 : K * t ≤ 1 / (4 * u 0) := hKt
    have : (21 / 10 * u 0)⁻¹ = 10 / (21 * u 0) := by field_simp
    rw [this]
    have : 10 / (11 * u 0) - 1 / (4 * u 0) ≥ 10 / (21 * u 0) := by
      rw [ge_iff_le, div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀
        (by positivity) (by positivity)]
      nlinarith [hu0, mul_pos hu0 hu0, mul_pos (mul_pos hu0 hu0) hu0]
    linarith
  have h8 : (u t + ε)⁻¹ ≥ (21 / 10 * u 0)⁻¹ := by linarith
  have h9 := (inv_le_inv₀ (by positivity) hp).1 h8
  linarith

/-- The squared slow length `Σ (xᵢ² + yᵢ²)`. -/
def p11cQ_u (z : Phase 2) : ℝ := ∑ i, (z.1 i ^ 2 + z.2 i ^ 2)

theorem p11cQ_u_nonneg (z : Phase 2) : 0 ≤ p11cQ_u z :=
  Finset.sum_nonneg fun i _ => by positivity

theorem p11cQ_slowLength_sq (z : Phase 2) : p11c_slowLength z ^ 2 = p11cQ_u z :=
  Real.sq_sqrt (p11cQ_u_nonneg z)

theorem p11cQ_norm_sq_le (z : Phase 2) : ‖z‖ ^ 2 ≤ p11cQ_u z := by
  have h1 : ∀ i, z.1 i ^ 2 ≤ p11cQ_u z := fun i => by
    unfold p11cQ_u
    have h2 : z.1 i ^ 2 ≤ z.1 i ^ 2 + z.2 i ^ 2 := by nlinarith [sq_nonneg (z.2 i)]
    exact h2.trans (Finset.single_le_sum (f := fun i => z.1 i ^ 2 + z.2 i ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i))
  have h2 : ∀ i, z.2 i ^ 2 ≤ p11cQ_u z := fun i => by
    unfold p11cQ_u
    have h2 : z.2 i ^ 2 ≤ z.1 i ^ 2 + z.2 i ^ 2 := by nlinarith [sq_nonneg (z.1 i)]
    exact h2.trans (Finset.single_le_sum (f := fun i => z.1 i ^ 2 + z.2 i ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i))
  have hu := p11cQ_u_nonneg z
  have hn : ‖z‖ ≤ Real.sqrt (p11cQ_u z) := by
    refine max_le (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.2 fun i => ?_)
      (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.2 fun i => ?_)
    · rw [Real.norm_eq_abs]; exact Real.abs_le_sqrt (h1 i)
    · rw [Real.norm_eq_abs]; exact Real.abs_le_sqrt (h2 i)
  calc ‖z‖ ^ 2 ≤ Real.sqrt (p11cQ_u z) ^ 2 := by gcongr
    _ = p11cQ_u z := Real.sq_sqrt hu

theorem p11cQ_u_le (z : Phase 2) : p11cQ_u z ≤ 4 * ‖z‖ ^ 2 := by
  unfold p11cQ_u
  have h1 : ∀ i, |z.1 i| ≤ ‖z‖ := fun i =>
    (norm_le_pi_norm (z.1) i).trans (norm_fst_le z)
  have h2 : ∀ i, |z.2 i| ≤ ‖z‖ := fun i =>
    (norm_le_pi_norm (z.2) i).trans (norm_snd_le z)
  have h3 : ∀ i, z.1 i ^ 2 + z.2 i ^ 2 ≤ 2 * ‖z‖ ^ 2 := fun i => by
    have a := sq_le_sq' (neg_le_of_abs_le (h1 i)) (le_of_abs_le (h1 i))
    have b := sq_le_sq' (neg_le_of_abs_le (h2 i)) (le_of_abs_le (h2 i))
    linarith
  calc ∑ i, (z.1 i ^ 2 + z.2 i ^ 2) ≤ ∑ _i : Fin 2, 2 * ‖z‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => h3 i
    _ = 4 * ‖z‖ ^ 2 := by simp; ring

/-- Derivative of the squared slow length along a solution, bounded by `8 C u²`. -/
theorem p11cQ_energy_deriv {F : Phase 2 → Phase 2} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ z, ‖F z‖ ≤ C * ‖z‖ ^ 3) {y : ℝ → Phase 2} {t : ℝ}
    (h : HasDerivAt y (F (y t)) t) :
    HasDerivAt (fun s => p11cQ_u (y s))
      (2 * ∑ i, ((y t).1 i * (F (y t)).1 i + (y t).2 i * (F (y t)).2 i)) t ∧
    2 * ∑ i, ((y t).1 i * (F (y t)).1 i + (y t).2 i * (F (y t)).2 i) ≤
      8 * C * p11cQ_u (y t) ^ 2 := by
  have hc1 : ∀ i, HasDerivAt (fun s => (y s).1 i) ((F (y t)).1 i) t := fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
      (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).hasFDerivAt.comp_hasDerivAt t h
  have hc2 : ∀ i, HasDerivAt (fun s => (y s).2 i) ((F (y t)).2 i) t := fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).hasFDerivAt.comp_hasDerivAt t h
  refine ⟨?_, ?_⟩
  · have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      ((hc1 i).pow 2).add ((hc2 i).pow 2)
    unfold p11cQ_u
    convert this using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Nat.cast_ofNat]
    ring
  · have hz := norm_nonneg (y t)
    have h1 : ∀ i, |(y t).1 i| ≤ ‖y t‖ := fun i =>
      (norm_le_pi_norm ((y t).1) i).trans (norm_fst_le _)
    have h2 : ∀ i, |(y t).2 i| ≤ ‖y t‖ := fun i =>
      (norm_le_pi_norm ((y t).2) i).trans (norm_snd_le _)
    have g1 : ∀ i, |(F (y t)).1 i| ≤ ‖F (y t)‖ := fun i =>
      (norm_le_pi_norm ((F (y t)).1) i).trans (norm_fst_le _)
    have g2 : ∀ i, |(F (y t)).2 i| ≤ ‖F (y t)‖ := fun i =>
      (norm_le_pi_norm ((F (y t)).2) i).trans (norm_snd_le _)
    have hb : ∀ i, (y t).1 i * (F (y t)).1 i + (y t).2 i * (F (y t)).2 i ≤
        2 * (‖y t‖ * ‖F (y t)‖) := fun i => by
      have a : (y t).1 i * (F (y t)).1 i ≤ ‖y t‖ * ‖F (y t)‖ :=
        (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul (h1 i) (g1 i) (abs_nonneg _) hz)
      have b : (y t).2 i * (F (y t)).2 i ≤ ‖y t‖ * ‖F (y t)‖ :=
        (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul (h2 i) (g2 i) (abs_nonneg _) hz)
      linarith
    have hs : ∑ i, ((y t).1 i * (F (y t)).1 i + (y t).2 i * (F (y t)).2 i) ≤
        ∑ _i : Fin 2, 2 * (‖y t‖ * ‖F (y t)‖) := Finset.sum_le_sum fun i _ => hb i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] at hs
    have hFy := hF (y t)
    have hu2 : ‖y t‖ ^ 2 ≤ p11cQ_u (y t) := p11cQ_norm_sq_le _
    have hu4 : ‖y t‖ ^ 4 ≤ p11cQ_u (y t) ^ 2 := by
      calc ‖y t‖ ^ 4 = (‖y t‖ ^ 2) ^ 2 := by ring
        _ ≤ _ := by gcongr
    have : ‖y t‖ * ‖F (y t)‖ ≤ C * ‖y t‖ ^ 4 := by
      calc ‖y t‖ * ‖F (y t)‖ ≤ ‖y t‖ * (C * ‖y t‖ ^ 3) := by gcongr
        _ = C * ‖y t‖ ^ 4 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hu4 hC]

/-- Forward energy estimate, positive initial energy. -/
theorem p11cQ_forward_pos {F : Phase 2 → Phase 2} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ z, ‖F z‖ ≤ C * ‖z‖ ^ 3) {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {y : ℝ → Phase 2} (hy : IsSolutionIn F univ J y) {t : ℝ} (ht : t ∈ J) (ht0 : 0 ≤ t)
    (hu0 : 0 < p11cQ_u (y 0)) (hKt : 8 * C * t * p11cQ_u (y 0) ≤ 1 / 4) :
    p11cQ_u (y t) ≤ 2 * p11cQ_u (y 0) := by
  have hsub : Icc 0 t ⊆ J := hJ.out h0 ht
  have hd : ∀ s ∈ Icc 0 t, HasDerivAt (fun s => p11cQ_u (y s))
      (2 * ∑ i, ((y s).1 i * (F (y s)).1 i + (y s).2 i * (F (y s)).2 i)) s := fun s hs =>
    (p11cQ_energy_deriv hC hF (hy s (hsub hs)).2).1
  exact p11cQ_riccati (u := fun s => p11cQ_u (y s)) (by positivity) hu0 hd
    (fun s hs => (p11cQ_energy_deriv hC hF (hy s (hsub hs)).2).2)
    (fun s _ => p11cQ_u_nonneg _) (by simpa [mul_assoc] using hKt) t ⟨ht0, le_rfl⟩

/-- Forward energy estimate, including the zero solution. -/
theorem p11cQ_forward {F : Phase 2 → Phase 2} {C : ℝ} (hC : 0 ≤ C)
    (hF1 : ContDiffOn ℝ 1 F univ) (hF : ∀ z, ‖F z‖ ≤ C * ‖z‖ ^ 3) {J : Set ℝ}
    (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {y : ℝ → Phase 2} (hy : IsSolutionIn F univ J y)
    {t : ℝ} (ht : t ∈ J) (ht0 : 0 ≤ t) (hKt : 8 * C * t * p11cQ_u (y 0) ≤ 1 / 4) :
    p11cQ_u (y t) ≤ 2 * p11cQ_u (y 0) := by
  rcases (p11cQ_u_nonneg (y 0)).eq_or_lt with h | h
  · have hy0 : y 0 = 0 := by
      have h1 : ‖y 0‖ ^ 2 ≤ 0 := by have := p11cQ_norm_sq_le (y 0); linarith
      exact norm_eq_zero.1 (by nlinarith [norm_nonneg (y 0)])
    have hF0 : F 0 = 0 := by simpa using hF 0
    have hz : IsSolutionIn F univ J (fun _ => (0 : Phase 2)) := fun s _ =>
      ⟨mem_univ _, by simpa [hF0] using hasDerivAt_const s (0 : Phase 2)⟩
    have := gen_uniqueness isOpen_univ hF1 hJ h0 hy hz (by simpa using hy0) ht
    rw [this, ← h]
    simp [p11cQ_u]
  · exact p11cQ_forward_pos hC hF hJ h0 hy ht ht0 h hKt

/-- Two-sided energy estimate. -/
theorem p11cQ_two_sided {F : Phase 2 → Phase 2} {C τ : ℝ} (hC : 0 ≤ C)
    (hF1 : ContDiffOn ℝ 1 F univ) (hF : ∀ z, ‖F z‖ ≤ C * ‖z‖ ^ 3) {J : Set ℝ}
    (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {y : ℝ → Phase 2} (hy : IsSolutionIn F univ J y)
    {t : ℝ} (ht : t ∈ J) (htτ : |t| ≤ τ) (hKt : 8 * C * τ * p11cQ_u (y 0) ≤ 1 / 4) :
    p11cQ_u (y t) ≤ 2 * p11cQ_u (y 0) := by
  have hu := p11cQ_u_nonneg (y 0)
  rcases le_total 0 t with h | h
  · exact p11cQ_forward hC hF1 hF hJ h0 hy ht h
      (le_trans (by gcongr; rwa [abs_of_nonneg h] at htτ) hKt)
  · have hJ' : (Neg.neg ⁻¹' J).OrdConnected := ⟨fun a ha b hb c hc => by
      have := hJ.out hb ha (show -c ∈ Icc (-b) (-a) from
        ⟨by linarith [hc.2], by linarith [hc.1]⟩)
      simpa using this⟩
    have hy' := gen_symmetry_neg hy
    have hτ : -t ≤ τ := by rw [abs_of_nonpos h] at htτ; exact htτ
    have hK' : 8 * C * (-t) * p11cQ_u ((fun s => y (-s)) 0) ≤ 1 / 4 := by
      simp only [neg_zero]
      exact le_trans (by gcongr) hKt
    have := p11cQ_forward hC (hF1.neg) (fun z => by simpa using hF z) hJ' (by simpa using h0)
      hy' (t := -t) (by simpa using ht) (by linarith) hK'
    simpa using this

/-- Existence on `[-1, 1]`, with the energy bound, for small initial slow length. -/
theorem p11cQ_exists {F : Phase 2 → Phase 2} {C : ℝ} (hC : 0 < C)
    (hF1 : ContDiffOn ℝ 1 F univ) (hF : ∀ z, ‖F z‖ ≤ C * ‖z‖ ^ 3) {z₀ : Phase 2}
    (h : 32 * C * p11cQ_u z₀ ≤ 1) :
    ∃ g : ℝ → Phase 2, IsSolutionIn F univ (Icc (-1) 1) g ∧ g 0 = z₀ ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, p11cQ_u (g t) ≤ 2 * p11cQ_u z₀ := by
  set ρ := Real.sqrt (2 * p11cQ_u z₀) with hρ
  obtain ⟨δ, M, L, hU, -, -⟩ := gen_uniform_compact (E := Phase 2) isOpen_univ hF1
    (isCompact_closedBall (0 : Phase 2) ρ) (subset_univ _)
  have hconf : ∀ (J : Set ℝ) (y : ℝ → Phase 2), IsOpen J → J.OrdConnected → (0 : ℝ) ∈ J →
      y 0 = z₀ → IsSolutionIn F univ J y → ∀ t ∈ J, |t| ≤ 1 → y t ∈ closedBall (0 : Phase 2) ρ := by
    intro J y _ hJ h0 hy0 hy t ht htτ
    have := p11cQ_two_sided hC.le hF1 hF hJ h0 hy ht htτ (τ := 1) (by rw [hy0]; linarith)
    rw [hy0] at this
    rw [mem_closedBall_iff_norm, sub_zero]
    exact Real.le_sqrt_of_sq_le ((p11cQ_norm_sq_le _).trans this)
  obtain ⟨Tm, Tp, z, hz, -, -, hsol, -, -⟩ := gen_confinement isOpen_univ hF1 (mem_univ z₀)
    one_pos hU hconf
  refine ⟨z, hsol, hz.init, fun t ht => ?_⟩
  have := p11cQ_two_sided hC.le hF1 hF (ordConnected_Icc) (J := Icc (-1 : ℝ) 1)
    (by simp) hsol ht (abs_le.2 ht) (τ := 1) (by rw [hz.init]; linarith)
  rwa [hz.init] at this

end KAM.Planetary

end
