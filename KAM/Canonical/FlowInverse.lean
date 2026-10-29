/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.FlowRegular
public import KAM.Strip.RealRestriction

/-!
# The canonical flow: inverse, derivative bound and reality

Blueprint-N Part 5, node `bpN:p5:flow`, parts (c) and (e).

* `KAM.Canonical.flow_c`: for `z ∈ Ω¹` the time-one map and its inverse `X^{-1}` stay in `Ω^{1/2}`
  and invert each other, and `ν(DX^t(z) v - v) ≤ 2 ε ν(v)` for `|t| ≤ 1`.
* `KAM.Canonical.flow_e`: if `F` preserves the real points of `Ω` then so does the flow.

Proof of (c). The curves `s ↦ X^{1+s} z` and `s ↦ X^{s-1} z` are solutions through `X¹ z`, resp.
`X^{-1} z`, so uniqueness (`flow_a`) identifies them with the flow of the new base point. The
derivative bound is the one-variable Cauchy estimate (`gauge_fderiv_le`) for `X^t - id`, which
has gauge size `≤ ε` on the gauge ball of radius `1/2` about `z ∈ Ω¹`.

Proof of (e). The Picard iterates `y_k(t, x)` of `FlowPicard` keep real points real (the integral
of a real-valued function lies in the closed real subspace `ker Im`), and converge to the flow
(`picard_flow_estimate`), so the flow is real.
-/

@[expose] public noncomputable section

open Set Metric
open scoped Interval

namespace KAM.Canonical

section FlowInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-! ### The Cauchy estimate in a gauge -/

omit [FiniteDimensional ℂ E] in
/-- One-variable Cauchy estimate in a gauge: if `G` is differentiable with gauge size `≤ ε` on the
gauge ball of radius `1/2` about `z`, then `ν(DG(z) v) ≤ 2 ε ν(v)`. -/
theorem gauge_fderiv_le {W : E ≃L[ℂ] E} {G : E → E} {z : E} {ε : ℝ}
    (hdiff : ∀ w, ‖W (w - z)‖ ≤ 1 / 2 → DifferentiableAt ℂ G w)
    (hb : ∀ w, ‖W (w - z)‖ ≤ 1 / 2 → ‖W (G w)‖ ≤ ε) (v : E) :
    ‖W (fderiv ℂ G z v)‖ ≤ 2 * ε * ‖W v‖ := by
  by_cases hv : v = 0
  · subst hv
    simp
  have hN : 0 < ‖W v‖ := norm_pos_iff.2 (by simpa using hv)
  set N := ‖W v‖ with hNdef
  set R : ℝ := 1 / (2 * N) with hR
  have hR0 : 0 < R := by positivity
  have hline : ∀ s : ℂ, ‖W (z + s • v - z)‖ = ‖s‖ * N := by
    intro s
    rw [add_sub_cancel_left, map_smul, norm_smul]
  have hmem : ∀ s : ℂ, ‖s‖ ≤ R → ‖W (z + s • v - z)‖ ≤ 1 / 2 := by
    intro s hs
    rw [hline]
    calc ‖s‖ * N ≤ R * N := mul_le_mul_of_nonneg_right hs hN.le
      _ = 1 / 2 := by rw [hR]; field_simp
  have hline' : ∀ s : ℂ, HasDerivAt (fun s : ℂ => z + s • v) v s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const v).const_add z
  set h : ℂ → E := fun s => W (G (z + s • v)) with hh
  have hhd : ∀ s : ℂ, ‖s‖ ≤ R → DifferentiableAt ℂ h s := by
    intro s hs
    have h1 : DifferentiableAt ℂ G (z + s • v) := hdiff _ (hmem s hs)
    exact W.toContinuousLinearMap.differentiableAt.comp s (h1.comp s (hline' s).differentiableAt)
  have hdc : DiffContOnCl ℂ h (ball (0 : ℂ) R) := by
    refine DifferentiableOn.diffContOnCl fun s hs => ?_
    rw [closure_ball (0 : ℂ) hR0.ne'] at hs
    exact (hhd s (by simpa using hs)).differentiableWithinAt
  have hsph : ∀ s ∈ sphere (0 : ℂ) R, ‖h s‖ ≤ ε := by
    intro s hs
    have : ‖s‖ = R := by simpa using hs
    exact hb _ (hmem s this.le)
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR0 hdc hsph
  have hGd : HasFDerivAt G (fderiv ℂ G z) z := by
    simpa using (hdiff z (by simp)).hasFDerivAt
  have hder : HasDerivAt h (W (fderiv ℂ G z v)) 0 := by
    have h1 : HasFDerivAt G (fderiv ℂ G z) (z + (0 : ℂ) • v) := by simpa using hGd
    have h2 := h1.comp_hasDerivAt (0 : ℂ) (hline' 0)
    exact W.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℂ) h2
  rw [hder.deriv] at hcau
  calc ‖W (fderiv ℂ G z v)‖ ≤ ε / R := hcau
    _ = 2 * ε * N := by rw [hR]; field_simp

/-! ### Part (c) -/

/-- The flow of `z ∈ Ω¹` at time `±1` lies in `Ω^{1/2}`. -/
private theorem flow_mem_half {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) {z : E} (hz : z ∈ gaugeInterior W Ω 1) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : flow F Ω t z ∈ gaugeInterior W Ω (1 / 2) := by
  have hz' : z ∈ gaugeInterior W Ω (1 / 2) := gaugeInterior_mono W (by norm_num) hz
  obtain ⟨-, -, -, hdisp⟩ := flow_a h hz'
  exact ball_subset_gaugeInterior W hz ((hdisp t ht).trans (by
    have := abs_mul_le_half h ht
    linarith))

/-- Going along the flow for time `a`, then back for time `-a`, lands at the start (`a = ±1`). -/
private theorem flow_back {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) {z : E} (hz : z ∈ gaugeInterior W Ω 1) {a : ℝ}
    (ha : a = 1 ∨ a = -1) : flow F Ω (-a) (flow F Ω a z) = z := by
  have hz' : z ∈ gaugeInterior W Ω (1 / 2) := gaugeInterior_mono W (by norm_num) hz
  have haI : a ∈ Icc (-1 : ℝ) 1 := by rcases ha with rfl | rfl <;> norm_num
  have hx := flow_mem_half h hz haI
  obtain ⟨h0, hsol, -, -⟩ := flow_a h hz'
  obtain ⟨-, -, huniq, -⟩ := flow_a h hx
  have hshift := (KAM.ODE.gen_symmetry hsol).1 a
  rcases ha with rfl | rfl
  · have hJ := hshift.mono (J' := Icc (-1 : ℝ) 0) (by
      intro s hs
      simp only [mem_preimage, mem_Icc] at hs ⊢
      constructor <;> linarith [hs.1, hs.2])
    have := huniq (Icc (-1 : ℝ) 0) ordConnected_Icc ⟨by norm_num, by norm_num⟩
      (fun s => flow F Ω (s + 1) z) hJ (by simp) (-1) ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩⟩
    simpa [h0] using this.symm
  · have hJ := hshift.mono (J' := Icc (0 : ℝ) 1) (by
      intro s hs
      simp only [mem_preimage, mem_Icc] at hs ⊢
      constructor <;> linarith [hs.1, hs.2])
    have := huniq (Icc (0 : ℝ) 1) ordConnected_Icc ⟨le_rfl, by norm_num⟩
      (fun s => flow F Ω (s + -1) z) hJ (by simp) 1 ⟨⟨by norm_num, le_rfl⟩, ⟨by norm_num, le_rfl⟩⟩
    simpa [h0] using this.symm

/-- (c) inverse and derivative bound `|DX^t - 1|_ν ≤ 2ε` at `z ∈ Ω¹`. -/
theorem flow_c {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ} (h : SmallField W Ω F ε) {z : E}
    (hz : z ∈ gaugeInterior W Ω 1) :
    flow F Ω 1 z ∈ gaugeInterior W Ω (1 / 2) ∧ flow F Ω (-1) (flow F Ω 1 z) = z ∧
    flow F Ω (-1) z ∈ gaugeInterior W Ω (1 / 2) ∧ flow F Ω 1 (flow F Ω (-1) z) = z ∧
    ∀ t ∈ Icc (-1 : ℝ) 1, ∀ v : E, ‖W (fderiv ℂ (flow F Ω t) z v - v)‖ ≤ 2 * ε * ‖W v‖ := by
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1' : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨flow_mem_half h hz h1, flow_back h hz (Or.inl rfl), flow_mem_half h hz h1',
    ?_, ?_⟩
  · simpa using flow_back h hz (Or.inr rfl)
  · intro t ht v
    have hball : ∀ w, ‖W (w - z)‖ ≤ 1 / 2 → w ∈ gaugeInterior W Ω (1 / 2) := fun w hw =>
      ball_subset_gaugeInterior W hz (by linarith)
    have hdiffAt : ∀ w, ‖W (w - z)‖ ≤ 1 / 2 → DifferentiableAt ℂ (flow F Ω t) w := fun w hw =>
      ((flow_b h).2.1 t ht).differentiableAt
        ((isOpen_gaugeInterior h.isOpen W (1 / 2)).mem_nhds (hball w hw))
    have key := gauge_fderiv_le (W := W) (G := fun w => flow F Ω t w - w) (z := z) (ε := ε)
      (fun w hw => (hdiffAt w hw).sub differentiableAt_id)
      (fun w hw => by
        obtain ⟨-, -, -, hdisp⟩ := flow_a h (hball w hw)
        have := hdisp t ht
        have hle : |t| * ε ≤ ε := by
          have : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
          nlinarith [h.eps_nonneg]
        exact this.trans hle) v
    have hfd : fderiv ℂ (fun w => flow F Ω t w - w) z v = fderiv ℂ (flow F Ω t) z v - v := by
      have := ((hdiffAt z (by simp)).hasFDerivAt.sub (hasFDerivAt_id z)).fderiv
      rw [show (fun w => flow F Ω t w - w) = flow F Ω t - id from rfl, this]
      simp
    rwa [hfd] at key

end FlowInverse

/-! ### Part (e): reality -/

section FlowReal

variable {n : ℕ}

/-- The componentwise imaginary part `ℂⁿ → ℝⁿ`, as a real-linear map. -/
def imCLM (n : ℕ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => Complex.imCLM.comp (ContinuousLinearMap.proj i)

/-- The componentwise imaginary part `ℂⁿ × ℂⁿ → ℝⁿ × ℝⁿ`; its kernel is `ℝᴺ`. -/
def imCLM₂ (n : ℕ) : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (imCLM n).prodMap (imCLM n)

theorem imCLM₂_apply (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    imCLM₂ n z = (fun i => (z.1 i).im, fun i => (z.2 i).im) := rfl

/-- The real points `range (realInclusion₂ n)` are the kernel of `imCLM₂`. -/
theorem mem_range_realInclusion₂_iff (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    z ∈ range (KAM.realInclusion₂ n) ↔ imCLM₂ n z = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    ext i <;> simp [imCLM₂_apply]
  · intro hz
    have h1 : ∀ i, (z.1 i).im = 0 := fun i => congrFun (congrArg Prod.fst hz) i
    have h2 : ∀ i, (z.2 i).im = 0 := fun i => congrFun (congrArg Prod.snd hz) i
    refine ⟨((fun i => (z.1 i).re, fun i => (z.2 i).re) :
      (Fin n → ℝ) × (Fin n → ℝ)), ?_⟩
    ext i <;> apply Complex.ext <;> simp [h1, h2]

/-- (e) reality, `N = 2n`: `ℝᴺ = range (KAM.realInclusion₂ n)`. -/
theorem flow_e {n : ℕ}
    {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {F : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ε : ℝ} (h : SmallField W Ω F ε)
    (hreal : ∀ x ∈ Ω, x ∈ range (KAM.realInclusion₂ n) → F x ∈ range (KAM.realInclusion₂ n)) :
    ∀ x ∈ gaugeInterior W Ω (1 / 2), x ∈ range (KAM.realInclusion₂ n) →
      ∀ t ∈ Icc (-1 : ℝ) 1, flow F Ω t x ∈ range (KAM.realInclusion₂ n) := by
  intro x hx hxR t ht
  rw [mem_range_realInclusion₂_iff] at hxR ⊢
  set T := imCLM₂ n with hT
  -- the Picard iterates stay real
  have hpic : ∀ k : ℕ, ∀ τ ∈ Icc (-1 : ℝ) 1, T (picard F k τ x) = 0 := by
    intro k
    induction k with
    | zero => intro τ _; simpa [picard_zero] using hxR
    | succ k ih =>
      intro τ hτ
      have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      have hsub : uIcc (0 : ℝ) τ ⊆ Icc (-1 : ℝ) 1 := uIcc_subset_Icc h0 hτ
      have hint := intervalIntegrable_picard_field h k hx hτ
      rw [picard_succ, map_add, hxR, zero_add, ← T.intervalIntegral_comp_comm hint]
      have hz : ∀ s ∈ uIcc (0 : ℝ) τ, T (F (picard F k s x)) = 0 := by
        intro s hs
        have hsI := hsub hs
        have hΩ : picard F k s x ∈ Ω := mem_of_displacement h hx hsI (by
          simpa using (picard_regular h k).2 s hsI x hx)
        have := hreal _ hΩ ((mem_range_realInclusion₂_iff _).2 (ih s hsI))
        exact (mem_range_realInclusion₂_iff _).1 this
      rw [intervalIntegral.integral_congr hz]
      simp
  -- the flow is the limit
  obtain ⟨η, Λ, hη, hΛ, -, hest⟩ := picard_flow_estimate h hx
  have hx0 : ‖W (x - x)‖ < η := by simpa using hη
  set C : ℝ := ‖T‖ * ‖W.symm.toContinuousLinearMap‖ with hC
  have hbd : ∀ k : ℕ, ‖T (flow F Ω t x)‖ ≤ C * (ε * (Λ ^ k / (k.factorial : ℝ))) := by
    intro k
    have h1 : T (flow F Ω t x) = - T (picard F k t x - flow F Ω t x) := by
      rw [map_sub, hpic k t ht]; simp
    have h2 : ‖picard F k t x - flow F Ω t x‖ ≤
        ‖W.symm.toContinuousLinearMap‖ * ‖W (picard F k t x - flow F Ω t x)‖ := by
      have := W.symm.toContinuousLinearMap.le_opNorm (W (picard F k t x - flow F Ω t x))
      simpa using this
    have h3 := (hest x hx0 k t ht).trans (picard_bound_le h.eps_nonneg hΛ ht k)
    rw [h1, norm_neg]
    calc ‖T (picard F k t x - flow F Ω t x)‖ ≤ ‖T‖ * ‖picard F k t x - flow F Ω t x‖ :=
          T.le_opNorm _
      _ ≤ ‖T‖ * (‖W.symm.toContinuousLinearMap‖ * ‖W (picard F k t x - flow F Ω t x)‖) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ ≤ ‖T‖ * (‖W.symm.toContinuousLinearMap‖ * (ε * (Λ ^ k / (k.factorial : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by rw [hC]; ring
  have hlim := ((FloorSemiring.tendsto_pow_div_factorial_atTop Λ).const_mul ε).const_mul C
  have hle : ‖T (flow F Ω t x)‖ ≤ C * (ε * 0) := ge_of_tendsto' (by simpa using hlim) hbd
  simpa using hle

end FlowReal

end KAM.Canonical

end
