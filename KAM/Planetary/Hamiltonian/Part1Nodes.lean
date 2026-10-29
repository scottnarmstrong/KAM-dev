/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Hamiltonian.Transport
public import KAM.Planetary.PGMeasure.Polar

/-!
# Part 1: literal exports of the chart and transport nodes (GAP-P13)

Unsigned exports stating the literal conclusions of `bpP:p1:typical`, `stepP:p1:pc-a`,
`stepP:p1:pc-b` and the six clauses `stepP:p1:tt-an`, `tt-lat`, `tt-inj`, `tt-lag`, `tt-flow`,
`tt-dio` of `torus-transport`, one lemma per clause, under the hypotheses of
`torus_transport_cyl` / `torus_transport_phys`.
-/

@[expose] public noncomputable section

open Set Real Function

namespace KAM.Planetary

open KAM KAM.Kepler

section Transport

variable {d : ℕ} {c : ℝ} {O : Set (Phase d)} {Ψ : Phase d → Phase d}
  {H : Phase d → ℝ} {w : Fin d → ℝ} {K : (Fin d → ℝ) → Phase d} {L : (Fin d → ℤ) → Phase d}

/-- `stepP:p1:tt-an` (i): `𝒦 = Ψ ∘ K` is analytic and `H` is differentiable along it. -/
theorem tt_an (hc : 0 < c) (hΨ : IsChart c Ψ O)
    (hK : IsLatticeTorus L (chartPullback c H Ψ) O w K) :
    AnalyticOnNhd ℝ (Ψ ∘ K) univ ∧ ∀ θ, DifferentiableAt ℝ H ((Ψ ∘ K) θ) := by
  obtain ⟨⟨hKan, hKO⟩, -⟩ := hK
  exact ⟨hΨ.1.comp hKan (fun θ _ => (hKO θ).1), fun θ =>
    (chart_field_differentiableAt_iff hc hΨ H (hKO θ).1).1 (hKO θ).2⟩

/-- `stepP:p1:tt-an` (i), range: `𝒦(θ) ∈ Ψ(K(ℝᵈ)) ⊆ U` (case (a)). -/
theorem tt_an_range {U : Set (Phase d)} (hU : Ψ '' range K ⊆ U) (θ : Fin d → ℝ) :
    (Ψ ∘ K) θ ∈ Ψ '' range K ∧ (Ψ ∘ K) θ ∈ U :=
  ⟨⟨K θ, mem_range_self θ, rfl⟩, hU ⟨K θ, mem_range_self θ, rfl⟩⟩

/-- `stepP:p1:tt-lat` (ii), case (a): `𝒦(θ + k) = Ψ(Kθ + ι_k) = 𝒦(θ) + σ_k`, `σ_k` the fast
shift of `(k_i)_{i<a}` (clause (iii) of `IsCylinderTorus`). -/
theorem tt_lat_cyl {a b : ℕ} {O : Set (Phase (a + b))} {Ψ : Phase (a + b) → Phase (a + b)}
    {G : Phase (a + b) → ℝ} {w : Fin (a + b) → ℝ} {K : (Fin (a + b) → ℝ) → Phase (a + b)}
    {L : (Fin (a + b) → ℤ) → Phase (a + b)} (hK : IsLatticeTorus L G O w K)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin (a + b) → ℤ, z + L k ∈ O ∧
      Ψ (z + L k) = Ψ z + fastShift (fun i : Fin a => k (Fin.castAdd b i))) :
    ∀ θ (k : Fin (a + b) → ℤ), (Ψ ∘ K) (θ + fun i => (k i : ℝ)) =
      (Ψ ∘ K) θ + fastShift (fun i : Fin a => k (Fin.castAdd b i)) := by
  obtain ⟨⟨-, hKO⟩, hlat, -⟩ := hK
  intro θ k
  simp only [Function.comp_apply]
  rw [hlat θ k]
  exact (hQ1 (K θ) (hKO θ).1 k).2

/-- `stepP:p1:tt-lat` (ii), case (b): periodicity, clause (iii) of `IsPhysicalTorus`. -/
theorem tt_lat_phys {G : Phase d → ℝ} (hK : IsLatticeTorus L G O w K)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin d → ℤ, z + L k ∈ O ∧ Ψ (z + L k) = Ψ z) :
    ∀ θ (k : Fin d → ℤ), (Ψ ∘ K) (θ + fun i => (k i : ℝ)) = (Ψ ∘ K) θ := by
  obtain ⟨⟨-, hKO⟩, hlat, -⟩ := hK
  intro θ k
  simp only [Function.comp_apply]
  rw [hlat θ k]
  exact (hQ1 (K θ) (hKO θ).1 k).2

/-- `stepP:p1:tt-inj` (iii), case (a): `𝒦(θ₁) = 𝒦(θ) + shift(k)` forces `θ₁ - θ ∈ ℤᵈ`. -/
theorem tt_inj_cyl {a b : ℕ} {O : Set (Phase (a + b))} {Ψ : Phase (a + b) → Phase (a + b)}
    {G : Phase (a + b) → ℝ} {w : Fin (a + b) → ℝ} {K : (Fin (a + b) → ℝ) → Phase (a + b)}
    {L : (Fin (a + b) → ℤ) → Phase (a + b)} (hK : IsLatticeTorus L G O w K)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, ∀ k : Fin (a + b) → ℤ,
      Ψ z' = Ψ z + fastShift (fun i : Fin a => k (Fin.castAdd b i)) →
        ∃ m : Fin (a + b) → ℤ, z' = z + L m) :
    ∀ θ θ' (k : Fin a → ℤ), (Ψ ∘ K) θ' = (Ψ ∘ K) θ + fastShift k →
      ∃ ell : Fin (a + b) → ℤ, θ' = θ + fun i => (ell i : ℝ) := by
  obtain ⟨⟨-, hKO⟩, hlat, hKinj, -⟩ := hK
  intro θ θ' k hk
  have h1 : Ψ (K θ') = Ψ (K θ) + fastShift
      (fun i : Fin a => (Fin.append k (0 : Fin b → ℤ) : Fin (a + b) → ℤ) (Fin.castAdd b i)) := by
    simpa [Fin.append_left] using hk
  obtain ⟨m, hm⟩ := hQ2 (K θ) (hKO θ).1 (K θ') (hKO θ').1 _ h1
  obtain ⟨l, hl⟩ := hKinj (θ + fun i => (m i : ℝ)) θ' (by rw [hlat θ m, hm])
  exact ⟨(fun i => m i + l i), by rw [hl]; funext i; simp [add_assoc]⟩

/-- `stepP:p1:tt-inj` (iii), case (b) (`k = 0`, `σ₀ = 0`). -/
theorem tt_inj_phys {G : Phase d → ℝ} (hK : IsLatticeTorus L G O w K)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ m : Fin d → ℤ, z' = z + L m) :
    ∀ θ θ', (Ψ ∘ K) θ = (Ψ ∘ K) θ' → ∃ k : Fin d → ℤ, θ' = θ + fun i => (k i : ℝ) := by
  obtain ⟨⟨-, hKO⟩, hlat, hKinj, -⟩ := hK
  intro θ θ' hk
  obtain ⟨m, hm⟩ := hQ2 (K θ) (hKO θ).1 (K θ') (hKO θ').1 hk.symm
  obtain ⟨l, hl⟩ := hKinj (θ + fun i => (m i : ℝ)) θ' (by rw [hlat θ m, hm])
  exact ⟨(fun i => m i + l i), by rw [hl]; funext i; simp [add_assoc]⟩

/-- `stepP:p1:tt-lag` (iv): `D𝒦(θ) = DΨ(Kθ) DK(θ)` is injective and
`Ω(D𝒦 u, D𝒦 v) = c Ω(DK u, DK v) = 0`. -/
theorem tt_lag (hc : 0 < c) (hΨ : IsChart c Ψ O)
    (hK : IsLatticeTorus L (chartPullback c H Ψ) O w K) (θ : Fin d → ℝ) :
    fderiv ℝ (Ψ ∘ K) θ = (fderiv ℝ Ψ (K θ)).comp (fderiv ℝ K θ) ∧
    Injective (fderiv ℝ (Ψ ∘ K) θ) ∧
    ∀ u v, symplecticForm (fderiv ℝ (Ψ ∘ K) θ u) (fderiv ℝ (Ψ ∘ K) θ v) =
        c * symplecticForm (fderiv ℝ K θ u) (fderiv ℝ K θ v) ∧
      c * symplecticForm (fderiv ℝ K θ u) (fderiv ℝ K θ v) = 0 := by
  obtain ⟨⟨hKan, hKO⟩, -, -, hDK, hLag, -⟩ := hK
  have hO : ∀ θ, K θ ∈ O := fun θ => (hKO θ).1
  have hd := fderiv_chart_comp_torus hc hΨ hKan hO θ
  refine ⟨hd, ?_, fun u v => ?_⟩
  · rw [hd]; exact (hΨ.bijective_fderiv hc (hO θ)).1.comp (hDK θ)
  · rw [hd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hΨ.2 _ (hO θ)]
    exact ⟨rfl, by rw [hLag θ u v, mul_zero]⟩

/-- `stepP:p1:tt-flow` (v): if `y(s) = K(θ + s w) ∈ O`, `G = H^Ψ` is differentiable at `y(t)` and
`y' = X_G(y)` at `t`, then `s ↦ 𝒦(θ + s w) = Ψ(y(s))` has derivative `X_H(𝒦(θ + t w))` at `t`. -/
theorem tt_flow (hc : 0 < c) (hΨ : IsChart c Ψ O) (θ : Fin d → ℝ) (t : ℝ)
    (hO : K (θ + t • w) ∈ O)
    (hdiff : DifferentiableAt ℝ (chartPullback c H Ψ) (K (θ + t • w)))
    (hflow : HasDerivAt (fun s : ℝ => K (θ + s • w))
      (hamiltonianVectorField (chartPullback c H Ψ) (K (θ + t • w))) t) :
    HasDerivAt (fun s : ℝ => (Ψ ∘ K) (θ + s • w))
      (hamiltonianVectorField H ((Ψ ∘ K) (θ + t • w))) t := by
  have := chart_orbit hc hΨ (H := H) (J := {t}) (y := fun s : ℝ => K (θ + s • w))
    (fun s hs => by rw [mem_singleton_iff.1 hs]; exact hO)
    (fun s hs => by rw [mem_singleton_iff.1 hs]; exact ⟨hdiff, hflow⟩) t rfl
  exact this.2

/-- `stepP:p1:tt-dio` (vi): in case (b), the Diophantine clause (vii) of `IsPhysicalTorus`. -/
theorem tt_dio {γ τ : ℝ} (hγ : 0 < γ) (hτ : (d : ℝ) - 1 < τ) (hw : IsDiophantine γ τ w) :
    ∃ γ τ : ℝ, 0 < γ ∧ (d : ℝ) - 1 < τ ∧ IsDiophantine γ τ w :=
  ⟨γ, τ, hγ, hτ, hw⟩

end Transport

section Scale

variable {d : ℕ}

/-- `stepP:p1:pc-a`: `Ω(S_c u, S_c v) = c Ω(u, v)`, `det DS_c = c^d`,
`S_c(z + ι_k) = S_c z + (c k, 0)`. -/
theorem pc_a (c : ℝ) :
    (∀ u v : Phase d, symplecticForm (angleScale c u) (angleScale c v) =
      c * symplecticForm u v) ∧
    (∀ z : Phase d, LinearMap.det (fderiv ℝ (angleScale c) z : Phase d →ₗ[ℝ] Phase d) = c ^ d) ∧
    (∀ (z : Phase d) (k : Fin d → ℤ),
      angleScale c (z + angleShift k) = angleScale c z + (fun i => c * (k i : ℝ), 0)) := by
  refine ⟨fun u v => ?_, fun z => ?_, angleScale_add_angleShift c⟩
  · simp only [symplecticForm, angleScale, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · have h : (angleScaleCLM c : Phase d →ₗ[ℝ] Phase d) =
        LinearMap.prodMap (c • LinearMap.id) LinearMap.id := by
      ext z <;> simp [angleScaleCLM]
    rw [show (angleScale c : Phase d → Phase d) = angleScaleCLM c from rfl,
      ContinuousLinearMap.fderiv, h, LinearMap.det_prodMap]
    simp

/-- `stepP:p1:pc-b`: `DS_c X_{H̃^{S_c}}(z) = X_{H̃}(S_c z)`, and the component formulas
`∂_{z₂} H̃^{S_c}(z) = c⁻¹ ∂₂H̃(S_c z)`, `∂_{z₁} H̃^{S_c}(z) = ∂₁H̃(S_c z)`. -/
theorem pc_b {c : ℝ} (hc : 0 < c) (H : Phase d → ℝ) (z : Phase d) :
    fderiv ℝ (angleScale c) z (hamiltonianVectorField (chartPullback c H (angleScale c)) z) =
      hamiltonianVectorField H (angleScale c z) ∧
    (fderiv ℝ (chartPullback c H (angleScale c)) z).comp (ContinuousLinearMap.inr ℝ _ _) =
      c⁻¹ • (fderiv ℝ H (angleScale c z)).comp (ContinuousLinearMap.inr ℝ _ _) ∧
    (fderiv ℝ (chartPullback c H (angleScale c)) z).comp (ContinuousLinearMap.inl ℝ _ _) =
      (fderiv ℝ H (angleScale c z)).comp (ContinuousLinearMap.inl ℝ _ _) := by
  have hΨ := isChart_angleScale (d := d) hc
  have hfield := chart_field hc hΨ H (mem_univ z)
  refine ⟨hfield, ?_⟩
  have hA : (fderiv ℝ (angleScale c) z) = angleScaleCLM c := by
    rw [show (angleScale c : Phase d → Phase d) = angleScaleCLM c from rfl]
    exact ContinuousLinearMap.fderiv _
  by_cases hH : DifferentiableAt ℝ H (angleScale c z)
  · have hΨd : DifferentiableAt ℝ (angleScale c) z := ((angleScaleCLM c).differentiableAt)
    have hd : fderiv ℝ (chartPullback c H (angleScale c)) z =
        c⁻¹ • (fderiv ℝ H (angleScale c z)).comp (angleScaleCLM c) := by
      have := (hH.hasFDerivAt.comp z hΨd.hasFDerivAt).const_mul c⁻¹
      rw [hA] at this
      exact this.fderiv
    rw [hd]
    constructor
    · ext v
      simp [angleScaleCLM]
    · ext v
      simp [angleScaleCLM]
      left; field_simp
  · have hG : ¬ DifferentiableAt ℝ (chartPullback c H (angleScale c)) z :=
      fun hG => hH ((chart_field_differentiableAt_iff hc hΨ H (mem_univ z)).1 hG)
    rw [fderiv_zero_of_not_differentiableAt hG, fderiv_zero_of_not_differentiableAt hH]
    simp

/-- `bpP:p1:typical`: (1) the one-oscillator polar map `(ψ, R) ↦ √(2R)(…)` is a `1`-chart on
`{R > 0}`, invariant under `ψ ↦ ψ + 2π`; (2) `S_c` is a `c`-chart; (3) charts compose, and
`(H^{Ψ₂})^{Ψ₁} = H^{Ψ₂ ∘ Ψ₁}`. -/
theorem typical (d : ℕ) :
    (IsChart 1 (fun z : Phase 1 => ((fun _ : Fin 1 => √(2 * z.2 0) * Real.cos (z.1 0)),
        (fun _ : Fin 1 => √(2 * z.2 0) * Real.sin (z.1 0)))) {z : Phase 1 | 0 < z.2 0} ∧
      ∀ (z : Phase 1) (k : Fin 1 → ℤ),
        (fun z : Phase 1 => ((fun _ : Fin 1 => √(2 * z.2 0) * Real.cos (z.1 0)),
          (fun _ : Fin 1 => √(2 * z.2 0) * Real.sin (z.1 0)))) (z + fullShift k) =
        (fun z : Phase 1 => ((fun _ : Fin 1 => √(2 * z.2 0) * Real.cos (z.1 0)),
          (fun _ : Fin 1 => √(2 * z.2 0) * Real.sin (z.1 0)))) z) ∧
    (∀ c : ℝ, 0 < c → IsChart c (angleScale c) (univ : Set (Phase d))) ∧
    ∀ (c₁ c₂ : ℝ) (H : Phase d → ℝ) (Ψ₁ Ψ₂ : Phase d → Phase d) (O₁ O₂ : Set (Phase d)),
      IsChart c₁ Ψ₁ O₁ → IsChart c₂ Ψ₂ O₂ → MapsTo Ψ₁ O₁ O₂ →
        IsChart (c₁ * c₂) (Ψ₂ ∘ Ψ₁) O₁ ∧
        chartPullback c₁ (chartPullback c₂ H Ψ₂) Ψ₁ = chartPullback (c₁ * c₂) H (Ψ₂ ∘ Ψ₁) :=
  ⟨⟨(disc_measure_chart (a := 0) (b := 1)).1, fun z k => by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [fullShift, Real.cos_add_int_mul_two_pi, mul_comm, Real.sin_add_int_mul_two_pi]⟩,
    fun c hc => isChart_angleScale hc, fun c₁ c₂ H Ψ₁ Ψ₂ O₁ O₂ h₁ h₂ hm =>
    ⟨h₁.comp h₂ hm, chartPullback_comp c₁ c₂ H Ψ₁ Ψ₂⟩⟩

end Scale

end KAM.Planetary

end
