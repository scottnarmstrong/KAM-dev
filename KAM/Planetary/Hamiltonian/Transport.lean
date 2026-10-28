/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Frozen.Planetary.Defs.IsCylinderTorus
public import KAM.Frozen.Planetary.Defs.IsPhysicalTorus
public import KAM.Kepler.Basic
public import KAM.ODE.Basic
public import KAM.Planetary.Hamiltonian.Chart
public import KAM.Planetary.Hamiltonian.Diophantine

/-!
# Transport of lattice tori through charts

`bpP:p1:lattice-torus`, `torus-transport`, `period-convert` (c), `cyl-pipeline`, `phys-pipeline`.
A lattice torus `K` for `H^Ψ` is carried by a chart `Ψ` to a frozen cylinder/physical torus
`Ψ ∘ K` of `H`; `periodOne` converts the `2π`-convention of CP09 to period one.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

section Transport

variable {d : ℕ}

/-- `bpP:p1:lattice-torus` with the lattice vectors `L k` as a parameter: the blueprint's
`LT(G, O, w, K)` is `IsLatticeTorus angleShift G O w K`; `L = fullShift` is the `2π` lattice
used by `phys-pipeline`. Clauses (L1)-(L6) in order. -/
def IsLatticeTorus (L : (Fin d → ℤ) → Phase d) (G : Phase d → ℝ) (O : Set (Phase d))
    (w : Fin d → ℝ) (K : (Fin d → ℝ) → Phase d) : Prop :=
  (AnalyticOnNhd ℝ K univ ∧ ∀ θ, K θ ∈ O ∧ DifferentiableAt ℝ G (K θ)) ∧
  (∀ θ (k : Fin d → ℤ), K (θ + fun i => (k i : ℝ)) = K θ + L k) ∧
  (∀ θ θ', K θ = K θ' → ∃ k : Fin d → ℤ, θ' = θ + fun i => (k i : ℝ)) ∧
  (∀ θ, Injective (fderiv ℝ K θ)) ∧
  (∀ θ u v, symplecticForm (fderiv ℝ K θ u) (fderiv ℝ K θ v) = 0) ∧
  (∀ θ t, HasDerivAt (fun s : ℝ => K (θ + s • w))
    (hamiltonianVectorField G (K (θ + t • w))) t)

/-- `bpP:p1:torus-transport`, closing sentence: derivative of the transported torus. -/
theorem fderiv_chart_comp_torus {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} {Ψ : Phase d → Phase d}
    (hΨ : IsChart c Ψ O) {K : (Fin d → ℝ) → Phase d} (hKan : AnalyticOnNhd ℝ K univ)
    (hKO : ∀ θ, K θ ∈ O) (θ : Fin d → ℝ) :
    fderiv ℝ (Ψ ∘ K) θ = (fderiv ℝ Ψ (K θ)).comp (fderiv ℝ K θ) :=
  fderiv_comp θ (hΨ.1 (K θ) (hKO θ)).differentiableAt (hKan θ (mem_univ _)).differentiableAt

/-- The clauses of the transported torus that do not involve the lattice (steps (i), (ii), (iv),
(v) and the flow), shared by the cylinder and physical cases. -/
private theorem transport_core {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} {Ψ : Phase d → Phase d}
    (hΨ : IsChart c Ψ O) {H : Phase d → ℝ} {w : Fin d → ℝ} {K : (Fin d → ℝ) → Phase d}
    {L : (Fin d → ℤ) → Phase d} (hK : IsLatticeTorus L (chartPullback c H Ψ) O w K) :
    AnalyticOnNhd ℝ (Ψ ∘ K) univ ∧ (∀ θ, DifferentiableAt ℝ H (Ψ (K θ))) ∧
      (∀ θ, Injective (fderiv ℝ (Ψ ∘ K) θ)) ∧
      (∀ θ u v, symplecticForm (fderiv ℝ (Ψ ∘ K) θ u) (fderiv ℝ (Ψ ∘ K) θ v) = 0) ∧
      (∀ θ t, HasDerivAt (fun s : ℝ => (Ψ ∘ K) (θ + s • w))
        (hamiltonianVectorField H ((Ψ ∘ K) (θ + t • w))) t) := by
  obtain ⟨⟨hKan, hKO⟩, -, -, hDK, hLag, hflow⟩ := hK
  have hO : ∀ θ, K θ ∈ O := fun θ => (hKO θ).1
  refine ⟨hΨ.1.comp hKan (fun θ _ => hO θ), fun θ => ?_, fun θ => ?_, fun θ u v => ?_,
    fun θ t => ?_⟩
  · exact (chart_field_differentiableAt_iff hc hΨ H (hO θ)).1 (hKO θ).2
  · rw [fderiv_chart_comp_torus hc hΨ hKan hO θ]
    exact (hΨ.bijective_fderiv hc (hO θ)).1.comp (hDK θ)
  · rw [fderiv_chart_comp_torus hc hΨ hKan hO θ]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hΨ.2 _ (hO θ), hLag θ u v, mul_zero]
  · have := chart_orbit hc hΨ (H := H) (J := univ) (y := fun s : ℝ => K (θ + s • w))
      (fun s _ => hO _) (fun s _ => ⟨(hKO _).2, hflow θ s⟩) t (mem_univ t)
    exact this.2

/-- `bpP:p1:torus-transport` (a), cylinder case (`σ_k = fastShift k_f`). -/
theorem torus_transport_cyl {a b : ℕ} {c : ℝ} (hc : 0 < c) {O : Set (Phase (a + b))}
    {Ψ : Phase (a + b) → Phase (a + b)} (hΨ : IsChart c Ψ O) {H : Phase (a + b) → ℝ}
    {w : Fin (a + b) → ℝ} {K : (Fin (a + b) → ℝ) → Phase (a + b)}
    {L : (Fin (a + b) → ℤ) → Phase (a + b)} (hK : IsLatticeTorus L (chartPullback c H Ψ) O w K)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin (a + b) → ℤ, z + L k ∈ O ∧
      Ψ (z + L k) = Ψ z + fastShift (fun i : Fin a => k (Fin.castAdd b i)))
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, ∀ k : Fin (a + b) → ℤ,
      Ψ z' = Ψ z + fastShift (fun i : Fin a => k (Fin.castAdd b i)) →
        ∃ m : Fin (a + b) → ℤ, z' = z + L m)
    {U : Set (Phase (a + b))} (hU : Ψ '' range K ⊆ U) :
    IsCylinderTorus H U w (Ψ ∘ K) := by
  obtain ⟨han, hdiff, hinj, hlag, hflow⟩ := transport_core hc hΨ hK
  obtain ⟨⟨-, hKO⟩, hlat, hKinj, -, -, -⟩ := hK
  refine ⟨han, fun θ => ⟨hU ⟨K θ, mem_range_self θ, rfl⟩, hdiff θ⟩, fun θ k => ?_,
    fun θ θ' k hk => ?_, hinj, hlag, hflow⟩
  · simp only [Function.comp_apply]
    rw [hlat θ k]
    exact (hQ1 (K θ) (hKO θ).1 k).2
  · have h1 : Ψ (K θ') = Ψ (K θ) + fastShift
        (fun i : Fin a => (Fin.append k (0 : Fin b → ℤ) : Fin (a + b) → ℤ) (Fin.castAdd b i)) := by
      simpa [Fin.append_left] using hk
    obtain ⟨m, hm⟩ := hQ2 (K θ) (hKO θ).1 (K θ') (hKO θ').1 _ h1
    obtain ⟨l, hl⟩ := hKinj (θ + fun i => (m i : ℝ)) θ' (by rw [hlat θ m, hm])
    exact ⟨(fun i => m i + l i), by
      rw [hl]; funext i; simp [add_assoc]⟩

/-- `bpP:p1:torus-transport` (b), physical case (`σ_k = 0`, `w` Diophantine). -/
theorem torus_transport_phys {c : ℝ} (hc : 0 < c) {O : Set (Phase d)} {Ψ : Phase d → Phase d}
    (hΨ : IsChart c Ψ O) {H : Phase d → ℝ} {w : Fin d → ℝ} {K : (Fin d → ℝ) → Phase d}
    {L : (Fin d → ℤ) → Phase d} (hK : IsLatticeTorus L (chartPullback c H Ψ) O w K)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin d → ℤ, z + L k ∈ O ∧ Ψ (z + L k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ m : Fin d → ℤ, z' = z + L m)
    {γ τ : ℝ} (hγ : 0 < γ) (hτ : (d : ℝ) - 1 < τ) (hw : IsDiophantine γ τ w) :
    IsPhysicalTorus H w (Ψ ∘ K) := by
  obtain ⟨han, hdiff, hinj, hlag, hflow⟩ := transport_core hc hΨ hK
  obtain ⟨⟨-, hKO⟩, hlat, hKinj, -, -, -⟩ := hK
  refine ⟨han, hdiff, fun θ k => ?_, fun θ θ' hk => ?_, hinj, hlag, ⟨γ, τ, hγ, hτ, hw⟩, hflow⟩
  · simp only [Function.comp_apply]
    rw [hlat θ k]
    exact (hQ1 (K θ) (hKO θ).1 k).2
  · obtain ⟨m, hm⟩ := hQ2 (K θ) (hKO θ).1 (K θ') (hKO θ').1 hk.symm
    obtain ⟨l, hl⟩ := hKinj (θ + fun i => (m i : ℝ)) θ' (by rw [hlat θ m, hm])
    exact ⟨(fun i => m i + l i), by
      rw [hl]; funext i; simp [add_assoc]⟩

/-- `bpP:p1:period-convert` (c): the period-one parameter `K(θ) = κ̃(2πθ)`. -/
def periodOne (κ : (Fin d → ℝ) → Phase d) : (Fin d → ℝ) → Phase d := fun θ => κ ((2 * π) • θ)

/-- The `2π`-convention torus of CP09 Thm. 3 (`bpP:p1:phys-pipeline`): (L1)-(L5) with period
`2π` (`τ_k = fullShift k`) and the flow clause with the angular frequency `ω̃`. -/
def IsTwoPiLatticeTorus (G : Phase d → ℝ) (O : Set (Phase d)) (ω : Fin d → ℝ)
    (κ : (Fin d → ℝ) → Phase d) : Prop :=
  (AnalyticOnNhd ℝ κ univ ∧ ∀ ϑ, κ ϑ ∈ O ∧ DifferentiableAt ℝ G (κ ϑ)) ∧
  (∀ ϑ (k : Fin d → ℤ), κ (ϑ + fun i => 2 * π * (k i : ℝ)) = κ ϑ + fullShift k) ∧
  (∀ ϑ ϑ', κ ϑ = κ ϑ' → ∃ k : Fin d → ℤ, ϑ' = ϑ + fun i => 2 * π * (k i : ℝ)) ∧
  (∀ ϑ, Injective (fderiv ℝ κ ϑ)) ∧
  (∀ ϑ u v, symplecticForm (fderiv ℝ κ ϑ u) (fderiv ℝ κ ϑ v) = 0) ∧
  (∀ ϑ t, HasDerivAt (fun s : ℝ => κ (ϑ + s • ω))
    (hamiltonianVectorField G (κ (ϑ + t • ω))) t)

private theorem two_pi_ne : (2 * π : ℝ) ≠ 0 := by positivity

private theorem smul_inv_smul (ϑ : Fin d → ℝ) : (2 * π) • (2 * π)⁻¹ • ϑ = ϑ := by
  rw [smul_smul, mul_inv_cancel₀ two_pi_ne, one_smul]

private theorem periodOne_inv (κ : (Fin d → ℝ) → Phase d) (ϑ : Fin d → ℝ) :
    periodOne κ ((2 * π)⁻¹ • ϑ) = κ ϑ := by
  simp only [periodOne, smul_inv_smul]

private theorem periodOne_scale (κ : (Fin d → ℝ) → Phase d) :
    (fun ϑ => periodOne κ ((2 * π)⁻¹ • ϑ)) = κ :=
  funext (periodOne_inv κ)

private theorem smul_add_lattice (θ : Fin d → ℝ) (k : Fin d → ℤ) :
    (2 * π) • (θ + fun i => (k i : ℝ)) = (2 * π) • θ + fun i => 2 * π * (k i : ℝ) := by
  funext i; simp [mul_add]

private theorem smul_eq_add_lattice_iff (θ θ' : Fin d → ℝ) (k : Fin d → ℤ) :
    (2 * π) • θ' = (2 * π) • θ + (fun i => 2 * π * (k i : ℝ)) ↔
      θ' = θ + fun i => (k i : ℝ) := by
  rw [← smul_add_lattice]
  exact (smul_right_injective _ two_pi_ne).eq_iff

private theorem periodOne_flow (κ : (Fin d → ℝ) → Phase d) (ω θ : Fin d → ℝ) (s : ℝ) :
    periodOne κ (θ + s • (2 * π)⁻¹ • ω) = κ ((2 * π) • θ + s • ω) := by
  simp only [periodOne, smul_add, smul_comm (2 * π) s, smul_inv_smul]

/-- (c) analyticity. -/
theorem analyticOnNhd_periodOne_iff (κ : (Fin d → ℝ) → Phase d) :
    AnalyticOnNhd ℝ (periodOne κ) univ ↔ AnalyticOnNhd ℝ κ univ := by
  have h1 : AnalyticOnNhd ℝ (fun θ : Fin d → ℝ => (2 * π) • θ) univ :=
    fun θ _ => (((2 * π) • ContinuousLinearMap.id ℝ (Fin d → ℝ)).analyticAt θ)
  have h2 : AnalyticOnNhd ℝ (fun θ : Fin d → ℝ => (2 * π)⁻¹ • θ) univ :=
    fun θ _ => (((2 * π)⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ)).analyticAt θ)
  constructor
  · intro h
    rw [← periodOne_scale κ]
    exact h.comp h2 (mapsTo_univ _ _)
  · intro h
    exact h.comp h1 (mapsTo_univ _ _)

/-- (c) `DK(θ) = 2π Dκ̃(2πθ)` (unconditionally). -/
theorem fderiv_periodOne (κ : (Fin d → ℝ) → Phase d) (θ : Fin d → ℝ) :
    fderiv ℝ (periodOne κ) θ = (2 * π) • fderiv ℝ κ ((2 * π) • θ) := by
  have hs : HasFDerivAt (fun θ : Fin d → ℝ => (2 * π) • θ)
      ((2 * π) • ContinuousLinearMap.id ℝ (Fin d → ℝ)) θ :=
    ((2 * π) • ContinuousLinearMap.id ℝ (Fin d → ℝ)).hasFDerivAt
  by_cases h : DifferentiableAt ℝ κ ((2 * π) • θ)
  · have := (h.hasFDerivAt.comp θ hs).fderiv
    rw [show periodOne κ = κ ∘ fun θ : Fin d → ℝ => (2 * π) • θ from rfl, this]
    ext u : 1
    simp
  · have hp : ¬ DifferentiableAt ℝ (periodOne κ) θ := by
      intro hp
      apply h
      have e : (2 * π)⁻¹ • ((2 * π) • θ) = θ := by
        rw [smul_smul, inv_mul_cancel₀ two_pi_ne, one_smul]
      have hp' : DifferentiableAt ℝ (periodOne κ) ((2 * π)⁻¹ • ((2 * π) • θ)) := by
        rw [e]; exact hp
      have h3 : DifferentiableAt ℝ (fun ϑ => periodOne κ ((2 * π)⁻¹ • ϑ)) ((2 * π) • θ) :=
        hp'.comp ((2 * π) • θ)
          (((2 * π)⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ)).differentiableAt)
      rwa [periodOne_scale] at h3
    rw [fderiv_zero_of_not_differentiableAt hp, fderiv_zero_of_not_differentiableAt h, smul_zero]

/-- (c) the lattice clause, for any family `τ_k`. -/
theorem periodOne_lattice_iff (κ : (Fin d → ℝ) → Phase d) (T : (Fin d → ℤ) → Phase d) :
    (∀ θ (k : Fin d → ℤ), periodOne κ (θ + fun i => (k i : ℝ)) = periodOne κ θ + T k) ↔
      ∀ ϑ (k : Fin d → ℤ), κ (ϑ + fun i => 2 * π * (k i : ℝ)) = κ ϑ + T k := by
  constructor
  · intro h ϑ k
    have := h ((2 * π)⁻¹ • ϑ) k
    simpa only [periodOne, smul_add_lattice, smul_inv_smul] using this
  · intro h θ k
    simp only [periodOne, smul_add_lattice]
    exact h _ k

/-- (c) injectivity modulo the lattice. -/
theorem periodOne_injMod_iff (κ : (Fin d → ℝ) → Phase d) :
    (∀ θ θ', periodOne κ θ = periodOne κ θ' → ∃ k : Fin d → ℤ, θ' = θ + fun i => (k i : ℝ)) ↔
      ∀ ϑ ϑ', κ ϑ = κ ϑ' → ∃ k : Fin d → ℤ, ϑ' = ϑ + fun i => 2 * π * (k i : ℝ) := by
  constructor
  · intro h ϑ ϑ' hκ
    obtain ⟨k, hk⟩ := h ((2 * π)⁻¹ • ϑ) ((2 * π)⁻¹ • ϑ') (by
      simpa only [periodOne_inv] using hκ)
    refine ⟨k, ?_⟩
    have := (smul_eq_add_lattice_iff ((2 * π)⁻¹ • ϑ) ((2 * π)⁻¹ • ϑ') k).2 hk
    simpa only [smul_inv_smul] using this
  · intro h θ θ' hκ
    obtain ⟨k, hk⟩ := h _ _ hκ
    exact ⟨k, (smul_eq_add_lattice_iff θ θ' k).1 hk⟩

/-- (c) the flow clause: frozen frequency `w = ω̃ / 2π`, same time. -/
theorem periodOne_hasDerivAt_iff (κ : (Fin d → ℝ) → Phase d) (ω : Fin d → ℝ) (θ : Fin d → ℝ)
    (v : Phase d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => periodOne κ (θ + s • (2 * π)⁻¹ • ω)) v t ↔
      HasDerivAt (fun s : ℝ => κ ((2 * π) • θ + s • ω)) v t := by
  simp only [periodOne_flow]

private theorem symplecticForm_smul_smul (r : ℝ) (u v : Phase d) :
    symplecticForm (r • u) (r • v) = r * r * symplecticForm u v := by
  simp only [symplecticForm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- (c) packaged: the `2π` torus is a `fullShift`-lattice torus of period one with `w = ω̃/2π`. -/
theorem isLatticeTorus_periodOne_iff (G : Phase d → ℝ) (O : Set (Phase d)) (ω : Fin d → ℝ)
    (κ : (Fin d → ℝ) → Phase d) :
    IsLatticeTorus fullShift G O ((2 * π)⁻¹ • ω) (periodOne κ) ↔ IsTwoPiLatticeTorus G O ω κ := by
  unfold IsLatticeTorus IsTwoPiLatticeTorus
  have hpt : (∀ θ, periodOne κ θ ∈ O ∧ DifferentiableAt ℝ G (periodOne κ θ)) ↔
      ∀ ϑ, κ ϑ ∈ O ∧ DifferentiableAt ℝ G (κ ϑ) := by
    constructor
    · intro h ϑ
      simpa only [periodOne_inv] using h ((2 * π)⁻¹ • ϑ)
    · intro h θ
      exact h _
  have hinj : (∀ θ, Injective (fderiv ℝ (periodOne κ) θ)) ↔ ∀ ϑ, Injective (fderiv ℝ κ ϑ) := by
    have key : ∀ θ, Injective (fderiv ℝ (periodOne κ) θ) ↔
        Injective (fderiv ℝ κ ((2 * π) • θ)) := by
      intro θ
      rw [fderiv_periodOne]
      constructor
      · intro h a b hab
        exact h (by simp [hab])
      · intro h a b hab
        apply h
        simpa [two_pi_ne] using hab
    constructor
    · intro h ϑ
      have := (key ((2 * π)⁻¹ • ϑ)).1 (h _)
      rwa [smul_inv_smul] at this
    · intro h θ
      exact (key θ).2 (h _)
  have hsym : (∀ θ u v, symplecticForm (fderiv ℝ (periodOne κ) θ u) (fderiv ℝ (periodOne κ) θ v) = 0)
      ↔ ∀ ϑ u v, symplecticForm (fderiv ℝ κ ϑ u) (fderiv ℝ κ ϑ v) = 0 := by
    have key : ∀ θ u v, symplecticForm (fderiv ℝ (periodOne κ) θ u) (fderiv ℝ (periodOne κ) θ v)
        = (2 * π) * (2 * π) * symplecticForm (fderiv ℝ κ ((2 * π) • θ) u)
          (fderiv ℝ κ ((2 * π) • θ) v) := by
      intro θ u v
      rw [fderiv_periodOne]
      exact symplecticForm_smul_smul _ _ _
    constructor
    · intro h ϑ u v
      have := h ((2 * π)⁻¹ • ϑ) u v
      rw [key, smul_inv_smul] at this
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_pi_ne two_pi_ne)
    · intro h θ u v
      rw [key, h, mul_zero]
  have hflow : (∀ θ t, HasDerivAt (fun s : ℝ => periodOne κ (θ + s • (2 * π)⁻¹ • ω))
      (hamiltonianVectorField G (periodOne κ (θ + t • (2 * π)⁻¹ • ω))) t) ↔
      ∀ ϑ t, HasDerivAt (fun s : ℝ => κ (ϑ + s • ω))
        (hamiltonianVectorField G (κ (ϑ + t • ω))) t := by
    simp only [periodOne_flow]
    constructor
    · intro h ϑ t
      simpa only [smul_inv_smul] using h ((2 * π)⁻¹ • ϑ) t
    · intro h θ t
      exact h _ t
  rw [analyticOnNhd_periodOne_iff, hpt, periodOne_lattice_iff, periodOne_injMod_iff, hinj, hsym,
    hflow]

private theorem angleScale_injective {c : ℝ} (hc : c ≠ 0) :
    Injective (angleScale c : Phase d → Phase d) := by
  intro z z' h
  have h1 : c • z.1 = c • z'.1 := congrArg Prod.fst h
  exact Prod.ext ((smul_right_injective _ hc) h1) (by simpa [angleScale] using congrArg Prod.snd h)

/-- `bpP:p1:cyl-pipeline` (consumed by Part 5). -/
theorem cyl_pipeline {a b : ℕ} {H : Phase (a + b) → ℝ} {Φ : Phase (a + b) → Phase (a + b)}
    {O₀ : Set (Phase (a + b))} (hΦ : IsChart 1 Φ O₀)
    (hQ1 : ∀ z ∈ O₀, ∀ k : Fin (a + b) → ℤ, z + fullShift k ∈ O₀ ∧
      Φ (z + fullShift k) = Φ z + fastShift (fun i : Fin a => k (Fin.castAdd b i)))
    (hQ2 : ∀ z ∈ O₀, ∀ z' ∈ O₀, ∀ k : Fin (a + b) → ℤ,
      Φ z' = Φ z + fastShift (fun i : Fin a => k (Fin.castAdd b i)) →
        ∃ m : Fin (a + b) → ℤ, z' = z + fullShift m)
    {w : Fin (a + b) → ℝ} {K₃ : (Fin (a + b) → ℝ) → Phase (a + b)}
    (hK : IsLatticeTorus angleShift (chartPullback (2 * π) H (Φ ∘ angleScale (2 * π)))
      (angleScale (2 * π) ⁻¹' O₀) w K₃)
    {U : Set (Phase (a + b))} (hU : (Φ ∘ angleScale (2 * π)) '' range K₃ ⊆ U) :
    IsCylinderTorus H U w (Φ ∘ angleScale (2 * π) ∘ K₃) := by
  have hpos : (0 : ℝ) < 2 * π := by positivity
  have hch : IsChart (2 * π) (Φ ∘ angleScale (2 * π)) (angleScale (2 * π) ⁻¹' O₀) := by
    have := ((isChart_angleScale (d := a + b) hpos).mono (subset_univ (angleScale (2 * π) ⁻¹' O₀))).comp hΦ
      (fun z hz => hz)
    rwa [mul_one] at this
  have hshift : ∀ (z : Phase (a + b)) (k : Fin (a + b) → ℤ),
      angleScale (2 * π) (z + angleShift k) = angleScale (2 * π) z + fullShift k :=
    fun z k => angleScale_add_angleShift (2 * π) z k
  refine torus_transport_cyl hpos hch hK (fun z hz k => ?_) (fun z hz z' hz' k h => ?_) hU
  · have := hQ1 _ hz k
    rw [← hshift] at this
    exact this
  · have h' : Φ (angleScale (2 * π) z') = Φ (angleScale (2 * π) z) +
        fastShift (fun i : Fin a => k (Fin.castAdd b i)) := h
    obtain ⟨m, hm⟩ := hQ2 _ hz _ hz' k h'
    exact ⟨m, angleScale_injective hpos.ne' (by rw [hshift, hm])⟩

/-- `bpP:p1:phys-pipeline` (consumed by Parts 12, 13). -/
theorem phys_pipeline {H : Phase d → ℝ} {Φ : Phase d → Phase d} {O₀ : Set (Phase d)}
    (hΦ : IsChart 1 Φ O₀)
    (hQ1 : ∀ z ∈ O₀, ∀ k : Fin d → ℤ, z + fullShift k ∈ O₀ ∧ Φ (z + fullShift k) = Φ z)
    (hQ2 : ∀ z ∈ O₀, ∀ z' ∈ O₀, Φ z' = Φ z → ∃ m : Fin d → ℤ, z' = z + fullShift m)
    {κ : (Fin d → ℝ) → Phase d} {ω : Fin d → ℝ} (hκ : IsTwoPiLatticeTorus (H ∘ Φ) O₀ ω κ)
    {γ τ : ℝ} (hγ : 0 < γ) (hτ : (d : ℝ) - 1 < τ) (hω : IsDiophantine γ τ ω) :
    IsPhysicalTorus H ((2 * π)⁻¹ • ω) (Φ ∘ periodOne κ) ∧
      range (Φ ∘ periodOne κ) = Φ '' range κ := by
  have hpos : (0 : ℝ) < 2 * π := by positivity
  have hG : chartPullback 1 H Φ = H ∘ Φ := by
    funext z; simp [chartPullback]
  have hK : IsLatticeTorus fullShift (chartPullback 1 H Φ) O₀ ((2 * π)⁻¹ • ω) (periodOne κ) := by
    rw [hG]
    exact (isLatticeTorus_periodOne_iff _ _ _ _).2 hκ
  refine ⟨torus_transport_phys one_pos hΦ hK hQ1 hQ2 (div_pos hγ hpos) hτ
    ((isDiophantine_smul_iff hpos ω).1 hω), ?_⟩
  rw [range_comp]
  congr 1
  ext z
  constructor
  · rintro ⟨θ, rfl⟩; exact ⟨(2 * π) • θ, rfl⟩
  · rintro ⟨ϑ, rfl⟩; exact ⟨(2 * π)⁻¹ • ϑ, periodOne_inv κ ϑ⟩

end Transport

end KAM.Planetary

end
