/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Charts.Apply
public import KAM.Iso.Confinement.RealHam
public import KAM.Strip.RealRestriction

/-!
# Part 3: the literal conclusion of `stepI:p3:tori-ig1`

Append-only exports (package GAP-I3T) stating the real form of the application of I-G1 in
`bpI:p3:tori`: T1 including real-analyticity of the real restriction, T2, T3 including
`Ham_{h,f}(K(θ)) = E` for real `θ`, T5, and `ω_± ≠ 0`. They repair the over-claim of `ToriSide`
and `TorusOutput`, which carry the strip statements only.

* `TorusOutput.realRestriction_analyticOnNhd`: T1, real-analytic clause.
* `TorusOutput.realHamiltonian_realRestriction_eq`: T3 at real points.
* `ToriSide.ig1_literal`: the conjunction T1, T2, T3, T5 with `ω_± ≠ 0`.
-/

public section

namespace KAM.Iso.Charts

open KAM KAM.Torus KAM.Iso.Confinement

/-- `stepI:p3:tori-ig1`, T1: the real restriction `k = Re ∘ K ∘ ι` of the torus is real-analytic
on all of `ℝ²`. -/
theorem _root_.KAM.Iso.Confinement.TorusOutput.realRestriction_analyticOnNhd
    {h : (Fin 2 → ℂ) → ℂ} {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε C_K s₀ E : ℝ}
    {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {I ωt : Fin 2 → ℝ} (hs : 0 < s₀)
    (T : TorusOutput h f ε C_K s₀ E K I ωt) :
    AnalyticOnNhd ℝ (realRestriction K) Set.univ :=
  analyticOnNhd_realRestriction (ApplyAux.rhoInf_pos hs) T.holo

/-- `stepI:p3:tori-ig1`, T3 at real angles: `Ham_{h,f}(k(θ)) = E`, since `H = Re H` at the real
points where `H ∘ K` is real. -/
theorem _root_.KAM.Iso.Confinement.TorusOutput.realHamiltonian_realRestriction_eq
    {h : (Fin 2 → ℂ) → ℂ} {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε C_K s₀ E : ℝ}
    {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {I ωt : Fin 2 → ℝ} (hs : 0 < s₀)
    (T : TorusOutput h f ε C_K s₀ E K I ωt) (x : Fin 2 → ℝ) :
    realHamiltonian h f (realRestriction K x) = E := by
  have hmem : realInclusion 2 x ∈ complexStrip 2 (rhoInf s₀) :=
    realInclusion_mem_complexStrip (ApplyAux.rhoInf_pos hs) x
  have h1 : realHamiltonian h f (realRestriction K x) =
      (totalH h f (realInclusion₂ 2 (realRestriction K x))).re := rfl
  rw [h1, ← isRealOnReals_iff.mp T.real x, T.energy _ hmem, Complex.ofReal_re]

/-- `stepI:p3:tori-ig1`: the literal conclusion for one sign, `K_± := K_∞`: T1 (holomorphic,
primary, real on reals, real-analytic restriction); T2 (`E_{H,K,ω} = 0` on `T_{ρ∞}`, and the
Diophantine ray `ω_± = s_± ω*_±`, `1 < s_± < σ_ω`); T3 (`H ∘ K = E` on the strip and
`Ham_{h,f}(k(θ)) = E` for real `θ`); T5 (frequency on the ray with `2 < s^o < 4 M_g / m_h` and
`‖ω_± - ∇h(I)‖ ≤ C_K ε`); and `ω_± ≠ 0`, `ω*_± ≠ 0`. -/
theorem ToriSide.ig1_literal {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ}
    {B' : Set (Fin 2 → ℝ)} {η η₁ : ℝ} {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε C_K E : ℝ}
    {I₀ : Fin 2 → ℝ} {Ψ : ℝ × ℝ → Fin 2 → ℝ} {m : ℝ}
    {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {I ωt : Fin 2 → ℝ} (hs : 0 < s₀)
    (T : ToriSide B s₀ r₀ h B' η η₁ f ε C_K E I₀ Ψ m K I ωt) :
    (DifferentiableOn ℂ K (complexStrip 2 (rhoInf s₀)) ∧ IsPrimaryOnStrip K (rhoInf s₀) ∧
      IsRealOnReals K ∧ AnalyticOnNhd ℝ (realRestriction K) Set.univ) ∧
    ((∀ θ ∈ complexStrip 2 (rhoInf s₀), invarianceError (totalH h f) K ωt θ = 0) ∧
      ∃ (γ : ℝ) (ωs : Fin 2 → ℝ) (st : ℝ), 0 < γ ∧ IsDiophantine γ 2 ωs ∧ ωt = st • ωs ∧
        1 < st ∧ st < sigmaOmegaConst h B B') ∧
    ((∀ θ ∈ complexStrip 2 (rhoInf s₀), totalH h f (K θ) = (E : ℂ)) ∧
      ∀ x : Fin 2 → ℝ, realHamiltonian h f (realRestriction K x) = E) ∧
    (∃ (γ : ℝ) (ωs : Fin 2 → ℝ) (st sc : ℝ), 0 < γ ∧ IsDiophantine γ 2 ωs ∧ ωt = st • ωs ∧
      frequencyMap h I = sc • ωs ∧ 2 < sc ∧ sc < 4 * MgConst h B B' / mhConst h B B' ∧
      ‖ωt - frequencyMap h I‖ ≤ C_K * ε ∧ ωs ≠ 0 ∧ ωt ≠ 0) := by
  obtain ⟨γ, ωs, st, sc, hγ, hD, hωt, hst1, hst2, hfr, hsc1, hsc2, hclose⟩ := T.ray
  have hωs : ωs ≠ 0 := by
    intro h0
    have := hD (Pi.single 0 1) (fun h' => by simpa using congrFun h' 0)
    simp [h0] at this
    linarith [div_pos hγ one_pos]
  refine ⟨⟨T.holo, T.primary, T.real, T.toTorusOutput.realRestriction_analyticOnNhd hs⟩,
    ⟨T.invariant, γ, ωs, st, hγ, hD, hωt, hst1, hst2⟩,
    ⟨T.energy, T.toTorusOutput.realHamiltonian_realRestriction_eq hs⟩,
    γ, ωs, st, sc, hγ, hD, hωt, hfr, hsc1, hsc2, hclose, hωs, ?_⟩
  rw [hωt]
  exact smul_ne_zero (by linarith) hωs

end KAM.Iso.Charts

end
