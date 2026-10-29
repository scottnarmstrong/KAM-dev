/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Charts.Apply
public import KAM.Iso.Charts.Tori
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
* `ToriSide.ig1_literal`: the conjunction T1, T2, T3, T5 with `ω_± ≠ 0`; a conditional helper
  (it takes the output bundle `ToriSide`), NOT the node export.
* `Ig1Clauses`, `tori_ig1_node`: the node export `stepI:p3:tori-ig1`, stated from its source
  hypotheses in source order (patch and ray, then the constants, then `f, ε, I₀, E`); the
  `ToriSide` is constructed inside the proof by `apply` and `toriSide_of_applyOut`.
-/

public section

namespace KAM.Iso.Charts

open KAM KAM.Torus KAM.Iso.Confinement
open KAM.Head (Fconst)

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

/-- `stepI:p3:tori-ig1`, the literal conclusion for one sign on the FIXED ray `ω* = ωs`:
T1 (holomorphic, primary, real on reals, real-analytic restriction); T2 (`E = 0`, `ω*` Diophantine,
`ω = s ω*` with `1 < s < σ_ω`, `ω ≠ 0`); T3 (`H ∘ K = E` on the strip, `Ham_{h,f}(k(x)) = E` for
real `x`); T5 (`h(I) = E`, `∇h(I) = s° ω*` with `2 < s° < 4 M_g/m_h`, `‖ω - ∇h(I)‖ ≤ C_K ε`, and
`= |s - s°| ‖ω*‖`). -/
@[expose] def Ig1Clauses (B : Set (Fin 2 → ℝ)) (s₀ : ℝ) (h : (Fin 2 → ℂ) → ℂ)
    (B' : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε C_K E γ : ℝ)
    (ωs I : Fin 2 → ℝ) (K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (st : ℝ) : Prop :=
  (DifferentiableOn ℂ K (complexStrip 2 (rhoInf s₀)) ∧ IsPrimaryOnStrip K (rhoInf s₀) ∧
    IsRealOnReals K ∧ AnalyticOnNhd ℝ (realRestriction K) Set.univ) ∧
  ((∀ θ ∈ complexStrip 2 (rhoInf s₀), invarianceError (totalH h f) K (st • ωs) θ = 0) ∧
    IsDiophantine γ 2 ωs ∧ 1 < st ∧ st < sigmaOmegaConst h B B' ∧ st • ωs ≠ 0) ∧
  ((∀ θ ∈ complexStrip 2 (rhoInf s₀), totalH h f (K θ) = (E : ℂ)) ∧
    ∀ x : Fin 2 → ℝ, realHamiltonian h f (realRestriction K x) = E) ∧
  (realPart h I = E ∧ ∃ sc : ℝ, frequencyMap h I = sc • ωs ∧ 2 < sc ∧
    sc < 4 * MgConst h B B' / mhConst h B B' ∧
    ‖st • ωs - frequencyMap h I‖ ≤ C_K * ε ∧
    ‖st • ωs - frequencyMap h I‖ = |st - sc| * ‖ωs‖)

/-- `stepI:p3:tori-ig1` from its source hypotheses, in source order: the Part 3 setting (`hd`,
`hne`, the premise `IG1Statement`), a patch and a ray of it, then the constants `C₁ C₂ C₃` of
`apply` and the uniform `ε₁, C_K`, and only then `f, ε, I₀, E`. The tori are produced by `apply`
(not assumed). -/
theorem tori_ig1_node {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ}
    {B' : Set (Fin 2 → ℝ)} {η : ℝ} (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty)
    (hG1 : IG1Statement) {δE δm ρc : ℝ} {c : Fin 2 → ℝ} {W : Set (Fin 2 → ℝ)}
    {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hp : IsPatch h B r₀ B' (eta1 η B B') c W Ψ δE δm ρc) {γ m : ℝ}
    {ωs : Fin 2 → ℝ} (hray : IsRay h B B' c γ ωs m) (hm : |m| < δm) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ C_K ε₁ : ℝ, 0 < C_K → Fconst 2 s₀ r₀ 1 * max C₂ C₃ / (γ ^ 2 * rhoIso s₀ ^ 4) ≤ C_K →
        ε₁ ≤ 1 → ε₁ ≤ epsT h B B' s₀ r₀ → ε₁ ≤ δE / 2 →
        ε₁ ≤ γ ^ 4 * rhoIso s₀ ^ 8 / (C₁ * Fconst 2 s₀ r₀ 1) →
        ε₁ ≤ eta1 η B B' / (2 * C_K) →
        ∀ (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε : ℝ), PerturbData B s₀ r₀ f ε → ε < ε₁ →
          ∀ I₀ ∈ closure B', ‖I₀ - c‖ < ρc → ∀ E : ℝ, |E - realPart h I₀| ≤ ε →
            ∃ (K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (st : ℝ),
              Ig1Clauses B s₀ h B' f ε C_K E γ ωs (Ψ (E, m)) K st := by
  have hs := hd.hs
  obtain ⟨C₁, C₂, C₃, h1, h2, h3, hA⟩ := applyLocal_exists hd hne hG1 hp hray hm
  refine ⟨C₁, C₂, C₃, h1, h2, h3, fun C_K ε₁ hCKpos hCK hε1 hεT hεδ hεC hεη f ε hf hε I₀ hI₀ hI₀c
    E hE => ?_⟩
  have hE' : |E - realPart h c| ≤ δE := by
    have := (hp.ball_h I₀ (mem_ball_iff_norm.2 hI₀c))
    have h2' : ε < δE / 2 := hε.trans_le hεδ
    calc |E - realPart h c| ≤ |E - realPart h I₀| + |realPart h I₀ - realPart h c| :=
          abs_sub_le _ _ _
      _ ≤ δE := by linarith
  have hεK : C_K * ε < eta1 η B B' / 2 := by
    have := hε.trans_le hεη
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  obtain ⟨Kinf, sinf, hout⟩ := hA f ε hf (hε.le.trans hε1) (hε.le.trans hεT)
    (hε.trans_le hεC) E hE'
  have hT := toriSide_of_applyOut hd hne hp hray hm hCK hf.nonneg hI₀ hI₀c hE' hεK
    (C₂ := C₂) (C₃ := C₃) hout
  obtain ⟨-, -, hIE, -, hpar, hsc2, hsc4, -⟩ := points hd hne hp hray hm hE'
  obtain ⟨hs1, hs2, -, -, -, -, -, -, hsc⟩ := hout
  have hωs : ωs ≠ 0 := by
    intro h0
    have := hray.2.2.2.2.1
    rw [h0, norm_zero] at this
    obtain ⟨-, -, -, -, hmh, -⟩ := compact hd hne
    linarith
  have hclose : ‖sinf • ωs - frequencyMap h (Ψ (E, m))‖ ≤ C_K * ε := by
    rw [hpar]
    refine hsc.trans ?_
    calc C₃ * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 2 * rhoIso s₀ ^ 4)
        ≤ max C₂ C₃ * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 2 * rhoIso s₀ ^ 4) := by
          have hε0 : 0 ≤ ε := hf.nonneg
          have hF := ApplyAux.one_le_Fconst hs hd.hr
          have hγ := hray.1
          have hF0 : 0 ≤ Fconst 2 s₀ r₀ 1 * ε := by positivity
          have hD : 0 < γ ^ 2 * rhoIso s₀ ^ 4 := by
            have := ApplyAux.rhoIso_pos hs
            positivity
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hF0) hD.le
      _ = (Fconst 2 s₀ r₀ 1 * max C₂ C₃ / (γ ^ 2 * rhoIso s₀ ^ 4)) * ε := by ring
      _ ≤ C_K * ε := mul_le_mul_of_nonneg_right hCK hf.nonneg
  refine ⟨Kinf, sinf, ⟨hT.holo, hT.primary, hT.real,
      hT.toTorusOutput.realRestriction_analyticOnNhd hs⟩,
    ⟨hT.invariant, hray.2.1, hs1, hs2, smul_ne_zero (by linarith) hωs⟩,
    ⟨hT.energy, hT.toTorusOutput.realHamiltonian_realRestriction_eq hs⟩, hIE,
    ‖frequencyMap h (Ψ (E, m))‖ / ‖ωs‖, hpar, hsc2, hsc4, hclose, ?_⟩
  conv_lhs => rw [hpar]
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]

end KAM.Iso.Charts

end
