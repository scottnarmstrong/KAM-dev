/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Assembly.Confinement

/-!
# Part 10 assembly: the full hypotheses check (`bpN:p10:hypotheses-check`)

`hypotheses_check_full` states items (a)-(h) of `bpN:p10:hypotheses-check` together, with the
Theorem-1 setting (constants `A, ε₁, a, R₀`) and the specification of `Ω₀` of the setting.
It is assembled from `hc_tubes`, `hc_h`, `hc_qc`, `hc_f`, `hc_exc`, `hc_time`,
`head_field_locality` and `head_theorem1_setting`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.Canonical KAM.Stability

variable {n : ℕ}

/-- hypotheses-check, items (a)-(h) together. `V = polyNbhd (centralSet n R) r0`,
`P = {‖J‖ ≤ R/2}`, `U` the real points of `V`, `W = ℝⁿ × U`. -/
theorem hypotheses_check_full (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hh : HeadHyp p h) (hf : IsAnalyticPerturbation p.R p.s ε f)
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) :
    -- (a) tubes
    (polyNbhd (centralSet n p.R) p.r0 ⊆ KAM.actionNbhd (actionBall n p.R) p.s ∧
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd (centralSet n p.R) p.r0 →
        I ∈ actionBall n (5 * p.R / 8) ∧ I ∈ actionBall n p.R ∧
          I ∈ realActionDomain n p.R p.s) ∧
      (∀ z : (Fin n → ℝ) × (Fin n → ℝ),
        z ∈ univ ×ˢ (KAM.realInclusion n ⁻¹' polyNbhd (centralSet n p.R) p.r0) →
          z ∈ Wdom n p.R p.s) ∧
      {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2}.Nonempty ∧
      actionBall n (p.R / 2) ⊆ {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2}) ∧
    -- (b) holomorphy, reality and Hessian bound for `h`
    (DifferentiableOn ℂ h (polyNbhd (centralSet n p.R) p.r0) ∧
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd (centralSet n p.R) p.r0 →
        (h (KAM.realInclusion n I)).im = 0) ∧
      ∀ I ∈ polyNbhd (centralSet n p.R) p.r0, ∀ x : Fin n → ℂ,
        euclid (fun i => ∑ j, complexHessian h I i j * x j) ≤ p.B * euclid x) ∧
    -- (c) quasi-convexity and `0 < μ ≤ B_c`
    ((∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd (centralSet n p.R) p.r0 →
        ∀ ξ : Fin n → ℝ, |∑ i, KAM.frequencyMap h I i * ξ i| ≤ p.ell * euclid ξ →
          p.mu * euclid ξ ^ 2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I ξ ξ) ∧
      0 < p.mu ∧ p.mu ≤ p.B) ∧
    -- (d) radius
    p.r0 ≤ p.ell / (2 * p.B) ∧
    -- (e) the perturbation, and the Theorem-1 setting with its constants
    (InClass (centralSet n p.R) p.r0 p.s1 f ∧
      RealOn (Dom n (centralSet n p.R) p.r0 p.s1) f ∧
      WBound (centralSet n p.R) p.r0 p.s1 f (p.epsPrime ε) ∧
      0 < p.epsPrime ε ∧ p.epsPrime ε ≤ p.eps1 ∧
      ∃ S : Theorem1Setting {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2} p.r0 p.s1 p.mu p.B p.ell h f,
        thmA p.mu p.B = p.A ∧ thmEps0 n p.r0 p.mu p.B = p.eps1 ∧
        HeadParams.expo n = 1 / (2 * (n : ℝ)) ∧ p.r0 / thmA p.mu p.B = p.R0 ∧
        -- (g) `Ω₀(I₀)` of the setting, its bounds and the time `T₀ ≥ 2T`
        ∀ I₀ (hP : I₀ ∈ {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2}), I₀ ∈ actionBall n (p.R / 2) →
          0 < p.wmin ∧ p.wmin ≤ (omega0Ball S I₀ hP).maximum ∧
          (omega0Ball S I₀ hP).maximum ≤ Real.sqrt n * p.M ∧
          2 * p.T ≤ thmA p.mu p.B ^ 2 * p.s1 / (omega0Ball S I₀ hP).maximum) ∧
    -- (f) the exceptional branch is empty
    (∀ I₀ ∈ actionBall n (p.R / 2),
      p.mu * p.r0 / 8 < p.wmin ∧ p.wmin ≤ euclid (KAM.frequencyMap h I₀)) ∧
    -- (h) the field: real valued on `W`, and the frozen field agrees with `X_{H^ℝ}`
    ((∀ z : (Fin n → ℝ) × (Fin n → ℝ),
        z ∈ univ ×ˢ (KAM.realInclusion n ⁻¹' polyNbhd (centralSet n p.R) p.r0) →
          (h (KAM.realInclusion n z.2) +
            f (KAM.realInclusion n z.1, KAM.realInclusion n z.2)).im = 0 ∧
          KAM.realHamiltonian h f z = realH (fun w => h w.2 + f w) z) ∧
      ∀ Hlocal : (Fin n → ℝ) × (Fin n → ℝ) → ℝ,
        EqOn Hlocal (KAM.realHamiltonian h f)
          (univ ×ˢ (KAM.realInclusion n ⁻¹' polyNbhd (centralSet n p.R) p.r0)) →
        EqOn (KAM.hamiltonianVectorField Hlocal)
          (KAM.hamiltonianVectorField (realH (fun w => h w.2 + f w)))
          (univ ×ˢ (KAM.realInclusion n ⁻¹' polyNbhd (centralSet n p.R) p.r0))) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨htube, hreal, hne, hball⟩ := hc_tubes hn p hp
  obtain ⟨h1, h2, h3⟩ := hc_h hn p hp hh
  obtain ⟨f1, f2, f3⟩ := hc_f hn p hp hf
  obtain ⟨-, -, -, hd⟩ := cp_dict hn p hp ε
  obtain ⟨d1, d2⟩ := hd hε hε0
  obtain ⟨-, -, -, -, -, hmu, hmuB, -, -, -, hrad, -⟩ := choice_props hn p hp
  have hs1 : 0 < p.s1 := by unfold HeadParams.s1; linarith [hp.hs]
  have S := head_theorem1_setting hn p hp hh hf hε hε0
  have hbound : ∀ I₀ ∈ actionBall n (p.R / 2), I₀ ∈ {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2} := by
    intro I₀ hI₀
    simp only [actionBall, mem_ball, dist_zero_right] at hI₀
    exact hI₀.le
  have hf_mem : ∀ {I : Fin n → ℝ}, KAM.realInclusion n I ∈ polyNbhd (centralSet n p.R) p.r0 →
      I ∈ realNbhd {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2} p.r0 := by
    rintro I ⟨_, ⟨J', hJ', rfl⟩, hlt⟩
    exact ⟨J', hJ', by rwa [← map_sub, KAM.norm_realInclusion] at hlt⟩
  have hwreal : ∀ z : (Fin n → ℝ) × (Fin n → ℝ),
      z ∈ univ ×ˢ (KAM.realInclusion n ⁻¹' polyNbhd (centralSet n p.R) p.r0) →
        (h (KAM.realInclusion n z.2) +
          f (KAM.realInclusion n z.1, KAM.realInclusion n z.2)).im = 0 := by
    intro z hz
    have hzV : KAM.realInclusion n z.2 ∈ polyNbhd (centralSet n p.R) p.r0 := hz.2
    have hz' : z ∈ realStrip {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2} p.r0 :=
      ⟨hz.1, hf_mem hzV⟩
    have hfz : (f (KAM.realInclusion₂ n z)).im = 0 :=
      f2 z ((realInclusion₂_mem_Dom_iff {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2} hs1 z).2 hz')
    rw [Complex.add_im, h2 z.2 hzV]
    simpa using hfz
  refine ⟨⟨htube, hreal, ?_, ?_, ?_⟩, ⟨h1, h2, h3⟩, ⟨hc_qc hn p hp hh, hmu, hmuB⟩, hrad,
    ⟨f1, f2, f3, d1, d2, S, rfl, rfl, rfl, rfl, ?_⟩, hc_exc hn p hp hh,
    ⟨fun z hz => ⟨hwreal z hz, rfl⟩, ?_⟩⟩
  · intro z hz
    have := (hreal z.2 hz.2).2.2
    rw [realActionDomain_eq hp.hR hp.hs] at this
    exact ⟨mem_univ _, this⟩
  · exact ⟨0, by simp only [mem_ofPred_eq, norm_zero]; linarith [hp.hR]⟩
  · exact hbound
  · intro I₀ hP hI₀
    obtain ⟨-, ⟨I1, hI1, hmx⟩, -, hcen, -⟩ := omega0 S I₀ hP
    obtain ⟨hlow1, hlow2⟩ := hc_exc hn p hp hh I₀ hI₀
    have hOm0 : 0 < (omega0Ball S I₀ hP).maximum := lt_of_lt_of_le hp.hω (hlow2.trans hcen)
    have hup : (omega0Ball S I₀ hP).maximum ≤ Real.sqrt n * p.M := by
      rw [hmx]
      exact hc_time hn p hp hh _ hI₀ I1 hI1
    exact ⟨hp.hω, hlow2.trans hcen, hup, head_time_prefactor hn p hp hOm0 hup⟩
  · intro Hl hHl
    have hfun : realH (fun w => h w.2 + f w) = KAM.realHamiltonian h f := by
      funext x
      rfl
    rw [hfun]
    exact head_field_locality p hHl

end KAM.Nekhoroshev

end
