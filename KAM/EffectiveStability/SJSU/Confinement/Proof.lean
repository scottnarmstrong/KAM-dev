/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Confinement.Statement
public import KAM.EffectiveStability.SJSU.Ham.Rate
public import KAM.EffectiveStability.SJSU.Check.Eta

/-!
# The T2-CONF theorem (T2-CONF, N5b + N9 (C))

`sjsu_secular_confinement_proof` is the statement `sjsu_secular_confinement` of D76 (draft v2 of
`docs/explorations/sjsu-g2-t2conf-proposal.md`), reflowed to 100 columns (same `Expr`; the frozen
anchor keeps the verbatim text). It is assembled in three steps:

* `sjsu_secular_confinement_of_N7`: `sjsu_secular_confinement_of_obs` (phase B) with N5a's
  `h̃ = sjsuHTilde sjsuB` discharged (`sjsu18O2_chart`; `sjsu_hhd`: `h̃` is differentiable on the
  tube box since `B_j + u_j ≥ b_min,j - ρ > 0`);
* `sjsu_secular_confinement_of_rate`: N8's observables `sjsuObs` and their checks discharged; the
  only hypotheses left are the rate bound `|{f_j, h̃}| ≤ η_j` on the box and `T η_j < δ / 2`;
* `sjsu_secular_confinement_proof`: the rate check `sjsu_hη`, `sjsu_hTη` with
  `η = (6, 23, 22)·10⁻¹⁹` (N9 (C), `SJSU.Check.Eta`).
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- `h̃` is differentiable on the whole tube box `|u| ≤ 2·10⁻⁶` (all `φ`). -/
theorem sjsu_hhd (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (hu : ∀ l, |u l| ≤ 2 / 10 ^ 6) :
    DifferentiableAt ℝ (sjsuHTilde sjsuB) (u, φ) :=
  differentiableAt_hTildeOf sjsuE sjsuN sjsuHwAll sjsuB (differentiable_sjsuB _) fun j => by
    have h1 := (sjsuB_bounds φ j).1
    have h2 := sjsu_rho_lt_bmin j
    have h3 := (abs_le.1 (hu j)).1
    show 0 < sjsuB φ j + u j
    linarith

/-- **The T2-CONF statement from N7's checks** (N5a's `h̃` and N5c's ball discharged). -/
theorem sjsu_secular_confinement_of_N7 {f : Fin 3 → (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {ct ε η : Fin 3 → ℝ}
    (hfper : ∀ j, ObsPeriodic (f j)) (hfd : ∀ j, Differentiable ℝ (f j))
    (hη : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) →
      |reducedBracket (f j) (sjsuHTilde sjsuB) (u, φ)| ≤ η j)
    (hTη : ∀ j, 5 * 10 ^ 9 * η j < 1 / 10 ^ 6 / 2)
    (hface : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → |f j (u, φ) - ct j - u j| ≤ ε j)
    (hερ : ∀ j, 1 / 10 ^ 6 + ε j + (ε j + (sjsuMu : ℝ)) < 2 / 10 ^ 6)
    (hFu : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → ∀ l,
      |fderiv ℝ (f j) (u, φ) (Pi.single l 1, 0)| ≤ (sjsuFuMax j l : ℝ))
    (hFφ : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → ∀ b,
      |fderiv ℝ (f j) (u, φ) (0, Pi.single b 1)| ≤ (sjsuFphiMax j b : ℝ))
    (z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ))
    (hz₀ : ∀ j,
      |z₀.2 j - ![0.03446271128616895, -0.0014352339355918572, -0.010122263133599879] j| ≤
          1 / 10 ^ 6 ∧
        |z₀.1 j - ![-0.009080669615926963, -0.025602508346796338, -0.0016540224121661881] j| ≤
          1 / 10 ^ 6) :
    ∃ T₁ : ℝ, 5 * 10 ^ 9 < T₁ ∧ ∃ z : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Set.Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField sjsu18O2 (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ → (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField sjsu18O2 (y t)) t) →
        ∀ t ∈ I, t ∈ Set.Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ 5 * 10 ^ 9 → ∀ j,
        ![0.026, 0.009, 0.006] j ≤
            Real.sqrt (1 - (1 - KAM.Planetary.oscillatorAction (z t).2 (z t).1 j /
              ![5.3993226066969503769e-1, 2.1912825008425995084e-1,
                4.7474331515411474555e-2] j) ^ 2) ∧
          Real.sqrt (1 - (1 - KAM.Planetary.oscillatorAction (z t).2 (z t).1 j /
              ![5.3993226066969503769e-1, 2.1912825008425995084e-1,
                4.7474331515411474555e-2] j) ^ 2) ≤ ![0.062, 0.085, 0.063] j :=
  sjsu_secular_confinement_of_obs (h := sjsuHTilde sjsuB) (fun y hy => sjsu18O2_chart y hy)
    sjsu_hhd hfper hfd hη hTη hface hερ hFu hFφ z₀ hz₀

/-- **The T2-CONF statement from the rate check alone** (N5a, N5c and N8's observables discharged):
the only hypotheses left are the bracket bound `|{f_j, h̃}| ≤ η_j` on the box and `T η_j < δ/2`. -/
theorem sjsu_secular_confinement_of_rate {η : Fin 3 → ℝ}
    (hη : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) →
      |reducedBracket (sjsuObs j) (sjsuHTilde sjsuB) (u, φ)| ≤ η j)
    (hTη : ∀ j, 5 * 10 ^ 9 * η j < 1 / 10 ^ 6 / 2)
    (z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ))
    (hz₀ : ∀ j,
      |z₀.2 j - ![0.03446271128616895, -0.0014352339355918572, -0.010122263133599879] j| ≤
          1 / 10 ^ 6 ∧
        |z₀.1 j - ![-0.009080669615926963, -0.025602508346796338, -0.0016540224121661881] j| ≤
          1 / 10 ^ 6) :
    ∃ T₁ : ℝ, 5 * 10 ^ 9 < T₁ ∧ ∃ z : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Set.Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField sjsu18O2 (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ → (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField sjsu18O2 (y t)) t) →
        ∀ t ∈ I, t ∈ Set.Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ 5 * 10 ^ 9 → ∀ j,
        ![0.026, 0.009, 0.006] j ≤
            Real.sqrt (1 - (1 - KAM.Planetary.oscillatorAction (z t).2 (z t).1 j /
              ![5.3993226066969503769e-1, 2.1912825008425995084e-1,
                4.7474331515411474555e-2] j) ^ 2) ∧
          Real.sqrt (1 - (1 - KAM.Planetary.oscillatorAction (z t).2 (z t).1 j /
              ![5.3993226066969503769e-1, 2.1912825008425995084e-1,
                4.7474331515411474555e-2] j) ^ 2) ≤ ![0.062, 0.085, 0.063] j :=
  sjsu_secular_confinement_of_N7 (f := sjsuObs) (ct := sjsuObsCt) (ε := sjsuObsEps) sjsu_hfper
    sjsu_hfd hη hTη sjsu_hface sjsu_hερ sjsu_hFu sjsu_hFφ z₀ hz₀


/-- **T2-CONF** (D76): for every start within `10⁻⁶` of the SJSU point, the `SJSU18-O2` flow exists
and is unique on a time interval beyond `5·10⁹`, and the three eccentricities stay in their bands
for `|t| ≤ 5·10⁹`. -/
theorem sjsu_secular_confinement_proof (z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ))
    (hz₀ : ∀ j,
      |z₀.2 j - ![0.03446271128616895, -0.0014352339355918572, -0.010122263133599879] j| ≤
          1 / 10 ^ 6 ∧
        |z₀.1 j - ![-0.009080669615926963, -0.025602508346796338, -0.0016540224121661881] j| ≤
          1 / 10 ^ 6) :
    ∃ T₁ : ℝ, 5 * 10 ^ 9 < T₁ ∧ ∃ z : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Set.Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField sjsu18O2 (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ → (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField sjsu18O2 (y t)) t) →
        ∀ t ∈ I, t ∈ Set.Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ 5 * 10 ^ 9 → ∀ j,
        ![0.026, 0.009, 0.006] j ≤
            Real.sqrt (1 - (1 - KAM.Planetary.oscillatorAction (z t).2 (z t).1 j /
              ![5.3993226066969503769e-1, 2.1912825008425995084e-1,
                4.7474331515411474555e-2] j) ^ 2) ∧
          Real.sqrt (1 - (1 - KAM.Planetary.oscillatorAction (z t).2 (z t).1 j /
              ![5.3993226066969503769e-1, 2.1912825008425995084e-1,
                4.7474331515411474555e-2] j) ^ 2) ≤ ![0.062, 0.085, 0.063] j :=
  sjsu_secular_confinement_of_rate (η := sjsuEta) sjsu_hη sjsu_hTη z₀ hz₀


end KAM.EffectiveStability.SJSU

end
