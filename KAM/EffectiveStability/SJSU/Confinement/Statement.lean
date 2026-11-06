/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Confinement.Shift
public import KAM.EffectiveStability.SJSU.Initial.Main
public import KAM.EffectiveStability.Tube.Check.TubeChart

/-!
# The T2-CONF statement from the tube checker (T2-CONF, N5b phase B)

The conclusion of `sjsu_secular_confinement` (D76, draft v2 of
`docs/explorations/sjsu-g2-t2conf-proposal.md`), derived from
`KAM.EffectiveStability.Tube.tubeChart_confinement` with `V = sjsuV` (`V′`), `B = sjsuB` (N5a),
`H = sjsu18O2`, `z = sjsuZStar`, `r = δ = 10⁻⁶`, `ρ = κδ = 2·10⁻⁶`, `T = 5·10⁹`:

* `sjsu_secular_confinement_of_checks`: every literal check that is not yet available is a
  hypothesis; the ball data of N5c (`Nv`, `A`, `a`, `β`, `μ`, `Fu`, `Fφ`) are still parameters;
* `sjsu_secular_confinement_of_obs`: N5c's ball discharges plugged in (`sjsu_hN`, …, `sjsu_hLF`,
  and `γ_j = ε_j + μ` through `abs_obs_sub_le_of_face`). The remaining hypotheses are N5a's tube
  form of the Hamiltonian (`hHh`, `hhd`) and N7's literal observables with their rate, face and
  partial-bound checks.

Discharged here: orthogonality of `V′` (`sjsuV_orth`), the shift properties (`Confinement/Shift`),
`ContDiff ℝ 2 sjsu18O2`, the box `hz₀` as the sup-metric ball (`mem_closedBall_iff_coords`), and
the eccentricity enclosure (N6's `sjsu_tube_ecc`, through `chartGamma sjsuV = eccGamma sjsuEccV`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube Matrix

/-- `Γ` in the tube checker's form is N6's `eccGamma` for the SJSU rotation. -/
theorem chartGamma_sjsuV (I : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (j : Fin 3) :
    chartGamma sjsuV I φ j = eccGamma sjsuEccV I φ j := by
  have hV : sjsuV = Matrix.of fun j k => (sjsuEccV j k : ℝ) := by
    ext i k; exact sjsuV_eq_eccV i k
  rw [hV]
  rfl

/-- The eccentricity enclosure on the tube, in the form of the tube checker's `hG`. -/
theorem sjsu_hG (φ : Fin 2 → ℝ) (I : Fin 3 → ℝ) (hI : ∀ k, |I k - sjsuB φ k| ≤ 2 / 10 ^ 6)
    (j : Fin 3) :
    ![0.026, 0.009, 0.006] j ≤ Real.sqrt (1 - (1 - chartGamma sjsuV I φ j /
        ![5.3993226066969503769e-1, 2.1912825008425995084e-1, 4.7474331515411474555e-2] j) ^ 2) ∧
      Real.sqrt (1 - (1 - chartGamma sjsuV I φ j /
        ![5.3993226066969503769e-1, 2.1912825008425995084e-1, 4.7474331515411474555e-2] j) ^ 2) ≤
        ![0.062, 0.085, 0.063] j := by
  rw [chartGamma_sjsuV]
  exact sjsu_tube_ecc φ I hI j

/-- **The T2-CONF statement from the remaining literal checks** (ball data as parameters). -/
theorem sjsu_secular_confinement_of_checks
    {h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} {f : Fin 3 → (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {β ct ε γ η μ A a : Fin 3 → ℝ} {Fu : Fin 3 → Fin 3 → ℝ} {Fφ : Fin 3 → Fin 2 → ℝ} {Nv : ℝ}
    -- N5a: the Hamiltonian in tube coordinates
    (hHh : ∀ y ∈ actionPos 3, sjsu18O2 (rotMap sjsuV (polar y)) = h (shiftChart sjsuB y))
    (hhd : ∀ u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → DifferentiableAt ℝ h (u, φ))
    -- N7: the observables, rates and faces
    (hfper : ∀ j, ObsPeriodic (f j)) (hfd : ∀ j, Differentiable ℝ (f j))
    (hη : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → |reducedBracket (f j) h (u, φ)| ≤ η j)
    (hTη : ∀ j, 5 * 10 ^ 9 * η j < 1 / 10 ^ 6 / 2)
    (hface : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → |f j (u, φ) - ct j - u j| ≤ ε j)
    (hc : ∀ j, |f j (tubeChart sjsuV sjsuB sjsuZStar) - ct j| ≤ γ j)
    (hερ : ∀ j, 1 / 10 ^ 6 + ε j + γ j < 2 / 10 ^ 6)
    -- N5c: the ball `Q = closedBall z* 10⁻⁶`
    (hN : ∀ j, ∑ k, |sjsuV k j| ≤ Nv)
    (hAb : ∀ y ∈ Metric.closedBall sjsuZStar (1 / 10 ^ 6), ∀ j,
      |(rotMap sjsuVᵀ y).1 j| + |(rotMap sjsuVᵀ y).2 j| ≤ A j)
    (ha : ∀ j, 0 < a j)
    (hab : ∀ y ∈ Metric.closedBall sjsuZStar (1 / 10 ^ 6), ∀ j, a j ≤ modeSq sjsuV y j)
    (hβ : ∀ φ (b : Fin 2) (l : Fin 3), |fderiv ℝ sjsuB φ (Pi.single b 1) l| ≤ β l)
    (hμ : ∀ j, |tubeU sjsuV sjsuB sjsuZStar j| ≤ μ j)
    (hμρ : ∀ j, μ j + chartLip Nv A a β (Pi.single j 1) 0 * (1 / 10 ^ 6) < 2 / 10 ^ 6)
    (hFu : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → ∀ l,
      |fderiv ℝ (f j) (u, φ) (Pi.single l 1, 0)| ≤ Fu j l)
    (hFφ : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → ∀ b,
      |fderiv ℝ (f j) (u, φ) (0, Pi.single b 1)| ≤ Fφ j b)
    (hLF : ∀ j, chartLip Nv A a β (Fu j) (Fφ j) * (1 / 10 ^ 6) ≤ 1 / 10 ^ 6 / 2)
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
                4.7474331515411474555e-2] j) ^ 2) ≤ ![0.062, 0.085, 0.063] j := by
  have hz : z₀ ∈ Metric.closedBall sjsuZStar (1 / 10 ^ 6) :=
    (mem_closedBall_iff_coords (by norm_num)).2 hz₀
  exact tubeChart_confinement sjsuV_orth (B := sjsuB) (H := sjsu18O2) (h := h) (f := f)
    (bmin := fun k => (sjsuBmin k : ℝ)) (bmax := fun k => (sjsuBmax k : ℝ)) (δ := 1 / 10 ^ 6)
    (ρ := 2 / 10 ^ 6) (T := 5 * 10 ^ 9) (r := 1 / 10 ^ 6) (z := sjsuZStar)
    (Pγ := fun j g => ![0.026, 0.009, 0.006] j ≤ Real.sqrt (1 - (1 - g /
        ![5.3993226066969503769e-1, 2.1912825008425995084e-1, 4.7474331515411474555e-2] j) ^ 2) ∧
      Real.sqrt (1 - (1 - g /
        ![5.3993226066969503769e-1, 2.1912825008425995084e-1, 4.7474331515411474555e-2] j) ^ 2) ≤
        ![0.062, 0.085, 0.063] j)
    shiftPeriodic_sjsuB differentiable_sjsuB sjsu_rho_lt_bmin
    (fun φ k => (sjsuB_bounds φ k).1) (fun φ k => (sjsuB_bounds φ k).2) hβ sjsuB_symm
    contDiff_sjsu18O2 hHh hhd hfper hfd hη (by norm_num) hTη hface hc hερ hN hAb ha hab hμ hμρ
    hFu hFφ hLF sjsu_hG hz

/-- **The T2-CONF statement from N5a's and N7's checks**, with N5c's ball discharges plugged in. -/
theorem sjsu_secular_confinement_of_obs
    {h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} {f : Fin 3 → (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {ct ε η : Fin 3 → ℝ}
    -- N5a: the Hamiltonian in tube coordinates
    (hHh : ∀ y ∈ actionPos 3, sjsu18O2 (rotMap sjsuV (polar y)) = h (shiftChart sjsuB y))
    (hhd : ∀ u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → DifferentiableAt ℝ h (u, φ))
    -- N7: the observables, rates, faces and partial bounds
    (hfper : ∀ j, ObsPeriodic (f j)) (hfd : ∀ j, Differentiable ℝ (f j))
    (hη : ∀ j u φ, (∀ l, |u l| ≤ 2 / 10 ^ 6) → |reducedBracket (f j) h (u, φ)| ≤ η j)
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
                4.7474331515411474555e-2] j) ^ 2) ≤ ![0.062, 0.085, 0.063] j := by
  have hμρ' : ∀ _ : Fin 3, (sjsuMu : ℝ) ≤ 2 / 10 ^ 6 := fun _ => by simp [sjsuMu]; norm_num
  exact sjsu_secular_confinement_of_checks (μ := fun _ => (sjsuMu : ℝ))
    (γ := fun j => ε j + (sjsuMu : ℝ)) hHh hhd hfper hfd hη hTη hface
    (fun j => abs_obs_sub_le_of_face j (hface j) sjsu_hμ hμρ') hερ sjsu_hN sjsu_hAb sjsu_ha
    sjsu_hab sjsu_hβ sjsu_hμ sjsu_hμρ hFu hFφ sjsu_hLF z₀ hz₀

end KAM.EffectiveStability.SJSU

end
