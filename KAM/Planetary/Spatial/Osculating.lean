/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Continuation
public import KAM.Planetary.Spatial.Osculating.Basic
public import KAM.Planetary.Spatial.Osculating.Core
public import KAM.Planetary.StrongAMD.Osculating

/-!
# Actual-velocity osculating ellipses in dimension three

Package LP-SP-OSC, `LP:MAIN L16 (508–529)` with `d = 3` and amendment N10 (`AMENDMENTS.md`); track
LP,
non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

Definitions, velocity identification and tangency are in `Osculating/Basic.lean`, the pointwise
estimate in `Osculating/Core.lean`.  Here:

* `exists_spatial_osc_estimates` — (43), uniformly on a set `K` of spatial negative-energy states
with
  `dS ≤ |q_i| ≤ R`, `|p_i| ≤ P`, `E_i ≤ -c`, `|𝐞_i| ≤ e_* < 1`: `∃ μ₀ A A_osc > 0`, for
  `0 < μ ≤ μ₀`, every `z ∈ K`, every `i`: `SpatialOscEstimate`.
* `spatialBarrier_osc_data` — `SpatialBarrierState`s (SP-GEO) satisfy all these bounds, are
collision
  free, and have the canonical perihelion/gap bounds.
* `spatial_osculating_barrier` — MAIN Lemma 16 with N10 on the safe set: `SpatialOscEstimate`
  (summed element estimate, ellipse validity `E^osc < 0`, `e^osc < 1`, tangency) and the half-gaps
  `d_⋆/2 ≤ oscPeri i`, `d_pair/2 ≤ oscPeri (i+1) - oscApo i`, with `A_osc μ₀ ≤ d_⋆/2` and
  `2 A_osc μ₀ ≤ d_pair/2`.
* `spatialOscPhase_of_estimates` — validity puts the state in the carrier `SpatialOscPhase` (OD-11
(b)).

Mass normalization: `spatialKeplerEnergy ν z i = ν_i E_i`; the osculating quantities are specific
(unit mass), so the energy clause is compared with `c/ν_i` (audit note of LP-OSC).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- The clauses of `LP:MAIN L16 (43)` at one state `z` and planet `i` (`d = 3`), for the parameters
`μ`, `A`, `A_osc` and the energy bound `c` (`spatialKeplerEnergy ≤ -c`, so the specific energy is
`≤ -c/ν_i`): the osculating elements are nondegenerate elliptic (`E^osc ≤ -(c/ν_i)/2`, `0 < a^osc`,
`e^osc < 1`), the ellipse passes through `q_i` (`a^osc (1 - e^osc) ≤ |q_i| ≤ a^osc (1 + e^osc)`),
`|a^osc - a| + |𝐞^osc - 𝐞| ≤ A μ`, and `|a^osc (1 ± e^osc) - a (1 ± e)| ≤ A_osc μ`. -/
def SpatialOscEstimate (ν : Fin n → ℝ) (c μ A Aosc : ℝ) (z : Phase (n * 3)) (i : Fin n) : Prop :=
  spatialOscEnergy ν μ z i ≤ -(c / ν i) / 2 ∧ 0 < spatialOscAxis ν μ z i ∧
  spatialOscPeri ν μ z i ≤ spaceLength (bodyVector3 z.1 i) ∧
  spaceLength (bodyVector3 z.1 i) ≤ spatialOscApo ν μ z i ∧ spatialOscEcc ν μ z i < 1 ∧
  |spatialOscAxis ν μ z i - spatialKeplerAxis ν z i| +
    spaceLength (spatialOscEccVector ν μ z i - spatialKeplerEccVector ν z i) ≤ A * μ ∧
  |spatialOscPeri ν μ z i - spatialKeplerPeri ν z i| ≤ Aosc * μ ∧
  |spatialOscApo ν μ z i - spatialKeplerApo ν z i| ≤ Aosc * μ

/-- **(43), uniform** (`LP:MAIN L16 (508–529)`): on a set `K` of physical states with the explicit
bounds `dS ≤ |q_i| ≤ R`, `|p_i| ≤ P`, `spatialKeplerEnergy ν z i ≤ -c`, `|𝐞_i| ≤ e_* < 1`, there are
`μ₀, A, A_osc > 0`, depending only on `ν`, `n` and the bounds, such that `SpatialOscEstimate` holds
for
`0 < μ ≤ μ₀`, every `z ∈ K` and every `i`. -/
theorem exists_spatial_osc_estimates {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {K : Set (Phase (n * 3))}
    {dS R P c eStar : ℝ} (hdS : 0 < dS) (hR : 0 < R) (hP : 0 < P) (hc : 0 < c) (he : eStar < 1)
    (hK : ∀ z ∈ K, SpatialNegativeEnergy ν z ∧
      (∀ i, dS ≤ spaceLength (bodyVector3 z.1 i) ∧ spaceLength (bodyVector3 z.1 i) ≤ R) ∧
      (∀ i, spaceLength (bodyVector3 z.2 i) ≤ P) ∧ (∀ i, spatialKeplerEnergy ν z i ≤ -c) ∧
      (∀ i, spaceLength (spatialKeplerEccVector ν z i) ≤ eStar)) :
    ∃ μ0 A Aosc : ℝ, 0 < μ0 ∧ 0 < A ∧ 0 < Aosc ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ0 → ∀ z ∈ K, ∀ i, SpatialOscEstimate ν c μ A Aosc z i := by
  obtain ⟨m0, M, hm0, hM1, hmM⟩ := exists_pos_bounds_mass hν
  have hM0 : 0 < M := by linarith
  set D : ℝ := (n : ℝ) * P with hDdef
  set Pv : ℝ := P / m0 with hPvdef
  set c1 : ℝ := c / M with hc1def
  have hD : 0 ≤ D := by positivity
  have hPv : 0 ≤ Pv := by positivity
  have hc1 : 0 < c1 := by positivity
  have hAE := oscAE_pos hD hPv hdS
  have hAe := oscAe_pos hR hD hPv hdS
  have hAa := oscAa_pos hD hPv hdS hc1
  have hAp := oscAperi_pos hR hD hPv hdS hc1
  have h1e : 0 < 1 - eStar := by linarith
  set s0 : ℝ := min 1 (min (c1 / (2 * oscAE D Pv dS)) ((1 - eStar) / (2 * oscAe R D Pv dS)))
    with hs0def
  have hs0pos : 0 < s0 := lt_min one_pos (lt_min (by positivity) (by positivity))
  refine ⟨s0 / M, M * (oscAa D Pv dS c1 + oscAe R D Pv dS), M * oscAperi R D Pv dS c1,
    by positivity, by positivity, by positivity, ?_⟩
  intro μ hμ hμ0 z hz i
  obtain ⟨hphys, hq, hp, hKE, hecc⟩ := hK z hz
  have hνi := hν i
  have hνne : ν i ≠ 0 := hνi.ne'
  set s : ℝ := M * μ with hs
  have hs0' : 0 ≤ s := by positivity
  have hsle : s ≤ s0 := by
    calc M * μ ≤ M * (s0 / M) := mul_le_mul_of_nonneg_left hμ0 hM0.le
      _ = s0 := by field_simp
  have hs1 : s ≤ 1 := hsle.trans (min_le_left _ _)
  have hsE : s * oscAE D Pv dS ≤ c1 / 2 := by
    have h := hsle.trans ((min_le_right _ _).trans (min_le_left _ _))
    have := (le_div_iff₀ (by positivity : 0 < 2 * oscAE D Pv dS)).1 h
    linarith
  have hsEcc : s * oscAe R D Pv dS ≤ (1 - eStar) / 2 := by
    have h := hsle.trans ((min_le_right _ _).trans (min_le_right _ _))
    have := (le_div_iff₀ (by positivity : 0 < 2 * oscAe R D Pv dS)).1 h
    linarith
  -- the perturbation `V - v = μ ∑ p_j`
  have hVv : spaceLength (spatialOscVelocity ν μ z i - (1 / ν i) • bodyVector3 z.2 i) ≤ s * D := by
    have h1 : spatialOscVelocity ν μ z i - (1 / ν i) • bodyVector3 z.2 i =
        μ • ∑ j, bodyVector3 z.2 j := by
      unfold spatialOscVelocity; rw [add_sub_cancel_left]
    rw [h1, spaceLength_smul, abs_of_pos hμ]
    have h2 : spaceLength (∑ j, bodyVector3 z.2 j) ≤ D := by
      refine (spaceLength_sum_le _ _).trans ?_
      calc ∑ j, spaceLength (bodyVector3 z.2 j) ≤ ∑ _j : Fin n, P :=
            Finset.sum_le_sum (fun j _ => hp j)
        _ = D := by simp [hDdef]
    calc μ * spaceLength (∑ j, bodyVector3 z.2 j) ≤ μ * D :=
          mul_le_mul_of_nonneg_left h2 hμ.le
      _ ≤ M * μ * D := by
          have : μ * D ≤ M * μ * D := by
            have := mul_le_mul_of_nonneg_right (by nlinarith : μ ≤ M * μ) hD
            exact this
          exact this
      _ = s * D := rfl
  have hv : spaceLength ((1 / ν i) • bodyVector3 z.2 i) ≤ Pv := by
    rw [spaceLength_smul, abs_of_pos (by positivity)]
    calc 1 / ν i * spaceLength (bodyVector3 z.2 i) ≤ 1 / m0 * P :=
          mul_le_mul (one_div_le_one_div_of_le hm0 (hmM i).1) (hp i)
            (spaceLength_nonneg _) (by positivity)
      _ = Pv := by rw [hPvdef]; ring
  have hk1 : 1 ≤ spatialOscParam ν μ i := by
    unfold spatialOscParam; have := mul_pos hμ hνi; linarith
  have hk : spatialOscParam ν μ i - 1 ≤ s := by
    unfold spatialOscParam
    calc 1 + μ * ν i - 1 = μ * ν i := by ring
      _ ≤ μ * M := mul_le_mul_of_nonneg_left (hmM i).2 hμ.le
      _ = s := by rw [hs]; ring
  -- the unperturbed specific energy
  have hKEi : ν i * spatialSpecEnergy 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2 i) ≤ -c :=
      by
    rw [← spatialKeplerEnergy_eq_spec ν z hνne]; exact hKE i
  have hE0neg : spatialSpecEnergy 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2 i) < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hνi.le h]
  have hE0 : spatialSpecEnergy 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2 i) ≤ -c1 := by
    rw [hc1def, ← neg_div]
    refine (le_div_iff₀ hM0).2 ?_
    have := mul_le_mul_of_nonpos_left (hmM i).2 hE0neg.le
    linarith
  have hE0ν : spatialSpecEnergy 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2 i) ≤ -(c / ν i)
      := by
    rw [← neg_div]
    refine (le_div_iff₀ hνi).2 ?_
    linarith
  have hc1le : c1 ≤ c / ν i := div_le_div_of_nonneg_left hc.le hνi (hmM i).2
  have he0 : spaceLength (spatialSpecEccVector 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2
      i)) ≤
      eStar := by
    rw [← spatialKeplerEccVector_eq_spec ν z hνne]; exact hecc i
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := spatial_osc_core (k := spatialOscParam ν μ i) (s := s) (D :=
      D) (Pv := Pv)
    (R := R) (dS := dS) (c1 := c1) (eStar := eStar) hdS (hq i).1 (hq i).2 hv hVv hs0' hs1 hD hPv
    hk1 hk hc1 hE0 he he0 hsE hsEcc
  have hEosc : spatialOscEnergy ν μ z i ≤ -(c / ν i) / 2 := by
    rw [spatialOscEnergy_eq_spec]; linarith
  have hEneg : spatialOscEnergy ν μ z i < 0 := by
    have : 0 < c / ν i := by positivity
    linarith
  obtain ⟨t1, t2, t3⟩ := spatialOsc_tangency ν hμ.le hνi (hdS.trans_le (hq i).1) hEneg
  have hA : s * oscAa D Pv dS c1 + s * oscAe R D Pv dS =
      M * (oscAa D Pv dS c1 + oscAe R D Pv dS) * μ := by rw [hs]; ring
  have hAp' : s * oscAperi R D Pv dS c1 = M * oscAperi R D Pv dS c1 * μ := by rw [hs]; ring
  refine ⟨hEosc, t1, t2, t3, k4, ?_, ?_, ?_⟩
  · rw [← hA, spatialKeplerAxis_eq_spec ν z hνne, spatialKeplerEccVector_eq_spec ν z hνne]
    exact add_le_add k2 k3
  · rw [← hAp']
    have e1 : spatialOscPeri ν μ z i - spatialKeplerPeri ν z i =
        spatialSpecAxis (spatialOscParam ν μ i) (bodyVector3 z.1 i) (spatialOscVelocity ν μ z i) *
          (1 - spaceLength (spatialSpecEccVector (spatialOscParam ν μ i) (bodyVector3 z.1 i)
            (spatialOscVelocity ν μ z i))) -
        spatialSpecAxis 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2 i) *
          (1 - spaceLength (spatialSpecEccVector 1 (bodyVector3 z.1 i)
            ((1 / ν i) • bodyVector3 z.2 i))) := by
      unfold spatialOscPeri spatialKeplerPeri spatialOscEcc
      rw [spatialKeplerAxis_eq_spec ν z hνne, spatialKeplerEccVector_eq_spec ν z hνne]
      rfl
    rw [e1]; exact k5
  · rw [← hAp']
    have e1 : spatialOscApo ν μ z i - spatialKeplerApo ν z i =
        spatialSpecAxis (spatialOscParam ν μ i) (bodyVector3 z.1 i) (spatialOscVelocity ν μ z i) *
          (1 + spaceLength (spatialSpecEccVector (spatialOscParam ν μ i) (bodyVector3 z.1 i)
            (spatialOscVelocity ν μ z i))) -
        spatialSpecAxis 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2 i) *
          (1 + spaceLength (spatialSpecEccVector 1 (bodyVector3 z.1 i)
            ((1 / ν i) • bodyVector3 z.2 i))) := by
      unfold spatialOscApo spatialKeplerApo spatialOscEcc
      rw [spatialKeplerAxis_eq_spec ν z hνne, spatialKeplerEccVector_eq_spec ν z hνne]
      rfl
    rw [e1]; exact k6

/-! ### GEOMOD's barrier states -/

/-- **The bridge from GEOMOD** (`LP:MAIN L5 (162–175)` to `L16`): barrier states satisfy all the
bounds required by `exists_spatial_osc_estimates`, with `e_* = 1 - 2 c d_⋆ / M` (`M ≥ max ν`, from
the
perihelion bound and `a ≤ M/(2c)`), together with collision-freeness and the barrier's perihelion
and gap bounds in canonical peri/apo form. -/
theorem spatialBarrier_osc_data {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {m : ℝ} (hm : 0 < m) :
    ∃ dS dP R P c eStar : ℝ, 0 < dS ∧ 0 < dP ∧ 0 < R ∧ 0 < P ∧ 0 < c ∧ eStar < 1 ∧
      ∀ z : Phase (n * 3), SpatialBarrierState ν U m z →
        SpatialNegativeEnergy ν z ∧ SpatialNoCollision z.1 ∧
        (∀ i, dS ≤ spaceLength (bodyVector3 z.1 i) ∧ spaceLength (bodyVector3 z.1 i) ≤ R) ∧
        (∀ i, spaceLength (bodyVector3 z.2 i) ≤ P) ∧ (∀ i, spatialKeplerEnergy ν z i ≤ -c) ∧
        (∀ i, spaceLength (spatialKeplerEccVector ν z i) ≤ eStar) ∧
        (∀ i, dS ≤ spatialKeplerPeri ν z i) ∧
        (∀ a : AdjIdx n, dP ≤ spatialKeplerPeri ν z a.upperIdx - spatialKeplerApo ν z a.1) := by
  obtain ⟨dS, dP, R, P, c, hdS, hdP, hR, hP, hc, -, hbar⟩ :=
    spatialStrongBarrier_physical hν hn hUc hUch hm
  obtain ⟨m0, M, hm0, hM1, hmM⟩ := exists_pos_bounds_mass hν
  have hM0 : 0 < M := by linarith
  refine ⟨dS, dP, R, P, c, 1 - 2 * c * dS / M, hdS, hdP, hR, hP, hc, ?_, ?_⟩
  · have : 0 < 2 * c * dS / M := by positivity
    linarith
  intro z hz
  obtain ⟨hS, hG, hq, hpair, hR', hP', hKE, -⟩ := hbar z hz
  have hphys := hz.1
  refine ⟨hphys, ⟨fun i => hdS.trans_le (hq i), fun i j hij => hdP.trans_le (hpair i j hij)⟩,
    fun i => ⟨hq i, hR' i⟩, hP', hKE, ?_, fun i => hS i, fun a => hG a⟩
  intro i
  obtain ⟨ha, -, -, -, he1, -⟩ := spatial_orbital_identities i (hphys i)
  have hKEn : spatialKeplerEnergy ν z i < 0 := by linarith [hKE i]
  have haE : spatialKeplerAxis ν z i * (2 * spatialKeplerEnergy ν z i) = -ν i := by
    have := hKEn.ne
    unfold spatialKeplerAxis; field_simp
  have h2 : 2 * c * spatialKeplerAxis ν z i ≤ M := by
    have := mul_le_mul_of_nonneg_left (by linarith [hKE i] : 2 * spatialKeplerEnergy ν z i ≤ -(2 *
        c))
      ha.le
    nlinarith [(hmM i).2]
  have h3 := hS i
  have h4 : 2 * c * dS ≤ (1 - spaceLength (spatialKeplerEccVector ν z i)) * M := by
    calc 2 * c * dS ≤ 2 * c * (spatialKeplerAxis ν z i * (1 - spaceLength (spatialKeplerEccVector ν
        z i))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (2 * c * spatialKeplerAxis ν z i) * (1 - spaceLength (spatialKeplerEccVector ν z i)) :=
          by ring
      _ ≤ M * (1 - spaceLength (spatialKeplerEccVector ν z i)) :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
      _ = _ := by ring
  have : 2 * c * dS / M ≤ 1 - spaceLength (spatialKeplerEccVector ν z i) := by
    rw [div_le_iff₀ hM0]; exact h4
  linarith

/-- **MAIN Lemma 16 with N10, planar** (`LP:MAIN L16 (508–529)`, `AMENDMENTS N10`): on the safe
compact physical set of GEOMOD (barrier states `C ≤ B(Λ z) - m`, `Λ z ∈ U`) there are
`d_⋆ = dS`, `d_pair = dP`, `c > 0` and `μ₀, A, A_osc > 0` with `A_osc μ₀ ≤ d_⋆/2` and
`2 A_osc μ₀ ≤ d_pair/2` such that for `0 < μ ≤ μ₀` and every barrier state `z`:
`V_i` is the actual heliocentric velocity (the `q_i`-block of the moving field), the osculating
elements satisfy (43) (`SpatialOscEstimate`), `d_⋆/2 ≤ a^osc_i (1 - e^osc_i)`, and for adjacent
planets
`d_pair/2 ≤ a^osc_{i+1} (1 - e^osc_{i+1}) - a^osc_i (1 + e^osc_i)`. -/
theorem spatial_osculating_barrier {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {m : ℝ} (hm : 0 < m) :
    ∃ dS dP c : ℝ, 0 < dS ∧ 0 < dP ∧ 0 < c ∧ ∃ μ0 A Aosc : ℝ, 0 < μ0 ∧ 0 < A ∧ 0 < Aosc ∧
      Aosc * μ0 ≤ dS / 2 ∧ 2 * (Aosc * μ0) ≤ dP / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ0 → ∀ z : Phase (n * 3), SpatialBarrierState ν U m z →
        (∀ i, bodyVector3 (spatialMovingField ν μ z).1 i = spatialOscVelocity ν μ z i) ∧
        (∀ i, SpatialOscEstimate ν c μ A Aosc z i) ∧
        (∀ i, dS / 2 ≤ spatialOscPeri ν μ z i) ∧
        (∀ a : AdjIdx n, dP / 2 ≤ spatialOscPeri ν μ z a.upperIdx - spatialOscApo ν μ z a.1) := by
  obtain ⟨dS, dP, R, P, c, eStar, hdS, hdP, hR, hP, hc, he, hdata⟩ :=
    spatialBarrier_osc_data hν hn hUc hUch hm
  obtain ⟨μ1, A, Aosc, hμ1, hA, hAosc, hest⟩ := exists_spatial_osc_estimates (ν := ν)
    (K := {z | SpatialBarrierState ν U m z}) hν hdS hR hP hc he
    (fun z hz => by
      obtain ⟨h1, -, h3, h4, h5, h6, -, -⟩ := hdata z hz
      exact ⟨h1, h3, h4, h5, h6⟩)
  refine ⟨dS, dP, c, hdS, hdP, hc, min μ1 (min (dS / (2 * Aosc)) (dP / (4 * Aosc))), A, Aosc,
    lt_min hμ1 (lt_min (by positivity) (by positivity)), hA, hAosc, ?_, ?_, ?_⟩
  · calc Aosc * min μ1 (min (dS / (2 * Aosc)) (dP / (4 * Aosc))) ≤ Aosc * (dS / (2 * Aosc)) :=
          mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hAosc.le
      _ = dS / 2 := by field_simp
  · calc 2 * (Aosc * min μ1 (min (dS / (2 * Aosc)) (dP / (4 * Aosc)))) ≤
          2 * (Aosc * (dP / (4 * Aosc))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            ((min_le_right _ _).trans (min_le_right _ _)) hAosc.le) (by norm_num)
      _ = dP / 2 := by field_simp; ring
  · intro μ hμ hμ0 z hz
    obtain ⟨-, hnc, -, -, -, -, hperi, hgap⟩ := hdata z hz
    have hμ1' : μ ≤ μ1 := hμ0.trans (min_le_left _ _)
    have hAμ : Aosc * μ ≤ dS / 2 := by
      calc Aosc * μ ≤ Aosc * (dS / (2 * Aosc)) :=
            mul_le_mul_of_nonneg_left (hμ0.trans ((min_le_right _ _).trans (min_le_left _ _)))
              hAosc.le
        _ = dS / 2 := by field_simp
    have hAμ' : Aosc * μ ≤ dP / 4 := by
      calc Aosc * μ ≤ Aosc * (dP / (4 * Aosc)) :=
            mul_le_mul_of_nonneg_left (hμ0.trans ((min_le_right _ _).trans (min_le_right _ _)))
              hAosc.le
        _ = dP / 4 := by field_simp
    have hE := fun i => hest μ hμ hμ1' z hz i
    refine ⟨fun i => spatialOscVelocity_eq_hamiltonianVectorField ν μ hnc i, hE, fun i => ?_, fun a
        => ?_⟩
    · have h1 := (abs_le.1 (hE i).2.2.2.2.2.2.1).1
      have h2 := hperi i
      linarith
    · have h1 := (abs_le.1 (hE a.upperIdx).2.2.2.2.2.2.1).2
      have h1' := (abs_le.1 (hE a.upperIdx).2.2.2.2.2.2.1).1
      have h2 := (abs_le.1 (hE a.1).2.2.2.2.2.2.2).2
      have h2' := (abs_le.1 (hE a.1).2.2.2.2.2.2.2).1
      have h3 := hgap a
      linarith

/-- Validity puts a state in the carrier of valid osculating states (OD-11 (b)): from
`SpatialOscEstimate` at every planet, `0 < ν`, `0 < μ` and `0 < |q_i|`. -/
theorem spatialOscPhase_of_estimates {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {c μ A Aosc : ℝ}
    (hc : 0 < c) (hμ : 0 < μ) {z : Phase (n * 3)}
    (hq : ∀ i, 0 < spaceLength (bodyVector3 z.1 i))
    (hE : ∀ i, SpatialOscEstimate ν c μ A Aosc z i) :
    ∃ w : SpatialOscPhase n ν μ, w.1 = z := by
  refine ⟨⟨z, hν, hμ, fun i => ⟨hq i, ?_, (hE i).2.2.2.2.1⟩⟩, rfl⟩
  have : 0 < c / ν i := by have := hν i; positivity
  linarith [(hE i).1]

end KAM.Planetary.Spatial

end
