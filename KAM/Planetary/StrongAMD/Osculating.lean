/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Osculating.Basic
public import KAM.Planetary.StrongAMD.Osculating.Core

/-!
# Actual-velocity osculating ellipses (planar)

Package LP-OSC, `LP:MAIN L16 (508–529)` with amendment N10 (`AMENDMENTS.md`); track LP,
non-frozen; the statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

Definitions and tangency are in `Osculating/Basic.lean`, the pointwise estimate in
`Osculating/Core.lean`.  Here:

* `exists_osc_estimates` — (43), uniformly on a set `K` of physical states with explicit bounds
  `dS ≤ |q_i| ≤ R`, `|p_i| ≤ P`, `keplerEnergy ≤ -c`, `|e_i| ≤ e_* < 1`:
  `∃ μ₀ A A_osc > 0`, for `0 < μ ≤ μ₀`, every `z ∈ K`, every `i`: `OscEstimate`.
* `barrier_osc_data` — GEOMOD's barrier states satisfy all the bounds (`e_*` from the deficit
  bound), the perihelion/gap bounds in canonical peri/apo form, and are collision free.
* `osculating_barrier` — MAIN Lemma 16 with N10 on the safe compact set: `OscEstimate` and the
  half-gaps `d_⋆/2 ≤ oscPeri i`, `d_pair/2 ≤ oscPeri (i+1) - oscApo i`, with
  `A_osc μ₀ ≤ d_⋆/2` and `2 A_osc μ₀ ≤ d_pair/2`.

Mass normalization: `keplerEnergy ν z i = ν_i E_i` (`keplerEnergy_eq_spec`); the osculating
quantities are specific (unit mass), so the energy clause is compared with `c/ν_i`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Kepler KAM.Planetary

variable {n : ℕ}

/-- The clauses of `LP:MAIN L16 (43)` at one state `z` and planet `i`, for the parameters
`μ`, `A`, `A_osc` and the energy bound `c` (`keplerEnergy ≤ -c`, so the specific energy is
`≤ -c/ν_i`):
the osculating elements are nondegenerate elliptic (`E^osc ≤ -(c/ν_i)/2`, `0 < a^osc`,
`e^osc < 1`), the ellipse passes through `q_i` (`a^osc (1 - e^osc) ≤ |q_i| ≤ a^osc (1 + e^osc)`),
`|a^osc - a| + |𝐞^osc - 𝐞| ≤ A μ`, and `|a^osc (1 ± e^osc) - a (1 ± e)| ≤ A_osc μ`. -/
def OscEstimate (ν : Fin n → ℝ) (c μ A Aosc : ℝ) (z : Phase (n * 2)) (i : Fin n) : Prop :=
  oscEnergy ν μ z i ≤ -(c / ν i) / 2 ∧ 0 < oscAxis ν μ z i ∧
  oscPeri ν μ z i ≤ planeLength (bodyVector z.1 i) ∧
  planeLength (bodyVector z.1 i) ≤ oscApo ν μ z i ∧ oscEcc ν μ z i < 1 ∧
  |oscAxis ν μ z i - keplerAxis ν z i| +
    planeLength (oscEccVector ν μ z i - keplerEccVector ν z i) ≤ A * μ ∧
  |oscPeri ν μ z i - keplerPeri ν z i| ≤ Aosc * μ ∧
  |oscApo ν μ z i - keplerApo ν z i| ≤ Aosc * μ

/-- Uniform lower and upper bounds for the masses (the upper bound is at least one). -/
theorem exists_pos_bounds_mass {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) :
    ∃ m0 M : ℝ, 0 < m0 ∧ 1 ≤ M ∧ ∀ i, m0 ≤ ν i ∧ ν i ≤ M := by
  by_cases h : Nonempty (Fin n)
  · obtain ⟨i0, hi0⟩ := Finite.exists_min ν
    refine ⟨ν i0, 1 + ∑ j, ν j, hν i0, ?_, fun i => ⟨hi0 i, ?_⟩⟩
    · have : 0 ≤ ∑ j, ν j := Finset.sum_nonneg (fun j _ => (hν j).le)
      linarith
    · have := Finset.single_le_sum (f := ν) (fun j _ => (hν j).le) (Finset.mem_univ i)
      linarith
  · have : IsEmpty (Fin n) := not_nonempty_iff.1 h
    exact ⟨1, 1, one_pos, le_rfl, fun i => isEmptyElim i⟩

/-- **(43), uniform** (`LP:MAIN L16 (508–529)`): on a set `K` of physical states with the explicit
bounds `dS ≤ |q_i| ≤ R`, `|p_i| ≤ P`, `keplerEnergy ν z i ≤ -c`, `|𝐞_i| ≤ e_* < 1`, there are
`μ₀, A, A_osc > 0`, depending only on `ν`, `n` and the bounds, such that `OscEstimate` holds for
`0 < μ ≤ μ₀`, every `z ∈ K` and every `i`. -/
theorem exists_osc_estimates {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {K : Set (Phase (n * 2))}
    {dS R P c eStar : ℝ} (hdS : 0 < dS) (hR : 0 < R) (hP : 0 < P) (hc : 0 < c) (he : eStar < 1)
    (hK : ∀ z ∈ K, IsPhysicalState ν z ∧
      (∀ i, dS ≤ planeLength (bodyVector z.1 i) ∧ planeLength (bodyVector z.1 i) ≤ R) ∧
      (∀ i, planeLength (bodyVector z.2 i) ≤ P) ∧ (∀ i, keplerEnergy ν z i ≤ -c) ∧
      (∀ i, planeLength (keplerEccVector ν z i) ≤ eStar)) :
    ∃ μ0 A Aosc : ℝ, 0 < μ0 ∧ 0 < A ∧ 0 < Aosc ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ0 → ∀ z ∈ K, ∀ i, OscEstimate ν c μ A Aosc z i := by
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
  have hVv : planeLength (oscVelocity ν μ z i - (1 / ν i) • bodyVector z.2 i) ≤ s * D := by
    have h1 : oscVelocity ν μ z i - (1 / ν i) • bodyVector z.2 i =
        μ • ∑ j, bodyVector z.2 j := by
      unfold oscVelocity; rw [add_sub_cancel_left]
    rw [h1, planeLength_smul, abs_of_pos hμ]
    have h2 : planeLength (∑ j, bodyVector z.2 j) ≤ D := by
      refine (planeLength_sum_le _ _).trans ?_
      calc ∑ j, planeLength (bodyVector z.2 j) ≤ ∑ _j : Fin n, P :=
            Finset.sum_le_sum (fun j _ => hp j)
        _ = D := by simp [hDdef]
    calc μ * planeLength (∑ j, bodyVector z.2 j) ≤ μ * D :=
          mul_le_mul_of_nonneg_left h2 hμ.le
      _ ≤ M * μ * D := by
          have : μ * D ≤ M * μ * D := by
            have := mul_le_mul_of_nonneg_right (by nlinarith : μ ≤ M * μ) hD
            exact this
          exact this
      _ = s * D := rfl
  have hv : planeLength ((1 / ν i) • bodyVector z.2 i) ≤ Pv := by
    rw [planeLength_smul, abs_of_pos (by positivity)]
    calc 1 / ν i * planeLength (bodyVector z.2 i) ≤ 1 / m0 * P :=
          mul_le_mul (one_div_le_one_div_of_le hm0 (hmM i).1) (hp i)
            (KAM.Kepler.planeLength_nonneg _) (by positivity)
      _ = Pv := by rw [hPvdef]; ring
  have hk1 : 1 ≤ oscParam ν μ i := by
    unfold oscParam; have := mul_pos hμ hνi; linarith
  have hk : oscParam ν μ i - 1 ≤ s := by
    unfold oscParam
    calc 1 + μ * ν i - 1 = μ * ν i := by ring
      _ ≤ μ * M := mul_le_mul_of_nonneg_left (hmM i).2 hμ.le
      _ = s := by rw [hs]; ring
  -- the unperturbed specific energy
  have hKEi : ν i * specEnergy 1 (bodyVector z.1 i) ((1 / ν i) • bodyVector z.2 i) ≤ -c := by
    rw [← keplerEnergy_eq_spec ν z hνne]; exact hKE i
  have hE0neg : specEnergy 1 (bodyVector z.1 i) ((1 / ν i) • bodyVector z.2 i) < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hνi.le h]
  have hE0 : specEnergy 1 (bodyVector z.1 i) ((1 / ν i) • bodyVector z.2 i) ≤ -c1 := by
    rw [hc1def, ← neg_div]
    refine (le_div_iff₀ hM0).2 ?_
    have := mul_le_mul_of_nonpos_left (hmM i).2 hE0neg.le
    linarith
  have hE0ν : specEnergy 1 (bodyVector z.1 i) ((1 / ν i) • bodyVector z.2 i) ≤ -(c / ν i) := by
    rw [← neg_div]
    refine (le_div_iff₀ hνi).2 ?_
    linarith
  have hc1le : c1 ≤ c / ν i := div_le_div_of_nonneg_left hc.le hνi (hmM i).2
  have he0 : planeLength (specEccVector 1 (bodyVector z.1 i) ((1 / ν i) • bodyVector z.2 i)) ≤
      eStar := by
    rw [← keplerEccVector_eq_spec ν z hνne]; exact hecc i
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := osc_core (k := oscParam ν μ i) (s := s) (D := D) (Pv := Pv)
    (R := R) (dS := dS) (c1 := c1) (eStar := eStar) hdS (hq i).1 (hq i).2 hv hVv hs0' hs1 hD hPv
    hk1 hk hc1 hE0 he he0 hsE hsEcc
  have hEosc : oscEnergy ν μ z i ≤ -(c / ν i) / 2 := by
    rw [oscEnergy_eq_spec]; linarith
  have hEneg : oscEnergy ν μ z i < 0 := by
    have : 0 < c / ν i := by positivity
    linarith
  obtain ⟨t1, t2, t3⟩ := osc_tangency ν hμ.le hνi (hdS.trans_le (hq i).1) hEneg
  have hA : s * oscAa D Pv dS c1 + s * oscAe R D Pv dS =
      M * (oscAa D Pv dS c1 + oscAe R D Pv dS) * μ := by rw [hs]; ring
  have hAp' : s * oscAperi R D Pv dS c1 = M * oscAperi R D Pv dS c1 * μ := by rw [hs]; ring
  refine ⟨hEosc, t1, t2, t3, k4, ?_, ?_, ?_⟩
  · rw [← hA, keplerAxis_eq_spec ν z hνne, keplerEccVector_eq_spec ν z hνne]
    exact add_le_add k2 k3
  · rw [← hAp']
    have e1 : oscPeri ν μ z i - keplerPeri ν z i =
        specAxis (oscParam ν μ i) (bodyVector z.1 i) (oscVelocity ν μ z i) *
          (1 - planeLength (specEccVector (oscParam ν μ i) (bodyVector z.1 i)
            (oscVelocity ν μ z i))) -
        specAxis 1 (bodyVector z.1 i) ((1 / ν i) • bodyVector z.2 i) *
          (1 - planeLength (specEccVector 1 (bodyVector z.1 i)
            ((1 / ν i) • bodyVector z.2 i))) := by
      unfold oscPeri keplerPeri oscEcc
      rw [keplerAxis_eq_spec ν z hνne, keplerEccVector_eq_spec ν z hνne]
      rfl
    rw [e1]; exact k5
  · rw [← hAp']
    have e1 : oscApo ν μ z i - keplerApo ν z i =
        specAxis (oscParam ν μ i) (bodyVector z.1 i) (oscVelocity ν μ z i) *
          (1 + planeLength (specEccVector (oscParam ν μ i) (bodyVector z.1 i)
            (oscVelocity ν μ z i))) -
        specAxis 1 (bodyVector z.1 i) ((1 / ν i) • bodyVector z.2 i) *
          (1 + planeLength (specEccVector 1 (bodyVector z.1 i)
            ((1 / ν i) • bodyVector z.2 i))) := by
      unfold oscApo keplerApo oscEcc
      rw [keplerAxis_eq_spec ν z hνne, keplerEccVector_eq_spec ν z hνne]
      rfl
    rw [e1]; exact k6

/-! ### GEOMOD's barrier states -/

/-- **The bridge from GEOMOD** (`LP:MAIN L5 (162–175)` to `L16`): barrier states satisfy all the
bounds required by `exists_osc_estimates`, with `e_* = 1 - 2 c d_⋆ / M` (`M ≥ max ν`, from the
perihelion bound and `a ≤ M/(2c)`), together with collision-freeness and the barrier's perihelion
and gap bounds in canonical peri/apo form. -/
theorem barrier_osc_data {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {m : ℝ} (hm : 0 < m) :
    ∃ dS dP R P c eStar : ℝ, 0 < dS ∧ 0 < dP ∧ 0 < R ∧ 0 < P ∧ 0 < c ∧ eStar < 1 ∧
      ∀ z : Phase (n * 2), BarrierState ν U m z →
        IsPhysicalState ν z ∧ NoCollision z.1 ∧
        (∀ i, dS ≤ planeLength (bodyVector z.1 i) ∧ planeLength (bodyVector z.1 i) ≤ R) ∧
        (∀ i, planeLength (bodyVector z.2 i) ≤ P) ∧ (∀ i, keplerEnergy ν z i ≤ -c) ∧
        (∀ i, planeLength (keplerEccVector ν z i) ≤ eStar) ∧
        (∀ i, dS ≤ keplerPeri ν z i) ∧
        (∀ a : AdjIdx n, dP ≤ keplerPeri ν z a.upperIdx - keplerApo ν z a.1) := by
  obtain ⟨dS, dP, R, P, c, hdS, hdP, hR, hP, hc, -, hbar⟩ :=
    strongBarrier_physical hν hn hUc hUch hm
  obtain ⟨m0, M, hm0, hM1, hmM⟩ := exists_pos_bounds_mass hν
  have hM0 : 0 < M := by linarith
  refine ⟨dS, dP, R, P, c, 1 - 2 * c * dS / M, hdS, hdP, hR, hP, hc, ?_, ?_⟩
  · have : 0 < 2 * c * dS / M := by positivity
    linarith
  intro z hz
  obtain ⟨hS, hG, hq, hpair, hR', hP', hKE, -⟩ := hbar z hz
  have hphys := hz.1
  have horb := hphys.orbital hν
  refine ⟨hphys, ⟨fun i => hdS.trans_le (hq i), fun i j hij => hdP.trans_le (hpair i j hij)⟩,
    fun i => ⟨hq i, hR' i⟩, hP', hKE, ?_, fun i => hS i, fun a => hG a⟩
  intro i
  obtain ⟨ha, -, -, -, he1, -⟩ := orbital_identities i (horb i)
  have hKEn : keplerEnergy ν z i < 0 := by linarith [hKE i]
  have haE : keplerAxis ν z i * (2 * keplerEnergy ν z i) = -ν i := by
    have := hKEn.ne
    unfold keplerAxis; field_simp
  have h2 : 2 * c * keplerAxis ν z i ≤ M := by
    have := mul_le_mul_of_nonneg_left (by linarith [hKE i] : 2 * keplerEnergy ν z i ≤ -(2 * c))
      ha.le
    nlinarith [(hmM i).2]
  have h3 := hS i
  have h4 : 2 * c * dS ≤ (1 - planeLength (keplerEccVector ν z i)) * M := by
    calc 2 * c * dS ≤ 2 * c * (keplerAxis ν z i * (1 - planeLength (keplerEccVector ν z i))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (2 * c * keplerAxis ν z i) * (1 - planeLength (keplerEccVector ν z i)) := by ring
      _ ≤ M * (1 - planeLength (keplerEccVector ν z i)) :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
      _ = _ := by ring
  have : 2 * c * dS / M ≤ 1 - planeLength (keplerEccVector ν z i) := by
    rw [div_le_iff₀ hM0]; exact h4
  linarith

/-- **MAIN Lemma 16 with N10, planar** (`LP:MAIN L16 (508–529)`, `AMENDMENTS N10`): on the safe
compact physical set of GEOMOD (barrier states `C ≤ B(Λ z) - m`, `Λ z ∈ U`) there are
`d_⋆ = dS`, `d_pair = dP`, `c > 0` and `μ₀, A, A_osc > 0` with `A_osc μ₀ ≤ d_⋆/2` and
`2 A_osc μ₀ ≤ d_pair/2` such that for `0 < μ ≤ μ₀` and every barrier state `z`:
`V_i` is the actual heliocentric velocity (the `q_i`-block of the moving field), the osculating
elements satisfy (43) (`OscEstimate`), `d_⋆/2 ≤ a^osc_i (1 - e^osc_i)`, and for adjacent planets
`d_pair/2 ≤ a^osc_{i+1} (1 - e^osc_{i+1}) - a^osc_i (1 + e^osc_i)`. -/
theorem osculating_barrier {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {m : ℝ} (hm : 0 < m) :
    ∃ dS dP c : ℝ, 0 < dS ∧ 0 < dP ∧ 0 < c ∧ ∃ μ0 A Aosc : ℝ, 0 < μ0 ∧ 0 < A ∧ 0 < Aosc ∧
      Aosc * μ0 ≤ dS / 2 ∧ 2 * (Aosc * μ0) ≤ dP / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ0 → ∀ z : Phase (n * 2), BarrierState ν U m z →
        (∀ i, bodyVector (movingField ν μ z).1 i = oscVelocity ν μ z i) ∧
        (∀ i, OscEstimate ν c μ A Aosc z i) ∧
        (∀ i, dS / 2 ≤ oscPeri ν μ z i) ∧
        (∀ a : AdjIdx n, dP / 2 ≤ oscPeri ν μ z a.upperIdx - oscApo ν μ z a.1) := by
  obtain ⟨dS, dP, R, P, c, eStar, hdS, hdP, hR, hP, hc, he, hdata⟩ :=
    barrier_osc_data hν hn hUc hUch hm
  obtain ⟨μ1, A, Aosc, hμ1, hA, hAosc, hest⟩ := exists_osc_estimates (ν := ν)
    (K := {z | BarrierState ν U m z}) hν hdS hR hP hc he
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
    refine ⟨fun i => oscVelocity_eq_movingField ν μ hnc i, hE, fun i => ?_, fun a => ?_⟩
    · have h1 := (abs_le.1 (hE i).2.2.2.2.2.2.1).1
      have h2 := hperi i
      linarith
    · have h1 := (abs_le.1 (hE a.upperIdx).2.2.2.2.2.2.1).2
      have h1' := (abs_le.1 (hE a.upperIdx).2.2.2.2.2.2.1).1
      have h2 := (abs_le.1 (hE a.1).2.2.2.2.2.2.2).2
      have h2' := (abs_le.1 (hE a.1).2.2.2.2.2.2.2).1
      have h3 := hgap a
      linarith

end KAM.Planetary.StrongAMD

end
