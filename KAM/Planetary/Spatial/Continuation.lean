/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Continuation
public import KAM.Planetary.Spatial.Geometry
public import KAM.Planetary.StrongAMD.Modulus

/-!
# The spatial moving threshold (17) and continuation

Package LP-SP-GEO, `LP:MAIN L6 (177–189)` with `d = 3` and amendment N2 (one shared compact `U`);
track LP, non-frozen.  The modulus `strongThresholdModulus` is the planar (dimension-free) one.

* `spatialMovingField`, `spatial_moving_ode`: the Hamilton field of `spatialHamiltonian` is `C¹` on
  the open collision-free domain, and `IsSpatialMovingSolutionOn` is `KAM.ODE.IsSolutionIn` there.
* M3 `spatialStrongAMD_le_of_tube`: inequality (17), `C(t) ≤ B(I(t)) - δ + n r + Ω_B(r)`.
* M4 `spatial_maximal_global_of_barrier`: a maximal solution that stays in barrier states near an
  end of its interval has that end infinite.
* `spatial_maximal_global_of_tube`: the MAIN-shaped corollary, `n r + Ω_B(r) ≤ δ / 2`.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD KAM.ODE

variable {n : ℕ}

/-- The spatial moving Hamiltonian vector field `X_H` of `spatialHamiltonian ν μ`. -/
def spatialMovingField (ν : Fin n → ℝ) (μ : ℝ) : Phase (n * 3) → Phase (n * 3) :=
  KAM.hamiltonianVectorField (spatialHamiltonian ν μ)

/-- The spatial moving system is an ODE on the open collision-free domain, with a `C¹` field, and
`IsSpatialMovingSolutionOn` is literally `IsSolutionIn` for it. -/
theorem spatial_moving_ode (ν : Fin n → ℝ) (μ : ℝ) :
    IsOpen (spatialCollisionFreeDomain n) ∧
    ContDiffOn ℝ 1 (spatialMovingField ν μ) (spatialCollisionFreeDomain n) ∧
    ∀ (J : Set ℝ) (z : ℝ → Phase (n * 3)), IsSpatialMovingSolutionOn ν μ J z ↔
      IsSolutionIn (spatialMovingField ν μ) (spatialCollisionFreeDomain n) J z := by
  have hW := isOpen_spatialCollisionFreeDomain n
  have hA := analyticOnNhd_spatialHamiltonian ν μ
  refine ⟨hW, KAM.ODE.ham_smooth_c1 hW (hA.contDiffOn hW.uniqueDiffOn), ?_⟩
  intro J z
  constructor
  · rintro ⟨h, hc⟩ t ht
    exact ⟨hc t ht, (h t ht).2.2⟩
  · intro h
    exact ⟨fun t ht => ⟨Set.mem_univ _,
      (analyticOnNhd_spatialHamiltonian ν μ _ (h t ht).1).differentiableAt, (h t ht).2⟩,
      fun t ht => (h t ht).1⟩

/-- M3, inequality (17) (`LP:MAIN L6 (181–183)`, `d = 3`): along a spatial moving solution on an
order-connected `J ∋ 0`, if `C(z 0) ≤ B(Λ(z 0)) - δ` and the actions at `t ∈ J` stay within `r` of
the initial ones, with both action vectors in `U`, then
`C(z t) ≤ B(Λ(z t)) - δ + n r + Ω_B(r)`. -/
theorem spatialStrongAMD_le_of_tube {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {μ : ℝ} {J : Set ℝ}
    (hJ : J.OrdConnected) {z : ℝ → Phase (n * 3)} (hz : IsSpatialMovingSolutionOn ν μ J z)
    (h0 : (0 : ℝ) ∈ J) {t : ℝ} (ht : t ∈ J) {δ r : ℝ}
    (hC0 : spatialStrongAMD ν (z 0) ≤ strongThreshold ν (spatialActionVector ν (z 0)) - δ)
    (hr : ‖spatialActionVector ν (z t) - spatialActionVector ν (z 0)‖ ≤ r)
    (hU0 : spatialActionVector ν (z 0) ∈ U) (hUt : spatialActionVector ν (z t) ∈ U) :
    spatialStrongAMD ν (z t) ≤ strongThreshold ν (spatialActionVector ν (z t)) - δ + n * r +
      strongThresholdModulus ν U r := by
  have hid := spatialStrongAMD_sub_eq_sum hJ hz h0 ht
  have hsum : ∑ i, (spatialKeplerAction ν (z t) i - spatialKeplerAction ν (z 0) i) ≤ n * r := by
    calc ∑ i, (spatialKeplerAction ν (z t) i - spatialKeplerAction ν (z 0) i)
        ≤ ∑ _i : Fin n, r :=
          Finset.sum_le_sum fun i _ => by
            have h1 := norm_le_pi_norm
              (spatialActionVector ν (z t) - spatialActionVector ν (z 0)) i
            rw [Real.norm_eq_abs] at h1
            exact (le_abs_self _).trans (h1.trans hr)
      _ = n * r := by simp
  have hmod := abs_strongThreshold_sub_le_modulus hν hn hUc hUch hU0 hUt
    (r := r) (by rw [norm_sub_rev]; exact hr)
  have hab := (abs_le.1 hmod).2
  linarith

section Maximal

variable {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)}

/-- M4 (`LP:MAIN L6 (181, 187)`, `d = 3`): the maximal solution of the spatial moving field on the
collision-free domain from `x₀` that is a barrier state on `[t_*, Tp)` has `Tp = ⊤`; the mirror
statement backwards has `Tm = ⊥`. -/
theorem spatial_maximal_global_of_barrier (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hUc : IsCompact U)
    (hUch : U ⊆ chamber ν) {m : ℝ} (hm : 0 < m) {μ : ℝ} {x₀ : Phase (n * 3)} {Tm Tp : EReal}
    {z : ℝ → Phase (n * 3)}
    (hz : IsMaximalSolution (spatialMovingField ν μ) (spatialCollisionFreeDomain n) x₀ Tm Tp z) :
    ((∃ t_star : ℝ, 0 ≤ t_star ∧ (t_star : EReal) < Tp ∧
        ∀ t : ℝ, t_star ≤ t → (t : EReal) < Tp → SpatialBarrierState ν U m (z t)) → Tp = ⊤) ∧
    ((∃ t_star : ℝ, t_star ≤ 0 ∧ Tm < (t_star : EReal) ∧
        ∀ t : ℝ, Tm < (t : EReal) → t ≤ t_star → SpatialBarrierState ν U m (z t)) → Tm = ⊥) := by
  obtain ⟨K, hK, hKW, hKs⟩ := exists_spatialBarrierCompact hν hn hUc hUch hm
  obtain ⟨hW, hF, -⟩ := spatial_moving_ode ν μ
  have key := gen_continuation_compact hW hF hz hK hKW
  refine ⟨?_, ?_⟩
  · rintro ⟨ts, h0, h1, h2⟩
    exact key.1 ⟨ts, h0, h1, fun t ht ht' => hKs _ (h2 t ht ht')⟩
  · rintro ⟨ts, h0, h1, h2⟩
    exact key.2 ⟨ts, h0, h1, fun t ht ht' => hKs _ (h2 t ht ht')⟩

/-- MAIN-shaped corollary of M3 and M4 (`LP:MAIN L6 (181, 187)`, `d = 3`): if
`C(x₀) ≤ B(Λ x₀) - δ`, `Λ x₀ ∈ U` and `n r + Ω_B(r) ≤ δ / 2`, then the maximal solution cannot
terminate at a finite time while negative energy, the action tube `‖Λ(z t) - Λ x₀‖ ≤ r` and
`Λ (z t) ∈ U` persist; the same backwards in time. -/
theorem spatial_maximal_global_of_tube (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hUc : IsCompact U)
    (hUch : U ⊆ chamber ν) {μ : ℝ} {x₀ : Phase (n * 3)} {Tm Tp : EReal}
    {z : ℝ → Phase (n * 3)}
    (hz : IsMaximalSolution (spatialMovingField ν μ) (spatialCollisionFreeDomain n) x₀ Tm Tp z)
    {δ r : ℝ} (hδ : 0 < δ) (hrΩ : n * r + strongThresholdModulus ν U r ≤ δ / 2)
    (hC0 : spatialStrongAMD ν x₀ ≤ strongThreshold ν (spatialActionVector ν x₀) - δ)
    (hU0 : spatialActionVector ν x₀ ∈ U) :
    ((∃ t_star : ℝ, 0 ≤ t_star ∧ (t_star : EReal) < Tp ∧ ∀ t : ℝ, t_star ≤ t → (t : EReal) < Tp →
        SpatialNegativeEnergy ν (z t) ∧
          ‖spatialActionVector ν (z t) - spatialActionVector ν x₀‖ ≤ r ∧
          spatialActionVector ν (z t) ∈ U) → Tp = ⊤) ∧
    ((∃ t_star : ℝ, t_star ≤ 0 ∧ Tm < (t_star : EReal) ∧ ∀ t : ℝ, Tm < (t : EReal) → t ≤ t_star →
        SpatialNegativeEnergy ν (z t) ∧
          ‖spatialActionVector ν (z t) - spatialActionVector ν x₀‖ ≤ r ∧
          spatialActionVector ν (z t) ∈ U) → Tm = ⊥) := by
  have hmov : IsSpatialMovingSolutionOn ν μ (eIoo Tm Tp) z :=
    ((spatial_moving_ode ν μ).2.2 _ z).2 hz.isSolution
  have h0 : (0 : ℝ) ∈ eIoo Tm Tp := zero_mem_eIoo hz
  have hz0 : z 0 = x₀ := hz.init
  have hbar : ∀ t : ℝ, t ∈ eIoo Tm Tp →
      (SpatialNegativeEnergy ν (z t) ∧
        ‖spatialActionVector ν (z t) - spatialActionVector ν x₀‖ ≤ r ∧
        spatialActionVector ν (z t) ∈ U) → SpatialBarrierState ν U (δ / 2) (z t) := by
    rintro t ht ⟨hp, hr, hUt⟩
    refine ⟨hp, hUt, ?_⟩
    have := spatialStrongAMD_le_of_tube hν hn hUc hUch (ordConnected_eIoo Tm Tp) hmov h0 ht
      (δ := δ) (r := r) (by rw [hz0]; exact hC0) (by rw [hz0]; exact hr)
      (by rw [hz0]; exact hU0) hUt
    linarith
  have hm : 0 < δ / 2 := half_pos hδ
  have key := spatial_maximal_global_of_barrier hν hn hUc hUch hm hz
  refine ⟨?_, ?_⟩
  · rintro ⟨ts, h0', h1, h2⟩
    refine key.1 ⟨ts, h0', h1, fun t ht ht' => hbar t ⟨?_, ht'⟩ (h2 t ht ht')⟩
    exact lt_of_lt_of_le hz.neg_lt (by exact_mod_cast h0'.trans ht)
  · rintro ⟨ts, h0', h1, h2⟩
    refine key.2 ⟨ts, h0', h1, fun t ht ht' => hbar t ⟨ht, ?_⟩ (h2 t ht ht')⟩
    exact lt_of_le_of_lt (by exact_mod_cast ht'.trans h0') hz.pos_lt

end Maximal

end KAM.Planetary.Spatial

end
