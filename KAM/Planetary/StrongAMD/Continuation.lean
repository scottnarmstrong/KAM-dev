/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Continuation
public import KAM.Planetary.AMD.MovingODE
public import KAM.Planetary.StrongAMD.Geometry
public import KAM.Planetary.StrongAMD.Modulus

/-!
# The moving threshold (17) and continuation

Source: `LP:MAIN L6 (177–189)` with amendment N2 (one shared compact `U`); track LP,
non-frozen.

* M3 `strongAMD_le_of_tube`: inequality (17), `C(t) ≤ B(I(t)) - δ + n r + Ω_B(r)`.
* M4 `maximal_global_of_barrier`: the maximal solution of the moving field on the collision-free
  domain that stays in barrier states near an end of its interval has that end infinite.
* `maximal_global_of_tube`: the MAIN-shaped corollary, with `n r + Ω_B(r) ≤ δ / 2`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary KAM.ODE

variable {n : ℕ}

/-- The moving Hamiltonian vector field `X_H` of `movingHamiltonian 1 1 ν μ`. -/
def movingField (ν : Fin n → ℝ) (μ : ℝ) : Phase (n * 2) → Phase (n * 2) :=
  KAM.hamiltonianVectorField (movingHamiltonian 1 1 ν μ)

/-- M3, inequality (17) (`LP:MAIN L6 (181–183)`): along a moving solution on an order-connected
`J ∋ 0`, if `C(z 0) ≤ B(Λ(z 0)) - δ` and the actions at `t ∈ J` stay within `r` of the initial
ones, with both action vectors in `U`, then
`C(z t) ≤ B(Λ(z t)) - δ + n r + Ω_B(r)`.  (No physical-state or `𝓛`-membership premise is
needed: the identity (13) is `strongAMD_sub_eq_sum`.) -/
theorem strongAMD_le_of_tube {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {μ : ℝ} {J : Set ℝ}
    (hJ : J.OrdConnected) {z : ℝ → Phase (n * 2)} (hz : IsMovingSolutionOn ν μ J z)
    (h0 : (0 : ℝ) ∈ J) {t : ℝ} (ht : t ∈ J) {δ r : ℝ}
    (hC0 : strongAMD ν (z 0) ≤ strongThreshold ν (actionVector ν (z 0)) - δ)
    (hr : ‖actionVector ν (z t) - actionVector ν (z 0)‖ ≤ r)
    (hU0 : actionVector ν (z 0) ∈ U) (hUt : actionVector ν (z t) ∈ U) :
    strongAMD ν (z t) ≤ strongThreshold ν (actionVector ν (z t)) - δ + n * r +
      strongThresholdModulus ν U r := by
  have hid := strongAMD_sub_eq_sum hJ hz h0 ht
  have hsum : ∑ i, (keplerAction ν (z t) i - keplerAction ν (z 0) i) ≤ n * r := by
    calc ∑ i, (keplerAction ν (z t) i - keplerAction ν (z 0) i) ≤ ∑ _i : Fin n, r :=
          Finset.sum_le_sum fun i _ => by
            have h1 := norm_le_pi_norm (actionVector ν (z t) - actionVector ν (z 0)) i
            rw [Real.norm_eq_abs] at h1
            exact (le_abs_self _).trans (h1.trans hr)
      _ = n * r := by simp
  have hmod := abs_strongThreshold_sub_le_modulus hν hn hUc hUch hU0 hUt
    (r := r) (by rw [norm_sub_rev]; exact hr)
  have hab := (abs_le.1 hmod).2
  linarith

section Maximal

variable {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)}

/-- M4 (`LP:MAIN L6 (181, 187)`): the maximal solution of the moving field on the collision-free
domain from `x₀` that is a barrier state on `[t_*, Tp)` has `Tp = ⊤`; the mirror statement
backwards has `Tm = ⊥`. -/
theorem maximal_global_of_barrier (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hUc : IsCompact U)
    (hUch : U ⊆ chamber ν) {m : ℝ} (hm : 0 < m) {μ : ℝ} {x₀ : Phase (n * 2)} {Tm Tp : EReal}
    {z : ℝ → Phase (n * 2)}
    (hz : IsMaximalSolution (movingField ν μ) (collisionFreeDomain n) x₀ Tm Tp z) :
    ((∃ t_star : ℝ, 0 ≤ t_star ∧ (t_star : EReal) < Tp ∧
        ∀ t : ℝ, t_star ≤ t → (t : EReal) < Tp → BarrierState ν U m (z t)) → Tp = ⊤) ∧
    ((∃ t_star : ℝ, t_star ≤ 0 ∧ Tm < (t_star : EReal) ∧
        ∀ t : ℝ, Tm < (t : EReal) → t ≤ t_star → BarrierState ν U m (z t)) → Tm = ⊥) := by
  obtain ⟨K, hK, hKW, hKs⟩ := exists_barrierCompact hν hn hUc hUch hm
  obtain ⟨hW, hF, -⟩ := moving_ode ν μ
  have key := gen_continuation_compact hW hF hz hK hKW
  refine ⟨?_, ?_⟩
  · rintro ⟨ts, h0, h1, h2⟩
    exact key.1 ⟨ts, h0, h1, fun t ht ht' => hKs _ (h2 t ht ht')⟩
  · rintro ⟨ts, h0, h1, h2⟩
    exact key.2 ⟨ts, h0, h1, fun t ht ht' => hKs _ (h2 t ht ht')⟩

/-- MAIN-shaped corollary of M3 and M4 (`LP:MAIN L6 (181, 187)`): if
`C(x₀) ≤ B(Λ x₀) - δ`, `Λ x₀ ∈ U` and `n r + Ω_B(r) ≤ δ / 2`, then the maximal solution cannot
terminate at a finite time while the physical state, the action tube
`‖Λ(z t) - Λ x₀‖ ≤ r` and `Λ (z t) ∈ U` persist; the same backwards in time. -/
theorem maximal_global_of_tube (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hUc : IsCompact U)
    (hUch : U ⊆ chamber ν) {μ : ℝ} {x₀ : Phase (n * 2)} {Tm Tp : EReal} {z : ℝ → Phase (n * 2)}
    (hz : IsMaximalSolution (movingField ν μ) (collisionFreeDomain n) x₀ Tm Tp z)
    {δ r : ℝ} (hδ : 0 < δ) (hrΩ : n * r + strongThresholdModulus ν U r ≤ δ / 2)
    (hC0 : strongAMD ν x₀ ≤ strongThreshold ν (actionVector ν x₀) - δ)
    (hU0 : actionVector ν x₀ ∈ U) :
    ((∃ t_star : ℝ, 0 ≤ t_star ∧ (t_star : EReal) < Tp ∧ ∀ t : ℝ, t_star ≤ t → (t : EReal) < Tp →
        IsPhysicalState ν (z t) ∧ ‖actionVector ν (z t) - actionVector ν x₀‖ ≤ r ∧
          actionVector ν (z t) ∈ U) → Tp = ⊤) ∧
    ((∃ t_star : ℝ, t_star ≤ 0 ∧ Tm < (t_star : EReal) ∧ ∀ t : ℝ, Tm < (t : EReal) → t ≤ t_star →
        IsPhysicalState ν (z t) ∧ ‖actionVector ν (z t) - actionVector ν x₀‖ ≤ r ∧
          actionVector ν (z t) ∈ U) → Tm = ⊥) := by
  have hmov : IsMovingSolutionOn ν μ (eIoo Tm Tp) z :=
    ((moving_ode ν μ).2.2 _ z).2 hz.isSolution
  have h0 : (0 : ℝ) ∈ eIoo Tm Tp := zero_mem_eIoo hz
  have hz0 : z 0 = x₀ := hz.init
  have hbar : ∀ t : ℝ, t ∈ eIoo Tm Tp →
      (IsPhysicalState ν (z t) ∧ ‖actionVector ν (z t) - actionVector ν x₀‖ ≤ r ∧
        actionVector ν (z t) ∈ U) → BarrierState ν U (δ / 2) (z t) := by
    rintro t ht ⟨hp, hr, hUt⟩
    refine ⟨hp, hUt, ?_⟩
    have := strongAMD_le_of_tube hν hn hUc hUch (ordConnected_eIoo Tm Tp) hmov h0 ht
      (δ := δ) (r := r) (by rw [hz0]; exact hC0) (by rw [hz0]; exact hr)
      (by rw [hz0]; exact hU0) hUt
    linarith
  have hm : 0 < δ / 2 := half_pos hδ
  have key := maximal_global_of_barrier hν hn hUc hUch hm hz
  refine ⟨?_, ?_⟩
  · rintro ⟨ts, h0', h1, h2⟩
    refine key.1 ⟨ts, h0', h1, fun t ht ht' => hbar t ⟨?_, ht'⟩ (h2 t ht ht')⟩
    exact lt_of_lt_of_le hz.neg_lt (by exact_mod_cast h0'.trans ht)
  · rintro ⟨ts, h0', h1, h2⟩
    refine key.2 ⟨ts, h0', h1, fun t ht ht' => hbar t ⟨ht, ?_⟩ (h2 t ht ht')⟩
    exact lt_of_le_of_lt (by exact_mod_cast ht'.trans h0') hz.pos_lt

end Maximal

end KAM.Planetary.StrongAMD
