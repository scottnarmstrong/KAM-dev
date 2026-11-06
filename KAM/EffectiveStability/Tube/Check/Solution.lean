/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.ODE.Maximal
public import KAM.ODE.Hamiltonian

/-!
# From a maximal solution to existence and uniqueness (T2-CONF, N5b)

The confinement theorem of `KAM/Application/Confinement/ApproxIntegral.lean` returns a maximal
solution `(Tm, Tp, z)` of `ẋ = X_H x` **in an open set `W`** (for the tube checker: all rotated
modes nonzero). The T2-CONF statement asserts existence on `(-T₁, T₁)` and uniqueness among **all**
solutions on intervals through `0`, with no constraint to stay in `W`. For an `H` of class `C²` on
the whole phase space (a polynomial), this follows by comparing with the maximal solution in `univ`:

* `hamiltonian_solution_of_maximal`: from `IsMaximalSolution X_H W z₀ Tm Tp z` with `Tm < -T` and
  `T < Tp`, there is a real `T₁ > T` with `(-T₁, T₁) ⊆ (Tm, Tp)`, `z` solves on `(-T₁, T₁)`, and
  every solution `y` through `z₀` on an order-connected `I ∋ 0` agrees with `z` on `I ∩ (-T₁, T₁)`.

This is the generic part of the Hénon–Heiles conversion (`henonHeiles_confinement_proof`).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Set KAM.ODE

variable {n : ℕ}

/-- **Existence and uniqueness from a maximal solution in an open set.** -/
theorem hamiltonian_solution_of_maximal {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hH : ContDiff ℝ 2 H)
    {W : Set ((Fin n → ℝ) × (Fin n → ℝ))} {z₀ : (Fin n → ℝ) × (Fin n → ℝ)} {Tm Tp : EReal}
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} {T : ℝ}
    (hz : IsMaximalSolution (KAM.hamiltonianVectorField H) W z₀ Tm Tp z)
    (hTm : Tm < ((-T : ℝ) : EReal)) (hTp : ((T : ℝ) : EReal) < Tp) :
    ∃ T₁ : ℝ, T < T₁ ∧ Ioo (-T₁) T₁ ⊆ eIoo Tm Tp ∧ z 0 = z₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ → (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) := by
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hTp
  obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.1 hTm
  have hTr : T < r := EReal.coe_lt_coe_iff.1 hr1
  have hqT : q < -T := EReal.coe_lt_coe_iff.1 hq2
  have hsub : Ioo (-min r (-q)) (min r (-q)) ⊆ eIoo Tm Tp := fun t ht => by
    refine ⟨lt_trans hq1 (EReal.coe_lt_coe_iff.2 ?_), lt_trans (EReal.coe_lt_coe_iff.2 ?_) hr2⟩
    · have := ht.1; have := min_le_right r (-q); linarith
    · have := ht.2; have := min_le_left r (-q); linarith
  -- the maximal solution in the whole space
  have hX : ContDiffOn ℝ 1 (KAM.hamiltonianVectorField H) univ :=
    ham_smooth_c1 isOpen_univ hH.contDiffOn
  obtain ⟨Tm', Tp', z', hz'⟩ := (gen_maximal isOpen_univ hX (mem_univ z₀)).1
  have hzz' : EqOn z z' (eIoo Tm Tp) :=
    (hz'.maximal (eIoo Tm Tp) z (ordConnected_eIoo _ _) (zero_mem_eIoo hz) hz.init
      fun t ht => ⟨mem_univ _, (hz.isSolution t ht).2⟩).2
  refine ⟨min r (-q), lt_min hTr (by linarith), hsub, hz.init,
    fun t ht => (hz.isSolution t (hsub ht)).2, ?_⟩
  intro I y hI h0 hy0 hyd t htI htT
  have hyz' : EqOn y z' I :=
    (hz'.maximal I y hI h0 hy0 fun t ht => ⟨mem_univ _, hyd t ht⟩).2
  rw [hyz' htI, hzz' (hsub htT)]

end KAM.EffectiveStability.Tube

end
