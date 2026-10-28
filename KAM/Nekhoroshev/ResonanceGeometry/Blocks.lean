/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.ResonanceGeometry.Maximal

/-!
# Zones, strata and blocks (`bpN:p8:blocks`, `bpN:p8:blocks-cover`)

The zone of a maximal `K`-lattice, the strata `Z*_d`, the blocks `B_Λ = Z_Λ ∖ Z*_{d+1}`, and the
covering of frequency space by finitely many blocks. The covering is the chain argument: take the
largest occupied positive dimension, with `Θ = ⊥` as the empty-strata case.
-/

@[expose] public noncomputable section
open Set Matrix Module Classical

namespace KAM.Nekhoroshev
variable {n : ℕ}

/-- λ is indexed by natural dimensions; only 1,...,n are consumed. -/
def zone (lam : ℕ → ℝ) (Λ : Lattice n) : Set (Fin n → ℝ) :=
  if Λ = ⊥ then univ else {w | resonanceDistance Λ w < lam (latticeDim Λ) / volume_def Λ}

def zoneStratum (K : ℝ) (lam : ℕ → ℝ) (d : ℕ) : Set (Fin n → ℝ) :=
  {w | 1 ≤ d ∧ d ≤ n ∧ ∃ Λ : Lattice n, maximalK K Λ ∧ latticeDim Λ = d ∧ w ∈ zone lam Λ}

def blocks (K : ℝ) (lam : ℕ → ℝ) (Λ : Lattice n) : Set (Fin n → ℝ) :=
  zone lam Λ \ zoneStratum K lam (latticeDim Λ + 1)

theorem blocks_cover {K : ℝ} (hK : 0 ≤ K) (lam : ℕ → ℝ)
    (hlam : ∀ d, 1 ≤ d → d ≤ n → 0 < lam d) :
    {Λ : Lattice n | maximalK K Λ}.Finite ∧
    ∀ w : Fin n → ℝ, ∃ Λ : Lattice n, maximalK K Λ ∧ w ∈ blocks K lam Λ := by
  refine ⟨(klattice_finite (n := n) K).subset fun Λ hΛ => hΛ.1, fun w => ?_⟩
  by_cases hD : ∃ d, w ∈ zoneStratum K lam d
  · classical
    have hbdd : ∀ d, w ∈ zoneStratum K lam d → d ≤ n := fun d hd => hd.2.1
    let D : Set ℕ := {d | w ∈ zoneStratum K lam d}
    have hne : D.Nonempty := hD
    have hbd : BddAbove D := ⟨n, hbdd⟩
    have hdD : sSup D ∈ D := Nat.sSup_mem hne hbd
    have hdmax : ∀ e ∈ D, e ≤ sSup D := fun e he => le_csSup hbd he
    generalize sSup D = d at hdD hdmax
    obtain ⟨h1, hdn, Λ, hΛ, hdim, hw⟩ := hdD
    refine ⟨Λ, hΛ, hw, ?_⟩
    rw [hdim]
    intro h
    have := hdmax _ h
    omega
  · push Not at hD
    refine ⟨⊥, maximalK_bot K, ?_, hD _⟩
    simp [zone]

end KAM.Nekhoroshev
