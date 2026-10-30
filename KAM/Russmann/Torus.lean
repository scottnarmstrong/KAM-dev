/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Hamiltonian.Transport
public import KAM.Frozen.Defs.IsInvariantLagrangianTorus

/-!
# Track R: lattice tori are frozen invariant Lagrangian tori

Track P's family of tori (`KAM.Planetary.QuantitativeFamily.lattice`) is stated with
`KAM.Planetary.IsLatticeTorus angleShift`, which differs from the frozen
`KAM.IsInvariantLagrangianTorus` only in two clauses: it also records that the torus lies in a
domain `O` where `H` is differentiable, and its embeddedness clause reads
`K θ = K θ' → θ' ∈ θ + ℤⁿ` instead of `K θ' = K θ + (k, 0) → θ' = θ + k`.
`isInvariantLagrangianTorus_of_isLatticeTorus` converts the first form into the second.
-/

@[expose] public section

namespace KAM.Russmann

open KAM KAM.Planetary KAM.ODE

variable {n : ℕ}

/-- A lattice torus with lattice `angleShift` (track P, `bpP:p1:lattice-torus`) is an invariant
Lagrangian torus in the sense of the frozen `KAM.IsInvariantLagrangianTorus`. -/
theorem isInvariantLagrangianTorus_of_isLatticeTorus
    {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {O : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {ω : Fin n → ℝ} {K : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hK : IsLatticeTorus angleShift H O ω K) : IsInvariantLagrangianTorus H ω K := by
  obtain ⟨⟨han, -⟩, hlat, hinj, himm, hlag, hflow⟩ := hK
  refine ⟨han, hlat, fun θ θ' k hk => ?_, himm, hlag, hflow⟩
  have h1 : K (θ + fun i => (k i : ℝ)) = K θ' := by rw [hlat θ k]; exact hk.symm
  obtain ⟨l, hl⟩ := hinj _ _ h1
  have h2 : K θ' = K θ' + angleShift l := by
    calc K θ' = K ((θ + fun i => (k i : ℝ)) + fun i => (l i : ℝ)) := by rw [← hl]
      _ = K θ' + angleShift l := by rw [hlat _ l, h1]
  have h3 : (fun i => (l i : ℝ)) = 0 := by
    have := congrArg Prod.fst h2
    simpa [angleShift] using this
  rw [hl, h3, add_zero]

end KAM.Russmann

end
