/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LatticeBW
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.PNat.Basic

/-!
# Frequencies, divisors and Melnikov conditions (blueprint-W `bpW:w4:melnikov`)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

Normal modes carry the P96-K index `j ≥ 1` (`ℕ+`), the wave mode being `J = j + 2`
(blueprint `bpW:w4:index`). `ω : (Fin 2 → ℝ) → Fin 2 → ℝ` and `Ω : (Fin 2 → ℝ) → ℕ+ → ℝ` are the
frequencies, on the parameter set `Π`. Integer vectors `l ∈ ℤ^{ℕ₊}` with finite support are
`ℕ+ →₀ ℤ`; `homPairZ k v = ⟨k, v⟩`, `homL1 l = |l|`, `homJap l = ⟨l⟩ = max(1, |∑ j l_j|)`.
`HomFreqHyp` is (`bpW:w4:freq`), `HomMelnikov` the conditions `(H_α)` and the six divisors with
their
weights follow Definition `bpW:w4:melnikov`.
-/

@[expose] public section

namespace KAM.Wave

/-- The pairing `⟨k, v⟩ = k₁v₁ + k₂v₂` of an integer and a real vector of `ℝ²`. -/
noncomputable def homPairZ (k : Fin 2 → ℤ) (v : Fin 2 → ℝ) : ℝ := ∑ i, (k i : ℝ) * v i

/-- `|l| = ∑_j |l_j|` for finitely supported `l ∈ ℤ^{ℕ₊}`. -/
def homL1 (l : ℕ+ →₀ ℤ) : ℕ := l.sum fun _ n => n.natAbs

/-- `⟨l⟩ = max(1, |∑_j j l_j|)` (the P96-K index `j`, `d = 1`). -/
def homJap (l : ℕ+ →₀ ℤ) : ℕ := max 1 (l.sum fun j n => (j : ℤ) * n).natAbs

/-- `⟨l, Ω⟩ = ∑_j l_j Ω_j`. -/
noncomputable def homPairL (l : ℕ+ →₀ ℤ) (Ω : ℕ+ → ℝ) : ℝ := l.sum fun j n => (n : ℝ) * Ω j

/-- The index set `𝒵 = {(k,l) : (k,l) ≠ 0, |l| ≤ 2}` (blueprint `bpW:w4:melnikov`). -/
def homZ : Set ((Fin 2 → ℤ) × (ℕ+ →₀ ℤ)) := {p | p ≠ 0 ∧ homL1 p.2 ≤ 2}

/-- **Frequency hypotheses** (blueprint `bpW:w4:freq`): `Ω_j = j + 2 + Ω̃_j`, `j |Ω̃_j| ≤ M₀`,
`ω` is `M_ω`-Lipschitz and `j |Ω_j(ξ) - Ω_j(ζ)| ≤ M_Ω |ξ - ζ|`, on `Π`, with max norms. -/
structure HomFreqHyp (Par : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) (M0 Mω MΩ : ℝ) : Prop where
  nonneg : 0 ≤ M0 ∧ 0 ≤ Mω ∧ 0 ≤ MΩ
  tail : ∀ ξ ∈ Par, ∀ j : ℕ+, (j : ℝ) * |Ω ξ j - ((j : ℝ) + 2)| ≤ M0
  lipOmega : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ‖ω ξ - ω ζ‖ ≤ Mω * ‖ξ - ζ‖
  lipTail : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ j : ℕ+, (j : ℝ) * |Ω ξ j - Ω ζ j| ≤ MΩ * ‖ξ - ζ‖

/-- **Melnikov conditions** `(H_α)` (blueprint `bpW:w4:melnikov`):
`|⟨k,ω(ξ)⟩ + ⟨l,Ω(ξ)⟩| ≥ α ⟨l⟩ / A_k` for all `ξ ∈ Par` and `(k,l) ∈ 𝒵`. -/
def HomMelnikov (τ α : ℝ) (Par : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) : Prop :=
  ∀ ξ ∈ Par, ∀ p ∈ homZ, α * (homJap p.2 : ℝ) / waveA τ p.1 ≤
    |homPairZ p.1 (ω ξ) + homPairL p.2 (Ω ξ)|

/-- The divisor `δ^0_k = ⟨k, ω⟩`. -/
noncomputable def homDelta0 (ω : Fin 2 → ℝ) (k : Fin 2 → ℤ) : ℝ := homPairZ k ω

/-- The divisor `δ^+_{k,j} = ⟨k,ω⟩ - Ω_j`. -/
noncomputable def homDeltaPlus (ω : Fin 2 → ℝ) (Ω : ℕ+ → ℝ) (k : Fin 2 → ℤ) (j : ℕ+) : ℝ :=
  homPairZ k ω - Ω j

/-- The divisor `δ^-_{k,j} = ⟨k,ω⟩ + Ω_j`. -/
noncomputable def homDeltaMinus (ω : Fin 2 → ℝ) (Ω : ℕ+ → ℝ) (k : Fin 2 → ℤ) (j : ℕ+) : ℝ :=
  homPairZ k ω + Ω j

/-- The divisor `δ^P_{k,ij} = ⟨k,ω⟩ - Ω_i - Ω_j`. -/
noncomputable def homDeltaP (ω : Fin 2 → ℝ) (Ω : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) : ℝ :=
  homPairZ k ω - Ω i - Ω j

/-- The divisor `δ^{P'}_{k,ij} = ⟨k,ω⟩ + Ω_i + Ω_j`. -/
noncomputable def homDeltaP' (ω : Fin 2 → ℝ) (Ω : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) : ℝ :=
  homPairZ k ω + Ω i + Ω j

/-- The divisor `δ^Q_{k,ij} = ⟨k,ω⟩ + Ω_i - Ω_j` (used for `(k,i) ≠ (0,j)`). -/
noncomputable def homDeltaQ (ω : Fin 2 → ℝ) (Ω : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) : ℝ :=
  homPairZ k ω + Ω i - Ω j

/-- The weight `w^Q_{ij} = max(1, |i - j|)`. -/
def homWeightQ (i j : ℕ+) : ℕ := max 1 ((i : ℤ) - j).natAbs

end KAM.Wave
