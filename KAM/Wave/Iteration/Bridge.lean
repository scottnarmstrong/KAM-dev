/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.K0
public import KAM.Wave.Homological.WaveReindex
public import KAM.Wave.Homological.LatticeBW
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: W7's normal-mode index versus W5's (`bpW:w6:iter-lemma`, `bpW:w4:wave` (ii))

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:iter-lemma` (milestone W6): the Melnikov conditions
`(bpW:w6:melnikov)` are stated with W7's index set `Z`, Dirichlet weight `⟨l⟩` and `A_k`; W5's step
uses W4's index set `𝒵`, P96-K's bracket and `A_k`. By Lemma `bpW:w4:wave` (ii) the former imply the
latter at the same level.

W7 indexes normal modes by `n : ℕ` (Dirichlet label `n + 3`), W5 by `j : ℕ+` (label `j + 2`); the
two are matched by `j = n + 1` (`Equiv.pnatEquivNat`). For `Ω : ℕ+ → ℝ`,
`w6Om7 Ω n = Ω (n + 1)`, and
for `l : ℕ+ →₀ ℤ`, `w6L7 l = l ∘ (· + 1)⁻¹`.

* `W6Mel a Par ω Ω`: the conditions `(bpW:w6:melnikov)` at level `a` on `Par` (W7 index);
* `w6_homMelnikov_of_mel`: they imply W5's `HomMelnikov 24 a` for the W5-indexed frequencies.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- W7's normal frequencies `n ↦ Ω (n + 1)` of W5-indexed `Ω : ℕ+ → ℝ`. -/
def w6Om7 (Ω : ℕ+ → ℝ) : ℕ → ℝ := fun n => Ω n.succPNat

/-- W7's index vector of a W5 index vector `l : ℕ+ →₀ ℤ`. -/
def w6L7 (l : ℕ+ →₀ ℤ) : ℕ →₀ ℤ := Finsupp.equivMapDomain Equiv.pnatEquivNat l

/-- The Melnikov conditions `(bpW:w6:melnikov)` at level `a` on `Par`, with W7's index set `Z`,
Dirichlet weight `⟨l⟩` and `A_k = 1 + |k|^{24}`: `|⟨k, ω⟩ + ⟨l, Ω⟩| ≥ a ⟨l⟩ / A_k`. -/
def W6Mel (a : ℝ) (Par : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω : (Fin 2 → ℝ) → ℕ → ℝ) : Prop :=
  ∀ ξ ∈ Par, ∀ (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ), InZ k l →
    a * japL l / kAk k ≤ |∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)|

theorem w6L7_apply (l : ℕ+ →₀ ℤ) (n : ℕ) : w6L7 l n = l n.succPNat := rfl

theorem w6L7_sum {M : Type*} [AddCommMonoid M] (l : ℕ+ →₀ ℤ) (g : ℕ → ℤ → M) :
    (w6L7 l).sum g = l.sum fun j v => g j.natPred v := by
  unfold w6L7
  rw [Finsupp.sum_equivMapDomain]
  rfl

theorem w6L7_eq_zero_iff (l : ℕ+ →₀ ℤ) : w6L7 l = 0 ↔ l = 0 := by
  constructor
  · intro h
    ext j
    have := congrArg (fun f => f j.natPred) h
    simpa [w6L7_apply] using this
  · rintro rfl; simp [w6L7]

theorem l1Norm_w6L7 (l : ℕ+ →₀ ℤ) : l1Norm (w6L7 l) = homL1 l := by
  unfold l1Norm homL1
  rw [w6L7_sum]

theorem linF_w6L7 (l : ℕ+ →₀ ℤ) (Ω : ℕ+ → ℝ) : linF (w6L7 l) (w6Om7 Ω) = homPairL l Ω := by
  unfold linF homPairL
  rw [w6L7_sum]
  unfold w6Om7
  refine Finsupp.sum_congr fun j _ => ?_
  rw [PNat.succPNat_natPred]

theorem japL_w6L7 (l : ℕ+ →₀ ℤ) : japL (w6L7 l) = (homJapW l : ℝ) := by
  unfold japL homJapW
  have e : linF (w6L7 l) normLab = ((l.sum fun j n => ((j : ℤ) + 2) * n : ℤ) : ℝ) := by
    unfold linF
    rw [w6L7_sum]
    unfold Finsupp.sum
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold normLab
    have : ((j.natPred : ℕ) : ℝ) = (j : ℝ) - 1 := by
      have h := PNat.natPred_add_one j
      have : ((j.natPred : ℕ) : ℝ) + 1 = ((j : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    rw [this]; ring
  rw [e, Nat.cast_max, Nat.cast_one, Nat.cast_natAbs, Int.cast_abs]

theorem kAbs_eq_modeSize (k : Fin 2 → ℤ) : kAbs k = Fourier.modeSize k := rfl

theorem kAk_eq_waveA (k : Fin 2 → ℤ) : kAk k = waveA 24 k := by
  unfold kAk waveA
  split_ifs with hk
  · subst hk; simp [kAbs]
  · rw [kAbs_eq_modeSize, show (24 : ℝ) = ((24 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem homPairZ_eq_sum (k : Fin 2 → ℤ) (v : Fin 2 → ℝ) :
    homPairZ k v = ∑ i, (k i : ℝ) * v i := rfl

/-- `(k, l) ∈ 𝒵` (W4) gives `(k, l_7) ∈ Z` (W7). -/
theorem inZ_w6L7 {p : (Fin 2 → ℤ) × (ℕ+ →₀ ℤ)} (hp : p ∈ homZ) : InZ p.1 (w6L7 p.2) := by
  obtain ⟨hne, h2⟩ := hp
  refine ⟨?_, ?_⟩
  · by_cases h0 : p.2 = 0
    · left; rw [h0]; simp [w6L7]
    · right
      refine ⟨?_, by rw [l1Norm_w6L7]; exact h2⟩
      rw [l1Norm_w6L7]
      exact Nat.one_le_iff_ne_zero.mpr fun h => h0 ((homL1_eq_zero_iff _).1 h)
  · by_cases hk : p.1 = 0
    · right
      intro h
      rw [w6L7_eq_zero_iff] at h
      exact hne (Prod.ext hk h)
    · left; exact hk

/-- **Bridge** (blueprint `bpW:w4:wave` (ii), as used in `bpW:w6:iter-lemma`, step `il-small`):
the conditions `(bpW:w6:melnikov)` at level `a > 0` imply W5's `(H_a)` with `τ = 24`. -/
theorem w6_homMelnikov_of_mel {a : ℝ} (ha : 0 < a) {Par : Set (Fin 2 → ℝ)}
    {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
    (h : W6Mel a Par ω (fun ξ => w6Om7 (Ω ξ))) : HomMelnikov 24 a Par ω Ω := by
  refine homMelnikov_of_melnikovW ha ?_
  intro ξ hξ p hp
  have := h ξ hξ p.1 (w6L7 p.2) (inZ_w6L7 hp)
  rwa [japL_w6L7, linF_w6L7, kAk_eq_waveA, ← homPairZ_eq_sum] at this

end KAM.Wave
