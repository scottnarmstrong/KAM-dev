/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Constants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Arithmetic of the constants of route A

* `StepInA.Pos`: the well-formedness of the inputs (audit finding F1: nothing is claimed for
  degenerate data);
* `StepInA.Pos.nonneg`: nonnegativity of the constants;
* `pow_mul_rpow_le`: `γ^i δ^j ≤ γ̄^i D^j`, the only place where the actual `(γ, δ)` meet the values
  `(γ̄, D)` used in the constants;
* `scales`: the relations between the normalised errors `u = ε/(γδ^κ)`, `E = ε/(γ²δ^{2κ})`,
  `X = ε/(γ²δ^{2κ+1})` and `x = ε/(γ⁴δ^{4κ})`.
-/

@[expose] public noncomputable section

namespace KAM.Sharp2.RouteA

/-- Well-formed inputs of a step. -/
structure StepInA.Pos (p : StepInA) : Prop where
  n_pos : 1 ≤ p.n
  κ_ge : 1 ≤ p.κ
  M1 : 0 ≤ p.M1
  M2 : 0 ≤ p.M2
  sK : 0 ≤ p.sK
  sB : 0 ≤ p.sB
  sT : 0 ≤ p.sT
  sLt : 0 ≤ p.sLt
  sN : 0 ≤ p.sN
  sNt : 0 ≤ p.sNt
  t : 0 ≤ p.t
  c : 0 ≤ p.c
  ca : 0 ≤ p.ca
  γb : 0 < p.γb
  δ : 0 < p.δ
  δ1 : p.δ ≤ 1
  th0 : 0 < p.th
  th1 : p.th < 1
  Θ : 0 ≤ p.Θ
  HY : 0 ≤ p.HY
  Mh2 : 0 ≤ p.Mh2

namespace StepInA

variable {p : StepInA}

theorem Pos.n_cast (hp : p.Pos) : (1 : ℝ) ≤ p.n := by exact_mod_cast hp.n_pos

theorem Pos.g (hp : p.Pos) : 0 ≤ p.g :=
  mul_nonneg hp.γb.le (Real.rpow_nonneg hp.δ.le _)

theorem Pos.COm (hp : p.Pos) : 0 ≤ p.COm := by
  have h1 : 0 ≤ (p.n : ℝ) - 1 := by linarith [hp.n_cast]
  have := hp.c
  have := hp.sLt
  unfold StepInA.COm
  positivity

theorem Pos.CSym (hp : p.Pos) : 0 ≤ p.CSym :=
  mul_nonneg (le_max_of_le_left zero_le_one) hp.COm

theorem Pos.CRed (hp : p.Pos) : 0 ≤ p.CRed :=
  mul_nonneg (Nat.cast_nonneg _) (le_max_of_le_left hp.sNt)

theorem Pos.w (hp : p.Pos) : 0 ≤ p.w := by
  have := hp.M1
  have := hp.sLt
  have := hp.sK
  unfold StepInA.w
  positivity

theorem Pos.CS (hp : p.Pos) : 0 ≤ p.CS := by
  have := hp.g
  have := hp.sNt
  have := hp.t
  have := hp.ca
  have := hp.sLt
  have := hp.sT
  unfold StepInA.CS
  split_ifs
  · exact mul_nonneg hp.sT (le_max_of_le_left (by positivity))
  · positivity

theorem Pos.CXiN (hp : p.Pos) : 0 ≤ p.CXiN :=
  add_nonneg hp.CS (mul_nonneg hp.c hp.sLt)

theorem Pos.CG (hp : p.Pos) : 0 ≤ p.CG :=
  add_nonneg (add_nonneg (mul_nonneg hp.t hp.CXiN) (mul_nonneg hp.Θ hp.CS))
    (mul_nonneg hp.sNt hp.g)

theorem Pos.CDXi (hp : p.Pos) : 0 ≤ p.CDXi := le_max_of_le_left hp.CG

theorem Pos.CXi (hp : p.Pos) : 0 ≤ p.CXi := le_max_of_le_left (mul_nonneg hp.c hp.CG)

theorem Pos.CDK (hp : p.Pos) : 0 ≤ p.CDK :=
  add_nonneg (mul_nonneg (mul_nonneg hp.sK hp.c) hp.CG) (mul_nonneg (mul_nonneg hp.sN hp.g) hp.CXiN)

theorem Pos.CLin (hp : p.Pos) : 0 ≤ p.CLin :=
  add_nonneg (add_nonneg (mul_nonneg hp.CRed hp.CXi) (mul_nonneg hp.CSym hp.CDXi))
    (mul_nonneg (mul_nonneg hp.Θ hp.COm) hp.CS)

theorem Pos.P (hp : p.Pos) : 0 ≤ p.P := add_nonneg hp.sK hp.sN

theorem Pos.CDw (hp : p.Pos) : 0 ≤ p.CDw := mul_nonneg (mul_nonneg hp.Θ hp.g) hp.CS

theorem Pos.CFr (hp : p.Pos) : 0 ≤ p.CFr := by
  have := hp.M1
  have := hp.sK
  have := hp.sB
  have := hp.sN
  have := hp.sLt
  unfold StepInA.CFr
  positivity

theorem Pos.CdK (hp : p.Pos) : 0 ≤ p.CdK :=
  add_nonneg (mul_nonneg hp.CFr hp.CXi) (mul_nonneg (mul_nonneg hp.P hp.g) hp.CDXi)

theorem Pos.CE1 (hp : p.Pos) : 0 ≤ p.CE1 := by
  have h0 : 0 ≤ p.δ ^ (2 * p.κ - 1) := Real.rpow_nonneg hp.δ.le _
  have h1 := hp.P
  have h2 := hp.CLin
  have h3 := hp.M2
  have h4 := hp.γb
  have h5 : 0 ≤ (if p.iso then p.g * p.CS * p.CdK else 0) := by
    split_ifs
    · exact mul_nonneg (mul_nonneg hp.g hp.CS) hp.CdK
    · exact le_rfl
  unfold StepInA.CE1
  positivity

theorem Pos.CE2 (hp : p.Pos) : 0 ≤ p.CE2 := by
  have h0 : 0 ≤ p.δ ^ (p.κ - 1) := Real.rpow_nonneg hp.δ.le _
  have h1 : 0 ≤ p.sLt * p.g + p.Θ * p.COm :=
    add_nonneg (mul_nonneg hp.sLt hp.g) (mul_nonneg hp.Θ hp.COm)
  have h2 := hp.c
  have h3 := hp.CG
  have h4 := hp.Mh2
  have h5 := hp.γb
  unfold StepInA.CE2
  positivity

theorem Pos.CE (hp : p.Pos) : 0 ≤ p.CE := by
  unfold StepInA.CE
  split_ifs
  · exact le_max_of_le_left hp.CE1
  · exact hp.CE1

theorem Pos.CGr (hp : p.Pos) : 0 ≤ p.CGr := by
  have := hp.sLt
  have := hp.sK
  unfold StepInA.CGr
  positivity

theorem Pos.one_sub_th (hp : p.Pos) : 0 < 1 - p.th := by linarith [hp.th1]

theorem Pos.CB (hp : p.Pos) : 0 ≤ p.CB := by
  have := hp.sB
  have := hp.CGr
  have := hp.one_sub_th
  unfold StepInA.CB
  positivity

theorem Pos.CNd (hp : p.Pos) : 0 ≤ p.CNd := by
  have := hp.sB
  have := hp.sK
  have := hp.CB
  unfold StepInA.CNd
  positivity

theorem Pos.CNtd (hp : p.Pos) : 0 ≤ p.CNtd := by
  have := hp.sB
  have := hp.sLt
  have := hp.CB
  unfold StepInA.CNtd
  positivity

theorem Pos.CDab (hp : p.Pos) : 0 ≤ p.CDab := by
  have := hp.M1
  have := hp.M2
  have := hp.sN
  have := hp.sNt
  have := hp.CNd
  have := hp.CNtd
  have := hp.δ
  unfold StepInA.CDab
  positivity

theorem Pos.CDc (hp : p.Pos) : 0 ≤ p.CDc := by
  have := hp.sB
  have := hp.w
  have := hp.sK
  have := hp.sLt
  unfold StepInA.CDc
  positivity

theorem Pos.CDT0 (hp : p.Pos) : 0 ≤ p.CDT0 := by
  have h0 : 0 ≤ p.δ ^ (2 * p.κ) := Real.rpow_nonneg hp.δ.le _
  have h1 := hp.CDab
  have h2 := hp.CDc
  have h3 := hp.CDK
  have h4 := hp.sNt
  have h5 := hp.sB
  have h6 := hp.w
  have h7 := hp.COm
  have h8 := hp.g
  have h9 := hp.γb
  unfold StepInA.CDT0
  positivity

theorem Pos.CDT (hp : p.Pos) : 0 ≤ p.CDT := by
  unfold StepInA.CDT
  split_ifs
  · exact le_max_of_le_left (add_nonneg hp.CDT0 (mul_nonneg hp.CDw hp.δ.le))
  · exact hp.CDT0

theorem Pos.rT (hp : p.Pos) : 0 ≤ p.rT := by
  have := hp.sT
  have := hp.CDT
  have := hp.one_sub_th
  unfold StepInA.rT
  positivity

end StepInA

/-- `γ^i δ^j ≤ γ̄^i D^j` for `γ ≤ γ̄`, `δ ≤ D`, `j ≥ 0`. -/
theorem pow_mul_rpow_le {γ γb δ D j : ℝ} (i : ℕ) (hγ : 0 < γ) (hγb : γ ≤ γb) (hδ : 0 < δ)
    (hD : δ ≤ D) (hj : 0 ≤ j) : γ ^ i * δ ^ j ≤ γb ^ i * D ^ j :=
  mul_le_mul (pow_le_pow_left₀ hγ.le hγb i) (Real.rpow_le_rpow hδ.le hD hj)
    (Real.rpow_nonneg hδ.le _) (pow_nonneg (hγ.le.trans hγb) i)

/-- The normalised errors of a bite `δ`. All are in terms of `s = δ^κ`. -/
theorem scales {γ δ ε κ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    ε = (γ * δ ^ κ) * (ε / (γ * δ ^ κ)) ∧
    ε / (γ * δ ^ κ) = (γ * δ ^ κ) * (ε / (γ ^ 2 * δ ^ (2 * κ))) ∧
    ε / (γ ^ 2 * δ ^ (2 * κ)) = δ * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ∧
    ε / δ = (γ ^ 2 * δ ^ (2 * κ)) * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ∧
    ε / (γ ^ 2 * δ ^ (2 * κ + 1)) = (γ ^ 2 * δ ^ (2 * κ - 1)) * (ε / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
    ε / δ = (γ ^ 4 * δ ^ (2 * (2 * κ) - 1)) * (ε / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
    ε / (γ * δ ^ (κ + 1)) = (γ ^ 3 * δ ^ (3 * κ - 1)) * (ε / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
    ε / (γ * δ ^ (κ + 1)) = (γ * δ ^ κ) * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) := by
  have hs : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ κ
  have e2 : δ ^ (2 * κ) = (δ ^ κ) ^ 2 := by rw [two_mul, Real.rpow_add hδ, sq]
  have e4 : δ ^ (2 * (2 * κ)) = (δ ^ κ) ^ 4 := by
    rw [show 2 * (2 * κ) = 2 * κ + 2 * κ by ring, Real.rpow_add hδ, e2]; ring
  have e21 : δ ^ (2 * κ + 1) = (δ ^ κ) ^ 2 * δ := by rw [Real.rpow_add_one hδ.ne', e2]
  have e11 : δ ^ (κ + 1) = δ ^ κ * δ := Real.rpow_add_one hδ.ne' _
  have e2m : δ ^ (2 * κ - 1) = (δ ^ κ) ^ 2 / δ := by
    rw [Real.rpow_sub_one hδ.ne', e2]
  have e3m : δ ^ (3 * κ - 1) = (δ ^ κ) ^ 3 / δ := by
    rw [Real.rpow_sub_one hδ.ne', show 3 * κ = κ + 2 * κ by ring, Real.rpow_add hδ, e2]; ring
  have e4m : δ ^ (2 * (2 * κ) - 1) = (δ ^ κ) ^ 4 / δ := by
    rw [Real.rpow_sub_one hδ.ne', e4]
  rw [e2, e4, e21, e11, e2m, e3m, e4m]
  generalize δ ^ κ = s at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp

end KAM.Sharp2.RouteA

end
