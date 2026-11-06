/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Poly.Polar
public import KAM.EffectiveStability.Tube.Poly.Dense
public import KAM.EffectiveStability.Tube.Witness.BinomialProdDeriv
public import KAM.EffectiveStability.Tube.Trig.Tube

/-!
# The Hamiltonian in tube coordinates: `h̃ = Σ_n T_n Π_j (B_j + u_j)^{n_j/2}` (T2-CONF, N5a)

The data are integer rows `(b, b', c)` of a modal Hamiltonian `Σ c/(10^E N^{|b|+|b'|}) w^b w̄^{b'}`.
Each row contributes the trigonometric term `rowTrig e φ = coef · cos(k·φ)` with the mode
`k = (b₀ - b'₀, b₁ - b'₁)` and the action exponent `n = b + b'` (`rowExp`). Grouped by `n`:
* `Tn rows n φ = Σ_{rows with b + b' = n} coef · cos(k·φ)`;
* `hTildeOf rows B (u, φ) = Σ_n T_n(φ) Π_j (B_j(φ) + u_j)^{n_j/2}` (`binomProd (halfExp n)`, N4);
* the Taylor coefficients `hCoef rows B m φ = Σ_n T_n(φ) Π_j binom(n_j/2, m_j) B_j(φ)^{n_j/2 - m_j}`
  and the remainder `hRem rows B L (u, φ) = Σ_n T_n(φ) binomProdRem (n/2) L (B φ) u`, with
  `hTildeOf_taylor : h̃ = Σ_{|m| ≤ L} h_m(φ) u^m + R`.
The `C¹` bounds of `R` on the box are `hRem_tube`, from N4's `binomProd_tube`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Finset

variable (E N : ℕ)

/-- The real coefficient `c / (10^E N^{|b| + |b'|})` of a row. -/
def rowCoef (e : (Mon × Mon) × ℤ) : ℝ :=
  (e.2 : ℝ) / ((10 : ℝ) ^ E * (N : ℝ) ^ (Mon.deg e.1.1 + Mon.deg e.1.2))

/-- The mode `k = (b₀ - b'₀, b₁ - b'₁)` of a row. -/
def rowMode (e : (Mon × Mon) × ℤ) : ℤ × ℤ :=
  ((e.1.1.1 : ℤ) - e.1.2.1, (e.1.1.2.1 : ℤ) - e.1.2.2.1)

/-- The action exponent `n = b + b'` of a row. -/
def rowExp (e : (Mon × Mon) × ℤ) : Fin 3 → ℕ :=
  ![e.1.1.1 + e.1.2.1, e.1.1.2.1 + e.1.2.2.1, e.1.1.2.2 + e.1.2.2.2]

/-- `n / 2` as real exponents. -/
def halfExp (n : Fin 3 → ℕ) : Fin 3 → ℝ := fun j => (n j : ℝ) / 2

/-- The trigonometric term `coef · cos(k·φ)` of a row. -/
def rowTrig (e : (Mon × Mon) × ℤ) (φ : Fin 2 → ℝ) : ℝ :=
  rowCoef E N e * Real.cos ((rowMode e).1 * φ 0 + (rowMode e).2 * φ 1)

/-- The action exponents occurring in the rows. -/
def expSet (rows : List ((Mon × Mon) × ℤ)) : Finset (Fin 3 → ℕ) := (rows.map rowExp).toFinset

/-- `T_n(φ) = Σ_{rows with b + b' = n} coef · cos(k·φ)`. -/
def Tn (rows : List ((Mon × Mon) × ℤ)) (n : Fin 3 → ℕ) (φ : Fin 2 → ℝ) : ℝ :=
  ((rows.filter fun e => decide (rowExp e = n)).map fun e => rowTrig E N e φ).sum

/-- **`h̃(u, φ) = Σ_n T_n(φ) Π_j (B_j(φ) + u_j)^{n_j/2}`.** -/
def hTildeOf (rows : List ((Mon × Mon) × ℤ)) (B : (Fin 2 → ℝ) → Fin 3 → ℝ)
    (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  ∑ n ∈ expSet rows, Tn E N rows n p.2 * binomProd (halfExp n) (B p.2) p.1

/-- The Taylor coefficient `h_m(φ) = Σ_n T_n(φ) Π_j binom(n_j/2, m_j) B_j(φ)^{n_j/2 - m_j}`. -/
def hCoef (rows : List ((Mon × Mon) × ℤ)) (B : (Fin 2 → ℝ) → Fin 3 → ℝ) (m : Fin 3 → ℕ)
    (φ : Fin 2 → ℝ) : ℝ :=
  ∑ n ∈ expSet rows, Tn E N rows n φ *
    ∏ j, gbinom (halfExp n j) (m j) * B φ j ^ (halfExp n j - m j)

/-- The Taylor remainder `R(u, φ) = Σ_n T_n(φ) binomProdRem (n/2) L (B φ) u`. -/
def hRem (rows : List ((Mon × Mon) × ℤ)) (B : (Fin 2 → ℝ) → Fin 3 → ℝ) (L : ℕ)
    (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  ∑ n ∈ expSet rows, Tn E N rows n p.2 * binomProdRem (halfExp n) L (B p.2) p.1

/-- **`h̃` row by row.** -/
theorem hTildeOf_eq_rows (rows : List ((Mon × Mon) × ℤ)) (B : (Fin 2 → ℝ) → Fin 3 → ℝ)
    (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) :
    hTildeOf E N rows B p =
      (rows.map fun e => rowTrig E N e p.2 * binomProd (halfExp (rowExp e)) (B p.2) p.1).sum := by
  rw [list_sum_eq_sum_filter rowExp _ (expSet rows) rows
    (fun a ha => List.mem_toFinset.2 (List.mem_map_of_mem ha))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Tn, ← List.sum_map_mul_right]
  congr 1
  refine List.map_congr_left fun e he => ?_
  rw [(by simpa using (List.mem_filter.1 he).2 : rowExp e = n)]

/-- **The Taylor split** `h̃ = Σ_{|m| ≤ L} h_m(φ) u^m + R(u, φ)`. -/
theorem hTildeOf_taylor (rows : List ((Mon × Mon) × ℤ)) (B : (Fin 2 → ℝ) → Fin 3 → ℝ) (L : ℕ)
    (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) :
    hTildeOf E N rows B p =
      ∑ m ∈ truncSet (Fin 3) L, hCoef E N rows B m p.2 * umon m p.1 + hRem E N rows B L p := by
  have hsplit : ∀ n, binomProd (halfExp n) (B p.2) p.1 =
      binomTrunc (halfExp n) L (B p.2) p.1 + binomProdRem (halfExp n) L (B p.2) p.1 := by
    intro n; rw [binomProdRem]; ring
  simp only [hTildeOf, hRem, hsplit, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [hCoef, binomTrunc, Finset.mul_sum, Finset.sum_mul, umon]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]

end KAM.EffectiveStability.Tube

end
