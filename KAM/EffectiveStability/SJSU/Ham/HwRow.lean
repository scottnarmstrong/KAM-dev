/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Poly.Compose

/-!
# The row format of the modal Hamiltonian data (T2-CONF, N5a)

A row of `H_w` is `hwRow a₀ a₁ a₂ b₀ b₁ b₂ neg limbs`: the exponents of `w` and `w̄` and the integer
`± Σ_i limbs_i 2^{320 (n - 1 - i)}` (most significant limb first), so that literal lines stay short.
A row of the integer model rows (`c · 10^E`, at most about 110 bits) is `cRow a₀ a₁ a₂ b₀ b₁ b₂ c`.
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The natural number with the given base-`2^320` limbs, most significant first. -/
def limbsVal (ls : List ℕ) : ℕ := ls.foldl (fun acc x => Nat.shiftLeft acc 320 + x) 0

/-- A row of the modal Hamiltonian: exponents of `w` and `w̄`, sign and limbs of the coefficient. -/
def hwRow (a₀ a₁ a₂ b₀ b₁ b₂ : ℕ) (neg : Bool) (ls : List ℕ) : (Mon × Mon) × ℤ :=
  (((a₀, a₁, a₂), (b₀, b₁, b₂)), if neg then -((limbsVal ls : ℕ) : ℤ) else ((limbsVal ls : ℕ) : ℤ))

/-- A signed integer from its sign and base-`2^320` limbs (most significant first). -/
def hz (neg : Bool) (ls : List ℕ) : ℤ :=
  if neg then -((limbsVal ls : ℕ) : ℤ) else ((limbsVal ls : ℕ) : ℤ)

/-- Both exponents of a row lie in the monomial list `A`. -/
def keyIn (A : List Mon) (e : (Mon × Mon) × ℤ) : Bool := decide (e.1.1 ∈ A) && decide (e.1.2 ∈ A)

/-- A row of the integer model `c · 10^E` (exponents of `z` and `z̄`, coefficient). -/
def cRow (a₀ a₁ a₂ b₀ b₁ b₂ : ℕ) (c : ℤ) : (Mon × Mon) × ℤ := (((a₀, a₁, a₂), (b₀, b₁, b₂)), c)

end KAM.EffectiveStability.SJSU

end
