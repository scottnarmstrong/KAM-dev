/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Trig.Tube

/-!
# The terms of a bracket of two tube models (T2-CONF, N7)

For `f = Σ_i u^{μ i} g_i(φ)` and `h = Σ_e u^{ν e} k_e(φ)` (both sums over lists), N2's
`reducedBracket f h = Σ_a ((∂_{u_a} - ∂_{u_2}) f · ∂_{φ_a} h - ∂_{φ_a} f · (∂_{u_a} - ∂_{u_2}) h)`
is the sum over the terms `b : BT` (direction `a`, indices `i`, `e`, a kind and a shift) of
`coef b · u^{mon b} · val b φ`:

| kind | shift | coefficient | monomial | value |
|---|---|---|---|---|
| `false` | `false` (`e_a`) | `μ_i(a)` | `μ i + ν e - e_a` | `g_i · ∂_a k_e` |
| `false` | `true` (`e_2`) | `-μ_i(2)` | `μ i + ν e - e_2` | `g_i · ∂_a k_e` |
| `true` | `false` | `-ν_e(a)` | `μ i + ν e - e_a` | `∂_a g_i · k_e` |
| `true` | `true` | `ν_e(2)` | `μ i + ν e - e_2` | `∂_a g_i · k_e` |

(`u_a` is `Pi.single a.castSucc 1`.) The kernel bounds the grouped values
`Σ_{mon b = p} coef b · val b` for the kept `p`; the identity itself is proved on the analytic side.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- A bracket term. -/
structure BT (ι κ : Type*) where
  a : Fin 2
  i : ι
  e : κ
  kind : Bool
  sh : Bool

namespace BT

variable {ι κ : Type*}

/-- The axis of the shift: `a` (as `Fin 3`) or `2`. -/
def axis (b : BT ι κ) : Fin 3 := if b.sh then 2 else b.a.castSucc

/-- The integer coefficient. -/
def coef (μ : ι → Fin 3 → ℕ) (ν : κ → Fin 3 → ℕ) (b : BT ι κ) : ℤ :=
  match b.kind, b.sh with
  | false, false => μ b.i b.a.castSucc
  | false, true => -(μ b.i 2 : ℤ)
  | true, false => -(ν b.e b.a.castSucc : ℤ)
  | true, true => ν b.e 2

/-- The `u`-monomial `μ i + ν e - e_axis` (natural subtraction; the coefficient vanishes when the
shifted exponent is `0`). -/
def mon (μ : ι → Fin 3 → ℕ) (ν : κ → Fin 3 → ℕ) (b : BT ι κ) : Fin 3 → ℕ :=
  μ b.i + ν b.e - Pi.single b.axis 1

/-- The angle value of a term. -/
noncomputable def val (g : ι → (Fin 2 → ℝ) → ℝ) (k : κ → (Fin 2 → ℝ) → ℝ) (b : BT ι κ)
    (φ : Fin 2 → ℝ) : ℝ :=
  if b.kind then pderiv (g b.i) φ b.a * k b.e φ else g b.i φ * pderiv (k b.e) φ b.a

end BT

/-- All terms of the bracket of `Σ_{i ∈ Fl}` and `Σ_{e ∈ Hl}`. -/
def bterms {ι κ : Type*} (Fl : List ι) (Hl : List κ) : List (BT ι κ) :=
  ([0, 1] : List (Fin 2)).flatMap fun a => Fl.flatMap fun i => Hl.flatMap fun e =>
    ([false, true] : List Bool).flatMap fun kind =>
      ([false, true] : List Bool).map fun sh => ⟨a, i, e, kind, sh⟩

end KAM.EffectiveStability.Tube

end
