/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.Basic

/-!
# The magnetic field-line Hamiltonian as a `HamExpr`

`magHamExpr` is `H((q, φ), (p, J)) = J + h(p) + V(q, φ)` of plan-magnetic-barrier §1.1 at
`ε = 3/2500`, in the factored control form
`V = ε (cos a + cos b) + (1427/3200) ε² ((32000/2777) cos a - (96000/7669) cos b)²`,
`a = 2π(2q - φ)`, `b = 2π(3q - 2φ)`, `h(p) = p - (3/4) p² + (1/3) p³ - (1/16) p⁴`
(angles `(q, φ)`, actions `(p, J)`). Division-free; only `const`, `action`, `cosMode`, `add`,
`mul`, `pow`. The node order is the one `scripts/magnetic/sofx_mag.py` (`mag_ham_expr`) compiles.
-/

@[expose] public section

namespace KAM.Magnetic

open KAM.Certificate

/-- The integrable part `h(p)` on the action `p = z.2 0`. -/
def magHExpr : HamExpr 2 :=
  .add (.action 0) (.add (.mul (.const (-3 / 4)) (.pow (.action 0) 2))
    (.add (.mul (.const (1 / 3)) (.pow (.action 0) 3))
      (.mul (.const (-1 / 16)) (.pow (.action 0) 4))))

/-- The controlled perturbation `V(q, φ)` at `ε = 3/2500` (factored control). -/
def magVExpr : HamExpr 2 :=
  .add (.mul (.const (3 / 2500)) (.add (.cosMode [2, -1]) (.cosMode [3, -2])))
    (.mul (.const (1427 / 3200 * (3 / 2500) ^ 2))
      (.pow (.add (.mul (.const (32000 / 2777)) (.cosMode [2, -1]))
        (.mul (.const (-(96000 / 7669))) (.cosMode [3, -2]))) 2))

/-- `H = J + h(p) + V(q, φ)`. -/
def magHamExpr : HamExpr 2 :=
  .add (.action 1) (.add magHExpr magVExpr)

end KAM.Magnetic

end
