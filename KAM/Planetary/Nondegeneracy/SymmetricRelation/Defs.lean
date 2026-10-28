/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.GoodPolynomial

/-!
# Symmetric relation product: definitions

Blueprint P, Part 10 (`bpP:p10:Fc-def`): the relation forms `L_{c,π}` and their product `F_c` over
all permutations `π ∈ S_n`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

def relation (D : Data n) (c : Vec n × Vec n) (p : Equiv.Perm (Fin n)) (a : Vec n) : ℝ :=
  (∑ i, c.1 i*nu D (action D a) i) + ∑ j, c.2 j*sigma D a (p j)
def fc_def (D : Data n) (c : Vec n × Vec n) (a : Vec n) : ℝ :=
  ∏ p : Equiv.Perm (Fin n), relation D c p a

end Nondegeneracy
end KAM.Planetary
end
