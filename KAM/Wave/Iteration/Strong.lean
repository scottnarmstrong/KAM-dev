/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.Omega

/-!
# W6: strong conjugacy at regular points, the linear-algebra core (blueprint `bpW:w6:strong`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:strong` (milestone W6), the core of its proof.

On W5's carrier `KamPhase` with the form `ϖ_{q,q'}` (`stepSymp`, `bpW:w5:omega`): if `L` is onto
and two vectors `x`, `y` of `𝒫^q` have the same pairings `ϖ_{q,q'}(x, L W) = ϖ_{q,q'}(y, L W)` with
every `L W`, `W ∈ 𝒫^{q'}`, then `x = y` (nondegeneracy, step `omnd` of `bpW:w5:omega`). In
`bpW:w6:strong`: `q = p-1`, `q' = p_+`, `L = DΦ(w)` on `𝒫^{p_+}` (onto), `x = X_H(Φw)`,
`y = DΦ(w) A` with `A = X_{H_+}(w) ∈ 𝒫`; the two pairings agree with `ϖ(A, W)` by the weak
conjugacy and by symplecticity of `DΦ(w)`. The concrete statement (functions `H`, `H_+`, their
fields with values in `𝒫^{p-1}`, the embeddings between the weights) needs W5's conventions for
fields valued in `𝒫^{p-1}` (`bpW:w5:new-ham` (iii), not yet in Lean) and is not stated here.
-/

@[expose] public section

namespace KAM.Wave

/-- **Core of `bpW:w6:strong`**: equal pairings with the image of an onto map force equality. -/
theorem w6Strong_core {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q')
    (L : KamPhase → KamPhase) (hL : Function.Surjective L) {x y : KamPhase} {c : KamPhase → ℂ}
    (hx : ∀ W, stepSymp ha hqq' x (L W) = c W) (hy : ∀ W, stepSymp ha hqq' y (L W) = c W) :
    x = y := by
  have h : x - y = 0 := by
    refine stepSymp_nondeg ha hqq' fun W' => ?_
    obtain ⟨W, rfl⟩ := hL W'
    rw [stepSymp_sub_left, hx, hy, sub_self]
  exact sub_eq_zero.1 h

end KAM.Wave
