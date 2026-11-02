/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Scalar drift on a segment (track B)

A real function whose derivative is bounded by `η` on the segment between `0` and `s` moves by at
most `η * |s|`, for either sign of `s`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

theorem abs_sub_le_of_deriv_bound {f f' : ℝ → ℝ} {s η : ℝ}
    (hf : ∀ u ∈ Set.uIcc 0 s, HasDerivAt f (f' u) u) (hb : ∀ u ∈ Set.uIcc 0 s, |f' u| ≤ η) :
    |f s - f 0| ≤ η * |s| := by
  have h := (convex_uIcc 0 s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hf u hu).hasDerivWithinAt) (fun u hu => by simpa using hb u hu)
    left_mem_uIcc right_mem_uIcc
  simpa [Real.norm_eq_abs, abs_sub_comm, mul_comm] using h

end KAM.EffectiveStability
