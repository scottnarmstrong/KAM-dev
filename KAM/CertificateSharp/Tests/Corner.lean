/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Corner.Certifier
public import KAM.CertificateSharp.Tests.Margin

/-!
# The corner certifier on a non-flat test model and on the toys

* **Non-flat model.** `n = 2`, the real trigonometric polynomial `e_{(1,1)} + e_{(1,-1)}` (not
  flat: its two modes have mixed signs), on the strip `ρ = 1/100` with `w = 1065/1000`. The landed
  bound is `2 w² = 2.268`, the corner bound is `w² + 1 = 2.134` (vertex `σ = (1,1)`: the
  second mode has `σ·k = 0`). A target `b = 2.2` separates them: the corner check passes, the
  landed one fails.
* **Toys.** T2 and T3 pass the corner invariance and embedding checks, hence the whole corner
  certifier with the sharp engine (`checkTorusCertificateCornerSharp`); the other five sub-checks
  are
  the landed ones. The toys are flat (`U ≡ 0`, constant `A`), so the corner and landed bounds agree
  on them, as design study §1.3 predicts.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM.Certificate

/-- Weight `ρ = 1/100`, `w = 1.065 ≥ e^{2π/100}`. -/
def cornerW : CertWeight := ⟨1 / 100, 1065 / 1000⟩

/-- `e_{(1,1)} + e_{(1,-1)}`. -/
def cornerModel : CertModel ℚ :=
  ⟨0, ⟨[([1, 1], ⟨1, 0⟩), ([1, -1], ⟨1, 0⟩)]⟩, 0⟩

theorem cornerW_ok : checkWeight cornerW 8 24 = true := by decide +kernel

/-- The landed bound `2 w²` exceeds `2.2`. -/
theorem corner_landed_fails :
    CertArith.ble (cornerModel.supBound cornerW) (22 / 10 : ℚ) = false := by
  decide +kernel

/-- The corner bound passes at `2.2`. -/
theorem corner_passes :
    cornerLeq cornerW (wloOf cornerW 24) 2 cornerModel (22 / 10 : ℚ) = true := by
  decide +kernel

/-- The corner bound is still a bound: it fails below `w² + 1 = 2.1342…`. -/
theorem corner_not_below :
    cornerLeq cornerW (wloOf cornerW 24) 2 cornerModel (213 / 100 : ℚ) = false := by
  decide +kernel

/-- The model is `e_{(1,1)} + e_{(1,-1)}`: it is bounded by the corner check on the whole strip. -/
theorem corner_model_bound {θ : Fin 2 → ℂ} (hθ : θ ∈ KAM.complexStrip 2 cornerW.rho) :
    ‖cornerModel.poly.eval 2 θ‖ ≤ ((22 / 10 : ℚ) : ℝ) := by
  have h := norm_le_of_cornerLeq (N' := 24) (m := cornerModel)
    (f := fun θ => cornerModel.poly.eval 2 θ) (n := 2) (W := cornerW) (s := 8) (N := 24)
    cornerW_ok (by
      intro θ hθ
      have h0 : CertArith.val (0 : ℚ) = 0 := by simp [CertArith.val]
      simp [cornerModel, h0]) hθ corner_passes
  exact h

open KAM.Certificate in
theorem toyCert2_corner_embedding : checkEmbeddingCorner toyCert2 = true := by decide +kernel
theorem toyCert2_corner_invariance : checkInvarianceCorner toyCert2 = true := by decide +kernel
theorem toyCert3_corner_embedding : checkEmbeddingCorner toyCert3 = true := by decide +kernel
theorem toyCert3_corner_invariance : checkInvarianceCorner toyCert3 = true := by decide +kernel

theorem toyCert2_corner_passes : checkTorusCertificateCornerSharp toyCert2 = true :=
  checkTorusCertificateCorner_of_old sharpEngine toyCert2_passes toyCert2_corner_embedding
    toyCert2_corner_invariance toyCert2_sharpTest

theorem toyCert3_corner_passes : checkTorusCertificateCornerSharp toyCert3 = true :=
  checkTorusCertificateCorner_of_old sharpEngine toyCert3_passes toyCert3_corner_embedding
    toyCert3_corner_invariance toyCert3_sharpTest

end KAM.CertificateSharp
