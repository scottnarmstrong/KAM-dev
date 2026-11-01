/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.Homological
public import KAM.Wave.Birkhoff.QuartNormal

/-!
# The quartic Hamiltonians of the normal form (blueprint-W `bpW:w3:main`, setting)

Package W3-MAIN, blueprint label `bpW:w3:main`.

`G = birkHamG` (all coefficients), `Ḡ = birkHamBar`, `G^{nor} = birkHamNor`, `G^{tan} = birkHamTan`
and `Z' = Ḡ - G^{tan} = birkHamZ` (`birkQuartP_Z`), each a quartic form of
`bpW:w3:quartic` (so `𝒜(𝔚)` with cubic field of norm `≤ C_*‖w‖³`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- The coefficient `c̄ - c^{tan}` of `Z'`. -/
def birkCoefZ : (Fin 4 → BirkIdx) → ℂ := fun x => birkCoefBar m hm x - birkCoefTan m hm x

theorem birkCoefZ_isCoef : IsBirkQuartCoef m hm (birkCoefZ m hm) where
  perm σ x := by
    unfold birkCoefZ
    rw [(birkCoefBar_isCoef m hm).perm, (birkCoefTan_isCoef m hm).perm]
  conj_neg x := by
    unfold birkCoefZ
    rw [(birkCoefBar_isCoef m hm).conj_neg, (birkCoefTan_isCoef m hm).conj_neg, map_sub]
  bound x := by
    classical
    unfold birkCoefZ birkCoefBar birkCoefTan birkQuartCoefOn
    by_cases hb : x ∈ birkBarSet
    · have ht : x ∈ birkTanSet := hb.1
      simp [hb, ht]
    · by_cases ht : x ∈ birkTanSet
      · simp [hb, ht]
      · simp [hb, ht]

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- `G`. -/
def birkHamG : BirkSpace → ℂ := birkQuartP m hm ha hp (birkCoefAll_isCoef m hm)
/-- `X_G`. -/
def birkHamGX : BirkSpace → BirkSpace := birkQuartX m hm ha hp (birkCoefAll_isCoef m hm)
/-- `Ḡ`. -/
def birkHamBar : BirkSpace → ℂ := birkQuartP m hm ha hp (birkCoefBar_isCoef m hm)
/-- `X_Ḡ`. -/
def birkHamBarX : BirkSpace → BirkSpace := birkQuartX m hm ha hp (birkCoefBar_isCoef m hm)
/-- `G^{nor}`. -/
def birkHamNor : BirkSpace → ℂ := birkQuartP m hm ha hp (birkCoefNor_isCoef m hm)
/-- `X_{G^{nor}}`. -/
def birkHamNorX : BirkSpace → BirkSpace := birkQuartX m hm ha hp (birkCoefNor_isCoef m hm)
/-- `G^{tan}`. -/
def birkHamTan : BirkSpace → ℂ := birkQuartP m hm ha hp (birkCoefTan_isCoef m hm)
/-- `Z' = Ḡ - G^{tan}` as a quartic form. -/
def birkHamZ : BirkSpace → ℂ := birkQuartP m hm ha hp (birkCoefZ_isCoef m hm)
/-- `X_{Z'}`. -/
def birkHamZX : BirkSpace → BirkSpace := birkQuartX m hm ha hp (birkCoefZ_isCoef m hm)

include ha hp in
theorem birkHamZ_eq (w : BirkSpace) :
    birkHamZ m hm ha hp w = birkHamBar m hm ha hp w - birkHamTan m hm ha hp w := by
  unfold birkHamZ birkHamBar birkHamTan birkQuartP birkDiag
  rw [birkQuartForm_apply, birkQuartForm_apply, birkQuartForm_apply, ← mul_sub]
  congr 1
  unfold birkQuartSum
  rw [← Summable.tsum_sub (summable_birkQuartTerm m hm ha hp (birkCoefBar_isCoef m hm).bound
    (fun _ => w)).of_norm
    (summable_birkQuartTerm m hm ha hp (birkCoefTan_isCoef m hm).bound (fun _ => w)).of_norm]
  refine tsum_congr fun x => ?_
  simp only [birkCoefZ, sub_mul]

include ha hp in
theorem birkHamG_eq (w : BirkSpace) :
    birkHamG m hm ha hp w = birkHamTan m hm ha hp w + birkHamNor m hm ha hp w :=
  birkQuartP_all_eq_tan_add_nor m hm ha hp w

include ha hp in
/-- (`bpW:w3:homological`) `DΛ(w) X_F(w) = Z'(w)`. -/
theorem birk_homological_Z (w : BirkSpace) :
    fderiv ℂ (birkLambda m hm ha hp) w (birkEmbed a (p + 1) p (by linarith)
        (birkDiagField (birkFgrad m hm ha hp) w)) = birkHamZ m hm ha hp w := by
  rw [birk_homological m hm ha hp w, birkHamZ_eq m hm ha hp w]
  rfl

end

end KAM.Wave

end
