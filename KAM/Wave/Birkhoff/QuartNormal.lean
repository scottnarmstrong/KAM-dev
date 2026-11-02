/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.QuartIdent

/-!
# The purely normal quartic `G^{nor}` (blueprint-W `bpW:w3:quartic-ident`)

Package W3-SETTING, blueprint label `bpW:w3:quartic-ident`.

`birkNormalPart` is `w ↦ ŵ` (the normal part, `|l| ≥ 3`, extended by zero). For the coefficient
`birkCoefNor = 𝔤 · 1_{𝒯ᶜ}` (all `|x_t| ≥ 3`): `G^{nor}(w) = G^{nor}(ŵ)` (`birkQuartP_normal`),
`X_{G^{nor}}(w) = X_{G^{nor}}(ŵ)` with vanishing tangential components
(`birkQuartX_normal`, `birkQuartX_tangential`), hence `|G^{nor}(w)| ≤ (C_*/4)‖ŵ‖⁴` and
`‖X_{G^{nor}}(w)‖₊ ≤ C_*‖ŵ‖³`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- The multiplier `1_{|l| ≥ 3}`. -/
def birkNormalMul (l : BirkIdx) : ℂ := open Classical in if 3 ≤ (l.2 : ℕ) then 1 else 0

/-- (`bpW:w3:space`) The normal part `w ↦ ŵ` (`|l| ≥ 3`), the identity on the normal modes. -/
def birkNormalPart : BirkSpace →L[ℂ] BirkSpace :=
  lpDiagCLM birkNormalMul zero_le_one (fun l => by unfold birkNormalMul; split_ifs <;> simp)

@[simp] theorem birkNormalPart_apply (y : BirkSpace) (l : BirkIdx) :
    birkNormalPart y l = birkNormalMul l * y l := rfl

theorem birkCoord_birkNormalPart (a p : ℝ) (y : BirkSpace) (l : BirkIdx) :
    birkCoord a p (birkNormalPart y) l = birkNormalMul l * birkCoord a p y l := by
  simp only [birkCoord, birkNormalPart_apply]; ring

/-- The set `𝒯ᶜ = {x : all |x_t| ≥ 3}`. -/
def birkNormalSet : Set (Fin 4 → BirkIdx) := {x | ∀ t, 3 ≤ ((x t).2 : ℕ)}

/-- The coefficient `𝔤 · 1_{𝒯ᶜ}` of `G^{nor}`. -/
def birkCoefNor : (Fin 4 → BirkIdx) → ℂ := birkQuartCoefOn m hm birkNormalSet

theorem birkCoefNor_isCoef : IsBirkQuartCoef m hm (birkCoefNor m hm) :=
  isBirkQuartCoef_on m hm birkNormalSet
    (fun σ _ hx t => hx (σ t)) (fun _ hx t => hx t)

theorem birkCoefNor_eq_zero {x : Fin 4 → BirkIdx} (hx : x ∉ birkNormalSet) : birkCoefNor m hm x = 0
    := by
  simp [birkCoefNor, birkQuartCoefOn, hx]

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include ha hp in
/-- (`bpW:w3:quartic-ident`) `G^{nor}(w) = G^{nor}(ŵ)`. -/
theorem birkQuartP_normal (w : BirkSpace) :
    birkQuartP m hm ha hp (birkCoefNor_isCoef m hm) w =
      birkQuartP m hm ha hp (birkCoefNor_isCoef m hm) (birkNormalPart w) := by
  unfold birkQuartP birkDiag
  rw [birkQuartForm_apply, birkQuartForm_apply]
  unfold birkQuartSum
  congr 1
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ birkNormalSet
  · congr 1
    rw [birkAtom_apply, birkAtom_apply]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [birkCoord_birkNormalPart]
    have : birkNormalMul (x t) = 1 := by simp [birkNormalMul, hx t]
    rw [this, one_mul]
  · rw [birkCoefNor_eq_zero m hm hx]; simp

include ha hp in
theorem birkCoord_birkQuartX_normal (w : BirkSpace) (l : BirkIdx) :
    birkCoord a (p + 1) (birkQuartX m hm ha hp (birkCoefNor_isCoef m hm) w) l =
      birkCoord a (p + 1) (birkQuartX m hm ha hp (birkCoefNor_isCoef m hm) (birkNormalPart w)) l :=
          by
  unfold birkQuartX birkDiagField
  rw [birkCoord_smul, birkCoord_smul, birkCoord_birkGradML m hm ha hp,
    birkCoord_birkGradML m hm ha hp]
  congr 2
  refine tsum_congr fun y => ?_
  by_cases hy : (![y 0, y 1, y 2, birkNeg l] : Fin 4 → BirkIdx) ∈ birkNormalSet
  · congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [birkCoord_birkNormalPart]
    have h3 := hy (Fin.castSucc t)
    have : birkNormalMul (y t) = 1 := by
      fin_cases t <;> simpa [birkNormalMul] using h3
    rw [this, one_mul]
  · rw [birkCoefNor_eq_zero m hm hy]; simp

include ha hp in
/-- (`bpW:w3:quartic-ident`) `X_{G^{nor}}(w) = X_{G^{nor}}(ŵ)`. -/
theorem birkQuartX_normal (w : BirkSpace) :
    birkQuartX m hm ha hp (birkCoefNor_isCoef m hm) w =
      birkQuartX m hm ha hp (birkCoefNor_isCoef m hm) (birkNormalPart w) := by
  ext l
  have h := birkCoord_birkQuartX_normal m hm ha hp w l
  have hw := ellWeight_cast_ne_zero (K := ℂ) a (p + 1) l.2
  simp only [birkCoord] at h
  exact (div_left_inj' hw).1 h

include ha hp in
/-- (`bpW:w3:quartic-ident`) `X_{G^{nor}}(w)` has vanishing tangential components. -/
theorem birkQuartX_tangential (w : BirkSpace) (l : BirkIdx) (hl : (l.2 : ℕ) ≤ 2) :
    birkQuartX m hm ha hp (birkCoefNor_isCoef m hm) w l = 0 := by
  have h := birkCoord_mul_weight a (p + 1)
    (birkQuartX m hm ha hp (birkCoefNor_isCoef m hm) w) l
  rw [← h]
  unfold birkQuartX birkDiagField
  rw [birkCoord_smul, birkCoord_birkGradML m hm ha hp]
  have : ∀ y : Fin 3 → BirkIdx, birkCoefNor m hm ![y 0, y 1, y 2, birkNeg l] = 0 := fun y =>
    birkCoefNor_eq_zero m hm fun hy => by
      have := hy 3
      simp at this
      omega
  simp [this]

include ha hp in
/-- (`bpW:w3:quartic-ident`) `|G^{nor}(w)| ≤ (C_*/4) ‖ŵ‖⁴`. -/
theorem norm_birkQuartP_normal_le (w : BirkSpace) :
    ‖birkQuartP m hm ha hp (birkCoefNor_isCoef m hm) w‖ ≤
      waveCubicConst p / 4 * ‖birkNormalPart w‖ ^ 4 := by
  rw [birkQuartP_normal m hm ha hp]
  exact norm_birkQuartP_le m hm ha hp _ _

include ha hp in
/-- (`bpW:w3:quartic-ident`) `‖X_{G^{nor}}(w)‖₊ ≤ C_* ‖ŵ‖³`. -/
theorem norm_birkQuartX_normal_le (w : BirkSpace) :
    ‖birkQuartX m hm ha hp (birkCoefNor_isCoef m hm) w‖ ≤
      waveCubicConst p * ‖birkNormalPart w‖ ^ 3 := by
  rw [birkQuartX_normal m hm ha hp]
  exact norm_birkQuartX_le m hm ha hp _ _

end

end KAM.Wave

end
