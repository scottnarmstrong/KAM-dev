/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.QuartSum

/-!
# Quartic forms (blueprint-W `bpW:w3:quartic`)

Package W3-SETTING, blueprint label `bpW:w3:quartic`.

For coefficients `c : (ℤ∖0)⁴ → ℂ` with `c_x = c_{σx} = conj c_{-x}` and `|c_x| ≤ |𝔤_x|`
(`IsBirkQuartCoef`) the form `𝔓(w¹,…,w⁴) = (1/16) Σ_x c_x ∏ w^t_{x_t}` (`birkQuartForm`) is a
continuous symmetric `4`-linear form, smoothing with constant `C_*/4` (`birkQuart_isSmoothing`) with
gradient `birkGradML`; its diagonal `P` is real, belongs to `𝒜(𝔚)` (`birkQuart_isClassA`) and
`‖X_P(w)‖₊ ≤ C_* ‖w‖³`, `|P(w)| ≤ (C_*/4) ‖w‖⁴` (`norm_birkQuartField_le`, `norm_birkQuartDiag_le`).
`birkQuartCoefOn S` is the coefficient `c = 𝔤` restricted to a set `S` invariant under permutations
and `x ↦ -x` (`isBirkQuartCoef_on`), for the sets `𝒯`, `𝒯 ∩ paired`, `𝒯ᶜ`, `(ℤ∖0)⁴`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

/-- (`bpW:w3:quartic`) The coefficient conditions: `c_x = c_{σx} = conj c_{-x}`, `|c_x| ≤ |𝔤_x|`. -/
structure IsBirkQuartCoef (m : ℝ) (hm : 0 < m) (c : (Fin 4 → BirkIdx) → ℂ) : Prop where
  perm : ∀ (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → BirkIdx), c (fun i => x (σ i)) = c x
  conj_neg : ∀ x, c (birkNegPi x) = conj (c x)
  bound : ∀ x, ‖c x‖ ≤ |birkG m hm x|

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) {c : (Fin 4 → BirkIdx) → ℂ}

include ha hp in
theorem birkQuartSum_update_add [DecidableEq (Fin 4)] (hc : IsBirkQuartCoef m hm c)
    (w : Fin 4 → BirkSpace) (i : Fin 4) (v v' : BirkSpace) :
    birkQuartSum a p c (Function.update w i (v + v')) =
      birkQuartSum a p c (Function.update w i v) + birkQuartSum a p c (Function.update w i v') := by
  unfold birkQuartSum
  rw [← Summable.tsum_add (summable_birkQuartTerm m hm ha hp hc.bound _).of_norm
    (summable_birkQuartTerm m hm ha hp hc.bound _).of_norm]
  refine tsum_congr fun x => ?_
  rw [MultilinearMap.map_update_add]; ring

omit ha hp in
theorem birkQuartSum_update_smul [DecidableEq (Fin 4)] (w : Fin 4 → BirkSpace) (i : Fin 4)
    (r : ℂ) (v : BirkSpace) :
    birkQuartSum a p c (Function.update w i (r • v)) =
      r * birkQuartSum a p c (Function.update w i v) := by
  unfold birkQuartSum
  rw [← tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [MultilinearMap.map_update_smul, smul_eq_mul]; ring

include ha hp in
/-- The quartic form `𝔓 = (1/16) Σ_x c_x ∏ w^t_{x_t}` as a multilinear map. -/
def birkQuartMap (hc : IsBirkQuartCoef m hm c) :
    MultilinearMap ℂ (fun _ : Fin 4 => BirkSpace) ℂ where
  toFun w := (1 / 16 : ℂ) * birkQuartSum a p c w
  map_update_add' w i v v' := by
    rw [birkQuartSum_update_add m hm ha hp hc, mul_add]
  map_update_smul' w i r v := by
    rw [birkQuartSum_update_smul, smul_eq_mul]; ring

include ha hp in
/-- (`bpW:w3:quartic`) The quartic form `𝔓`, continuous with `‖𝔓‖ ≤ C_*/4`. -/
def birkQuartForm (hc : IsBirkQuartCoef m hm c) :
    ContinuousMultilinearMap ℂ (fun _ : Fin 4 => BirkSpace) ℂ :=
  (birkQuartMap m hm ha hp hc).mkContinuous (waveCubicConst p / 4) (fun w => by
    show ‖(1 / 16 : ℂ) * birkQuartSum a p c w‖ ≤ _
    rw [birkQuartSum_eq_omega m hm ha hp hc.bound w]
    refine (norm_birkOmegaPlus_le ha _ _ _).trans ?_
    have h1 := norm_birkGradLp_le m hm ha hp hc.bound (birkInit4 w)
    have h2 : ‖birkGradML m hm ha hp hc.bound (birkInit4 w)‖ ≤
        waveCubicConst p / 4 * ∏ t, ‖birkInit4 w t‖ := h1
    calc ‖birkGradML m hm ha hp hc.bound (birkInit4 w)‖ * ‖w 3‖
        ≤ (waveCubicConst p / 4 * ∏ t, ‖birkInit4 w t‖) * ‖w 3‖ := by gcongr
      _ = _ := by
        simp [birkInit4, Fin.prod_univ_four, Fin.prod_univ_three]; ring)

include ha hp in
theorem birkQuartForm_apply (hc : IsBirkQuartCoef m hm c) (w : Fin 4 → BirkSpace) :
    birkQuartForm m hm ha hp hc w = (1 / 16 : ℂ) * birkQuartSum a p c w := rfl

/-- The quartic sum is symmetric under permutations of the four arguments. -/
theorem birkQuartSum_perm (hc : IsBirkQuartCoef m hm c) (σ : Equiv.Perm (Fin 4))
    (w : Fin 4 → BirkSpace) : birkQuartSum a p c (fun i => w (σ i)) = birkQuartSum a p c w := by
  unfold birkQuartSum
  rw [← (Equiv.arrowCongr σ (Equiv.refl BirkIdx)).tsum_eq (fun x => c x * birkAtom a p x w)]
  refine tsum_congr fun x => ?_
  have e1 : c (fun i => x (σ.symm i)) = c x := hc.perm σ.symm x
  have e2 : birkAtom a p x (fun i => w (σ i)) = birkAtom a p (fun i => x (σ.symm i)) w := by
    rw [birkAtom_apply, birkAtom_apply,
      ← Equiv.prod_comp σ (fun s => birkCoord a p (w s) (x (σ.symm s)))]
    simp
  show c x * _ = c (fun i => x (σ.symm i)) * birkAtom a p (fun i => x (σ.symm i)) w
  rw [e1, e2]

/-- `𝔓` is symmetric. -/
theorem birkQuartForm_perm (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (hc : IsBirkQuartCoef m hm c)
    (σ : Equiv.Perm (Fin 4)) (w : Fin 4 → BirkSpace) :
    birkQuartForm m hm ha hp hc (fun i => w (σ i)) = birkQuartForm m hm ha hp hc w := by
  rw [birkQuartForm_apply, birkQuartForm_apply, birkQuartSum_perm m hm hc]

/-- `𝔓(ϱw¹,…,ϱw⁴) = conj 𝔓(w¹,…,w⁴)` (reality of the diagonal). -/
theorem birkQuartSum_rho (hc : IsBirkQuartCoef m hm c) (w : Fin 4 → BirkSpace) :
    birkQuartSum a p c (fun i => birkRho (w i)) = conj (birkQuartSum a p c w) := by
  unfold birkQuartSum
  rw [Complex.conj_tsum, ← (birkNegPiEquiv 4).tsum_eq]
  refine tsum_congr fun x => ?_
  simp only [birkNegPiEquiv, Equiv.coe_fn_mk, map_mul]
  have e1 : c (birkNegPi x) = conj (c x) := hc.conj_neg x
  have e2 : birkAtom a p (birkNegPi x) (fun i => birkRho (w i)) = conj (birkAtom a p x w) := by
    rw [birkAtom_apply, birkAtom_apply, map_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    simp [birkCoord_birkRho, birkNegPi_apply]
  rw [e1, e2]

include ha hp in
theorem birkQuartForm_rho (hc : IsBirkQuartCoef m hm c) (w : Fin 4 → BirkSpace) :
    birkQuartForm m hm ha hp hc (fun i => birkRho (w i)) = conj (birkQuartForm m hm ha hp hc w) :=
        by
  rw [birkQuartForm_apply, birkQuartForm_apply, birkQuartSum_rho m hm hc, map_mul]
  have : conj (1 / 16 : ℂ) = 1 / 16 := by
    have h16 : (1 / 16 : ℂ) = ((1 / 16 : ℝ) : ℂ) := by push_cast; ring
    rw [h16, Complex.conj_ofReal]
  rw [this]

include ha hp in
/-- (`bpW:w3:quartic`) `𝔓` is smoothing with constant `C_*/4` and gradient `∇𝔓 = birkGradML`. -/
theorem birkQuart_isSmoothing (hc : IsBirkQuartCoef m hm c) :
    IsBirkSmoothing a p ha (by linarith) 3 (waveCubicConst p / 4) (birkQuartForm m hm ha hp hc)
      (birkGradML m hm ha hp hc.bound) where
  nonneg := by unfold waveCubicConst; positivity
  symm σ w := birkQuartForm_perm m hm ha hp hc σ w
  pairing w v := by
    rw [birkQuartForm_apply, birkQuartSum_eq_omega m hm ha hp hc.bound, birkInit4_snoc]
    rfl
  bound w := norm_birkGradLp_le m hm ha hp hc.bound w

end

end KAM.Wave

end
