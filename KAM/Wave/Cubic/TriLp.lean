/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.TriSeq
public import KAM.Wave.Normal.Analysis.CubicAnalytic

/-!
# The trilinear map `𝒯^{a,p}_𝕜` on `ℓ²_𝕜` (blueprint `bpW:w1:trilinear` (i))

For `a ≥ 0`, `p ≥ 1/2` and `𝕜 ∈ {ℝ, ℂ}` (any `RCLike` field),
`KAM.Wave.waveTriAux a p y y' y'' = τ_{a,p+1} T(κ_{a,p} y, κ_{a,p} y', κ_{a,p} y'')` is trilinear
(`waveTriAux_add_left`, …), symmetric (`waveTriAux_swap_*`) and bounded by `C_* ∏‖y‖`
(`waveTriAux_norm_le`); `KAM.Wave.waveTriML` is the resulting continuous multilinear map, of
norm `≤ C_*` (`waveTriML_norm_le`). The defining property
`κ_{a,p+1} 𝒯(y,y',y'') = T(κ y, κ y', κ y'')` is `coeffW_waveTriAux`, and it characterizes `𝒯`
(`waveTriAux_unique`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {K : Type*} [RCLike K] (m : ℝ) (hm : 0 < m) {a p : ℝ}

section Coords

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- The coordinates `T(κ_{a,p} y, κ_{a,p} y', κ_{a,p} y'')` of the trilinear map. -/
def waveTriCoords (y y' y'' : lp (fun _ : ℕ+ => K) 2) : ℕ+ → K :=
  waveTriSeq m hm (coeffW a p y) (coeffW a p y') (coeffW a p y'')

include ha hp in
lemma waveTriCoords_isEll (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    IsEll a (p + 1) (waveTriCoords m hm (a := a) (p := p) y y' y'') :=
  (waveTri_oneSided m hm ha hp (isEll_coeffW a p y) (isEll_coeffW a p y')
    (isEll_coeffW a p y'')).2.1

include ha hp in
lemma waveTriCoords_summable (y y' y'' : lp (fun _ : ℕ+ => K) 2) (l : ℕ+) :
    Summable fun t : ℕ+ × ℕ+ × ℕ+ => (waveTriCoef m hm t.1 t.2.1 t.2.2 l : K) *
      (coeffW a p y t.1 * (coeffW a p y' t.2.1 * coeffW a p y'' t.2.2)) :=
  ((waveTri_oneSided m hm ha hp (isEll_coeffW a p y) (isEll_coeffW a p y')
    (isEll_coeffW a p y'')).1 l).of_norm

/-- `𝒯^{a,p}(y,y',y'') = τ_{a,p+1} T(κ_{a,p} y, κ_{a,p} y', κ_{a,p} y'')` on `ℓ²_𝕜`. -/
def waveTriAux (y y' y'' : lp (fun _ : ℕ+ => K) 2) : lp (fun _ : ℕ+ => K) 2 :=
  tauLp a (p + 1) (waveTriCoords m hm (a := a) (p := p) y y' y'')
    (waveTriCoords_isEll m hm ha hp y y' y'')

lemma waveTriAux_apply (y y' y'' : lp (fun _ : ℕ+ => K) 2) (l : ℕ+) :
    waveTriAux m hm ha hp y y' y'' l =
      (ellWeight a (p + 1) l : K) * waveTriCoords m hm (a := a) (p := p) y y' y'' l := rfl

/-- The defining property `κ_{a,p+1} 𝒯(y,y',y'') = T(κ_{a,p} y, κ_{a,p} y', κ_{a,p} y'')`. -/
theorem coeffW_waveTriAux (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    coeffW a (p + 1) (waveTriAux m hm ha hp y y' y'') =
      waveTriSeq m hm (coeffW a p y) (coeffW a p y') (coeffW a p y'') :=
  coeffW_tauLp _ _ _ _

/-- Uniqueness in `bpW:w1:trilinear` (i): the coordinates determine the map. -/
theorem waveTriAux_unique {y y' y'' z : lp (fun _ : ℕ+ => K) 2}
    (h : coeffW a (p + 1) z = waveTriSeq m hm (coeffW a p y) (coeffW a p y') (coeffW a p y'')) :
    z = waveTriAux m hm ha hp y y' y'' :=
  coeffW_injective a (p + 1) (h.trans (coeffW_waveTriAux m hm ha hp y y' y'').symm)

/-- `‖𝒯(y,y',y'')‖ ≤ C_* ‖y‖‖y'‖‖y''‖`. -/
theorem waveTriAux_norm_le (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    ‖waveTriAux m hm ha hp y y' y''‖ ≤ waveCubicConst p * (‖y‖ * ‖y'‖ * ‖y''‖) := by
  have h := (waveTri_oneSided m hm ha hp (isEll_coeffW a p y) (isEll_coeffW a p y')
    (isEll_coeffW a p y'')).2.2
  rw [ellTsumNorm_coeffW, ellTsumNorm_coeffW, ellTsumNorm_coeffW] at h
  calc ‖waveTriAux m hm ha hp y y' y''‖
      = ellTsumNorm a (p + 1) (waveTriCoords m hm (a := a) (p := p) y y' y'') := by
        rw [← ellNorm_eq_ellTsumNorm _ _ _ (waveTriCoords_isEll m hm ha hp y y' y'')]
        rfl
    _ ≤ _ := h

/-! Linearity in each argument. -/

include ha hp in
lemma waveTriCoords_add_left (y z y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriCoords m hm (a := a) (p := p) (y + z) y' y'' =
      fun l => waveTriCoords m hm (a := a) (p := p) y y' y'' l +
        waveTriCoords m hm (a := a) (p := p) z y' y'' l := by
  funext l
  unfold waveTriCoords waveTriSeq waveSelSum
  rw [← Summable.tsum_add (waveTriCoords_summable m hm ha hp y y' y'' l)
    (waveTriCoords_summable m hm ha hp z y' y'' l)]
  refine tsum_congr fun t => ?_
  simp only [coeffW_add, Pi.add_apply]
  ring

include ha hp in
lemma waveTriCoords_add_mid (y y' z y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriCoords m hm (a := a) (p := p) y (y' + z) y'' =
      fun l => waveTriCoords m hm (a := a) (p := p) y y' y'' l +
        waveTriCoords m hm (a := a) (p := p) y z y'' l := by
  funext l
  unfold waveTriCoords waveTriSeq waveSelSum
  rw [← Summable.tsum_add (waveTriCoords_summable m hm ha hp y y' y'' l)
    (waveTriCoords_summable m hm ha hp y z y'' l)]
  refine tsum_congr fun t => ?_
  simp only [coeffW_add, Pi.add_apply]
  ring

include ha hp in
lemma waveTriCoords_add_right (y y' y'' z : lp (fun _ : ℕ+ => K) 2) :
    waveTriCoords m hm (a := a) (p := p) y y' (y'' + z) =
      fun l => waveTriCoords m hm (a := a) (p := p) y y' y'' l +
        waveTriCoords m hm (a := a) (p := p) y y' z l := by
  funext l
  unfold waveTriCoords waveTriSeq waveSelSum
  rw [← Summable.tsum_add (waveTriCoords_summable m hm ha hp y y' y'' l)
    (waveTriCoords_summable m hm ha hp y y' z l)]
  refine tsum_congr fun t => ?_
  simp only [coeffW_add, Pi.add_apply]
  ring

lemma waveTriCoords_smul_left (c : K) (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriCoords m hm (a := a) (p := p) (c • y) y' y'' =
      fun l => c * waveTriCoords m hm (a := a) (p := p) y y' y'' l := by
  funext l
  unfold waveTriCoords waveTriSeq waveSelSum
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  simp only [coeffW_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma waveTriCoords_smul_mid (c : K) (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriCoords m hm (a := a) (p := p) y (c • y') y'' =
      fun l => c * waveTriCoords m hm (a := a) (p := p) y y' y'' l := by
  funext l
  unfold waveTriCoords waveTriSeq waveSelSum
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  simp only [coeffW_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma waveTriCoords_smul_right (c : K) (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriCoords m hm (a := a) (p := p) y y' (c • y'') =
      fun l => c * waveTriCoords m hm (a := a) (p := p) y y' y'' l := by
  funext l
  unfold waveTriCoords waveTriSeq waveSelSum
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  simp only [coeffW_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem waveTriAux_add_left (y z y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriAux m hm ha hp (y + z) y' y'' =
      waveTriAux m hm ha hp y y' y'' + waveTriAux m hm ha hp z y' y'' := by
  ext l
  simp only [waveTriAux_apply, lp.coeFn_add, Pi.add_apply, waveTriCoords_add_left m hm ha hp,
    mul_add]

theorem waveTriAux_add_mid (y y' z y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriAux m hm ha hp y (y' + z) y'' =
      waveTriAux m hm ha hp y y' y'' + waveTriAux m hm ha hp y z y'' := by
  ext l
  simp only [waveTriAux_apply, lp.coeFn_add, Pi.add_apply, waveTriCoords_add_mid m hm ha hp,
    mul_add]

theorem waveTriAux_add_right (y y' y'' z : lp (fun _ : ℕ+ => K) 2) :
    waveTriAux m hm ha hp y y' (y'' + z) =
      waveTriAux m hm ha hp y y' y'' + waveTriAux m hm ha hp y y' z := by
  ext l
  simp only [waveTriAux_apply, lp.coeFn_add, Pi.add_apply, waveTriCoords_add_right m hm ha hp,
    mul_add]

theorem waveTriAux_smul_left (c : K) (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriAux m hm ha hp (c • y) y' y'' = c • waveTriAux m hm ha hp y y' y'' := by
  ext l
  simp only [waveTriAux_apply, lp.coeFn_smul, Pi.smul_apply, waveTriCoords_smul_left, smul_eq_mul]
  ring

theorem waveTriAux_smul_mid (c : K) (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriAux m hm ha hp y (c • y') y'' = c • waveTriAux m hm ha hp y y' y'' := by
  ext l
  simp only [waveTriAux_apply, lp.coeFn_smul, Pi.smul_apply, waveTriCoords_smul_mid, smul_eq_mul]
  ring

theorem waveTriAux_smul_right (c : K) (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriAux m hm ha hp y y' (c • y'') = c • waveTriAux m hm ha hp y y' y'' := by
  ext l
  simp only [waveTriAux_apply, lp.coeFn_smul, Pi.smul_apply, waveTriCoords_smul_right, smul_eq_mul]
  ring

/-! Symmetry. -/

theorem waveTriSeq_swap_left_mid (q q' q'' : ℕ+ → K) :
    waveTriSeq m hm q q' q'' = waveTriSeq m hm q' q q'' := by
  funext l
  unfold waveTriSeq waveSelSum
  let e : ℕ+ × ℕ+ × ℕ+ ≃ ℕ+ × ℕ+ × ℕ+ :=
    { toFun := fun t => (t.2.1, t.1, t.2.2)
      invFun := fun t => (t.2.1, t.1, t.2.2)
      left_inv := fun t => rfl
      right_inv := fun t => rfl }
  rw [← e.tsum_eq]
  refine tsum_congr fun t => ?_
  simp only [e, Equiv.coe_fn_mk]
  unfold waveTriCoef
  rw [waveQuartic_comm12 t.2.1 t.1]
  push_cast
  ring

theorem waveTriSeq_swap_mid_right (q q' q'' : ℕ+ → K) :
    waveTriSeq m hm q q' q'' = waveTriSeq m hm q q'' q' := by
  funext l
  unfold waveTriSeq waveSelSum
  let e : ℕ+ × ℕ+ × ℕ+ ≃ ℕ+ × ℕ+ × ℕ+ :=
    { toFun := fun t => (t.1, t.2.2, t.2.1)
      invFun := fun t => (t.1, t.2.2, t.2.1)
      left_inv := fun t => rfl
      right_inv := fun t => rfl }
  rw [← e.tsum_eq]
  refine tsum_congr fun t => ?_
  simp only [e, Equiv.coe_fn_mk]
  unfold waveTriCoef
  rw [waveQuartic_comm23 t.1 t.2.2 t.2.1]
  push_cast
  ring

theorem waveTriAux_swap_left_mid (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriAux m hm ha hp y y' y'' = waveTriAux m hm ha hp y' y y'' := by
  ext l
  simp only [waveTriAux_apply, waveTriCoords]
  rw [waveTriSeq_swap_left_mid]

theorem waveTriAux_swap_mid_right (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriAux m hm ha hp y y' y'' = waveTriAux m hm ha hp y y'' y' := by
  ext l
  simp only [waveTriAux_apply, waveTriCoords]
  rw [waveTriSeq_swap_mid_right]

theorem waveTriAux_swap_left_right (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriAux m hm ha hp y y' y'' = waveTriAux m hm ha hp y'' y' y := by
  rw [waveTriAux_swap_left_mid, waveTriAux_swap_mid_right, waveTriAux_swap_left_mid]

end Coords

end KAM.Wave

end
