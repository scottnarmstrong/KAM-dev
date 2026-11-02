/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.TriLp

/-!
# The continuous multilinear map `𝒯^{a,p}_𝕜` (blueprint `bpW:w1:trilinear` (i))

`KAM.Wave.waveTriML a p` is the continuous symmetric `𝕜`-trilinear map
`(ℓ²_𝕜)³ → ℓ²_𝕜` (`ContinuousMultilinearMap`) with norm at most `C_* = K_{p+1/2}²/π`
(`KAM.Wave.waveTriML_norm_le`) whose coordinates are those of `T`
(`KAM.Wave.coeffW_waveTriML`); `KAM.Wave.waveTriML_unique` is the uniqueness clause.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {K : Type*} [RCLike K] (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- The continuous symmetric trilinear map `𝒯^{a,p}_𝕜 : (ℓ²_𝕜)³ → ℓ²_𝕜`. -/
def waveTriML :
    ContinuousMultilinearMap K (fun _ : Fin 3 => lp (fun _ : ℕ+ => K) 2)
      (lp (fun _ : ℕ+ => K) 2) :=
  MultilinearMap.mkContinuous
    { toFun := fun v => waveTriAux m hm ha hp (v 0) (v 1) (v 2)
      map_update_add' := fun v i x y => by
        match i with
        | 0 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_10,
            Function.update_of_ne wave_fin3_ne_20]
          exact waveTriAux_add_left m hm ha hp x y (v 1) (v 2)
        | 1 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_01,
            Function.update_of_ne wave_fin3_ne_21]
          exact waveTriAux_add_mid m hm ha hp (v 0) x y (v 2)
        | 2 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_02,
            Function.update_of_ne wave_fin3_ne_12]
          exact waveTriAux_add_right m hm ha hp (v 0) (v 1) x y
      map_update_smul' := fun v i c x => by
        match i with
        | 0 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_10,
            Function.update_of_ne wave_fin3_ne_20]
          exact waveTriAux_smul_left m hm ha hp c x (v 1) (v 2)
        | 1 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_01,
            Function.update_of_ne wave_fin3_ne_21]
          exact waveTriAux_smul_mid m hm ha hp c (v 0) x (v 2)
        | 2 =>
          simp only [Function.update_self,
            Function.update_of_ne wave_fin3_ne_02,
            Function.update_of_ne wave_fin3_ne_12]
          exact waveTriAux_smul_right m hm ha hp c (v 0) (v 1) x }
    (waveCubicConst p) (fun v => by
      simpa [Fin.prod_univ_three, mul_assoc] using
        waveTriAux_norm_le m hm ha hp (v 0) (v 1) (v 2))

lemma waveTriML_apply (v : Fin 3 → lp (fun _ : ℕ+ => K) 2) :
    waveTriML (K := K) m hm ha hp v = waveTriAux m hm ha hp (v 0) (v 1) (v 2) := rfl

lemma waveTriML_apply' (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriML (K := K) m hm ha hp ![y, y', y''] = waveTriAux m hm ha hp y y' y'' := rfl

/-- `bpW:w1:trilinear` (i): `‖𝒯^{a,p}_𝕜‖ ≤ C_* = K_{p+1/2}²/π`. -/
theorem waveTriML_norm_le : ‖(waveTriML (K := K) m hm ha hp)‖ ≤ waveCubicConst p :=
  MultilinearMap.mkContinuous_norm_le _ (waveCubicConst_nonneg p) _

/-- `bpW:w1:trilinear` (i): `κ_{a,p+1} 𝒯(y,y',y'') = T(κ_{a,p} y, κ_{a,p} y', κ_{a,p} y'')`. -/
theorem coeffW_waveTriML (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    coeffW a (p + 1) (waveTriML (K := K) m hm ha hp ![y, y', y'']) =
      waveTriSeq m hm (coeffW a p y) (coeffW a p y') (coeffW a p y'') :=
  coeffW_waveTriAux m hm ha hp y y' y''

/-- `bpW:w1:trilinear` (i), uniqueness: any continuous multilinear map with these coordinates is
`𝒯^{a,p}_𝕜`. -/
theorem waveTriML_unique
    (S : ContinuousMultilinearMap K (fun _ : Fin 3 => lp (fun _ : ℕ+ => K) 2)
      (lp (fun _ : ℕ+ => K) 2))
    (hS : ∀ y y' y'' : lp (fun _ : ℕ+ => K) 2, coeffW a (p + 1) (S ![y, y', y'']) =
      waveTriSeq m hm (coeffW a p y) (coeffW a p y') (coeffW a p y'')) :
    S = waveTriML (K := K) m hm ha hp := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hv : v = ![v 0, v 1, v 2] := by
    ext i; fin_cases i <;> rfl
  rw [hv]
  exact coeffW_injective a (p + 1)
    ((hS _ _ _).trans (coeffW_waveTriML (K := K) m hm ha hp _ _ _).symm)

/-- Symmetry of `𝒯^{a,p}_𝕜` under the transposition of the first two arguments. -/
theorem waveTriML_swap_left_mid (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriML (K := K) m hm ha hp ![y, y', y''] = waveTriML (K := K) m hm ha hp ![y', y, y''] :=
  waveTriAux_swap_left_mid m hm ha hp y y' y''

/-- Symmetry of `𝒯^{a,p}_𝕜` under the transposition of the last two arguments. -/
theorem waveTriML_swap_mid_right (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriML (K := K) m hm ha hp ![y, y', y''] = waveTriML (K := K) m hm ha hp ![y, y'', y'] :=
  waveTriAux_swap_mid_right m hm ha hp y y' y''

/-- Symmetry of `𝒯^{a,p}_𝕜` under the transposition of the outer arguments. -/
theorem waveTriML_swap_left_right (y y' y'' : lp (fun _ : ℕ+ => K) 2) :
    waveTriML (K := K) m hm ha hp ![y, y', y''] = waveTriML (K := K) m hm ha hp ![y'', y', y] :=
  waveTriAux_swap_left_right m hm ha hp y y' y''

end KAM.Wave

end
