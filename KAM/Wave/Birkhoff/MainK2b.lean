/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainK2a
public import KAM.Wave.Birkhoff.LieSympl

/-!
# The derivative of the homological identity (blueprint-W `bpW:w3:main`, Step K2/XK2)

Package W3-MAIN, blueprint label `bpW:w3:main`.

`birk_DLam_homological_diff`: differentiating `DΛ(y) X_F(y) = Z'(y)` in `y` along `z`:
`DΛ(z)(X_F(y)) + DΛ(y)(3 S(z,y,y)) = DZ'(y) z` (all fields embedded in `𝔚` by `ι`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
theorem fderiv_birkLambda_eq (y q : BirkSpace) :
    fderiv ℂ (birkLambda m hm ha hp) y q =
      birkLamBil m hm ha hp y q + birkLamBil m hm ha hp q y := by
  rw [(hasFDerivAt_birkLambda m hm ha hp y).fderiv]
  rfl

include hm hp in
theorem birk_DLam_homological_diff (y z : BirkSpace) :
    fderiv ℂ (birkLambda m hm ha hp) z (birkEmbed a (p + 1) p (by linarith)
        (birkS m hm ha hp (fun _ => y))) +
      fderiv ℂ (birkLambda m hm ha hp) y (birkEmbed a (p + 1) p (by linarith)
        (((2 + 1 : ℕ) : ℂ) • birkS m hm ha hp (Fin.cons z (fun _ : Fin 2 => y)))) =
      fderiv ℂ (birkHamZ m hm ha hp) y z := by
  set ι := birkEmbed a (p + 1) p (by linarith) with hι
  set B := birkLamBil m hm ha hp with hB
  -- the line `ε ↦ y + ε z`
  have hline : HasDerivAt (fun ε : ℝ => y + ε • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add y
  -- derivative of the field along the line
  have hS : HasFDerivAt (fun w : BirkSpace => birkS m hm ha hp (fun _ => w))
      (((2 + 1 : ℕ) : ℂ) • ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin 2 => BirkSpace)
        BirkSpace (fun _ => y)).comp (birkS m hm ha hp).curryLeft)) y :=
    hasFDerivAt_diag_symm (birkS m hm ha hp) (fun τ v => birkS_perm m hm ha hp τ v) y
  have h1 : HasFDerivAt (fun w : BirkSpace => ι (birkS m hm ha hp (fun _ => w)))
      ((ι.comp (((2 + 1 : ℕ) : ℂ) • ((ContinuousMultilinearMap.apply ℂ
        (fun _ : Fin 2 => BirkSpace) BirkSpace (fun _ => y)).comp
        (birkS m hm ha hp).curryLeft))).restrictScalars ℝ) (y + (0 : ℝ) • z) := by
    rw [zero_smul, add_zero]; exact (ι.hasFDerivAt.comp y hS).restrictScalars ℝ
  have hq := h1.comp_hasDerivAt (0 : ℝ) hline
  have hF := (hasDerivAt_omega_pair B hline hq).add (hasDerivAt_omega_pair B hq hline)
  have hZan : AnalyticAt ℂ (birkHamZ m hm ha hp) y :=
    (birkHamZ_isClassA m hm ha hp).analytic y (Set.mem_univ _)
  have hZ : HasDerivAt (fun ε : ℝ => birkHamZ m hm ha hp (y + ε • z))
      (fderiv ℂ (birkHamZ m hm ha hp) y z) 0 := by
    have hd : HasFDerivAt (birkHamZ m hm ha hp)
        ((fderiv ℂ (birkHamZ m hm ha hp) y).restrictScalars ℝ) (y + (0 : ℝ) • z) := by
      rw [zero_smul, add_zero]; exact hZan.differentiableAt.hasFDerivAt.restrictScalars ℝ
    exact hd.comp_hasDerivAt (0 : ℝ) hline
  have hfun : (fun ε : ℝ => B (y + ε • z) (ι (birkS m hm ha hp (fun _ => y + ε • z))) +
      B (ι (birkS m hm ha hp (fun _ => y + ε • z))) (y + ε • z)) =
      fun ε : ℝ => birkHamZ m hm ha hp (y + ε • z) := by
    funext ε
    rw [← fderiv_birkLambda_eq (ha := ha) (hm := hm) (hp := hp), ← birkXF_eq m hm ha hp,
      birk_homological_Z m hm ha hp]
  have hF' := hF.unique (hfun ▸ hZ : HasDerivAt (fun ε : ℝ => B (y + ε • z)
    (ι (birkS m hm ha hp (fun _ => y + ε • z))) +
      B (ι (birkS m hm ha hp (fun _ => y + ε • z))) (y + ε • z))
    (fderiv ℂ (birkHamZ m hm ha hp) y z) 0)
  have hq' : (ι.comp (((2 + 1 : ℕ) : ℂ) • ((ContinuousMultilinearMap.apply ℂ
        (fun _ : Fin 2 => BirkSpace) BirkSpace (fun _ => y)).comp
        (birkS m hm ha hp).curryLeft))).restrictScalars ℝ z =
      ι (((2 + 1 : ℕ) : ℂ) • birkS m hm ha hp (Fin.cons z (fun _ : Fin 2 => y))) := rfl
  simp only [Function.comp_apply, zero_smul, add_zero, hq'] at hF'
  rw [fderiv_birkLambda_eq (ha := ha) (hm := hm) (hp := hp),
    fderiv_birkLambda_eq (ha := ha) (hm := hm) (hp := hp)]
  rw [← hF']
  ring

end KAM.Wave

end
