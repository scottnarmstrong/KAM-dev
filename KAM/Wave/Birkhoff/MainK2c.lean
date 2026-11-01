/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainK2b

/-!
# The field of `K₂` (blueprint-W `bpW:w3:main`, Step XK2)

Package W3-MAIN, blueprint label `bpW:w3:main`.

`hasDerivAt_dLambda_gamma`: `∂_t [DΛ(Γ_t w)(DΓ_t(w) u)] = DZ'(Γ_t w)(DΓ_t(w) u)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
theorem hasDerivAt_dLambda_gamma (s : ℝ) (w u : BirkSpace) (hs : |s| < 2)
    (hw : 40 * birkCF m p * ‖w‖ ^ 2 < 1) :
    HasDerivAt (fun r : ℝ => fderiv ℂ (birkLambda m hm ha hp) (birkGamma m hm ha hp r w)
        (birkGammaD m hm ha hp r w u))
      (fderiv ℂ (birkHamZ m hm ha hp) (birkGamma m hm ha hp s w)
        (birkGammaD m hm ha hp s w u)) s := by
  have hflow := birkGamma_flow (ha := ha) (hm := hm) (hp := hp) s w hs hw
  have hvar := birkGammaD_var (ha := ha) (hm := hm) (hp := hp) s w hs hw u
  set y := birkGamma m hm ha hp s w with hy
  set Au := birkGammaD m hm ha hp s w u with hAu
  set B := birkLamBil m hm ha hp with hB
  have h1 := hasDerivAt_omega_pair B hflow hvar
  have h2 := hasDerivAt_omega_pair B hvar hflow
  have h3 := h1.add h2
  have hfun : (fun r : ℝ => fderiv ℂ (birkLambda m hm ha hp) (birkGamma m hm ha hp r w)
        (birkGammaD m hm ha hp r w u)) =
      fun r : ℝ => B (birkGamma m hm ha hp r w) (birkGammaD m hm ha hp r w u) +
        B (birkGammaD m hm ha hp r w u) (birkGamma m hm ha hp r w) := by
    funext r; exact fderiv_birkLambda_eq (ha := ha) (hm := hm) (hp := hp) _ _
  rw [hfun]
  refine h3.congr_deriv ?_
  have hd := birk_DLam_homological_diff (ha := ha) (hm := hm) (hp := hp) y Au
  rw [fderiv_birkLambda_eq (ha := ha) (hm := hm) (hp := hp),
    fderiv_birkLambda_eq (ha := ha) (hm := hm) (hp := hp)] at hd
  rw [← hd]
  have e1 : birkT m hm ha hp ![y, y, y] =
      birkEmbed a (p + 1) p (by linarith) (birkS m hm ha hp (fun _ => y)) := by
    rw [birkT_apply]
    have : (![y, y, y] : Fin 3 → BirkSpace) = fun _ => y := by
      funext i; fin_cases i <;> rfl
    rw [this]
  have e2 : ((3 : ℂ)) • birkT m hm ha hp ![Au, y, y] =
      birkEmbed a (p + 1) p (by linarith)
        (((2 + 1 : ℕ) : ℂ) • birkS m hm ha hp (Fin.cons Au (fun _ : Fin 2 => y))) := by
    rw [birkT_apply, map_smul]
    have : (![Au, y, y] : Fin 3 → BirkSpace) = Fin.cons Au (fun _ : Fin 2 => y) := by
      funext i; fin_cases i <;> rfl
    rw [this]
    norm_num
  rw [e1, e2]
  ring

end KAM.Wave

end
