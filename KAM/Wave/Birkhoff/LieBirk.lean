/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieApp
public import KAM.Wave.Birkhoff.LieMain
public import KAM.Wave.Birkhoff.LieInv
public import KAM.Wave.Birkhoff.LieVar

/-!
# The flow of `X_F` on `𝔚` (blueprint-W `bpW:w3:flow`, `bpW:w3:symplectic`)

Package W3-FLOW, blueprint labels `bpW:w3:flow`, `bpW:w3:symplectic`.

The Lie-series flow `Γ_t = birkGamma` of the field `X_F(w) = S(w,w,w)` on `𝔚`
(`birkGamma m hm ha hp t w = Σ_k t^k φ_k(w)`) and its derivative `birkGammaD`, specialised from
the abstract theory (`LieFlow1`–`LieMain`) to `T = ι ∘ S` (`birkT`) with `C = C_F`. The domain is
`|t| < 2`, `40 C_F ‖w‖² < 1` (that is, `‖w‖ < ρ₀ = (40 C_F)^{-1/2}`).

Estimates in the `𝔚`-norm only (the `𝔚⁺`-norm refinements are not formalised here, see the
handoff): `‖Γ_t w‖ ≤ 10/9 ‖w‖`, `‖Γ_t w - w‖ ≤ 3|t|C_F‖w‖³`, `‖DΓ_t - I‖ ≤ 10|t|C_F‖w‖²`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- The flow `Γ_t(w) = Σ_k t^k φ_k(w)` of `X_F` (`t` real). -/
def birkGamma (t : ℝ) (w : BirkSpace) : BirkSpace := lieGamma (birkT m hm ha hp) t w

/-- `DΓ_t(w) = Σ_k t^k Dφ_k(w)`. -/
def birkGammaD (t : ℝ) (w : BirkSpace) : BirkSpace →L[ℂ] BirkSpace :=
  lieGammaD (birkT m hm ha hp) t w

variable {m hm ha hp}

section
variable (t : ℝ) (w : BirkSpace) (ht : |t| < 2) (hw : 40 * birkCF m p * ‖w‖ ^ 2 < 1)

include hm hp ht hw in
/-- (`bpW:w3:flow` (ii)) The flow equation `∂_t Γ_t(w) = X_F(Γ_t(w))`. -/
theorem birkGamma_flow :
    HasDerivAt (fun s : ℝ => birkGamma m hm ha hp s w)
      (birkT m hm ha hp ![birkGamma m hm ha hp t w, birkGamma m hm ha hp t w,
        birkGamma m hm ha hp t w]) t :=
  hasDerivAt_lieGamma_flow _ (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp)
    (birkCF_pos m hm hp) t w ht hw

include hm hp ht hw in
/-- (`bpW:w3:flow` (ii)) The transport equation `∂_t Γ_t(w) = DΓ_t(w) X_F(w)`. -/
theorem birkGamma_transport :
    HasDerivAt (fun s : ℝ => birkGamma m hm ha hp s w)
      (birkGammaD m hm ha hp t w (birkT m hm ha hp ![w, w, w])) t :=
  hasDerivAt_lieGamma_transport _ (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp)
    (birkT_perm m hm ha hp) (birkCF_pos m hm hp) t w ht hw

include hm hp ht hw in
/-- (`bpW:w3:flow` (i)) `D_wΓ_t(w) = DΓ_t(w)` (real Fréchet derivative). -/
theorem birkGamma_hasFDerivAt :
    HasFDerivAt (fun w' : BirkSpace => birkGamma m hm ha hp t w')
      ((birkGammaD m hm ha hp t w).restrictScalars ℝ) w :=
  hasFDerivAt_lieGamma_w _ (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp)
    (birkCF_pos m hm hp) t w ht hw

include hm hp ht hw in
/-- (`bpW:w3:flow` (v)) The variational equation
`∂_t DΓ_t(w) v = 3 S(Γ_t w, Γ_t w, DΓ_t(w) v)` (`DX_F(y) ξ = 3 S(y,y,ξ)`). -/
theorem birkGammaD_var (v : BirkSpace) :
    HasDerivAt (fun s : ℝ => birkGammaD m hm ha hp s w v)
      ((3 : ℂ) • birkT m hm ha hp ![birkGammaD m hm ha hp t w v, birkGamma m hm ha hp t w,
        birkGamma m hm ha hp t w]) t :=
  hasDerivAt_lieGammaD_var _ (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp)
    (birkT_perm m hm ha hp) (birkCF_pos m hm hp) t w v ht hw

end

section
variable (t : ℝ) (w : BirkSpace) (hq : 2 * |t| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10)

include hm hp hq in
/-- (`bpW:w3:flow` (iii)) `‖Γ_t(w)‖ ≤ 10/9 ‖w‖`. -/
theorem norm_birkGamma_le : ‖birkGamma m hm ha hp t w‖ ≤ 10 / 9 * ‖w‖ :=
  norm_lieGamma_le _ (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp) t w hq

include hm hp hq in
/-- (`bpW:w3:flow` (iii)) `‖Γ_t(w) - w‖ ≤ 3 |t| C_F ‖w‖³` (norm of `𝔚`). -/
theorem norm_birkGamma_sub_le : ‖birkGamma m hm ha hp t w - w‖ ≤ 3 * |t| * birkCF m p * ‖w‖ ^ 3 :=
  norm_lieGamma_sub_le _ (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp) t w hq

include hm hp hq in
/-- (`bpW:w3:flow` (iii)) `‖DΓ_t(w) - I‖ ≤ 10 |t| C_F ‖w‖²` (operator norm on `𝔚`). -/
theorem norm_birkGammaD_sub_le :
    ‖birkGammaD m hm ha hp t w - ContinuousLinearMap.id ℂ BirkSpace‖ ≤
      10 * |t| * birkCF m p * ‖w‖ ^ 2 :=
  norm_lieGammaD_sub_le _ (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp) t w hq

include hm hp hq in
/-- (`bpW:w3:flow` (iii)) `DΓ_t(w)` is invertible on `𝔚` with inverse of norm `≤ 2`
and `‖DΓ_t(w)⁻¹ - I‖ ≤ 20 |t| C_F ‖w‖²`. -/
theorem birkGammaD_invertible :
    ∃ B : BirkSpace →L[ℂ] BirkSpace, birkGammaD m hm ha hp t w * B = 1 ∧
      B * birkGammaD m hm ha hp t w = 1 ∧ ‖B‖ ≤ 2 ∧ ‖B - 1‖ ≤ 20 * |t| * birkCF m p * ‖w‖ ^ 2 :=
  lieGammaD_invertible _ (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp) t w hq

end

include hm hp in
/-- (`bpW:w3:flow` (iv)) Reality: `Γ_t(ϱ w) = ϱ Γ_t(w)`. -/
theorem birkGamma_rho (t : ℝ) (w : BirkSpace) (hq : 2 * |t| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10) :
    birkGamma m hm ha hp t (birkRho w) = birkRho (birkGamma m hm ha hp t w) :=
  lieGamma_rho _ birkRho (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp)
    (birkT_rho m hm ha hp) t w (by simpa using hq)

include hm hp in
/-- (`bpW:w3:flow` (vi)) `Γ_{-t}(Γ_t(w)) = w` for `|t| < 2` and `‖w‖ < ρ₁ = ρ₀ / 2`. -/
theorem birkGamma_neg_birkGamma (t : ℝ) (w : BirkSpace) (ht : |t| < 2)
    (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    birkGamma m hm ha hp (-t) (birkGamma m hm ha hp t w) = w :=
  lieGamma_neg_lieGamma _ (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp)
    (birkT_perm m hm ha hp) (birkCF_pos m hm hp) t w ht hw

include hm hp in
/-- (`bpW:w3:symplectic`) `Ω(DΓ_t(w) ξ, DΓ_t(w) η) = Ω(ξ, η)`. -/
theorem birkGammaD_symplectic (t : ℝ) (w ξ η : BirkSpace) (ht : |t| < 2)
    (hw : 40 * birkCF m p * ‖w‖ ^ 2 < 1) :
    birkOmega ha (by linarith : 0 ≤ p) (birkGammaD m hm ha hp t w ξ)
        (birkGammaD m hm ha hp t w η) = birkOmega ha (by linarith : 0 ≤ p) ξ η :=
  lie_symplectic _ (birkCF_pos m hm hp).le (norm_birkT_le m hm ha hp) (birkT_perm m hm ha hp)
    (birkOmega ha (by linarith : 0 ≤ p))
    (fun u v => birkOmega_antisymm ha (by linarith : 0 ≤ p) v u)
    (birkT_omega_symm m hm ha hp) (birkCF_pos m hm hp) t w ξ η ht hw

end KAM.Wave

end
