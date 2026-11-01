/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainTori
public import KAM.Wave.Birkhoff.MainQuartSum

/-!
# Weak invariance is transported: regularity (blueprint-W `bpW:w3:transport-tori-weak`)

Package W3-MAIN, blueprint label `bpW:w3:transport-tori-weak`.

`birkXLamInv`: the inverse of `X_Λ` (multiplier `(-i sgn λ_{|l|}/|l|)⁻¹`, norm `≤ 1`), taking
`𝔚` to `𝔚⁺`. `birkEmbed_birkXLamInv`: if `R ∈ 𝔚` satisfies `X_Λ(Ψ) = R` in `𝔚_{a,p-1}` for a
point `Ψ ∈ 𝔚`, then `Ψ = ι (X_Λ⁻¹ R) ∈ 𝔚⁺` with `‖Ψ‖₊ ≤ ‖R‖`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

/-- The inverse `𝔚 → 𝔚⁺` of `X_Λ`. -/
def birkXLamInv : BirkSpace →L[ℂ] BirkSpace :=
  lpDiagCLM (fun l : BirkIdx => (-Complex.I * birkSgn l * ((lamRatio m hm 1 l.2 : ℝ) : ℂ))⁻¹)
    (M := 1) zero_le_one (fun l => by
      rw [norm_inv, norm_mul, norm_mul, norm_neg, Complex.norm_I, norm_birkSgn, one_mul, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lamRatio_pos hm 1 l.2)]
      unfold lamRatio
      rw [Real.rpow_one]
      exact inv_le_one_of_one_le₀ (one_le_lam_div_pnat hm l.2))

@[simp] theorem birkXLamInv_apply (R : BirkSpace) (l : BirkIdx) :
    birkXLamInv m hm R l =
      (-Complex.I * birkSgn l * ((lamRatio m hm 1 l.2 : ℝ) : ℂ))⁻¹ * R l := rfl

theorem birkXLam_mu_ne (l : BirkIdx) :
    (-Complex.I * birkSgn l * ((lamRatio m hm 1 l.2 : ℝ) : ℂ)) ≠ 0 := by
  have h1 : birkSgn l ≠ 0 := by
    intro h; have := norm_birkSgn l; rw [h] at this; simp at this
  have h2 : ((lamRatio m hm 1 l.2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (lamRatio_pos hm 1 l.2).ne'
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) h1) h2

theorem birkXLam_birkXLamInv (R : BirkSpace) : birkXLam m hm (birkXLamInv m hm R) = R := by
  ext l
  rw [birkXLam_apply, birkXLamInv_apply]
  rw [mul_inv_cancel_left₀ (birkXLam_mu_ne m hm l)]

theorem birkXLamInv_birkXLam (y : BirkSpace) : birkXLamInv m hm (birkXLam m hm y) = y := by
  ext l
  rw [birkXLamInv_apply, birkXLam_apply]
  exact inv_mul_cancel_left₀ (birkXLam_mu_ne m hm l) _

theorem norm_birkXLamInv_le (R : BirkSpace) : ‖birkXLamInv m hm R‖ ≤ ‖R‖ := by
  refine ((birkXLamInv m hm).le_opNorm R).trans ?_
  have : ‖birkXLamInv m hm‖ ≤ 1 := norm_lpDiagCLM_le _ _ _
  calc ‖birkXLamInv m hm‖ * ‖R‖ ≤ 1 * ‖R‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = ‖R‖ := one_mul _

variable {m hm} {a p : ℝ}

theorem embedRatio_succ (a p : ℝ) (j : ℕ+) :
    embedRatio a (p + 1) a p j = 1 / (j : ℝ) := by
  have hj : (j : ℝ) ≠ 0 := by exact_mod_cast j.ne_zero
  have hw := ellWeight_ne_zero a p j
  unfold embedRatio
  rw [birk_weight_succ a p j]
  field_simp

theorem birkEmbed_birkXLamInv (R Ψ : BirkSpace)
    (heq : birkEmbed a p (p - 1) (by linarith) R = birkXLam m hm Ψ) :
    birkEmbed a (p + 1) p (by linarith) (birkXLamInv m hm R) = Ψ := by
  ext l
  have h1 := congrArg (fun z : BirkSpace => z l) heq
  simp only [birkEmbed_apply, birkXLam_apply] at h1 ⊢
  rw [birkXLamInv_apply]
  have e1 : embedRatio a (p + 1) a p l.2 = 1 / (l.2 : ℝ) := embedRatio_succ a p l.2
  have e2 : embedRatio a p a (p - 1) l.2 = 1 / (l.2 : ℝ) := by
    have := embedRatio_succ a (p - 1) l.2
    rwa [sub_add_cancel] at this
  rw [e1]
  rw [e2] at h1
  have hμ := birkXLam_mu_ne m hm l
  rw [mul_left_comm, h1, inv_mul_cancel_left₀ hμ]

variable (m hm) in
/-- Internal totalized helper (meaningful on `B_{ρ₁}`; public object `birkRestField`):
the right-hand side `X_Ḡ + X_{G^{nor}} + X_K` (embedded in `𝔚`). -/
def birkRestFieldExt (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (w : BirkSpace) : BirkSpace :=
  birkEmbed a (p + 1) p (by linarith) (birkHamBarX m hm ha hp w) +
    birkEmbed a (p + 1) p (by linarith) (birkHamNorX m hm ha hp w) +
    birkEmbed a (p + 1) p (by linarith) (birkXKExt m hm ha hp w)

variable {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
theorem norm_birkRestFieldExt_le (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    ‖birkRestFieldExt m hm ha hp w‖ ≤
      waveCubicConst p * ‖w‖ ^ 3 + 66 * waveCubicConst p * birkCF m p * ‖w‖ ^ 5 := by
  have hι : ∀ v : BirkSpace, ‖birkEmbed a (p + 1) p (by linarith) v‖ ≤ ‖v‖ := fun v => by
    refine ((birkEmbed a (p + 1) p (by linarith)).le_opNorm v).trans ?_
    calc ‖birkEmbed a (p + 1) p (by linarith)‖ * ‖v‖ ≤ 1 * ‖v‖ :=
          mul_le_mul_of_nonneg_right (norm_birkEmbed_le a (p + 1) p (by linarith)) (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  have h12 := norm_birkHamBarX_add_birkHamNorX_le m hm ha hp w
  have h3 := norm_birkXKExt_le (ha := ha) (hm := hm) (hp := hp) w hw
  have e : birkRestFieldExt m hm ha hp w = birkEmbed a (p + 1) p (by linarith)
      (birkHamBarX m hm ha hp w + birkHamNorX m hm ha hp w) +
      birkEmbed a (p + 1) p (by linarith) (birkXKExt m hm ha hp w) := by
    unfold birkRestFieldExt; rw [map_add]
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add ((hι _).trans h12) ((hι _).trans h3))

include hm hp in
/-- (`bpW:w3:transport-tori-weak`) Weak invariance is transported: the weak equation in
`𝔚_{a,p-1}` forces `Ψ(θ) ∈ 𝔚⁺` (with `‖Ψ‖₊ ≤ ‖DΨ ν‖ + C_*‖Ψ‖³ + C'_K‖Ψ‖⁵`), and then
`D(Γ∘Ψ)ν = X_H(Γ∘Ψ)`. -/
theorem birk_transport_tori_weak_aux (ν : Fin 2 → ℝ) (Ψ D : (Fin 2 → ℝ) → BirkSpace)
    (hΨ : ∀ θ, 160 * birkCF m p * ‖Ψ θ‖ ^ 2 < 1)
    (hder : ∀ θ : Fin 2 → ℝ, HasDerivAt (fun t : ℝ => Ψ (θ + t • ν)) (D θ) 0)
    (heq : ∀ θ, birkEmbed a p (p - 1) (by linarith) (D θ) =
      birkXLam m hm (Ψ θ) + birkEmbed a p (p - 1) (by linarith)
        (birkRestFieldExt m hm ha hp (Ψ θ)))
    (θ : Fin 2 → ℝ) :
    ∃ y z : BirkSpace, birkEmbed a (p + 1) p (by linarith) y = Ψ θ ∧
      ‖y‖ ≤ ‖D θ‖ + waveCubicConst p * ‖Ψ θ‖ ^ 3 +
        66 * waveCubicConst p * birkCF m p * ‖Ψ θ‖ ^ 5 ∧
      birkEmbed a (p + 1) p (by linarith) z = birkGamma m hm ha hp 1 (Ψ θ) ∧
      HasDerivAt (fun t : ℝ => birkGamma m hm ha hp 1 (Ψ (θ + t • ν)))
        (birkXLam m hm z + birkEmbed a (p + 1) p (by linarith)
          (birkHamGX m hm ha hp (birkGamma m hm ha hp 1 (Ψ θ)))) 0 := by
  -- the `𝔚⁺`-regularity at every point
  have hreg : ∀ θ', ∃ y : BirkSpace, birkEmbed a (p + 1) p (by linarith) y = Ψ θ' ∧
      birkXLam m hm y = D θ' - birkRestFieldExt m hm ha hp (Ψ θ') := fun θ' => by
    set R := D θ' - birkRestFieldExt m hm ha hp (Ψ θ') with hR
    have h0 : birkEmbed a p (p - 1) (by linarith) R = birkXLam m hm (Ψ θ') := by
      rw [hR, map_sub, heq θ']; abel
    exact ⟨birkXLamInv m hm R, birkEmbed_birkXLamInv R (Ψ θ') h0,
      birkXLam_birkXLamInv m hm R⟩
  choose Y hY1 hY2 using hreg
  obtain ⟨z, hz, hd⟩ := birk_transport_tori_aux (ha := ha) (hm := hm) (hp := hp) ν Y
    (fun θ' => by rw [hY1 θ']; exact hΨ θ') (fun θ' => by
      have h1 : (fun t : ℝ => birkEmbed a (p + 1) p (by linarith) (Y (θ' + t • ν))) =
          fun t : ℝ => Ψ (θ' + t • ν) := funext fun t => hY1 _
      rw [h1]
      refine (hder θ').congr_deriv ?_
      have h2 := hY2 θ'
      rw [h2, hY1 θ']; unfold birkRestFieldExt; abel) θ
  refine ⟨Y θ, z, hY1 θ, ?_, ?_, ?_⟩
  · have hR := norm_birkRestFieldExt_le (ha := ha) (hm := hm) (hp := hp) (Ψ θ) (hΨ θ)
    have hy : ‖Y θ‖ ≤ ‖D θ - birkRestFieldExt m hm ha hp (Ψ θ)‖ := by
      have h4 : Y θ = birkXLamInv m hm (D θ - birkRestFieldExt m hm ha hp (Ψ θ)) := by
        rw [← hY2 θ, birkXLamInv_birkXLam]
      rw [h4]; exact norm_birkXLamInv_le m hm _
    refine hy.trans ((norm_sub_le _ _).trans ?_)
    linarith
  · rw [hY1 θ] at hz; exact hz
  · have e : (fun t : ℝ => birkGamma m hm ha hp 1
        (birkEmbed a (p + 1) p (by linarith) (Y (θ + t • ν)))) =
        fun t : ℝ => birkGamma m hm ha hp 1 (Ψ (θ + t • ν)) := funext fun t => by rw [hY1]
    rw [e, hY1 θ] at hd
    exact hd

end KAM.Wave

end
