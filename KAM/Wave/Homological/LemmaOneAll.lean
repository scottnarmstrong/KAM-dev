/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LieDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Lemma 1 (ii) for all `(z, \bar z)` (`bpW:w4:lemma1`, step *The equation*, density)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

Both sides of `L_N F + N̂ = R - â₀` are continuous in `(z, \bar z) ∈ ℓ^N_{a,p} × ℓ^N_{a,p}`
(carrier `HomL2 × HomL2`), given `|Ω_j| ≤ K₀ (j+2)`: the pairings are bounded bilinear forms and the
pairing `⟨c, Ωz⟩₀` is `homPairL2 (diag(D_jΩ_j) ĉ) ẑ` with `|D_jΩ_j| ≤ K₀`. The truncations
`P_N z → z` are finitely supported (`homLemma1_equation`), hence the identity holds for all `z`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Filter Topology

variable {a p s : ℝ}

theorem homPairRep_eq' {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (c z : HomL2) :
    homPairRep ha hp c z = homPairL2 (homLamDiag ha hp c) z := rfl

theorem continuous_homPairRep_right {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (c : HomL2) :
    Continuous fun z : HomL2 => homPairRep ha hp c z :=
  (homPairL2 (homLamDiag ha hp c)).continuous

theorem continuous_homPairRep_op {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (M : HomOp) :
    Continuous fun q : HomL2 × HomL2 => homPairRep ha hp (M q.1) q.2 := by
  have h1 : Continuous fun q : HomL2 × HomL2 => homPairL2 (homLamDiag ha hp (M q.1)) :=
    homPairL2.continuous.comp ((homLamDiag ha hp).continuous.comp (M.continuous.comp
      continuous_fst))
  exact h1.clm_apply continuous_snd

theorem continuous_homRval {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (T : HomTaylor a p s)
    (θ y : Fin 2 → ℂ) :
    Continuous fun q : HomL2 × HomL2 => homRval ha hp T θ y q.1 q.2 := by
  unfold homRval
  have hf : Continuous fun q : HomL2 × HomL2 => q.1 := continuous_fst
  have hs : Continuous fun q : HomL2 × HomL2 => q.2 := continuous_snd
  have h1 := (continuous_homPairRep_right ha hp (T.cp θ)).comp hf
  have h2 := (continuous_homPairRep_right ha hp (T.cm θ)).comp hs
  have h3 := (continuous_homPairRep_op ha hp (T.P θ)).comp
    ((continuous_fst : Continuous fun q : HomL2 × HomL2 => q.1).prodMk
      (continuous_fst : Continuous fun q : HomL2 × HomL2 => q.1))
  have h4 := continuous_homPairRep_op ha hp (T.Q θ)
  have h5 := (continuous_homPairRep_op ha hp (T.P' θ)).comp
    ((continuous_snd : Continuous fun q : HomL2 × HomL2 => q.2).prodMk
      (continuous_snd : Continuous fun q : HomL2 × HomL2 => q.2))
  have h0 : Continuous fun _ : HomL2 × HomL2 => T.a0 θ + ∑ k, T.b θ k * y k := continuous_const
  exact ((((h0.add h1).add h2).add h3).add h4).add h5

theorem continuous_homRtheta {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (T : HomTaylor a p s)
    (l : Fin 2) (θ y : Fin 2 → ℂ) :
    Continuous fun q : HomL2 × HomL2 => homRtheta ha hp T l θ y q.1 q.2 := by
  unfold homRtheta
  have hf : Continuous fun q : HomL2 × HomL2 => q.1 := continuous_fst
  have hs : Continuous fun q : HomL2 × HomL2 => q.2 := continuous_snd
  have h1 := (continuous_homPairRep_right ha hp (homPartial l T.cp θ)).comp hf
  have h2 := (continuous_homPairRep_right ha hp (homPartial l T.cm θ)).comp hs
  have h3 := (continuous_homPairRep_op ha hp (homPartial l T.P θ)).comp
    ((continuous_fst : Continuous fun q : HomL2 × HomL2 => q.1).prodMk
      (continuous_fst : Continuous fun q : HomL2 × HomL2 => q.1))
  have h4 := continuous_homPairRep_op ha hp (homPartial l T.Q θ)
  have h5 := (continuous_homPairRep_op ha hp (homPartial l T.P' θ)).comp
    ((continuous_snd : Continuous fun q : HomL2 × HomL2 => q.2).prodMk
      (continuous_snd : Continuous fun q : HomL2 × HomL2 => q.2))
  have h0 : Continuous fun _ : HomL2 × HomL2 =>
      homPartial l T.a0 θ + ∑ k, homPartial l T.b θ k * y k := continuous_const
  exact ((((h0.add h1).add h2).add h3).add h4).add h5

theorem continuous_homRz {a p s : ℝ} (T : HomTaylor a p s) (θ : Fin 2 → ℂ) :
    Continuous fun q : HomL2 × HomL2 => homRz T θ q.1 q.2 := by
  unfold homRz
  exact ((continuous_const.add (((T.P θ).continuous.comp continuous_fst).const_smul (2 : ℂ))).add
    ((T.Qt θ).continuous.comp continuous_snd))

theorem continuous_homRzb {a p s : ℝ} (T : HomTaylor a p s) (θ : Fin 2 → ℂ) :
    Continuous fun q : HomL2 × HomL2 => homRzb T θ q.1 q.2 := by
  unfold homRzb
  exact ((continuous_const.add ((T.Q θ).continuous.comp continuous_fst)).add
    (((T.P' θ).continuous.comp continuous_snd).const_smul (2 : ℂ)))


theorem one_le_homWt {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (j : ℕ+) : 1 ≤ homWt a p j := by
  rw [homWt_eq]
  have hJ : (1 : ℝ) ≤ (j : ℝ) + 2 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    linarith
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hJ hp)
    (Real.one_le_exp (by positivity))

theorem norm_homLamD_mul_le {a p K0 : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hK0 : 0 ≤ K0) {Ω : ℕ+ → ℝ}
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (j : ℕ+) :
    ‖homLamD a p j * (Ω j : ℂ)‖ ≤ K0 := by
  have hw := one_le_homWt ha hp j
  have hJ : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  unfold homLamD
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    homWt_succ, abs_of_pos (by positivity)]
  have h1 := hΩ j
  rw [show (homWt a p j * (((j : ℝ) + 2) * homWt a p j))⁻¹ * |Ω j| =
    |Ω j| / (homWt a p j * (((j : ℝ) + 2) * homWt a p j)) by ring, div_le_iff₀ (by positivity)]
  calc |Ω j| ≤ K0 * ((j : ℝ) + 2) := h1
    _ ≤ K0 * (homWt a p j * (((j : ℝ) + 2) * homWt a p j)) := by
        apply mul_le_mul_of_nonneg_left _ hK0
        nlinarith [mul_pos hJ (by linarith : (0 : ℝ) < homWt a p j)]

/-- `⟨c, Ωz⟩₀ = homPairL2 (diag(D_jΩ_j) ĉ) ẑ`, bounded for `|Ω_j| ≤ K₀(j+2)`. -/
def homDiagW {a p K0 : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hK0 : 0 ≤ K0) {Ω : ℕ+ → ℝ}
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) : HomOp :=
  weightedDiagCLM (fun j => homLamD a p j * (Ω j : ℂ)) (norm_homLamD_mul_le ha hp hK0 hΩ)

theorem homPairOmega_eq_clm {a p K0 : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hK0 : 0 ≤ K0) {Ω : ℕ+ → ℝ}
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (c z : HomL2) :
    homPairOmega ha hp Ω c z = homPairL2 (homDiagW ha hp hK0 hΩ c) z := by
  show _ = homPairF _ z
  unfold homPairOmega homPairF
  refine tsum_congr fun j => ?_
  simp only [homDiagW, weightedDiagCLM_apply, homLamDiag_apply]
  ring

theorem truncLp_apply_not_mem (N : ℕ) (y : HomL2) (j : ℕ+)
    (hj : j ∉ Finset.image Nat.succPNat (Finset.range N)) : truncLp N y j = 0 := by
  unfold truncLp
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply]
  refine Finset.sum_eq_zero fun j' hj' => ?_
  have : j ≠ j' := fun h => hj (h ▸ hj')
  simp [Ne.symm this]

theorem tendsto_truncLp (y : HomL2) : Tendsto (fun N : ℕ => truncLp N y) atTop (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using tendsto_norm_sub_truncLp y


section main

variable {σ τ α K0 : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

/-- **Lemma 1 (ii), all `(z, \bar z)`** (`bpW:w4:lemma1` (ii)): `L_N F + N̂ = R - â₀` on
`T_{s-σ} × ℂ² × (ℓ^N_{a,p})²` (for `|Ω_j| ≤ K₀(j+2)`, `K₀ ≥ 0`). -/
theorem homLemma1_equation_all (ha : 0 ≤ a) (hp : 0 ≤ p) {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ)
    (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hm : HomMultBounds τ α w W) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |W j| ≤ K0 * ((j : ℝ) + 2)) (R : HomTaylor a p s)
    (hX : HomFieldBound ha hp r ε R) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
    (y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN ha hp w W (homSolveTaylor hτ hα hσ hσs hm R) θ y z zb + homNhat R y z zb =
      homRval ha hp R θ y z zb - homCoeff R.a0 0 := by
  set F := homSolveTaylor hτ hα hσ hσs hm R with hF
  let Ψ : HomL2 × HomL2 → ℂ := fun q => homLieN ha hp w W F θ y q.1 q.2 + homNhat R y q.1 q.2 -
    (homRval ha hp R θ y q.1 q.2 - homCoeff R.a0 0)
  have hΨ : Continuous Ψ := by
    have hNh : Continuous fun q : HomL2 × HomL2 => homNhat R y q.1 q.2 := by
      have := continuous_homRval ha hp (homNhatTaylor R) θ y
      simpa only [homNhatTaylor_val ha hp R θ y] using this
    have hf : Continuous fun q : HomL2 × HomL2 => q.1 := continuous_fst
    have hs : Continuous fun q : HomL2 × HomL2 => q.2 := continuous_snd
    have hLie : Continuous fun q : HomL2 × HomL2 => homLieN ha hp w W F θ y q.1 q.2 := by
      unfold homLieN
      have h1 : Continuous fun q : HomL2 × HomL2 =>
          (2 * Real.pi : ℂ)⁻¹ * ∑ l, (w l : ℂ) * homRtheta ha hp F l θ y q.1 q.2 :=
        continuous_const.mul (continuous_finset_sum _ fun l _ =>
          continuous_const.mul (continuous_homRtheta ha hp F l θ y))
      have h2 : Continuous fun q : HomL2 × HomL2 =>
          homPairOmega ha hp W (homRz F θ q.1 q.2) q.1 := by
        simp only [homPairOmega_eq_clm ha hp hK0 hΩ]
        exact (homPairL2.continuous.comp ((homDiagW ha hp hK0 hΩ).continuous.comp
          (continuous_homRz F θ))).clm_apply hf
      have h3 : Continuous fun q : HomL2 × HomL2 =>
          homPairOmega ha hp W (homRzb F θ q.1 q.2) q.2 := by
        simp only [homPairOmega_eq_clm ha hp hK0 hΩ]
        exact (homPairL2.continuous.comp ((homDiagW ha hp hK0 hΩ).continuous.comp
          (continuous_homRzb F θ))).clm_apply hs
      exact (h1.sub (continuous_const.mul h2)).add (continuous_const.mul h3)
    exact (hLie.add hNh).sub ((continuous_homRval ha hp R θ y).sub continuous_const)
  have hzero : ∀ N : ℕ, Ψ (truncLp N z, truncLp N zb) = 0 := fun N => by
    have := homLemma1_equation ha hp hr hτ hα hσ hσs hm R hX hθ y
      (S := Finset.image Nat.succPNat (Finset.range N)) (z := truncLp N z) (zb := truncLp N zb)
      (fun j hj => truncLp_apply_not_mem N z j hj) (fun j hj => truncLp_apply_not_mem N zb j hj)
    simp only [Ψ]
    rw [this]; ring
  have hlim : Tendsto (fun N : ℕ => Ψ (truncLp N z, truncLp N zb)) atTop (𝓝 (Ψ (z, zb))) :=
    (hΨ.tendsto _).comp ((tendsto_truncLp z).prodMk_nhds (tendsto_truncLp zb))
  have h0 : Tendsto (fun N : ℕ => Ψ (truncLp N z, truncLp N zb)) atTop (𝓝 0) := by
    simp only [hzero]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hlim h0
  simp only [Ψ] at this
  linear_combination this

end main

end KAM.Wave
