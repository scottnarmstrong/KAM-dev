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

Both sides of `L_N F + N̂ = R - â₀` are continuous in `(z, \bar z) ∈ ℓ^N_{a,p} × ℓ^N_{a,p}`
(carrier `HomL2 × HomL2`), given `|Ω_j| ≤ K₀ (j+2)`: the pairings are bounded bilinear forms and the
pairing `⟨c, Ωz⟩₀` is `homPairL2 (diag(D_jΩ_j) ĉ) ẑ` with `|D_jΩ_j| ≤ K₀`. The truncations
`P_N z → z` are finitely supported (`homLemma1_equation_gen`), hence the identity holds for all `z`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Filter Topology

variable {a p pb s : ℝ}

theorem continuous_homPairRep_right_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (c :
    HomL2) :
    Continuous fun z : HomL2 => homPairRep_gen ha (homPP hp hpb) c z :=
  (homPairL2 (homLamDiag_gen ha (homPP hp hpb) c)).continuous

theorem continuous_homPairRep_op_gen {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (M :
    HomOp) :
    Continuous fun q : HomL2 × HomL2 => homPairRep_gen ha (homPP hp hpb) (M q.1) q.2 := by
  have h1 : Continuous fun q : HomL2 × HomL2 => homPairL2 (homLamDiag_gen ha (homPP hp hpb) (M
      q.1)) :=
    homPairL2.continuous.comp ((homLamDiag_gen ha (homPP hp hpb)).continuous.comp (M.continuous.comp
      continuous_fst))
  exact h1.clm_apply continuous_snd

theorem continuous_homRval_gen {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T :
    HomTaylor_gen a
    p pb s)
    (θ y : Fin 2 → ℂ) :
    Continuous fun q : HomL2 × HomL2 => homRval_gen ha hp hpb T θ y q.1 q.2 := by
  unfold homRval_gen
  have hf : Continuous fun q : HomL2 × HomL2 => q.1 := continuous_fst
  have hs : Continuous fun q : HomL2 × HomL2 => q.2 := continuous_snd
  have h1 := (continuous_homPairRep_right_gen ha hp hpb (T.cp θ)).comp hf
  have h2 := (continuous_homPairRep_right_gen ha hp hpb (T.cm θ)).comp hs
  have h3 := (continuous_homPairRep_op_gen ha hp hpb (T.P θ)).comp
    ((continuous_fst : Continuous fun q : HomL2 × HomL2 => q.1).prodMk
      (continuous_fst : Continuous fun q : HomL2 × HomL2 => q.1))
  have h4 := continuous_homPairRep_op_gen ha hp hpb (T.Q θ)
  have h5 := (continuous_homPairRep_op_gen ha hp hpb (T.P' θ)).comp
    ((continuous_snd : Continuous fun q : HomL2 × HomL2 => q.2).prodMk
      (continuous_snd : Continuous fun q : HomL2 × HomL2 => q.2))
  have h0 : Continuous fun _ : HomL2 × HomL2 => T.a0 θ + ∑ k, T.b θ k * y k := continuous_const
  exact ((((h0.add h1).add h2).add h3).add h4).add h5

theorem continuous_homRtheta_gen {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T :
    HomTaylor_gen
    a p pb s)
    (l : Fin 2) (θ y : Fin 2 → ℂ) :
    Continuous fun q : HomL2 × HomL2 => homRtheta_gen ha hp hpb T l θ y q.1 q.2 := by
  unfold homRtheta_gen
  have hf : Continuous fun q : HomL2 × HomL2 => q.1 := continuous_fst
  have hs : Continuous fun q : HomL2 × HomL2 => q.2 := continuous_snd
  have h1 := (continuous_homPairRep_right_gen ha hp hpb (homPartial l T.cp θ)).comp hf
  have h2 := (continuous_homPairRep_right_gen ha hp hpb (homPartial l T.cm θ)).comp hs
  have h3 := (continuous_homPairRep_op_gen ha hp hpb (homPartial l T.P θ)).comp
    ((continuous_fst : Continuous fun q : HomL2 × HomL2 => q.1).prodMk
      (continuous_fst : Continuous fun q : HomL2 × HomL2 => q.1))
  have h4 := continuous_homPairRep_op_gen ha hp hpb (homPartial l T.Q θ)
  have h5 := (continuous_homPairRep_op_gen ha hp hpb (homPartial l T.P' θ)).comp
    ((continuous_snd : Continuous fun q : HomL2 × HomL2 => q.2).prodMk
      (continuous_snd : Continuous fun q : HomL2 × HomL2 => q.2))
  have h0 : Continuous fun _ : HomL2 × HomL2 =>
      homPartial l T.a0 θ + ∑ k, homPartial l T.b θ k * y k := continuous_const
  exact ((((h0.add h1).add h2).add h3).add h4).add h5

theorem continuous_homRz_gen {a p pb s : ℝ} (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) :
    Continuous fun q : HomL2 × HomL2 => homRz_gen T θ q.1 q.2 := by
  unfold homRz_gen
  exact ((continuous_const.add (((T.P θ).continuous.comp continuous_fst).const_smul (2 : ℂ))).add
    ((T.Qt θ).continuous.comp continuous_snd))

theorem continuous_homRzb_gen {a p pb s : ℝ} (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) :
    Continuous fun q : HomL2 × HomL2 => homRzb_gen T θ q.1 q.2 := by
  unfold homRzb_gen
  exact ((continuous_const.add ((T.Q θ).continuous.comp continuous_fst)).add
    (((T.P' θ).continuous.comp continuous_snd).const_smul (2 : ℂ)))

theorem homWt_mul_ge {a p pb : ℝ} (ha : 0 ≤ a) (hp1 : 1 ≤ p + pb) (j : ℕ+) :
    (j : ℝ) + 2 ≤ homWt a p j * homWt a pb j := by
  have hJ : (1 : ℝ) ≤ (j : ℝ) + 2 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    linarith
  have hc : (((j + 2 : ℕ+) : ℕ+) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
  unfold homWt ellWeight
  rw [hc]
  have h1 : (j : ℝ) + 2 ≤ ((j : ℝ) + 2) ^ (p + pb) := by
    calc (j : ℝ) + 2 = ((j : ℝ) + 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hJ hp1
  have h2 : (1 : ℝ) ≤ Real.exp (a * ((j : ℝ) + 2)) * Real.exp (a * ((j : ℝ) + 2)) := by
    have := Real.one_le_exp (by positivity : 0 ≤ a * ((j : ℝ) + 2))
    nlinarith
  calc (j : ℝ) + 2 ≤ ((j : ℝ) + 2) ^ (p + pb) * 1 := by linarith
    _ ≤ ((j : ℝ) + 2) ^ (p + pb) *
        (Real.exp (a * ((j : ℝ) + 2)) * Real.exp (a * ((j : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by rw [Real.rpow_add (by linarith)]; ring

theorem norm_homLamD_mul_le_gen {a p pb K0 : ℝ} (ha : 0 ≤ a) (hp1 : 1 ≤ p + pb) (hK0 : 0 ≤ K0)
    {Ω : ℕ+ → ℝ} (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (j : ℕ+) :
    ‖homLamD_gen a p pb j * (Ω j : ℂ)‖ ≤ K0 := by
  have hw := homWt_mul_ge (a := a) (p := p) (pb := pb) ha hp1 j
  have hpos : 0 < homWt a p j * homWt a pb j := mul_pos (homWt_pos _ _ _) (homWt_pos _ _ _)
  unfold homLamD_gen
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos)]
  rw [inv_mul_eq_div, div_le_iff₀ hpos]
  calc |Ω j| ≤ K0 * ((j : ℝ) + 2) := hΩ j
    _ ≤ K0 * (homWt a p j * homWt a pb j) := mul_le_mul_of_nonneg_left hw hK0

/-- `⟨c, Ωz⟩₀ = homPairL2 (diag(D_jΩ_j) ĉ) ẑ`, bounded for `|Ω_j| ≤ K₀(j+2)`. -/
def homDiagW_gen {a p pb K0 : ℝ} (ha : 0 ≤ a) (hp1 : 1 ≤ p + pb) (hK0 : 0 ≤ K0) {Ω : ℕ+ → ℝ}
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) : HomOp :=
  weightedDiagCLM (fun j => homLamD_gen a p pb j * (Ω j : ℂ)) (norm_homLamD_mul_le_gen ha hp1 hK0
      hΩ)

theorem homPairOmega_eq_clm_gen {a p pb K0 : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (hp1 : 1 ≤ p + pb) (hK0 : 0 ≤ K0) {Ω
    : ℕ+ → ℝ}
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (c z : HomL2) :
    homPairOmegaRaw_gen ha hp hpb Ω c z = homPairL2 (homDiagW_gen ha hp1 hK0 hΩ c) z := by
  show _ = homPairF _ z
  unfold homPairOmegaRaw_gen homPairF
  refine tsum_congr fun j => ?_
  simp only [homDiagW_gen, weightedDiagCLM_apply, homLamDiag_apply_gen]
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

/-- **Carrier evidence** from the frequency bound `|Ω_j| ≤ K₀(j+2)` and `1 ≤ p + p_+`. -/
theorem homOmegaCarrier_of_bound {a p pb K0 : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (hp1 : 1 ≤ p + pb) (hK0 : 0 ≤ K0) {Ω : ℕ+ → ℝ}
    (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) : HomOmegaCarrier ha hp hpb Ω := fun c z => by
  refine (homPairF_summable (homDiagW_gen ha hp1 hK0 hΩ c) z).congr fun j => ?_
  simp only [homDiagW_gen, weightedDiagCLM_apply, homLamDiag_apply_gen]
  ring

section main

variable {σ τ α K0 : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

/-- Hypothesis-taking variant for Lemma 1 (ii), all `(z, \bar z)`: assumes the gate `HomMultBounds`
and the frequency bound. The source-premise export is `homLemma1_equation_all_gen`. -/
theorem homLemma1_equation_all_of_gates_gen (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hp1 : 1 ≤ p +
  pb) {r ε
    :
    ℝ} (hr : 0 < r) (hτ
    : 0 ≤ τ)
    (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hm : HomMultBounds τ α w W) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |W j| ≤ K0 * ((j : ℝ) + 2)) (R : HomTaylor_gen a p pb s)
    (hX : HomFieldBound_gen ha hp hpb r ε R) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
    (y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN_gen ha hp hpb (homOmegaCarrier_of_bound ha hp hpb hp1 hK0 hΩ) w
        (homSolveTaylor_gen hτ hα hσ hσs hm R) θ y z zb + homNhat_gen R y z zb =
      homRval_gen ha hp hpb R θ y z zb - homCoeff R.a0 0 := by
  show homLieNRaw_gen ha hp hpb w W (homSolveTaylor_gen hτ hα hσ hσs hm R) θ y z zb +
    homNhat_gen R y z zb = _
  set F := homSolveTaylor_gen hτ hα hσ hσs hm R with hF
  let Ψ : HomL2 × HomL2 → ℂ := fun q => homLieNRaw_gen ha hp hpb w W F θ y q.1 q.2 + homNhat_gen R y
      q.1 q.2 -
    (homRval_gen ha hp hpb R θ y q.1 q.2 - homCoeff R.a0 0)
  have hΨ : Continuous Ψ := by
    have hNh : Continuous fun q : HomL2 × HomL2 => homNhat_gen R y q.1 q.2 := by
      have := continuous_homRval_gen ha hp hpb (homNhatTaylor_gen R) θ y
      simpa only [homNhatTaylor_val_gen ha hp hpb R θ y] using this
    have hf : Continuous fun q : HomL2 × HomL2 => q.1 := continuous_fst
    have hs : Continuous fun q : HomL2 × HomL2 => q.2 := continuous_snd
    have hLie : Continuous fun q : HomL2 × HomL2 => homLieNRaw_gen ha hp hpb w W F θ y q.1 q.2 := by
      unfold homLieNRaw_gen
      have h1 : Continuous fun q : HomL2 × HomL2 =>
          (2 * Real.pi : ℂ)⁻¹ * ∑ l, (w l : ℂ) * homRtheta_gen ha hp hpb F l θ y q.1 q.2 :=
        continuous_const.mul (continuous_finset_sum _ fun l _ =>
          continuous_const.mul (continuous_homRtheta_gen ha hp hpb F l θ y))
      have h2 : Continuous fun q : HomL2 × HomL2 =>
          homPairOmegaRaw_gen ha hp hpb W (homRz_gen F θ q.1 q.2) q.1 := by
        simp only [homPairOmega_eq_clm_gen ha hp hpb hp1 hK0 hΩ]
        exact (homPairL2.continuous.comp ((homDiagW_gen ha hp1 hK0 hΩ).continuous.comp
          (continuous_homRz_gen F θ))).clm_apply hf
      have h3 : Continuous fun q : HomL2 × HomL2 =>
          homPairOmegaRaw_gen ha hp hpb W (homRzb_gen F θ q.1 q.2) q.2 := by
        simp only [homPairOmega_eq_clm_gen ha hp hpb hp1 hK0 hΩ]
        exact (homPairL2.continuous.comp ((homDiagW_gen ha hp1 hK0 hΩ).continuous.comp
          (continuous_homRzb_gen F θ))).clm_apply hs
      exact (h1.sub (continuous_const.mul h2)).add (continuous_const.mul h3)
    exact (hLie.add hNh).sub ((continuous_homRval_gen ha hp hpb R θ y).sub continuous_const)
  have hzero : ∀ N : ℕ, Ψ (truncLp N z, truncLp N zb) = 0 := fun N => by
    have := homLemma1_equation_gen ha hp hpb hr hτ hα hσ hσs hm R hX hθ y
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

/-- **Lemma 1 (ii), all `(z, \bar z)`** (`bpW:w4:lemma1` (ii)) from the source premises
(`HomFreqHyp`, `HomMelnikov`, positivity, `ξ ∈ Π`, and `1 ≤ p + p_+`):
`L_N F + N̂ = R - â₀` on `T_{s-σ} × ℂ² × (ℓ^N_{a,p})²`, with the pairings of `L_N`
defined by the carrier evidence `homOmegaCarrier_of_bound`. -/
theorem homLemma1_equation_all_gen {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hp1 : 1 ≤ p + pb)
    {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor_gen a p pb s)
    (hX : HomFieldBound_gen ha hp hpb r ε R) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
    (y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN_gen ha hp hpb
        (homOmegaCarrier_of_bound ha hp hpb hp1 (by linarith [h.consts_nonneg.1] :
          0 ≤ 1 + M0) (homOmega_le h hξ)) (ω ξ)
        (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb
      + homNhat_gen R y z zb = homRval_gen ha hp hpb R θ y z zb - homCoeff R.a0 0 :=
  homLemma1_equation_all_of_gates_gen ha hp hpb hp1 hr hτ hα hσ hσs (homMultBounds_of h hα hH hξ)
    (by linarith [h.consts_nonneg.1]) (homOmega_le h hξ) R hX hθ y z zb

end main

end KAM.Wave
