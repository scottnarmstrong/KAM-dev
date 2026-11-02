/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ModifiedEq
public import KAM.Wave.Homological.LemmaOneAll
public import KAM.Wave.Homological.NhatTaylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The homological equation with modified divisors (`bpW:w5:w4-modified` (i))

`bpW:w5:w4-modified` (i) asserts that the equation (ii) of `bpW:w4:lemma1` holds for the solution
`F` with modified divisors:
* `homModLemma_equation_fin`: `L_N F + N̂ = R - â₀` for finitely supported `z, \bar z`
  (W4's assembly with the entrywise equations of `ModifiedEq.lean`, for the reweighted data);
* `homModLemma_equation_all`: the same on `T_{s-σ} × ℂ² × (ℓ^N_{a,p})²` (density), from the
  source premises, with the value `R` and `N̂` of `R ∈ 𝒯_s` (`p̄ = p+1`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Filter Topology

variable {a p pb s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

section fin

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1) {r ε : ℝ} (hr : 0 < r)
  (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) (hm : HomModMultBounds a p pb τ α w W)
  (R : HomTaylor_gen a p (p + 1) s)
  (hX : HomFieldBound_gen ha hp (homModPP1 p) r ε R) {θ : Fin 2 → ℂ}
  (hθ : θ ∈ complexStrip 2 (s - σ)) (y : Fin 2 → ℂ) {S : Finset ℕ+} {z zb : HomL2}
  (hz : ∀ j ∉ S, z j = 0) (hzb : ∀ j ∉ S, zb j = 0)
include ha hp hpb hr hτ hα hσ hσs hm hX hθ hz hzb

/-- **The homological equation for finitely supported `z, \bar z`** (`bpW:w5:w4-modified` (i)),
for the reweighted data `R' = homReweight R`. -/
theorem homModLemma_equation_fin :
    homLieNRaw_gen ha hp hpb w W (homModSolveTaylor hτ hα hσ hσs hc hm R) θ y z zb +
        homNhat_gen (homReweight hc R) y z zb =
      homRval_gen ha hp hpb (homReweight hc R) θ y z zb - homCoeff (homReweight hc R).a0 0 := by
  set F := homModSolveTaylor hτ hα hσ hσs hc hm R with hF
  set R' := homReweight hc R with hR'
  have hLa : homLop w (fun l => homPartial l F.a0 θ) = R'.a0 θ - homCoeff R'.a0 0 :=
    homModEq_a ha hp hpb hc hr hτ hα hσ hσs hm R hX hθ
  have hLb : ∀ k : Fin 2, homLop w (fun l => homPartial l F.b θ k) =
      R'.b θ k - homCoeff R'.b 0 k := fun k => homModEq_b ha hp hpb hc hr hτ hα hσ hσs hm R hX hθ k
  have hLcp : ∀ j : ℕ+, homLop w (fun l => homLamDiag_gen ha (homPP hp hpb)
      (homPartial l F.cp θ) j) =
      homLamDiag_gen ha (homPP hp hpb) (R'.cp θ) j + Complex.I * (W j : ℂ) *
        homLamDiag_gen ha (homPP hp hpb) (F.cp θ) j := by
    intro j
    have := homModEq_cp ha hp hpb hc hr hτ hα hσ hσs hm R hX hθ j (W := W)
    unfold homLop; push_cast at this; linear_combination this
  have hLcm : ∀ j : ℕ+, homLop w (fun l => homLamDiag_gen ha (homPP hp hpb)
      (homPartial l F.cm θ) j) =
      homLamDiag_gen ha (homPP hp hpb) (R'.cm θ) j + (-Complex.I) * (W j : ℂ) *
        homLamDiag_gen ha (homPP hp hpb) (F.cm θ) j := by
    intro j
    have := homModEq_cm ha hp hpb hc hr hτ hα hσ hσs hm R hX hθ j (W := W)
    unfold homLop; push_cast at this; linear_combination this
  have hLP : ∀ i j : ℕ+, homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.P θ) i j) =
      homSent_gen ha hp hpb (R'.P θ) i j + Complex.I * ((W i : ℂ) + (W j : ℂ)) *
        homSent_gen ha hp hpb (F.P θ) i j := by
    intro i j
    have := homModEq_P ha hp hpb hc hr hτ hα hσ hσs hm R hX hθ i j (W := W)
    unfold homLop; push_cast at this; linear_combination this
  have hLP' : ∀ i j : ℕ+, homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.P' θ) i j) =
      homSent_gen ha hp hpb (R'.P' θ) i j + (-Complex.I) * ((W i : ℂ) + (W j : ℂ)) *
        homSent_gen ha hp hpb (F.P' θ) i j := by
    intro i j
    have := homModEq_P' ha hp hpb hc hr hτ hα hσ hσs hm R hX hθ i j (W := W)
    unfold homLop; push_cast at this; linear_combination this
  have hLQ : ∀ i j : ℕ+, homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.Q θ) i j) =
      homSent_gen ha hp hpb (R'.Q θ) i j -
        (if i = j then homSent_gen ha hp hpb (homCoeff R'.Q 0) i j else 0)
        + Complex.I * ((W j : ℂ) - (W i : ℂ)) * homSent_gen ha hp hpb (F.Q θ) i j := by
    intro i j
    have := homModEq_Q ha hp hpb hc hr hτ hα hσ hσs hm R hX hθ i j (W := W)
    unfold homLop; push_cast at this; linear_combination this
  have hsymP : ∀ i j, homSent_gen ha hp hpb (F.P θ) i j = homSent_gen ha hp hpb (F.P θ) j i :=
    fun i j => homLam_entry_symm_gen ha hp hpb (F.symP θ hθ) i j
  have hsymP' : ∀ i j, homSent_gen ha hp hpb (F.P' θ) i j = homSent_gen ha hp hpb (F.P' θ) j i :=
    fun i j => homLam_entry_symm_gen ha hp hpb (F.symP' θ hθ) i j
  have hQt : ∀ i j, homSent_gen ha hp hpb (F.Qt θ) i j = homSent_gen ha hp hpb (F.Q θ) j i := by
    intro i j
    unfold homSent_gen
    rw [homLam_entry_eq_gen ha hp hpb, homLam_entry_eq_gen ha hp hpb, F.transQ θ hθ i j,
      mul_comm (homWt a p i : ℂ)]
  have hNhat : homNhat_gen R' y z zb = ∑ k, homCoeff R'.b 0 k * y k +
      ∑ j ∈ S, homSent_gen ha hp hpb (homCoeff R'.Q 0) j j * z j * zb j := by
    unfold homNhat_gen
    congr 1
    rw [tsum_eq_sum (s := S) (fun j hj => by simp [hz j hj])]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold homSent_gen
    rw [homLam_entry_eq_gen ha hp hpb]
    have : (homWt a p j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p j).ne'
    field_simp
  have hLop : (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homRtheta_gen ha hp hpb F l θ y z zb) =
      homLop w (fun l => homRtheta_gen ha hp hpb F l θ y z zb) := rfl
  unfold homLieNRaw_gen
  rw [homPairOmega_Rz_gen ha hp hpb hz hzb W F θ, homPairOmega_Rzb_gen ha hp hpb hz hzb W F θ, hLop,
    hNhat, homRval_fin_gen ha hp hpb hz hzb R' θ y]
  simp only [homRtheta_fin_gen ha hp hpb hz hzb, homLop_add, homLop_sumK, homLop_sum1,
    homLop_sum2, hLa, hLb, hLcp, hLcm, hLP, hLP', hLQ]
  have hbk : ∑ k, (R'.b θ k - homCoeff R'.b 0 k) * y k =
      ∑ k, R'.b θ k * y k - ∑ k, homCoeff R'.b 0 k * y k := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  have bP := homBlk_sym S Complex.I (fun i j => homSent_gen ha hp hpb (R'.P θ) i j)
    (fun i j => homSent_gen ha hp hpb (F.P θ) i j) hsymP W z
  have bP' := homBlk_sym S (-Complex.I) (fun i j => homSent_gen ha hp hpb (R'.P' θ) i j)
    (fun i j => homSent_gen ha hp hpb (F.P' θ) i j) hsymP' W zb
  have bQ := homBlk_Q S (fun i j => homSent_gen ha hp hpb (R'.Q θ) i j)
    (fun i j => homSent_gen ha hp hpb (F.Q θ) i j)
    (fun i j => homSent_gen ha hp hpb (homCoeff R'.Q 0) i j)
    (fun i j => homSent_gen ha hp hpb (F.Qt θ) i j) hQt W z zb
  have bC := homBlk_c S Complex.I (fun j => (homLamDiag_gen ha (homPP hp hpb) (R'.cp θ) j : ℂ))
    (fun j => (homLamDiag_gen ha (homPP hp hpb) (F.cp θ) j : ℂ)) W z
  have bCm := homBlk_c S (-Complex.I)
    (fun j => (homLamDiag_gen ha (homPP hp hpb) (R'.cm θ) j : ℂ))
    (fun j => (homLamDiag_gen ha (homPP hp hpb) (F.cm θ) j : ℂ)) W zb
  have hN : ∑ i ∈ S, (if i ∈ S then homSent_gen ha hp hpb (homCoeff R'.Q 0) i i * z i * zb i
      else 0) = ∑ i ∈ S, homSent_gen ha hp hpb (homCoeff R'.Q 0) i i * z i * zb i :=
    Finset.sum_congr rfl fun i hi => by simp [hi]
  rw [hbk]
  linear_combination bP + bP' + bQ + bC + bCm - hN

end fin

section all

variable {K0 : ℝ}

/-- CONDITIONAL helper for `bpW:w5:w4-modified` (i), the equation on all `(z, \bar z)`: assumes
the gate `HomModMultBounds` and the frequency bound. The source-premise export is
`homModLemma_equation_all`. -/
theorem homModLemma_equation_all_of_gates (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (hc : pb ≤ p + 1) (hp1 : 1 ≤ p + pb) {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α)
    (hσ : 0 < σ) (hσs : σ < s) (hm : HomModMultBounds a p pb τ α w W) (hK0 : 0 ≤ K0)
    (hΩ : ∀ j : ℕ+, |W j| ≤ K0 * ((j : ℝ) + 2)) (R : HomTaylor_gen a p (p + 1) s)
    (hX : HomFieldBound_gen ha hp (homModPP1 p) r ε R) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) (y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN_gen ha hp hpb (homOmegaCarrier_of_bound ha hp hpb hp1 hK0 hΩ) w
        (homModSolveTaylor hτ hα hσ hσs hc hm R) θ y z zb + homNhat_gen R y z zb =
      homRval_gen ha hp (homModPP1 p) R θ y z zb - homCoeff R.a0 0 := by
  have hs : 0 < s := hσ.trans hσs
  set R' := homReweight hc R with hR'
  rw [← homNhat_reweight hs hc R y z zb, ← homRval_reweight ha hp hpb hc R θ y z zb]
  show homLieNRaw_gen ha hp hpb w W (homModSolveTaylor hτ hα hσ hσs hc hm R) θ y z zb +
    homNhat_gen R' y z zb = _ - homCoeff R'.a0 0
  set F := homModSolveTaylor hτ hα hσ hσs hc hm R with hF
  let Ψ : HomL2 × HomL2 → ℂ := fun q => homLieNRaw_gen ha hp hpb w W F θ y q.1 q.2 +
    homNhat_gen R' y q.1 q.2 - (homRval_gen ha hp hpb R' θ y q.1 q.2 - homCoeff R'.a0 0)
  have hΨ : Continuous Ψ := by
    have hNh : Continuous fun q : HomL2 × HomL2 => homNhat_gen R' y q.1 q.2 := by
      have := continuous_homRval_gen ha hp hpb (homNhatTaylor_gen R') θ y
      simpa only [homNhatTaylor_val_gen ha hp hpb R' θ y] using this
    have hf : Continuous fun q : HomL2 × HomL2 => q.1 := continuous_fst
    have hs' : Continuous fun q : HomL2 × HomL2 => q.2 := continuous_snd
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
          (continuous_homRzb_gen F θ))).clm_apply hs'
      exact (h1.sub (continuous_const.mul h2)).add (continuous_const.mul h3)
    exact (hLie.add hNh).sub ((continuous_homRval_gen ha hp hpb R' θ y).sub continuous_const)
  have hzero : ∀ N : ℕ, Ψ (truncLp N z, truncLp N zb) = 0 := fun N => by
    have := homModLemma_equation_fin ha hp hpb hc hr hτ hα hσ hσs hm R hX hθ y
      (S := Finset.image Nat.succPNat (Finset.range N)) (z := truncLp N z) (zb := truncLp N zb)
      (W := W) (fun j hj => truncLp_apply_not_mem N z j hj)
      (fun j hj => truncLp_apply_not_mem N zb j hj)
    simp only [Ψ]
    rw [this]; ring
  have hlim : Tendsto (fun N : ℕ => Ψ (truncLp N z, truncLp N zb)) atTop (𝓝 (Ψ (z, zb))) :=
    (hΨ.tendsto _).comp ((tendsto_truncLp z).prodMk_nhds (tendsto_truncLp zb))
  have h0 : Tendsto (fun N : ℕ => Ψ (truncLp N z, truncLp N zb)) atTop (𝓝 0) := by
    simp only [hzero]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hlim h0
  simp only [Ψ] at this
  linear_combination this

/-- **`bpW:w5:w4-modified` (i), the equation** (equation (ii) of `bpW:w4:lemma1` for the solution
with modified divisors) from the source premises (`HomFreqHyp` (`bpW:w5:freq`), `HomMelnikovMod`
with `0 ≤ β ≤ p+1-p₊`, `α > 0`, `ξ ∈ Π`, `1 ≤ p + p₊`): `L_N F + N̂ = R - â₀` on
`T_{s-σ} × ℂ² × (ℓ^N_{a,p})²`, with `L_N` read with the gradients of `F` in `ℓ^N_{a,p₊}` and the
pairings defined by the carrier evidence `homOmegaCarrier_of_bound`. -/
theorem homModLemma_equation_all {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ β : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikovMod τ α β Par ω Ω) (hβ0 : 0 ≤ β) (hβ : β ≤ p + 1 - pb) (ha : 0 ≤ a)
    (hp : 0 ≤ p) (hpb : p ≤ pb) (hp1 : 1 ≤ p + pb) {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ)
    (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    (R : HomTaylor_gen a p (p + 1) s)
    (hX : HomFieldBound_gen ha hp (homModPP1 p) r ε R) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) (y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN_gen ha hp hpb
        (homOmegaCarrier_of_bound ha hp hpb hp1 (by linarith [h.consts_nonneg.1] :
          0 ≤ 1 + M0) (homOmega_le h hξ)) (ω ξ)
        (homModSolveTaylor hτ hα hσ hσs (homMod_pb_le hβ0 hβ)
          (homModMultBounds_of hα hβ0 hβ hH hξ) R) θ y z zb
      + homNhat_gen R y z zb =
      homRval_gen ha hp (homModPP1 p) R θ y z zb - homCoeff R.a0 0 :=
  homModLemma_equation_all_of_gates ha hp hpb (by linarith) hp1 hr hτ hα hσ hσs
    (homModMultBounds_of hα hβ0 hβ hH hξ) (by linarith [h.consts_nonneg.1]) (homOmega_le h hξ)
    R hX hθ y z zb

end all

end KAM.Wave
