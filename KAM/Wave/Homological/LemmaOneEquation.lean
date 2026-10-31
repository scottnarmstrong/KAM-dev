/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneEqFam
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The homological equation `L_N F + N̂ = R - â₀` (`bpW:w4:lemma1` (ii))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

* `homRval_gen T θ y z zb`: the value of the Taylor polynomial `R` (`bpW:w4:R`);
* `homLieNRaw_gen`: `L_N F = (1/2π)⟨ω,F_θ⟩ - i⟨F_z,Ωz⟩₀ + i⟨F_{\bar z},Ω\bar z⟩₀` (`bpW:w4:lie`);
* `homNhat_gen R y z zb = ⟨ω̂,y⟩ + ∑ Ω̂_j z_j \bar z_j`, `ω̂ = [b]`, `Ω̂_j = ([Q])_{jj}` (true
    coordinates
  `z_j = ẑ_j/ω_{a,p}(j+2)`);
* `homLemma1_equation_gen`: for finitely supported `z, \bar z`, all `y` and `θ ∈ T_{s-σ}`,
  `L_N F + N̂ = R - â₀`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s σ τ α : ℝ} {w : Fin 2 → ℝ} {W : ℕ+ → ℝ}

/-- The value of the Taylor polynomial `R = a + ⟨b,y⟩ + ⟨c^+,z⟩ + ⟨c^-,\bar z⟩ + ⟨Pz,z⟩ +
⟨Qz,\bar z⟩ + ⟨P'\bar z,\bar z⟩` (`bpW:w4:R`). -/
def homRval_gen {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb
    s) (θ y :
    Fin 2 → ℂ)
    (z zb : HomL2) : ℂ :=
  T.a0 θ + ∑ k, T.b θ k * y k + homPairRep_gen ha (homPP hp hpb) (T.cp θ) z + homPairRep_gen ha
      (homPP hp
      hpb) (T.cm θ) zb
    + homPairRep_gen ha (homPP hp hpb) (T.P θ z) z + homPairRep_gen ha (homPP hp hpb) (T.Q θ z) zb
    + homPairRep_gen ha (homPP hp hpb) (T.P' θ zb) zb

/-- INTERNAL totalized `L_N F` (uses `homPairOmegaRaw_gen`); the source-domain version is
`homLieN_gen`. -/
def homLieNRaw_gen {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (w : Fin 2 → ℝ) (W : ℕ+
  → ℝ)
    (T : HomTaylor_gen a p pb s) (θ y : Fin 2 → ℂ) (z zb : HomL2) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homRtheta_gen ha hp hpb T l θ y z zb)
    - Complex.I * homPairOmegaRaw_gen ha hp hpb W (homRz_gen T θ z zb) z
    + Complex.I * homPairOmegaRaw_gen ha hp hpb W (homRzb_gen T θ z zb) zb

/-- **`L_N F = (1/2π)⟨ω,F_θ⟩ - i⟨F_z,Ωz⟩₀ + i⟨F_{\bar z},Ω\bar z⟩₀`** (`bpW:w4:lie`) on the source
domain: both pairings are defined under the carrier evidence `HomOmegaCarrier`
(`homLieN_gen_eq` unfolds to the convergent pairings `homPairOmega_gen`). -/
def homLieN_gen {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {W : ℕ+ → ℝ}
    (_hC : HomOmegaCarrier ha hp hpb W) (w : Fin 2 → ℝ) (T : HomTaylor_gen a p pb s)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) : ℂ :=
  homLieNRaw_gen ha hp hpb w W T θ y z zb

theorem homLieN_gen_eq {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {W : ℕ+ → ℝ}
    (hC : HomOmegaCarrier ha hp hpb W) (w : Fin 2 → ℝ) (T : HomTaylor_gen a p pb s)
    (θ y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN_gen ha hp hpb hC w T θ y z zb =
      (2 * Real.pi : ℂ)⁻¹ * (∑ l, (w l : ℂ) * homRtheta_gen ha hp hpb T l θ y z zb)
        - Complex.I * homPairOmega_gen ha hp hpb hC (homRz_gen T θ z zb) z
        + Complex.I * homPairOmega_gen ha hp hpb hC (homRzb_gen T θ z zb) zb := rfl

/-- `N̂ = ⟨ω̂,y⟩ + ∑_j Ω̂_j z_j \bar z_j` with `ω̂ = [b]`, `Ω̂_j = ([Q])_{jj}`, in true
    coordinates. -/
def homNhat_gen {a p pb s : ℝ} (R : HomTaylor_gen a p pb s) (y : Fin 2 → ℂ) (z zb : HomL2) : ℂ :=
  ∑ k, homCoeff R.b 0 k * y k +
    ∑' j : ℕ+, homNormalEntry_gen a p pb (homCoeff R.Q 0) j j *
      (z j / (homWt a p j : ℂ)) * (zb j / (homWt a p j : ℂ))

/-- The operator `𝔏 g = (2π)⁻¹ ∑_l ω_l g_l`. -/
def homLop (w : Fin 2 → ℝ) (g : Fin 2 → ℂ) : ℂ := (2 * Real.pi : ℂ)⁻¹ * ∑ l, (w l : ℂ) * g l

theorem homLop_add (w : Fin 2 → ℝ) (g₁ g₂ : Fin 2 → ℂ) :
    homLop w (fun l => g₁ l + g₂ l) = homLop w g₁ + homLop w g₂ := by
  unfold homLop; simp [mul_add, Finset.sum_add_distrib]

theorem homLop_sum1 (w : Fin 2 → ℝ) {S : Finset ℕ+} (f : Fin 2 → ℕ+ → ℂ) (c : ℕ+ → ℂ) :
    homLop w (fun l => ∑ j ∈ S, f l j * c j) = ∑ j ∈ S, homLop w (fun l => f l j) * c j := by
  unfold homLop
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

theorem homLop_sum2 (w : Fin 2 → ℝ) {S : Finset ℕ+} (f : Fin 2 → ℕ+ → ℕ+ → ℂ)
    (c d : ℕ+ → ℂ) :
    homLop w (fun l => ∑ i ∈ S, ∑ j ∈ S, f l i j * c j * d i) =
      ∑ i ∈ S, ∑ j ∈ S, homLop w (fun l => f l i j) * c j * d i := by
  unfold homLop
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun l _ => (rfl : _ = _)]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => by ring


section fin

variable {a p pb s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {S : Finset ℕ+} {z zb : HomL2}
  (hz : ∀ j ∉ S, z j = 0) (hzb : ∀ j ∉ S, zb j = 0)
include hz hzb

theorem homRtheta_fin_gen (T : HomTaylor_gen a p pb s) (l : Fin 2) (θ y : Fin 2 → ℂ) :
    homRtheta_gen ha hp hpb T l θ y z zb = homPartial l T.a0 θ + ∑ k, homPartial l T.b θ k * y k
      + ∑ j ∈ S, homLamDiag_gen ha (homPP hp hpb) (homPartial l T.cp θ) j * z j
      + ∑ j ∈ S, homLamDiag_gen ha (homPP hp hpb) (homPartial l T.cm θ) j * zb j
      + ∑ i ∈ S, ∑ j ∈ S, homSent_gen ha hp hpb (homPartial l T.P θ) i j * z j * z i
      + ∑ i ∈ S, ∑ j ∈ S, homSent_gen ha hp hpb (homPartial l T.Q θ) i j * z j * zb i
      + ∑ i ∈ S, ∑ j ∈ S, homSent_gen ha hp hpb (homPartial l T.P' θ) i j * zb j * zb i := by
  unfold homRtheta_gen
  rw [homPairRep_fin_gen ha hp hpb _ hz, homPairRep_fin_gen ha hp hpb _ hzb, homPairRep_op_fin_gen
      ha hp hpb _
      hz hz,
    homPairRep_op_fin_gen ha hp hpb _ hz hzb, homPairRep_op_fin_gen ha hp hpb _ hzb hzb]

theorem homRval_fin_gen (T : HomTaylor_gen a p pb s) (θ y : Fin 2 → ℂ) :
    homRval_gen ha hp hpb T θ y z zb = T.a0 θ + ∑ k, T.b θ k * y k
      + ∑ j ∈ S, homLamDiag_gen ha (homPP hp hpb) (T.cp θ) j * z j
      + ∑ j ∈ S, homLamDiag_gen ha (homPP hp hpb) (T.cm θ) j * zb j
      + ∑ i ∈ S, ∑ j ∈ S, homSent_gen ha hp hpb (T.P θ) i j * z j * z i
      + ∑ i ∈ S, ∑ j ∈ S, homSent_gen ha hp hpb (T.Q θ) i j * z j * zb i
      + ∑ i ∈ S, ∑ j ∈ S, homSent_gen ha hp hpb (T.P' θ) i j * zb j * zb i := by
  unfold homRval_gen
  rw [homPairRep_fin_gen ha hp hpb _ hz, homPairRep_fin_gen ha hp hpb _ hzb, homPairRep_op_fin_gen
      ha hp hpb _
      hz hz,
    homPairRep_op_fin_gen ha hp hpb _ hz hzb, homPairRep_op_fin_gen ha hp hpb _ hzb hzb]

theorem homPairOmega_Rz_gen (W : ℕ+ → ℝ) (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) :
    homPairOmegaRaw_gen ha hp hpb W (homRz_gen T θ z zb) z =
      ∑ j ∈ S, homLamDiag_gen ha (homPP hp hpb) (T.cp θ) j * (W j : ℂ) * z j
      + 2 * ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * homSent_gen ha hp hpb (T.P θ) i j * z j * z i
      + ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * homSent_gen ha hp hpb (T.Qt θ) i j * zb j * z i := by
  rw [← homPairOmega_op_fin_gen ha hp hpb W (T.P θ) hz hz, ← homPairOmega_op_fin_gen ha hp hpb W
      (T.Qt θ)
      hzb hz,
    ← homPairOmega_fin_gen ha hp hpb W _ hz, homPairOmega_fin_gen ha hp hpb W _ hz,
    homPairOmega_fin_gen ha hp hpb W _ hz, homPairOmega_fin_gen ha hp hpb W _ hz, homRz_gen]
  rw [homPairOmega_fin_gen ha hp hpb W _ hz]
  simp only [map_add, map_smul, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_; ring

theorem homPairOmega_Rzb_gen (W : ℕ+ → ℝ) (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) :
    homPairOmegaRaw_gen ha hp hpb W (homRzb_gen T θ z zb) zb =
      ∑ j ∈ S, homLamDiag_gen ha (homPP hp hpb) (T.cm θ) j * (W j : ℂ) * zb j
      + ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * homSent_gen ha hp hpb (T.Q θ) i j * z j * zb i
      + 2 * ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * homSent_gen ha hp hpb (T.P' θ) i j * zb j * zb i := by
  rw [← homPairOmega_op_fin_gen ha hp hpb W (T.Q θ) hz hzb, ← homPairOmega_op_fin_gen ha hp hpb W
      (T.P' θ)
      hzb hzb,
    ← homPairOmega_fin_gen ha hp hpb W _ hzb, homPairOmega_fin_gen ha hp hpb W _ hzb,
    homPairOmega_fin_gen ha hp hpb W _ hzb, homPairOmega_fin_gen ha hp hpb W _ hzb, homRzb_gen]
  rw [homPairOmega_fin_gen ha hp hpb W _ hzb]
  simp only [map_add, map_smul, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

end fin

theorem homLop_sumK (w : Fin 2 → ℝ) (f : Fin 2 → Fin 2 → ℂ) (c : Fin 2 → ℂ) :
    homLop w (fun l => ∑ k, f l k * c k) = ∑ k, homLop w (fun l => f l k) * c k := by
  unfold homLop
  simp only [Fin.sum_univ_two]
  ring


section blocks

theorem homBlk_sym (S : Finset ℕ+) (c : ℂ) (SR SF : ℕ+ → ℕ+ → ℂ) (hsym : ∀ i j, SF i j = SF j i)
    (W : ℕ+ → ℝ) (z : ℕ+ → ℂ) :
    ∑ i ∈ S, ∑ j ∈ S, (SR i j + c * ((W i : ℂ) + (W j : ℂ)) * SF i j) * z j * z i
      - c * (2 * ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * SF i j * z j * z i) =
      ∑ i ∈ S, ∑ j ∈ S, SR i j * z j * z i := by
  have swap : ∑ i ∈ S, ∑ j ∈ S, (W j : ℂ) * SF i j * z j * z i =
      ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * SF i j * z j * z i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]; ring
  have e : ∀ i j, (SR i j + c * ((W i : ℂ) + (W j : ℂ)) * SF i j) * z j * z i =
      SR i j * z j * z i + c * ((W i : ℂ) * SF i j * z j * z i)
        + c * ((W j : ℂ) * SF i j * z j * z i) := fun i j => by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [swap]
  ring

theorem homBlk_Q (S : Finset ℕ+) (SR SF S0 SQt : ℕ+ → ℕ+ → ℂ)
    (hQt : ∀ i j, SQt i j = SF j i) (W : ℕ+ → ℝ) (z zb : ℕ+ → ℂ) :
    ∑ i ∈ S, ∑ j ∈ S, (SR i j - (if i = j then S0 i j else 0) +
        Complex.I * ((W j : ℂ) - (W i : ℂ)) * SF i j) * z j * zb i
      - Complex.I * ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * SQt i j * zb j * z i
      + Complex.I * ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * SF i j * z j * zb i =
      ∑ i ∈ S, ∑ j ∈ S, SR i j * z j * zb i - ∑ i ∈ S, (if i ∈ S then S0 i i * z i * zb i else 0)
          := by
  have swap : ∑ i ∈ S, ∑ j ∈ S, (W i : ℂ) * SQt i j * zb j * z i =
      ∑ i ∈ S, ∑ j ∈ S, (W j : ℂ) * SF i j * z j * zb i := by
    simp only [hQt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hd : ∑ i ∈ S, ∑ j ∈ S, (if i = j then S0 i j else 0) * z j * zb i =
      ∑ i ∈ S, (if i ∈ S then S0 i i * z i * zb i else 0) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hi, if_true]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd hi h
  have e : ∀ i j, (SR i j - (if i = j then S0 i j else 0) +
        Complex.I * ((W j : ℂ) - (W i : ℂ)) * SF i j) * z j * zb i =
      SR i j * z j * zb i - (if i = j then S0 i j else 0) * z j * zb i
        + Complex.I * ((W j : ℂ) * SF i j * z j * zb i)
        - Complex.I * ((W i : ℂ) * SF i j * z j * zb i) := fun i j => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [swap, hd]
  ring

theorem homBlk_c (S : Finset ℕ+) (c : ℂ) (A B : ℕ+ → ℂ) (W : ℕ+ → ℝ) (z : ℕ+ → ℂ) :
    ∑ j ∈ S, (A j + c * (W j : ℂ) * B j) * z j - c * ∑ j ∈ S, B j * (W j : ℂ) * z j =
      ∑ j ∈ S, A j * z j := by
  have e : ∀ j, (A j + c * (W j : ℂ) * B j) * z j = A j * z j + c * (B j * (W j : ℂ) * z j) :=
    fun j => by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end blocks


section main

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α)
    (hσ : 0 < σ)
  (hσs : σ < s) (hm : HomMultBounds τ α w W) (R : HomTaylor_gen a p pb s)
  (hX : HomFieldBound_gen ha hp hpb r ε R) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
  (y : Fin 2 → ℂ) {S : Finset ℕ+} {z zb : HomL2} (hz : ∀ j ∉ S, z j = 0)
  (hzb : ∀ j ∉ S, zb j = 0)
include ha hp hpb hr hτ hα hσ hσs hm hX hθ hz hzb

/-- **Lemma 1 (ii): the homological equation** (`bpW:w4:lemma1` (ii)): for finitely supported
`z, \bar z`, `L_N F + N̂ = R - â₀` on `T_{s-σ}`. -/
theorem homLemma1_equation_gen :
    homLieNRaw_gen ha hp hpb w W (homSolveTaylor_gen hτ hα hσ hσs hm R) θ y z zb + homNhat_gen R y z
        zb =
      homRval_gen ha hp hpb R θ y z zb - homCoeff R.a0 0 := by
  set F := homSolveTaylor_gen hτ hα hσ hσs hm R with hF
  have hLa : homLop w (fun l => homPartial l F.a0 θ) = R.a0 θ - homCoeff R.a0 0 :=
    homEq_a ha hp hpb hr hτ hα hσ hσs hm R hX hθ
  have hLb : ∀ k : Fin 2, homLop w (fun l => homPartial l F.b θ k) =
      R.b θ k - homCoeff R.b 0 k := fun k => homEq_b ha hp hpb hr hτ hα hσ hσs hm R hX hθ k
  have hLcp : ∀ j : ℕ+, homLop w (fun l => homLamDiag_gen ha (homPP hp hpb) (homPartial l F.cp θ)
      j) =
      homLamDiag_gen ha (homPP hp hpb) (R.cp θ) j + Complex.I * (W j : ℂ) * homLamDiag_gen ha
          (homPP hp
          hpb) (F.cp θ) j := by
    intro j
    have := homEq_cp_gen ha hp hpb hr hτ hα hσ hσs hm R hX hθ j (W := W)
    unfold homLop; push_cast at this; linear_combination this
  have hLcm : ∀ j : ℕ+, homLop w (fun l => homLamDiag_gen ha (homPP hp hpb) (homPartial l F.cm θ)
      j) =
      homLamDiag_gen ha (homPP hp hpb) (R.cm θ) j + (-Complex.I) * (W j : ℂ) * homLamDiag_gen ha
          (homPP hp
          hpb) (F.cm θ) j := by
    intro j
    have := homEq_cm_gen ha hp hpb hr hτ hα hσ hσs hm R hX hθ j (W := W)
    unfold homLop; push_cast at this; linear_combination this
  have hLP : ∀ i j : ℕ+, homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.P θ) i j) =
      homSent_gen ha hp hpb (R.P θ) i j + Complex.I * ((W i : ℂ) + (W j : ℂ)) * homSent_gen ha hp
          hpb (F.P
          θ) i j
          := by
    intro i j
    have := homEq_P_gen ha hp hpb hr hτ hα hσ hσs hm R hX hθ i j (W := W)
    unfold homLop; push_cast at this; linear_combination this
  have hLP' : ∀ i j : ℕ+, homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.P' θ) i j) =
      homSent_gen ha hp hpb (R.P' θ) i j + (-Complex.I) * ((W i : ℂ) + (W j : ℂ)) * homSent_gen ha
          hp hpb
          (F.P' θ)
          i j := by
    intro i j
    have := homEq_P'_gen ha hp hpb hr hτ hα hσ hσs hm R hX hθ i j (W := W)
    unfold homLop; push_cast at this; linear_combination this
  have hLQ : ∀ i j : ℕ+, homLop w (fun l => homSent_gen ha hp hpb (homPartial l F.Q θ) i j) =
      homSent_gen ha hp hpb (R.Q θ) i j - (if i = j then homSent_gen ha hp hpb (homCoeff R.Q 0) i j
          else 0)
        + Complex.I * ((W j : ℂ) - (W i : ℂ)) * homSent_gen ha hp hpb (F.Q θ) i j := by
    intro i j
    have := homEq_Q_gen ha hp hpb hr hτ hα hσ hσs hm R hX hθ i j (W := W)
    unfold homLop; push_cast at this; linear_combination this
  have hsymP : ∀ i j, homSent_gen ha hp hpb (F.P θ) i j = homSent_gen ha hp hpb (F.P θ) j i :=
    fun i j => homLam_entry_symm_gen ha hp hpb (F.symP θ hθ) i j
  have hsymP' : ∀ i j, homSent_gen ha hp hpb (F.P' θ) i j = homSent_gen ha hp hpb (F.P' θ) j i :=
    fun i j => homLam_entry_symm_gen ha hp hpb (F.symP' θ hθ) i j
  have hQt : ∀ i j, homSent_gen ha hp hpb (F.Qt θ) i j = homSent_gen ha hp hpb (F.Q θ) j i := by
    intro i j
    unfold homSent_gen
    rw [homLam_entry_eq_gen ha hp hpb, homLam_entry_eq_gen ha hp hpb, F.transQ θ hθ i j, mul_comm
        (homWt a
        p i : ℂ)]
  have hNhat : homNhat_gen R y z zb = ∑ k, homCoeff R.b 0 k * y k +
      ∑ j ∈ S, homSent_gen ha hp hpb (homCoeff R.Q 0) j j * z j * zb j := by
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
    hNhat, homRval_fin_gen ha hp hpb hz hzb R θ y]
  simp only [homRtheta_fin_gen ha hp hpb hz hzb, homLop_add, homLop_sumK, homLop_sum1, homLop_sum2,
      hLa,
    hLb, hLcp, hLcm, hLP, hLP', hLQ]
  have hbk : ∑ k, (R.b θ k - homCoeff R.b 0 k) * y k =
      ∑ k, R.b θ k * y k - ∑ k, homCoeff R.b 0 k * y k := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  have bP := homBlk_sym S Complex.I (fun i j => homSent_gen ha hp hpb (R.P θ) i j)
    (fun i j => homSent_gen ha hp hpb (F.P θ) i j) hsymP W z
  have bP' := homBlk_sym S (-Complex.I) (fun i j => homSent_gen ha hp hpb (R.P' θ) i j)
    (fun i j => homSent_gen ha hp hpb (F.P' θ) i j) hsymP' W zb
  have bQ := homBlk_Q S (fun i j => homSent_gen ha hp hpb (R.Q θ) i j) (fun i j => homSent_gen ha
      hp hpb
      (F.Q θ) i
      j)
    (fun i j => homSent_gen ha hp hpb (homCoeff R.Q 0) i j) (fun i j => homSent_gen ha hp hpb (F.Qt
        θ) i j)
        hQt W z
        zb
  have bC := homBlk_c S Complex.I (fun j => (homLamDiag_gen ha (homPP hp hpb) (R.cp θ) j : ℂ))
    (fun j => (homLamDiag_gen ha (homPP hp hpb) (F.cp θ) j : ℂ)) W z
  have bCm := homBlk_c S (-Complex.I) (fun j => (homLamDiag_gen ha (homPP hp hpb) (R.cm θ) j : ℂ))
    (fun j => (homLamDiag_gen ha (homPP hp hpb) (F.cm θ) j : ℂ)) W zb
  have hN : ∑ i ∈ S, (if i ∈ S then homSent_gen ha hp hpb (homCoeff R.Q 0) i i * z i * zb i else 0)
      =
      ∑ i ∈ S, homSent_gen ha hp hpb (homCoeff R.Q 0) i i * z i * zb i :=
    Finset.sum_congr rfl fun i hi => by simp [hi]
  rw [hbk]
  linear_combination bP + bP' + bQ + bC + bCm - hN

end main

end KAM.Wave
