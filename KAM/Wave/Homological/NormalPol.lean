/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.NormalOps
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The unconjugated pairing on `ℓ²` and polarization (blueprint-W `bpW:w4:components`,
step *Polarization*)

* `homPairL2 : ℓ² →L ℓ² →L ℂ`, `(v,w) ↦ ∑ v_j w_j`, a continuous bilinear form of norm `≤ 1`;
* `homPairL2_symm_of_entries`: for `B` with symmetric matrix, `⟨Bx,y⟩₀ = ⟨By,x⟩₀`;
* `norm_le_of_quadratic`: a symmetric `B` with `|⟨Bz,z⟩₀| ≤ K‖z‖²` has `‖B‖ ≤ K`
  (polarization and the parallelogram law, W4-E2).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- The raw pairing `∑ v_j w_j`. -/
def homPairF (v w : HomL2) : ℂ := ∑' j : ℕ+, (v j : ℂ) * (w j : ℂ)

theorem homPairF_summable (v w : HomL2) : Summable fun j : ℕ+ => (v j : ℂ) * (w j : ℂ) :=
  Summable.of_norm (homL2_pair_le v w).1

theorem homPairF_add_left (v v' w : HomL2) : homPairF (v + v') w = homPairF v w + homPairF v' w :=
    by
  unfold homPairF
  rw [← Summable.tsum_add (homPairF_summable v w) (homPairF_summable v' w)]
  refine tsum_congr fun j => ?_
  simp only [lp.coeFn_add, Pi.add_apply, add_mul]

theorem homPairF_smul_left (c : ℂ) (v w : HomL2) : homPairF (c • v) w = c * homPairF v w := by
  unfold homPairF
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem homPairF_comm (v w : HomL2) : homPairF v w = homPairF w v :=
  tsum_congr fun _ => mul_comm _ _

theorem homPairF_add_right (v w w' : HomL2) : homPairF v (w + w') = homPairF v w + homPairF v w' :=
    by
  rw [homPairF_comm, homPairF_add_left, homPairF_comm w, homPairF_comm w' ]

theorem homPairF_smul_right (c : ℂ) (v w : HomL2) : homPairF v (c • w) = c * homPairF v w := by
  rw [homPairF_comm, homPairF_smul_left, homPairF_comm]

theorem norm_homPairF_le (v w : HomL2) : ‖homPairF v w‖ ≤ 1 * ‖v‖ * ‖w‖ := by
  rw [one_mul]
  exact (homL2_pair_le v w).2

/-- The unconjugated pairing `⟨v, w⟩₀ = ∑ v_j w_j` as a continuous bilinear form on `ℓ²`. -/
def homPairL2 : HomL2 →L[ℂ] HomL2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ homPairF homPairF_add_left homPairF_smul_left homPairF_add_right
      homPairF_smul_right) 1 norm_homPairF_le

theorem homPairL2_apply (v w : HomL2) : homPairL2 v w = homPairF v w := rfl

theorem homPairL2_comm (v w : HomL2) : homPairL2 v w = homPairL2 w v := homPairF_comm v w

theorem homPairL2_single_right (v : HomL2) (j : ℕ+) : homPairL2 v (kamBasis ℂ j) = v j := by
  rw [homPairL2_apply, homPairF]
  have : (fun k : ℕ+ => (v k : ℂ) * (kamBasis ℂ j k : ℂ)) = fun k => if k = j then v j else 0 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp [kamBasis]
    · simp [kamBasis, hk]
  rw [this, tsum_ite_eq]

/-- A continuous linear functional vanishing on the basis vanishes. -/
theorem homCLM_eq_zero_of_basis (L : HomL2 →L[ℂ] ℂ) (h : ∀ j, L (kamBasis ℂ j) = 0) : L = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hs := (lp.hasSum_single (p := 2) (by norm_num) x).mapL L
  have hz : ∀ j : ℕ+, L (lp.single 2 j (x j)) = 0 := by
    intro j
    have : lp.single 2 j (x j) = x j • kamBasis ℂ j := by
      ext k
      by_cases hk : k = j
      · subst hk; simp [kamBasis]
      · simp [kamBasis, hk]
    rw [this, map_smul, h j, smul_zero]
  simp only [hz] at hs
  simpa using hs.unique hasSum_zero

/-- **Symmetric matrices pair symmetrically**: if `B_ij = B_ji` then `⟨Bx,y⟩₀ = ⟨By,x⟩₀`. -/
theorem homPairL2_symm_of_entries {B : HomOp} (hB : ∀ i j, kamEntry B i j = kamEntry B j i)
    (x y : HomL2) : homPairL2 (B x) y = homPairL2 (B y) x := by
  set S : HomL2 →L[ℂ] ℂ := ((homPairL2.flip y).comp B) - homPairL2 (B y) with hS
  have h0 : S = 0 := by
    refine homCLM_eq_zero_of_basis S fun j => ?_
    have e1 : homPairL2 (B (kamBasis ℂ j)) y = ∑' i : ℕ+, kamEntry B i j * y i := by
      rw [homPairL2_apply, homPairF]
      rfl
    have e2 : homPairL2 (B y) (kamBasis ℂ j) = ∑' i : ℕ+, kamEntry B j i * y i := by
      rw [homPairL2_single_right]
      exact ((homOp_hasSum B y j).tsum_eq).symm
    simp only [hS, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, e1, e2]
    rw [sub_eq_zero]
    exact tsum_congr fun i => by rw [hB i j]
  have := congrArg (fun L : HomL2 →L[ℂ] ℂ => L x) h0
  simp only [hS, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, sub_eq_zero] at this
  exact this

/-- **Polarization** (blueprint `bpW:w4:components`, step *Polarization*, with W4-E2): a
symmetric `B` with `|⟨Bz,z⟩₀| ≤ K‖z‖²` has `‖B‖ ≤ K`. -/
theorem norm_le_of_quadratic {B : HomOp} (hB : ∀ i j, kamEntry B i j = kamEntry B j i) {K : ℝ}
    (hq : ∀ z : HomL2, ‖homPairL2 (B z) z‖ ≤ K * ‖z‖ ^ 2) : ‖B‖ ≤ K := by
  have hK : 0 ≤ K := by
    have := hq (kamBasis ℂ 1)
    rw [norm_kamBasis] at this
    exact (norm_nonneg _).trans (by simpa using this)
  have hxy : ∀ x y : HomL2, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖homPairL2 (B x) y‖ ≤ K := by
    intro x y hx hy
    have e : (4 : ℂ) * homPairL2 (B x) y =
        homPairL2 (B (x + y)) (x + y) - homPairL2 (B (x - y)) (x - y) := by
      have hs := homPairL2_symm_of_entries hB y x
      simp only [map_add, map_sub, add_apply, sub_apply]
      rw [← hs]
      ring
    have h4 : ‖(4 : ℂ) * homPairL2 (B x) y‖ ≤ K * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) := by
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      nlinarith [hq (x + y), hq (x - y)]
    have hpar : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      have := parallelogram_law_with_norm ℂ x y
      linarith
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hy2 : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
    rw [norm_mul] at h4
    have : ‖(4 : ℂ)‖ = 4 := by simp
    rw [this, hpar] at h4
    nlinarith
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hK fun x hx => ?_
  refine norm_le_of_pairing_le fun y hy => ?_
  exact hxy x y hx.le hy

end KAM.Wave
