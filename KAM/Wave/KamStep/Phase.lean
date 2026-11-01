/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamSupport.KamSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The phase space as a Banach space (blueprint-W `bpW:w5:setting`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`StepPhase r` is the carrier `KamPhase = ℂ² × ℂ² × ℓ² × ℓ²` (weighted coordinates of
`bpW:w1:kam-space`) equipped with the norm `|W|_{q,r}` (`kamNorm r`): a complex Banach space for
`r > 0`, in which the flow lemma of W1 (`KAM/Wave/Analytic/Flow`) is applied
(`bpW:w5:flow`). Since the norm depends on the representative weights only through the fixed
carrier, the same type serves every smoothing exponent `q` (the weight is in the representatives).
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- `𝒫` with the norm `|·|_r` of `bpW:w1:kam-space`. -/
def StepPhase (r : ℝ) : Type := KamPhase

instance (r : ℝ) : AddCommGroup (StepPhase r) := inferInstanceAs (AddCommGroup KamPhase)
instance (r : ℝ) : Module ℂ (StepPhase r) := inferInstanceAs (Module ℂ KamPhase)

namespace StepPhase

variable {r : ℝ}

/-- The identification with `KamPhase`. -/
def toK (W : StepPhase r) : KamPhase := W

/-- The identification from `KamPhase`. -/
def ofK (W : KamPhase) : StepPhase r := W

@[simp] theorem toK_add (W W' : StepPhase r) : toK (W + W') = toK W + toK W' := rfl
@[simp] theorem toK_smul (c : ℂ) (W : StepPhase r) : toK (c • W) = c • toK W := rfl
@[simp] theorem toK_zero : toK (0 : StepPhase r) = 0 := rfl
@[simp] theorem toK_neg (W : StepPhase r) : toK (-W) = -toK W := rfl

end StepPhase

theorem kamNorm_add_le {r : ℝ} (hr : 0 < r) (W W' : KamPhase) :
    kamNorm r (W + W') ≤ kamNorm r W + kamNorm r W' := by
  unfold kamNorm
  have h1 := norm_add_le W.1 W'.1
  have h2 := norm_add_le W.2.1 W'.2.1
  have h3 := norm_add_le W.2.2.1 W'.2.2.1
  have h4 := norm_add_le W.2.2.2 W'.2.2.2
  have e2 : ‖W.2.1 + W'.2.1‖ / r ^ 2 ≤ (‖W.2.1‖ + ‖W'.2.1‖) / r ^ 2 :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have e3 : ‖W.2.2.1 + W'.2.2.1‖ / r ≤ (‖W.2.2.1‖ + ‖W'.2.2.1‖) / r :=
    div_le_div_of_nonneg_right h3 hr.le
  have e4 : ‖W.2.2.2 + W'.2.2.2‖ / r ≤ (‖W.2.2.2‖ + ‖W'.2.2.2‖) / r :=
    div_le_div_of_nonneg_right h4 hr.le
  simp only [Prod.fst_add, Prod.snd_add]
  rw [add_div] at e2 e3 e4
  linarith

theorem kamNorm_neg {r : ℝ} (W : KamPhase) : kamNorm r (-W) = kamNorm r W := by
  unfold kamNorm; simp

theorem kamNorm_smul {r : ℝ} (c : ℂ) (W : KamPhase) : kamNorm r (c • W) = ‖c‖ * kamNorm r W := by
  unfold kamNorm
  simp only [Prod.smul_fst, Prod.smul_snd, norm_smul]
  ring

/-- The norm `|·|_r` as an additive group norm. -/
def kamAddGroupNorm {r : ℝ} (hr : 0 < r) : AddGroupNorm (StepPhase r) where
  toFun W := kamNorm r (StepPhase.toK W)
  map_zero' := by
    show kamNorm r (0 : KamPhase) = 0
    unfold kamNorm; simp
  add_le' W W' := kamNorm_add_le hr _ _
  neg' W := kamNorm_neg _
  eq_zero_of_map_eq_zero' W h := kamNorm_eq_zero hr h

instance stepPhaseNormed (r : ℝ) [Fact (0 < r)] : NormedAddCommGroup (StepPhase r) :=
  (kamAddGroupNorm (Fact.out : 0 < r)).toNormedAddCommGroup

theorem stepPhase_norm_eq (r : ℝ) [Fact (0 < r)] (W : StepPhase r) :
    ‖W‖ = kamNorm r (StepPhase.toK W) := rfl

instance stepPhaseNormedSpace (r : ℝ) [Fact (0 < r)] : NormedSpace ℂ (StepPhase r) where
  norm_smul_le c W := by
    rw [stepPhase_norm_eq, stepPhase_norm_eq]
    exact (kamNorm_smul c _).le


theorem norm_kamPhase_le_kamNorm {r : ℝ} (hr : 0 < r) (W : KamPhase) :
    ‖W‖ ≤ max 1 (max (r ^ 2) r) * kamNorm r W := by
  have n1 : 0 ≤ ‖W.1‖ := norm_nonneg _
  have n2 : 0 ≤ ‖W.2.1‖ / r ^ 2 := by positivity
  have n3 : 0 ≤ ‖W.2.2.1‖ / r := by positivity
  have n4 : 0 ≤ ‖W.2.2.2‖ / r := by positivity
  have hk : 0 ≤ kamNorm r W := by unfold kamNorm; positivity
  have m1 : (1 : ℝ) ≤ max 1 (max (r ^ 2) r) := le_max_left _ _
  have m2 : r ^ 2 ≤ max 1 (max (r ^ 2) r) := (le_max_left _ _).trans (le_max_right _ _)
  have m3 : r ≤ max 1 (max (r ^ 2) r) := (le_max_right _ _).trans (le_max_right _ _)
  have c1 : ‖W.1‖ ≤ max 1 (max (r ^ 2) r) * kamNorm r W := by
    unfold kamNorm; nlinarith
  have c2 : ‖W.2.1‖ ≤ max 1 (max (r ^ 2) r) * kamNorm r W := by
    have : ‖W.2.1‖ = r ^ 2 * (‖W.2.1‖ / r ^ 2) := by field_simp
    have h : ‖W.2.1‖ / r ^ 2 ≤ kamNorm r W := by unfold kamNorm; linarith
    nlinarith [mul_le_mul m2 h n2 (by positivity)]
  have c3 : ‖W.2.2.1‖ ≤ max 1 (max (r ^ 2) r) * kamNorm r W := by
    have : ‖W.2.2.1‖ = r * (‖W.2.2.1‖ / r) := by field_simp
    have h : ‖W.2.2.1‖ / r ≤ kamNorm r W := by unfold kamNorm; linarith
    nlinarith [mul_le_mul m3 h n3 (by positivity)]
  have c4 : ‖W.2.2.2‖ ≤ max 1 (max (r ^ 2) r) * kamNorm r W := by
    have : ‖W.2.2.2‖ = r * (‖W.2.2.2‖ / r) := by field_simp
    have h : ‖W.2.2.2‖ / r ≤ kamNorm r W := by unfold kamNorm; linarith
    nlinarith [mul_le_mul m3 h n4 (by positivity)]
  rw [Prod.norm_def, Prod.norm_def, Prod.norm_def]
  refine max_le c1 (max_le c2 (max_le c3 c4))

theorem kamNorm_le_norm_kamPhase {r : ℝ} (hr : 0 < r) (W : KamPhase) :
    kamNorm r W ≤ (1 + 1 / r ^ 2 + 2 / r) * ‖W‖ := by
  have h1 : ‖W.1‖ ≤ ‖W‖ := by
    rw [Prod.norm_def]; exact le_max_left _ _
  have h2 : ‖W.2.1‖ ≤ ‖W‖ := by
    rw [Prod.norm_def, Prod.norm_def]; exact (le_max_left _ _).trans (le_max_right _ _)
  have h3 : ‖W.2.2.1‖ ≤ ‖W‖ := by
    rw [Prod.norm_def, Prod.norm_def, Prod.norm_def]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h4 : ‖W.2.2.2‖ ≤ ‖W‖ := by
    rw [Prod.norm_def, Prod.norm_def, Prod.norm_def]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  unfold kamNorm
  have e2 : ‖W.2.1‖ / r ^ 2 ≤ ‖W‖ / r ^ 2 := div_le_div_of_nonneg_right h2 (by positivity)
  have e3 : ‖W.2.2.1‖ / r ≤ ‖W‖ / r := div_le_div_of_nonneg_right h3 hr.le
  have e4 : ‖W.2.2.2‖ / r ≤ ‖W‖ / r := div_le_div_of_nonneg_right h4 hr.le
  have : (1 + 1 / r ^ 2 + 2 / r) * ‖W‖ = ‖W‖ + ‖W‖ / r ^ 2 + ‖W‖ / r + ‖W‖ / r := by ring
  rw [this]; linarith

instance stepPhaseComplete (r : ℝ) [Fact (0 < r)] : CompleteSpace (StepPhase r) := by
  have hr : 0 < r := Fact.out
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hc : CauchySeq (fun n => StepPhase.toK (u n)) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu (ε / max 1 (max (r ^ 2) r)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have := hN m hm n hn
    rw [dist_eq_norm] at this ⊢
    have hb := norm_kamPhase_le_kamNorm hr (StepPhase.toK (u m) - StepPhase.toK (u n))
    have : kamNorm r (StepPhase.toK (u m) - StepPhase.toK (u n)) < ε / max 1 (max (r ^ 2) r) :=
      this
    have hpos : 0 < max 1 (max (r ^ 2) r) := by positivity
    calc ‖StepPhase.toK (u m) - StepPhase.toK (u n)‖ ≤ _ := hb
      _ < max 1 (max (r ^ 2) r) * (ε / max 1 (max (r ^ 2) r)) :=
        mul_lt_mul_of_pos_left this hpos
      _ = ε := by field_simp
  obtain ⟨W, hW⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨StepPhase.ofK W, ?_⟩
  rw [Metric.tendsto_atTop] at hW ⊢
  intro ε hε
  have hK : 0 < 1 + 1 / r ^ 2 + 2 / r := by positivity
  obtain ⟨N, hN⟩ := hW (ε / (1 + 1 / r ^ 2 + 2 / r)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [dist_eq_norm] at h1 ⊢
  have hb := kamNorm_le_norm_kamPhase hr (StepPhase.toK (u n) - W)
  calc ‖u n - StepPhase.ofK W‖ = kamNorm r (StepPhase.toK (u n) - W) := rfl
    _ ≤ _ := hb
    _ < (1 + 1 / r ^ 2 + 2 / r) * (ε / (1 + 1 / r ^ 2 + 2 / r)) :=
        mul_lt_mul_of_pos_left h1 hK
    _ = ε := by field_simp

end KAM.Wave
