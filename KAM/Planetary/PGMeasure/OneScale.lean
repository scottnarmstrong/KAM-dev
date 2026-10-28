/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Planetary.PG.Setting
public import KAM.Planetary.PGMeasure.CompactLipschitz
public import KAM.Planetary.PGMeasure.AffineSlab
public import KAM.Planetary.PGMeasure.LatticeTail

/-!
# P Part 5: single-scale fast Diophantine exclusion (`bpP:p5:dio-one`)

`dio_one`: the set of actions `I ∈ V` whose fast frequency is not `(γ, τ)`-Diophantine has volume
at most `dioConstant d τ * γ`, where `dioConstant = 2 Λg^a S(a+b, τ) (2 Ry)^(a-1)`. The proof pushes
the resonant slabs `{y ∈ [-Ry, Ry]^a : |k·y| < γ |k|₁^(-τ)}` (`affine_slab`, summed with
`lattice_tail`) through the `Λg`-Lipschitz frozen inverse, using `μH[a] = volume` on `ℝ^a` with the
max norm. Also fixes the chosen inverse and its constants `pgInverse`, `pgInverseL`, `pgInverseR`
(design signature of `bpP:p4:lip-inverse`), which are used by downstream modules.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace KAM.Planetary

variable {a b : ℕ}

/-- Chosen inverse and its constants come from the same frozen-inverse specification. -/
def pgInverse (d : PGData a b) : (Fin a → ℝ) → Fin a → ℝ :=
  (lip_inverse d.hW d.hVb d.hVW d.hfreq).choose

def pgInverseL (d : PGData a b) : ℝ :=
  (lip_inverse d.hW d.hVb d.hVW d.hfreq).choose_spec.choose

def pgInverseR (d : PGData a b) : ℝ :=
  (lip_inverse d.hW d.hVb d.hVW d.hfreq).choose_spec.choose_spec.choose

/-- The specification of the chosen inverse and its constants. -/
theorem pgInverse_spec (d : PGData a b) :
    1 ≤ pgInverseL d ∧ 0 < pgInverseR d ∧
      ContinuousOn (fastFrequency d.H0) d.W ∧ IsCompact (fastFrequency d.H0 '' closure d.V) ∧
      (∀ I ∈ d.W, pgInverse d (fastFrequency d.H0 I) = I) ∧
      (∀ y ∈ fastFrequency d.H0 '' closure d.V, ‖y‖ ≤ pgInverseR d) ∧
      ∀ y ∈ fastFrequency d.H0 '' closure d.V, ∀ y' ∈ fastFrequency d.H0 '' closure d.V,
        ‖pgInverse d y - pgInverse d y'‖ ≤ pgInverseL d * ‖y - y'‖ :=
  (lip_inverse d.hW d.hVb d.hVW d.hfreq).choose_spec.choose_spec.choose_spec

def dioConstant (d : PGData a b) (tau : ℝ) : ℝ :=
  2*(pgInverseL d)^a*latticeS (a+b) tau*(2*pgInverseR d)^(a-1)

/-- `latticeS` is monotone in the dimension. -/
theorem latticeS_mono {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {tau : ℝ} (hm : (m : ℝ) < tau) :
    latticeS n tau ≤ latticeS m tau := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have h1 : (0 : ℝ) < tau - m := by linarith
  have h2 : (0 : ℝ) < tau - n := by linarith
  have hp : (3 : ℝ) ^ (n - 1) ≤ 3 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hq : (tau + 1 - n) / (tau - n) ≤ (tau + 1 - m) / (tau - m) := by
    rw [div_le_div_iff₀ h2 h1]; nlinarith
  unfold latticeS
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul (by gcongr) hq (div_nonneg (by linarith) h2.le) (by positivity)

/-- The union of the resonant slabs `|k·y| < γ |k|₁^(-τ)` inside the cube `[-R, R]^a`. -/
def resonantSlabs (a : ℕ) (gamma tau R : ℝ) : Set (Fin a → ℝ) :=
  {y | (∀ i, y i ∈ Icc (-R) R) ∧ ∃ k : Fin a → ℤ, k ≠ 0 ∧
    |∑ i, ((k i : ℤ) : ℝ) * y i| < gamma / (∑ i, |((k i : ℤ) : ℝ)|) ^ tau}

/-- Slab estimate summed over the lattice (`affine_slab`, `lattice_tail`). -/
theorem volume_resonantSlabs_le (ha : 0 < a) {tau : ℝ} (htau : (a : ℝ) < tau) {gamma R : ℝ}
    (hγ : 0 < gamma) (hR : 0 < R) :
    volume (resonantSlabs a gamma tau R) ≤
      ENNReal.ofReal (2 * gamma * (2 * R) ^ (a - 1) * latticeS a tau) := by
  have hw : ∀ k : {k : Fin a → ℤ // k ≠ 0}, 0 < latticeWeight tau k.val := fun k => by
    unfold latticeWeight
    refine Real.rpow_pos_of_pos ?_ _
    obtain ⟨i, hi⟩ := Function.ne_iff.mp k.2
    exact Finset.sum_pos' (fun _ _ => abs_nonneg _)
      ⟨i, Finset.mem_univ i, abs_pos.2 (by exact_mod_cast hi)⟩
  have hc : 0 ≤ 2 * gamma * (2 * R) ^ (a - 1) := by positivity
  let Sl : {k : Fin a → ℤ // k ≠ 0} → Set (Fin a → ℝ) := fun k =>
    {y | (∀ i, y i ∈ Icc (-R) R) ∧
      |∑ i, ((k.val i : ℤ) : ℝ) * y i + 0| < gamma * latticeWeight tau k.val}
  have hslab : ∀ k, volume (Sl k) ≤
      ENNReal.ofReal (2 * gamma * (2 * R) ^ (a - 1) * latticeWeight tau k.val) := by
    intro k
    obtain ⟨i, hi⟩ := Function.ne_iff.mp k.2
    have hne : (fun i => ((k.val i : ℤ) : ℝ)) ≠ 0 := by
      intro h
      have := congrFun h i
      exact hi (by simpa using this)
    have h := affine_slab ha _ hne 0 R (gamma * latticeWeight tau k.val) hR
      (mul_pos hγ (hw k))
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hn1 : 1 ≤ ‖(fun i => ((k.val i : ℤ) : ℝ))‖ := by
      have h1 : (1 : ℝ) ≤ |((k.val i : ℤ) : ℝ)| := by
        have : (1 : ℤ) ≤ |k.val i| := Int.one_le_abs hi
        exact_mod_cast this
      exact h1.trans (by simpa using norm_le_pi_norm (fun i => ((k.val i : ℤ) : ℝ)) i)
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ 2 * gamma * (2 * R) ^ (a - 1) * latticeWeight tau k.val :=
      mul_nonneg hc (hw k).le
    nlinarith
  have hsub : resonantSlabs a gamma tau R ⊆ ⋃ k, Sl k := by
    rintro y ⟨hy, k, hk, hlt⟩
    refine mem_iUnion.2 ⟨⟨k, hk⟩, hy, ?_⟩
    have hnn : 0 ≤ ∑ i, |((k i : ℤ) : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have : gamma * latticeWeight tau k = gamma / (∑ i, |((k i : ℤ) : ℝ)|) ^ tau := by
      unfold latticeWeight
      rw [Real.rpow_neg hnn, div_eq_mul_inv]
    simp only [add_zero]
    rw [this]
    exact hlt
  obtain ⟨hs, hsum, -⟩ := lattice_tail ha htau
  calc volume (resonantSlabs a gamma tau R) ≤ volume (⋃ k, Sl k) := measure_mono hsub
    _ ≤ ∑' k, volume (Sl k) := measure_iUnion_le _
    _ ≤ ∑' k : {k : Fin a → ℤ // k ≠ 0},
        ENNReal.ofReal (2 * gamma * (2 * R) ^ (a - 1) * latticeWeight tau k.val) :=
      ENNReal.tsum_le_tsum hslab
    _ = ENNReal.ofReal (∑' k : {k : Fin a → ℤ // k ≠ 0},
        2 * gamma * (2 * R) ^ (a - 1) * latticeWeight tau k.val) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hc (hw k).le)
        (hs.mul_left _)).symm
    _ ≤ _ := by
      rw [tsum_mul_left]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsum hc)

/-- A set covered by an `L`-Lipschitz image of a subset of `T` has volume at most `L^a vol T`. -/
theorem volume_le_of_lipschitz {E K T : Set (Fin a → ℝ)} {g : (Fin a → ℝ) → Fin a → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hg : ∀ y ∈ K, ∀ y' ∈ K, ‖g y - g y'‖ ≤ L * ‖y - y'‖)
    (hE : E ⊆ g '' (K ∩ T)) : volume E ≤ ENNReal.ofReal L ^ a * volume T := by
  have hH : (μH[(a : ℝ)] : Measure (Fin a → ℝ)) = volume := by
    simpa using hausdorffMeasure_pi_real (ι := Fin a)
  have hLip : LipschitzOnWith (Real.toNNReal L) g K :=
    LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal L hL]
      exact hg y hy y' hy'
  calc volume E = μH[(a : ℝ)] E := by rw [hH]
    _ ≤ μH[(a : ℝ)] (g '' (K ∩ T)) := measure_mono hE
    _ ≤ (Real.toNNReal L : ℝ≥0∞) ^ (a : ℝ) * μH[(a : ℝ)] (K ∩ T) :=
      (hLip.mono inter_subset_left).hausdorffMeasure_image_le (Nat.cast_nonneg a)
    _ ≤ ENNReal.ofReal L ^ a * volume T := by
      rw [ENNReal.rpow_natCast, hH]
      exact mul_le_mul' le_rfl (measure_mono inter_subset_right)

theorem dio_one (d : PGData a b) {tau : ℝ} (ht : (a+b:ℕ) < tau) :
    0 < dioConstant d tau ∧ ∀ gamma : ℝ, 0 < gamma →
      volume {I ∈ d.V | ¬ KAM.IsDiophantine gamma tau
        (fastFrequency d.H0 I)} ≤
          ENNReal.ofReal (dioConstant d tau*gamma) := by
  obtain ⟨hL, hR, -, -, hginv, hRb, hglip⟩ := pgInverse_spec d
  have ha := d.ha
  have htau : (a : ℝ) < tau :=
    lt_of_le_of_lt (by exact_mod_cast Nat.le_add_right a b) ht
  have hS : 0 < latticeS (a+b) tau := by
    have h1 : (0 : ℝ) < tau + 1 - ((a + b : ℕ) : ℝ) := by linarith
    have h2 : (0 : ℝ) < tau - ((a + b : ℕ) : ℝ) := by linarith
    unfold latticeS; positivity
  refine ⟨by unfold dioConstant; positivity, fun γ hγ => ?_⟩
  have hbad : {I ∈ d.V | ¬ KAM.IsDiophantine γ tau (fastFrequency d.H0 I)} ⊆
      pgInverse d '' (fastFrequency d.H0 '' closure d.V ∩
        resonantSlabs a γ tau (pgInverseR d)) := by
    rintro I ⟨hI, hnd⟩
    have hy : fastFrequency d.H0 I ∈ fastFrequency d.H0 '' closure d.V :=
      ⟨I, subset_closure hI, rfl⟩
    refine ⟨fastFrequency d.H0 I, ⟨hy, fun i => ?_, ?_⟩, hginv I (d.hVW (subset_closure hI))⟩
    · have := (norm_le_pi_norm (fastFrequency d.H0 I) i).trans (hRb _ hy)
      exact abs_le.1 (by simpa using this)
    · unfold KAM.IsDiophantine at hnd
      push Not at hnd
      obtain ⟨k, hk, hlt⟩ := hnd
      exact ⟨k, hk, hlt⟩
  have h1 := volume_le_of_lipschitz (by linarith) hglip hbad
  have h2 := volume_resonantSlabs_le ha htau hγ hR
  have hSle : latticeS a tau ≤ latticeS (a + b) tau :=
    latticeS_mono ha (Nat.le_add_right a b) ht
  refine h1.trans ?_
  calc ENNReal.ofReal (pgInverseL d) ^ a * volume (resonantSlabs a γ tau (pgInverseR d))
      ≤ ENNReal.ofReal (pgInverseL d) ^ a *
          ENNReal.ofReal (2 * γ * (2 * pgInverseR d) ^ (a - 1) * latticeS a tau) :=
        mul_le_mul' le_rfl h2
    _ ≤ ENNReal.ofReal (dioConstant d tau * γ) := by
        rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        unfold dioConstant
        have h3 : 0 ≤ pgInverseL d ^ a * (2 * γ * (2 * pgInverseR d) ^ (a - 1)) := by
          have := hL; have := hR; positivity
        calc pgInverseL d ^ a * (2 * γ * (2 * pgInverseR d) ^ (a - 1) * latticeS a tau)
            = (pgInverseL d ^ a * (2 * γ * (2 * pgInverseR d) ^ (a - 1))) * latticeS a tau := by
              ring
          _ ≤ (pgInverseL d ^ a * (2 * γ * (2 * pgInverseR d) ^ (a - 1))) *
                latticeS (a + b) tau := mul_le_mul_of_nonneg_left hSle h3
          _ = _ := by ring

end KAM.Planetary

end
