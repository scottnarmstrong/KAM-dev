/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.DiagonalTensor
public import KAM.Planetary.Nondegeneracy.FiniteType

/-!
# Nondegeneracy: stability of the amount and its scaling

Blueprint P, Part 10 (`bpP:p10:stability`, `bpP:p10:scaling`): the stability of the amount
`betaMu` under perturbation of the map in the diagonal tensor norms, and its comparison under a
coordinatewise positive rescaling of the map.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise Pointwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {d m : ℕ}

/-! ### Coordinate combinations and Cauchy–Schwarz -/

lemma abs_sum_mul_le_length2 (c a : Vec m) (hc : length2 c = 1) :
    |∑ i, c i * a i| ≤ length2 a := by
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ c a
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ c (fun i => -a i)
  have hc' : √(∑ i, c i ^ 2) = 1 := hc
  simp only [neg_sq, mul_neg, Finset.sum_neg_distrib, hc', one_mul] at h1 h2
  have hl : length2 a = √(∑ i, a i ^ 2) := rfl
  rw [hl]
  exact abs_le.2 ⟨by linarith, h1⟩

/-- The linear functional `x ↦ ∑ cᵢ xᵢ`. -/
def coordForm (c : Vec m) : Vec m →L[ℝ] ℝ := ∑ i, c i • ContinuousLinearMap.proj i

lemma coordForm_apply (c x : Vec m) : coordForm c x = ∑ i, c i * x i := by
  simp [coordForm]

lemma analyticOnNhd_coordForm {B : Set (Vec d)} {F : Vec d → Vec m}
    (hF : AnalyticOnNhd ℝ F B) (c : Vec m) :
    AnalyticOnNhd ℝ (fun z => ∑ i, c i * F z i) B := fun y hy => by
  have := (coordForm c).analyticAt (F y) |>.comp (hF y hy)
  simpa [Function.comp_def, coordForm_apply] using this

lemma iteratedFDeriv_coordForm {F : Vec d → Vec m} {y : Vec d} (c : Vec m) (k : ℕ)
    (hF : ContDiffAt ℝ k F y) (v : Fin k → Vec d) :
    iteratedFDeriv ℝ k (fun z => ∑ i, c i * F z i) y v = ∑ i, c i * iteratedFDeriv ℝ k F y v i := by
  have h := (coordForm c).iteratedFDeriv_comp_left hF le_rfl (i := k)
  have e : (fun z => ∑ i, c i * F z i) = coordForm c ∘ F := by
    funext z; simp [coordForm_apply]
  rw [e, h]
  simp [coordForm_apply]

/-- The diagonal values of the derivative of a map are bounded on the Euclidean unit sphere. -/
lemma bddAbove_jetNorm (F : Vec d → Vec m) (ν : ℕ) (y : Vec d) :
    BddAbove {r | ∃ v : Vec d, length2 v = 1 ∧
      r = length2 (iteratedFDeriv ℝ ν F y (fun _ => v))} := by
  refine ⟨√m * ‖iteratedFDeriv ℝ ν F y‖, ?_⟩
  rintro r ⟨v, hv, rfl⟩
  refine (length2_le_sqrt_mul_norm _).trans ?_
  gcongr
  have h1 := (iteratedFDeriv ℝ ν F y).le_opNorm (fun _ => v)
  have h2 : ∏ _i : Fin ν, ‖v‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (norm_le_one_of_length2 hv)
  calc _ ≤ _ := h1
    _ ≤ ‖iteratedFDeriv ℝ ν F y‖ * 1 := by gcongr
    _ = _ := mul_one _

lemma length2_diag_le_jetNorm (F : Vec d → Vec m) (ν : ℕ) (y : Vec d) {v : Vec d}
    (hv : ν = 0 ∨ length2 v = 1) :
    length2 (iteratedFDeriv ℝ ν F y (fun _ => v)) ≤ jetNorm F ν y := by
  by_cases hν : ν = 0
  · subst hν
    simp [jetNorm, iteratedFDeriv_zero_apply]
  · simp only [jetNorm, hν, ite_false]
    exact le_csSup (bddAbove_jetNorm F ν y) ⟨v, hv.resolve_left hν, rfl⟩

/-- A jet-norm bound bounds every coordinate combination on the unit sphere. -/
lemma abs_coordJet_le {B : Set (Vec d)} (hB : IsOpen B) {F : Vec d → Vec m}
    (hF : AnalyticOnNhd ℝ F B) {y : Vec d} (hy : y ∈ B) {c : Vec m} (hc : length2 c = 1)
    {k : ℕ} {T : ℝ} (hT : jetNorm F k y ≤ T) {v : Vec d} (hv : k = 0 ∨ length2 v = 1) :
    |iteratedFDeriv ℝ k (fun z => ∑ i, c i * F z i) y (fun _ => v)| ≤ T := by
  have hcd : ContDiffAt ℝ k F y :=
    ((hF.contDiffOn hB.uniqueDiffOn) y hy).contDiffAt (hB.mem_nhds hy) |>.of_le le_top
  rw [iteratedFDeriv_coordForm c k hcd]
  exact (abs_sum_mul_le_length2 c _ hc).trans ((length2_diag_le_jetNorm F k y hv).trans hT)

/-! ### Differences of diagonal jets -/

lemma jetOp_le_add_of {ν : ℕ} (T T' : (Fin d → ℝ) [×ν]→L[ℝ] ℝ) {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ v : Vec d, length2 v = 1 → |T (fun _ => v) - T' (fun _ => v)| ≤ E) :
    jetOp T ≤ jetOp T' + E := by
  refine Real.sSup_le ?_ (add_nonneg (jetOp_nonneg T') hE)
  rintro r ⟨v, hv, rfl⟩
  have h2 : |T' (fun _ => v)| ≤ jetOp T' := le_csSup (bddAbove_jetOp T') ⟨v, hv, rfl⟩
  have := h v hv
  have h3 : |T (fun _ => v)| ≤ |T' (fun _ => v)| + |T (fun _ => v) - T' (fun _ => v)| := by
    have e : T (fun _ => v) = T' (fun _ => v) + (T (fun _ => v) - T' (fun _ => v)) := by ring
    rw [e]; exact abs_add_le _ _ |>.trans (by simp)
  linarith

lemma abs_scalarJet_sub_le {g g' : Vec d → ℝ} {y : Vec d} (ν : ℕ)
    (hg : ContDiffAt ℝ ν g y) (hg' : ContDiffAt ℝ ν g' y) {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ v : Vec d, (ν = 0 ∨ length2 v = 1) →
      |iteratedFDeriv ℝ ν (fun z => g' z - g z) y (fun _ => v)| ≤ E) :
    |scalarJet g' ν y - scalarJet g ν y| ≤ E := by
  have hsub : iteratedFDeriv ℝ ν (fun z => g' z - g z) y =
      iteratedFDeriv ℝ ν g' y - iteratedFDeriv ℝ ν g y :=
    iteratedFDeriv_sub_apply hg' hg
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · have h0 := h 0 (Or.inl rfl)
    rw [hsub] at h0
    simp only [scalarJet, ite_true]
    simp only [sub_apply, iteratedFDeriv_zero_apply] at h0
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans h0
  · rw [hsub] at h
    have e1 : ∀ T : (Fin d → ℝ) [×ν]→L[ℝ] ℝ,
        sSup {r | ∃ v : Vec d, length2 v = 1 ∧ r = |T (fun _ => v)|} = jetOp T := fun _ => rfl
    simp only [scalarJet, hν.ne', ite_false, e1]
    have a1 := jetOp_le_add_of (iteratedFDeriv ℝ ν g' y) (iteratedFDeriv ℝ ν g y) hE
      fun v hv => by simpa using h v (Or.inr hv)
    have a2 := jetOp_le_add_of (iteratedFDeriv ℝ ν g y) (iteratedFDeriv ℝ ν g' y) hE
      fun v hv => by
        have := h v (Or.inr hv)
        simpa [abs_sub_comm] using this
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-! ### Stability -/

lemma sq_sub_eq (ω ω' : Vec d → Vec m) (c : Vec m) (z : Vec d) :
    squaredForm ω' c z - squaredForm ω c z =
      (∑ i, c i * (ω' z i - ω z i)) *
        (2 * (∑ i, c i * ω z i) + ∑ i, c i * (ω' z i - ω z i)) := by
  simp only [squaredForm, mul_sub, Finset.sum_sub_distrib]
  ring

lemma stability_pointwise (hm : 0 < m) {B K : Set (Vec d)} (hB : IsOpen B) (hKB : K ⊆ B)
    {ω ω' : Vec d → Vec m} (hAn : AnalyticOnNhd ℝ ω B) (hAn' : AnalyticOnNhd ℝ ω' B)
    (μ : ℕ) {M θ : ℝ} (hM : 0 ≤ M) (hθ : 0 ≤ θ)
    (hBound : ∀ ν ≤ μ, ∀ y ∈ K, jetNorm ω ν y ≤ M)
    (hDiff : ∀ ν ≤ μ, ∀ y ∈ K, jetNorm (fun z => ω' z - ω z) ν y ≤ θ)
    {c : Vec m} (hc : c ∈ sphere m) {y : Vec d} (hy : y ∈ K) {ν : ℕ} (hν : ν ≤ μ)
    {v : Vec d} (hv : ν = 0 ∨ length2 v = 1) :
    |iteratedFDeriv ℝ ν (fun z => squaredForm ω' c z - squaredForm ω c z) y (fun _ => v)| ≤
      2 ^ ν * θ * (2 * M + θ) := by
  have _ := And.intro hm hM
  have hyB : y ∈ B := hKB hy
  have hD : AnalyticOnNhd ℝ (fun z => ω' z - ω z) B := fun z hz => (hAn' z hz).sub (hAn z hz)
  have hW : AnalyticOnNhd ℝ (fun z => ∑ i, c i * (ω' z i - ω z i)) B :=
    analyticOnNhd_coordForm hD c
  have hV := analyticOnNhd_coordForm hAn c
  have hU : AnalyticOnNhd ℝ (fun z => 2 * (∑ i, c i * ω z i) + ∑ i, c i * (ω' z i - ω z i)) B :=
    fun z hz => (analyticAt_const.mul (hV z hz)).add (hW z hz)
  have e : (fun z => squaredForm ω' c z - squaredForm ω c z) =
      fun z => (∑ i, c i * (ω' z i - ω z i)) *
        (2 * (∑ i, c i * ω z i) + ∑ i, c i * (ω' z i - ω z i)) :=
    funext (sq_sub_eq ω ω' c)
  rw [e, f_leib hB hW hU hyB v ν]
  have hcd : ∀ (f : Vec d → ℝ) (k : ℕ), AnalyticOnNhd ℝ f B → ContDiffAt ℝ k f y := fun f k hf =>
    ((hf.contDiffOn hB.uniqueDiffOn) y hyB).contDiffAt (hB.mem_nhds hyB) |>.of_le le_top
  have hvk : ∀ k ≤ ν, k = 0 ∨ length2 v = 1 := fun k hk => by
    rcases hv with h0 | h1
    · exact Or.inl (Nat.le_zero.1 (h0 ▸ hk))
    · exact Or.inr h1
  have hbW : ∀ k ≤ ν, |iteratedFDeriv ℝ k (fun z => ∑ i, c i * (ω' z i - ω z i)) y
      (fun _ => v)| ≤ θ := fun k hk =>
    abs_coordJet_le hB hD hyB hc (hDiff k (hk.trans hν) y hy) (hvk k hk)
  have hbV : ∀ k ≤ ν, |iteratedFDeriv ℝ k (fun z => ∑ i, c i * ω z i) y (fun _ => v)| ≤ M :=
    fun k hk => abs_coordJet_le hB hAn hyB hc (hBound k (hk.trans hν) y hy) (hvk k hk)
  have hbU : ∀ k ≤ ν, |iteratedFDeriv ℝ k (fun z => 2 * (∑ i, c i * ω z i) +
      ∑ i, c i * (ω' z i - ω z i)) y (fun _ => v)| ≤ 2 * M + θ := by
    intro k hk
    have h1 := hcd _ k hV
    have h2 := hcd _ k hW
    have e2 : iteratedFDeriv ℝ k (fun z => 2 * (∑ i, c i * ω z i) +
        ∑ i, c i * (ω' z i - ω z i)) y =
        (2 : ℝ) • iteratedFDeriv ℝ k (fun z => ∑ i, c i * ω z i) y +
          iteratedFDeriv ℝ k (fun z => ∑ i, c i * (ω' z i - ω z i)) y := by
      have a := iteratedFDeriv_add_apply (h1.const_smul (2 : ℝ)) h2
      have b := iteratedFDeriv_const_smul_apply' (a := (2 : ℝ)) h1
      exact a.trans (by rw [b])
    rw [e2]
    simp only [add_apply, smul_apply,
      smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_two]; linarith [hbV k hk, hbW k hk]
  calc _ ≤ ∑ k ∈ Finset.range (ν + 1), (ν.choose k : ℝ) * (θ * (2 * M + θ)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        have hk' : k ≤ ν := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        rw [abs_mul, abs_mul, Nat.abs_cast, mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hbW k hk') (hbU (ν - k) (Nat.sub_le _ _)) (abs_nonneg _) hθ)
          (Nat.cast_nonneg _)
    _ = 2 ^ ν * θ * (2 * M + θ) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast; ring

theorem stability (hm : 0 < m) {B K : Set (Vec d)} (hB : IsOpen B)
    (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B)
    {ω ω' : Vec d → Vec m} (hAn : AnalyticOnNhd ℝ ω B) (hAn' : AnalyticOnNhd ℝ ω' B)
    (μ : ℕ) {M θ : ℝ} (hM : 0 ≤ M) (hθ : 0 ≤ θ)
    (hBound : ∀ ν ≤ μ, ∀ y ∈ K, jetNorm ω ν y ≤ M)
    (hDiff : ∀ ν ≤ μ, ∀ y ∈ K, jetNorm (fun z => ω' z - ω z) ν y ≤ θ) :
    (∀ c ∈ sphere m, ∀ y ∈ K, ∀ ν ≤ μ,
      |scalarJet (squaredForm ω' c) ν y - scalarJet (squaredForm ω c) ν y| ≤
        2^ν*θ*(2*M+θ)) ∧
    betaMu ω K μ - 2^μ*θ*(2*M+θ) ≤ betaMu ω' K μ ∧
    (0 < betaMu ω K μ → 2^μ*θ*(2*M+θ) ≤ betaMu ω K μ/2 →
      betaMu ω K μ/2 ≤ betaMu ω' K μ ∧ 0 < betaMu ω' K μ) := by
  have _ := And.intro hK hM
  have hE : ∀ ν : ℕ, 0 ≤ 2 ^ ν * θ * (2 * M + θ) := fun ν => by positivity
  have hcd : ∀ (f : Vec d → ℝ) (k : ℕ) (y : Vec d), y ∈ B → AnalyticOnNhd ℝ f B →
      ContDiffAt ℝ k f y := fun f k y hy hf =>
    ((hf.contDiffOn hB.uniqueDiffOn) y hy).contDiffAt (hB.mem_nhds hy) |>.of_le le_top
  have hsq : ∀ (F : Vec d → Vec m), AnalyticOnNhd ℝ F B → ∀ c : Vec m,
      AnalyticOnNhd ℝ (squaredForm F c) B := fun F hF c y hy => by
    exact (analyticOnNhd_coordForm hF c y hy).pow 2
  have part1 : ∀ c ∈ sphere m, ∀ y ∈ K, ∀ ν ≤ μ,
      |scalarJet (squaredForm ω' c) ν y - scalarJet (squaredForm ω c) ν y| ≤
        2^ν*θ*(2*M+θ) := fun c hc y hy ν hν =>
    abs_scalarJet_sub_le ν (hcd _ ν y (hKB hy) (hsq ω hAn c))
      (hcd _ ν y (hKB hy) (hsq ω' hAn' c)) (hE ν)
      fun v hv => stability_pointwise hm hB hKB hAn hAn' μ hM hθ hBound hDiff hc hy hν hv
  have step : ∀ c ∈ sphere m, ∀ y ∈ K,
      jetMax (squaredForm ω c) μ y ≤ jetMax (squaredForm ω' c) μ y + 2 ^ μ * θ * (2 * M + θ) := by
    intro c hc y hy
    refine Real.sSup_le ?_ (add_nonneg (jetMax_nonneg _ _ _) (hE μ))
    rintro r ⟨ν, hν, rfl⟩
    have h1 := part1 c hc y hy ν hν
    have h2 := scalarJet_le_jetMax (squaredForm ω' c) hν y
    have h3 : 2 ^ ν * θ * (2 * M + θ) ≤ 2 ^ μ * θ * (2 * M + θ) := by
      have : (2 : ℝ) ^ ν ≤ 2 ^ μ := pow_le_pow_right₀ (by norm_num) hν
      have h4 : 0 ≤ θ * (2 * M + θ) := by positivity
      nlinarith
    have := (abs_sub_le_iff.1 h1).2
    linarith
  have part2 : betaMu ω K μ - 2 ^ μ * θ * (2 * M + θ) ≤ betaMu ω' K μ := by
    refine le_csInf (((sphere_nonempty hm).prod hKn).image _) ?_
    rintro r ⟨z, hz, rfl⟩
    have : betaMu ω K μ ≤ jetMax (squaredForm ω z.1) μ z.2 := betaFamily_le hz.1 hz.2
    linarith [step z.1 hz.1 z.2 hz.2]
  refine ⟨part1, part2, fun hpos hsmall => ?_⟩
  exact ⟨by linarith, by linarith⟩

/-! ### Scaling -/

lemma analyticOnNhd_squaredForm {B : Set (Vec d)} {F : Vec d → Vec m}
    (hF : AnalyticOnNhd ℝ F B) (c : Vec m) : AnalyticOnNhd ℝ (squaredForm F c) B :=
  fun y hy => (analyticOnNhd_coordForm hF c y hy).pow 2

lemma jetOp_smul {ν : ℕ} (a : ℝ) (ha : 0 ≤ a) (T : (Fin d → ℝ) [×ν]→L[ℝ] ℝ) :
    jetOp (a • T) = a * jetOp T := by
  have h : {r | ∃ v : Vec d, length2 v = 1 ∧ r = |(a • T) (fun _ => v)|} =
      a • {r | ∃ v : Vec d, length2 v = 1 ∧ r = |T (fun _ => v)|} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨|T (fun _ => v)|, ⟨v, hv, rfl⟩, by simp [abs_mul, abs_of_nonneg ha]⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, by simp [abs_mul, abs_of_nonneg ha]⟩
  unfold jetOp
  rw [h, Real.sSup_smul_of_nonneg ha, smul_eq_mul]

lemma scalarJet_const_mul {g : Vec d → ℝ} {y : Vec d} (ν : ℕ) (hg : ContDiffAt ℝ ν g y)
    {a : ℝ} (ha : 0 ≤ a) : scalarJet (fun z => a * g z) ν y = a * scalarJet g ν y := by
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · simp [scalarJet, abs_mul, abs_of_nonneg ha]
  · have h := iteratedFDeriv_const_smul_apply' (a := a) hg
    simp only [smul_eq_mul] at h
    have e1 : ∀ T : (Fin d → ℝ) [×ν]→L[ℝ] ℝ,
        sSup {r | ∃ v : Vec d, length2 v = 1 ∧ r = |T (fun _ => v)|} = jetOp T := fun _ => rfl
    simp only [scalarJet, hν.ne', ite_false, e1, h]
    exact jetOp_smul a ha _

lemma jetMax_const_mul {g : Vec d → ℝ} {y : Vec d} (hg : ∀ ν : ℕ, ContDiffAt ℝ ν g y)
    {a : ℝ} (ha : 0 ≤ a) (μ : ℕ) :
    jetMax (fun z => a * g z) μ y = a * jetMax g μ y := by
  induction μ with
  | zero => simp only [jetMax_zero, scalarJet_const_mul 0 (hg 0) ha]
  | succ μ ih =>
    simp only [jetMax_succ, ih, scalarJet_const_mul (μ + 1) (hg _) ha]
    exact (mul_max_of_nonneg _ _ ha).symm

lemma length2_weighted_bounds (hm : 0 < m) {w c : Vec m} {a b : ℝ} (ha : 0 ≤ a)
    (hw : ∀ i, a ≤ w i ∧ w i ≤ b) (hc : length2 c = 1) :
    a ≤ length2 (fun i => w i * c i) ∧ length2 (fun i => w i * c i) ≤ b := by
  have hs : ∑ i, c i ^ 2 = 1 := Real.sqrt_eq_one.1 hc
  have hb : 0 ≤ b := ha.trans ((hw ⟨0, hm⟩).1.trans (hw ⟨0, hm⟩).2)
  unfold length2
  constructor
  · refine Real.le_sqrt_of_sq_le ?_
    calc a ^ 2 = ∑ i, a ^ 2 * c i ^ 2 := by rw [← Finset.mul_sum, hs, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun i _ => by
        have : a ^ 2 ≤ w i ^ 2 := pow_le_pow_left₀ ha (hw i).1 2
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  · refine Real.sqrt_le_iff.2 ⟨hb, ?_⟩
    calc _ ≤ ∑ i, b ^ 2 * c i ^ 2 := Finset.sum_le_sum fun i _ => by
          have : w i ^ 2 ≤ b ^ 2 :=
            pow_le_pow_left₀ (ha.trans (hw i).1) (hw i).2 2
          rw [mul_pow]; exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = b ^ 2 := by rw [← Finset.mul_sum, hs, mul_one]

lemma sq_scale (ω : Vec d → Vec m) (s c c' : Vec m) (r : ℝ) (h : (fun i => s i * c i) = r • c') :
    squaredForm (fun y i => s i * ω y i) c = fun z => r ^ 2 * squaredForm ω c' z := by
  funext z
  have h1 : ∀ i, s i * c i = r * c' i := fun i => by simpa using congrFun h i
  have : ∑ i, c i * (s i * ω z i) = r * ∑ i, c' i * ω z i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← mul_assoc, mul_comm (c i), h1 i]; ring
  simp only [squaredForm, this]
  ring

theorem scaling_amount {B K : Set (Vec d)} (hB : IsOpen B)
    (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B) (hm : 0 < m)
    {ω : Vec d → Vec m} (hAn : AnalyticOnNhd ℝ ω B) {s : Vec m} {lo hi : ℝ}
    (hlo : 0 < lo) (hs : ∀ i, lo ≤ s i ∧ s i ≤ hi) (μ : ℕ) :
    lo^2*betaMu ω K μ ≤ betaMu (fun y i => s i*ω y i) K μ ∧
    betaMu (fun y i => s i*ω y i) K μ ≤ hi^2*betaMu ω K μ := by
  have _ := hK
  have hsp : ∀ i, 0 < s i := fun i => hlo.trans_le (hs i).1
  have hhi : 0 < hi := (hsp ⟨0, hm⟩).trans_le (hs _).2
  have hcd : ∀ (c : Vec m) (y : Vec d), y ∈ K → ∀ ν : ℕ, ContDiffAt ℝ ν (squaredForm ω c) y :=
    fun c y hy ν => (((analyticOnNhd_squaredForm hAn c).contDiffOn hB.uniqueDiffOn) y (hKB hy)
      |>.contDiffAt (hB.mem_nhds (hKB hy))).of_le le_top
  have hSn : (sphere m ×ˢ K).Nonempty := (sphere_nonempty hm).prod hKn
  have hβ0 : 0 ≤ betaMu ω K μ := betaFamily_nonneg _ _ _ _
  have hjm : ∀ (c : Vec m) (y : Vec d), y ∈ K → ∀ r : ℝ, 0 ≤ r →
      jetMax (fun z => r ^ 2 * squaredForm ω c z) μ y =
      r ^ 2 * jetMax (squaredForm ω c) μ y := fun c y hy r _ =>
    jetMax_const_mul (hcd c y hy) (sq_nonneg r) μ
  constructor
  · refine le_csInf (hSn.image _) ?_
    rintro r ⟨⟨c, y⟩, ⟨hc, hy⟩, rfl⟩
    have hc1 : length2 c = 1 := hc
    obtain ⟨hl, hu⟩ := length2_weighted_bounds hm hlo.le hs hc1
    set t := length2 (fun i => s i * c i) with ht
    have ht0 : 0 < t := hlo.trans_le hl
    have hc'' : length2 (t⁻¹ • fun i => s i * c i) = 1 := by
      rw [length2_smul, abs_of_pos (inv_pos.2 ht0), inv_mul_cancel₀ ht0.ne']
    have e := sq_scale ω s c (t⁻¹ • fun i => s i * c i) t (by
      funext i; simp only [Pi.smul_apply, smul_eq_mul]; field_simp)
    simp only
    rw [e, hjm _ y hy t ht0.le]
    have h1 := betaFamily_le (g := squaredForm ω) (μ := μ) (c := t⁻¹ • fun i => s i * c i)
      (C0 := sphere m) hc'' hy
    have h2 : lo ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hlo.le hl 2
    change lo ^ 2 * betaMu ω K μ ≤ t ^ 2 * _
    calc lo ^ 2 * betaMu ω K μ ≤ t ^ 2 * betaMu ω K μ := mul_le_mul_of_nonneg_right h2 hβ0
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (sq_nonneg t)
  · have hsi : ∀ i, hi⁻¹ ≤ (s i)⁻¹ ∧ (s i)⁻¹ ≤ lo⁻¹ := fun i =>
      ⟨inv_anti₀ (hsp i) (hs i).2, inv_anti₀ hlo (hs i).1⟩
    have key : betaMu (fun y i => s i*ω y i) K μ / hi ^ 2 ≤ betaMu ω K μ := by
      refine le_csInf (hSn.image _) ?_
      rintro r ⟨⟨c, y⟩, ⟨hc, hy⟩, rfl⟩
      have hc1 : length2 c = 1 := hc
      obtain ⟨hl, hu⟩ := length2_weighted_bounds hm (inv_nonneg.2 hhi.le) hsi hc1
      set τ := length2 (fun i => (s i)⁻¹ * c i) with hτ
      have hτ0 : 0 < τ := (inv_pos.2 hhi).trans_le hl
      have hc0 : length2 (τ⁻¹ • fun i => (s i)⁻¹ * c i) = 1 := by
        rw [length2_smul, abs_of_pos (inv_pos.2 hτ0), inv_mul_cancel₀ hτ0.ne']
      have e := sq_scale ω s (τ⁻¹ • fun i => (s i)⁻¹ * c i) c τ⁻¹ (by
        funext i; simp only [Pi.smul_apply, smul_eq_mul]
        have := (hsp i).ne'
        field_simp)
      have h1 := betaFamily_le (g := squaredForm (fun y i => s i * ω y i)) (μ := μ)
        (c := τ⁻¹ • fun i => (s i)⁻¹ * c i) (C0 := sphere m) hc0 hy
      have h1' : betaMu (fun y i => s i*ω y i) K μ ≤ _ := h1
      rw [e, hjm _ y hy _ (inv_nonneg.2 hτ0.le)] at h1'
      have h3 : hi⁻¹ ≤ τ := hl
      have h4 : (τ⁻¹) ^ 2 ≤ hi ^ 2 := by
        have : τ⁻¹ ≤ hi := by
          have := inv_anti₀ (inv_pos.2 hhi) h3
          simpa using this
        exact pow_le_pow_left₀ (inv_nonneg.2 hτ0.le) this 2
      have hj0 := jetMax_nonneg (squaredForm ω c) μ y
      change _ / hi ^ 2 ≤ _
      rw [div_le_iff₀ (by positivity)]
      calc _ ≤ _ := h1'
        _ ≤ hi ^ 2 * jetMax (squaredForm ω c) μ y := mul_le_mul_of_nonneg_right h4 hj0
        _ = _ := mul_comm _ _
    rw [div_le_iff₀ (by positivity)] at key
    linarith

end Nondegeneracy
end KAM.Planetary
