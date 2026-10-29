/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.GoodAxes
public import KAM.Planetary.Nondegeneracy.GoodAxes.N2
public import KAM.Planetary.Nondegeneracy.GoodAxes.SortedAnalytic
public import KAM.Planetary.Nondegeneracy.Interface

/-!
# Good axes: literal node statements

Blueprint P, Part 10 (package GAP-P10a): unsigned exports stating the literal conclusions of the
nodes `bpP:p10:conv#data` (supplements), `stepP:p10:n2-t`, `bpP:p10:n2`, `stepP:p10:sa-loc`,
`stepP:p10:sa-n2`, `bpP:p10:sorted-analytic` and `bpP:p10:good-set`, built from the landed
declarations.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n : ℕ}

/-! ### `bpP:p10:sa-loc`, `bpP:p10:sa-n2`, `bpP:p10:sorted-analytic` -/

/-- `stepP:p10:sa-loc`: around each point of `U_n` the local analytic ordered branches agree with
the sorted eigenvalues `σ`. -/
theorem sorted_local_branch (D : Data n) {a : Vec n} (ha : a ∈ simpleAxes D) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ simpleAxes D ∧ ∃ s : Vec n → Vec n, ∃ R : Vec n → Mat n,
      AnalyticOnNhd ℝ s (Metric.ball a r) ∧ AnalyticOnNhd ℝ R (Metric.ball a r) ∧
      ∀ x ∈ Metric.ball a r, isSO (R x) ∧ StrictMono (s x) ∧ s x = sigma D x ∧
        coeffs D x = R x * Matrix.diagonal (s x) * (R x).transpose := by
  have hinj : Function.Injective (sigma D a) := (discriminant_ne_zero_iff _).1 ha.2
  obtain ⟨r, hr, hball, s, R, hs, hR, hfr⟩ := local_analytic (isOpen_axes n)
    (fun x _ => coeffs_hermitian D x) (coeffs_analytic D) ha.1
    (eigenvalues_injective_of_sorted _ hinj)
  have hsig : ∀ x ∈ Metric.ball a r, s x = sigma D x := fun x hx => by
    obtain ⟨hSO, hmono, hM⟩ := hfr x hx
    exact (sorted_eq_of_frame (coeffs_hermitian D x) hSO.1 hmono hM).symm
  refine ⟨r, hr, fun x hx => ⟨hball hx, ?_⟩, s, R, hs, hR, fun x hx => ?_⟩
  · rw [← hsig x hx]
    exact (discriminant_ne_zero_iff _).2 (hfr x hx).2.1.injective
  · obtain ⟨hSO, hmono, hM⟩ := hfr x hx
    exact ⟨hSO, hmono, hsig x hx, hM⟩

/-- `bpP:p10:conv#data`: `U_n` is open. -/
theorem isOpen_simpleAxes (D : Data n) : IsOpen (simpleAxes D) := by
  rw [isOpen_iff_forall_mem_open]
  intro a ha
  obtain ⟨r, hr, hsub, -⟩ := sorted_local_branch D ha
  exact ⟨Metric.ball a r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩

/-- The sorted spectrum is strictly increasing on `U_n`. -/
theorem sorted_strictMono_simple (D : Data n) {a : Vec n} (ha : a ∈ simpleAxes D) :
    StrictMono (sigma D a) :=
  (sorted_mono _ (coeffs_hermitian D a)).strictMono_of_injective
    ((discriminant_ne_zero_iff _).1 ha.2)

/-- `stepP:p10:sa-n2`: for two planets the discriminant is positive on all of `A₂`, so
`U₂ = A₂`. -/
theorem simpleAxes_two_eq_axes (D : Data 2) : simpleAxes D = axes 2 := by
  ext a
  refine ⟨fun h => h.1, fun ha => ⟨ha, ?_⟩⟩
  exact (discriminant_ne_zero_iff _).2 (sigma_two_inj D ha)

/-- `bpP:p10:sorted-analytic`: the sorted `σ₁ < ⋯ < σₙ` are real analytic on `U_n`, and
`U₂ = A₂`. -/
theorem sorted_analytic_node (D : Data n) :
    AnalyticOnNhd ℝ (sigma D) (simpleAxes D) ∧ (∀ a ∈ simpleAxes D, StrictMono (sigma D a)) ∧
      (∀ E : Data 2, simpleAxes E = axes 2) :=
  ⟨sorted_analytic D, fun _ ha => sorted_strictMono_simple D ha, simpleAxes_two_eq_axes⟩

/-! ### `bpP:p10:conv#data` supplements -/

/-- `bpP:p10:conv#data`: `G_n ⊆ U_n`. -/
theorem goodAxes_subset_simpleAxes (D : Data n) : goodAxes D ⊆ simpleAxes D := fun _ ha =>
  ⟨ha.1, (discriminant_ne_zero_iff _).2 ((good_ne_zero_iff _).1 ha.2).1⟩

/-- `bpP:p10:conv#data`: `G_n` is open (`n ≥ 2`). -/
theorem isOpen_goodAxes (D : Data n) (hn : 2 ≤ n) : IsOpen (goodAxes D) :=
  (good_set D hn).1

/-- `bpP:p10:conv#data`: the fast frequencies are `νᵢ(a) = √(G m₀) · aᵢ^(-3/2)` for the frozen
action `Λ(a)`. -/
theorem nu_action_eq (D : Data n) {a : Vec n} (ha : a ∈ axes n) (i : Fin n) :
    nu D (action D a) i = √(D.G * D.m0) * a i ^ (-(3 / 2 : ℝ)) := by
  have hk : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hai : 0 < a i := ha.1 i
  have hs : 0 < √(D.G * D.m0) := Real.sqrt_pos.2 hk
  have hsa : 0 < √(a i) := Real.sqrt_pos.2 hai
  have h1 : √(D.G * D.m0 * a i) = √(D.G * D.m0) * √(a i) := Real.sqrt_mul hk.le _
  have h2 : a i ^ (-(3 / 2 : ℝ)) = (√(a i) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hai.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hai.le]
    norm_num
  have h3 : (D.G * D.m0) ^ 2 = √(D.G * D.m0) ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hk.le]
  have hm := D.hm i
  simp only [nu, action]
  rw [h1, h2, h3]
  field_simp

/-! ### `stepP:p10:n2-t`, `bpP:p10:n2` -/

section N2Nodes
variable (D : Data 2) {a : Vec 2}

/-- `stepP:p10:n2-t`: with `t = σ₁/σ₂` and `r = tr² / det`: `t > 1`, `r = t + 1/t + 2` and
`r - 3 < t`. -/
theorem n2_t_node (ha : a ∈ axes 2) :
    1 < sigma D a 0 / sigma D a 1 ∧
    (coeffs D a).trace ^ 2 / (coeffs D a).det =
      sigma D a 0 / sigma D a 1 + 1 / (sigma D a 0 / sigma D a 1) + 2 ∧
    (coeffs D a).trace ^ 2 / (coeffs D a).det - 3 < sigma D a 0 / sigma D a 1 := by
  have hlt := sigma_two_lt D ha
  have n1 := sigma_two_neg D ha 1
  have n0 := sigma_two_neg D ha 0
  have h1 := sorted_two_sum (coeffs D a) (coeffs_hermitian D a)
  have h2 := sorted_two_prod (coeffs D a) (coeffs_hermitian D a)
  change sigma D a 0 + sigma D a 1 = _ at h1
  change sigma D a 0 * sigma D a 1 = _ at h2
  have ht : 1 < sigma D a 0 / sigma D a 1 := by
    rw [lt_div_iff_of_neg n1]; linarith
  have he : (coeffs D a).trace ^ 2 / (coeffs D a).det =
      sigma D a 0 / sigma D a 1 + 1 / (sigma D a 0 / sigma D a 1) + 2 := by
    rw [← h1, ← h2]
    generalize sigma D a 0 = s at *
    generalize sigma D a 1 = t at *
    have := n0.ne; have := n1.ne
    field_simp
    ring
  refine ⟨ht, he, ?_⟩
  have : 1 / (sigma D a 0 / sigma D a 1) < 1 := by
    rw [div_lt_one (by linarith)]; exact ht
  linarith

/-- The ratio of the two actions is `(m₂/m₁) √(a₂/a₁)`. -/
lemma action_ratio_eq (ha : a ∈ axes 2) :
    action D a 1 / action D a 0 = D.m 1 / D.m 0 * √(a 1 / a 0) := by
  have hk : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have a0 := ha.1 0
  have a1 := ha.1 1
  have m0 := D.hm 0
  have m1 := D.hm 1
  have hs0 : 0 < √(D.G * D.m0 * a 0) := Real.sqrt_pos.2 (mul_pos hk a0)
  have hq : √(a 1 / a 0) = √(D.G * D.m0 * a 1) / √(D.G * D.m0 * a 0) := by
    rw [← Real.sqrt_div (mul_pos hk a1).le, mul_div_mul_left _ _ hk.ne']
  rw [hq]
  simp only [action]
  field_simp

/-- `bpP:p10:n2`: the `Λ`-ratio identity and the exact formula for `r = tr² / det`; `r > 6` (and
non-resonance) in the hierarchical regime; and `r, t → ∞` as `a₁/a₂ → 0`, uniformly in `a`. -/
theorem n2_node (ha : a ∈ axes 2) :
    action D a 1 / action D a 0 = D.m 1 / D.m 0 * √(a 1 / a 0) ∧
    (coeffs D a).trace ^ 2 / (coeffs D a).det =
      (action D a 0 + action D a 1) ^ 2 / (action D a 0 * action D a 1) /
        (1 - (pairB D a 0 1 / pairA D a 0 1) ^ 2) ∧
    (coeffs D a).trace ^ 2 / (coeffs D a).det > action D a 1 / action D a 0 + 2 ∧
    sigma D a 0 / sigma D a 1 ≥ (coeffs D a).trace ^ 2 / (coeffs D a).det - 3 ∧
    (16 * D.m 0 ^ 2 / D.m 1 ^ 2 ≤ a 1 / a 0 →
      6 < (coeffs D a).trace ^ 2 / (coeffs D a).det ∧ nr4 (sigma D a) ∧
        good (sigma D a) ≠ 0) ∧
    ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ axes 2, b 0 / b 1 < ε →
      M < (coeffs D b).trace ^ 2 / (coeffs D b).det ∧ M < sigma D b 0 / sigma D b 1 := by
  refine ⟨action_ratio_eq D ha, ratio_formula D ha, ratio_gt D ha, sigma_ratio_ge D ha,
    fun h => ?_, fun M => ?_⟩
  · have h4 := action_ratio_ge D ha h
    have hr := ratio_gt D ha
    have hn := nr4_of_hier D ha h
    exact ⟨by linarith, hn, (good_ne_zero_iff _).2 hn⟩
  · have m0 := D.hm 0
    have m1 := D.hm 1
    set K : ℝ := (|M| + 3) * D.m 0 / D.m 1 with hK
    have hKp : 0 < K := by positivity
    refine ⟨1 / K ^ 2, by positivity, fun b hb hlt => ?_⟩
    have b0 := hb.1 0
    have b1 := hb.1 1
    have hgt : K ^ 2 < b 1 / b 0 := by
      rw [lt_div_iff₀ b0]
      rw [div_lt_iff₀ b1] at hlt
      have hK2 : 0 < K ^ 2 := by positivity
      have := mul_lt_mul_of_pos_left hlt hK2
      rwa [← mul_assoc, mul_one_div_cancel hK2.ne', one_mul] at this
    have hsq : K < √(b 1 / b 0) := Real.lt_sqrt hKp.le |>.2 hgt
    have hrat : |M| + 3 < action D b 1 / action D b 0 := by
      rw [action_ratio_eq D hb]
      calc |M| + 3 = D.m 1 / D.m 0 * K := by rw [hK]; field_simp
        _ < _ := mul_lt_mul_of_pos_left hsq (by positivity)
    have hr := ratio_gt D hb
    have hge := sigma_ratio_ge D hb
    have := le_abs_self M
    constructor <;> linarith

end N2Nodes

/-! ### `bpP:p10:good-set` -/

/-- `bpP:p10:good-set`: `G_n` is open, dense and of full measure in `A_n`; at every point of `G_n`
the eigenvalues are simple and have local analytic ordered branches; `Ω = 2σ` is `NR₄` uniformly
on compact subsets of `G_n`; and every `a ∈ A_n` has a closed ball `B̄(r, 2a₀)` inside
`G_n ∩ B(a, η)`. -/
theorem good_set_node (D : Data n) (hn : 2 ≤ n) :
    IsOpen (goodAxes D) ∧ axes n ⊆ closure (goodAxes D) ∧
    volume (axes n \ goodAxes D) = 0 ∧
    (∀ a ∈ goodAxes D, discriminant (sigma D a) ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      ∃ s : Vec n → Vec n, ∃ R : Vec n → Mat n,
        AnalyticOnNhd ℝ s (Metric.ball a r) ∧ AnalyticOnNhd ℝ R (Metric.ball a r) ∧
        ∀ x ∈ Metric.ball a r, isSO (R x) ∧ StrictMono (s x) ∧ s x = sigma D x) ∧
    (∀ a ∈ goodAxes D, nr4 (fun j => 2 * sigma D a j)) ∧
    (∀ K : Set (Vec n), K ⊆ goodAxes D → IsCompact K → ∃ c : ℝ, 0 < c ∧
      ∀ a ∈ K, ∀ k ∈ k4 n, c ≤ |∑ j, (k j : ℝ) * (2 * sigma D a j)|) ∧
    ∀ a ∈ axes n, ∀ η : ℝ, 0 < η → ∃ a0 : ℝ, ∃ r : Vec n,
      0 < a0 ∧ Metric.closedBall r (2 * a0) ⊆ goodAxes D ∩ Metric.ball a η := by
  obtain ⟨h1, h2, h3, h4⟩ := good_set D hn
  refine ⟨h1, h2, h3, fun a ha => ?_, fun a ha => ?_, fun K hK hKc => ?_, h4⟩
  · have hs : a ∈ simpleAxes D := goodAxes_subset_simpleAxes D ha
    obtain ⟨r, hr, -, s, R, hs', hR, h⟩ := sorted_local_branch D hs
    exact ⟨hs.2, r, hr, s, R, hs', hR, fun x hx => ⟨(h x hx).1, (h x hx).2.1, (h x hx).2.2.1⟩⟩
  · have hnr := (good_ne_zero_iff _).1 ha.2
    refine ⟨fun i j h => hnr.1 (by simpa using h), fun k hk => ?_⟩
    have := hnr.2 k hk
    have e : ∑ j, (k j : ℝ) * (2 * sigma D a j) = 2 * ∑ j, (k j : ℝ) * sigma D a j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e]
    exact mul_ne_zero two_ne_zero this
  · obtain ⟨hne, hcont, hpos⟩ := min_mode_continuous_positive D hn
    rcases K.eq_empty_or_nonempty with rfl | hK0
    · exact ⟨1, one_pos, fun a ha => absurd ha (Set.notMem_empty a)⟩
    obtain ⟨a0, ha0, hmin⟩ := hKc.exists_isMinOn hK0 (hcont.mono hK)
    refine ⟨_, hpos a0 (hK ha0), fun a ha k hk => ?_⟩
    exact (Finset.inf'_le _ ((k4_finite n).mem_toFinset.2 hk)).trans' (hmin ha)

end Nondegeneracy
end KAM.Planetary
end
