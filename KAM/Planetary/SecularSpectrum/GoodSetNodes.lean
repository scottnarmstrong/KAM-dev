/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.Interface

/-!
# Secular spectrum: the literal good-set nodes

Blueprint P, Part 9 (`bpP:p9:good-set`, `stepP:p9:gs-c`, `bpP:p9:dict`).  Unsigned literal exports
built from the landed `good_set`, `good_set_dichotomy`, `local_analytic`, `diagonalize` and
`min_mode_continuous_positive`: the zero set of `good ∘ σ` on an open connected set of axes is
relatively closed, nowhere dense and null once one point is good; the non-resonance bound is
uniform on compact subsets of `goodAxes`; `2σⱼ ≠ 0`; the hypotheses of `diagonalize` hold on an
action ball around a good point; the bundle (a)–(c) of the proposition; the dictionary clauses.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm Nondegeneracy
variable {n : ℕ}

/-- `stepP:p9:gs-c` (first half): if `good ∘ σ` is not identically zero on an open connected set
`B` of axes, its zero set is relatively closed in `B`, nowhere dense in `B` and Lebesgue null. -/
theorem good_zero_set_small (D : Data n) {B : Set (Vec n)} (hB : IsOpen B)
    (hBc : IsConnected B) (hBA : B ⊆ axes n) (hne : ∃ a ∈ B, good (sigma D a) ≠ 0) :
    (∃ C : Set (Vec n), IsClosed C ∧ {a ∈ B | good (sigma D a) = 0} = B ∩ C) ∧
    B ∩ interior (closure {a ∈ B | good (sigma D a) = 0}) = ∅ ∧
    volume {a ∈ B | good (sigma D a) = 0} = 0 := by
  have hf : AnalyticOnNhd ℝ (fun a => good (sigma D a)) B := (good_set D).1.mono hBA
  have hcont : ContinuousOn (fun a => good (sigma D a)) B := hf.continuousOn
  obtain ⟨hopen, hdense, hnull⟩ : IsOpen {a ∈ B | good (sigma D a) ≠ 0} ∧
      B ⊆ closure {a ∈ B | good (sigma D a) ≠ 0} ∧ volume {a ∈ B | good (sigma D a) = 0} = 0 := by
    rcases good_set_dichotomy D hB hBc hBA with h | h
    · obtain ⟨a, ha, h0⟩ := hne
      exact absurd (h a ha) h0
    · exact h
  refine ⟨?_, ?_, hnull⟩
  · obtain ⟨C, hC, hCe⟩ := (continuousOn_iff_isClosed.1 hcont) {0} isClosed_singleton
    refine ⟨C, hC, ?_⟩
    ext a
    have := congrArg (a ∈ ·) hCe
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, eq_iff_iff] at this
    simp only [mem_ofPred_eq, mem_inter_iff]
    tauto
  · refine eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨hxB, hxi⟩ := hx
    have hV : IsOpen (B ∩ interior (closure {a ∈ B | good (sigma D a) = 0})) :=
      hB.inter isOpen_interior
    obtain ⟨g, hgG, hgV⟩ : ∃ g ∈ {a ∈ B | good (sigma D a) ≠ 0},
        g ∈ B ∩ interior (closure {a ∈ B | good (sigma D a) = 0}) := by
      have := (mem_closure_iff.1 (hdense hxB)) _ hV ⟨hxB, hxi⟩
      obtain ⟨g, hgV, hgG⟩ := this
      exact ⟨g, hgG, hgV⟩
    have hcl := interior_subset hgV.2
    obtain ⟨z, hzG, hzZ⟩ := (mem_closure_iff.1 hcl) _ hopen hgG
    exact hzG.2 hzZ.2

/-- `stepP:p9:gs-c` (second half), `bpP:p9:good-set` (c): uniform non-resonance on compact subsets
of `goodAxes D`: some `α > 0` bounds `|k·Ω|` from below for every `k ∈ k4 n`, `Ω = 2σ`. -/
theorem good_uniform_nonresonance (D : Data n) (hn : 2 ≤ n) {K : Set (Vec n)}
    (hK : IsCompact K) (hKG : K ⊆ goodAxes D) :
    ∃ α : ℝ, 0 < α ∧ ∀ a ∈ K, ∀ k ∈ k4 n, α ≤ |∑ j, (k j : ℝ) * (2 * sigma D a j)| := by
  obtain ⟨hne, hcont, hpos⟩ := min_mode_continuous_positive D hn
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨a0, ha0, hmin⟩ := hK.exists_isMinOn hKne (hcont.mono hKG)
  refine ⟨_, hpos a0 (hKG ha0), fun a ha k hk => ?_⟩
  refine (hmin ha).trans ?_
  exact Finset.inf'_le _ ((Set.Finite.mem_toFinset _).2 hk)

/-- `bpP:p9:good-set` (b): at a good axis point, every `2σⱼ ≠ 0`. -/
theorem two_sigma_ne_zero (D : Data n) (hn : 2 ≤ n) {a : Vec n} (ha : a ∈ goodAxes D) (j : Fin n) :
    2 * sigma D a j ≠ 0 :=
  mul_ne_zero two_ne_zero (sigma_neg D hn ha.1 j).ne

/-- `bpP:p9:good-set` (b): the hypotheses of `diagonalize` hold on the action image of a small
ball around a good axis point (open, inside `actionDomain D`, analytic special orthogonal frame,
diagonalisation with the sorted spectrum, `Ω = 2σ` never zero). -/
theorem good_diagonalize_data (D : Data n) (hn : 2 ≤ n) {a : Vec n} (ha : a ∈ goodAxes D) :
    ∃ r : ℝ, 0 < r ∧ ∃ R : Vec n → Mat n,
      IsOpen (action D '' Metric.ball a r) ∧ action D '' Metric.ball a r ⊆ actionDomain D ∧
      action D a ∈ action D '' Metric.ball a r ∧
      AnalyticOnNhd ℝ R (action D '' Metric.ball a r) ∧
      (∀ I ∈ action D '' Metric.ball a r, isSO (R I)) ∧
      (∀ I ∈ action D '' Metric.ball a r, coeffs D (axis D I) =
        R I * Matrix.diagonal (sigma D (axis D I)) * (R I).transpose) ∧
      (∀ I ∈ action D '' Metric.ball a r, ∀ j, 2 * sigma D (axis D I) j ≠ 0) := by
  have hinj : Function.Injective (sigma D a) :=
    (discriminant_ne_zero_iff _).1
      ((discriminant_ne_zero_iff _).2 ((good_ne_zero_iff _).1 ha.2).1)
  obtain ⟨r, hr, hball, s, R, hs, hR, h⟩ := local_analytic (isOpen_axes n)
    (fun x _ => coeffs_hermitian D x) (coeffs_analytic D) ha.1
    (eigenvalues_injective_of_sorted _ hinj)
  have hax : ∀ I ∈ action D '' Metric.ball a r, axis D I ∈ Metric.ball a r ∧ axis D I ∈ axes n := by
    rintro I ⟨b, hb, rfl⟩
    rw [axis_action D b (hball hb)]
    exact ⟨hb, hball hb⟩
  have hsig : ∀ x ∈ Metric.ball a r, s x = sigma D x := fun x hx => by
    obtain ⟨hSO, hmono, hM⟩ := h x hx
    exact (sorted_eq_of_frame (coeffs_hermitian D x) hSO.1 hmono hM).symm
  refine ⟨r, hr, fun I => R (axis D I), image_action_open D Metric.isOpen_ball hball,
    ?_, ⟨a, Metric.mem_ball_self hr, rfl⟩, ?_, fun I hI => (h _ (hax I hI).1).1,
    fun I hI => ?_, fun I hI j => ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, hball hb, rfl⟩
  · intro I hI
    exact (hR _ (hax I hI).1).comp_of_eq (analyticAt_axis D I) rfl
  · have := (h _ (hax I hI).1).2.2
    rwa [hsig _ (hax I hI).1] at this
  · exact mul_ne_zero two_ne_zero (sigma_neg D hn (hax I hI).2 j).ne

/-- `bpP:p9:good-set` (a)–(c) as one bundle, from the source hypotheses only (`2 ≤ n`, the secular
data `D`; in (c) `B` open and connected in the axes): (a) `good` is a symmetric polynomial in `σ`,
a polynomial in the characteristic coefficients, analytic on `axes n`, label independent;
(b) `Φ₄ ≠ 0 ↔ NR₄`, and at such a point the spectrum is simple, every `2σⱼ ≠ 0` and
`diagonalize` applies on an action ball; (c) the dichotomy, with the good set of the nonzero branch
uniformly non-resonant on compacts. -/
theorem good_set_bundle (D : Data n) (hn : 2 ≤ n) :
    ((goodPoly n).IsSymmetric ∧
      (∃ P : MvPolynomial (Fin n) ℝ, ∀ M : Mat n, ∀ hM : M.IsHermitian,
        good (sorted M hM) = MvPolynomial.eval (fun i => M.charpoly.coeff i.val) P) ∧
      AnalyticOnNhd ℝ (fun a => good (sigma D a)) (axes n) ∧
      (∀ p : Equiv.Perm (Fin n), ∀ s : Vec n, good (s ∘ p) = good s)) ∧
    (∀ a ∈ axes n, (good (sigma D a) ≠ 0 ↔ nr4 (sigma D a)) ∧
      (good (sigma D a) ≠ 0 → Function.Injective (sigma D a) ∧ (∀ j, 2 * sigma D a j ≠ 0) ∧
        ∃ r : ℝ, 0 < r ∧ ∃ R : Vec n → Mat n,
          IsOpen (action D '' Metric.ball a r) ∧ action D '' Metric.ball a r ⊆ actionDomain D ∧
          action D a ∈ action D '' Metric.ball a r ∧
          AnalyticOnNhd ℝ R (action D '' Metric.ball a r) ∧
          (∀ I ∈ action D '' Metric.ball a r, isSO (R I)) ∧
          (∀ I ∈ action D '' Metric.ball a r, coeffs D (axis D I) =
            R I * Matrix.diagonal (sigma D (axis D I)) * (R I).transpose))) ∧
    (∀ B : Set (Vec n), IsOpen B → IsConnected B → B ⊆ axes n →
      ((∀ a ∈ B, good (sigma D a) = 0) ∨
        (IsOpen {a ∈ B | good (sigma D a) ≠ 0} ∧
          B ⊆ closure {a ∈ B | good (sigma D a) ≠ 0} ∧
          volume {a ∈ B | good (sigma D a) = 0} = 0 ∧
          ∀ K : Set (Vec n), IsCompact K → K ⊆ {a ∈ B | good (sigma D a) ≠ 0} →
            ∃ α : ℝ, 0 < α ∧ ∀ a ∈ K, ∀ k ∈ k4 n,
              α ≤ |∑ j, (k j : ℝ) * (2 * sigma D a j)|))) := by
  refine ⟨⟨goodPoly_isSymmetric n, good_characteristic n, (good_set D).1, (good_set D).2.2⟩,
    fun a ha => ⟨(good_set D).2.1 a ha, fun hg => ⟨?_, ?_, ?_⟩⟩, fun B hB hBc hBA => ?_⟩
  · exact ((good_ne_zero_iff _).1 hg).1
  · exact fun j => mul_ne_zero two_ne_zero (sigma_neg D hn ha j).ne
  · obtain ⟨r, hr, R, h⟩ := good_diagonalize_data D hn (a := a) ⟨ha, hg⟩
    exact ⟨r, hr, R, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  · rcases good_set_dichotomy D hB hBc hBA with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, h2, h3, fun K hK hKB => ?_⟩
      exact good_uniform_nonresonance D hn hK fun a ha => ⟨hBA (hKB ha).1, (hKB ha).2⟩
