/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.AnalyticZeros
public import KAM.Planetary.Nondegeneracy.GoodAxes
public import KAM.Planetary.Nondegeneracy.SymmetricRelation

/-!
# The frequency map and real nondegeneracy

Blueprint P, Part 10 (`bpP:p10:conv#data`, `bpP:p10:sec-rnd#data`, `bpP:p10:rnd`,
`bpP:p10:scaling`): the action/axis change of variables is an analytic bijection between `axes n`
and `actionDomain D` (`action_diffeomorphism`); the frequency map `frequency` consists of the
Kepler frequencies and twice the sorted secular spectrum; and on every open connected set of
simple axes it is really nondegenerate (`rnd`), by the non-vanishing of the symmetric relation
product `fc_def` (`f_nonzero`) together with the measure-zero theorem `analytic_zero_null`.
`scaling` shows that real nondegeneracy is stable under positive rescaling and permutation of the
components.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

/-! ### The action-axis change of variables -/

lemma analyticAt_action (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    AnalyticAt ℝ (action D) a := by
  refine analyticAt_pi_iff.2 fun i => ?_
  have h0 : 0 < D.G * D.m0 * a i := mul_pos (mul_pos D.hG D.hm0) (ha.1 i)
  have hin : AnalyticAt ℝ (fun b : Vec n => D.G * D.m0 * b i) a :=
    analyticAt_const.mul (analyticAt_pi_iff.1 analyticAt_id i)
  exact analyticAt_const.mul (hin.contDiffAt.sqrt h0.ne').analyticAt

lemma analyticAt_axis (D : Data n) (I : Vec n) : AnalyticAt ℝ (axis D) I := by
  refine analyticAt_pi_iff.2 fun i => ?_
  exact ((analyticAt_pi_iff.1 analyticAt_id i).pow 2).div analyticAt_const
    (mul_pos (pow_pos (D.hm i) 2) (mul_pos D.hG D.hm0)).ne'

lemma axis_action (D : Data n) (a : Vec n) (ha : a ∈ axes n) : axis D (action D a) = a := by
  funext i
  have h0 : 0 ≤ D.G * D.m0 * a i := (mul_pos (mul_pos D.hG D.hm0) (ha.1 i)).le
  have hm := D.hm i
  have hG := D.hG
  have hm0 := D.hm0
  simp only [axis, action, mul_pow, Real.sq_sqrt h0]
  field_simp

lemma action_axis (D : Data n) (I : Vec n) (hI : ∀ i, 0 < I i) : action D (axis D I) = I := by
  funext i
  have hm := D.hm i
  have hG := D.hG
  have hm0 := D.hm0
  have : D.G * D.m0 * (I i ^ 2 / (D.m i ^ 2 * (D.G * D.m0))) = (I i / D.m i) ^ 2 := by
    field_simp
  simp only [action, axis, this, Real.sqrt_sq (div_pos (hI i) hm).le]
  field_simp

lemma actionDomain_eq (D : Data n) :
    actionDomain D = {I | (∀ i, 0 < I i) ∧ axis D I ∈ axes n} := by
  ext I
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun i => mul_pos (D.hm i)
      (Real.sqrt_pos.2 (mul_pos (mul_pos D.hG D.hm0) (ha.1 i))), by rwa [axis_action D a ha]⟩
  · rintro ⟨hI, hax⟩
    exact ⟨axis D I, hax, action_axis D I hI⟩

theorem action_diffeomorphism {n : ℕ} (D : Data n) :
    IsOpen (axes n) ∧ Convex ℝ (axes n) ∧ IsConnected (axes n) ∧
    IsOpen (actionDomain D) ∧
    AnalyticOnNhd ℝ (action D) (axes n) ∧ AnalyticOnNhd ℝ (axis D) (actionDomain D) ∧
    (∀ a ∈ axes n, axis D (action D a) = a) ∧
    (∀ I ∈ actionDomain D, action D (axis D I) = I) := by
  refine ⟨isOpen_axes n, convex_axes n, isConnected_axes n, ?_, fun a ha => analyticAt_action D ha,
    fun I _ => analyticAt_axis D I, axis_action D, ?_⟩
  · rw [actionDomain_eq]
    have hc : Continuous (axis D) :=
      continuous_pi fun i => ((continuous_apply i).pow 2).div_const _
    have : {I : Vec n | (∀ i, 0 < I i) ∧ axis D I ∈ axes n} =
        (⋂ i, {I : Vec n | 0 < I i}) ∩ axis D ⁻¹' axes n := by ext; simp
    rw [this]
    exact (isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_apply i)).inter ((isOpen_axes n).preimage hc)
  · intro I hI
    rw [actionDomain_eq] at hI
    exact action_axis D I hI.1

/-! ### Real nondegeneracy of the frequency map -/

def frequency (D : Data n) (I : Vec n) : Vec (n+n) :=
  Fin.append (nu D I) (fun j => 2*sigma D (axis D I) j)
def frequencyAxes (D : Data n) (a : Vec n) : Vec (n+n) := frequency D (action D a)

lemma analyticAt_frequency (D : Data n) {a : Vec n} (ha : a ∈ simpleAxes D) :
    AnalyticAt ℝ (frequency D) (action D a) := by
  refine analyticAt_pi_iff.2 fun k => ?_
  induction k using Fin.addCases with
  | left i =>
    simp only [frequency, Fin.append_left]
    have hI : 0 < action D a i :=
      mul_pos (D.hm i) (Real.sqrt_pos.2 (mul_pos (mul_pos D.hG D.hm0) (ha.1.1 i)))
    exact analyticAt_const.div ((analyticAt_pi_iff.1 analyticAt_id i).pow 3) (pow_pos hI 3).ne'
  | right j =>
    simp only [frequency, Fin.append_right]
    have h1 : AnalyticAt ℝ (sigma D) (axis D (action D a)) := by
      rw [axis_action D a ha.1]; exact sorted_analytic D a ha
    exact analyticAt_const.mul
      (analyticAt_pi_iff.1 (h1.comp (analyticAt_axis D (action D a))) j)

lemma analyticAt_frequencyAxes (D : Data n) {a : Vec n} (ha : a ∈ simpleAxes D) :
    AnalyticAt ℝ (frequencyAxes D) a :=
  (analyticAt_frequency D ha).comp (analyticAt_action D ha.1)

/-- A nonvanishing relation form on every open nonempty set of axes. -/
lemma exists_relation_ne (D : Data n) (hn : 2 ≤ n) {B : Set (Vec n)} (hB : IsOpen B)
    (hBne : B.Nonempty) (hBA : B ⊆ axes n) {c : Vec n × Vec n} (hc : c ≠ 0) :
    ∃ a ∈ B, ∑ i, c.1 i * nu D (action D a) i + ∑ j, c.2 j * sigma D a j ≠ 0 := by
  obtain ⟨a0, ha0, h0⟩ := f_nonzero D hn hc
  have hnull := analytic_zero_null (isOpen_axes n) (isConnected_axes n) (fc_analytic D c)
    ⟨a0, ha0, h0⟩
  by_contra hcon
  push Not at hcon
  have hsub : B ⊆ {x ∈ axes n | fc_def D c x = 0} := by
    intro a ha
    refine ⟨hBA ha, ?_⟩
    simp only [fc_def]
    exact Finset.prod_eq_zero (Finset.mem_univ (1 : Equiv.Perm (Fin n)))
      (by simpa [relation] using hcon a ha)
  exact (hB.measure_pos volume hBne).ne' (measure_mono_null hsub hnull)

lemma sum_append (c : Vec (n+n)) (x y : Vec n) :
    ∑ k, c k * (Fin.append x y : Vec (n+n)) k =
      ∑ i, c (Fin.castAdd n i) * x i + ∑ j, c (Fin.natAdd n j) * y j := by
  rw [Fin.sum_univ_add]
  simp [Fin.append_left]

lemma exists_freq_ne (D : Data n) (hn : 2 ≤ n) {B : Set (Vec n)} (hB : IsOpen B)
    (hBne : B.Nonempty) (hBA : B ⊆ axes n) {c : Vec (n+n)} (hc : c ≠ 0) :
    ∃ a ∈ B, ∑ k, c k * (Fin.append (nu D (action D a))
      (fun j => 2 * sigma D a j) : Vec (n+n)) k ≠ 0 := by
  obtain ⟨a, haB, ha⟩ := exists_relation_ne D hn hB hBne hBA
    (c := (fun i => c (Fin.castAdd n i), fun j => 2 * c (Fin.natAdd n j))) (by
      intro h
      apply hc
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      funext k
      induction k using Fin.addCases with
      | left i => exact congrFun h1 i
      | right j =>
        have := congrFun h2 j
        simp only [Prod.snd_zero, Pi.zero_apply] at this
        simpa using this)
  refine ⟨a, haB, ?_⟩
  rw [sum_append]
  convert ha using 2
  refine Finset.sum_congr rfl fun j _ => by ring

theorem rnd (D : Data n) (hn : 2 ≤ n) {B : Set (Vec n)}
    (hB : IsOpen B) (hBc : IsConnected B) (hBS : B ⊆ simpleAxes D) :
    AnalyticOnNhd ℝ (frequencyAxes D) B ∧ rnd_def B (frequencyAxes D) ∧
    AnalyticOnNhd ℝ (frequency D) (action D '' B) ∧ rnd_def (action D '' B) (frequency D) ∧
    rnd_def (action D '' B) (nu D) ∧
    rnd_def B (fun a j => 2*sigma D a j) := by
  have hBA : B ⊆ axes n := fun a ha => (hBS ha).1
  have hfa : ∀ a ∈ B, frequencyAxes D a = Fin.append (nu D (action D a))
      (fun j => 2 * sigma D a j) := fun a ha => by
    simp only [frequencyAxes, frequency, axis_action D a (hBA ha)]
  have hfreq : rnd_def B (frequencyAxes D) := fun c hc => by
    obtain ⟨a, ha, h⟩ := exists_freq_ne D hn hB hBc.nonempty hBA hc
    exact ⟨a, ha, by rwa [hfa a ha]⟩
  refine ⟨fun a ha => analyticAt_frequencyAxes D (hBS ha), hfreq, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact analyticAt_frequency D (hBS ha)
  · intro c hc
    obtain ⟨a, ha, h⟩ := hfreq c hc
    exact ⟨action D a, ⟨a, ha, rfl⟩, h⟩
  · intro c hc
    obtain ⟨a, ha, h⟩ := exists_freq_ne D hn hB hBc.nonempty hBA
      (c := Fin.append c 0) (by
        intro h
        apply hc
        funext i
        simpa using congrFun h (Fin.castAdd n i))
    refine ⟨action D a, ⟨a, ha, rfl⟩, ?_⟩
    rw [sum_append] at h
    simpa using h
  · intro c hc
    obtain ⟨a, ha, h⟩ := exists_freq_ne D hn hB hBc.nonempty hBA
      (c := Fin.append 0 c) (by
        intro h
        apply hc
        funext i
        simpa using congrFun h (Fin.natAdd n i))
    refine ⟨a, ha, ?_⟩
    rw [sum_append] at h
    simpa using h

theorem scaling {B : Set (Vec d)} {ω : Vec d → Vec m} (hω : rnd_def B ω)
    {s : Vec m} (hs : ∀ i, 0 < s i) (p : Equiv.Perm (Fin m)) :
    rnd_def B (fun y i => s i * ω y (p i)) := by
  intro c hc
  obtain ⟨y, hy, h⟩ := hω (fun j => c (p.symm j) * s (p.symm j)) (by
    intro h
    apply hc
    funext i
    have := congrFun h (p i)
    simp only [Equiv.symm_apply_apply, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_right (hs i).ne')
  refine ⟨y, hy, ?_⟩
  rw [← Equiv.sum_comp p] at h
  convert h using 2 with i
  simp only [Equiv.symm_apply_apply]
  ring

end Nondegeneracy
end KAM.Planetary
end
