/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Lift.Field

/-!
# Planar quartic torsion: the lifted orbit solves the full Hamilton equations (package T11)

Blueprint P, Part 11b (`bpP:p11b:lm-ham`).  The slow flow of `p11c_flow` is a solution only on the
closed interval `[-1, 1]`, so its endpoint derivatives are not controlled by an open interval.  For
a start point of slow length `< r / 2` the flow `p11cL_ext` therefore re-centres the trajectory at
the time `1/2`: the resulting solution lives on `(-1/2, 3/2)` and agrees with the flow on `[-1/2, 1]`.
On that open interval `p11cL_orbit_solution` shows that the slow solution together with the angle
integral of `∂_I chi` solves the full Hamilton equations of `p11cL_ham chi`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

variable {O : Set (Fin 2 → ℝ)}

/-- The part of the conclusion of the signed theorem `flow` used by the lift. -/
def p11cL_FlowSpec (chi : (Fin 2 → ℝ) → Phase 2 → ℝ) (K : Set (Fin 2 → ℝ)) (r : ℝ) : Prop :=
  ∀ I ∈ K, ∀ z : Phase 2, p11c_slowLength z < r →
    p11c_flow chi I 0 z = z ∧
    IsSolutionIn (hamiltonianVectorField (chi I)) univ (Icc (-1) 1)
      (fun t => p11c_flow chi I t z) ∧
    ∀ t ∈ Icc (-1 : ℝ) 1,
      (p11c_slowLength (p11c_flow chi I t z)) ^ 2 ≤ 2 * (p11c_slowLength z) ^ 2

theorem p11cL_hasDerivAt_append {a b : ℝ → Fin 2 → ℝ} {a' b' : Fin 2 → ℝ} {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => (Fin.append (a s) (b s) : Fin (2 + 2) → ℝ)) (Fin.append a' b') t := by
  rw [hasDerivAt_pi] at ha hb ⊢
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro i
  · simpa [Fin.append_left] using ha i
  · simpa [Fin.append_right] using hb i

theorem p11cL_slow_lt_of_sq {a b : ℝ} (hb : 0 < b) (h : a ^ 2 < b ^ 2) : a < b :=
  (le_abs_self a).trans_lt (abs_lt_of_sq_lt_sq h hb.le)

/-- Re-centred trajectory: a solution on `(-1/2, 3/2)` agreeing with the flow on `[-1/2, 1]`. -/
theorem p11cL_ext (chi : QuarticFamily O) {K : Set (Fin 2 → ℝ)} (hKO : K ⊆ O) {r : ℝ}
    (hfs : p11cL_FlowSpec chi.eval K r) {I : Fin 2 → ℝ} (hI : I ∈ K) {z : Phase 2}
    (hz : p11c_slowLength z < r / 2) :
    ∃ Y : ℝ → Phase 2,
      IsSolutionIn (hamiltonianVectorField (chi.eval I)) univ (Ioo (-1 / 2) (3 / 2)) Y ∧
      ∀ t ∈ Icc (-1 / 2 : ℝ) 1, Y t = p11c_flow chi.eval I t z := by
  have hr : 0 < r := by
    have := Real.sqrt_nonneg (∑ i, ((z.1 i) ^ 2 + (z.2 i) ^ 2))
    unfold p11c_slowLength at hz; linarith
  obtain ⟨h0, hsol, hen⟩ := hfs I hI z (by linarith)
  set z' : Phase 2 := p11c_flow chi.eval I (1 / 2) z with hz'
  have hz'r : p11c_slowLength z' < r := by
    have h1 := hen (1 / 2) ⟨by norm_num, by norm_num⟩
    refine p11cL_slow_lt_of_sq hr ?_
    have h2 : p11c_slowLength z ^ 2 < (r / 2) ^ 2 :=
      pow_lt_pow_left₀ hz (Real.sqrt_nonneg _) two_ne_zero
    nlinarith [sq_nonneg r]
  obtain ⟨h0', hsol', -⟩ := hfs I hI z' hz'r
  have hY : IsSolutionIn (hamiltonianVectorField (chi.eval I)) univ (Icc (-1 / 2) (3 / 2))
      (fun t => p11c_flow chi.eval I (t - 1 / 2) z') := by
    intro t ht
    refine ⟨mem_univ _, ?_⟩
    have := (hsol' (t - 1 / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩).2
    exact this.comp_sub_const t (1 / 2)
  refine ⟨_, hY.mono Ioo_subset_Icc_self, fun t ht => ?_⟩
  have hF1 := p11cQ_field_slice_contDiffOn chi (hKO hI)
  have := gen_uniqueness isOpen_univ hF1 (ordConnected_Icc (a := (-1 / 2 : ℝ)) (b := 1))
    (t₀ := 1 / 2) ⟨by norm_num, by norm_num⟩
    (hY.mono (Icc_subset_Icc le_rfl (by norm_num)))
    (hsol.mono (Icc_subset_Icc (by norm_num) le_rfl))
    (by show p11c_flow chi.eval I (1 / 2 - 1 / 2) z' = _; rw [sub_self, h0'])
  exact this ht

/-- The lifted orbit solves the full Hamilton equations. -/
theorem p11cL_orbit_solution (chi : QuarticFamily O) {I : Fin 2 → ℝ} (hI : I ∈ O)
    {Y : ℝ → Phase 2}
    (hY : IsSolutionIn (hamiltonianVectorField (chi.eval I)) univ (Ioo (-1 / 2) (3 / 2)) Y)
    (lam : Fin 2 → ℝ) :
    IsSolutionIn (hamiltonianVectorField (p11cL_ham chi)) (p11cL_dom O) (Ioo (-1 / 2) (3 / 2))
      (fun t => assemble I (lam + fun i => ∫ s in (0 : ℝ)..t,
        fderiv ℝ (fun J => chi.eval J (Y s)) I (Pi.single i 1)) (Y t).2 (Y t).1) := by
  intro t ht
  refine ⟨?_, ?_⟩
  · show p11cL_act _ ∈ O
    rw [p11cL_act_assemble]; exact hI
  have hF : ∀ i, (fun s => fderiv ℝ (fun J => chi.eval J (Y s)) I (Pi.single i 1)) =
      fun s => p11cL_dI chi (I, Y s) i := fun i =>
    funext fun s => p11cL_partial_eq chi hI (Y s) i
  have hcont : ∀ i, ContinuousOn (fun s => p11cL_dI chi (I, Y s) i) (Ioo (-1 / 2) (3 / 2)) := by
    intro i s hs
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun v => p11cL_dI chi v i) (I, Y s) :=
      (p11cL_dI_analyticAt chi (u := (I, Y s)) hI i).continuousAt
    exact h1.comp (f := fun s => (I, Y s)) (continuousAt_const.prodMk (hY s hs).2.continuousAt)
  have hG : ∀ i, HasDerivAt (fun s => ∫ x in (0 : ℝ)..s,
      fderiv ℝ (fun J => chi.eval J (Y x)) I (Pi.single i 1)) (p11cL_dI chi (I, Y t) i) t := by
    intro i
    rw [hF i]
    have h0 : (0 : ℝ) ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := ⟨by norm_num, by norm_num⟩
    have hsub : uIcc (0 : ℝ) t ⊆ Ioo (-1 / 2) (3 / 2) := ordConnected_Ioo.uIcc_subset h0 ht
    exact intervalIntegral.integral_hasDerivAt_right
      (((hcont i).mono hsub).intervalIntegrable)
      ((hcont i).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      ((hcont i t ht).continuousAt (isOpen_Ioo.mem_nhds ht))
  have hang : HasDerivAt (fun s => lam + fun i => ∫ x in (0 : ℝ)..s,
      fderiv ℝ (fun J => chi.eval J (Y x)) I (Pi.single i 1))
      (fun i => p11cL_dI chi (I, Y t) i) t := by
    rw [hasDerivAt_pi]
    intro i
    have h := (hasDerivAt_const t (lam i)).add (hG i)
    rw [zero_add] at h
    exact h
  have hX := (hY t ht).2
  rw [p11cL_field_assemble chi hI]
  exact (p11cL_hasDerivAt_append hang hX.fst).prodMk
    (p11cL_hasDerivAt_append (hasDerivAt_const t I) hX.snd)

theorem p11cL_norm_le_slow (y : Phase 2) : ‖y‖ ≤ p11c_slowLength y := by
  unfold p11c_slowLength
  exact Real.le_sqrt_of_sq_le (p11cQ_norm_sq_le y)

/-- The part of `Phase (2 + 2)` where the lift is described by short-time iterates. -/
def p11cL_nbhd (O' : Set (Fin 2 → ℝ)) (r : ℝ) : Set (Phase (2 + 2)) :=
  {w | p11cL_act w ∈ O' ∧ p11c_slowLength (p11cL_slow w) < r ∧ ‖p11cL_ang w‖ < 1}

theorem p11cL_nbhd_isOpen {O' : Set (Fin 2 → ℝ)} (hO' : IsOpen O') (r : ℝ) :
    IsOpen (p11cL_nbhd O' r) := by
  have h1 : Continuous p11cL_act := continuous_pi fun i => (continuous_apply _).comp continuous_snd
  have h2 : Continuous p11cL_ang := continuous_pi fun i => (continuous_apply _).comp continuous_fst
  have h3 : Continuous fun w => p11c_slowLength (p11cL_slow w) := by
    unfold p11c_slowLength p11cL_slow
    refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => ?_)
    fun_prop
  exact (hO'.preimage h1).inter ((isOpen_lt h3 continuous_const).inter
    (isOpen_lt h2.norm continuous_const))

/-- A uniform bound for the action derivative of `chi` on `K × {‖y‖ ≤ ρ}`. -/
theorem p11cL_exists_bound (chi : QuarticFamily O) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKO : K ⊆ O) (ρ : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ I ∈ K, ∀ y : Phase 2, ‖y‖ ≤ ρ → ‖fun i => p11cL_dI chi (I, y) i‖ ≤ D := by
  have hKc : IsCompact (K ×ˢ closedBall (0 : Phase 2) ρ) := hK.prod (isCompact_closedBall _ _)
  obtain ⟨D₀, hD₀⟩ := hKc.exists_bound_of_continuousOn
    (f := fun u : (Fin 2 → ℝ) × Phase 2 => (fun i => p11cL_dI chi u i : Fin 2 → ℝ))
    (fun u hu => (continuousAt_pi.2 fun i =>
      (p11cL_dI_analyticAt chi (hKO hu.1) i).continuousAt).continuousWithinAt)
  exact ⟨max D₀ 0, le_max_right _ _, fun I hI y hy =>
    (hD₀ (I, y) ⟨hI, by simpa using hy⟩).trans (le_max_left _ _)⟩

/-- The explicit orbit of the full lift through a point of `p11cL_nbhd`. -/
theorem p11cL_orbit_exists (chi : QuarticFamily O) {K : Set (Fin 2 → ℝ)} (hKO : K ⊆ O) {r : ℝ}
    (hr : 0 < r) (hfs : p11cL_FlowSpec chi.eval K (2 * r)) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ I ∈ K, ∀ y : Phase 2, ‖y‖ ≤ 2 * r → ‖fun i => p11cL_dI chi (I, y) i‖ ≤ D)
    {O' : Set (Fin 2 → ℝ)} (hO'K : O' ⊆ K) {w : Phase (2 + 2)} (hIO' : p11cL_act w ∈ O')
    (hz : p11c_slowLength (p11cL_slow w) < r) :
    ∃ g : ℝ → Phase (2 + 2),
      IsSolutionIn (hamiltonianVectorField (p11cL_ham chi)) (p11cL_dom O) (Ioo (-1 / 2) (3 / 2))
        g ∧ g 0 = w ∧ g 1 = p11c_liftFlow chi.eval w ∧
      ∀ t ∈ Icc (0 : ℝ) 1, p11cL_act (g t) = p11cL_act w ∧ ‖p11cL_slow (g t)‖ ≤ 2 * r ∧
        ‖p11cL_ang (g t)‖ ≤ ‖p11cL_ang w‖ + D ∧
        p11c_slowLength (p11cL_slow (g t)) ^ 2 ≤ 2 * p11c_slowLength (p11cL_slow w) ^ 2 := by
  have hIK : p11cL_act w ∈ K := hO'K hIO'
  have hz2 : p11c_slowLength (p11cL_slow w) < 2 * r / 2 := by linarith
  obtain ⟨Y, hY, hYf⟩ := p11cL_ext chi hKO hfs hIK hz2
  obtain ⟨h0, hsol, hen⟩ := hfs _ hIK _ (by linarith)
  set G : ℝ → Fin 2 → ℝ := fun t i => ∫ s in (0 : ℝ)..t,
    fderiv ℝ (fun J => chi.eval J (Y s)) (p11cL_act w) (Pi.single i 1) with hG
  have hmemI : ∀ t ∈ Icc (0 : ℝ) 1, Y t = p11c_flow chi.eval (p11cL_act w) t (p11cL_slow w) :=
    fun t ht => hYf t ⟨by linarith [ht.1], ht.2⟩
  refine ⟨fun t => assemble (p11cL_act w) (p11cL_ang w + G t) (Y t).2 (Y t).1,
    p11cL_orbit_solution chi (hKO hIK) hY _, ?_, ?_, ?_⟩
  · have hY0 : Y 0 = p11cL_slow w := by
      rw [hmemI 0 ⟨le_rfl, zero_le_one⟩, h0]
    have hG0 : G 0 = 0 := by funext i; simp [hG]
    simp only [hY0, hG0, add_zero]
    exact p11cL_assemble_eq w
  · have hY1 := hmemI 1 ⟨zero_le_one, le_rfl⟩
    have hGeq : G 1 = fun i => ∫ t in (0 : ℝ)..1, fderiv ℝ
        (fun J => chi.eval J (p11c_flow chi.eval (p11cL_act w) t (p11cL_slow w)))
        (p11cL_act w) (Pi.single i 1) := by
      funext i
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le zero_le_one] at ht
      simp only [hmemI t ht]
    rw [p11cL_liftFlow_eq]
    simp only [hY1, hGeq]
  · intro t ht
    have hYt := hmemI t ht
    have hsq := hen t ⟨by linarith [ht.1], ht.2⟩
    have hsl : p11c_slowLength (Y t) ≤ 2 * r := by
      rw [hYt]
      by_contra hc
      push_neg at hc
      have : (0 : ℝ) ≤ p11c_slowLength (p11cL_slow w) := Real.sqrt_nonneg _
      nlinarith
    refine ⟨p11cL_act_assemble _ _ _, ?_, ?_, ?_⟩
    · rw [p11cL_slow_assemble]
      exact (p11cL_norm_le_slow _).trans hsl
    · rw [p11cL_ang_assemble]
      refine (norm_add_le _ _).trans ?_
      have hGb : ‖G t‖ ≤ D := by
        refine (pi_norm_le_iff_of_nonneg hD0).2 fun i => ?_
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun s => fderiv ℝ (fun J => chi.eval J (Y s)) (p11cL_act w) (Pi.single i 1))
          (C := D) (a := 0) (b := t) fun s hs => by
            rw [uIoc_of_le ht.1] at hs
            rw [p11cL_partial_eq chi (hKO hIK)]
            have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.trans ht.2⟩
            have hb := hD _ hIK (Y s) ((p11cL_norm_le_slow _).trans (by
              rw [hmemI s hs']
              by_contra hc
              push_neg at hc
              have := hen s ⟨by linarith [hs'.1], hs'.2⟩
              have h0' : (0 : ℝ) ≤ p11c_slowLength (p11cL_slow w) := Real.sqrt_nonneg _
              nlinarith))
            exact (norm_le_pi_norm (fun i => p11cL_dI chi (p11cL_act w, Y s) i) i).trans hb
        simp only [sub_zero, abs_of_nonneg ht.1] at h
        refine h.trans ?_
        nlinarith [ht.2]
      linarith
    · rw [p11cL_slow_assemble, hYt]; exact hsq

end KAM.Planetary

end
