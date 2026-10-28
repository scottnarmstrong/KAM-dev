/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowData

/-!
# Sharp polydisc Cauchy estimate for coordinate multi-index derivatives (P11A-P7)

`p11PartialVec_norm_le`: if `g` is holomorphic on an open `U`, bounded by `M`, and the closed
polydisc of radius `R` around `J` lies in `U`, then
`‖p11PartialVec α g J‖ ≤ (∏ i, (α i)!) * M / R ^ (∑ i, α i)`.
The proof differentiates one coordinate at a time (the signed `p11PartialVec` orders the
derivatives coordinate by coordinate) and applies the one-variable estimate
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` on the circle of that coordinate,
keeping the already-differentiated coordinates at the centre.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section Cauchy

variable {n m : ℕ}

/-- One coordinate derivative. -/
def p11Step (i : Fin n) (g : P11CVec n → P11CVec m) : P11CVec n → P11CVec m :=
  fun x => fderiv ℂ g x (Pi.single i 1)

theorem p11Step_differentiableOn {U : Set (P11CVec n)} (hU : IsOpen U) {g : P11CVec n → P11CVec m}
    (hg : DifferentiableOn ℂ g U) (i : Fin n) : DifferentiableOn ℂ (p11Step i g) U := by
  have h := (KAM.analyticOnNhd_of_differentiableOn hU hg).fderiv
  exact h.differentiableOn.clm_apply (differentiableOn_const _)

theorem p11Step_iterate_differentiableOn {U : Set (P11CVec n)} (hU : IsOpen U)
    {g : P11CVec n → P11CVec m} (hg : DifferentiableOn ℂ g U) (i : Fin n) (k : ℕ) :
    DifferentiableOn ℂ ((p11Step i)^[k] g) U := by
  induction k with
  | zero => exact hg
  | succ k ih => rw [Function.iterate_succ_apply']; exact p11Step_differentiableOn hU ih i

/-- The `k`-th derivative of the restriction to the line `y + t e_i` is the `k`-fold step. -/
theorem iteratedDeriv_line {U : Set (P11CVec n)} (hU : IsOpen U) {g : P11CVec n → P11CVec m}
    (hg : DifferentiableOn ℂ g U) (i : Fin n) (y : P11CVec n) (k : ℕ) :
    ∀ t0 : ℂ, y + t0 • Pi.single i 1 ∈ U →
      iteratedDeriv k (fun t : ℂ => g (y + t • Pi.single i 1)) t0 =
        (p11Step i)^[k] g (y + t0 • Pi.single i 1) := by
  have hcont : Continuous fun t : ℂ => y + t • (Pi.single i 1 : P11CVec n) := by fun_prop
  have hΩ : IsOpen {t : ℂ | y + t • (Pi.single i 1 : P11CVec n) ∈ U} := hU.preimage hcont
  induction k with
  | zero => intro t0 _; simp
  | succ k ih =>
    intro t0 ht0
    rw [iteratedDeriv_succ, Function.iterate_succ_apply']
    have hev : iteratedDeriv k (fun t : ℂ => g (y + t • Pi.single i 1)) =ᶠ[nhds t0]
        fun t => (p11Step i)^[k] g (y + t • Pi.single i 1) := by
      filter_upwards [hΩ.mem_nhds ht0] with t ht using ih t ht
    rw [hev.deriv_eq]
    have hd : DifferentiableAt ℂ ((p11Step i)^[k] g) (y + t0 • Pi.single i 1) :=
      ((p11Step_iterate_differentiableOn hU hg i k).differentiableAt (hU.mem_nhds ht0))
    have hline : HasDerivAt (fun t : ℂ => y + t • (Pi.single i 1 : P11CVec n))
        (Pi.single i 1) t0 := by
      simpa using ((hasDerivAt_id t0).smul_const (Pi.single i 1 : P11CVec n)).const_add y
    exact (hd.hasFDerivAt.comp_hasDerivAt t0 hline).deriv

/-- One outer coordinate of the polydisc estimate. -/
theorem p11Step_iterate_bound {U : Set (P11CVec n)} (hU : IsOpen U) {g : P11CVec n → P11CVec m}
    (hg : DifferentiableOn ℂ g U) {J : P11CVec n} {R B : ℝ} (hR : 0 < R)
    (hcl : closedBall J R ⊆ U) (S : Set (Fin n)) (i : Fin n) (hiS : i ∉ S)
    (hB : ∀ y : P11CVec n, (∀ j ∈ S, y j = J j) → (∀ j, j ∉ S → ‖y j - J j‖ ≤ R) →
      ‖g y‖ ≤ B)
    (k : ℕ) (y : P11CVec n) (hy1 : ∀ j ∈ insert i S, y j = J j)
    (hy2 : ∀ j, j ∉ insert i S → ‖y j - J j‖ ≤ R) :
    ‖(p11Step i)^[k] g y‖ ≤ k.factorial * B / R ^ k := by
  have hyi : y i = J i := hy1 i (Set.mem_insert _ _)
  have hmem : ∀ t : ℂ, ‖t‖ ≤ R → y + t • (Pi.single i 1 : P11CVec n) ∈ closedBall J R := by
    intro t ht
    rw [mem_closedBall_iff_norm, pi_norm_le_iff_of_nonneg hR.le]
    intro j
    by_cases hj : j = i
    · subst hj; simp [hyi, ht]
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, hj, if_false,
        smul_zero, add_zero]
      by_cases hjS : j ∈ S
      · rw [hy1 j (Set.mem_insert_of_mem _ hjS), sub_self, norm_zero]; exact hR.le
      · exact hy2 j (by simp [hj, hjS])
  have hφd : DifferentiableOn ℂ (fun t : ℂ => g (y + t • (Pi.single i 1 : P11CVec n)))
      (closedBall 0 R) := by
    refine hg.comp (by fun_prop) fun t ht => hcl (hmem t ?_)
    simpa using ht
  have hdc : DiffContOnCl ℂ (fun t : ℂ => g (y + t • (Pi.single i 1 : P11CVec n))) (ball 0 R) :=
    ⟨hφd.mono ball_subset_closedBall, by rw [closure_ball _ hR.ne']; exact hφd.continuousOn⟩
  have hcirc : ∀ t ∈ sphere (0 : ℂ) R, ‖g (y + t • (Pi.single i 1 : P11CVec n))‖ ≤ B := by
    intro t ht
    have ht' : ‖t‖ = R := by simpa using ht
    refine hB _ (fun j hj => ?_) (fun j hj => ?_)
    · have hji : j ≠ i := fun h => hiS (h ▸ hj)
      simp [Pi.single_apply, hji, hy1 j (Set.mem_insert_of_mem _ hj)]
    · have := hmem t ht'.le
      rw [mem_closedBall_iff_norm] at this
      exact (norm_le_pi_norm (y + t • (Pi.single i 1 : P11CVec n) - J) j).trans this
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR hdc hcirc
  rw [iteratedDeriv_line hU hg i y k 0 (by simpa using hcl (hmem 0 (by simp [hR.le])))] at h
  simpa using h

/-- Coordinate runs: apply `k` derivatives in coordinate `i` for each pair `(i, k)` in order. -/
def p11Runs (P : List (Fin n × ℕ)) (g : P11CVec n → P11CVec m) : P11CVec n → P11CVec m :=
  P.foldl (fun g p => (p11Step p.1)^[p.2] g) g

theorem p11Runs_nil (g : P11CVec n → P11CVec m) : p11Runs [] g = g := rfl

theorem p11Runs_append (P : List (Fin n × ℕ)) (p : Fin n × ℕ) (g : P11CVec n → P11CVec m) :
    p11Runs (P ++ [p]) g = (p11Step p.1)^[p.2] (p11Runs P g) := by
  simp [p11Runs, List.foldl_append]

theorem p11Runs_differentiableOn {U : Set (P11CVec n)} (hU : IsOpen U) {g : P11CVec n → P11CVec m}
    (hg : DifferentiableOn ℂ g U) (P : List (Fin n × ℕ)) : DifferentiableOn ℂ (p11Runs P g) U := by
  induction P using List.reverseRecOn with
  | nil => exact hg
  | append_singleton P p ih =>
    rw [p11Runs_append]; exact p11Step_iterate_differentiableOn hU ih _ _

theorem foldl_step_replicate (i : Fin n) (k : ℕ) (g : P11CVec n → P11CVec m) :
    (List.replicate k i).foldl (fun g i => p11Step i g) g = (p11Step i)^[k] g := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]

theorem p11PartialVec_eq_runs (α : Fin n → ℕ) (g : P11CVec n → P11CVec m) :
    p11PartialVec α g = p11Runs (List.ofFn fun i => (i, α i)) g := by
  have key : ∀ (P : List (Fin n × ℕ)) (g : P11CVec n → P11CVec m),
      ((P.map fun p => List.replicate p.2 p.1).flatten).foldl (fun g i => p11Step i g) g =
        p11Runs P g := by
    intro P
    induction P with
    | nil => intro g; rfl
    | cons p P ih =>
      intro g
      simp only [List.map_cons, List.flatten_cons, List.foldl_append, foldl_step_replicate]
      exact ih _
  have := key (List.ofFn fun i => (i, α i)) g
  rw [← this, List.map_ofFn]
  rfl

/-- The polydisc estimate in the signed coordinate order, by induction on the runs. -/
theorem p11Runs_bound {U : Set (P11CVec n)} (hU : IsOpen U) {g : P11CVec n → P11CVec m}
    (hg : DifferentiableOn ℂ g U) {J : P11CVec n} {R M : ℝ} (hR : 0 < R)
    (hcl : closedBall J R ⊆ U) (hM : ∀ w ∈ U, ‖g w‖ ≤ M) (P : List (Fin n × ℕ))
    (hnd : (P.map Prod.fst).Nodup) :
    ∀ y : P11CVec n, (∀ j ∈ P.map Prod.fst, y j = J j) →
      (∀ j, j ∉ P.map Prod.fst → ‖y j - J j‖ ≤ R) →
      ‖p11Runs P g y‖ ≤
        (P.map fun p => (p.2.factorial : ℝ)).prod * M / R ^ (P.map Prod.snd).sum := by
  induction P using List.reverseRecOn with
  | nil =>
    intro y _ hy2
    have : y ∈ closedBall J R := by
      rw [mem_closedBall_iff_norm, pi_norm_le_iff_of_nonneg hR.le]
      exact fun j => hy2 j (by simp)
    rw [p11Runs_nil]
    simpa using hM y (hcl this)
  | append_singleton P p ih =>
    intro y hy1 hy2
    simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append,
      List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self] at hnd
    obtain ⟨hndP, -, hpi⟩ := hnd
    have hib : p.1 ∉ {j | j ∈ P.map Prod.fst} := fun h =>
      hpi _ h p.1 (List.mem_singleton_self _) rfl
    have hmemL : ∀ j, j ∈ (P ++ [p]).map Prod.fst ↔ j ∈ P.map Prod.fst ∨ j = p.1 := by
      intro j
      rw [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton]
    rw [p11Runs_append]
    have h := p11Step_iterate_bound hU (p11Runs_differentiableOn hU hg P) hR hcl
      {j | j ∈ P.map Prod.fst} p.1 hib
      (fun y h1 h2 => ih hndP y (fun j hj => h1 j hj) (fun j hj => h2 j hj)) p.2 y
      (by
        intro j hj
        rcases Set.mem_insert_iff.1 hj with rfl | hj
        · exact hy1 _ ((hmemL _).2 (Or.inr rfl))
        · exact hy1 j ((hmemL _).2 (Or.inl hj)))
      (by
        intro j hj
        refine hy2 j fun h => hj ?_
        rcases (hmemL _).1 h with h | h
        · exact Set.mem_insert_of_mem _ h
        · exact Set.mem_insert_iff.2 (Or.inl h))
    refine h.trans (le_of_eq ?_)
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, List.sum_append, List.sum_cons, List.sum_nil, add_zero, pow_add]
    field_simp

theorem p11PartialVec_norm_le {U : Set (P11CVec n)} (hU : IsOpen U) {g : P11CVec n → P11CVec m}
    (hg : DifferentiableOn ℂ g U) {J : P11CVec n} {R M : ℝ} (hR : 0 < R)
    (hcl : closedBall J R ⊆ U) (hM : ∀ w ∈ U, ‖g w‖ ≤ M) (α : Fin n → ℕ) :
    ‖p11PartialVec α g J‖ ≤ (∏ i, ((α i).factorial : ℝ)) * M / R ^ (∑ i, α i) := by
  rw [p11PartialVec_eq_runs]
  have hnd : ((List.ofFn fun i : Fin n => (i, α i)).map Prod.fst).Nodup := by
    rw [List.map_ofFn]
    exact List.nodup_ofFn.2 Function.injective_id
  have h := p11Runs_bound hU hg hR hcl hM (List.ofFn fun i : Fin n => (i, α i)) hnd J
    (fun j hj => rfl) (fun j hj => by simp [hR.le])
  simpa [List.map_ofFn, Function.comp_def, List.prod_ofFn, List.sum_ofFn] using h

end Cauchy

end KAM.Planetary

end
