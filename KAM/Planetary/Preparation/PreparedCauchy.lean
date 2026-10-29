/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowCauchy

/-!
# Polydisc Cauchy estimate with one radius per coordinate (P11A-P8b, `stepP:p11:pr-in`)

`p11PartialVec_norm_le_poly`: if `g` is holomorphic on an open `U`, bounded by `M`, and the closed
polydisc `{y | ∀ j, ‖y j - J j‖ ≤ R j}` lies in `U`, then
`‖p11PartialVec α g J‖ ≤ (∏ i, (α i)!) * M / ∏ i, R i ^ α i`.
It is the copy of `p11PartialVec_norm_le` (`SlowCauchy`) with a radius per coordinate, needed for
the mixed radii `s₂/4` (in `J`) and `ε/4` (in `ρ̃`) of the Cauchy estimates (e2) of step pr-in.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section PolyCauchy

variable {n m : ℕ}

/-- One outer coordinate of the polydisc estimate with radii `R`. -/
theorem p11PolyStep_iterate_bound {U : Set (P11CVec n)} (hU : IsOpen U)
    {g : P11CVec n → P11CVec m} (hg : DifferentiableOn ℂ g U) {J : P11CVec n} {R : Fin n → ℝ}
    {B : ℝ} (hR : ∀ j, 0 < R j) (hcl : {y | ∀ j, ‖y j - J j‖ ≤ R j} ⊆ U)
    (S : Set (Fin n)) (i : Fin n) (hiS : i ∉ S)
    (hB : ∀ y : P11CVec n, (∀ j ∈ S, y j = J j) → (∀ j, j ∉ S → ‖y j - J j‖ ≤ R j) →
      ‖g y‖ ≤ B)
    (k : ℕ) (y : P11CVec n) (hy1 : ∀ j ∈ insert i S, y j = J j)
    (hy2 : ∀ j, j ∉ insert i S → ‖y j - J j‖ ≤ R j) :
    ‖(p11Step i)^[k] g y‖ ≤ k.factorial * B / R i ^ k := by
  have hyi : y i = J i := hy1 i (Set.mem_insert _ _)
  have hmem : ∀ t : ℂ, ‖t‖ ≤ R i →
      ∀ j, ‖(y + t • (Pi.single i 1 : P11CVec n)) j - J j‖ ≤ R j := by
    intro t ht j
    by_cases hj : j = i
    · subst hj; simp [hyi, ht]
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hj, ite_false,
        smul_zero, add_zero]
      by_cases hjS : j ∈ S
      · rw [hy1 j (Set.mem_insert_of_mem _ hjS), sub_self, norm_zero]; exact (hR j).le
      · exact hy2 j (by simp [hj, hjS])
  have hφd : DifferentiableOn ℂ (fun t : ℂ => g (y + t • (Pi.single i 1 : P11CVec n)))
      (closedBall 0 (R i)) := by
    refine hg.comp (by fun_prop) fun t ht => hcl (hmem t ?_)
    simpa using ht
  have hdc : DiffContOnCl ℂ (fun t : ℂ => g (y + t • (Pi.single i 1 : P11CVec n)))
      (ball 0 (R i)) :=
    ⟨hφd.mono ball_subset_closedBall, by rw [closure_ball _ (hR i).ne']; exact hφd.continuousOn⟩
  have hcirc : ∀ t ∈ sphere (0 : ℂ) (R i),
      ‖g (y + t • (Pi.single i 1 : P11CVec n))‖ ≤ B := by
    intro t ht
    have ht' : ‖t‖ = R i := by simpa using ht
    refine hB _ (fun j hj => ?_) (fun j hj => ?_)
    · have hji : j ≠ i := fun h => hiS (h ▸ hj)
      simp [hji, hy1 j (Set.mem_insert_of_mem _ hj)]
    · exact hmem t ht'.le j
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (hR i) hdc hcirc
  rw [iteratedDeriv_line hU hg i y k 0
    (by simpa using hcl (hmem 0 (by simp [(hR i).le])))] at h
  simpa using h

/-- The polydisc estimate with radii `R`, by induction on the runs. -/
theorem p11PolyRuns_bound {U : Set (P11CVec n)} (hU : IsOpen U) {g : P11CVec n → P11CVec m}
    (hg : DifferentiableOn ℂ g U) {J : P11CVec n} {R : Fin n → ℝ} {M : ℝ}
    (hR : ∀ j, 0 < R j) (hcl : {y | ∀ j, ‖y j - J j‖ ≤ R j} ⊆ U)
    (hM : ∀ w ∈ U, ‖g w‖ ≤ M) (P : List (Fin n × ℕ)) (hnd : (P.map Prod.fst).Nodup) :
    ∀ y : P11CVec n, (∀ j ∈ P.map Prod.fst, y j = J j) →
      (∀ j, j ∉ P.map Prod.fst → ‖y j - J j‖ ≤ R j) →
      ‖p11Runs P g y‖ ≤
        (P.map fun p => (p.2.factorial : ℝ)).prod * M /
          (P.map fun p => R p.1 ^ p.2).prod := by
  induction P using List.reverseRecOn with
  | nil =>
    intro y _ hy2
    rw [p11Runs_nil]
    simpa using hM y (hcl (fun j => hy2 j (by simp)))
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
    have h := p11PolyStep_iterate_bound hU (p11Runs_differentiableOn hU hg P) hR hcl
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
    have hpos : 0 < (P.map fun p => R p.1 ^ p.2).prod :=
      List.prod_pos (by simp only [List.mem_map]; rintro _ ⟨q, -, rfl⟩; exact pow_pos (hR _) _)
    have hRp : 0 < R p.1 ^ p.2 := pow_pos (hR _) _
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one]
    field_simp

/-- Polydisc Cauchy estimate with one radius per coordinate. -/
theorem p11PartialVec_norm_le_poly {U : Set (P11CVec n)} (hU : IsOpen U)
    {g : P11CVec n → P11CVec m} (hg : DifferentiableOn ℂ g U) {J : P11CVec n}
    {R : Fin n → ℝ} {M : ℝ} (hR : ∀ j, 0 < R j) (hcl : {y | ∀ j, ‖y j - J j‖ ≤ R j} ⊆ U)
    (hM : ∀ w ∈ U, ‖g w‖ ≤ M) (α : Fin n → ℕ) :
    ‖p11PartialVec α g J‖ ≤ (∏ i, ((α i).factorial : ℝ)) * M / ∏ i, R i ^ α i := by
  rw [p11PartialVec_eq_runs]
  have hnd : ((List.ofFn fun i : Fin n => (i, α i)).map Prod.fst).Nodup := by
    rw [List.map_ofFn]
    exact List.nodup_ofFn.2 Function.injective_id
  have h := p11PolyRuns_bound hU hg hR hcl hM (List.ofFn fun i : Fin n => (i, α i)) hnd J
    (fun j hj => rfl) (fun j hj => by simp [(hR j).le])
  simpa [List.map_ofFn, Function.comp_def, List.prod_ofFn] using h

end PolyCauchy

end KAM.Planetary

end
