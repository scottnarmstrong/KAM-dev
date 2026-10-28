/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Analytic

/-!
# Planar quartic torsion: uniform sixth-order bound for analytic remainders (package T10)

Blueprint P, Part 11b (`bpP:p11b:lie`, `stepP:p11b:li-ord`).  An analytic remainder
`R (I, z)` with vanishing five-jet in `z` at `z = 0` is `O (‖z‖ ^ 6)` uniformly for `I` in a
compact parameter set (`p11cN_remainder_bound`).  The proof restricts to rays and applies the
one-variable Taylor estimate, the iterated derivative along a ray being computed by composition
with a linear map.
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology

namespace KAM.Planetary

open KAM

/-- The iterated derivative along an affine line is the multilinear iterated derivative
evaluated on the direction. -/
theorem p11cN_iteratedFDeriv_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {V : Set E} (hV : IsOpen V) (k : ℕ) (hf : ContDiffOn ℝ k f V) (p v : E) {t : ℝ}
    (ht : p + t • v ∈ V) :
    iteratedFDeriv ℝ k (fun s : ℝ => f (p + s • v)) t =
      (iteratedFDeriv ℝ k f (p + t • v)).compContinuousLinearMap
        (fun _ => (ContinuousLinearMap.id ℝ ℝ).smulRight v) := by
  set g : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v with hg
  have hgx : ∀ s, g s = s • v := fun s => by simp [hg]
  set W : Set E := (fun x => p + x) ⁻¹' V with hW
  have hWo : IsOpen W := hV.preimage (continuous_const.add continuous_id)
  have hF : ContDiffOn ℝ k (fun x => f (p + x)) W :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn fun x hx => hx
  have hgo : IsOpen (g ⁻¹' W) := hWo.preimage g.continuous
  have hgt : g t ∈ W := by
    rw [hgx]; exact ht
  have h1 := g.iteratedFDerivWithin_comp_right hF hWo.uniqueDiffOn hgo.uniqueDiffOn
    (x := t) hgt (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hgo (mem_preimage.2 hgt),
    iteratedFDerivWithin_of_isOpen k hWo hgt] at h1
  have h2 : (fun s : ℝ => f (p + s • v)) = (fun x => f (p + x)) ∘ g := by
    funext s; simp [hgx]
  rw [h2, h1, iteratedFDeriv_comp_add_left, hgx]

/-- Uniform sixth-order bound for an analytic remainder with vanishing five-jet. -/
theorem p11cN_remainder_bound {O : Set (Fin 2 → ℝ)} (R : (Fin 2 → ℝ) × Phase 2 → ℝ)
    (hR : ∀ I ∈ O, AnalyticAt ℝ R (I, 0))
    (hj : ∀ I ∈ O, p11c_JetEq 5 (fun z => R (I, z)) 0)
    {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ A r : ℝ, 0 < r ∧ ∀ I ∈ K, ∀ z : Phase 2, ‖z‖ ≤ r → |R (I, z)| ≤ A * ‖z‖ ^ 6 := by
  have hAo : IsOpen {p | AnalyticAt ℝ R p} := isOpen_analyticAt ℝ R
  have hKs : K ×ˢ ({0} : Set (Phase 2)) ⊆ {p | AnalyticAt ℝ R p} := by
    rintro ⟨I, w⟩ ⟨hI, hw⟩
    rw [mem_singleton_iff] at hw
    subst hw
    exact hR I (hKO hI)
  obtain ⟨δ, hδ, hsub⟩ := (hK.prod isCompact_singleton).exists_thickening_subset_open hAo hKs
  have hmem : ∀ I ∈ K, ∀ w : Phase 2, ‖w‖ ≤ δ / 2 → AnalyticAt ℝ R (I, w) := by
    intro I hI w hw
    refine hsub ((mem_thickening_iff).2 ⟨(I, 0), ⟨hI, rfl⟩, ?_⟩)
    rw [Prod.dist_eq, dist_self, dist_zero_right]
    exact max_lt hδ (by linarith)
  set S : Set ((Fin 2 → ℝ) × Phase 2) := K ×ˢ closedBall (0 : Phase 2) (δ / 2) with hS
  have hSc : IsCompact S := hK.prod (isCompact_closedBall _ _)
  have hSA : S ⊆ {p | AnalyticAt ℝ R p} := fun u hu =>
    hmem u.1 hu.1 u.2 (by simpa using hu.2)
  have hAn : AnalyticOnNhd ℝ R {p | AnalyticAt ℝ R p} := fun p hp => hp
  have hcont : ContinuousOn (fun u => ‖iteratedFDeriv ℝ 6 R u‖) S :=
    ((hAn.iteratedFDeriv 6).continuousOn.mono hSA).norm
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn hcont
  refine ⟨B / 120, δ / 2, by linarith, fun I hI z hz => ?_⟩
  have hIO : I ∈ O := hKO hI
  set ψ : ℝ → ℝ := fun t => R ((I, 0) + t • ((0 : Fin 2 → ℝ), z)) with hψ
  have hψt : ∀ t : ℝ, (I, 0) + t • ((0 : Fin 2 → ℝ), z) = (I, t • z) := fun t => by simp
  have hmt : ∀ t ∈ Icc (0 : ℝ) 1, ‖t • z‖ ≤ δ / 2 := fun t ht => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [norm_nonneg z, ht.2]
  have hAt : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℝ R ((I, 0) + t • ((0 : Fin 2 → ℝ), z)) :=
    fun t ht => by rw [hψt]; exact hmem I hI _ (hmt t ht)
  have hCD : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 6 ψ t := by
    intro t ht
    have h1 : ContDiffAt ℝ 6 R ((I, 0) + t • ((0 : Fin 2 → ℝ), z)) := (hAt t ht).contDiffAt
    exact h1.comp t (contDiffAt_const.add (contDiff_id.smul contDiff_const).contDiffAt)
  have hCDon : ContDiffOn ℝ (5 + 1 : ℕ) ψ (Icc 0 1) := fun t ht => (hCD t ht).contDiffWithinAt
  have hRcd : ContDiffOn ℝ 6 R {p | AnalyticAt ℝ R p} := hAn.contDiffOn hAo.uniqueDiffOn
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, iteratedDerivWithin 6 ψ (Icc 0 1) t =
      iteratedFDeriv ℝ 6 R (I, t • z) (fun _ => ((0 : Fin 2 → ℝ), z)) := by
    intro t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) (hCD t ht) ht,
      iteratedDeriv_eq_iteratedFDeriv, hψ,
      p11cN_iteratedFDeriv_line hAo 6 hRcd (I, 0) _ (hAt t ht)]
    simp
  have hvan : ∀ k ≤ 5, iteratedDerivWithin k ψ (Icc 0 1) 0 = 0 := by
    intro k hk
    have hRI : AnalyticAt ℝ (fun w : Phase 2 => R (I, w)) 0 :=
      (hR I hIO).comp (g := R) (f := fun w : Phase 2 => (I, w)) (analyticAt_const.prod analyticAt_id)
    have hψ' : ψ = fun s : ℝ => (fun w : Phase 2 => R (I, w)) (0 + s • z) := by
      funext s; simp [hψ]
    have hCDk : ContDiffAt ℝ k ψ 0 := by
      have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
      exact (hCD 0 h0).of_le (by exact_mod_cast (by omega : k ≤ 6))
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) hCDk
      ⟨le_rfl, zero_le_one⟩, iteratedDeriv_eq_iteratedFDeriv, hψ',
      p11cN_iteratedFDeriv_line (isOpen_analyticAt ℝ (fun w : Phase 2 => R (I, w))) k
        (fun w hw => hw.contDiffAt.contDiffWithinAt) 0 z (by simpa using hRI)]
    simp only [zero_smul, add_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [hj I hIO k hk]
    simp
  have hbd : ∀ y ∈ Icc (0 : ℝ) 1, ‖iteratedDerivWithin (5 + 1) ψ (Icc 0 1) y‖ ≤ B * ‖z‖ ^ 6 := by
    intro y hy
    rw [show (5 + 1 : ℕ) = 6 from rfl, hder y hy]
    have hyS : (I, y • z) ∈ S := ⟨hI, by simpa using hmt y hy⟩
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have hn : ‖((0 : Fin 2 → ℝ), z)‖ = ‖z‖ := by simp [Prod.norm_def]
    simp only [hn, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (by simpa using hB _ hyS) (by positivity)
  have htay := taylor_mean_remainder_bound (zero_le_one' ℝ) hCDon (x := 1) ⟨zero_le_one, le_rfl⟩ hbd
  have hT : taylorWithinEval ψ 5 (Icc 0 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    exact Finset.sum_eq_zero fun k hk => by
      rw [hvan k (by simpa [Nat.lt_succ_iff] using hk), smul_zero]
  rw [hT, sub_zero] at htay
  have h1 : ψ 1 = R (I, z) := by simp [hψ]
  rw [h1, Real.norm_eq_abs] at htay
  refine htay.trans (le_of_eq ?_)
  simp [Nat.factorial]
  ring

end KAM.Planetary

end
