/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Analytic
public import KAM.Planetary.PlanarTorsion.OrbitJet.Jet
public import KAM.Planetary.PlanarTorsion.Setting
public import KAM.Planetary.Nondegeneracy.DiagonalTensor

/-!
# Planar quartic torsion: diagonal derivatives and jets on the slow phase space

Blueprint P, Part 11b (`stepP:p11b:pj-formal`): two facts about analytic functions `f : Phase 2 → ℝ`
at `0`.  (1) If `f (t w)` agrees with a degree-four polynomial `P` up to `O(t⁵)`, then the diagonal
derivative `D^j f(0)(w, …, w)` is `j! · [t^j] P` for `j ≤ 4` (`p11cPJ_diag_coeff`).  (2) Two analytic
functions whose diagonal derivatives of order at most `k` agree have equal jets of order `k`
(`p11cPJ_jetEq_of_diag`, by polarization).  `p11cPJequiv` identifies `Phase 2` with `Fin 4 → ℝ`.
-/

@[expose] public noncomputable section
open Filter Asymptotics Topology
open scoped ContDiff
namespace KAM.Planetary
open KAM.Planetary.OrbitJet

/-- The coefficient of `t ^ j` of a jet. -/
def p11cPJcoeff (P : Jet5) : ℕ → ℂ
  | 0 => P.a0
  | 1 => P.a1
  | 2 => P.a2
  | 3 => P.a3
  | 4 => P.a4
  | _ => 0

/-- The continuous linear equivalence `(y₀, y₁, y₂, y₃) ↦ ((y₀, y₁), (y₂, y₃))`. -/
def p11cPJequiv : (Fin 4 → ℝ) ≃L[ℝ] Phase 2 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun y => (![y 0, y 1], ![y 2, y 3])
      invFun := fun z => ![z.1 0, z.1 1, z.2 0, z.2 1]
      map_add' := fun x y => Prod.ext (funext fun i => by fin_cases i <;> simp)
        (funext fun i => by fin_cases i <;> simp)
      map_smul' := fun c x => Prod.ext (funext fun i => by fin_cases i <;> simp)
        (funext fun i => by fin_cases i <;> simp)
      left_inv := fun y => funext fun i => by fin_cases i <;> simp
      right_inv := fun z => Prod.ext (funext fun i => by fin_cases i <;> simp)
        (funext fun i => by fin_cases i <;> simp) }

theorem p11cPJequiv_apply (y : Fin 4 → ℝ) :
    p11cPJequiv y = (![y 0, y 1], ![y 2, y 3]) := rfl

private theorem pj_pow_isBigO_pow {i m : ℕ} (hm : m ≤ i) :
    (fun t : ℝ => t ^ i) =O[𝓝 0] fun t : ℝ => t ^ m := by
  refine IsBigO.of_bound 1 ?_
  have : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    simpa using ht
  filter_upwards [this] with t ht
  simp only [norm_pow, Real.norm_eq_abs, one_mul]
  exact pow_le_pow_of_le_one (abs_nonneg t) ht.le hm

private theorem pj_eq_zero_of_isBigO {j : ℕ} {c : ℂ}
    (h : (fun t : ℝ => (t : ℂ) ^ j * c) =O[𝓝 0] fun t : ℝ => t ^ (j + 1)) : c = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖c‖ ≤ C * |t| := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hC, self_mem_nhdsWithin] with t ht ht0
    have ht0' : t ≠ 0 := ht0
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at ht
    have hp : 0 < |t| ^ j := pow_pos (abs_pos.2 ht0') j
    rw [pow_succ] at ht
    have : |t| ^ j * ‖c‖ ≤ |t| ^ j * (C * |t|) := by nlinarith
    exact le_of_mul_le_mul_left this hp
  have hlim : Tendsto (fun t : ℝ => C * |t|) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * |t|) (𝓝 0) (𝓝 (C * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  exact norm_eq_zero.1 (le_antisymm (ge_of_tendsto hlim hev) (norm_nonneg _))

/-- A polynomial of degree at most four that is `O(t⁵)` has vanishing coefficients. -/
theorem p11cPJ_poly_unique (d : ℕ → ℂ)
    (h : (fun t : ℝ => ∑ k ∈ Finset.range 5, (t : ℂ) ^ k * d k) =O[𝓝 0] fun t : ℝ => t ^ 5) :
    ∀ k < 5, d k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hlow : ∀ i < k, d i = 0 := fun i hi => ih i hi (by omega)
    have hsplit : ∀ t : ℝ, ∑ i ∈ Finset.range 5, (t : ℂ) ^ i * d i =
        (t : ℂ) ^ k * d k + ∑ i ∈ Finset.Ico (k + 1) 5, (t : ℂ) ^ i * d i := by
      intro t
      rw [← Finset.sum_range_add_sum_Ico _ (show k ≤ 5 by omega)]
      have : ∑ i ∈ Finset.range k, (t : ℂ) ^ i * d i = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hlow i (Finset.mem_range.1 hi), mul_zero]
      rw [this, zero_add, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    have h1 : (fun t : ℝ => ∑ i ∈ Finset.range 5, (t : ℂ) ^ i * d i) =O[𝓝 0]
        fun t : ℝ => t ^ (k + 1) := h.trans (pj_pow_isBigO_pow (by omega))
    have h2 : (fun t : ℝ => ∑ i ∈ Finset.Ico (k + 1) 5, (t : ℂ) ^ i * d i) =O[𝓝 0]
        fun t : ℝ => t ^ (k + 1) := by
      have hsum : ∀ i ∈ Finset.Ico (k + 1) 5,
          (fun t : ℝ => (t : ℂ) ^ i * d i) =O[𝓝 0] fun t : ℝ => t ^ (k + 1) := by
        intro i hi
        have hi' := Finset.mem_Ico.1 hi
        have h3 : (fun t : ℝ => (t : ℂ) ^ i * d i) =O[𝓝 0] fun t : ℝ => t ^ i := by
          refine IsBigO.of_bound ‖d i‖ (Eventually.of_forall fun t => ?_)
          simp [norm_mul, norm_pow, mul_comm]
        exact h3.trans (pj_pow_isBigO_pow hi'.1)
      refine (IsBigO.sum hsum).congr_left fun t => ?_
      simp [Finset.sum_apply]
    have h4 : (fun t : ℝ => (t : ℂ) ^ k * d k) =O[𝓝 0] fun t : ℝ => t ^ (k + 1) := by
      refine (h1.sub h2).congr_left fun t => ?_
      rw [hsplit t]; ring
    exact pj_eq_zero_of_isBigO h4

/-- The diagonal derivatives of an analytic function along a line with a degree-four jet. -/
theorem p11cPJ_diag_coeff {f : Phase 2 → ℝ} (hf : AnalyticAt ℝ f 0) (w : Phase 2) {P : Jet5}
    (hP : IsJet (fun t : ℝ => ((f (t • w) : ℝ) : ℂ)) P) :
    ∀ j ≤ 4, ((iteratedFDeriv ℝ j f 0 (fun _ => w) : ℝ) : ℂ) =
      (j.factorial : ℂ) * p11cPJcoeff P j := by
  obtain ⟨p, r, hr⟩ := hf
  have hp : HasFPowerSeriesAt f p 0 := hr.hasFPowerSeriesAt
  have h1 := hp.isBigO_sub_partialSum_pow 5
  have h2 : Tendsto (fun t : ℝ => t • w) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => t • w := by fun_prop
    simpa using hc.tendsto 0
  have h3 := h1.comp_tendsto h2
  have h4 : (fun t : ℝ => ‖t • w‖ ^ 5) =O[𝓝 0] fun t : ℝ => t ^ 5 := by
    refine IsBigO.of_bound (‖w‖ ^ 5) (Eventually.of_forall fun t => ?_)
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, norm_pow]
    rw [abs_of_nonneg (by positivity), mul_comm]
  have h5 := h3.trans h4
  have hps : ∀ t : ℝ, p.partialSum 5 (t • w) =
      ∑ k ∈ Finset.range 5, t ^ k * p k (fun _ => w) := by
    intro t
    simp only [FormalMultilinearSeries.partialSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := (p k).map_smul_univ (fun _ : Fin k => t) (fun _ => w)
    simpa [Finset.prod_const, Finset.card_fin] using this
  have h6 : (fun t : ℝ => ((f (t • w) : ℝ) : ℂ) -
      ∑ k ∈ Finset.range 5, (t : ℂ) ^ k * ((p k (fun _ => w) : ℝ) : ℂ)) =O[𝓝 0]
        fun t : ℝ => t ^ 5 := by
    obtain ⟨C, hC⟩ := h5.bound
    refine IsBigO.of_bound C ?_
    filter_upwards [hC] with t ht
    have : ((f (t • w) : ℝ) : ℂ) - ∑ k ∈ Finset.range 5, (t : ℂ) ^ k * ((p k (fun _ => w) : ℝ) : ℂ) =
        ((f (0 + t • w) - p.partialSum 5 (t • w) : ℝ) : ℂ) := by
      rw [zero_add, hps]; push_cast; rfl
    rw [this, Complex.norm_real]
    simpa using ht
  have hev : ∀ t : ℝ, P.ev t = ∑ k ∈ Finset.range 5, (t : ℂ) ^ k * p11cPJcoeff P k := by
    intro t
    simp [Jet5.ev, Finset.sum_range_succ, p11cPJcoeff]
    ring
  have h7 : (fun t : ℝ => ∑ k ∈ Finset.range 5, (t : ℂ) ^ k *
      (((p k (fun _ => w) : ℝ) : ℂ) - p11cPJcoeff P k)) =O[𝓝 0] fun t : ℝ => t ^ 5 := by
    refine (hP.bigO.sub h6).congr_left fun t => ?_
    simp only [hev t, mul_sub, Finset.sum_sub_distrib]
    ring
  have h8 := p11cPJ_poly_unique _ h7
  intro j hj
  have h9 := h8 j (by omega)
  have h10 := hr.factorial_smul w j
  rw [← h10]
  simp only [nsmul_eq_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [sub_eq_zero.1 h9]

/-- Analytic functions with equal diagonal derivatives of order at most `k` have equal jets. -/
theorem p11cPJ_jetEq_of_diag {f g : Phase 2 → ℝ} (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0)
    (k : ℕ)
    (h : ∀ j ≤ k, ∀ w : Phase 2,
      iteratedFDeriv ℝ j f 0 (fun _ => w) = iteratedFDeriv ℝ j g 0 (fun _ => w)) :
    p11c_JetEq k f g := by
  intro j hj
  have hfa : ContDiffAt ℝ ω f 0 := hf.contDiffAt
  have hga : ContDiffAt ℝ ω g 0 := hg.contDiffAt
  set e : (Fin 4 → ℝ) →L[ℝ] Phase 2 := (p11cPJequiv : (Fin 4 → ℝ) →L[ℝ] Phase 2) with he
  set T : Phase 2 [×j]→L[ℝ] ℝ := iteratedFDeriv ℝ j f 0 - iteratedFDeriv ℝ j g 0 with hT
  have hsym : ∀ (σ : Equiv.Perm (Fin j)) (v : Fin j → Phase 2), T (v ∘ σ) = T v := by
    intro σ v
    simp only [hT, sub_apply]
    rw [hfa.iteratedFDeriv_comp_perm, hga.iteratedFDeriv_comp_perm]
  set T' : (Fin 4 → ℝ) [×j]→L[ℝ] ℝ := T.compContinuousLinearMap (fun _ => e) with hT'
  have hsym' : ∀ (σ : Equiv.Perm (Fin j)) (v : Fin j → Fin 4 → ℝ), T' (v ∘ σ) = T' v := by
    intro σ v
    simp only [hT', ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact hsym σ (fun i => e (v i))
  have hdiag : ∀ y : Fin 4 → ℝ, T' (fun _ => y) = 0 := by
    intro y
    simp only [hT', ContinuousMultilinearMap.compContinuousLinearMap_apply, hT,
      sub_apply]
    rw [h j hj (e y), sub_self]
  have hT'0 : T' = 0 := (Nondegeneracy.f_pol T' hsym').2 hdiag
  have hT0 : T = 0 := by
    ext v
    have := congrArg (fun A => A (fun i => p11cPJequiv.symm (v i))) hT'0
    simpa [hT', e, ContinuousMultilinearMap.compContinuousLinearMap_apply] using this
  exact sub_eq_zero.1 hT0

/-- Diagonal derivatives transfer along `p11cPJequiv`. -/
theorem p11cPJ_diag_comp_equiv (W : Phase 2 → ℝ) (j : ℕ) (y : Fin 4 → ℝ) :
    iteratedFDeriv ℝ j (W ∘ p11cPJequiv) 0 (fun _ => y) =
      iteratedFDeriv ℝ j W 0 (fun _ => p11cPJequiv y) := by
  have := p11cPJequiv.iteratedFDerivWithin_comp_right W uniqueDiffOn_univ
    (Set.mem_univ (p11cPJequiv (0 : Fin 4 → ℝ))) j
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at this
  rw [this]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

end KAM.Planetary

end
