/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Assembly.Hypotheses
public import KAM.Nekhoroshev.Poschel.Theorem1

/-!
# Part 10 assembly: confinement (`bpN:p10:confinement`)

`cf_orbit` extracts the total-field solution from the frozen `IsSolutionOn`; `cf_branch` is the
local specialization of Pöschel's Theorem 1 (branch (a)) to the concrete data of `HeadParams`,
with the Part 9 setting built locally from `hypotheses_check` (no stability assumption);
`confinement` converts the time and radius with `cp_rad`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.Canonical KAM.Stability

variable {n : ℕ}

/-- `I` lies in the real neighbourhood iff its embedding lies in the polydisc neighbourhood. -/
private theorem cf_mem_realNbhd {P : Set (Fin n → ℝ)} {r0 : ℝ} {I : Fin n → ℝ} :
    I ∈ realNbhd P r0 ↔ KAM.realInclusion n I ∈ polyNbhd (cpx P) r0 := by
  constructor
  · rintro ⟨J', hJ', hlt⟩
    exact ⟨KAM.realInclusion n J', ⟨J', hJ', rfl⟩, by rwa [← map_sub, KAM.norm_realInclusion]⟩
  · rintro ⟨_, ⟨J', hJ', rfl⟩, hlt⟩
    exact ⟨J', hJ', by rwa [← map_sub, KAM.norm_realInclusion] at hlt⟩

/-- The second derivative applied in the first slot is the Hessian action. -/
private theorem cf_fderiv_apply {h : (Fin n → ℂ) → ℂ} {I : Fin n → ℂ}
    (hd : DifferentiableAt ℂ (fderiv ℂ h) I) (u w : Fin n → ℂ) :
    fderiv ℂ (fun J => fderiv ℂ h J w) I u = fderiv ℂ (fderiv ℂ h) I u w := by
  have := hd.hasFDerivAt.clm_apply (hasFDerivAt_const w I)
  rw [this.fderiv]
  simp

/-- The operator bound in the form used by the Part 9 setting. -/
private theorem cf_hess {h : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) {B : ℝ}
    (hB : ∀ I ∈ U, ∀ x : Fin n → ℂ,
      euclid (fun i => ∑ j, complexHessian h I i j * x j) ≤ B * euclid x) :
    ∀ I ∈ U, ∀ v : Fin n → ℂ,
      euclid (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) ≤ B * euclid v := by
  intro I hI v
  have hd : DifferentiableAt ℂ (fderiv ℂ h) I :=
    ((KAM.holomorphic_regularity hU hh).1).differentiableAt (hU.mem_nhds hI)
  have key : (fun i => fderiv ℂ (fun J => fderiv ℂ h J v) I (Pi.single i 1)) =
      fun i => ∑ j, complexHessian h I i j * v j := by
    funext i
    rw [cf_fderiv_apply hd]
    have hv : v = ∑ j, v j • (Pi.single j 1 : Fin n → ℂ) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    unfold complexHessian
    rw [cf_fderiv_apply hd]
  rw [key]
  exact hB I hI v

/-- cf-setting: the Part 9 setting for the concrete data, built locally from the concrete
analytic clauses of `hypotheses_check`. -/
private theorem cf_setting (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hh : HeadHyp p h) (hf : IsAnalyticPerturbation p.R p.s ε f)
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) :
    Theorem1Setting {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2} p.r0 p.s1 p.mu p.B p.ell h f := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, hholo, hreal, hess, hqc, fcl, freal, fb, -, -⟩ := hypotheses_check hn p hp hh hf hε hε0
  obtain ⟨-, -, -, -, -, hmu, hmuB, -, -, -, hrad, -⟩ := choice_props hn p hp
  have hs1 : 0 < p.s1 := by unfold HeadParams.s1; linarith [hp.hs]
  have hr0 := p.r0_pos hn1 hp
  have hnb : ∀ I : Fin n → ℝ, I ∈ realNbhd {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2} p.r0 →
      KAM.realInclusion n I ∈ polyNbhd (centralSet n p.R) p.r0 := fun I hI =>
    cf_mem_realNbhd.1 hI
  refine ⟨by omega, hr0, hs1, hmu, hmuB, p.ell_pos hn1 hp, hholo, ?_,
    cf_hess (isOpen_polyNbhd _ _) hholo hess, ?_, hrad, fcl, freal, ⟨_, fb⟩⟩
  · intro x hx
    have hx' := (realInclusion₂_mem_Dom_iff {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2} hs1 x).1 hx
    exact hreal x.2 (hnb _ hx'.2)
  · intro I hI ξ
    by_cases hle : |∑ i, KAM.frequencyMap h I i * ξ i| ≤ p.ell * euclid ξ
    · exact Or.inr (hqc I (hnb I hI) ξ hle)
    · exact Or.inl (lt_of_not_ge hle)

/-- cf-orbit: extract a total-field solution; no confinement in the smaller tube is assumed. -/
theorem cf_orbit {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {U : Set (Fin n → ℝ)} {J : Set ℝ} {y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hy : IsSolutionOn H U J y) :
    ∀ t ∈ J, HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t :=
  fun t ht => (hy t ht).2.2

/-- Part 9 thm1(a) specialized to the concrete data, with the uniform shorter time. -/
theorem cf_branch (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hh : HeadHyp p h) (hf : IsAnalyticPerturbation p.R p.s ε f)
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) {θ₀ I₀ : Fin n → ℝ}
    (hI : I₀ ∈ actionBall n (p.R / 2)) {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hy0 : y 0 = (θ₀, I₀))
    (hy : IsSolutionOn (KAM.realHamiltonian h f) (actionBall n p.R) J y) :
    ∀ t ∈ J, |t| ≤ 2 * p.T * Real.exp
        (Real.pi * p.s1 / (3 * Real.sqrt n) * (p.eps1 / p.epsPrime ε) ^ HeadParams.expo n) →
      KAM.realInclusion n (y t).2 ∈ KAM.Weighted.polyNbhd (centralSet n p.R) p.r0 ∧
      ‖(y t).2 - I₀‖ ≤ p.R0 / 2 * (p.epsPrime ε / p.eps1) ^ HeadParams.expo n := by
  have hn1 : 1 ≤ n := by omega
  obtain rfl : I₀ = (y 0).2 := by rw [hy0]
  have S := cf_setting hn p hp hh hf hε hε0
  obtain ⟨-, -, -, -, -, -, -, hfb, hdd, hde⟩ := hypotheses_check hn p hp hh hf hε hε0
  have hIP : (y 0).2 ∈ {J : Fin n → ℝ | ‖J‖ ≤ p.R / 2} := by
    simp only [actionBall, mem_ball, dist_zero_right] at hI
    exact hI.le
  have hfun : realH (fun w => h w.2 + f w) = KAM.realHamiltonian h f := by
    funext x
    rfl
  obtain ⟨ka, -⟩ := thm1 S hdd hde hfb (F := KAM.hamiltonianVectorField (KAM.realHamiltonian h f))
    (fun x _ => by rw [hfun]) hJ h0 (cf_orbit hy) hIP
  obtain ⟨-, ⟨I1, hI1, hmx⟩, -, hcen, -⟩ := omega0 S (y 0).2 hIP
  obtain ⟨hlow1, hlow2⟩ := hc_exc hn p hp hh (y 0).2 hI
  have hOm0 : 0 < (omega0Ball S (y 0).2 hIP).maximum :=
    lt_of_lt_of_le hp.hω (hlow2.trans hcen)
  have hup : (omega0Ball S (y 0).2 hIP).maximum ≤ Real.sqrt n * p.M := by
    rw [hmx]
    exact hc_time hn p hp hh _ hI I1 hI1
  have hpre := head_time_prefactor hn p hp hOm0 hup
  intro t ht htime
  obtain ⟨hm, hn'⟩ := ka (hlow1.le.trans hlow2) t ht
    (htime.trans (mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le))
  exact ⟨cf_mem_realNbhd.1 hm.2, hn'⟩

/-- confinement, including endpoints of any interval J containing 0. -/
theorem confinement (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hh : HeadHyp p h) (hf : IsAnalyticPerturbation p.R p.s ε f)
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) {θ₀ I₀ : Fin n → ℝ}
    (hI : I₀ ∈ actionBall n (p.R / 2)) {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hy0 : y 0 = (θ₀, I₀))
    (hy : IsSolutionOn (KAM.realHamiltonian h f) (actionBall n p.R) J y) :
    ∀ t ∈ J, |t| ≤ p.tau ε → ‖(y t).2 - I₀‖ ≤ p.rho ε := by
  have hn1 : 1 ≤ n := by omega
  intro t ht htau
  obtain ⟨c1, c2⟩ := cp_rad hn p hp hε
  have hT := p.T_pos hn1 hp
  have hC := p.C_pos hn1 hp
  have hexp := Real.exp_pos (p.c * ε ^ (-HeadParams.expo n))
  have htime : |t| ≤ 2 * p.T * Real.exp
      (Real.pi * p.s1 / (3 * Real.sqrt n) * (p.eps1 / p.epsPrime ε) ^ HeadParams.expo n) := by
    rw [c2]
    calc |t| ≤ p.tau ε := htau
      _ = p.T * Real.exp (p.c * ε ^ (-HeadParams.expo n)) := rfl
      _ ≤ 2 * p.T * Real.exp (p.c * ε ^ (-HeadParams.expo n)) := by nlinarith [mul_pos hT hexp]
  have hb := (cf_branch hn p hp hh hf hε hε0 hI hJ h0 hy0 hy t ht htime).2
  rw [c1] at hb
  have hρ : 0 ≤ p.rho ε := (mul_pos hC (Real.rpow_pos_of_pos hε _)).le
  linarith

end KAM.Nekhoroshev

end
