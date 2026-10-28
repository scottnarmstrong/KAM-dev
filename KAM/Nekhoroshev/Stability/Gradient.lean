/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Stability.RealSystem
public import KAM.Weighted.Cauchy
public import KAM.Weighted.SupWeighted

/-!
# Derivative bound and resonant gradients (`bpN:p7:theta-derivative`, `bpN:p7:resonant-gradient`)
-/

@[expose] public noncomputable section

open Set

namespace KAM.Stability

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

private theorem realInclusion_mem_polyNbhd {D : Set (Fin n → ℝ)} {ϱ : ℝ} {I : Fin n → ℝ}
    (hI : I ∈ realNbhd D ϱ) : KAM.realInclusion n I ∈ polyNbhd (cpx D) ϱ := by
  obtain ⟨J', hJ', hlt⟩ := hI
  exact ⟨KAM.realInclusion n J', ⟨J', hJ', rfl⟩, by rwa [← map_sub, KAM.norm_realInclusion]⟩

private theorem inClass_mono' {D : Set (Fin n → ℂ)} {r₀ s₀ s : ℝ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r₀ s₀ u) (hs : s ≤ s₀) :
    InClass D r₀ s u :=
  ⟨hu.differentiableOn.mono (Dom_mono le_rfl hs), fun j z hz =>
    hu.periodic j z (Dom_mono le_rfl hs hz)⟩

/-- Pointwise value bound by the weighted sum at the same action. -/
private theorem norm_le_wsum {D : Set (Fin n → ℂ)} {r s M : ℝ}
    {v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hs : 0 < s) (hv : InClass D r s v)
    (hb : WBound D r s v M) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ Dom n D r s) :
    ‖v z‖ ≤ wsum v s z.2 := by
  obtain ⟨hrep, -⟩ := coefficients_repr hs hv hb
  obtain ⟨hsum, -⟩ := hb z.2 hz.2
  refine (hrep z hz).norm_le_of_bounded hsum.hasSum fun k => ?_
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (KAM.norm_character_le k hz.1) (norm_nonneg _)

private theorem euclid_le_sum_norm (x : Fin n → ℂ) :
    KAM.Nekhoroshev.euclid x ≤ ∑ i, ‖x i‖ := by
  unfold KAM.Nekhoroshev.euclid
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_⟩
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, ‖x i‖ * ∑ j, ‖x j‖ :=
        Finset.sum_le_sum fun i _ => by
          rw [sq]
          exact mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun j => ‖x j‖) (fun _ _ => norm_nonneg _)
              (Finset.mem_univ i)) (norm_nonneg _)
    _ = (∑ i, ‖x i‖) ^ 2 := by rw [← Finset.sum_mul, sq]

theorem theta_derivative {D : Set (Fin n → ℝ)} {ϱ s M : ℝ} {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hs : 0 < s) (hu : InClass (cpx D) ϱ s u) (hb : WBound (cpx D) ϱ s u M) :
    (∀ θ : Fin n → ℝ, ∀ I ∈ realNbhd D ϱ,
      ∑ j, ‖dtheta j u (KAM.realInclusion₂ n (θ, I))‖ ≤ M / (Real.exp 1 * s) ∧
      KAM.Nekhoroshev.euclid (fun j => dtheta j u (KAM.realInclusion₂ n (θ, I))) ≤
        M / (Real.exp 1 * s)) ∧
    ∀ x ∈ Dom n (cpx D) ϱ s, ‖u x‖ ≤ M := by
  refine ⟨fun θ I hI => ?_, sup_le_wbound hu hb⟩
  have hIp := realInclusion_mem_polyNbhd hI
  have hsum : ∑ j, ‖dtheta j u (KAM.realInclusion₂ n (θ, I))‖ ≤ M / (Real.exp 1 * s) := by
    have key : ∀ s' ∈ Ioo 0 s, ∑ j, ‖dtheta j u (KAM.realInclusion₂ n (θ, I))‖ ≤
        M / (Real.exp 1 * (s - s')) := by
      intro s' hs'
      obtain ⟨h1, h2⟩ := cauchy_theta hu hb hs'.1 hs'.2
      have hz : KAM.realInclusion₂ n (θ, I) ∈ Dom n (cpx D) ϱ s' :=
        (realInclusion₂_mem_Dom_iff D hs'.1 _).2 ⟨mem_univ _, hI⟩
      have hcl := (coefficients_deriv (hs'.1.trans hs'.2) hu).1
      calc ∑ j, ‖dtheta j u (KAM.realInclusion₂ n (θ, I))‖
          ≤ ∑ j, wsum (dtheta j u) s' (KAM.realInclusion n I) :=
            Finset.sum_le_sum fun j _ => by
              have hcj := (hcl j).1
              have := norm_le_wsum hs'.1 (inClass_mono' hcj hs'.2.le) (h2 j) hz
              simpa using this
        _ ≤ wsum u s (KAM.realInclusion n I) / (Real.exp 1 * (s - s')) := (h1 _ hIp).2
        _ ≤ M / (Real.exp 1 * (s - s')) := by
            have hpos : 0 < s - s' := sub_pos.2 hs'.2
            gcongr
            exact (hb _ hIp).2
    have hlim : Filter.Tendsto (fun s' : ℝ => M / (Real.exp 1 * (s - s')))
        (nhdsWithin 0 (Ioi 0)) (nhds (M / (Real.exp 1 * s))) := by
      have hne : Real.exp 1 * (s - 0) ≠ 0 := by
        have := Real.exp_pos 1
        positivity
      have : Filter.Tendsto (fun s' : ℝ => M / (Real.exp 1 * (s - s'))) (nhds 0)
          (nhds (M / (Real.exp 1 * (s - 0)))) :=
        ContinuousAt.tendsto (ContinuousAt.div continuousAt_const (by fun_prop) hne)
      simpa using this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hs] with s' hs' using key s' hs'
  exact ⟨hsum, (euclid_le_sum_norm _).trans hsum⟩

/-- `span_ℝ Λ ⊆ ℝⁿ`. -/
def resSpan (Λ : Set (Fin n → ℤ)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun k i => (k i : ℝ)) '' Λ)

/-- The real `θ`-gradient of `realH g` at a real point is the real part of `∂_θ g`. -/
private theorem thetaGradR_realH {D : Set (Fin n → ℝ)} {r s : ℝ}
    {g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hs : 0 < s) (hg : InClass (cpx D) r s g)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ realStrip D r) (i : Fin n) :
    thetaGradR (realH g) x i = (dtheta i g (KAM.realInclusion₂ n x)).re := by
  have hxD : KAM.realInclusion₂ n x ∈ Dom n (cpx D) r s := (realInclusion₂_mem_Dom_iff D hs x).2 hx
  have hgd : DifferentiableAt ℂ g (KAM.realInclusion₂ n x) :=
    hg.differentiableOn.differentiableAt ((isOpen_Dom (n := n) (cpx D) r s).mem_nhds hxD)
  have h2 : HasFDerivAt (fun y => g (KAM.realInclusion₂ n y))
      (((fderiv ℂ g (KAM.realInclusion₂ n x)).restrictScalars ℝ).comp (KAM.realInclusion₂ n)) x :=
    (hgd.hasFDerivAt.restrictScalars ℝ).comp x (KAM.realInclusion₂ n).hasFDerivAt
  have h3 := congrArg (fun L => L (Pi.single i 1, 0)) (Complex.reCLM.hasFDerivAt.comp x h2).fderiv
  unfold thetaGradR realH dtheta
  rw [show (fun y => (g (KAM.realInclusion₂ n y)).re) =
    Complex.reCLM ∘ (fun y => g (KAM.realInclusion₂ n y)) from rfl]
  simpa [KAM.realInclusion_single] using h3

/-- `∑ⱼ vⱼ ∂_{θⱼ} g` vanishes at real points if `v ⊥ Λ` and the coefficients of `g` vanish
off `Λ`. -/
private theorem sum_dtheta_eq_zero {D : Set (Fin n → ℝ)} {r s M : ℝ} {Λ : Set (Fin n → ℤ)}
    {g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hs : 0 < s) (hg : InClass (cpx D) r s g)
    (hb : WBound (cpx D) r s g M)
    (hΛ : ∀ I ∈ polyNbhd (cpx D) r, ∀ k, k ∉ Λ → coeff g I k = 0) (v : Fin n → ℝ)
    (hv : ∀ k ∈ Λ, ∑ i, (k i : ℝ) * v i = 0) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realStrip D r) : ∑ j, (v j : ℂ) * dtheta j g (KAM.realInclusion₂ n x) = 0 := by
  obtain ⟨hcoef, -⟩ := coefficients_deriv hs hg
  have hs2 : 0 < s / 2 := half_pos hs
  have hlt : s / 2 < s := half_lt_self hs
  obtain ⟨h1, h2⟩ := cauchy_theta hg hb hs2 hlt
  have hz : KAM.realInclusion₂ n x ∈ Dom n (cpx D) r (s / 2) :=
    (realInclusion₂_mem_Dom_iff D hs2 x).2 hx
  have hI : KAM.realInclusion n x.2 ∈ polyNbhd (cpx D) r := realInclusion_mem_polyNbhd hx.2
  have hrep : ∀ j, HasSum (fun k => KAM.character k (KAM.realInclusion₂ n x).1 •
      coeff (dtheta j g) (KAM.realInclusion n x.2) k) (dtheta j g (KAM.realInclusion₂ n x)) :=
    fun j => (coefficients_repr hs2 (inClass_mono' (hcoef j).1 hlt.le) (h2 j)).1 _ hz
  have hsum := hasSum_sum (s := Finset.univ) fun j _ => (hrep j).mul_left (v j : ℂ)
  have hzero : ∀ k, ∑ j, (v j : ℂ) * (KAM.character k (KAM.realInclusion₂ n x).1 •
      coeff (dtheta j g) (KAM.realInclusion n x.2) k) = 0 := fun k => by
    by_cases hk : k ∈ Λ
    · have : ∀ j, coeff (dtheta j g) (KAM.realInclusion n x.2) k =
          (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) • coeff g (KAM.realInclusion n x.2) k :=
        fun j => (hcoef j).2 _ hI k
      simp only [this, smul_eq_mul]
      have hvk := hv k hk
      have hvk' : ∑ j, (v j : ℂ) * (k j : ℂ) = 0 := by
        have := congrArg (fun a : ℝ => (a : ℂ)) hvk
        simpa [mul_comm] using this
      calc ∑ j, (v j : ℂ) * (KAM.character k (KAM.realInclusion₂ n x).1 *
            (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) * coeff g (KAM.realInclusion n x.2) k))
          = (KAM.character k (KAM.realInclusion₂ n x).1 * (2 * (Real.pi : ℂ) * Complex.I) *
              coeff g (KAM.realInclusion n x.2) k) * ∑ j, (v j : ℂ) * (k j : ℂ) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hvk', mul_zero]
    · have hz0 := hΛ _ hI k hk
      have : ∀ j, coeff (dtheta j g) (KAM.realInclusion n x.2) k = 0 := fun j => by
        rw [(hcoef j).2 _ hI k, hz0, smul_zero]
      simp [this]
  simp only [hzero] at hsum
  exact hsum.unique hasSum_zero

theorem resonant_gradient {D : Set (Fin n → ℝ)} {r s M : ℝ} {Λ : Set (Fin n → ℤ)}
    {g : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hs : 0 < s) (hg : InClass (cpx D) r s g)
    (hgr : RealOn (Dom n (cpx D) r s) g) (hb : WBound (cpx D) r s g M)
    (hΛ : ∀ I ∈ polyNbhd (cpx D) r, ∀ k, k ∉ Λ → coeff g I k = 0) :
    ∀ x ∈ realStrip D r, thetaGradR (realH g) x ∈ resSpan Λ := by
  intro x hx
  by_contra hnot
  obtain ⟨f, hfx, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  set v : Fin n → ℝ := fun i => f (Pi.single i 1) with hvdef
  have hfv : ∀ w : Fin n → ℝ, f w = ∑ i, w i * v i := fun w => by
    conv_lhs => rw [pi_eq_sum_univ w]
    simp only [map_sum, map_smul, smul_eq_mul, hvdef]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  have hv : ∀ k ∈ Λ, ∑ i, (k i : ℝ) * v i = 0 := fun k hk => by
    rw [← hfv]
    have : f (fun i => (k i : ℝ)) ∈ (resSpan Λ).map f :=
      ⟨_, Submodule.subset_span ⟨k, hk, rfl⟩, rfl⟩
    rwa [hfmap, Submodule.mem_bot] at this
  have hxD : KAM.realInclusion₂ n x ∈ Dom n (cpx D) r s := (realInclusion₂_mem_Dom_iff D hs x).2 hx
  have h0 := sum_dtheta_eq_zero hs hg hb hΛ v hv hx
  have h1 := congrArg Complex.re h0
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.zero_re] at h1
  apply hfx
  rw [hfv]
  simp only [thetaGradR_realH hs hg hx]
  rw [← h1]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end KAM.Stability

end
