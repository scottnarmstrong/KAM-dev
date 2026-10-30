/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteA.Scheme
public import KAM.Sharp2.RouteA.G1
public import KAM.Iso.Sharp.G1
import KAM.Iso.Linear.Energy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The v2 isoenergetic a-posteriori theorem, route A (blueprint `bpI:p2s2:g1`, `bpI:p2s2:frozen`)

* `RefHypIA`: the refined data of the isoenergetic theorem;
* `iso_energy_limit_A`: the energy of the limit torus.
  `KAM.Iso.Apost.tendsto_energyAverage_of_uniform`
  needs closeness `≤ μ/4`, and route A spends the free ball budget `μ/2`, so the lemma is applied
  from a
  late iterate of the scheme;
* `iso_g1_core_A`: Theorem `bpI:p2s2:g1`, route A;
* `IG1BodyA`: the frozen `IG1Body` with the refined data and the certificates on the ray;
* `iso_g1_v2A`: Corollary `bpI:p2s2:frozen`, route A, with `C₁ = min {C₁♯, c1A}`,
  `C₂ = max {C₂♯, c2I}`, `C₃ = max {C₃♯, c3I}`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology KAM.Sharp.Engine

namespace KAM.Iso.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp

/-- The refined hypotheses of the isoenergetic theorem, with the initial values `I`. -/
structure RefHypIA (N : NumA) (I : InitA) (Mh1 : ℝ) (D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ)))
    (H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ) (K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ))
    (ω : Fin N.n → ℝ) : Prop where
  dX : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ N.M1
  d2X : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ N.M2
  dH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1
  d2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ N.Mh2
  tangentT : ∀ θ ∈ complexStrip N.n N.ρ, ‖(tangentMat K θ)ᵀ‖ ≤ I.iLt
  normal : ∀ θ ∈ complexStrip N.n N.ρ, ‖normalMat K θ‖ ≤ I.iN
  normalT : ∀ θ ∈ complexStrip N.n N.ρ, ‖(normalMat K θ)ᵀ‖ ≤ I.iNt
  tors : ∀ θ ∈ complexStrip N.n (N.ρ - N.δ 0), ‖torsion H K ω θ‖ ≤ I.iH

/-- The initial cap values. -/
def initI (I : InitA) (σK σB σT μ : ℝ) : Fin 9 → ℝ :=
  ![0, σK - μ, σB - μ, σT - μ, I.iLt, I.iN, I.iNt, I.iH, 0]

/-- `C₂` of route A, isoenergetic. -/
def c2I (N : NumA) (Xs : ℝ) : ℝ :=
  N.ρ ^ (2 * N.τ) * sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xI N Xs) (fun s => (stageI N s).CD) (2 * N.τ)
      N.kp /
    (Xs * delta0 3 N.ρ N.ρinf ^ (4 * N.τ))

/-- `C₃` of route A, isoenergetic. -/
def c3I (N : NumA) (Xs : ℝ) : ℝ :=
  N.ρ ^ (2 * N.τ) * sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xI N Xs) (fun s => (stageI N s).Cp) (2 * N.τ)
      N.kp /
    (Xs * delta0 3 N.ρ N.ρinf ^ (4 * N.τ))

variable {N : NumA}

/-- Lemma `bpI:p2:energy-limit` for route A: from a late iterate, the budget `μ/4` of
`tendsto_energyAverage_of_uniform` holds with `μ/2` in place of `μ`. -/
theorem iso_energy_limit_A {M μ ρinf E₀ : ℝ} {D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))}
    {H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ} (hρinf : 0 < ρinf) (hM : 0 ≤ M) (hopen : IsOpen D)
    (hH : DifferentiableOn ℂ H D) (hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M) (hμ : 0 < μ)
    {Ks : ℕ → (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)}
    {L : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)} {ε : ℕ → ℝ}
    (hball : ∀ j, ∀ θ ∈ complexStrip N.n ρinf, Metric.ball (Ks j θ) (μ / 2) ⊆ D)
    (hd : ∀ j, DifferentiableOn ℂ (Ks j) (complexStrip N.n ρinf))
    (hLd : DifferentiableOn ℂ L (complexStrip N.n ρinf))
    (hconv : TendstoUniformlyOn Ks L atTop (complexStrip N.n ρinf))
    (hen : ∀ j, ‖KAM.Iso.energyAverage H (Ks j) - (E₀ : ℂ)‖ ≤ ε j)
    (hε : Tendsto ε atTop (𝓝 0)) :
    KAM.Iso.energyAverage H L = (E₀ : ℂ) := by
  have hμ16 : 0 < μ / 16 := by positivity
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hconv _ hμ16)
  have hcl : ∀ j ≥ j₀, ∀ θ ∈ complexStrip N.n ρinf, ‖L θ - Ks j θ‖ ≤ μ / 16 := fun j hj θ hθ => by
    have := hj₀ j hj θ hθ
    rw [dist_eq_norm] at this
    exact this.le
  have hconv' : TendstoUniformlyOn (fun j => Ks (j + j₀)) L atTop (complexStrip N.n ρinf) :=
    Metric.tendstoUniformlyOn_iff.2 fun e he =>
      (tendsto_add_atTop_nat j₀).eventually (Metric.tendstoUniformlyOn_iff.1 hconv e he)
  have hT := tendsto_energyAverage_of_uniform (μ := μ / 2) hρinf hM hopen hH hdH (half_pos hμ)
    (K := Ks j₀) (L := L) (Ks := fun j => Ks (j + j₀)) (hball j₀)
    (fun j θ hθ => by
      have h1 := hcl (j + j₀) (by omega) θ hθ
      have h2 := hcl j₀ le_rfl θ hθ
      have h3 : ‖Ks (j + j₀) θ - Ks j₀ θ‖ ≤ ‖Ks (j + j₀) θ - L θ‖ + ‖L θ - Ks j₀ θ‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      rw [norm_sub_rev (Ks (j + j₀) θ) (L θ)] at h3
      linarith)
    (fun θ hθ => by
      have := hcl j₀ le_rfl θ hθ
      linarith)
    (fun j => hd (j + j₀)) hLd hconv'
  have hE0 : Tendsto (fun j => KAM.Iso.energyAverage H (Ks (j + j₀))) atTop (𝓝 (E₀ : ℂ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => hen (j + j₀))
      ((tendsto_add_atTop_iff_nat j₀).2 hε)
  exact tendsto_nhds_unique hT hE0

/-- Blueprint `bpI:p2s2:g1`, route A. -/
theorem iso_g1_core_A (hN : N.Wf) (hiso : N.iso = true) {τ M μ σω ν γ e Xs E₀ s Mh1 : ℝ}
    {D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))} {H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ}
    {ωstar : Fin N.n → ℝ} {Ω : Set (Fin N.n → ℝ)} {m₀ : Fin 9 → ℝ}
    {K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)}
    (hS : IsoStanding N.n τ M N.sK N.sB N.sT σω ν ωstar D H γ) (hΘ : N.Θ = σω * ‖ωstar‖)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ N.M1)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ N.M2)
    (hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ N.Mh2)
    (hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1) (hHY : N.HY = Mh1 * N.sN)
    (hγb : γ ≤ N.γb) (hΩ : ∀ s : ℝ, 1 ≤ s → s • ωstar ∈ Ω) (hC : N.Cert γ Ω) (hμ : 0 < μ)
    (hm0 : m₀ 0 = 0) (hm8 : m₀ 8 = 0) (hOk : routeAOkI N (capI N (μ / 2) (ν / 2)) m₀ Xs)
    (h0 : AdmIA D H ωstar E₀ (N.r 0) (N.r 0 - N.δ 0) μ e s (m₀ 1) (m₀ 2) (m₀ 3) (m₀ 4) (m₀ 5)
      (m₀ 6) (m₀ 7) K) (hray : ν ≤ rayMargin σω ωstar s)
    (hX : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) ≤ Xs) (hXpos : 0 < Xs) :
    ∃ (Kinf : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) (sinf : ℝ),
      1 < sinf ∧ sinf < σω ∧ DifferentiableOn ℂ Kinf (complexStrip N.n N.ρinf) ∧
      IsPrimaryOnStrip Kinf N.ρinf ∧ IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, invarianceError H Kinf (sinf • ωstar) θ = 0) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, H (Kinf θ) = (E₀ : ℂ)) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ D) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ N.sK) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖Kinf θ - K θ‖ ≤
        c2I N Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))) ∧
      ‖sinf • ωstar - s • ωstar‖ ≤ c3I N Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := by
  have hγ := hS.gamma_pos
  have hν := hS.ν_pos
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hb : μ / 2 < μ := by linarith
  have hbν : ν / 2 < ν := by linarith
  have hNw := schemeIA_isNewton (E₀ := E₀) hN hiso hΘ hS hd1 hd2 hd2H hdH hHY hγb hΩ hC hb hbν
  have R := hOk.runData hN
  have h0' : (schemeIA N D H ωstar E₀ σω ν μ).Adm 0 e m₀ (K, s) := by
    refine ⟨?_, ?_⟩
    · show AdmIA D H ωstar E₀ (N.r 0) (N.r 0 - N.δ 0) (μ - m₀ 0) e s (m₀ 1) (m₀ 2) (m₀ 3) (m₀ 4)
        (m₀ 5) (m₀ 6) (m₀ 7) K
      rw [hm0, sub_zero]
      exact h0
    · show ν - m₀ 8 ≤ rayMargin σω ωstar s
      rw [hm8, sub_zero]
      exact hray
  have hlam : (0 : ℝ) < 3 := by norm_num
  have hit := SchemeA.run hNw R hlam hN.ρinf_lt hγ hγb h0' hX
  obtain ⟨hconv, hconvd, hholoL, hprimL, hrealL, hclose, hclose', hpar, -, hparb', hεz⟩ :=
    SchemeA.limit hNw R hlam hN.ρinf_pos hN.ρinf_lt hγ hγb h0' hX
  have hsub : ∀ j, complexStrip N.n N.ρinf ⊆ complexStrip N.n (N.r j) := fun j =>
    Triangular.strip_mono (hN.ρinf_lt_r j).le
  have hAdm := fun j => (hit j).1
  -- the ray scalar
  have hωpos : 0 < ‖ωstar‖ := norm_pos_iff.2 hS.ωstar_ne
  set p := (schemeIA N D H ωstar E₀ σω ν μ).limPar (K, s) with hp
  have hs : Tendsto (fun j => ((schemeIA N D H ωstar E₀ σω ν μ).iter (K, s) j).2) atTop
      (𝓝 (p / ‖ωstar‖)) := by
    refine (hpar.div_const ‖ωstar‖).congr fun j => ?_
    exact mul_div_cancel_right₀ _ hωpos.ne'
  have hmj : ∀ j, ν / 2 ≤ rayMargin σω ωstar ((schemeIA N D H ωstar E₀ σω ν μ).iter (K, s) j).2 :=
    fun j => by
      have h1 := (hAdm j).2
      have h2 := (hit j).2.1 8
      have h3 : capI N (μ / 2) (ν / 2) 8 = ν / 2 := rfl
      linarith
  have hmarg : ν / 2 ≤ rayMargin σω ωstar (p / ‖ωstar‖) :=
    ge_of_tendsto ((continuous_rayMargin.tendsto _).comp hs) (Eventually.of_forall hmj)
  have hpos : 0 < rayMargin σω ωstar (p / ‖ωstar‖) := by linarith
  have hmin : 0 < min (p / ‖ωstar‖ - 1) (σω - p / ‖ωstar‖) := by
    by_contra hneg
    exact absurd (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) (norm_nonneg ωstar))
      (not_le.2 hpos)
  have hs1 : 1 < p / ‖ωstar‖ := by linarith [(lt_min_iff.1 hmin).1]
  have hs2 : p / ‖ωstar‖ < σω := by linarith [(lt_min_iff.1 hmin).2]
  have hD : 0 < delta0 3 N.ρ N.ρinf := delta0_pos hlam hN.ρinf_lt
  have hDp : 0 < delta0 3 N.ρ N.ρinf ^ (4 * N.τ) := Real.rpow_pos_of_pos hD _
  have hρp : 0 < N.ρ ^ (2 * N.τ) := Real.rpow_pos_of_pos hρ0 _
  have hsclose : ‖(p / ‖ωstar‖) • ωstar - s • ωstar‖ ≤
      c3I N Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    calc |p / ‖ωstar‖ - s| * ‖ωstar‖ = |(p / ‖ωstar‖ - s) * ‖ωstar‖| := by
          rw [abs_mul, abs_of_pos hωpos]
      _ = |p - s * ‖ωstar‖| := by rw [sub_mul, div_mul_cancel₀ _ hωpos.ne']
      _ ≤ _ := hparb'
      _ = _ := by
          rw [show 2 * (2 * N.τ) = 4 * N.τ by ring]
          unfold c3I
          have : sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xA (2 * N.τ) (fun s => (stageI N s).CE) Xs)
              (fun s => (stageI N s).Cp) (2 * N.τ) N.kp =
            sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xI N Xs) (fun s => (stageI N s).Cp) (2 * N.τ) N.kp := rfl
          rw [this]
          field_simp
  -- the ball budget
  have hbud : ∀ j i, runCap (2 * N.τ) 3 N.ρ N.ρinf γ (stageI N) jI m₀ e j i ≤
      capI N (μ / 2) (ν / 2) i := fun j i => (hit j).2.1 i
  have hbal : ∀ θ ∈ complexStrip N.n N.ρinf,
      ‖(schemeIA N D H ωstar E₀ σω ν μ).limTor N.ρinf (K, s) θ - K θ‖ ≤ μ / 2 := fun θ hθ => by
    have h1 := hclose θ hθ
    have h2 := R.J3 0
    rw [hm0, zero_add] at h2
    have e1 : (2 * N.τ + ((jI 0 : ℕ) : ℝ)) = 2 * N.τ := by simp [jI]
    rw [e1] at h2
    exact h1.trans h2
  have hmarg' : ∀ θ ∈ complexStrip N.n N.ρinf,
      Metric.ball ((schemeIA N D H ωstar E₀ σω ν μ).limTor N.ρinf (K, s) θ) (μ / 2) ⊆ D :=
    fun θ hθ => by
      have := PerturbationAux.ball_subset_of_close (h0.ball_sub θ (hsub 0 hθ)) (hbal θ hθ)
      rwa [show μ - μ / 2 = μ / 2 by ring] at this
  have hKD : ∀ θ ∈ complexStrip N.n N.ρinf,
      (schemeIA N D H ωstar E₀ σω ν μ).limTor N.ρinf (K, s) θ ∈ D := fun θ hθ =>
    hmarg' θ hθ (Metric.mem_ball_self (half_pos hμ))
  have hXd : DifferentiableOn ℂ (hamiltonianVectorFieldℂ H) D :=
    differentiableOn_ham (hS.setting (le_refl 1)).toStanding
  have hinv : ∀ θ ∈ complexStrip N.n N.ρinf, invarianceError H
      ((schemeIA N D H ωstar E₀ σω ν μ).limTor N.ρinf (K, s)) ((p / ‖ωstar‖) • ωstar) θ = 0 :=
    fun θ hθ => lim_invariance_moving
      (Ks := fun j => (schemeIA N D H ωstar E₀ σω ν μ).tor
        ((schemeIA N D H ωstar E₀ σω ν μ).iter (K, s) j))
      (ss := fun j => ((schemeIA N D H ωstar E₀ σω ν μ).iter (K, s) j).2)
      (ε := runEps (2 * N.τ) 3 N.ρ N.ρinf γ (stageI N) e)
      ((hXd.differentiableAt (hS.isOpen.mem_nhds (hKD θ hθ))).continuousAt)
      (hconv.tendsto_at hθ) (hconvd.tendsto_at hθ) hs
      (fun j => AdmIA.error_le (hAdm j).1 θ (hsub j hθ)) hεz
  -- the energy
  have hEn : KAM.Iso.energyAverage H ((schemeIA N D H ωstar E₀ σω ν μ).limTor N.ρinf (K, s)) =
      (E₀ : ℂ) := by
    refine iso_energy_limit_A (M := M) (μ := μ) hN.ρinf_pos hS.M_pos.le hS.isOpen hS.holo
      (fun z hz => (hS.bounds z hz).1) hμ
      (Ks := fun j => (schemeIA N D H ωstar E₀ σω ν μ).tor
        ((schemeIA N D H ωstar E₀ σω ν μ).iter (K, s) j))
      (ε := runEps (2 * N.τ) 3 N.ρ N.ρinf γ (stageI N) e)
      (fun j θ hθ => ?_) (fun j => (hNw.adm (hAdm j)).2.1.mono (hsub j)) hholoL hconv
      (fun j => AdmIA.energy_le (hAdm j).1) hεz
    have h1 := AdmIA.ball_sub (hAdm j).1 θ (hsub j hθ)
    have h2 := hbud j 0
    have h3 : capI N (μ / 2) (ν / 2) 0 = μ / 2 := rfl
    rw [h3] at h2
    exact (Metric.ball_subset_ball (by linarith)).trans h1
  have hcons := (energy_conservation (hS.setting hs1.le) hN.ρinf_pos hholoL hprimL hrealL hKD
    hinv).2.1 (E₀ : ℂ) hEn
  have hdk : ∀ θ ∈ complexStrip N.n N.ρinf,
      ‖fderiv ℂ ((schemeIA N D H ωstar E₀ σω ν μ).limTor N.ρinf (K, s)) θ‖ ≤ N.sK := fun θ hθ => by
    refine le_of_tendsto (hconvd.tendsto_at hθ).norm (Eventually.of_forall fun j => ?_)
    exact (AdmIA.deriv_le (hAdm j).1 θ (hsub j hθ)).trans (hbud j 1)
  refine ⟨_, p / ‖ωstar‖, hs1, hs2, hholoL, hprimL, hrealL, hinv, hcons, hmarg', hdk, fun θ hθ =>
      ?_,
    hsclose⟩
  refine (hclose' θ hθ).trans (le_of_eq ?_)
  rw [show 2 * (2 * N.τ) = 4 * N.τ by ring]
  unfold c2I
  have : sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xA (2 * N.τ) (fun s => (stageI N s).CE) Xs)
      (fun s => (stageI N s).CD) (2 * N.τ) N.kp =
    sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xI N Xs) (fun s => (stageI N s).CD) (2 * N.τ) N.kp := rfl
  rw [this]
  field_simp

/-- The frozen `IG1Body` with the refined data of route A and the certificates on the ray. -/
def IG1BodyA (N : NumA) (I : InitA) (Mh1 M σK σB σT μ γbar σω ν : ℝ) (ωstar : Fin N.n → ℝ)
    (C₁ C₂ C₃ : ℝ) : Prop :=
  ∀ (D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))) (H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ)
    (K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) (s γ e E₀ : ℝ) (Ω : Set (Fin N.n → ℝ)),
    IsOpen D → (∀ z ∈ D, ∀ k : Fin N.n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ D) →
    DifferentiableOn ℂ H D →
    (∀ z ∈ D, ∀ k : Fin N.n → ℤ, H (z.1 + (fun i => (k i : ℂ)), z.2) = H z) →
    (∀ θ I : Fin N.n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ D →
      (H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
    (∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ H z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧ ‖iteratedFDeriv ℂ 2 H z‖ ≤ M) →
    DifferentiableOn ℂ K (complexStrip N.n N.ρ) → IsPrimaryOnStrip K N.ρ → IsRealOnReals K →
    (∀ θ ∈ complexStrip N.n N.ρ, Metric.ball (K θ) μ ⊆ D) →
    (∀ θ ∈ complexStrip N.n N.ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ) →
    (∀ θ ∈ complexStrip N.n N.ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ) →
    IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)).det →
    (∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹ i j‖ ≤ σT - μ) →
    1 < s → s < σω → ν ≤ (s - 1) * ‖ωstar‖ → ν ≤ (σω - s) * ‖ωstar‖ →
    RefHypIA N I Mh1 D H K (s • ωstar) → (∀ s' : ℝ, 1 ≤ s' → s' • ωstar ∈ Ω) → N.Cert γ Ω →
    0 < γ → γ ≤ γbar → IsDiophantine γ N.τ ωstar → 0 ≤ e →
    (∀ θ ∈ complexStrip N.n N.ρ, ‖invarianceError H K (s • ωstar) θ‖ ≤ e) →
    ‖KAM.Iso.energyAverage H K - (E₀ : ℂ)‖ ≤ e →
    C₁ * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) < 1 →
    ∃ (Kinf : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) (sinf : ℝ),
      1 < sinf ∧ sinf < σω ∧ DifferentiableOn ℂ Kinf (complexStrip N.n N.ρinf) ∧
      IsPrimaryOnStrip Kinf N.ρinf ∧ IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, invarianceError H Kinf (sinf • ωstar) θ = 0) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, H (Kinf θ) = (E₀ : ℂ)) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ D) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖Kinf θ - K θ‖ ≤ C₂ * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))) ∧
      ‖sinf • ωstar - s • ωstar‖ ≤ C₃ * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))

/-- The route-A branch of the isoenergetic frozen form. -/
theorem iso_g1_branch_A (hN : N.Wf) (hiso : N.iso = true) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar σω ν Xs Mh1 : ℝ} {I : InitA} (hM : 0 < M) (hμ : 0 < μ) (hσω : 1 < σω)
    (hν : 0 < ν) {ωstar : Fin N.n → ℝ} (hωstar : ωstar ≠ 0) (hγbar : γbar = N.γb)
    (hsK : N.sK = σK - μ / 2) (hΘ : N.Θ = σω * ‖ωstar‖) (hHY : N.HY = Mh1 * N.sN)
    (hOk : routeAOkI N (capI N (μ / 2) (ν / 2)) (initI I σK σB σT μ) Xs) (hXpos : 0 < Xs)
    {D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))} {H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ}
    {K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)} {s γ e E₀ : ℝ}
    {Ω : Set (Fin N.n → ℝ)} (hopen : IsOpen D)
    (htransl : ∀ z ∈ D, ∀ k : Fin N.n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ D)
    (hholo : DifferentiableOn ℂ H D)
    (hper : ∀ z ∈ D, ∀ k : Fin N.n → ℤ, H (z.1 + (fun i => (k i : ℂ)), z.2) = H z)
    (hreal : ∀ θ I : Fin N.n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ D →
      (H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ H z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧ ‖iteratedFDeriv ℂ 2 H z‖ ≤ M)
    (hK : DifferentiableOn ℂ K (complexStrip N.n N.ρ)) (hKp : IsPrimaryOnStrip K N.ρ)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip N.n N.ρ, Metric.ball (K θ) μ ⊆ D)
    (hDK : ∀ θ ∈ complexStrip N.n N.ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip N.n N.ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ)
    (hTu : IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)).det)
    (hTb : ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹ i j‖ ≤ σT - μ)
    (hs1 : 1 < s) (hν1 : ν ≤ (s - 1) * ‖ωstar‖) (hν2 : ν ≤ (σω - s) * ‖ωstar‖)
    (hRef : RefHypIA N I Mh1 D H K (s • ωstar)) (hΩ : ∀ s' : ℝ, 1 ≤ s' → s' • ωstar ∈ Ω)
    (hCt : N.Cert γ Ω) (hγ : 0 < γ) (hγγbar : γ ≤ γbar) (hdio : IsDiophantine γ N.τ ωstar)
    (he0 : 0 ≤ e) (hE : ∀ θ ∈ complexStrip N.n N.ρ, ‖invarianceError H K (s • ωstar) θ‖ ≤ e)
    (hEn : ‖KAM.Iso.energyAverage H K - (E₀ : ℂ)‖ ≤ e)
    (hsm : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) < Xs) :
    ∃ (Kinf : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) (sinf : ℝ),
      1 < sinf ∧ sinf < σω ∧ DifferentiableOn ℂ Kinf (complexStrip N.n N.ρinf) ∧
      IsPrimaryOnStrip Kinf N.ρinf ∧ IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, invarianceError H Kinf (sinf • ωstar) θ = 0) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, H (Kinf θ) = (E₀ : ℂ)) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ D) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖Kinf θ - K θ‖ ≤
        c2I N Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))) ∧
      ‖sinf • ωstar - s • ωstar‖ ≤ c3I N Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := by
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hS : IsoStanding N.n N.τ M N.sK N.sB N.sT σω ν ωstar D H γ :=
    { toParams := ⟨hN.two_le, hτ, hM, hN.sK, hN.sB, hN.sT⟩
      σω_gt := hσω
      ν_pos := hν
      ωstar_ne := hωstar
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := hbd
      gamma_pos := hγ
      dio := hdio }
  have : Nonempty (Fin N.n) := ⟨⟨0, by have := hN.two_le; omega⟩⟩
  have hr0 : N.r 0 = N.ρ := rSeq_zero
  have h0 : AdmIA D H ωstar E₀ (N.r 0) (N.r 0 - N.δ 0) μ e s (σK - μ) (σB - μ) (σT - μ) I.iLt I.iN
      I.iNt I.iH K := by
    rw [hr0]
    exact
      { r_pos := hρ0
        β_pos := hμ
        ε_nonneg := he0
        holo := hK
        primary := hKp
        real := hKr
        ball_sub := hball
        deriv_le := hDK
        gram := fun θ hθ =>
          ⟨(hG θ hθ).1, norm_le_of_rowSum_le_of_nonempty (m := Fin N.n) (hG θ hθ).2⟩
        tangentT := hRef.tangentT
        normal := hRef.normal
        normalT := hRef.normalT
        tors := hRef.tors
        error_le := hE
        s_gt := hs1
        twist := ⟨hTu, norm_le_of_rowSum_le_of_nonempty hTb⟩
        energy_le := hEn }
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := iso_g1_core_A hN hiso hS hΘ
    hRef.dX hRef.d2X hRef.d2H hRef.dH hHY (hγγbar.trans_eq hγbar) hΩ hCt hμ rfl rfl hOk h0
    (margin_of_le hν1 hν2) hsm.le hXpos
  exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, fun θ hθ => (h9 θ hθ).trans_eq hsK, h10, h11⟩

/-- Corollary `bpI:p2s2:frozen`, route A. `C₁♯, C₂♯, C₃♯` are v1's constants with Rüssmann's data,
so the
theorem is never worse than v1. -/
theorem iso_g1_v2A (hN : N.Wf) (hiso : N.iso = true) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar σω ν Xs Mh1 : ℝ} (I : InitA) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB)
    (hσT : 0 < σT) (hμ : 0 < μ) (hσω : 1 < σω) (hν : 0 < ν) (ωstar : Fin N.n → ℝ)
    (hωstar : ωstar ≠ 0) (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2)
    (hΘ : N.Θ = σω * ‖ωstar‖) (hHY : N.HY = Mh1 * N.sN)
    (hOk : routeAOkI N (capI N (μ / 2) (ν / 2)) (initI I σK σB σT μ) Xs) (hXpos : 0 < Xs) :
    0 < min (sharpIsoC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ ν N.τ N.ρ N.ρinf) (c1A N Xs) ∧
      0 < max (sharpIsoC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c2I N Xs) ∧
      0 < max (sharpIsoC3 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c3I N Xs) ∧
      IG1BodyA N I Mh1 M σK σB σT μ γbar σω ν ωstar
        (min (sharpIsoC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ ν N.τ N.ρ N.ρinf) (c1A N Xs))
        (max (sharpIsoC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c2I N Xs))
        (max (sharpIsoC3 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c3I N Xs)) :=
            by
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hlam : (0 : ℝ) < 3 := by norm_num
  have hD : 0 < delta0 3 N.ρ N.ρinf := delta0_pos hlam hN.ρinf_lt
  have hDp : 0 < delta0 3 N.ρ N.ρinf ^ (4 * N.τ) := Real.rpow_pos_of_pos hD _
  have hγb0 : 0 < γbar := hγbar ▸ hN.γb
  obtain ⟨hC1, hC2, hC3, hbody⟩ := KAM.Iso.Sharp.g1_sharp (n := N.n) hN.two_le hτ hN.ρinf_pos
    hN.ρinf_lt hM hσK hσB hσT hμ hγb0 hσω hν ωstar hωstar
  have hc1 : 0 < c1A N Xs := div_pos (Real.rpow_pos_of_pos hρ0 _) (mul_pos hXpos hDp)
  refine ⟨lt_min hC1 hc1, lt_max_of_lt_left hC2, lt_max_of_lt_left hC3, ?_⟩
  intro D H K s γ e E₀ Ω hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hs1 hsσ
    hν1 hν2 hRef hΩ hCt hγ hγγbar hdio he0 hE hEn hsm
  have hp2 : 0 ≤ e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
    div_nonneg he0 (mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hρ0 _)).le
  have hmono : ∀ {c c' : ℝ}, c ≤ c' → c * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) ≤
      c' * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := fun {c c'} hc => by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hc hp2
  by_cases hcase : sharpIsoC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ ν N.τ N.ρ N.ρinf ≤
      c1A N Xs
  · -- the branch of v1
    rw [min_eq_left hcase] at hsm
    obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hbody D H K s γ e E₀ hopen
      htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hs1 hsσ hν1 hν2 hγ hγγbar hdio
      he0 hE hEn hsm
    exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      fun θ hθ => (h10 θ hθ).trans (hmono (le_max_left _ _)), h11.trans (hmono (le_max_left _ _))⟩
  · -- route A
    rw [min_eq_right (not_le.1 hcase).le] at hsm
    have hsm' : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) < Xs := by
      rw [show 2 * (2 * N.τ) = 4 * N.τ by ring]
      have hρp : 0 < N.ρ ^ (4 * N.τ) := Real.rpow_pos_of_pos hρ0 _
      have e1 : c1A N Xs * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) =
          (e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (4 * N.τ))) / Xs := by
        unfold c1A
        field_simp
      rw [e1, div_lt_one hXpos] at hsm
      exact hsm
    obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := iso_g1_branch_A hN hiso hτ
        hM
      hμ hσω hν hωstar hγbar hsK hΘ hHY hOk hXpos hopen htransl hholo hper hreal hbd hK hKp hKr
          hball
      hDK hG hTu hTb hs1 hν1 hν2 hRef hΩ hCt hγ hγγbar hdio he0 hE hEn hsm'
    exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      fun θ hθ => (h10 θ hθ).trans (hmono (le_max_right _ _)), h11.trans (hmono (le_max_right _ _))⟩

end KAM.Iso.Sharp2.RouteA

end
