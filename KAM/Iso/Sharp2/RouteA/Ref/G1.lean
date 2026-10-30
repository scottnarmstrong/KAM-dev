/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteA.G1
public import KAM.Iso.Sharp2.RouteA.Ref.Scheme
public import KAM.Sharp2.RouteA.Ref.G1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Lever L8′ of the isoenergetic route A: the theorem

* `initRI`: the initial cap values;
* `Ref.iso_g1_core_R`: Theorem `bpI:p2s2:g1`, route A, with item (L8′) of `bp:p2s2:constantsA`;
* `Ref.iso_g1_branch_R`: the route-A branch of the frozen form;
* `iso_g1_v2A'`: the analogue of `iso_g1_v2A`: `routeAOkRI` and `Ref.Budget` in place of
  `routeAOkI`, with the same constants `c1A`, `c2I`, `c3I`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology KAM.Sharp.Engine

namespace KAM.Iso.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp

/-- The initial cap values. -/
def initRI (I : InitA) (σK σB μ : ℝ) : Fin 8 → ℝ :=
  ![0, σK - μ, σB - μ, 0, I.iLt, I.iN, I.iNt, 0]

namespace Ref

open KAM.Sharp2.RouteA.Ref

variable {N : NumA}

/-- Blueprint `bpI:p2s2:g1`, route A, with the torsion against the initial pair. -/
theorem iso_g1_core_R (hN : N.Wf) (hiso : N.iso = true) {τ M μ σω ν γ e Xs E₀ s Mh1 bF bT iH mT : ℝ}
    {D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))} {H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ}
    {ωstar : Fin N.n → ℝ} {Ω : Set (Fin N.n → ℝ)} {m₀ : Fin 8 → ℝ}
    {K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)}
    (hS : IsoStanding N.n τ M N.sK N.sB N.sT σω ν ωstar D H γ) (hΘ : N.Θ = σω * ‖ωstar‖)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ N.M1)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ N.M2)
    (hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ N.Mh2)
    (hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1) (hHY : N.HY = Mh1 * N.sN)
    (hγb : γ ≤ N.γb) (hΩ : ∀ s : ℝ, 1 ≤ s → s • ωstar ∈ Ω) (hC : N.Cert γ Ω) (hμ : 0 < μ)
    (hm0 : m₀ 0 = 0) (hm3 : m₀ 3 = 0) (hm7 : m₀ 7 = 0)
    (hOk : routeAOkRI N bF (capRI N (μ / 2) bT (ν / 2)) m₀ Xs) (hB : Budget N mT iH bF bT)
    (h0 : Adm0 D H (s • ωstar) (N.r 0) μ e (m₀ 1) (m₀ 2) (m₀ 4) (m₀ 5) (m₀ 6) K) (hs1 : 1 < s)
    (hEn : ‖KAM.Iso.energyAverage H K - (E₀ : ℂ)‖ ≤ e)
    (hTu : IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)).det)
    (hTb : ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤ mT)
    (hTs : ∀ θ ∈ complexStrip N.n (N.r 0 - N.δ 0), ‖torsion H K (s • ωstar) θ‖ ≤ iH)
    (hray : ν ≤ rayMargin σω ωstar s)
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
  have R := hOk.runData hN
  have hlam : (0 : ℝ) < 3 := by norm_num
  -- the reference data of the initial pair
  have hSt := (hS.setting hs1.le).toStanding
  have hcaps : ∀ i, m₀ i ≤ capRI N (μ / 2) bT (ν / 2) i := fun i =>
    le_of_add_le_of_nonneg_left (hOk.J3 i) (sumA_nonneg
      (fun j => rateRI_nonneg (hN.pos j) i) (xS_nonneg hN hOk.Xs_nonneg)
      (fun j => (hN.δ_pos j).le) _)
  have hδ0 : N.δ 0 = delta0 3 N.ρ N.ρinf := deltaSeq_zero
  have hX0 : e / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ))) ≤ Xs := by rw [hδ0]; exact hX
  have hc0 : N.CondR bF 0 Xs := by
    rcases Nat.eq_zero_or_pos N.kp with hk | hk
    · have := hOk.J1t
      rwa [hk] at this
    · exact hOk.J1 0 hk
  have hc0' := hc0.down hN hX0
  have hδ := hN.δ_pos 0
  have hδD := hN.δ_le_dS 0
  obtain ⟨hεδ, -, -, -⟩ := hc0'.base.facts (hN.pos 0) hγ hγb hδ hδD h0.ε_nonneg
  have hc2 : SDConst N.n N.τ γ (N.δ 0 / 2) (N.cS (0 + 1)) Ω := by
    have := (hC.at hN (0 + 1)).1
    rwa [NumA.δ_succ] at this
  have hcap0 : Adm0 D H (s • ωstar) (N.r 0) μ e N.sK N.sB N.sLt N.sN N.sNt K :=
    h0.mono (hcaps 1) (hcaps 2) (hcaps 4) (hcaps 5) (hcaps 6)
  have h3δ := hN.lam_δ_lt 0
  have hbL : N.bLocS 0 = max ((N.inp 0).bLoc0 (N.cS (0 + 1)))
      ((N.inp 0).n * (N.inp 0).sNt *
        ((N.inp 0).γb ^ 4 * (N.inp 0).δ ^ (2 * (2 * (N.inp 0).κ)))) := by
    have hf : (N.inp 0).iso = true := hiso
    simp [NumA.bLocS, StepInA.bLoc, hf]
  have hl2 := hc0'.loc
  rw [hbL] at hl2
  have hx0 : 0 ≤ e / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ))) :=
    div_nonneg h0.ε_nonneg (by positivity)
  have hR : RefTI H K (s • ωstar) (N.r 0 - N.δ 0) bF iH mT :=
    { cont := (extended_regular hSt hcap0.r_pos hcap0.holo hcap0.mem
        (fun θ hθ => (hcap0.gram θ hθ).1) (s • ωstar)).2.2
      unit := hTu
      inv := hTb
      tors := hTs
      loc := fun θ hθ => by
        have h1 := local_bound (hN.pos 0) rfl hSt hd1 hγb (hΩ s hs1.le) hcap0 hδ hδD (by linarith)
          hεδ hc2 θ hθ
        exact h1.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hx0).trans hl2)
      row := fun θ hθ => by
        have hθr : θ ∈ complexStrip N.n (N.r 0) := Triangular.strip_mono (by linarith) hθ
        have h1 := norm_etaL_le (hcap0.normalT θ hθr) (hcap0.error_le θ hθr)
        have h2 := row_le (N := N) (hN.pos 0) rfl hγ hγb hδ hδD h0.ε_nonneg h1
        exact h2.trans ((mul_le_mul_of_nonneg_right (le_max_right _ _) hx0).trans hl2)
      gram := fun θ hθ => (hcap0.gram θ (Triangular.strip_mono (by linarith) hθ)).1 }
  have hNw := schemeRI_isNewton (E₀ := E₀) hN hiso hΘ hS hd1 hd2 hd2H hdH hHY hγb hΩ hC hb hbν hR hB
  have h0' : (schemeRI N D H ωstar E₀ σω ν μ K s).Adm 0 e m₀ (K, s) := by
    refine ⟨?_, ?_⟩
    · show AdmRI D H ωstar E₀ K s (N.r 0) (N.r 0 - N.δ 0) (μ - m₀ 0) e s (m₀ 1) (m₀ 2) (m₀ 3) (m₀ 4)
        (m₀ 5) (m₀ 6) K
      rw [hm0, hm3, sub_zero]
      exact ⟨h0, hs1, hEn, fun θ _ => by simp, by simp⟩
    · show ν - m₀ 7 ≤ rayMargin σω ωstar s
      rw [hm7, sub_zero]
      exact hray
  have hit := SchemeA.run hNw R hlam hN.ρinf_lt hγ hγb h0' hX
  obtain ⟨hconv, hconvd, hholoL, hprimL, hrealL, hclose, hclose', hpar, -, hparb', hεz⟩ :=
    SchemeA.limit hNw R hlam hN.ρinf_pos hN.ρinf_lt hγ hγb h0' hX
  have hsub : ∀ j, complexStrip N.n N.ρinf ⊆ complexStrip N.n (N.r j) := fun j =>
    Triangular.strip_mono (hN.ρinf_lt_r j).le
  have hAdm := fun j => (hit j).1
  -- the ray scalar
  have hωpos : 0 < ‖ωstar‖ := norm_pos_iff.2 hS.ωstar_ne
  set p := (schemeRI N D H ωstar E₀ σω ν μ K s).limPar (K, s) with hp
  have hs : Tendsto (fun j => ((schemeRI N D H ωstar E₀ σω ν μ K s).iter (K, s) j).2) atTop
      (𝓝 (p / ‖ωstar‖)) := by
    refine (hpar.div_const ‖ωstar‖).congr fun j => ?_
    exact mul_div_cancel_right₀ _ hωpos.ne'
  have hmj : ∀ j, ν / 2 ≤
      rayMargin σω ωstar ((schemeRI N D H ωstar E₀ σω ν μ K s).iter (K, s) j).2 :=
    fun j => by
      have h1 := (hAdm j).2
      have h2 := (hit j).2.1 7
      have h3 : capRI N (μ / 2) bT (ν / 2) 7 = ν / 2 := rfl
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
          have : sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xA (2 * N.τ) (fun s => (stageRI N s).CE) Xs)
              (fun s => (stageRI N s).Cp) (2 * N.τ) N.kp =
            sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xI N Xs) (fun s => (stageI N s).Cp) (2 * N.τ) N.kp := rfl
          rw [this]
          field_simp
  -- the ball budget
  have hbud : ∀ j i, runCap (2 * N.τ) 3 N.ρ N.ρinf γ (stageRI N) jRI m₀ e j i ≤
      capRI N (μ / 2) bT (ν / 2) i := fun j i => (hit j).2.1 i
  have hbal : ∀ θ ∈ complexStrip N.n N.ρinf,
      ‖(schemeRI N D H ωstar E₀ σω ν μ K s).limTor N.ρinf (K, s) θ - K θ‖ ≤ μ / 2 := fun θ hθ => by
    have h1 := hclose θ hθ
    have h2 := R.J3 0
    rw [hm0, zero_add] at h2
    have e1 : (2 * N.τ + ((jRI 0 : ℕ) : ℝ)) = 2 * N.τ := by simp [jRI]
    rw [e1] at h2
    exact h1.trans h2
  have hmarg' : ∀ θ ∈ complexStrip N.n N.ρinf,
      Metric.ball ((schemeRI N D H ωstar E₀ σω ν μ K s).limTor N.ρinf (K, s) θ) (μ / 2) ⊆ D :=
    fun θ hθ => by
      have := PerturbationAux.ball_subset_of_close (h0.ball_sub θ (hsub 0 hθ)) (hbal θ hθ)
      rwa [show μ - μ / 2 = μ / 2 by ring] at this
  have hKD : ∀ θ ∈ complexStrip N.n N.ρinf,
      (schemeRI N D H ωstar E₀ σω ν μ K s).limTor N.ρinf (K, s) θ ∈ D := fun θ hθ =>
    hmarg' θ hθ (Metric.mem_ball_self (half_pos hμ))
  have hXd : DifferentiableOn ℂ (hamiltonianVectorFieldℂ H) D :=
    differentiableOn_ham (hS.setting (le_refl 1)).toStanding
  have hinv : ∀ θ ∈ complexStrip N.n N.ρinf, invarianceError H
      ((schemeRI N D H ωstar E₀ σω ν μ K s).limTor N.ρinf (K, s)) ((p / ‖ωstar‖) • ωstar) θ = 0 :=
    fun θ hθ => lim_invariance_moving
      (Ks := fun j => (schemeRI N D H ωstar E₀ σω ν μ K s).tor
        ((schemeRI N D H ωstar E₀ σω ν μ K s).iter (K, s) j))
      (ss := fun j => ((schemeRI N D H ωstar E₀ σω ν μ K s).iter (K, s) j).2)
      (ε := runEps (2 * N.τ) 3 N.ρ N.ρinf γ (stageRI N) e)
      ((hXd.differentiableAt (hS.isOpen.mem_nhds (hKD θ hθ))).continuousAt)
      (hconv.tendsto_at hθ) (hconvd.tendsto_at hθ) hs
      (fun j => Adm0.error_le (AdmRI.toAdm0 (hAdm j).1) θ (hsub j hθ)) hεz
  -- the energy
  have hEn : KAM.Iso.energyAverage H ((schemeRI N D H ωstar E₀ σω ν μ K s).limTor N.ρinf (K, s)) =
      (E₀ : ℂ) := by
    refine iso_energy_limit_A (M := M) (μ := μ) hN.ρinf_pos hS.M_pos.le hS.isOpen hS.holo
      (fun z hz => (hS.bounds z hz).1) hμ
      (Ks := fun j => (schemeRI N D H ωstar E₀ σω ν μ K s).tor
        ((schemeRI N D H ωstar E₀ σω ν μ K s).iter (K, s) j))
      (ε := runEps (2 * N.τ) 3 N.ρ N.ρinf γ (stageRI N) e)
      (fun j θ hθ => ?_) (fun j => (hNw.adm (hAdm j)).2.1.mono (hsub j)) hholoL hconv
      (fun j => AdmRI.energy_le (hAdm j).1) hεz
    have h1 := Adm0.ball_sub (AdmRI.toAdm0 (hAdm j).1) θ (hsub j hθ)
    have h2 := hbud j 0
    have h3 : capRI N (μ / 2) bT (ν / 2) 0 = μ / 2 := rfl
    rw [h3] at h2
    exact (Metric.ball_subset_ball (by linarith)).trans h1
  have hcons := (energy_conservation (hS.setting hs1.le) hN.ρinf_pos hholoL hprimL hrealL hKD
    hinv).2.1 (E₀ : ℂ) hEn
  have hdk : ∀ θ ∈ complexStrip N.n N.ρinf,
      ‖fderiv ℂ ((schemeRI N D H ωstar E₀ σω ν μ K s).limTor N.ρinf (K, s)) θ‖ ≤ N.sK := by
    intro θ hθ
    refine le_of_tendsto (hconvd.tendsto_at hθ).norm (Eventually.of_forall fun j => ?_)
    exact (Adm0.deriv_le (AdmRI.toAdm0 (hAdm j).1) θ (hsub j hθ)).trans (hbud j 1)
  refine ⟨_, p / ‖ωstar‖, hs1, hs2, hholoL, hprimL, hrealL, hinv, hcons, hmarg', hdk, fun θ hθ =>
      ?_,
    hsclose⟩
  refine (hclose' θ hθ).trans (le_of_eq ?_)
  rw [show 2 * (2 * N.τ) = 4 * N.τ by ring]
  unfold c2I
  have : sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xA (2 * N.τ) (fun s => (stageRI N s).CE) Xs)
      (fun s => (stageRI N s).CD) (2 * N.τ) N.kp =
    sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xI N Xs) (fun s => (stageI N s).CD) (2 * N.τ) N.kp := rfl
  rw [this]
  field_simp

/-- The route-A branch of the isoenergetic frozen form, with the torsion against the initial
pair. -/
theorem iso_g1_branch_R (hN : N.Wf) (hiso : N.iso = true) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar σω ν Xs Mh1 bF bT : ℝ} {I : InitA} (hM : 0 < M) (hμ : 0 < μ) (hσω : 1 < σω)
    (hν : 0 < ν) {ωstar : Fin N.n → ℝ} (hωstar : ωstar ≠ 0) (hγbar : γbar = N.γb)
    (hsK : N.sK = σK - μ / 2) (hΘ : N.Θ = σω * ‖ωstar‖) (hHY : N.HY = Mh1 * N.sN)
    (hOk : routeAOkRI N bF (capRI N (μ / 2) bT (ν / 2)) (initRI I σK σB μ) Xs)
    (hB : Budget N (σT - μ) I.iH bF bT) (hXpos : 0 < Xs)
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
  have h0 : Adm0 D H (s • ωstar) (N.r 0) μ e (initRI I σK σB μ 1) (initRI I σK σB μ 2)
      (initRI I σK σB μ 4) (initRI I σK σB μ 5) (initRI I σK σB μ 6) K := by
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
        error_le := hE }
  have hTs : ∀ θ ∈ complexStrip N.n (N.r 0 - N.δ 0), ‖torsion H K (s • ωstar) θ‖ ≤ I.iH := by
    rw [hr0]
    exact hRef.tors
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := iso_g1_core_R hN hiso hS hΘ
    hRef.dX hRef.d2X hRef.d2H hRef.dH hHY (hγγbar.trans_eq hγbar) hΩ hCt hμ rfl rfl rfl hOk hB h0
    hs1 hEn hTu (norm_le_of_rowSum_le_of_nonempty hTb) hTs (margin_of_le hν1 hν2) hsm.le hXpos
  exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, fun θ hθ => (h9 θ hθ).trans_eq hsK, h10, h11⟩

end Ref

open Ref KAM.Sharp2.RouteA.Ref

variable {N : NumA}

/-- The analogue of `iso_g1_v2A` with lever L8′: the frozen conclusion, whenever `routeAOkRI` and
the budgets `Ref.Budget` hold at `X⋆ > 0`. -/
theorem iso_g1_v2A' (hN : N.Wf) (hiso : N.iso = true) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar σω ν Xs Mh1 bF bT : ℝ} (I : InitA) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB)
    (hσT : 0 < σT) (hμ : 0 < μ) (hσω : 1 < σω) (hν : 0 < ν) (ωstar : Fin N.n → ℝ)
    (hωstar : ωstar ≠ 0) (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2)
    (hΘ : N.Θ = σω * ‖ωstar‖) (hHY : N.HY = Mh1 * N.sN)
    (hOk : routeAOkRI N bF (capRI N (μ / 2) bT (ν / 2)) (initRI I σK σB μ) Xs)
    (hB : Budget N (σT - μ) I.iH bF bT) (hXpos : 0 < Xs) :
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
    obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := Ref.iso_g1_branch_R hN hiso
      hτ hM
      hμ hσω hν hωstar hγbar hsK hΘ hHY hOk hB hXpos hopen htransl hholo hper hreal hbd hK hKp hKr
          hball
      hDK hG hTu hTb hs1 hν1 hν2 hRef hΩ hCt hγ hγγbar hdio he0 hE hEn hsm'
    exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      fun θ hθ => (h10 θ hθ).trans (hmono (le_max_right _ _)), h11.trans (hmono (le_max_right _ _))⟩

end KAM.Iso.Sharp2.RouteA

end
