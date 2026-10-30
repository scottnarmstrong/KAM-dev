/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp.Scheme
public import KAM.Iso.Apost.G1
public import KAM.Sharp.CohData
import KAM.Iso.Linear.Energy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The sharp I-G1 (blueprint `bpI:p2s:g1`)

`KAM.Iso.Sharp.g1_gen` is the frozen body `KAM.Iso.Charts.IG1Body` of `KAM.Iso.isoenergetic_kam`
with the sharp constants `C₁♯ = sharpIsoC1`, `C₂♯ = sharpIsoC2`, `C₃♯ = sharpIsoC3` for general
small-divisor data `(κ, c_R)` (a conditional helper). The instances `g1_sharp` (Rüssmann, the
headline), `g1_sharp_parseval` and `g1_sharp_crude` have the binders of
`KAM.Iso.Apost.g1_explicit`, verbatim, and no hypothesis on `(κ, c_R)`.

The proof is `iso_g1_core`, following the blueprint:

* `stepI:p2s:g1-eng`: the isoenergetic scheme (`KAM.Iso.Sharp.isoScheme`) is run by the engine
  (`Engine.Scheme.iterate`, `Engine.Scheme.limit`) from `(K, s)` with the bounds
  `m⁽⁰⁾ = (σ_K - μ, σ_B - μ, σ_T - μ, 0)`;
* `stepI:p2s:g1-lim`: `s_∞ = p_∞/|ω*|`; the ray margins `ν(s_j) ≥ ν/2` pass to the limit
  (continuity of `ν(·)`), so `1 < s_∞ < σ_ω`; `|s_∞ ω* - s ω*| = |p_∞ - p_0|`;
* `stepI:p2s:g1-o`: invariance at the moving frequency (`KAM.Iso.Apost.lim_invariance_moving`),
  the energy (`KAM.Iso.Sharp.iso_energy_limit` and `KAM.Iso.Linear.energy_conservation`), the
  margins (`KAM.Apost.lim_margins`) and `|DK_∞| ≤ σ_K - μ/2` from the caps.

`g1_gen` then turns `C₁♯ e/(γ⁴ρ^{4τ}) < 1` into `e < 1` and `ĉ_* e/(γ⁴δ₀^{2a}) < 1`
(`KAM.Apost.g1_error_small_aux`) and `2 C e/(γ²δ₀^a)` into `C♯ e/(γ²ρ^{2τ})`
(`KAM.Apost.g1_closeness_eq`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp

section Core

variable {n : ℕ} {κ cR M σK σB σT γb μ ν : ℝ}
variable {τ σω : ℝ} {ωstar : Fin n → ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {γ : ℝ}

/-- The ray margin `ν(s) = min {s - 1, σ_ω - s} |ω*|` is continuous in `s`. -/
theorem continuous_rayMargin : Continuous (rayMargin σω ωstar) := by
  unfold rayMargin
  exact ((continuous_id.sub continuous_const).min (continuous_const.sub continuous_id)).mul
    continuous_const

/-- The core of `g1_gen`: the conclusion of I-G1 with the closeness `2 C_ΔK e/(γ² δ₀^a)` and the
frequency closeness `2 C_Δω e/(γ² δ₀^a)`, from the admissibility of `(K, s)` with the bounds
`(σ_K - μ, σ_B - μ, σ_T - μ, 0)` and `ĉ_* e/(γ⁴ δ₀^{2a}) ≤ 1`. -/
theorem iso_g1_core (hC : CohData n τ κ cR) (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    (hγb : γ ≤ γb) {E₀ ρ ρinf e s : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hμ : 0 < μ)
    (h0 : (isoScheme n H D ωstar E₀ σω ν).Adm ρ μ e ![σK - μ, σB - μ, σT - μ, 0] (K, s))
    (hsm : iCStar n κ cR M σK σB σT γb μ ν * e / (γ ^ 4 * delta0s ρ ρinf ^ (2 * (2 * κ))) ≤ 1) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
      1 < sinf ∧ sinf < σω ∧ DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧
      IsPrimaryOnStrip Kinf ρinf ∧ IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n ρinf, invarianceError H Kinf (sinf • ωstar) θ = 0) ∧
      (∀ θ ∈ complexStrip n ρinf, H (Kinf θ) = (E₀ : ℂ)) ∧
      (∀ θ ∈ complexStrip n ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ D) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤
        2 * iCDK n cR M σK σB σT γb * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ))) ∧
      ‖sinf • ωstar - s • ωstar‖ ≤
        2 * iCDw n cR M σK σB σT γb * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ)) := by
  have hγ := hS.gamma_pos
  have hP := hS.toParams
  have hν := hS.ν_pos
  -- step `g1-eng`: the engine
  have hN := isoScheme_isNewton (κ := κ) (cR := cR) (μ := μ) hC hS hγb hμ.le E₀
  have he : 0 ≤ e := (hN.adm h0).1
  obtain ⟨hEh, hst, hbl, hcap⟩ := iso_engine_hyps (κ := κ) hC hP (ρinf := ρinf) hρ hγ hγb hμ hν
    he hsm
  have hit := Engine.Scheme.iterate hN hρinf hρ hγ h0 hEh hst hbl hcap
  obtain ⟨hconv, hconvd, hholoL, hprimL, hrealL, hclose, hpar, hparb, hεz⟩ :=
    Engine.Scheme.limit hN hρinf hρ hγ h0 hEh hst hbl hcap
  have hsch := Engine.schedule (lam := (isoConsts n κ cR M σK σB σT γb μ ν).lam) hN.lam_pos
    hρinf hρ
  have hsub : ∀ j, complexStrip n ρinf ⊆
      complexStrip n (Engine.rSeq (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf j) :=
    fun j => Triangular.strip_mono (hsch.2.2.2.2.1 j).le
  have hsubρ : complexStrip n ρinf ⊆ complexStrip n ρ := Triangular.strip_mono hρ.le
  obtain ⟨h0', -⟩ := isoScheme_adm_iff.1 h0
  have hAdm := fun j => isoScheme_adm_iff.1 (hit j).1
  -- step `g1-lim`: the ray scalar
  have hωpos : 0 < ‖ωstar‖ := norm_pos_iff.2 hS.ωstar_ne
  set p := (isoScheme n H D ωstar E₀ σω ν).limPar (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf
    (K, s) with hp
  have hs : Tendsto (fun j => ((isoScheme n H D ωstar E₀ σω ν).iter
      (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf (K, s) j).2) atTop
      (𝓝 (p / ‖ωstar‖)) := by
    refine (hpar.div_const ‖ωstar‖).congr fun j => ?_
    exact mul_div_cancel_right₀ _ hωpos.ne'
  have hmj : ∀ j, ν / 2 ≤ rayMargin σω ωstar ((isoScheme n H D ωstar E₀ σω ν).iter
      (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf (K, s) j).2 := fun j => by
    have h1 := (hAdm j).2
    have h2 := (hit j).2.2.1 3
    have h3 : (isoConsts n κ cR M σK σB σT γb μ ν).cap 3 = ν / 2 := rfl
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
  have hsclose : ‖(p / ‖ωstar‖) • ωstar - s • ωstar‖ ≤
      2 * iCDw n cR M σK σB σT γb * e / (γ ^ 2 * delta0s ρ ρinf ^ (2 * κ)) := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    calc |p / ‖ωstar‖ - s| * ‖ωstar‖ = |(p / ‖ωstar‖ - s) * ‖ωstar‖| := by
          rw [abs_mul, abs_of_pos hωpos]
      _ = |p - s * ‖ωstar‖| := by rw [sub_mul, div_mul_cancel₀ _ hωpos.ne']
      _ ≤ _ := hparb
  -- step `g1-o`: margins, invariance, energy, derivative
  have hmarg' : ∀ θ ∈ complexStrip n ρinf, Metric.ball ((isoScheme n H D ωstar E₀ σω ν).limTor
      (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf (K, s) θ) (μ / 2) ⊆ D := fun θ hθ =>
    lim_margins ((hclose θ hθ).trans hbl) (h0'.ball_sub θ (hsubρ hθ))
  have hKD : ∀ θ ∈ complexStrip n ρinf, (isoScheme n H D ωstar E₀ σω ν).limTor
      (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf (K, s) θ ∈ D := fun θ hθ =>
    hmarg' θ hθ (Metric.mem_ball_self (half_pos hμ))
  have hXd : DifferentiableOn ℂ (hamiltonianVectorFieldℂ H) D :=
    differentiableOn_ham (hS.setting (le_refl 1)).toStanding
  have hinv : ∀ θ ∈ complexStrip n ρinf, invarianceError H ((isoScheme n H D ωstar E₀ σω ν).limTor
      (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf (K, s)) ((p / ‖ωstar‖) • ωstar) θ = 0 :=
    fun θ hθ => lim_invariance_moving
      (Ks := fun j => (isoScheme n H D ωstar E₀ σω ν).tor ((isoScheme n H D ωstar E₀ σω ν).iter
        (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf (K, s) j))
      (ss := fun j => ((isoScheme n H D ωstar E₀ σω ν).iter
        (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf (K, s) j).2)
      (ε := fun j => (isoConsts n κ cR M σK σB σT γb μ ν).eps ρ ρinf γ e j)
      ((hXd.differentiableAt (hS.isOpen.mem_nhds (hKD θ hθ))).continuousAt)
      (hconv.tendsto_at hθ) (hconvd.tendsto_at hθ) hs
      (fun j => (hAdm j).1.error_le θ (hsub j hθ)) hεz
  have hEnergy := iso_energy_limit (κ := κ) (cR := cR) (γb := γb) hC hS hγb hρinf hρ hμ h0
    (fun _ => le_rfl) hsm
  have hcons := (energy_conservation (hS.setting hs1.le) hρinf hholoL hprimL hrealL hKD
    hinv).2.1 (E₀ : ℂ) hEnergy
  have hdk : ∀ θ ∈ complexStrip n ρinf, ‖fderiv ℂ ((isoScheme n H D ωstar E₀ σω ν).limTor
      (isoConsts n κ cR M σK σB σT γb μ ν).lam ρ ρinf (K, s)) θ‖ ≤ σK - μ / 2 := by
    intro θ hθ
    refine le_of_tendsto (hconvd.tendsto_at hθ).norm (Eventually.of_forall fun j => ?_)
    have h1 := (hAdm j).1.deriv_le θ (hsub j hθ)
    have h2 := (hit j).2.2.1 0
    have h3 : (isoConsts n κ cR M σK σB σT γb μ ν).cap 0 = σK - μ / 2 := rfl
    exact h1.trans (h2.trans h3.le)
  exact ⟨_, p / ‖ωstar‖, hs1, hs2, hholoL, hprimL, hrealL, hinv, hcons, hmarg', hdk, hclose,
    hsclose⟩

end Core

/-- Blueprint `bpI:p2s:g1` for general small-divisor data (a conditional helper; the source results are
the instances below). The body is the frozen `IG1Body`. -/
theorem g1_gen {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ) {κ cR : ℝ}
    (hC : CohData n τ κ cR) {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ γbar σω ν : ℝ}
    (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT)
    (hμ : 0 < μ) (hγbar : 0 < γbar) (hσω : 1 < σω) (hν : 0 < ν)
    (ωstar : Fin n → ℝ) (hωstar : ωstar ≠ 0) :
    0 < sharpIsoC1 n κ cR M σK σB σT γbar μ ν τ ρ ρinf ∧
      0 < sharpIsoC2 n κ cR M σK σB σT γbar τ ρ ρinf ∧
      0 < sharpIsoC3 n κ cR M σK σB σT γbar τ ρ ρinf ∧
      KAM.Iso.Charts.IG1Body n τ ρ ρinf M σK σB σT μ γbar σω ν ωstar
        (sharpIsoC1 n κ cR M σK σB σT γbar μ ν τ ρ ρinf) (sharpIsoC2 n κ cR M σK σB σT γbar τ ρ ρinf)
        (sharpIsoC3 n κ cR M σK σB σT γbar τ ρ ρinf) := by
  have hP : Params n τ M σK σB σT := ⟨hn, hτ, hM, hσK, hσB, hσT⟩
  have hρ0 : 0 < ρ := hρinf.trans hρinfρ
  obtain ⟨hDK, hDw, -, -, -, -, hcs⟩ := iso_consts_pos (n := n) (κ := κ) (by omega) hC.cR_pos hM
    hσK hσB hσT hγbar hμ hν
  have hD0 : 0 < delta0s ρ ρinf := Engine.delta0_pos (by norm_num : (0 : ℝ) < 3) hρinfρ
  refine ⟨mul_pos (Real.rpow_pos_of_pos hρ0 _) (lt_max_of_lt_left (pow_pos hγbar 4)),
    mul_pos (mul_pos (mul_pos two_pos hDK) (Real.rpow_pos_of_pos hρ0 _))
      (Real.rpow_pos_of_pos hD0 _),
    mul_pos (mul_pos (mul_pos two_pos hDw) (Real.rpow_pos_of_pos hρ0 _))
      (Real.rpow_pos_of_pos hD0 _), ?_⟩
  intro D H K s γ e E₀ hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK' hG hTu hTb hs1 hsσ
    hν1 hν2 hγ hγγbar hdio he0 hE hEn hC1
  -- step `g1-standing` of `bpI:p2:g1`
  have hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ :=
    { toParams := hP
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
  -- `e < 1` and `ĉ_* e/(γ⁴ δ₀^{2a}) < 1`
  obtain ⟨he1, hsm⟩ := g1_error_small_aux (τ' := τ) (a := 2 * κ) hρ0 hγ hγγbar hD0 hcs.le hC1
  -- the initial state: row sums become operator norms, (I9) becomes `ν ≤ ν(s)`
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have h0 : (isoScheme n H D ωstar E₀ σω ν).Adm ρ μ e ![σK - μ, σB - μ, σT - μ, 0] (K, s) := by
    refine isoScheme_adm_iff.2 ⟨?_, ?_⟩
    · exact
        { r_pos := hρ0
          β_pos := hμ
          ε_nonneg := he0
          ε_le_one := he1.le
          holo := hK
          primary := hKp
          real := hKr
          ball_sub := hball
          deriv_le := hDK'
          gram := fun θ hθ =>
            ⟨(hG θ hθ).1, norm_le_of_rowSum_le_of_nonempty (m := Fin n) (hG θ hθ).2⟩
          error_le := hE
          s_gt := hs1
          twist := ⟨hTu, norm_le_of_rowSum_le_of_nonempty hTb⟩
          energy_le := hEn }
    · show ν - 0 ≤ rayMargin σω ωstar s
      rw [sub_zero]
      exact margin_of_le hν1 hν2
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    iso_g1_core (γb := γbar) hC hS hγγbar hρinf hρinfρ hμ h0 hsm.le
  exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans_eq (g1_closeness_eq (τ' := τ) hρ0 hγ hD0),
    h11.trans_eq (g1_closeness_eq (τ' := τ) hρ0 hγ hD0)⟩

/-- Blueprint `bpI:p2s:g1-instances`, the headline: Rüssmann's data `(τ, cohConstR n τ)`. Binders
and body: those of `KAM.Iso.Apost.g1_explicit`, verbatim; the SO certificate checker can use it in place
of `g1_explicit` by replacing the two rational mirrors of `checkSmallness`. -/
theorem g1_sharp {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ)
    {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ γbar σω ν : ℝ}
    (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT)
    (hμ : 0 < μ) (hγbar : 0 < γbar) (hσω : 1 < σω) (hν : 0 < ν)
    (ωstar : Fin n → ℝ) (hωstar : ωstar ≠ 0) :
    0 < sharpIsoC1 n τ (cohConstR n τ) M σK σB σT γbar μ ν τ ρ ρinf ∧
      0 < sharpIsoC2 n τ (cohConstR n τ) M σK σB σT γbar τ ρ ρinf ∧
      0 < sharpIsoC3 n τ (cohConstR n τ) M σK σB σT γbar τ ρ ρinf ∧
      KAM.Iso.Charts.IG1Body n τ ρ ρinf M σK σB σT μ γbar σω ν ωstar
        (sharpIsoC1 n τ (cohConstR n τ) M σK σB σT γbar μ ν τ ρ ρinf)
        (sharpIsoC2 n τ (cohConstR n τ) M σK σB σT γbar τ ρ ρinf)
        (sharpIsoC3 n τ (cohConstR n τ) M σK σB σT γbar τ ρ ρinf) := by
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact KAM.Iso.Sharp.g1_gen hn hτ (cohData_russmann (n := n) (by linarith)) hρinf hρinfρ hM hσK
    hσB hσT hμ hγbar hσω hν ωstar hωstar

/-- `bpI:p2s:g1-instances`: Parseval's data `(τ + n/2, cohConstP n τ)`. -/
theorem g1_sharp_parseval {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ)
    {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ γbar σω ν : ℝ}
    (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT)
    (hμ : 0 < μ) (hγbar : 0 < γbar) (hσω : 1 < σω) (hν : 0 < ν)
    (ωstar : Fin n → ℝ) (hωstar : ωstar ≠ 0) :
    0 < sharpIsoC1 n (τ + (n : ℝ) / 2) (cohConstP n τ) M σK σB σT γbar μ ν τ ρ ρinf ∧
      0 < sharpIsoC2 n (τ + (n : ℝ) / 2) (cohConstP n τ) M σK σB σT γbar τ ρ ρinf ∧
      0 < sharpIsoC3 n (τ + (n : ℝ) / 2) (cohConstP n τ) M σK σB σT γbar τ ρ ρinf ∧
      KAM.Iso.Charts.IG1Body n τ ρ ρinf M σK σB σT μ γbar σω ν ωstar
        (sharpIsoC1 n (τ + (n : ℝ) / 2) (cohConstP n τ) M σK σB σT γbar μ ν τ ρ ρinf)
        (sharpIsoC2 n (τ + (n : ℝ) / 2) (cohConstP n τ) M σK σB σT γbar τ ρ ρinf)
        (sharpIsoC3 n (τ + (n : ℝ) / 2) (cohConstP n τ) M σK σB σT γbar τ ρ ρinf) := by
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact KAM.Iso.Sharp.g1_gen hn hτ (cohData_parseval (by omega) (by linarith) (by linarith))
    hρinf hρinfρ hM hσK hσB hσT hμ hγbar hσω hν ωstar hωstar

/-- `bpI:p2s:g1-instances`: the crude data `(τ + n, cohConst n τ)`. -/
theorem g1_sharp_crude {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ)
    {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ γbar σω ν : ℝ}
    (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT)
    (hμ : 0 < μ) (hγbar : 0 < γbar) (hσω : 1 < σω) (hν : 0 < ν)
    (ωstar : Fin n → ℝ) (hωstar : ωstar ≠ 0) :
    0 < sharpIsoC1 n (τ + n) (cohConst n τ) M σK σB σT γbar μ ν τ ρ ρinf ∧
      0 < sharpIsoC2 n (τ + n) (cohConst n τ) M σK σB σT γbar τ ρ ρinf ∧
      0 < sharpIsoC3 n (τ + n) (cohConst n τ) M σK σB σT γbar τ ρ ρinf ∧
      KAM.Iso.Charts.IG1Body n τ ρ ρinf M σK σB σT μ γbar σω ν ωstar
        (sharpIsoC1 n (τ + n) (cohConst n τ) M σK σB σT γbar μ ν τ ρ ρinf)
        (sharpIsoC2 n (τ + n) (cohConst n τ) M σK σB σT γbar τ ρ ρinf)
        (sharpIsoC3 n (τ + n) (cohConst n τ) M σK σB σT γbar τ ρ ρinf) := by
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact KAM.Iso.Sharp.g1_gen hn hτ (cohData_crude (by omega) (by linarith)) hρinf hρinfρ hM hσK
    hσB hσT hμ hγbar hσω hν ωstar hωstar

end KAM.Iso.Sharp

end
