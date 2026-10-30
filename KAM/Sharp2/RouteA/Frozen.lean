/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.G1
public import KAM.Sharp2.SmallDiv.Instances
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The default-data form of route A: the literal frozen body

Lemma `bp:p2s2:defaults` for route A (audit finding F3): `g1_v2A_frozen` concludes the literal
`KAM.Sharp.G1Body`, with no refined hypothesis. The refined data are derived from the frozen ones:

* `defaultInit`: `|Lᵀ| ≤ 2n(σ_K - μ)`, `|N| ≤ (σ_K - μ)(σ_B - μ)`, `|Nᵀ| ≤ 2n(σ_K - μ)(σ_B - μ)`,
  and `|T| ≤ H_T` on `T_{ρ-δ₀}` from `KAM.Sharp.torsion_bound`, which needs the smallness `TorsionOk`;
* `NumA.cert_classical`: the classical constants of `bp:p2s2sd:classical` are certificates on the whole
  Diophantine set, for `ρ ≤ 1`.

The torsion bound is proved only in the route-A branch of the minimum, so the case split on the branch
is made here, and `g1_branch_A` is the route-A branch.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology KAM.Sharp.Engine

namespace KAM.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Sharp

/-- A small-divisor constant stays one when it is increased. -/
theorem sdConst_mono {n : ℕ} {κ γ δ c c' : ℝ} {Ω : Set (Fin n → ℝ)} (hγ : 0 < γ)
    (h : SDConst n κ γ δ c Ω) (hcc : c ≤ c') : SDConst n κ γ δ c' Ω := by
  have hδ := h.delta_pos
  have hi : 0 ≤ γ⁻¹ * δ ^ (-κ) :=
    mul_nonneg (inv_pos.2 hγ).le (Real.rpow_nonneg hδ.le _)
  have key : ∀ {H : ℝ}, 0 ≤ H → c * γ⁻¹ * δ ^ (-κ) * H ≤ c' * γ⁻¹ * δ ^ (-κ) * H := fun {H} hH => by
    have := mul_le_mul_of_nonneg_right hcc (mul_nonneg hi hH)
    calc _ = c * (γ⁻¹ * δ ^ (-κ) * H) := by ring
      _ ≤ c' * (γ⁻¹ * δ ^ (-κ) * H) := this
      _ = _ := by ring
  refine ⟨h.c_pos.trans_le hcc, hδ, ?_, ?_, ?_⟩
  · intro ω hω r hr p g H hg hgp hgH hg0 θ hθ
    have hr0 : 0 < r := hδ.trans hr
    have hH : 0 ≤ H := (norm_nonneg _).trans (hgH _ (ofReal_mem_complexStrip hr0 0))
    exact (h.sol ω hω hr g H hg hgp hgH hg0 θ hθ).trans (key hH)
  · intro ω hω r hr p q u H hu hup hu0 hH θ hθ
    have hr0 : 0 < r := hδ.trans hr
    have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH _ (ofReal_mem_complexStrip hr0 0))
    exact (h.apriori ω hω hr u H hu hup hu0 hH θ hθ).trans (key hH0)
  · intro ω hω r hr p g H hg hgp hgH hg0 x
    have hr0 : 0 < r := hδ.trans_le hr
    have hH : 0 ≤ H := (norm_nonneg _).trans (hgH _ (ofReal_mem_complexStrip hr0 0))
    exact (h.real ω hω hr g H hg hgp hgH hg0 x).trans (key hH)

/-- `r_s ≤ ρ`. -/
theorem NumA.Wf.r_le {N : NumA} (hN : N.Wf) (s : ℕ) : N.r s ≤ N.ρ := by
  have hd : 0 < delta0 3 N.ρ N.ρinf := delta0_pos (by norm_num) hN.ρinf_lt
  have h1 : (2 : ℝ)⁻¹ ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : 0 ≤ 2 * 3 * delta0 3 N.ρ N.ρinf * (1 - (2 : ℝ)⁻¹ ^ s) :=
    mul_nonneg (by positivity) (by linarith)
  show N.ρ - 2 * 3 * delta0 3 N.ρ N.ρinf * (1 - (2 : ℝ)⁻¹ ^ s) ≤ N.ρ
  linarith

/-- The classical constants at the schedule are certificates on the Diophantine set. -/
theorem NumA.cert_classical {N : NumA} (hN : N.Wf) (hρ1 : N.ρ ≤ 1) {γ : ℝ} (hγ : 0 < γ)
    (hc : ∀ s < N.kp, N.c s = cohConstC N.n N.τ (N.δ s))
    (hcb : ∀ s < N.kp, N.cbar s = cohConstC N.n N.τ (N.r s))
    (ht : N.ctail = cohConstC N.n N.τ (N.δ N.kp)) :
    N.Cert γ {ω | IsDiophantine γ N.τ ω} where
  stage := fun s hs => by
    rw [hc s hs]
    exact sdConst_classical (by have := hN.two_le; omega) hN.τ_ge hγ (hN.δ_pos s) (hN.δ_le s)
  bar := fun s hs => by
    rw [hcb s hs]
    exact sdConst_classical (by have := hN.two_le; omega) hN.τ_ge hγ (hN.r_pos s)
      ((hN.r_le s).trans hρ1)
  tail := fun δ hδ hle => by
    rw [ht]
    have h1 := sdConst_classical (n := N.n) (by have := hN.two_le; omega) hN.τ_ge hγ hδ
      (hle.trans (hN.δ_le _))
    exact sdConst_mono hγ h1 (cohConstC_mono hN.τ_ge hδ.le hle)

/-- The default initial values. -/
def defaultInit (n : ℕ) (M σK σB μ : ℝ) : InitA :=
  ⟨2 * n * (σK - μ), (σK - μ) * (σB - μ), 2 * n * (σK - μ) * (σB - μ), hT n M σK σB⟩

/-- The smallness that gives the initial torsion bound `|T| ≤ H_T`. -/
def TorsionOk (N : NumA) (M σK σB Xs : ℝ) : Prop :=
  (cT1 N.n σK σB * (N.γb ^ 4 * N.δ 0 ^ (2 * (2 * N.τ) - 1)) +
    cT2 N.n N.τ (cohConstR N.n N.τ) M σK σB * (N.γb ^ 3 * N.δ 0 ^ (3 * N.τ - 1))) * Xs ≤ 1

/-- The initial torsion bound: at stage `0`, `e ≤ δ₀`, and `TorsionOk` gives `|T| ≤ H_T` on
`T_{ρ-δ₀}`, for any frequency `ω`. -/
theorem torsion_default {N : NumA} (hN : N.Wf) {M σK σB σT μ γ e Xs : ℝ} {ω : Fin N.n → ℝ}
    {𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))} {h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ}
    {K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)}
    (hS : Standing N.n N.τ M σK σB σT 𝔅 h ω γ)
    (hAd : KAM.Iso.Linear.AdmissibleNoTwist σK σB 𝔅 h ω N.ρ μ e K) (hγb : γ ≤ N.γb)
    (hc0 : (N.inp 0).Cond (e / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ)))))
    (hXs : e / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ))) ≤ Xs)
    (hTs : TorsionOk N M σK σB Xs) (hTn : 0 ≤ cT1 N.n σK σB)
    (hTn2 : 0 ≤ cT2 N.n N.τ (cohConstR N.n N.τ) M σK σB) :
    ∀ θ ∈ complexStrip N.n (N.ρ - N.δ 0), ‖torsion h K ω θ‖ ≤ hT N.n M σK σB := by
  intro θ hθ
  have hγ := hS.gamma_pos
  have hδ := hN.δ_pos 0
  have hε0 := hAd.ε_nonneg
  have hδD : N.δ 0 ≤ (N.inp 0).δ := hN.δ_le_dS 0
  obtain ⟨hεδ, -⟩ := hc0.facts (hN.pos 0) hγ hγb hδ hδD hε0
  have hr0 : N.δ 0 < N.ρ := by
    have h1 := hN.lam_δ_lt 0
    have h2 : N.r 0 = N.ρ := rSeq_zero
    rw [h2] at h1
    linarith
  have hb := torsion_bound (cohData_russmann (n := N.n) hN.τ_ge) hS hAd hδ (hN.δ_le 0) hr0 hεδ θ hθ
  obtain ⟨-, -, -, -, -, s6, s7, -⟩ := scales (ε := e) (κ := N.τ) hγ hδ
  set x := e / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ))) with hx
  have hx0 : 0 ≤ x := div_nonneg hε0 (by positivity)
  have hκ := hN.τ_ge
  have b4 := mul_le_mul (pow_mul_rpow_le (j := 2 * (2 * N.τ) - 1) 4 hγ hγb hδ le_rfl (by linarith))
    hXs hx0 (mul_nonneg (pow_nonneg hN.γb.le 4) (Real.rpow_nonneg hδ.le _))
  have b3 := mul_le_mul (pow_mul_rpow_le (j := 3 * N.τ - 1) 3 hγ hγb hδ le_rfl (by linarith))
    hXs hx0 (mul_nonneg (pow_nonneg hN.γb.le 3) (Real.rpow_nonneg hδ.le _))
  have e1 : cT1 N.n σK σB * e / N.δ 0 = cT1 N.n σK σB * (e / N.δ 0) := mul_div_assoc _ _ _
  have e2 : cT2 N.n N.τ (cohConstR N.n N.τ) M σK σB * e / (γ * N.δ 0 ^ (N.τ + 1)) =
      cT2 N.n N.τ (cohConstR N.n N.τ) M σK σB * (e / (γ * N.δ 0 ^ (N.τ + 1))) := mul_div_assoc _ _ _
  rw [e1, e2, s6, s7] at hb
  have h1 := mul_le_mul_of_nonneg_left b4 hTn
  have h2 := mul_le_mul_of_nonneg_left b3 hTn2
  unfold hT
  unfold TorsionOk at hTs
  nlinarith [hb, h1, h2, hTs]

variable {N : NumA}

/-- Lemma `bp:p2s2:defaults` and Corollary `bp:p2s2:frozen-form` for route A: the literal frozen body
`KAM.Sharp.G1Body`, with the default refined data. `hcert` is a statement on the numbers `N.c`,
`N.cbar`, `N.ctail` alone: `NumA.cert_classical` proves it for the classical constants. -/
theorem g1_v2A_frozen (hN : N.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar Xs : ℝ} (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT)
    (hμ : 0 < μ) (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2) (hM1 : N.M1 = M) (hM2 : N.M2 = M)
    (hOk : routeAOk N (N.capV (μ / 2)) (initV (defaultInit N.n M σK σB μ) σK σB σT μ) Xs)
    (hXpos : 0 < Xs) (hTs : TorsionOk N M σK σB Xs)
    (hcert : ∀ γ, 0 < γ → γ ≤ γbar → N.Cert γ {ω | IsDiophantine γ N.τ ω}) :
    0 < min (sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf) (c1A N Xs) ∧
      0 < max (sharpC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c2A N Xs) ∧
      G1Body N.n N.τ N.ρ N.ρinf M σK σB σT μ γbar
        (min (sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf) (c1A N Xs))
        (max (sharpC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c2A N Xs)) := by
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hlam : (0 : ℝ) < 3 := by norm_num
  have hD : 0 < delta0 3 N.ρ N.ρinf := delta0_pos hlam hN.ρinf_lt
  have hDp : 0 < delta0 3 N.ρ N.ρinf ^ (4 * N.τ) := Real.rpow_pos_of_pos hD _
  have hγb0 : 0 < γbar := hγbar ▸ hN.γb
  obtain ⟨hC1, hC2, hbody⟩ := g1_sharp (n := N.n) hN.two_le hτ hN.ρinf_pos hN.ρinf_lt hM hσK hσB hσT
    hμ hγb0
  have hc1 : 0 < c1A N Xs := div_pos (Real.rpow_pos_of_pos hρ0 _) (mul_pos hXpos hDp)
  refine ⟨lt_min hC1 hc1, lt_max_of_lt_left hC2, ?_⟩
  intro 𝔅 h K ω γ e hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hγ hγγbar
    hdio hE hsm
  have h00 : (0 : Fin N.n → ℂ) ∈ complexStrip N.n N.ρ := fun i => by simpa using hρ0
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hp2 : 0 ≤ e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
    div_nonneg he0 (mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hρ0 _)).le
  have hmono : ∀ {c c' : ℝ}, c ≤ c' → c * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) ≤
      c' * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := fun {c c'} hc => by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hc hp2
  by_cases hcase : sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf ≤ c1A N Xs
  · rw [min_eq_left hcase] at hsm
    obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := hbody 𝔅 h K ω γ e hopen htransl hholo hper hreal hbd
      hK hKp hKr hball hDK hG hTu hTb hγ hγγbar hdio hE hsm
    exact ⟨Kinf, h1, h2, h3, h4, h5, h6, fun θ hθ => (h7 θ hθ).trans (hmono (le_max_left _ _))⟩
  · rw [min_eq_right (not_le.1 hcase).le] at hsm
    have hsm' : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) < Xs := by
      rw [show 2 * (2 * N.τ) = 4 * N.τ by ring]
      have hρp : 0 < N.ρ ^ (4 * N.τ) := Real.rpow_pos_of_pos hρ0 _
      have e1 : c1A N Xs * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) =
          (e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (4 * N.τ))) / Xs := by
        unfold c1A
        field_simp
      rw [e1, div_lt_one hXpos] at hsm
      exact hsm
    have hSv : Standing N.n N.τ M σK σB σT 𝔅 h ω γ :=
      { toParams := ⟨hN.two_le, hτ, hM, hσK, hσB, hσT⟩
        isOpen := hopen
        transl_mem := htransl
        holo := hholo
        periodic := hper
        real := hreal
        bounds := fun z hz => ⟨(hbd z hz).2.1, (hbd z hz).2.2.1, (hbd z hz).2.2.2⟩
        gamma_pos := hγ
        dio := hdio }
    have hγb : γ ≤ N.γb := hγγbar.trans_eq hγbar
    have hδ0 : N.δ 0 = delta0 3 N.ρ N.ρinf := deltaSeq_zero
    have hX0 : e / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ))) ≤ Xs := by rw [hδ0]; exact hsm'.le
    have hx0 : 0 ≤ e / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ))) :=
      div_nonneg he0 (mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos (hN.δ_pos 0) _)).le
    have hc0 : (N.inp 0).Cond Xs := by
      rcases Nat.eq_zero_or_pos N.kp with hk | hk
      · have := hOk.J1t
        rwa [hk] at this
      · exact hOk.J1 0 hk
    have hc0' := hc0.down (hN.pos 0) hX0
    obtain ⟨hεδ, -⟩ := hc0'.facts (hN.pos 0) hγ hγb (hN.δ_pos 0) (hN.δ_le_dS 0) he0
    have hGn : ∀ θ ∈ complexStrip N.n N.ρ, ‖(gramMatrix K θ)⁻¹‖ ≤ σB - μ := fun θ hθ =>
      norm_le_of_rowSum_le hN.two_le (hG θ hθ).2
    have hAd : KAM.Iso.Linear.AdmissibleNoTwist σK σB 𝔅 h ω N.ρ μ e K :=
      ⟨hρ0, hμ, he0, hεδ.trans (hN.δ_le 0), hK, hKp, hKr, hball,
        fun θ hθ => (hDK θ hθ).trans (by linarith),
        fun θ hθ => ⟨(hG θ hθ).1, (hGn θ hθ).trans (by linarith)⟩, hE⟩
    have hK𝔅 : ∀ θ ∈ complexStrip N.n N.ρ, K θ ∈ 𝔅 := fun θ hθ =>
      hball θ hθ (Metric.mem_ball_self hμ)
    have hfb : ∀ θ ∈ complexStrip N.n N.ρ, _ := fun θ hθ =>
      frame_bounds hSv (hK𝔅 θ hθ) (hDK θ hθ) (hG θ hθ).1 (hGn θ hθ) ω
    have hT1 : 0 ≤ cT1 N.n σK σB := by unfold cT1; positivity
    have hT2 : 0 ≤ cT2 N.n N.τ (cohConstR N.n N.τ) M σK σB := by
      have hcR := (cohData_russmann (n := N.n) hN.τ_ge).cR_pos
      unfold cT2 wT cOm
      positivity
    have hRef : RefHypA N (defaultInit N.n M σK σB μ) 𝔅 h K ω :=
      { dX := fun z hz => hM1 ▸ (hbd z hz).2.2.1
        d2X := fun z hz => hM2 ▸ (hbd z hz).2.2.2
        tangentT := fun θ hθ => (hfb θ hθ).2.1
        normal := fun θ hθ => (hfb θ hθ).2.2.1
        normalT := fun θ hθ => (hfb θ hθ).2.2.2.2.1
        tors := torsion_default hN hSv hAd hγb hc0' hX0 hTs hT1 hT2 }
    obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := g1_branch_A hN hfix hΘ hτ hM hμ hγbar hsK hOk hXpos
      hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hRef hdio
      (hcert γ hγ hγγbar) hγ hγγbar hdio he0 hE hsm'
    exact ⟨Kinf, h1, h2, h3, h4, h5, h6, fun θ hθ => (h7 θ hθ).trans (hmono (le_max_right _ _))⟩

end KAM.Sharp2.RouteA

end
