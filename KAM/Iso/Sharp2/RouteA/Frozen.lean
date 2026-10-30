/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteA.G1
public import KAM.Sharp2.RouteA.Frozen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The default-data form of the isoenergetic route A: the literal frozen body

`iso_g1_v2A_frozen` concludes the literal `KAM.Iso.Charts.IG1Body`, with no refined hypothesis: the
refined data come from (I1)–(I13) as in `KAM.Sharp2.RouteA.g1_v2A_frozen`, the certificates are on
the
whole Diophantine set, which contains the ray.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology KAM.Sharp.Engine

namespace KAM.Iso.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp

variable {N : NumA}

/-- Corollary `bpI:p2s2:frozen`, route A, with the default refined data: literally `IG1Body`, so
every
sub-check of a certificate of I-G1 except the smallness transfers. -/
theorem iso_g1_v2A_frozen (hN : N.Wf) (hiso : N.iso = true) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar σω ν Xs : ℝ} (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT)
    (hμ : 0 < μ) (hσω : 1 < σω) (hν : 0 < ν) (ωstar : Fin N.n → ℝ) (hωstar : ωstar ≠ 0)
    (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2) (hΘ : N.Θ = σω * ‖ωstar‖)
    (hHY : N.HY = M * N.sN) (hM1 : N.M1 = M) (hM2 : N.M2 = M) (hMh2 : N.Mh2 = M)
    (hOk : routeAOkI N (capI N (μ / 2) (ν / 2)) (initI (defaultInit N.n M σK σB μ) σK σB σT μ) Xs)
    (hXpos : 0 < Xs) (hTs : TorsionOk N M σK σB Xs)
    (hcert : ∀ γ, 0 < γ → γ ≤ γbar → N.Cert γ {ω | IsDiophantine γ N.τ ω}) :
    0 < min (sharpIsoC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ ν N.τ N.ρ N.ρinf) (c1A N Xs) ∧
      0 < max (sharpIsoC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c2I N Xs) ∧
      0 < max (sharpIsoC3 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c3I N Xs) ∧
      KAM.Iso.Charts.IG1Body N.n N.τ N.ρ N.ρinf M σK σB σT μ γbar σω ν ωstar
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
  intro D H K s γ e E₀ hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hs1 hsσ
    hν1 hν2 hγ hγγbar hdio he0 hE hEn hsm
  have hp2 : 0 ≤ e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
    div_nonneg he0 (mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hρ0 _)).le
  have hmono : ∀ {c c' : ℝ}, c ≤ c' → c * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) ≤
      c' * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := fun {c c'} hc => by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hc hp2
  by_cases hcase : sharpIsoC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ ν N.τ N.ρ N.ρinf ≤
      c1A N Xs
  · rw [min_eq_left hcase] at hsm
    obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hbody D H K s γ e E₀ hopen
      htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hs1 hsσ hν1 hν2 hγ hγγbar hdio
      he0 hE hEn hsm
    exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      fun θ hθ => (h10 θ hθ).trans (hmono (le_max_left _ _)), h11.trans (hmono (le_max_left _ _))⟩
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
    have hIS : IsoStanding N.n N.τ M σK σB σT σω ν ωstar D H γ :=
      { toParams := ⟨hN.two_le, hτ, hM, hσK, hσB, hσT⟩
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
    have hSv := (hIS.setting hs1.le).toStanding
    have hγb : γ ≤ N.γb := hγγbar.trans_eq hγbar
    have hδ0 : N.δ 0 = delta0 3 N.ρ N.ρinf := deltaSeq_zero
    have hX0 : e / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ))) ≤ Xs := by rw [hδ0]; exact hsm'.le
    have hc0 : (N.inp 0).Cond Xs := by
      rcases Nat.eq_zero_or_pos N.kp with hk | hk
      · have := hOk.J1t
        rwa [hk] at this
      · exact hOk.J1 0 hk
    have hc0' := hc0.down (hN.pos 0) hX0
    obtain ⟨hεδ, -⟩ := hc0'.facts (hN.pos 0) hγ hγb (hN.δ_pos 0) (hN.δ_le_dS 0) he0
    have : Nonempty (Fin N.n) := ⟨⟨0, by have := hN.two_le; omega⟩⟩
    have hGn : ∀ θ ∈ complexStrip N.n N.ρ, ‖(gramMatrix K θ)⁻¹‖ ≤ σB - μ := fun θ hθ =>
      norm_le_of_rowSum_le_of_nonempty (m := Fin N.n) (hG θ hθ).2
    have hAd : AdmissibleNoTwist σK σB D H (s • ωstar) N.ρ μ e K :=
      ⟨hρ0, hμ, he0, hεδ.trans (hN.δ_le 0), hK, hKp, hKr, hball,
        fun θ hθ => (hDK θ hθ).trans (by linarith),
        fun θ hθ => ⟨(hG θ hθ).1, (hGn θ hθ).trans (by linarith)⟩, hE⟩
    have hKD : ∀ θ ∈ complexStrip N.n N.ρ, K θ ∈ D := fun θ hθ =>
      hball θ hθ (Metric.mem_ball_self hμ)
    have hfb : ∀ θ ∈ complexStrip N.n N.ρ, _ := fun θ hθ =>
      frame_bounds hSv (hKD θ hθ) (hDK θ hθ) (hG θ hθ).1 (hGn θ hθ) (s • ωstar)
    have hT1 : 0 ≤ cT1 N.n σK σB := by unfold cT1; positivity
    have hT2 : 0 ≤ cT2 N.n N.τ (cohConstR N.n N.τ) M σK σB := by
      have hcR := (cohData_russmann (n := N.n) hN.τ_ge).cR_pos
      unfold cT2 wT cOm
      positivity
    have hRef : RefHypIA N (defaultInit N.n M σK σB μ) M D H K (s • ωstar) :=
      { dX := fun z hz => hM1 ▸ (hbd z hz).2.2.1
        d2X := fun z hz => hM2 ▸ (hbd z hz).2.2.2.1
        dH := fun z hz => (hbd z hz).1
        d2H := fun z hz => hMh2 ▸ (hbd z hz).2.2.2.2
        tangentT := fun θ hθ => (hfb θ hθ).2.1
        normal := fun θ hθ => (hfb θ hθ).2.2.1
        normalT := fun θ hθ => (hfb θ hθ).2.2.2.2.1
        tors := torsion_default hN hSv hAd hγb hc0' hX0 hTs hT1 hT2 }
    obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := iso_g1_branch_A hN hiso hτ
        hM
      hμ hσω hν hωstar hγbar hsK hΘ hHY hOk hXpos hopen htransl hholo hper hreal hbd hK hKp hKr
          hball
      hDK hG hTu hTb hs1 hν1 hν2 hRef (fun s' hs' => isDiophantine_smul hdio hs')
      (hcert γ hγ hγγbar) hγ hγγbar hdio he0 hE hEn hsm'
    exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      fun θ hθ => (h10 θ hθ).trans (hmono (le_max_right _ _)), h11.trans (hmono (le_max_right _ _))⟩

/-- (J1)–(J3) pass to every smaller threshold. -/
theorem routeAOkI.mono (hN : N.Wf) {σ m₀ : Fin 9 → ℝ} {X Y : ℝ} (h : routeAOkI N σ m₀ Y)
    (h0 : 0 ≤ X) (hXY : X ≤ Y) : routeAOkI N σ m₀ X := by
  have hCE : ∀ s, 0 ≤ (stageI N s).CE := fun s => (hN.pos s).CE
  have hx : ∀ s, 0 ≤ xI N X s ∧ xI N X s ≤ xI N Y s := xA_mono hCE h0 hXY
  refine ⟨h0, fun s hs => (h.J1 s hs).down (hN.pos s) (hx s).2,
    h.J1t.down (hN.pos _) (hx _).2, ?_, fun i => ?_⟩
  · refine le_trans ?_ h.J2
    exact mul_le_mul_of_nonneg_left (hx _).2
      (mul_nonneg (Real.rpow_nonneg zero_le_two _) (hCE _))
  · refine le_trans (add_le_add le_rfl ?_) (h.J3 i)
    exact sumA_mono (fun s => rateI_nonneg (hN.pos s) i) (fun s => (hN.δ_pos s).le)
      (fun s => (hx s).2) _

/-- The literal `IG1Body` with no torsion smallness among the inputs: `routeAOkI` at `X⋆` and the
certificates suffice, at the threshold `torsionXs N M σK σB X⋆`. -/
theorem iso_g1_v2A_default (hN : N.Wf) (hiso : N.iso = true) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar σω ν Xs : ℝ} (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT)
    (hμ : 0 < μ) (hσω : 1 < σω) (hν : 0 < ν) (ωstar : Fin N.n → ℝ) (hωstar : ωstar ≠ 0)
    (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2) (hΘ : N.Θ = σω * ‖ωstar‖)
    (hHY : N.HY = M * N.sN) (hM1 : N.M1 = M) (hM2 : N.M2 = M) (hMh2 : N.Mh2 = M)
    (hOk : routeAOkI N (capI N (μ / 2) (ν / 2)) (initI (defaultInit N.n M σK σB μ) σK σB σT μ) Xs)
    (hXpos : 0 < Xs)
    (hcert : ∀ γ, 0 < γ → γ ≤ γbar → N.Cert γ {ω | IsDiophantine γ N.τ ω}) :
    0 < min (sharpIsoC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ ν N.τ N.ρ N.ρinf)
        (c1A N (torsionXs N M σK σB Xs)) ∧
      0 < max (sharpIsoC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf)
        (c2I N (torsionXs N M σK σB Xs)) ∧
      0 < max (sharpIsoC3 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf)
        (c3I N (torsionXs N M σK σB Xs)) ∧
      KAM.Iso.Charts.IG1Body N.n N.τ N.ρ N.ρinf M σK σB σT μ γbar σω ν ωstar
        (min (sharpIsoC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ ν N.τ N.ρ N.ρinf)
          (c1A N (torsionXs N M σK σB Xs)))
        (max (sharpIsoC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf)
          (c2I N (torsionXs N M σK σB Xs)))
        (max (sharpIsoC3 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf)
          (c3I N (torsionXs N M σK σB Xs))) := by
  obtain ⟨h1, h2, h3⟩ := torsionXs_spec hN hM hσK hσB hXpos
  exact iso_g1_v2A_frozen hN hiso hτ hM hσK hσB hσT hμ hσω hν ωstar hωstar hγbar hsK hΘ hHY hM1 hM2
    hMh2 (hOk.mono hN h1.le h2) h1 h3 hcert

end KAM.Iso.Sharp2.RouteA

end
