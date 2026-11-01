/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteBE.Step
public import KAM.Iso.Sharp2.RouteB.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The run and the theorem of the isoenergetic route B, with a separate gradient bound

`RunHypE.isNewton` and `RunHypE.core` are `RunHypI.isNewton` (`KAM/Iso/Sharp2/RouteB/Run.lean`) and
`RunHypI.core` (`KAM/Iso/Sharp2/RouteB/Core.lean`) at `RunHypE`. The iterates, `iterI_spec` and the
limit lemmas do not depend on the run record and are reused.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology MeasureTheory

namespace KAM.Iso.Sharp2.RouteBE

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB KAM.Iso.Linear KAM.Iso.Apost
  KAM.Iso.Sharp2.RouteB KAM.Iso.Sharp
open KAM.Iso.Sharp2.ModStepB (newK)

variable {n : ℕ} {N : NumB n} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ωstar : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {τ M Mh1 E₀ σω ν γ σT μm Xi ς0 : ℝ} {K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- (N1), (N2) for the isoenergetic scheme of route B. -/
theorem RunHypE.isNewton (R : RunHypE τ M Mh1 N 𝔅 h ωstar Ω σω ν γ σT μm K0 ς0) :
    (schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0).IsNewton N.τ γ (bite0R N.a N.ρ N.ρinf) (stageC N)
      (capB N σT μm ν) where
  regular := by
    intro r β w m x hx
    rcases x with ⟨s, b, K, ς, ςp⟩
    cases b
    · exact hx
    · exact ⟨hx.μ_nonneg, hx.holo, hx.primary, hx.real⟩
  step := by
    intro r β w δ m x hx hδ hδm h3 hcond hβ hcap
    rcases x with ⟨s, b, K, ς, ςp⟩
    have hnn := stageC_nonneg R.wf δ
    have hX0 : 0 ≤ w := by
      cases b
      · exact hx.1
      · exact hx.μ_nonneg
    have hg : 0 < γ * δ ^ N.τ := mul_pos R.γ_pos (Real.rpow_pos_of_pos hδ _)
    have hg1 : 0 < γ * δ ^ (N.τ + 1) := mul_pos R.γ_pos (Real.rpow_pos_of_pos hδ _)
    by_cases hm : b = true ∧ r = N.r s ∧ δ = N.δ s
    · obtain ⟨rfl, rfl, rfl⟩ := hm
      have hG : GoodI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s (N.r s) β w m K ς ςp := hx
      rw [stageC_sched R.wf] at hcond hβ hcap ⊢
      obtain ⟨hG', hcl, hpar⟩ := R.good_step hG hcond hβ hcap
      have hstep : (schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0).step (N.r s) (N.δ s)
          (s, true, K, ς, ςp) = (s + 1, true, newK h K (ς • ωstar) E₀ (N.r s - 2 * N.δ s),
            isoNewS h K ωstar E₀ ς, ς) := by
        simp [schemeIB]
      rw [hstep]
      exact ⟨hG', hcl, hpar⟩
    · have hstep : (schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0).step r δ (s, b, K, ς, ςp) =
          (s + 1, false, K, ς, ςp) := by
        simp only [schemeIB]
        split_ifs
        rfl
      rw [hstep]
      have hreg : DifferentiableOn ℂ K (complexStrip n r) ∧ IsPrimaryOnStrip K r ∧
          IsRealOnReals K := by
        cases b
        · exact hx.2
        · exact ⟨hx.holo, hx.primary, hx.real⟩
      refine ⟨junk_mono (by linarith) (by have := hnn.1; positivity) hreg, fun θ _ => ?_, ?_⟩
      · show ‖K θ - K θ‖ ≤ _
        rw [sub_self, norm_zero]
        have := hnn.2.1
        positivity
      · show |ς * ‖ωstar‖ - ς * ‖ωstar‖| ≤ _
        rw [sub_self, abs_zero]
        exact mul_nonneg hnn.2.2.1 hX0

/-- Blueprint `bpI:p2s2:g1`, route B: the run from a flagged initial state. -/
theorem RunHypE.core (R : RunHypE τ M Mh1 N 𝔅 h ωstar Ω σω ν γ σT μm K0 ς0) {β0 Xi Xs : ℝ}
    {m₀ : Fin 7 → ℝ} (hOk : routeBOk N (capB N σT μm ν) m₀ β0 Xs) (hXi0 : 0 ≤ Xi) (hXi : Xi ≤ Xs)
    (h0 : GoodI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 0 N.ρ β0 (γ * N.δ0 ^ (N.τ + 1) * Xi) m₀ K0 ς0 ς0) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ), 1 < sinf ∧ sinf < σω ∧
      DifferentiableOn ℂ Kinf (complexStrip n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n N.ρinf, invarianceError h Kinf (sinf • ωstar) θ = 0) ∧
      (∀ θ ∈ complexStrip n N.ρinf, h (Kinf θ) = (E₀ : ℂ)) ∧
      (∀ θ ∈ complexStrip n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ N.sK) ∧
      (∀ θ ∈ complexStrip n N.ρinf, ‖Kinf θ - K0 θ‖ ≤ N.ballSum Xi) ∧
      ‖sinf • ωstar - ς0 • ωstar‖ ≤ N.freqSum Xi := by
  have hN := R.wf
  have hγ := R.γ_pos
  have hn : 0 < n := by have := hN.two_le; omega
  have hNw := R.isNewton (E₀ := E₀) (Xi := Xi)
  have hx₀ : (schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0).Adm N.ρ β0 (γ * N.δ0 ^ (N.τ + 1) * Xi) m₀
      ((0, true, K0, ς0, ς0) : StI n) := h0
  have hXe := engine_xS hN (Xi := Xi) hγ
  have hBe := engine_ball hN (Xi := Xi) hγ
  have hrw : ∀ s, stageC N (biteSR N.a N.ρ N.ρinf s) = N.stage s := fun s =>
    stageC_sched hN s
  have hy1 : 0 < 1 - N.ybar := by linarith [hN.ybar.2]
  obtain ⟨Kinf, -, hholo, hprim, hreal, hadm, hconv, hclose⟩ :=
    StageScheme.converge_ratio (S := schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0) (κ := N.τ) (γ := γ)
      (ρ := N.ρ) (ρinf := N.ρinf) (β₀ := β0) (μ₀ := γ * N.δ0 ^ (N.τ + 1) * Xi) (a := N.a)
      (ybar := N.ybar) (C := stageC N) (σ := capB N σT μm ν) (m₀ := m₀)
      (x₀ := ((0, true, K0, ς0, ς0) : StI n)) N.kp
      (N.stage N.kp) hNw hN.a_gt hN.ybar.1 hN.ybar.2 hγ hN.ρinf_pos hN.ρinf_lt hx₀
      (fun δ _ hδk => by
        rw [stageC_tail hN hδk]
        exact ⟨le_rfl, fun X hX => hX, le_rfl, le_rfl, fun i => le_rfl⟩)
      (fun s hs => by
        rw [hXe, hrw]
        exact cond_run hN hOk hXi0 hXi (xS_nonneg hN hXi0 s) le_rfl)
      (by
        rw [hXe]
        refine le_trans ?_ hOk.J2
        exact mul_le_mul_of_nonneg_left (xS_mono hN hXi0 hXi _)
          (mul_nonneg (Real.rpow_nonneg hN.a_pos.le _) (Qs_nonneg hN _)))
      (fun i => by
        rw [hXe]
        refine le_trans ?_ (hOk.J3 i)
        have hw : ∀ s, 0 ≤ N.rate s i * N.wt s i := fun s => by
          have := (stageC_nonneg hN (N.δ s)).2.2.2 i
          rwa [stageC_sched hN] at this
        refine add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun s _ => ?_)) ?_
        · rw [hrw]
          exact mul_le_mul_of_nonneg_left (xS_mono hN hXi0 hXi s) (hw s)
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (xS_mono hN hXi0 hXi _) (hw _)) hy1.le)
      (fun δ _ _ => by
        obtain ⟨h1, h2, -, h4⟩ := stageC_nonneg hN δ
        exact ⟨h1, h2, h4⟩)
      (fun X hX0 hX => by
        rw [hXe] at hX
        exact cond_run hN hOk hXi0 hXi (s := N.kp) hX0 hX)
      (by rw [hBe]; exact (ballSum_mono hN hXi0 hXi).trans_lt hOk.J4)
  -- the iterates
  set x : ℕ → StI n := iterI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 with hx
  set Ks : ℕ → (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) := fun s => (x s).2.2.1 with hKs
  set ss : ℕ → ℝ := fun s => (x s).2.2.2.1 with hss
  have hgood : ∀ s, ∃ β w m, GoodI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s (N.r s) β w m (Ks s) (ss s)
      (x s).2.2.2.2 ∧ ∀ i, m i ≤ capB N σT μm ν i := by
    intro s
    obtain ⟨r, β, w, m, hA, -, hm⟩ := hadm s
    have hA' : (schemeIB N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0).Adm r β w m (x s) := hA
    obtain ⟨h1, h2, -⟩ := iterI_spec (N := N) (𝔅 := 𝔅) (h := h) (ωstar := ωstar) (E₀ := E₀)
      (σω := σω) (ν := ν) (γ := γ) (Xi := Xi) (K0 := K0) (ς0 := ς0) s
    have hG : GoodI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s r β w m (Ks s) (ss s) (x s).2.2.2.2 := by
      simp only [schemeIB, hx, h2, ↓reduceIte, h1] at hA'
      exact hA'
    have hr := hG.r_eq
    subst hr
    exact ⟨β, w, m, hG, hm⟩
  have hsub : ∀ s, complexStrip n N.ρinf ⊆ complexStrip n (N.r s - N.δ s) := fun s =>
    Triangular.strip_mono (by
      have := hN.r_succ s; have := hN.r_gt (s + 1); have := hN.δ_pos s; linarith)
  have hsubr : ∀ s, complexStrip n N.ρinf ⊆ complexStrip n (N.r s) := fun s =>
    Triangular.strip_mono (hN.r_gt s).le
  -- the frequency
  have hωpos : 0 < ‖ωstar‖ := norm_pos_iff.2 R.std.ωstar_ne
  set d : ℕ → ℝ := fun s => (stepConstsB (N.inp s)).Cnu * (N.γb * N.δ s ^ (N.τ + 1)) *
    N.xS Xi s with hd
  have hinc : ∀ s, |ss (s + 1) * ‖ωstar‖ - ss s * ‖ωstar‖| ≤ d s := by
    intro s
    obtain ⟨β, w, m, hG, -⟩ := hgood (s + 1)
    obtain ⟨-, -, hp⟩ := iterI_spec (N := N) (𝔅 := 𝔅) (h := h) (ωstar := ωstar) (E₀ := E₀)
      (σω := σω) (ν := ν) (γ := γ) (Xi := Xi) (K0 := K0) (ς0 := ς0) s
    have h1 := hG.incr s rfl
    have hp' : (x (s + 1)).2.2.2.2 = ss s := hp
    rw [hp'] at h1
    refine h1.trans ?_
    have hx0 := xS_nonneg hN hXi0 s
    have hpw := Real.rpow_nonneg (hN.δ_pos s).le (N.τ + 1)
    have hC := Cnu_nonneg hN s
    calc _ ≤ (stepConstsB (N.inp s)).Cnu * (N.γb * N.δ s ^ (N.τ + 1) * N.xS Xi s) := by
          gcongr
          exact R.γ_le
      _ = _ := by simp only [hd]; ring
  have htl : ∀ s, N.kp ≤ s → d s ≤ d N.kp * N.ybar ^ (s - N.kp) := by
    intro s hs
    have hxt := xS_tail hN hOk hXi0 hXi s hs
    have hC : (stepConstsB (N.inp s)).Cnu = (stepConstsB (N.inp N.kp)).Cnu := by
      rw [hN.inp_tail hs]
    have hδ : N.δ s ^ (N.τ + 1) ≤ N.δ N.kp ^ (N.τ + 1) :=
      Real.rpow_le_rpow (hN.δ_pos s).le (hN.δ_anti hs) (by linarith [hN.τ_pos])
    have hc0 : 0 ≤ (stepConstsB (N.inp N.kp)).Cnu * (N.γb * N.δ N.kp ^ (N.τ + 1)) :=
      mul_nonneg (Cnu_nonneg hN _) (mul_nonneg hN.γb.le (Real.rpow_nonneg (hN.δ_pos _).le _))
    have hx0 := xS_nonneg hN hXi0 s
    have hCn := Cnu_nonneg hN N.kp
    have hγb := hN.γb.le
    simp only [hd]
    rw [hC]
    calc _ ≤ (stepConstsB (N.inp N.kp)).Cnu * (N.γb * N.δ N.kp ^ (N.τ + 1)) * N.xS Xi s := by
          gcongr
      _ ≤ (stepConstsB (N.inp N.kp)).Cnu * (N.γb * N.δ N.kp ^ (N.τ + 1)) *
          (N.xS Xi N.kp * N.ybar ^ (s - N.kp)) := mul_le_mul_of_nonneg_left hxt hc0
      _ = _ := by ring
  obtain ⟨p, hpt, hpb⟩ := exists_limit_of_incr (p := fun s => ss s * ‖ωstar‖) hN.ybar.2 hinc htl
  have hs : Tendsto ss atTop (𝓝 (p / ‖ωstar‖)) := by
    refine (hpt.div_const ‖ωstar‖).congr fun j => ?_
    exact mul_div_cancel_right₀ _ hωpos.ne'
  have hmj : ∀ j, ν / 2 ≤ rayMargin σω ωstar (ss j) := fun j => by
    obtain ⟨β, w, m, hG, hm⟩ := hgood j
    have h1 := hG.ray
    have h2 : m 6 ≤ ν / 2 := hm 6
    linarith
  have hν := R.std.ν_pos
  have hmarg : ν / 2 ≤ rayMargin σω ωstar (p / ‖ωstar‖) :=
    ge_of_tendsto ((continuous_rayMargin.tendsto _).comp hs) (Eventually.of_forall hmj)
  have hpos : 0 < rayMargin σω ωstar (p / ‖ωstar‖) := by linarith
  have hmin : 0 < min (p / ‖ωstar‖ - 1) (σω - p / ‖ωstar‖) := by
    by_contra hneg
    exact absurd (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) (norm_nonneg ωstar))
      (not_le.2 hpos)
  have hs1 : 1 < p / ‖ωstar‖ := by linarith [(lt_min_iff.1 hmin).1]
  have hs2 : p / ‖ωstar‖ < σω := by linarith [(lt_min_iff.1 hmin).2]
  have hsclose : ‖(p / ‖ωstar‖) • ωstar - ς0 • ωstar‖ ≤ N.freqSum Xi := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have e1 : |p / ‖ωstar‖ - ς0| * ‖ωstar‖ = |p - ς0 * ‖ωstar‖| := by
      rw [← abs_of_pos hωpos, ← abs_mul, abs_of_pos hωpos, sub_mul,
        div_mul_cancel₀ _ hωpos.ne']
    rw [e1]
    exact hpb
  -- the errors along the run
  set ε : ℕ → ℝ := fun s => sCE (N.inp s) * (γ * N.δ s ^ (N.τ + 1) * N.xS Xi s) with hε
  have hE : ∀ s, ∀ θ ∈ complexStrip n N.ρinf,
      ‖invarianceError h (Ks s) (ss s • ωstar) θ‖ ≤ ε s := by
    intro s θ hθ
    obtain ⟨β, w, m, hG, hm⟩ := hgood s
    have hw0 := hG.μ_nonneg
    have hX : w / (γ * N.δ s ^ (N.τ + 1)) ≤ N.xS Xi s := by
      rw [div_le_iff₀ (R.gd1_pos s)]; linarith [hG.μ_le]
    obtain ⟨c', L⟩ := R.loc hG (cond_run hN hOk hXi0 hXi (div_nonneg hw0 (R.gd1_pos s).le) hX) hm
    have h1 := L.E_le (R.setting hG.ς_gt).toStanding θ (hsub s hθ)
    rw [R.mu_eq s] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hG.μ_le (nn_sCE (hN.inp_ok s)))
  have hεt : Tendsto ε atTop (𝓝 0) :=
    tendsto_weighted_zero hN hγ hOk hXi0 hXi (fun s => nn_sCE (hN.inp_ok s))
      fun s hs => by rw [hN.inp_tail hs]
  -- the derivatives
  have hKsd : ∀ s, DifferentiableOn ℂ (Ks s) (complexStrip n N.ρinf) := fun s => by
    obtain ⟨β, w, m, hG, -⟩ := hgood s
    exact hG.holo.mono (hsubr s)
  have hconv' : TendstoUniformlyOn Ks Kinf atTop (complexStrip n N.ρinf) := hconv
  have hclose' : ∀ θ ∈ complexStrip n N.ρinf, ‖Kinf θ - K0 θ‖ ≤ N.ballSum Xi := fun θ hθ => by
    have := hclose θ hθ
    rwa [hBe] at this
  have hρ0 : complexStrip n N.ρinf ⊆ complexStrip n N.ρ :=
    Triangular.strip_mono hN.ρinf_lt.le
  have hbs : N.ballSum Xi < β0 := (ballSum_mono hN hXi0 hXi).trans_lt hOk.J4
  have hmarg' : ∀ θ ∈ complexStrip n N.ρinf, Metric.ball (Kinf θ) (β0 - N.ballSum Xi) ⊆ 𝔅 :=
    fun θ hθ => PerturbationAux.ball_subset_of_close (h0.ball θ (hρ0 hθ)) (hclose' θ hθ)
  have hKD : ∀ θ ∈ complexStrip n N.ρinf, Kinf θ ∈ 𝔅 := fun θ hθ =>
    hmarg' θ hθ (Metric.mem_ball_self (by linarith))
  have hXd : DifferentiableOn ℂ (hamiltonianVectorFieldℂ h) 𝔅 :=
    differentiableOn_ham (R.std.setting (le_refl 1)).toStanding
  have hinv : ∀ θ ∈ complexStrip n N.ρinf,
      invarianceError h Kinf ((p / ‖ωstar‖) • ωstar) θ = 0 := fun θ hθ =>
    lim_invariance_moving (Ks := Ks) (ss := ss) (ε := ε)
      ((hXd.differentiableAt (R.std.isOpen.mem_nhds (hKD θ hθ))).continuousAt)
      (hconv'.tendsto_at hθ) (tendsto_fderiv_of_uniform hn hKsd hholo hconv' hθ) hs
      (fun j => hE j θ hθ) hεt
  -- the energy
  have hen : ∀ j, ‖KAM.Iso.energyAverage h (Ks j) - (E₀ : ℂ)‖ ≤
      1 * (γ * N.δ j ^ (N.τ + 1) * N.xS Xi j) := fun j => by
    obtain ⟨β, w, m, hG, -⟩ := hgood j
    rw [one_mul]
    refine hG.ηω.trans ?_
    have hl : (N.inp j).lamW ≤ 1 := (hN.inp_ok j).lam.2.2.2
    calc (N.inp j).lamW * w ≤ 1 * w := mul_le_mul_of_nonneg_right hl hG.μ_nonneg
      _ = w := one_mul _
      _ ≤ _ := hG.μ_le
  have hEn : KAM.Iso.energyAverage h Kinf = (E₀ : ℂ) :=
    iso_energy_limit_B (M := M) hN.ρinf_pos R.std.M_pos.le R.std.isOpen R.std.holo
      (fun z hz => (R.std.bounds z hz).1) (by linarith : 0 < β0 - N.ballSum Xi) hmarg' hKsd hholo
      hconv' hen (tendsto_weighted_zero hN hγ hOk hXi0 hXi (C := fun _ => 1)
        (fun _ => zero_le_one) fun _ _ => rfl)
  have hcons := (energy_conservation (R.std.setting hs1.le) hN.ρinf_pos hholo hprim hreal hKD
    hinv).2.1 (E₀ : ℂ) hEn
  refine ⟨Kinf, p / ‖ωstar‖, hs1, hs2, hholo, hprim, hreal, hinv, hcons, fun θ hθ => ?_, hclose',
    hsclose⟩
  refine le_of_tendsto (tendsto_fderiv_of_uniform hn hKsd hholo hconv' hθ).norm
    (Eventually.of_forall fun s => ?_)
  obtain ⟨β, w, m, hG, hm⟩ := hgood s
  rw [← norm_colMat]
  exact (hG.L θ (hsubr s hθ)).trans (hm 0)

end KAM.Iso.Sharp2.RouteBE

end
