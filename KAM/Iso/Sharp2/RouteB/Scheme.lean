/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.ModStepB
public import KAM.Sharp2.RouteB.Scheme
public import KAM.Iso.Apost.TorsionDiff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The isoenergetic scheme of route B, and the bordered reference torsion

The isoenergetic counterpart of `KAM.Sharp2.RouteB.Scheme` (SHARP2-B6), with the bordered modified
step `modified_stepIB`.

* `StI`, `GoodI`, `schemeIB`: the states `(s, b, K, ς)`, with the frequency `ς ω*` on the ray.
  `GoodI` is `Good` at the frequency `ς ω*`, with the energy error `|⟨H ∘ K⟩ - E₀| ≤ λ_ω μ`, the ray
  margin `ν - m₆ ≤ ν(ς)`, and the drift of `Tab` in the two forms that the row sums of the bordered
  torsion need: `|⟨𝒯_ab(K)⟩ - ⟨𝒯_ab(K₀)⟩| + |ς ω* - ς₀ ω*| ≤ m₅`, `n |ς ω* - ς₀ ω*| ≤ m₅`.
* `RunHypI`: the fixed data of a run, with the reference data of the initial pair `(K₀, ς₀)`.
* `RunHypI.tors`: step `stepI:p2s2:st-t`: the local parts at the stage and at stage `0`
  (`|⟨T⟩ - ⟨𝒯_ab⟩| ≤ B_sup X ≤ b_F`, `n |⟨Y⟩ - ω| ≤ n g₁ X ≤ b_F`, `B^𝖳_loc X ≤ b_F`) and the drift
  give `|⟨𝖳⟩ - ⟨𝖳₀⟩| ≤ β_T`, so `|⟨𝖳⟩⁻¹| ≤ σ̂_T`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology MeasureTheory

namespace KAM.Iso.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB KAM.Iso.Linear KAM.Iso.Apost
open KAM.Iso.Sharp2.ModStepB (newK)

variable {n : ℕ}

/-- The states of the isoenergetic route B: stage, validity flag, torus, frequency scale. -/
abbrev StI (n : ℕ) := ℕ × Bool × (((Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) × ℝ)

/-- Admissibility of a flagged state at stage `s` (`bpI:p2s2:g1`). -/
structure GoodI (N : NumB n) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ωstar : Fin n → ℝ) (E₀ σω ν γ Xi : ℝ)
    (K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ς0 : ℝ) (s : ℕ) (r β μ : ℝ) (m : Fin 7 → ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ς : ℝ) : Prop where
  r_eq : r = N.r s
  μ_nonneg : 0 ≤ μ
  μ_le : μ ≤ γ * N.δ s ^ (N.τ + 1) * N.xS Xi s
  holo : DifferentiableOn ℂ K (complexStrip n r)
  primary : IsPrimaryOnStrip K r
  real : IsRealOnReals K
  ball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅
  β_pos : 0 < β
  L : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ m 0
  Lt : ∀ θ ∈ complexStrip n r, ‖(tangentMat K θ)ᵀ‖ ≤ m 1
  G : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ m 2
  Nm : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ m 3
  NmT : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ‖ ≤ m 4
  drift : ‖torsionABAverage h K - torsionABAverage h K0‖ + ‖ς • ωstar - ς0 • ωstar‖ ≤ m 5
  drift' : n * ‖ς • ωstar - ς0 • ωstar‖ ≤ m 5
  ς_gt : 1 < ς
  ray : ν - m 6 ≤ rayMargin σω ωstar ς
  ηL : ∀ θ ∈ complexStrip n r, ‖etaL h K (ς • ωstar) θ‖ ≤ (N.inp s).lam * μ
  ηN : ∀ θ ∈ complexStrip n r, ‖etaN h K (ς • ωstar) θ‖ ≤ γ * N.δ s ^ N.τ * μ
  ηω : ‖KAM.Iso.energyAverage h K - (E₀ : ℂ)‖ ≤ (N.inp s).lamW * μ
  E0 : s = 0 → ∀ θ ∈ complexStrip n r, ‖invarianceError h K (ς • ωstar) θ‖ ≤ N.ePer0 * μ

open Classical in
/-- The isoenergetic scheme of route B. -/
def schemeIB (N : NumB n) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ωstar : Fin n → ℝ) (E₀ σω ν γ Xi : ℝ)
    (K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ς0 : ℝ) : StageScheme n 7 (StI n) where
  tor := fun x => x.2.2.1
  par := fun x => x.2.2.2 * ‖ωstar‖
  Adm := fun r β μ m x => if x.2.1 then
      GoodI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 x.1 r β μ m x.2.2.1 x.2.2.2
    else Junk r μ x.2.2.1
  step := fun r δ x => if x.2.1 = true ∧ r = N.r x.1 ∧ δ = N.δ x.1 then
      (x.1 + 1, true, newK h x.2.2.1 (x.2.2.2 • ωstar) E₀ (r - 2 * δ),
        isoNewS h x.2.2.1 ωstar E₀ x.2.2.2)
    else (x.1 + 1, false, x.2.2)

/-- `bp:p2s2:torsion-ref` over any index type: Neumann against the initial average. -/
theorem inv_le_of_ref_bord {ι : Type*} [Fintype ι] [DecidableEq ι] {A A0 : Matrix ι ι ℂ} {m σ : ℝ}
    (hA0 : IsUnit A0.det) (hm : ‖A0⁻¹‖ ≤ m) (hm0 : 0 < m) (hmσ : m < σ)
    (hd : ‖A - A0‖ ≤ (σ - m) / (σ * m)) : IsUnit A.det ∧ ‖A⁻¹‖ ≤ σ := by
  have hσ : 0 < σ := hm0.trans hmσ
  have hq : (σ - m) / σ < 1 := by rw [div_lt_one hσ]; linarith
  have hsmall : ‖A0⁻¹‖ * ‖A - A0‖ ≤ (σ - m) / σ := by
    calc ‖A0⁻¹‖ * ‖A - A0‖ ≤ m * ((σ - m) / (σ * m)) :=
          mul_le_mul hm hd (norm_nonneg _) hm0.le
      _ = (σ - m) / σ := by field_simp
  obtain ⟨hu, hb, -⟩ := neumann_ratio ((Matrix.isUnit_iff_isUnit_det A0).2 hA0) hq hsmall
  rw [add_sub_cancel] at hu hb
  refine ⟨(Matrix.isUnit_iff_isUnit_det A).1 hu, hb.trans ?_⟩
  have h1 : 1 - (σ - m) / σ = m / σ := by field_simp; ring
  rw [h1, div_le_iff₀ (div_pos hm0 hσ)]
  calc ‖A0⁻¹‖ ≤ m := hm
    _ = σ * (m / σ) := by field_simp

/-- The fixed data of a run of the isoenergetic route B, with the reference data of `(K₀, ς₀)`. -/
structure RunHypI (τ M : ℝ) (N : NumB n) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ωstar : Fin n → ℝ) (Ω : Set (Fin n → ℝ))
    (E₀ σω ν γ σT μm : ℝ) (K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ς0 : ℝ) : Prop where
  wf : N.Wf
  iso : N.iso = true
  std : IsoStanding n τ M N.sK N.sB N.sT σω ν ωstar 𝔅 h γ
  hΘ : N.Θ = σω * ‖ωstar‖
  y0 : N.y0 = M * N.sN
  dX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N.M1
  d2X : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N.M2
  d2H : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 h z‖ ≤ N.Mh2
  comm : ∀ z ∈ 𝔅, ‖hamComm h z‖ ≤ N.cTh
  lip : ∀ z ∈ 𝔅, ∀ z' ∈ 𝔅, segment ℝ z z' ⊆ 𝔅 →
    ‖hamComm h z - hamComm h z'‖ ≤ N.cDTh * ‖z - z'‖
  γ_le : γ ≤ N.γb
  mem : ∀ s : ℝ, 1 ≤ s → s • ωstar ∈ Ω
  cert : N.Cert γ Ω
  A0 : IsUnit (KAM.Iso.extendedTorsionAverage h K0 (ς0 • ωstar)).det
  A0inv : ‖(KAM.Iso.extendedTorsionAverage h K0 (ς0 • ωstar))⁻¹‖ ≤ σT - μm
  mT_pos : 0 < σT - μm
  mT_lt : σT - μm < N.sT
  loc0 : ‖torsionAverage h K0 (ς0 • ωstar) - torsionABAverage h K0‖ ≤ N.bF
  Y0 : n * ‖avg (energyRow h K0) - fun a => ((ς0 • ωstar) a : ℂ)‖ ≤ N.bF
  form0 : KAM.Iso.extendedTorsionAverage h K0 (ς0 • ωstar) =
    bordMat (torsionAverage h K0 (ς0 • ωstar)) (fun a => ((ς0 • ωstar) a : ℂ))
      (avg (energyRow h K0))

variable {N : NumB n} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ωstar : Fin n → ℝ} {Ω : Set (Fin n → ℝ)} {τ M E₀ σω ν γ σT μm Xi ς0 : ℝ}
  {K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

namespace RunHypI

variable (R : RunHypI τ M N 𝔅 h ωstar Ω E₀ σω ν γ σT μm K0 ς0)
include R

theorem γ_pos : 0 < γ := R.std.gamma_pos

theorem gd_pos (s : ℕ) : 0 < γ * N.δ s ^ N.τ :=
  mul_pos R.γ_pos (Real.rpow_pos_of_pos (R.wf.δ_pos s) _)

theorem gd1_pos (s : ℕ) : 0 < γ * N.δ s ^ (N.τ + 1) :=
  mul_pos R.γ_pos (Real.rpow_pos_of_pos (R.wf.δ_pos s) _)

/-- With the weights `λ_s`, `γ δ_s^τ`, the two-term `μ` of `LocHyp` is `w`. -/
theorem mu_eq (s : ℕ) {w : ℝ} :
    KAM.Sharp2.ModStepB.mu (N.inp s) γ ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w) (N.δ s) = w := by
  have hl := (R.wf.inp_lam_pos s).1
  have hg := R.gd_pos s
  show max ((N.inp s).lam * w / (N.inp s).lam) (γ * N.δ s ^ N.τ * w / (γ * N.δ s ^ N.τ)) = w
  rw [mul_div_cancel_left₀ _ hl.ne', mul_div_cancel_left₀ _ hg.ne', max_self]

theorem xX_eq (s : ℕ) {w : ℝ} :
    KAM.Sharp2.ModStepB.xX (N.inp s) γ ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w) (N.δ s) =
      w / (γ * N.δ s ^ (N.τ + 1)) := by
  rw [KAM.Sharp2.ModStepB.xX, R.mu_eq s]
  rfl

/-- The caps used in the local data. -/
theorem caps_of {s : ℕ} {w : ℝ} {m : Fin 7 → ℝ} (hw : 0 ≤ w)
    (hcap : ∀ i, m i + N.rate s i * N.wt s i * (w / (γ * N.δ s ^ (N.τ + 1))) ≤
      capB N σT μm ν i) :
    ∀ i, m i ≤ capB N σT μm ν i := by
  intro i
  have h0 := (stageC_nonneg R.wf (N.δ s)).2.2.2 i
  rw [stageC_sched R.wf] at h0
  have hX : 0 ≤ w / (γ * N.δ s ^ (N.τ + 1)) := div_nonneg hw (R.gd1_pos s).le
  have := hcap i
  have : 0 ≤ N.rate s i * N.wt s i * (w / (γ * N.δ s ^ (N.τ + 1))) := mul_nonneg h0 hX
  linarith

/-- The standing data at the frequency `ς ω*`. -/
theorem setting {ς : ℝ} (hς : 1 < ς) : Setting n τ M N.sK N.sB N.sT 𝔅 h (ς • ωstar) γ :=
  R.std.setting hς.le

/-- The local data `LocHyp` of a flagged stage torus. -/
theorem loc {s : ℕ} {β w : ℝ} {m : Fin 7 → ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ς : ℝ} (hG : GoodI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s (N.r s) β w m K ς)
    (hcond : stepCondB (N.inp s) (w / (γ * N.δ s ^ (N.τ + 1))))
    (hcaps : ∀ i, m i ≤ capB N σT μm ν i) :
    ∃ c', LocHyp (N.inp s) 𝔅 h K (ς • ωstar) Ω γ β ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w)
      (N.δ s) (N.r s) N.split c' ![m 0, m 1, m 2, m 3, m 4] := by
  obtain ⟨-, ⟨c', hc', hc1⟩, -⟩ := R.cert.at R.wf s
  refine ⟨c', ?_⟩
  exact
    { ok := R.wf.inp_ok s
      pn := rfl
      γ_pos := R.γ_pos
      γ_le := R.γ_le
      δ_pos := R.wf.δ_pos s
      δ_le := R.wf.δ_le_inp s
      three := R.wf.three_δ_lt s
      mem := R.mem _ hG.ς_gt.le
      s_pos := R.wf.split_pos
      s_lt := R.wf.split_lt_one
      cert' := hc'
      c1_le := hc1
      std := ⟨τ, M, γ, (R.setting hG.ς_gt).toStanding⟩
      dX := R.dX
      holo := hG.holo
      primary := hG.primary
      ball := hG.ball
      β_pos' := hG.β_pos
      L := hG.L
      Lt := hG.Lt
      G := hG.G
      N := hG.Nm
      Nt := hG.NmT
      ηL := hG.ηL
      ηN := hG.ηN
      E0 := fun h0 θ hθ => by
        have hs0 : s = 0 := of_decide_eq_true h0
        rw [R.mu_eq s]
        exact hG.E0 hs0 θ hθ
      cond := by rw [R.xX_eq s]; exact hcond
      caps' := ⟨hcaps 0, hcaps 1, hcaps 2, hcaps 3, hcaps 4⟩ }

/-- `|⟨Y⟩ - ω| ≤ A` when `|ηᴸ| ≤ A` on a strip: `Y = ω - ηᴸ`. -/
theorem avgY_sub_le {r A ς : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hr : 0 < r)
    (hc : Continuous fun x : Fin n → ℝ => energyRow h K fun i => (x i : ℂ))
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det)
    (hη : ∀ θ ∈ complexStrip n r, ‖etaL h K (ς • ωstar) θ‖ ≤ A) :
    ‖avg (energyRow h K) - fun a => ((ς • ωstar) a : ℂ)‖ ≤ A := by
  have e := avg_sub_of_continuous (F := Fin n → ℂ) (f := energyRow h K)
    (g := fun _ => fun a => ((ς • ωstar) a : ℂ)) hc continuous_const
  have e0 : avg (fun _ : Fin n → ℂ => fun a => ((ς • ωstar) a : ℂ)) =
      fun a => ((ς • ωstar) a : ℂ) := avg_const _
  rw [e0] at e
  rw [← e]
  refine norm_torusAverage_le_of_strip_bound (F := Fin n → ℂ)
    (f := fun θ => energyRow h K θ - fun a => ((ς • ωstar) a : ℂ)) hr fun θ hθ => ?_
  show ‖energyRow h K θ - fun a => ((ς • ωstar) a : ℂ)‖ ≤ A
  rw [LastRowAux.energyRow_eq_sub_etaL (ω := ς • ωstar) (hG θ hθ), sub_sub_cancel_left, norm_neg]
  exact hη θ hθ

/-- The local parts and the torsion bound at a flagged stage torus (`stepI:p2s2:st-t`). -/
theorem local_parts {s : ℕ} {β w : ℝ} {m : Fin 7 → ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ς : ℝ}
    (hG : GoodI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s (N.r s) β w m K ς)
    (hcond : stepCondB (N.inp s) (w / (γ * N.δ s ^ (N.τ + 1))))
    (hcaps : ∀ i, m i ≤ capB N σT μm ν i) :
    (∀ θ ∈ complexStrip n (N.r s - N.δ s), ‖torsion h K (ς • ωstar) θ‖ ≤
      (N.inp s).cTh * (N.inp s).sNt * (N.inp s).sN + (N.inp s).ts) ∧
      ‖torsionAverage h K (ς • ωstar) - torsionABAverage h K‖ ≤ N.bF ∧
      n * ‖avg (energyRow h K) - fun a => ((ς • ωstar) a : ℂ)‖ ≤ N.bF ∧
      KAM.Iso.extendedTorsionAverage h K (ς • ωstar) =
        bordMat (torsionAverage h K (ς • ωstar)) (fun a => ((ς • ωstar) a : ℂ))
          (avg (energyRow h K)) := by
  obtain ⟨c', L⟩ := R.loc hG hcond hcaps
  have hSet := R.setting hG.ς_gt
  have hS := hSet.toStanding
  have hr0 : 0 < N.r s := (R.wf.r_gt s).trans' R.wf.ρinf_pos
  have hr1 : 0 < N.r s - N.δ s := by linarith [R.wf.three_δ_lt s, R.wf.δ_pos s, R.wf.ρinf_pos]
  have hX : 0 ≤ w / (γ * N.δ s ^ (N.τ + 1)) := div_nonneg hG.μ_nonneg (R.gd1_pos s).le
  have hloc := L.torsion_sub_le hS
  have hBX : sBsup (N.inp s) *
      KAM.Sharp2.ModStepB.xX (N.inp s) γ ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w) (N.δ s)
      ≤ (N.inp s).ts := L.c_Bsup
  have hBl : sBloc (N.inp s) *
      KAM.Sharp2.ModStepB.xX (N.inp s) γ ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w) (N.δ s) ≤
      (N.inp s).bF := L.cond.2.2.2.2.2.2.2.2.2.1
  have hBmax : sBloc (N.inp s) = max (sBsup (N.inp s)) ((n : ℝ) * sg1 (N.inp s)) := by
    rw [sBloc]
    simp only [show (N.inp s).iso = true from R.iso, ↓reduceIte]
    rfl
  rw [R.xX_eq s] at hBl hBX
  rw [R.xX_eq s] at hloc
  have hB1 : sBsup (N.inp s) * (w / (γ * N.δ s ^ (N.τ + 1))) ≤ N.bF :=
    (mul_le_mul_of_nonneg_right (by rw [hBmax]; exact le_max_left _ _) hX).trans hBl
  have hB2 : (n : ℝ) * sg1 (N.inp s) * (w / (γ * N.δ s ^ (N.τ + 1))) ≤ N.bF :=
    (mul_le_mul_of_nonneg_right (by rw [hBmax]; exact le_max_right _ _) hX).trans hBl
  have hdK : ∀ θ ∈ complexStrip n (N.r s), ‖fderiv ℂ K θ‖ ≤ N.sK := fun θ hθ => by
    rw [← norm_colMat]; exact (hG.L θ hθ).trans (hcaps 0)
  have hGB : ∀ θ ∈ complexStrip n (N.r s),
      IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ N.sB := fun θ hθ =>
    ⟨(hG.G θ hθ).1, (hG.G θ hθ).2.trans (hcaps 2)⟩
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hcT⟩, -⟩ :=
    frame_basic hS hr0 hG.β_pos hG.holo hG.ball hdK hGB
  have hcAB : Continuous (fun x : Fin n → ℝ => torsionAB h K (fun i => (x i : ℂ))) :=
    Triangular.continuous_ofReal_comp hr0 (diffOn_torsionAB hS hr0 hG.β_pos hG.holo hG.ball hdK hGB)
  have hKD : ∀ θ ∈ complexStrip n (N.r s), K θ ∈ 𝔅 := fun θ hθ =>
    hG.ball θ hθ (Metric.mem_ball_self hG.β_pos)
  obtain ⟨⟨hYd, -, -, -, -, -, -, hform, -⟩, -⟩ :=
    extended_basic hSet hr0 hG.holo hG.primary hG.real hKD fun θ hθ => (hG.G θ hθ).1
  have hcY : Continuous fun x : Fin n → ℝ => energyRow h K fun i => (x i : ℂ) :=
    Exactness.continuous_real_of_differentiableOn hr0 hYd
  refine ⟨fun θ hθ => ?_, ?_, ?_, hform⟩
  · have hθr : θ ∈ complexStrip n (N.r s) :=
      Triangular.strip_mono (by linarith [R.wf.δ_pos s]) hθ
    have hab := norm_torsionAB_le (hG.G θ hθr).1 ((hG.Nm θ hθr).trans (hcaps 3))
      ((hG.NmT θ hθr).trans (hcaps 4)) (R.comm _ (hG.ball θ hθr (Metric.mem_ball_self hG.β_pos)))
    calc ‖torsion h K (ς • ωstar) θ‖ ≤ ‖torsionAB h K θ‖ +
          ‖torsion h K (ς • ωstar) θ - torsionAB h K θ‖ := by
          have := norm_add_le (torsionAB h K θ) (torsion h K (ς • ωstar) θ - torsionAB h K θ)
          rwa [add_sub_cancel] at this
      _ ≤ N.sNt * N.cTh * N.sN + (N.inp s).ts := add_le_add hab ((hloc θ hθ).trans hBX)
      _ = _ := by show _ = N.cTh * N.sNt * N.sN + _; ring
  · rw [torsionAverage_eq' hcT, torsionABAverage_eq hcAB]
    refine norm_torusAverage_sub_le hcT hcAB fun x =>
      ((hloc _ (ofReal_mem_complexStrip hr1 x)).trans hB1)
  · -- `|ηᴸ| ≤ λ μ ≤ μ ≤ g₁ X`
    have hl := R.wf.inp_lam_pos s
    have hμg : w ≤ sg1 (N.inp s) * (w / (γ * N.δ s ^ (N.τ + 1))) := by
      have h1 := L.mu_le
      rw [R.mu_eq s, R.xX_eq s] at h1
      exact h1
    have hA : ∀ θ ∈ complexStrip n (N.r s), ‖etaL h K (ς • ωstar) θ‖ ≤ w := fun θ hθ =>
      (hG.ηL θ hθ).trans ((mul_le_mul_of_nonneg_right hl.2 hG.μ_nonneg).trans_eq (one_mul _))
    have hY := R.avgY_sub_le (ς := ς) hr0 hcY (fun θ hθ => (hG.G θ hθ).1) hA
    calc (n : ℝ) * ‖avg (energyRow h K) - fun a => ((ς • ωstar) a : ℂ)‖ ≤
        (n : ℝ) * (sg1 (N.inp s) * (w / (γ * N.δ s ^ (N.τ + 1)))) :=
          mul_le_mul_of_nonneg_left (hY.trans hμg) (Nat.cast_nonneg _)
      _ = (n : ℝ) * sg1 (N.inp s) * (w / (γ * N.δ s ^ (N.τ + 1))) := by ring
      _ ≤ _ := hB2

/-- The torsion and bordered twist bounds at a flagged stage torus (`stepI:p2s2:st-t`). -/
theorem tors {s : ℕ} {β w : ℝ} {m : Fin 7 → ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ς : ℝ}
    (hG : GoodI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s (N.r s) β w m K ς)
    (hcond : stepCondB (N.inp s) (w / (γ * N.δ s ^ (N.τ + 1))))
    (hcaps : ∀ i, m i ≤ capB N σT μm ν i) :
    (∀ θ ∈ complexStrip n (N.r s - N.δ s), ‖torsion h K (ς • ωstar) θ‖ ≤
      (N.inp s).cTh * (N.inp s).sNt * (N.inp s).sN + (N.inp s).ts) ∧
      IsUnit (KAM.Iso.extendedTorsionAverage h K (ς • ωstar)).det ∧
      ‖(KAM.Iso.extendedTorsionAverage h K (ς • ωstar))⁻¹‖ ≤ (N.inp s).sT := by
  obtain ⟨hT, hlT, hlY, hform⟩ := R.local_parts hG hcond hcaps
  refine ⟨hT, ?_⟩
  set bF := N.bF
  set βT := (N.sT - (σT - μm)) / (N.sT * (σT - μm)) with hβT
  set ω' : Fin n → ℂ := fun a => ((ς • ωstar) a : ℂ) with hω'
  set ω0 : Fin n → ℂ := fun a => ((ς0 • ωstar) a : ℂ) with hω0
  have hm5 : m 5 ≤ βT - 2 * bF := hcaps 5
  have hbF0 : 0 ≤ bF := R.wf.budgets.2.le
  have hdω : ‖ω' - ω0‖ ≤ ‖ς • ωstar - ς0 • ωstar‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
    show ‖(((ς • ωstar) a : ℝ) : ℂ) - (((ς0 • ωstar) a : ℝ) : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub, Complex.norm_real]
    exact norm_le_pi_norm (ς • ωstar - ς0 • ωstar) a
  set Y := avg (energyRow h K)
  set Y0 := avg (energyRow h K0)
  have hTd : ‖torsionAverage h K (ς • ωstar) - torsionAverage h K0 (ς0 • ωstar)‖ ≤
      2 * bF + ‖torsionABAverage h K - torsionABAverage h K0‖ := by
    have e : torsionAverage h K (ς • ωstar) - torsionAverage h K0 (ς0 • ωstar) =
        (torsionAverage h K (ς • ωstar) - torsionABAverage h K) +
          (torsionABAverage h K - torsionABAverage h K0) -
            (torsionAverage h K0 (ς0 • ωstar) - torsionABAverage h K0) := by abel
    rw [e]
    calc _ ≤ ‖(torsionAverage h K (ς • ωstar) - torsionABAverage h K) +
          (torsionABAverage h K - torsionABAverage h K0)‖ +
            ‖torsionAverage h K0 (ς0 • ωstar) - torsionABAverage h K0‖ := norm_sub_le _ _
      _ ≤ (bF + ‖torsionABAverage h K - torsionABAverage h K0‖) + bF :=
          add_le_add ((norm_add_le _ _).trans (add_le_add_left hlT _)) R.loc0
      _ = _ := by ring
  have hYd : ∑ b, ‖(Y - Y0) b‖ ≤ m 5 + 2 * bF := by
    have hsum : ∑ b, ‖(Y - Y0) b‖ ≤ ∑ _b : Fin n, ‖Y - Y0‖ :=
      Finset.sum_le_sum fun b _ => norm_le_pi_norm (Y - Y0) b
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have e : Y - Y0 = (Y - ω') + (ω' - ω0) - (Y0 - ω0) := by abel
    have h1 : ‖Y - Y0‖ ≤ ‖Y - ω'‖ + ‖ω' - ω0‖ + ‖Y0 - ω0‖ := by
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    calc _ ≤ (n : ℝ) * ‖Y - Y0‖ := hsum
      _ ≤ (n : ℝ) * (‖Y - ω'‖ + ‖ς • ωstar - ς0 • ωstar‖ + ‖Y0 - ω0‖) :=
          mul_le_mul_of_nonneg_left (h1.trans (by linarith)) hn
      _ = (n : ℝ) * ‖Y - ω'‖ + (n : ℝ) * ‖ς • ωstar - ς0 • ωstar‖ + (n : ℝ) * ‖Y0 - ω0‖ := by ring
      _ ≤ bF + m 5 + bF := add_le_add (add_le_add hlY hG.drift') R.Y0
      _ = _ := by ring
  have hdiff : ‖KAM.Iso.extendedTorsionAverage h K (ς • ωstar) -
      KAM.Iso.extendedTorsionAverage h K0 (ς0 • ωstar)‖ ≤ βT := by
    rw [hform, R.form0, TorsionDiff.bordMat_sub]
    have hm0 : 0 ≤ m 5 + 2 * bF := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans hYd
    refine (TorsionDiff.norm_bordMat_le _ _ _ hTd hdω hYd hm0).trans ?_
    refine max_le ?_ (by linarith)
    linarith [hG.drift]
  exact inv_le_of_ref_bord R.A0 R.A0inv R.mT_pos R.mT_lt hdiff

end RunHypI

end KAM.Iso.Sharp2.RouteB

end
