/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.Hybrid.Core
public import KAM.Sharp2.Hybrid.G1
import Mathlib.Tactic.Linarith

/-!
# The isoenergetic hybrid theorem and the minimum (`bpI:p2s2hc:g1`, `bpI:p2s2hc:frozen`)

* `linNewErrorIso`, `linNewError_eq_iso`: `Ẽ_s` of `bpI:p2s2hc:lin` is `linNewError` at `s₁ ω*`;
* `IsoNum`, `IsoNum.e1`, `IsoNum.tAext`: the numbers of `bpI:p2s2hc:bounds`, `:errors`, `:torsion`;
* `iso_g1_hybrid_R`: Theorem `bpI:p2s2hc:g1`, route A with L8′, the step form;
* `NumA.restartI`, `IHybOkR`, `iso_g1_v2A'_hybrid`: Corollary `bpI:p2s2hc:frozen`, by cases.

`NumA.restartI` is `NumA.restart` with `HY` recomputed from the restart cap `σ_N`. The isoenergetic
numbers keep `HY = M_{h1} σ_N`, and `RestartA` changes `σ_N`; the design note's signatures stop
before the isoenergetic minimum, where this appears.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Iso.Sharp2.Hybrid

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2
open KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteA KAM.Sharp2.RouteA.Ref KAM.Iso.Sharp2.RouteA.Ref
open KAM.Sharp2.Hybrid KAM.Iso.Sharp

variable {n : ℕ}

/-- `IG1Concl` is monotone in the two closeness bounds. -/
theorem IG1Concl.mono {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ωstar : Fin n → ℝ} {s E₀ ρinf μ σK σω Dk Dk' Dω Dω' : ℝ} (hk : Dk ≤ Dk') (hω : Dω ≤ Dω')
    (h1 : IG1Concl D H K ωstar s E₀ ρinf μ σK σω Dk Dω) :
    IG1Concl D H K ωstar s E₀ ρinf μ σK σω Dk' Dω' := by
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h1
  exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, fun θ hθ => (h10 θ hθ).trans hk,
    h11.trans hω⟩

/-- `bpI:p2s2hc:lin`: `Ẽ_s = E_s + DX_H(K) ΔK - DΔK (s ω*) - Δs D(K + ΔK) ω*`. -/
def linNewErrorIso (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ωstar : Fin n → ℝ) (s s₁ : ℝ)
    (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  invarianceError H K (s • ωstar) θ + fderiv ℂ (hamiltonianVectorFieldℂ H) (K θ) (ΔK θ) -
    fderiv ℂ ΔK θ (fun i => ((s • ωstar) i : ℂ)) -
      ((s₁ - s : ℝ) : ℂ) • fderiv ℂ (K + ΔK) θ (fun i => (ωstar i : ℂ))

/-- `Ẽ_s` is `linNewError` at the new frequency `s₁ ω*`, the form of `StepBounds.lin`. -/
theorem linNewError_eq_iso {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ωstar : Fin n → ℝ} {s s₁ : ℝ}
    {θ : Fin n → ℂ} (hK : DifferentiableAt ℂ K θ) (hΔ : DifferentiableAt ℂ ΔK θ) :
    linNewError H K ΔK (s₁ • ωstar) θ = linNewErrorIso H K ΔK ωstar s s₁ θ := by
  have e : ∀ c : ℝ, (fun i => ((c • ωstar) i : ℂ)) = (c : ℂ) • fun i => (ωstar i : ℂ) := fun c => by
    ext i
    simp
  simp only [linNewError, linNewErrorIso, invarianceError, e, map_smul, fderiv_add_step hK hΔ,
    _root_.add_apply, Complex.ofReal_sub]
  module

/-- The isoenergetic hybrid numbers beyond the fixed-frequency ones (Definition
`bpI:p2s2hc:bounds`): `ℓ_H ≥ |ε̃|`, `d_ω ≥ |Δs||ω*|`, and `Mh1 ≥ |DH|`, `Mh2 ≥ |D²H|`. -/
structure IsoNum where
  lH : ℝ
  dω : ℝ
  Mh1 : ℝ
  Mh2 : ℝ

/-- `e₁` of Lemma `bpI:p2s2hc:errors`. -/
def IsoNum.e1 (q : IsoNum) (b : StepNum) (M2 : ℝ) : ℝ :=
  max (b.e1 M2) (q.lH + q.Mh2 / 2 * b.d0R ^ 2)

/-- `t_A^ext` of Lemma `bpI:p2s2hc:torsion`: the last row `Σ_j |DH(K₁)N₁ e_j - DH(K)N e_j|` is
bounded through the transposes, `n (M_{h1} n_Δᵗ + M_{h2} d₀ (νᵗ + n_Δᵗ))` on `ℝⁿ`. -/
def IsoNum.tAext (q : IsoNum) (b : StepNum) (k : KData) (nn M1 M2 δ cTh : ℝ) : ℝ :=
  max (b.tA k nn M1 M2 δ cTh + q.dω)
    (nn * (q.Mh1 * (b.frR k).nΔt + q.Mh2 * b.d0R * (k.νt + (b.frR k).nΔt)))

/-- Theorem `bpI:p2s2hc:g1`, route A with L8′, the step form: `iso_g1_hybrid_core_R` with every
hypothesis on `(K₁, s₁)` derived from the step bounds and the certified data of `(K, s)` by
Lemmas `bp:p2s2hc:struct`–`bp:p2s2hc:torsion`, `bpI:p2s2hc:errors`, `bpI:p2s2hc:torsion`. The
fields of `StepBounds` are taken at the frequency `s ω*` for `K` and `s₁ ω*` for `K₁` (so its
`lin` is `Ẽ_s`); the iso refined data are `RefHypIA`'s for `K` on `T_{ρ₀}`. -/
theorem iso_g1_hybrid_R {N₁ : NumA} (hN : N₁.Wf) (hiso : N₁.iso = true)
    (hτ : (N₁.n : ℝ) - 1 ≤ N₁.τ) {M σK σB σT μ μ₁ γbar σω ν ρ₀ Xs bF bT cTh : ℝ} (k : KData)
    (b : StepNum) (q : IsoNum) (hM : 0 < M) (hμ₁ : 0 < μ₁) (hσω : 1 < σω)
    {ωstar : Fin N₁.n → ℝ} (hωstar : ωstar ≠ 0) (hγbar : γbar = N₁.γb) (hρ : N₁.ρ ≤ ρ₀)
    (hℓ : k.ℓ = σK - μ) (hβ : k.β = σB - μ) (hm : k.m = σT - μ)
    (hsK : N₁.sK = b.sK1 k μ₁ - μ₁ / 2) (hΘ : N₁.Θ = σω * ‖ωstar‖)
    (hHY : N₁.HY = q.Mh1 * N₁.sN) (hνq : 0 < ν - q.dω)
    (hOk : routeAOkRI N₁ bF (capRI N₁ (μ₁ / 2) bT ((ν - q.dω) / 2))
      (initRI (b.init1 k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh) (b.sK1 k μ₁) (b.sB1 k μ₁) μ₁) Xs)
    (hB : Budget N₁ (k.m / (1 - k.m * q.tAext b k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh))
      (b.init1 k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh).iH bF bT) (hXpos : 0 < Xs)
    (hm1 : b.d0 + μ₁ ≤ μ) (hm2 : b.d1 + μ₁ / 2 ≤ μ / 2) (hgS : k.β * (b.frS k).g < 1)
    (hgR : k.β * (b.frR k).g < 1)
    (htA : k.m * q.tAext b k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh < 1)
    {D : Set ((Fin N₁.n → ℂ) × (Fin N₁.n → ℂ))} {H : (Fin N₁.n → ℂ) × (Fin N₁.n → ℂ) → ℂ}
    {K ΔK : (Fin N₁.n → ℂ) → (Fin N₁.n → ℂ) × (Fin N₁.n → ℂ)} {s s₁ γ E₀ : ℝ}
    {Ω : Set (Fin N₁.n → ℝ)} (hopen : IsOpen D)
    (htransl : ∀ z ∈ D, ∀ k : Fin N₁.n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ D)
    (hholo : DifferentiableOn ℂ H D)
    (hper : ∀ z ∈ D, ∀ k : Fin N₁.n → ℤ, H (z.1 + (fun i => (k i : ℂ)), z.2) = H z)
    (hreal : ∀ θ I : Fin N₁.n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ D →
      (H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ H z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧ ‖iteratedFDeriv ℂ 2 H z‖ ≤ M)
    (hcTh : ∀ z ∈ D, ‖hamComm H z‖ ≤ cTh)
    (hK : DifferentiableOn ℂ K (complexStrip N₁.n ρ₀)) (hKp : IsPrimaryOnStrip K ρ₀)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip N₁.n ρ₀, Metric.ball (K θ) μ ⊆ D)
    (hDK : ∀ θ ∈ complexStrip N₁.n ρ₀, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip N₁.n ρ₀, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ)
    (hTu : IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)).det)
    (hTb : ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹ i j‖ ≤ σT - μ)
    (hs1 : 1 < s) (hν1 : ν ≤ (s - 1) * ‖ωstar‖) (hν2 : ν ≤ (σω - s) * ‖ωstar‖)
    (hRef : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ N₁.M1 ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ N₁.M2 ∧
      ‖fderiv ℂ H z‖ ≤ q.Mh1 ∧ ‖iteratedFDeriv ℂ 2 H z‖ ≤ q.Mh2 ∧ q.Mh2 ≤ N₁.Mh2)
    (hLt : ∀ θ ∈ complexStrip N₁.n ρ₀, ‖(tangentMat K θ)ᵀ‖ ≤ k.ℓt)
    (hNm : ∀ θ ∈ complexStrip N₁.n ρ₀, ‖normalMat K θ‖ ≤ k.ν)
    (hNt : ∀ θ ∈ complexStrip N₁.n ρ₀, ‖(normalMat K θ)ᵀ‖ ≤ k.νt)
    (hT : ∀ θ ∈ complexStrip N₁.n (N₁.ρ - N₁.δ 0), ‖torsion H K (s • ωstar) θ‖ ≤ k.t)
    (hS : IsStep ΔK ρ₀)
    (hb : StepBounds H K ΔK (s • ωstar) (s₁ • ωstar) N₁.ρ N₁.ρinf (N₁.ρ - N₁.δ 0) b)
    (hlinH : ‖linNewEnergy H K ΔK E₀‖ ≤ q.lH) (hdω : ‖s₁ • ωstar - s • ωstar‖ ≤ q.dω)
    (hΩ : ∀ s' : ℝ, 1 ≤ s' → s' • ωstar ∈ Ω) (hCt : N₁.Cert γ Ω) (hγ : 0 < γ)
    (hγγbar : γ ≤ γbar) (hdio : IsDiophantine γ N₁.τ ωstar)
    (hsm : q.e1 b N₁.M2 / (γ ^ 4 * delta0 3 N₁.ρ N₁.ρinf ^ (2 * (2 * N₁.τ))) < Xs)
    (hbud : b.dinf + c2I N₁ Xs * q.e1 b N₁.M2 / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ)) ≤ μ / 2) :
    IG1Concl D H K ωstar s E₀ N₁.ρinf μ σK σω
      (b.dinf + c2I N₁ Xs * q.e1 b N₁.M2 / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ)))
      (q.dω + c3I N₁ Xs * q.e1 b N₁.M2 / (γ ^ 2 * N₁.ρ ^ (2 * N₁.τ))) := by
  have hρ₁ : 0 < N₁.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hρ₀ : 0 < ρ₀ := hρ₁.trans_le hρ
  have hdω0 : 0 ≤ q.dω := (norm_nonneg _).trans hdω
  have hν : 0 < ν := by linarith
  obtain ⟨hs₁, -, hν₁1, hν₁2⟩ := ray_step hωstar hν1 hν2 hdω hνq
  have hIS : IsoStanding N₁.n N₁.τ M N₁.sK N₁.sB N₁.sT σω ν ωstar D H γ :=
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
  have T : StepHyp D H K ΔK (s • ωstar) (s₁ • ωstar) ρ₀ N₁.ρ N₁.ρinf (N₁.δ 0) N₁.M1 N₁.M2 cTh μ μ₁
      k b :=
    { one_le := by have := hN.two_le; omega
      std := ⟨_, _, _, _, _, _, (hIS.setting hs1.le).toStanding⟩
      std₁ := ⟨_, _, _, _, _, _, (hIS.setting hs₁.le).toStanding⟩
      δ_pos := hN.δ_pos 0
      ρδ_pos := ρ_sub_δ_pos hN
      ρ_le := hρ
      holo := hK
      ball := hball
      L := fun θ hθ => by rw [FrameAux.norm_tangentMat, hℓ]; exact hDK θ hθ
      Lt := hLt
      gram := fun θ hθ => (hG θ hθ).1
      B := fun θ hθ => by rw [hβ]; exact norm_le_of_rowSum_le hN.two_le (hG θ hθ).2
      Nm := hNm
      Nt := hNt
      step := hS
      bd := hb
      dX := fun z hz => (hRef z hz).1
      d2X := fun z hz => (hRef z hz).2.1
      comm := hcTh
      m1 := hm1
      μ₁_pos := hμ₁
      gS := hgS
      gR := hgR }
  obtain ⟨h1, h2, h3, h4, h5⟩ := T.struct hKp hKr
  have hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ q.Mh1 := fun z hz => (hRef z hz).2.2.1
  have hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ q.Mh2 := fun z hz => (hRef z hz).2.2.2.1
  have hq : 0 < 1 - k.m * q.tAext b k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh := by linarith
  have hm0 : 0 < k.m := (div_pos_iff_of_pos_right hq).1 hB.mT_pos
  -- the bordered torsion
  obtain ⟨hTu₁, hTn₁⟩ := extTorsionAverage_step (K₁ := K + ΔK)
    (fun i j => integrableOn_torsion (s • ωstar) hopen hholo hρ₀ hK (fun θ hθ => T.mem hθ) T.gram i
      j)
    (fun i j => integrableOn_torsion (s₁ • ωstar) hopen hholo hρ₁ T.holo₁ (fun θ hθ => T.mem₁ hθ)
      T.gram₁ i j)
    (integrableOn_lastRow hopen hholo hρ₀ hK (fun θ hθ => T.mem hθ) T.gram)
    (integrableOn_lastRow hopen hholo hρ₁ T.holo₁ (fun θ hθ => T.mem₁ hθ) T.gram₁)
    T.torsR (fun x => sum_norm_lastRow_step_le hopen hholo hdH hd2H (hball _ (T.sub (T.real₁ x)))
      (hb.real x).1 (T.Δ_lt (T.real₁ x)) (T.framesR x).2.2.2.2.2.1 (T.framesR x).2.2.2.2.2.2.2)
    hdω hTu (by rw [hm]; exact norm_le_of_rowSum_le_of_nonempty (m := Fin N₁.n ⊕ Unit) hTb) hm0
    htA ((norm_nonneg _).trans (T.torsR 0))
  -- the energy
  have hd0m : ∀ x : Fin N₁.n → ℝ, ‖ΔK fun l => (x l : ℂ)‖ ≤ min b.d0 b.d0R := fun x =>
    le_min (hb.d0 _ (T.real₁ x)) (hb.real x).1
  have hEn₁ : ‖KAM.Iso.energyAverage H (K + ΔK) - (E₀ : ℂ)‖ ≤ q.lH + q.Mh2 / 2 * b.d0R ^ 2 := by
    refine (energyAverage_step_le hopen hholo hd2H (fun x => hball _ (T.sub (T.real₁ x))) hd0m
      ((min_le_left _ _).trans_lt T.d0_lt)
      (integrableOn_comp hholo hρ₀ hK (fun θ hθ => T.mem hθ))
      (integrableOn_comp hholo hρ₁ T.holo₁ (fun θ hθ => T.mem₁ hθ))
      (integrableOn_fderiv_apply hopen hholo hρ₀ hK (fun θ hθ => T.mem hθ) hS.holo) hlinH).trans ?_
    have h00 : 0 ≤ min b.d0 b.d0R := (norm_nonneg _).trans (hd0m 0)
    have hM2 : 0 ≤ q.Mh2 := (norm_nonneg _).trans (hd2H _ (T.mem (T.sub (T.real₁ 0))))
    have := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ h00 (min_le_right b.d0 b.d0R) 2) (show 0 ≤ q.Mh2 / 2 by positivity)
    linarith
  have he1 : b.e1 N₁.M2 ≤ q.e1 b N₁.M2 := le_max_left _ _
  have hE₁ : ∀ θ ∈ complexStrip N₁.n N₁.ρ,
      ‖invarianceError H (K + ΔK) (s₁ • ωstar) θ‖ ≤ q.e1 b N₁.M2 :=
    fun θ hθ => (T.err θ hθ).trans he1
  refine iso_g1_hybrid_core_R (σK₁ := b.sK1 k μ₁) (σB₁ := b.sB1 k μ₁)
    (σT₁ := k.m / (1 - k.m * q.tAext b k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh) + μ₁) (ν₁ := ν - q.dω)
    (Mh1 := q.Mh1) (I₁ := b.init1 k N₁.n N₁.M1 N₁.M2 (N₁.δ 0) cTh) (s₁ := s₁)
    hN hiso hτ hM hμ₁ hσω hνq hωstar
    hγbar hsK hΘ hHY hOk (by rwa [add_sub_cancel_right]) hXpos hopen htransl hholo hper hreal hbd h1
    h2 h3 h4 ?_ ?_ hTu₁ ?_ hs₁ hν₁1 hν₁2 ?_ hΩ hCt hγ hγγbar hdio
    ((norm_nonneg _).trans (hE₁ _ (T.real₁ 0))) hE₁
    (hEn₁.trans (le_max_right _ _)) hsm
    (fun θ hθ => hball θ (strip_le (hN.ρinf_lt.le.trans hρ) hθ))
    (fun θ hθ => by simpa using hb.dinf θ hθ) hdω hbud ?_
  · intro θ hθ
    rw [StepNum.sK1, add_sub_cancel_right]
    exact h5 θ hθ
  · intro θ hθ
    refine ⟨(T.frames hθ).1, fun i => ?_⟩
    rw [StepNum.sB1, add_sub_cancel_right]
    exact (T.gramRow hθ).2 i
  · intro i
    rw [add_sub_cancel_right]
    exact (sum_norm_row_le _ i).trans hTn₁
  · exact ⟨fun z hz => (hRef z hz).1, fun z hz => (hRef z hz).2.1, hdH,
      fun z hz => (hRef z hz).2.2.2.1.trans (hRef z hz).2.2.2.2,
      fun θ hθ => (T.frames hθ).2.1, fun θ hθ => (T.frames hθ).2.2.2.2.2.2.1,
      fun θ hθ => (T.frames hθ).2.2.2.2.2.2.2, T.tors₁ hT⟩
  · rw [StepNum.sK1, hℓ]
    linarith

/-- The isoenergetic restart numbers: `NumA.restart` with `HY = M_{h1} σ_N` at the restart cap
`σ_N`; `(N.restartI R Mh1).n = N.n` definitionally. -/
def _root_.KAM.Sharp2.RouteA.NumA.restartI (N : NumA) (R : RestartA) (Mh1 : ℝ) : NumA :=
  { N.restart R with HY := Mh1 * R.sN }

/-- The hybrid condition `HybOk^I_A'` of Theorem `bpI:p2s2hc:g1` for `(K, s)` with the data `k`, the
step numbers `b`, `q`, the restart `N₁ = N.restartI R q.Mh1`, margin `μ₁`, `X⋆`, budgets `bF`,
`bT`. -/
structure IHybOkR (N : NumA) (R : RestartA) (k : KData) (b : StepNum) (q : IsoNum)
    (σK σB σT μ μ₁ γ ν Xs bF bT cTh : ℝ) : Prop where
  wf : (N.restartI R q.Mh1).Wf
  μ₁_pos : 0 < μ₁
  ρ_le : R.ρ₁ ≤ N.ρ
  ℓ : k.ℓ = σK - μ
  β : k.β = σB - μ
  m : k.m = σT - μ
  sK : R.sK = b.sK1 k μ₁ - μ₁ / 2
  ν₁ : 0 < ν - q.dω
  ok : routeAOkRI (N.restartI R q.Mh1) bF (capRI (N.restartI R q.Mh1) (μ₁ / 2) bT ((ν - q.dω) / 2))
    (initRI (b.init1 k N.n N.M1 N.M2 ((N.restartI R q.Mh1).δ 0) cTh) (b.sK1 k μ₁) (b.sB1 k μ₁) μ₁)
    Xs
  budget : Budget (N.restartI R q.Mh1)
    (k.m / (1 - k.m * q.tAext b k N.n N.M1 N.M2 ((N.restartI R q.Mh1).δ 0) cTh))
    (b.init1 k N.n N.M1 N.M2 ((N.restartI R q.Mh1).δ 0) cTh).iH bF bT
  Xs_pos : 0 < Xs
  m1 : b.d0 + μ₁ ≤ μ
  m2 : b.d1 + μ₁ / 2 ≤ μ / 2
  gS : k.β * (b.frS k).g < 1
  gR : k.β * (b.frR k).g < 1
  tA : k.m * q.tAext b k N.n N.M1 N.M2 ((N.restartI R q.Mh1).δ 0) cTh < 1
  small : q.e1 b N.M2 / (γ ^ 4 * delta0 3 R.ρ₁ N.ρinf ^ (2 * (2 * N.τ))) < Xs
  bud : b.dinf + c2I (N.restartI R q.Mh1) Xs * q.e1 b N.M2 / (γ ^ 2 * R.ρ₁ ^ (2 * N.τ)) ≤ μ / 2

/-- Corollary `bpI:p2s2hc:frozen`, route A with L8′: the plain branch (`iso_g1_v2A'`'s constants at
`N`) or the hybrid branch (`IHybOkR` at `N.restartI R q.Mh1`), by cases; each closeness is the
maximum. Every hypothesis of `IG1BodyA` is kept; the step `ΔK`, its bounds and the hybrid numbers
are additional and are used only in the hybrid branch. -/
theorem iso_g1_v2A'_hybrid (N : NumA) (hN : N.Wf) (hiso : N.iso = true)
    (hτ : (N.n : ℝ) - 1 ≤ N.τ) {M σK σB σT μ γbar σω ν Xs Mh1 bF bT : ℝ} (I : InitA) (hM : 0 < M)
    (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT) (hμ : 0 < μ) (hσω : 1 < σω) (hν : 0 < ν)
    (ωstar : Fin N.n → ℝ) (hωstar : ωstar ≠ 0) (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2)
    (hΘ : N.Θ = σω * ‖ωstar‖) (hHY : N.HY = Mh1 * N.sN)
    (hOk : routeAOkRI N bF (capRI N (μ / 2) bT (ν / 2)) (initRI I σK σB μ) Xs)
    (hB : Budget N (σT - μ) I.iH bF bT) (hXpos : 0 < Xs) :
    ∀ (D : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))) (H : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ)
      (K ΔK : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) (s s₁ γ e E₀ : ℝ)
      (Ω : Set (Fin N.n → ℝ)) (R : RestartA) (k : KData) (b : StepNum) (q : IsoNum)
      (μ₁ X₁ bF₁ bT₁ cTh : ℝ),
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
      -- the hybrid data (used in the second branch only)
      (∀ z ∈ D, ‖hamComm H z‖ ≤ cTh) →
      (∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ q.Mh1 ∧ ‖iteratedFDeriv ℂ 2 H z‖ ≤ q.Mh2) → q.Mh2 ≤ N.Mh2 →
      I.iLt ≤ k.ℓt → I.iN ≤ k.ν → I.iNt ≤ k.νt → I.iH ≤ k.t → IsStep ΔK N.ρ →
      StepBounds H K ΔK (s • ωstar) (s₁ • ωstar) R.ρ₁ N.ρinf
        (R.ρ₁ - (N.restartI R q.Mh1).δ 0) b →
      ‖linNewEnergy H K ΔK E₀‖ ≤ q.lH → ‖s₁ • ωstar - s • ωstar‖ ≤ q.dω →
      (N.restartI R q.Mh1).Cert γ Ω →
      (min (sharpIsoC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ ν N.τ N.ρ N.ρinf) (c1A N Xs) *
          e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) < 1 ∨
        IHybOkR N R k b q σK σB σT μ μ₁ γ ν X₁ bF₁ bT₁ cTh) →
      IG1Concl D H K ωstar s E₀ N.ρinf μ σK σω
        (max (max (sharpIsoC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf)
            (c2I N Xs) * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)))
          (b.dinf + c2I (N.restartI R q.Mh1) X₁ * q.e1 b N.M2 / (γ ^ 2 * R.ρ₁ ^ (2 * N.τ))))
        (max (max (sharpIsoC3 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf)
            (c3I N Xs) * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)))
          (q.dω + c3I (N.restartI R q.Mh1) X₁ * q.e1 b N.M2 / (γ ^ 2 * R.ρ₁ ^ (2 * N.τ)))) := by
  intro D H K ΔK s s₁ γ e E₀ Ω R k b q μ₁ X₁ bF₁ bT₁ cTh hopen htransl hholo hper hreal hbd hK hKp
    hKr hball hDK hG hTu hTb hs1 hsσ hν1 hν2 hRef hΩ hCt hγ hγγbar hdio he0 hE hEn hcTh hdq hMh2 hLt
    hNu hNtt hHt hS hb hlinH hdω hCt₁ hor
  rcases hor with hsm | hy
  · obtain ⟨-, -, -, hbody⟩ := iso_g1_v2A' hN hiso hτ I hM hσK hσB hσT hμ hσω hν ωstar hωstar hγbar
      hsK hΘ hHY hOk hB hXpos
    exact IG1Concl.mono (le_max_left _ _) (le_max_left _ _) (hbody D H K s γ e E₀ Ω hopen htransl
      hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hs1 hsσ hν1 hν2 hRef hΩ hCt hγ hγγbar
      hdio he0 hE hEn hsm)
  · refine IG1Concl.mono (le_max_right _ _) (le_max_right _ _)
      (iso_g1_hybrid_R (N₁ := N.restartI R q.Mh1) (ρ₀ := N.ρ) hy.wf hiso hτ k b q hM hy.μ₁_pos hσω
        hωstar hγbar hy.ρ_le hy.ℓ hy.β hy.m hy.sK hΘ rfl hy.ν₁ hy.ok hy.budget hy.Xs_pos hy.m1 hy.m2
        hy.gS hy.gR hy.tA hopen htransl hholo hper hreal hbd hcTh hK hKp hKr hball hDK hG hTu hTb
        hs1 hν1 hν2 (fun z hz => ⟨hRef.dX z hz, hRef.d2X z hz, (hdq z hz).1, (hdq z hz).2, hMh2⟩)
        (fun θ hθ => (hRef.tangentT θ hθ).trans hLt) (fun θ hθ => (hRef.normal θ hθ).trans hNu)
        (fun θ hθ => (hRef.normalT θ hθ).trans hNtt)
        (fun θ hθ => (hRef.tors θ (strip_le (bite_mono hy.ρ_le) hθ)).trans hHt) hS hb hlinH hdω hΩ
        hCt₁ hγ hγγbar hdio hy.small hy.bud)

end KAM.Iso.Sharp2.Hybrid

end
