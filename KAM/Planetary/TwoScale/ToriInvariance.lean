/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.ToriInvConj
public import KAM.Planetary.TwoScale.ToriInvLimit
public import KAM.Planetary.TwoScale.ToriLagr

/-!
# Two-scale KAM: invariance (`bpP:p3:invariance`)

The private conditional helper `tori_invariance_of_limit` for the local obligation `invariance`:
for `I₀ ∈ D₀`, `ω = ω(I₀)` and `φ(θ) = Φ(θ, ǐ(I₀))`, `d/dt φ(θ + tω) = X_H(φ(θ + tω))`. The finite
stage curves `γ_j(t) = ψ_j(θ + tω, I_*)` satisfy `γ_j' − X_H(γ_j) = Dψ_j ((ω, 0) − X_{H_j})`
(`conj_field`), with `‖Dψ_j‖ ≤ κ` uniformly (`psiR_fderiv_bound`) and `‖(ω, 0) − X_{H_j}‖ ≤ C Ê_j`
(`field_err`, with `ω = ω_j(ǐ_j(I₀))` the proved frequency identity and the three error terms of
P3b L137–141), so `‖γ_j' − X_H(γ_j)‖ ≤ κ C Ê_j → 0` uniformly (`stage_err_le`); the passage to the
limit is `curve_limit_field`. Design package P23-20.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}
  {is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)}
  {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)} {Φinf : Phase (a + b) → Phase (a + b)}

/-- `M R̂ ≤ γ₁/3` and `E ≤ Ê R̂ γ₁/3` (from `R̂ ≤ γ₁/(3 M K^{τ+1})`, `K ≥ 1`, `E ≤ Ê R̂² M`). -/
theorem stage_bound (H : KamHyp D sbar p h f) :
    p.M * rhoHat p ≤ p.γ₁ / 3 ∧ p.E ≤ eHat p * rhoHat p * (p.γ₁ / 3) := by
  have hK : 1 ≤ cutoff p := by
    have h6 := H.K_mul_s
    have hs0 := H.positive.2.1
    have hw := H.widths
    have hs1 : p.s < 1 := by linarith
    by_contra hlt
    push_neg at hlt
    nlinarith [H.K_pos]
  have hKp : 1 ≤ cutoff p ^ (p.τ + 1) := Real.one_le_rpow hK (by have := H.τ_pos; linarith)
  have hR := H.R_pos
  have hM := H.positive.2.2.2.2.1
  have h1 := H.R_le_γ₁
  have h2 : p.M * rhoHat p ≤ p.γ₁ / 3 := by
    have : p.M * rhoHat p ≤ p.M * cutoff p ^ (p.τ + 1) * rhoHat p := by
      have := mul_le_mul_of_nonneg_left hKp hM.le
      nlinarith
    linarith
  refine ⟨h2, ?_⟩
  have := H.E_le_M
  have he := H.eHat_nonneg
  calc p.E ≤ eHat p * rhoHat p ^ 2 * p.M := this
    _ = eHat p * rhoHat p * (p.M * rhoHat p) := by ring
    _ ≤ eHat p * rhoHat p * (p.γ₁ / 3) := by gcongr

/-- The scalar bound of the three error terms: `M ‖I − c‖ + E/δ ≤ C Ê`. -/
theorem stage_err_le (H : KamHyp D sbar p h f) {Rmax : ℝ} (hR : rhoHat p ≤ Rmax)
    {d : ℝ} (hd : d ≤ 20 * rhoHat p * eHat p) (hd0 : 0 ≤ d) :
    p.M * d + p.E / min (p.ρ / 2) (sbar / (4 * π)) ≤
      eHat p * (20 * p.γ₁ / 3 + p.γ₁ / 3 * (2 + 4 * π * Rmax / sbar)) := by
  obtain ⟨hMR, hER⟩ := stage_bound H
  have hρ := H.positive.2.2.1
  have hs0 := H.positive.2.1
  have hsb : 0 < sbar := by have := H.widths.1; linarith
  have hM := H.positive.2.2.2.2.1
  have hE := H.positive.2.2.2.1
  have hRh := H.R_pos
  have he := eHat_pos H
  have hRρ := H.R_le_ρ
  have hγ := H.γ₁_pos
  have h1 : p.M * d ≤ 20 * eHat p * (p.γ₁ / 3) := by
    calc p.M * d ≤ p.M * (20 * rhoHat p * eHat p) := by gcongr
      _ = 20 * eHat p * (p.M * rhoHat p) := by ring
      _ ≤ _ := by gcongr
  have hmin : p.E / min (p.ρ / 2) (sbar / (4 * π)) ≤
      p.E / (p.ρ / 2) + p.E / (sbar / (4 * π)) := by
    have hp1 : 0 ≤ p.E / (p.ρ / 2) := by positivity
    have hp2 : 0 ≤ p.E / (sbar / (4 * π)) := by positivity
    rcases min_choice (p.ρ / 2) (sbar / (4 * π)) with e | e <;> rw [e] <;> linarith
  have h2 : p.E / (p.ρ / 2) ≤ eHat p * (p.γ₁ / 3) * 2 := by
    rw [div_le_iff₀ (by positivity)]
    calc p.E ≤ eHat p * rhoHat p * (p.γ₁ / 3) := hER
      _ ≤ eHat p * p.ρ * (p.γ₁ / 3) := by gcongr
      _ = _ := by ring
  have h3 : p.E / (sbar / (4 * π)) ≤ eHat p * (p.γ₁ / 3) * (4 * π * Rmax / sbar) := by
    rw [div_le_iff₀ (by positivity)]
    calc p.E ≤ eHat p * rhoHat p * (p.γ₁ / 3) := hER
      _ ≤ eHat p * Rmax * (p.γ₁ / 3) := by gcongr
      _ = _ := by field_simp
  nlinarith

theorem PsiSteps.eHat_tendsto (P : PsiSteps sbar p Ds hs fs Ψ Φ) :
    Tendsto (fun j => eHat (seq p j)) atTop (𝓝 0) := by
  have hb : ∀ j, eHat (seq p j) ≤ eHat p * (1 / 160) ^ j := by
    intro j
    induction j with
    | zero => simp [seq]
    | succ j ih =>
      have h1 := P.eHat_sq j
      have h2 := (P.hyp j).eHat_nonneg
      have h3 := (P.hyp j).eHat_lt_small
      calc eHat (seq p (j + 1)) ≤ eHat (seq p j) ^ 2 := h1.le
        _ ≤ eHat (seq p j) * (1 / 160) := by nlinarith
        _ ≤ eHat p * (1 / 160) ^ j * (1 / 160) := by gcongr
        _ = _ := by ring
  have hz : Tendsto (fun j : ℕ => eHat p * (1 / 160 : ℝ) ^ j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 160)
      (by norm_num)).const_mul (eHat p)
  exact squeeze_zero (fun j => (P.hyp j).eHat_nonneg) hb hz

/-- The local obligation `invariance` of `two_scale_kam` (private conditional helper, P23-20): for
`I₀ ∈ D₀`, `ω = ω(I₀)` and `φ(θ) = Φ(θ, ǐ(I₀))`, `d/dt φ(θ + tω) = X_H(φ(θ + tω))`, on the shared
witnesses (`P`, `Q`, `T`). -/
theorem tori_invariance_of_limit (H : KamHyp D sbar p h f)
    (P : PsiSteps sbar p Ds hs fs Ψ Φ) (Q : StageSteps D sbar p h f Ds hs fs Φ)
    (hD0 : Ds 0 ⊆ D) (T : ToriLimit sbar p h Ds hs Φ is i Φinf)
    {I₀ : Fin (a + b) → ℝ} (hI₀ : I₀ ∈ Ds 0) (θ : Fin (a + b) → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Φinf (θ + s • realFreq h I₀, i I₀))
      (KAM.hamiltonianVectorField (fun z : Phase (a + b) =>
        (h (KAM.realInclusion (a + b) z.2) + f (KAM.realInclusion₂ (a + b) z)).re)
        (Φinf (θ + t • realFreq h I₀, i I₀))) t := by
  have hs0 := H.positive.2.1
  have hsb : 0 < sbar := by have := H.widths.1; linarith
  have hρ := H.positive.2.2.1
  set ω := realFreq h I₀ with hω
  set Is := i I₀ with hIs
  have hmemD : Is ∈ i '' Ds 0 := ⟨I₀, hI₀, rfl⟩
  have path : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((θ + s • ω, Is) : Phase (a + b))) (ω, 0) t := by
    intro t
    have h1 := (((hasDerivAt_id t).smul_const ω).const_add θ).prodMk (hasDerivAt_const t Is)
    simpa using h1
  have hx : ∀ j (t : ℝ), ((θ + t • ω, Is) : Phase (a + b)) ∈
      phaseTube (Ds j) ((seq p j).ρ / 2) := fun j t => ⟨trivial, T.i_tube I₀ hI₀ j⟩
  set x : ℕ → ℝ → Phase (a + b) := fun j t => psiR (Φ j) (θ + t • ω, Is) with hxdef
  have hxd : ∀ j t, HasDerivAt (x j) (fderiv ℝ (psiR (Φ j)) (θ + t • ω, Is) (ω, 0)) t := by
    intro j t
    have hL := P.psiR_hasFDerivAt j (hx j t)
    have := hL.comp_hasDerivAt t (path t)
    rw [hL.fderiv]; exact this
  -- the scalar sequence
  set κ := 1 + max (p.s / (2 * π)) (rhoHat p) * max (2 * π / p.s) (rhoHat p)⁻¹ with hκ
  set C0 := 20 * p.γ₁ / 3 + p.γ₁ / 3 * (2 + 4 * π * rhoHat p / sbar) with hC0
  have hder : ∀ j t, ‖deriv (x j) t - KAM.hamiltonianVectorField (fun z : Phase (a + b) =>
      (h (KAM.realInclusion (a + b) z.2) + f (KAM.realInclusion₂ (a + b) z)).re) (x j t)‖ ≤
      κ * (C0 * eHat (seq p j)) := by
    intro j t
    have hHj := P.hyp j
    have hxt := hx j t
    rw [(hxd j t).deriv]
    have hX := conj_field H P Q j hxt
    have hxj : x j t = psiR (Φ j) (θ + t • ω, Is) := rfl
    rw [hxj, hX, ← map_sub]
    refine ((fderiv ℝ (psiR (Φ j)) (θ + t • ω, Is)).le_opNorm _).trans ?_
    have hκj := P.psiR_fderiv_bound j hxt
    have hc := T.i_mem I₀ hI₀ j
    obtain ⟨J, hJ, hIJ⟩ := mem_realTube_iff.1 (T.i_tube I₀ hI₀ j)
    have hRj := hHj.R_pos
    have hlt := hHj.eHat_lt_small
    have htail := T.i_tail I₀ hI₀ j
    have hd0 : 0 ≤ ‖Is - actionChain is j I₀‖ := norm_nonneg _
    have hIc : ‖Is - actionChain is j I₀‖ < rhoHat (seq p j) := by
      refine htail.trans_lt ?_
      have := hHj.eHat_nonneg
      nlinarith
    have hfe := field_err hHj hc hJ (θ := θ + t • ω) hIJ hIc
    rw [T.i_freq I₀ hI₀ j] at hfe
    have hse := stage_err_le hHj (Rmax := rhoHat p) (P.rho_le_zero j) htail hd0
    rw [seq_γ₁] at hse
    have hn : 0 ≤ ‖((ω, 0) : Phase (a + b)) - KAM.hamiltonianVectorField (fun z : Phase (a + b) =>
        (hs j (KAM.realInclusion (a + b) z.2) + fs j (KAM.realInclusion₂ (a + b) z)).re)
          (θ + t • ω, Is)‖ := norm_nonneg _
    have hfin : ‖((ω, 0) : Phase (a + b)) - KAM.hamiltonianVectorField
        (fun z : Phase (a + b) => (hs j (KAM.realInclusion (a + b) z.2) +
          fs j (KAM.realInclusion₂ (a + b) z)).re) (θ + t • ω, Is)‖ ≤ C0 * eHat (seq p j) := by
      refine (hfe.trans hse).trans (le_of_eq ?_)
      rw [hC0, mul_comm]
    calc _ ≤ κ * ‖((ω, 0) : Phase (a + b)) - KAM.hamiltonianVectorField
          (fun z : Phase (a + b) => (hs j (KAM.realInclusion (a + b) z.2) +
            fs j (KAM.realInclusion₂ (a + b) z)).re) (θ + t • ω, Is)‖ :=
          mul_le_mul_of_nonneg_right hκj hn
      _ ≤ _ := by gcongr
  have hε : Tendsto (fun j => κ * (C0 * eHat (seq p j))) atTop (𝓝 0) := by
    simpa using (P.eHat_tendsto.const_mul C0).const_mul κ
  sorry

end KAM.Planetary

end
