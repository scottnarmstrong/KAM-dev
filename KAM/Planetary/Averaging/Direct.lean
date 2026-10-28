/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.Setting
public import KAM.Nekhoroshev.NormalForm.IterativeReal

/-!
# P Part 2: the direct homological solve and its iterative step (`bpP:p2:direct`)

`direct` and `direct_step` are the selected views of the exact N Part 6 results
`homological_direct` and `iterative_direct_a`–`iterative_direct_e`, instantiated at `p = 2` and
`α_N = 2α/q`, so that `conjExp 2 = 2`, `α_N / conjExp 2 = α / q` and `conjExp 2 / α_N = q / α`.
The generator is the unchanged `homGen K Λ h f` and the flow is the unchanged `iterMap`; no
premise is added. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-05.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Instantiate

variable {n : ℕ} {D : Set (Fin n → ℂ)} {r s K α q δ : ℝ} {Λ : Set (Fin n → ℤ)}
  {h : (Fin n → ℂ) → ℂ} {f : CHam n}

theorem conjExp_two : conjExp 2 = 2 := by
  unfold conjExp; norm_num

/-- The N direct-divisor premise at `p = 2`, `α_N = 2α/q` is the P2 setting. -/
theorem divisor_two (H : DirectHyp D r s K α q δ Λ h f) :
    DivisorBound (polyNbhd D r) K Λ h (2 * α / q / conjExp 2) := by
  have e : 2 * α / q / conjExp 2 = α / q := by
    rw [conjExp_two]; ring
  rw [e]; exact H.div

theorem bound_two (H : DirectHyp D r s K α q δ Λ h f) :
    conjExp 2 * δ / (2 * π * (2 * α / q)) = q * δ / (2 * π * α) := by
  have := H.α_pos
  have := H.q_ge
  have := Real.pi_pos
  rw [conjExp_two]
  field_simp

theorem iterU_two (H : DirectHyp D r s K α q δ Λ h f) (ρ σ : ℝ) :
    iterU (2 * α / q) 2 δ ρ σ = q * δ / (2 * π * α * ρ * σ) := by
  have := H.α_pos
  have := H.q_ge
  unfold iterU
  rw [conjExp_two]
  by_cases hρσ : ρ * σ = 0
  · rcases mul_eq_zero.1 hρσ with h0 | h0 <;> simp [h0]
  · have := Real.pi_pos
    field_simp

end Instantiate

/-- Selected solve/norm view of N `homological_direct`, not its full contract.
Use that upstream theorem on this same `homGen` for all other projections. -/
theorem direct {n : ℕ} {D : Set (Fin n → ℂ)} {r s K α q δ : ℝ}
    {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f : CHam n}
    (H : DirectHyp D r s K α q δ Λ h f) :
    InClass D r s (homGen K Λ h f) ∧
    WBound D r s (homGen K Λ h f) (q * δ / (2 * π * α)) ∧
    ∀ z ∈ Dom n D r s,
      poissonBracket (homGen K Λ h f) (fun w => h w.2) z +
        projMode Λ (truncate K f) z = truncate K f z := by
  have hα : 0 < 2 * α / q := by
    have := H.α_pos
    have := H.q_ge
    positivity
  obtain ⟨c1, -, -, c4, -, -, -, -, c9, -⟩ :=
    homological_direct (p := 2) (by norm_num) hα H.s_pos H.K_nonneg H.holo (divisor_two H)
      H.cls H.bound
  exact ⟨c1, (bound_two H) ▸ c9, c4⟩

/-- Selected view of N `iterative_direct_a` through `iterative_direct_e`. Instantiate
`p = 2`, `α_N = 2α/q` on this same generator/flow. In particular, finite averaging
uses upstream `iterative_direct_a` for integer translations; this wrapper is not
the entire inherited N contract. -/
theorem direct_step {n J : ℕ} {D : Set (Fin n → ℂ)} {r s K α q δ ρ σ : ℝ}
    {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f : CHam n}
    {gj : Fin J → CHam n} {rj sj Mj : Fin J → ℝ}
    (H : DirectHyp D r s K α q δ Λ h f)
    (hρ : 0 < ρ ∧ 2 * ρ < r) (hσ : 0 < σ ∧ 2 * σ < s)
    (hsmall : q * δ / (2 * π * α * ρ * σ) ≤ 1 / 4)
    (hg : ∀ j, InClass D (rj j) (sj j) (gj j) ∧ WBound D (rj j) (sj j) (gj j) (Mj j) ∧
      r ≤ rj j ∧ s ≤ sj j) :
    let φ := homGen K Λ h f
    let Ψ := flow (KAM.hamiltonianVectorFieldℂ φ) (Dom n D (r - ρ) (s - σ)) 1
    let g := fun z => ∑ j, gj j z
    let gp := fun z => g z + projMode Λ (truncate K f) z
    let fp := fun z => h (Ψ z).2 + g (Ψ z) + f (Ψ z) - h z.2 - gp z
    let u := q * δ / (2 * π * α * ρ * σ)
    let star := ∑ j, (1 / 2) * (ρ / (rj j - r + ρ) + σ / (sj j - s + σ)) * Mj j
    let V := Dom n D (r - 2 * ρ) (s - 2 * σ)
    DifferentiableOn ℂ Ψ (Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2)) ∧
    MapsTo Ψ (Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2)) (Dom n D (r - ρ) (s - σ)) ∧
    Set.InjOn Ψ V ∧
    (∀ z ∈ V, ∀ v w, symplFormC (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = symplFormC v w) ∧
    InClass D (r - 2 * ρ) (s - 2 * σ) fp ∧
    WBound D (r - 2 * ρ) (s - 2 * σ) fp
      ((1 - 2 * u)⁻¹ * (2 * q / (exp 1 * (2 * π * α) * ρ * σ) * (star + δ) +
        exp (-(2 * π * K * σ))) * δ) ∧
    (∀ z ∈ V, ‖(Ψ z).1 - z.1‖ ≤ q * δ / (2 * π * α * ρ) ∧
      ‖(Ψ z).2 - z.2‖ ≤ q * δ / (exp 1 * (2 * π * α) * σ)) ∧
    ((∀ k ∈ Λ, -k ∈ Λ) → RealOn (Dom n D r s) (fun z => h z.2) →
      RealOn (Dom n D r s) f → (∀ j, RealOn (Dom n D (rj j) (sj j)) (gj j)) →
      RealOn V gp ∧ RealOn V fp ∧
      ∀ x : Phase n, KAM.realInclusion₂ n x ∈ V → Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n)) := by
  intro φ Ψ g gp fp u star V
  have hα : 0 < 2 * α / q := by
    have := H.α_pos
    have := H.q_ge
    positivity
  have hu := iterU_two H ρ σ
  have hq : 0 < q := by linarith [H.q_ge]
  have hπ := Real.pi_pos
  have hαp := H.α_pos
  have HI : IterHyp D r s ρ σ K (2 * α / q) 2 δ Λ h g f gj rj sj Mj :=
    { hp := by norm_num
      hα := hα
      hK := H.K_nonneg
      hs := H.s_pos
      hρ := hρ.1
      hρr := hρ.2
      hσ := hσ.1
      hσs := hσ.2
      h_holo := H.holo
      divisor := divisor_two H
      decomp := ⟨rfl, fun j => (hg j).2.2.1, fun j => (hg j).2.2.2, fun j => (hg j).1,
        fun j => (hg j).2.1⟩
      f_class := H.cls
      f_bound := H.bound
      δ_nonneg := H.δ_nonneg
      δ_small := by
        have h1 : iterU (2 * α / q) 2 δ ρ σ ≤ 1 / 4 := hu ▸ hsmall
        unfold iterU at h1
        rw [div_le_iff₀ (by have := hρ.1; have := hσ.1; positivity)] at h1
        rw [le_div_iff₀ (by rw [conjExp_two]; norm_num)]
        linarith }
  have ha := iterative_direct_a HI
  have hb := iterative_direct_b HI
  have hc := iterative_direct_c HI
  have hd := iterative_direct_d HI
  have hV : V ⊆ Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2) :=
    Dom_mono (by linarith [hρ.1]) (by linarith [hσ.1])
  have e1 : conjExp 2 * δ / (2 * π * (2 * α / q) * ρ) = q * δ / (2 * π * α * ρ) := by
    rw [conjExp_two]; field_simp
  have e2 : conjExp 2 * δ / (Real.exp 1 * (2 * π * (2 * α / q)) * σ) =
      q * δ / (Real.exp 1 * (2 * π * α) * σ) := by
    rw [conjExp_two]; field_simp
  have e3 : 2 * conjExp 2 / (Real.exp 1 * (2 * π * (2 * α / q)) * ρ * σ) =
      2 * q / (Real.exp 1 * (2 * π * α) * ρ * σ) := by
    rw [conjExp_two]; field_simp
  obtain ⟨a1, a2, a3, -, a5, -⟩ := ha
  obtain ⟨b1, -⟩ := hb
  obtain ⟨-, -, -, hc4⟩ := hc
  refine ⟨a1, a2, a5, fun z hz => a3 z (hV hz), hc4, ?_, fun z hz => ?_, fun hΛ hhr hfr hgr => ?_⟩
  · have := hd
    rw [hu, e3] at this
    exact this
  · obtain ⟨-, b2, b3⟩ := b1 z (hV hz)
    rw [e1] at b2
    rw [e2] at b3
    exact ⟨b2, b3⟩
  · have hgr' : RealOn (Dom n D r s) g := fun x hx => by
      show (∑ j, gj j (KAM.realInclusion₂ n x)).im = 0
      rw [Complex.im_sum]
      exact Finset.sum_eq_zero fun j _ =>
        hgr j x (Dom_mono (hg j).2.2.1 (hg j).2.2.2 hx)
    obtain ⟨-, e2', e3', e4'⟩ := iterative_direct_e HI hΛ hhr hgr' hfr
    exact ⟨fun x hx => e2' x (Dom_mono (by linarith [hρ.1]) (by linarith [hσ.1]) hx),
      fun x hx => e3' x hx, fun x hx => e4' x (hV hx)⟩

end KAM.Planetary

end
