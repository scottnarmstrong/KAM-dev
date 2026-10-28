/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.ToriSetup

/-!
# Two-scale KAM: complex extension of the torus and `estimates` (`bpP:p3:estimates`)

`tori_complex_ext`: for `I ∈ D_*`, the torus `θ ↦ Φ(θ, I)` extends holomorphically to the strip
`|Im θ| < s̄/2π` with angle displacement `≤ 3 Ê s / 4π` (the three coordinatewise `StripLimit`s of
`limit_phi_strip_of_steps`, reassembled). `tori_estimates_of_limit` is the private conditional
helper for the local obligation `estimates` (steps `es-sup`, `es-loc`): angle bound, the two block
sup bounds, and the location `v ∈ Re(D_r)`, `r = 32 Ê ρ̂`. Design package P23-20.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData} {h : (Fin (a + b) → ℂ) → ℂ}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {Φ : ℕ → CPhase (a + b) → CPhase (a + b)}
  {is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)}
  {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)} {Φinf : Phase (a + b) → Phase (a + b)}

/-- Reassembly of the coordinatewise extensions of the torus `θ ↦ Φ(θ, I)`, for `I ∈ D_*`:
holomorphic on the strip, equal to `Φ(θ, I)` at real angles, with angle displacement
`≤ 3 Ê s / 4π`. -/
theorem tori_complex_ext {D : Set (Fin (a + b) → ℝ)} {f : CHam (a + b)}
    (H : KamHyp D sbar p h f) (T : ToriLimit sbar p h Ds hs Φ is i Φinf) {I : Fin (a + b) → ℝ}
    (hI : I ∈ i '' Ds 0) :
    ∃ KC : (Fin (a + b) → ℂ) → CPhase (a + b),
      DifferentiableOn ℂ KC (KAM.complexStrip (a + b) (geometricWidth sbar)) ∧
      (∀ θ, KC (KAM.realInclusion (a + b) θ) = KAM.realInclusion₂ (a + b) (Φinf (θ, I))) ∧
      (∀ θ ∈ KAM.complexStrip (a + b) (geometricWidth sbar),
        ‖(KC θ).1 - θ‖ ≤ 3 / (4 * π) * eHat p * p.s) := by
  obtain ⟨h1, h2, h3⟩ := T.phi_strip I hI
  choose G hG using h1
  choose Gf hGf using h2
  choose Gl hGl using h3
  let A : Fin (a + b) → (Fin (a + b) → ℂ) → ℂ := fun c => Fin.addCases (motive := fun _ => _)
    (fun k => Gf k) (fun k => Gl k) c
  have hAd : ∀ c, DifferentiableOn ℂ (A c) (KAM.complexStrip (a + b) (geometricWidth sbar)) := by
    intro c
    induction c using Fin.addCases with
    | left k => simpa [A] using (hGf k).1
    | right k => simpa [A] using (hGl k).1
  have hAr : ∀ c θ, A c (KAM.realInclusion (a + b) θ) =
      (((Φinf (θ, I) - (θ, I)).2 c : ℝ) : ℂ) := by
    intro c θ
    induction c using Fin.addCases with
    | left k => simpa [A] using (hGf k).2.1 θ
    | right k => simpa [A] using (hGl k).2.1 θ
  refine ⟨fun θ => (fun c => θ c + G c θ, fun c => (I c : ℂ) + A c θ), ?_, ?_, ?_⟩
  · refine DifferentiableOn.prodMk ?_ ?_
    · exact differentiableOn_pi.2 fun c =>
        (((differentiable_apply c).differentiableOn).add (hG c).1)
    · exact differentiableOn_pi.2 fun c => (differentiableOn_const _).add (hAd c)
  · intro θ
    ext c
    · simp [(hG c).2.1 θ]
    · simp [hAr c θ]
  · intro θ hθ
    have hB : 0 ≤ 3 / (4 * π) * eHat p * p.s := by
      have := eHat_pos H; have := H.positive.2.1; positivity
    refine (pi_norm_le_iff_of_nonneg hB).2 fun c => ?_
    show ‖(θ c + G c θ) - θ c‖ ≤ _
    rw [add_sub_cancel_left]
    refine ((hG c).2.2.1 θ hθ).trans (le_of_eq ?_)
    field_simp
    ring

/-- The local obligation `estimates` of `two_scale_kam` (private conditional helper, P23-20), on
the shared limit data: for `I₀ ∈ D₀`, with `I_* = ǐ(I₀)` and the torus `θ ↦ Φ(θ, I_*) = (θ + u, v)`:
the holomorphic extension with `|u| ≤ 3 Ê s/4π` on the strip (`tori_complex_ext`), the sup bounds
`|v₁ - I₀,₁| ≤ 20 (M̄₁/M̄ + M̂/M) Ê ρ̂`, `|v₂ - I₀,₂| ≤ 20 (M̄₂/M̄ + 1) Ê ρ̂`, and the location
`v ∈ Re(D_r)`, `r = 32 Ê ρ̂`. -/
theorem tori_estimates_of_limit {D : Set (Fin (a + b) → ℝ)} {f : CHam (a + b)}
    (H : KamHyp D sbar p h f) (hD0 : Ds 0 ⊆ D) (T : ToriLimit sbar p h Ds hs Φ is i Φinf)
    {I₀ : Fin (a + b) → ℝ} (hI₀ : I₀ ∈ Ds 0) :
    (∃ KC : (Fin (a + b) → ℂ) → CPhase (a + b),
      DifferentiableOn ℂ KC (KAM.complexStrip (a + b) (geometricWidth sbar)) ∧
      (∀ θ, KC (KAM.realInclusion (a + b) θ) =
        KAM.realInclusion₂ (a + b) (Φinf (θ, i I₀))) ∧
      (∀ θ ∈ KAM.complexStrip (a + b) (geometricWidth sbar),
        ‖(KC θ).1 - θ‖ ≤ 3 / (4 * π) * eHat p * p.s)) ∧
    (∀ θ, ‖firstBlock (b := b) ((Φinf (θ, i I₀)).2 - I₀)‖ ≤
        20 * (p.Mbar₁ / p.Mbar + p.Mhat / p.M) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) ((Φinf (θ, i I₀)).2 - I₀)‖ ≤
        20 * (p.Mbar₂ / p.Mbar + 1) * eHat p * rhoHat p) ∧
    (∀ θ, (Φinf (θ, i I₀)).2 ∈ realTube D (32 * eHat p * rhoHat p)) := by
  have hmem : i I₀ ∈ i '' Ds 0 := ⟨I₀, hI₀, rfl⟩
  have he := eHat_pos H
  have hR := H.R_pos
  have heR : 0 < eHat p * rhoHat p := mul_pos he hR
  have hr1 : 0 ≤ p.Mhat / p.M :=
    div_nonneg H.positive.2.2.2.2.2.1.le H.positive.2.2.2.2.1.le
  have hr1' : p.Mhat / p.M ≤ 1 := (div_le_one H.positive.2.2.2.2.1).2 H.normalized.1
  have hr2 : 0 ≤ p.Mbar₁ / p.Mbar :=
    div_nonneg H.positive.2.2.2.2.2.2.2.1.le H.positive.2.2.2.2.2.2.1.le
  have hr3 : 0 ≤ p.Mbar₂ / p.Mbar :=
    div_nonneg H.positive.2.2.2.2.2.2.2.2.le H.positive.2.2.2.2.2.2.1.le
  have key : ∀ θ, ((Φinf (θ, i I₀)).2 - I₀) =
      (Φinf (θ, i I₀) - (θ, i I₀)).2 + (i I₀ - I₀) := by intro θ; simp
  refine ⟨tori_complex_ext H T hmem, fun θ => ?_, fun θ => ?_⟩
  · have hx : (θ, i I₀) ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))) := ⟨trivial, hmem⟩
    obtain ⟨c1, c2, -⟩ := T.phi_block _ hx
    obtain ⟨d1, d2, -⟩ := T.i_block I₀ hI₀
    have h0 : seq p 0 = p := rfl
    rw [h0] at d1 d2
    rw [key θ]
    have hp := heR.le
    have e1 : ‖firstBlock (b := b) ((Φinf (θ, i I₀) - (θ, i I₀)).2 + (i I₀ - I₀))‖ ≤
        ‖firstBlock (b := b) (Φinf (θ, i I₀) - (θ, i I₀)).2‖ +
          ‖firstBlock (b := b) (i I₀ - I₀)‖ :=
      norm_add_le (firstBlock (b := b) (Φinf (θ, i I₀) - (θ, i I₀)).2)
        (firstBlock (b := b) (i I₀ - I₀))
    have e2 : ‖lastBlock (a := a) ((Φinf (θ, i I₀) - (θ, i I₀)).2 + (i I₀ - I₀))‖ ≤
        ‖lastBlock (a := a) (Φinf (θ, i I₀) - (θ, i I₀)).2‖ +
          ‖lastBlock (a := a) (i I₀ - I₀)‖ :=
      norm_add_le (lastBlock (a := a) (Φinf (θ, i I₀) - (θ, i I₀)).2)
        (lastBlock (a := a) (i I₀ - I₀))
    refine ⟨e1.trans ?_, e2.trans ?_⟩
    · nlinarith [mul_nonneg hr1 hp]
    · nlinarith [mul_nonneg hr3 hp]
  · have hx : (θ, i I₀) ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))) := ⟨trivial, hmem⟩
    obtain ⟨c1, c2, -⟩ := T.phi_block _ hx
    obtain ⟨-, -, d3⟩ := T.i_block I₀ hI₀
    have h0 : seq p 0 = p := rfl
    rw [h0] at d3
    refine (mem_realTube_iff).2 ⟨I₀, hD0 hI₀, ?_⟩
    rw [key θ]
    have hsup : ‖(Φinf (θ, i I₀) - (θ, i I₀)).2‖ ≤ 3 / 2 * eHat p * rhoHat p := by
      refine norm_le_of_blocks (by positivity) (c1.trans ?_) c2
      nlinarith [mul_pos he hR]
    refine (norm_add_le ((Φinf (θ, i I₀) - (θ, i I₀)).2) (i I₀ - I₀)).trans_lt ?_
    nlinarith [mul_pos he hR]

end KAM.Planetary

end
