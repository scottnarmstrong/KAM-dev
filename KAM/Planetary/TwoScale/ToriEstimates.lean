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

/-- First derivatives of a `StripLimit` converge pointwise on the open strip. -/
theorem StripLimit.fderiv_tendsto {n : ℕ} [Nonempty (Fin n)] {w B : ℝ}
    {F : ℕ → (Fin n → ℂ) → ℂ} {f : (Fin n → ℝ) → ℂ} {G : (Fin n → ℂ) → ℂ}
    (hS : StripLimit n w B F f G) {z : Fin n → ℂ} (hz : z ∈ KAM.complexStrip n w)
    (u : Fin n → ℂ) :
    Tendsto (fun j => fderiv ℂ (F j) z u) atTop (𝓝 (fderiv ℂ G z u)) := by
  have hw : 0 < w := (abs_nonneg _).trans_lt (hz (Classical.arbitrary _))
  set v0 := Finset.univ.sup' Finset.univ_nonempty (fun k => |(z k).im|) with hv0
  have hv0w : v0 < w := (Finset.sup'_lt_iff _).2 fun k _ => hz k
  have hvw : max v0 (w / 2) < w := max_lt hv0w (by linarith)
  have hvpos : 0 < max v0 (w / 2) := lt_max_of_lt_right (by linarith)
  have hmem : z ∈ {z : Fin n → ℂ | ∀ i, |(z i).im| ≤ max v0 (w / 2)} := fun k =>
    ((Finset.le_sup' (fun k => |(z k).im|) (Finset.mem_univ k)).trans (le_max_left _ _))
  have hT := (hS.2.2.2.2 _ hvpos hvw 1).tendsto_at hmem
  have hc := ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin 1 => Fin n → ℂ) ℂ
    (fun _ => u)).continuous.tendsto _).comp hT
  simpa [Function.comp_def] using hc

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
        ‖(KC θ).1 - θ‖ ≤ 3 / (4 * π) * eHat p * p.s) ∧
      (∀ z ∈ KAM.complexStrip (a + b) (geometricWidth sbar), ∀ u,
        Tendsto (fun j => fderiv ℂ (fun θ => Φ j (θ, KAM.realInclusion (a + b) I)) z u) atTop
          (𝓝 (fderiv ℂ KC z u))) := by
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
  refine ⟨fun θ => (fun c => θ c + G c θ, fun c => (I c : ℂ) + A c θ), ?_, ?_, ?_, ?_⟩
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
  · intro z hz u
    haveI : Nonempty (Fin (a + b)) := ⟨⟨0, by have := H.a_pos; omega⟩⟩
    have hzn := (KAM.isOpen_complexStrip (a + b) (geometricWidth sbar)).mem_nhds hz
    have hFd : ∀ j, DifferentiableAt ℂ (fun θ => Φ j (θ, KAM.realInclusion (a + b) I)) z :=
      fun j => (T.stage_diff j I hI).differentiableAt hzn
    have hGd : ∀ c, DifferentiableAt ℂ (G c) z := fun c => (hG c).1.differentiableAt hzn
    have hAd' : ∀ c, DifferentiableAt ℂ (A c) z := fun c => (hAd c).differentiableAt hzn
    have hK1 : HasFDerivAt (fun θ : Fin (a + b) → ℂ => fun c => θ c + G c θ)
        (ContinuousLinearMap.pi fun c => (ContinuousLinearMap.proj c + fderiv ℂ (G c) z)) z := by
      rw [hasFDerivAt_pi']
      intro c
      exact (hasFDerivAt_apply c z).add (hGd c).hasFDerivAt
    have hK2 : HasFDerivAt (fun θ : Fin (a + b) → ℂ => fun c => (I c : ℂ) + A c θ)
        (ContinuousLinearMap.pi fun c => fderiv ℂ (A c) z) z := by
      rw [hasFDerivAt_pi']
      intro c
      simpa using (hAd' c).hasFDerivAt.const_add (I c : ℂ)
    have hKC := congrArg (fun L => L u) (hK1.prodMk hK2).fderiv
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
      add_apply, ContinuousLinearMap.proj_apply] at hKC
    have hstrip : ∀ (πc : CPhase (a + b) →L[ℂ] ℂ) j,
        fderiv ℂ (PsiSteps.stripSeq Φ πc I j) z u =
          πc (fderiv ℂ (fun θ => Φ j (θ, KAM.realInclusion (a + b) I)) z u) - πc (u, 0) := by
      intro πc j
      have hg : HasFDerivAt (fun θ : Fin (a + b) → ℂ => (θ, KAM.realInclusion (a + b) I))
          ((ContinuousLinearMap.id ℂ _).prod (0 : (Fin (a + b) → ℂ) →L[ℂ] _)) z :=
        (hasFDerivAt_id z).prodMk (hasFDerivAt_const _ z)
      have h1 : HasFDerivAt (PsiSteps.stripSeq Φ πc I j)
          (πc.comp ((fderiv ℂ (fun θ => Φ j (θ, KAM.realInclusion (a + b) I)) z) -
            (ContinuousLinearMap.id ℂ _).prod (0 : (Fin (a + b) → ℂ) →L[ℂ] _))) z :=
        πc.hasFDerivAt.comp z ((hFd j).hasFDerivAt.sub hg)
      rw [h1.fderiv]
      simp
    rw [hKC]
    refine Prod.tendsto_iff _ _ |>.2 ⟨tendsto_pi_nhds.2 fun c => ?_, tendsto_pi_nhds.2 fun c => ?_⟩
      have e : ∀ j, (fderiv ℂ (fun θ => Φ j (θ, KAM.realInclusion (a + b) I)) z u).1 c =
          u c + fderiv ℂ (PsiSteps.stripSeq Φ ((ContinuousLinearMap.proj c).comp
            (ContinuousLinearMap.fst ℂ _ _)) I j) z u := by
        intro j; rw [hstrip]; simp
      simp_rw [e]
      exact tendsto_const_nhds.add ((hG c).fderiv_tendsto hz u)
    · induction c using Fin.addCases with
      | left k =>
        have e : ∀ j, (fderiv ℂ (fun θ => Φ j (θ, KAM.realInclusion (a + b) I)) z u).2
            (Fin.castAdd b k) = fderiv ℂ (PsiSteps.stripSeq Φ
            ((ContinuousLinearMap.proj (Fin.castAdd b k)).comp (ContinuousLinearMap.snd ℂ _ _)) I
            j) z u := by
          intro j; rw [hstrip]; simp
        simp_rw [e]
        simpa [A] using (hGf k).fderiv_tendsto hz u
      | right k =>
        have e : ∀ j, (fderiv ℂ (fun θ => Φ j (θ, KAM.realInclusion (a + b) I)) z u).2
            (Fin.natAdd a k) = fderiv ℂ (PsiSteps.stripSeq Φ
            ((ContinuousLinearMap.proj (Fin.natAdd a k)).comp (ContinuousLinearMap.snd ℂ _ _)) I
            j) z u := by
          intro j; rw [hstrip]; simp
        simp_rw [e]
        simpa [A] using (hGl k).fderiv_tendsto hz u

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
  obtain ⟨KC, k1, k2, k3, -⟩ := tori_complex_ext H T hmem
  refine ⟨⟨KC, k1, k2, k3⟩, fun θ => ?_, fun θ => ?_⟩
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
