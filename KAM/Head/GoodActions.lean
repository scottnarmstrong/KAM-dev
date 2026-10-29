/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.RealTorus
import KAM.Head.Frequency
import KAM.Head.InverseFrequency
import KAM.Head.Lip
import KAM.Head.Parameters
import KAM.Head.UnperturbedFrame

/-!
# Good actions and the displacement is `1/2`-Lipschitz

Blueprint Part 4, `bp:p4:good-actions` (the claim after the definition) and `bp:p4:map-lipschitz`.
Under `(SA)`:

* `KAM.Head.good_actions`: for `I ∈ A_γ` the frequency `∇h(I)` lies in `Ω_γ`, `I_{∇h(I)} = I`, and
  `G₀(θ, I)` is the real restriction of `W_{∇h(I)}` at `θ` (`ι G₀(θ, I) = W_{∇h(I)}(ι θ)`).
* `KAM.Head.map_lipschitz`: `A_γ` and `Z` are disjoint, `‖G₀‖ ≤ η₀`, and `G₀` is `1/2`-Lipschitz on
  `ℝⁿ × (A_γ ∪ Z)` for the max norm.

The proof of `map_lipschitz` follows the three steps of the blueprint.
* `step:p4:ml-size`: `KAM.Head.disjoint_goodActions_layerSet` and `KAM.Head.norm_disp_le`.
* `step:p4:ml-good`: `KAM.Head.disp_sub_le_good_good`. The angle variable moves along a segment of
  `ℝⁿ`, and the real displacement has derivative at most `n (ρ/2)⁻¹ η₀ = A₄ ε γ⁻²`
  (`KAM.Head.realDisp_lipschitz`, from the Cauchy estimate); the action moves by
  `bp:p4:lip` and `bp:p4:freq-map` (v); the sum is at most `1/4` of the distance by (s6).
* `step:p4:ml-mixed`: `KAM.Head.disp_sub_le_mixed`. A good action and a boundary-layer action are
  at distance `≥ γ`, since `infDist(·, Bᶜ)` is `1`-Lipschitz, and `‖G₀‖ ≤ η₀ ≤ γ/2` by (s7).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Head

section RealDisp

variable {n : ℕ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}

/-- The derivative of the real displacement `y ↦ k(y) - (y, I)` is bounded by `n (ρ/2)⁻¹ η`. -/
theorem realDisp_fderiv_le (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hKr : IsRealOnReals K) {I : Fin n → ℝ} {η : ℝ}
    (hη : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η) (y v : Fin n → ℝ) :
    ‖fderiv ℝ (realRestriction K) y v - (v, 0)‖ ≤ n * (ρ / 2)⁻¹ * η * ‖v‖ := by
  obtain ⟨-, hv⟩ := realRestriction_fderiv hρ hK hKr y
  have hW : DifferentiableOn ℂ (fun θ => K θ - unperturbedTorus I θ) (complexStrip n ρ) :=
    hK.sub (differentiable_unperturbedTorus I).differentiableOn
  have hy : realInclusion n y ∈ complexStrip n (ρ - ρ / 2) := by
    rw [show ρ - ρ / 2 = ρ / 2 by ring]
    exact realInclusion_mem_complexStrip (half_pos hρ) y
  have hc := (cauchy_strip hW hη (half_pos hρ)).2 _ hy
  have hKθ : DifferentiableAt ℂ K (realInclusion n y) :=
    hK.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds
      (realInclusion_mem_complexStrip hρ y))
  have hder : fderiv ℂ (fun θ => K θ - unperturbedTorus I θ) (realInclusion n y) =
      fderiv ℂ K (realInclusion n y) - ContinuousLinearMap.inl ℂ (Fin n → ℂ) (Fin n → ℂ) :=
    (hKθ.hasFDerivAt.sub (unperturbedTorus_hasFDerivAt I _)).fderiv
  have h1 : realInclusion₂ n (fderiv ℝ (realRestriction K) y v - (v, 0)) =
      fderiv ℂ (fun θ => K θ - unperturbedTorus I θ) (realInclusion n y) (realInclusion n v) := by
    rw [map_sub, hv v, hder]
    simp
  rw [← norm_realInclusion₂, h1]
  calc _ ≤ ‖fderiv ℂ (fun θ => K θ - unperturbedTorus I θ) (realInclusion n y)‖ *
        ‖realInclusion n v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ n * (ρ / 2)⁻¹ * η * ‖v‖ := by
        rw [norm_realInclusion]
        exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

/-- The real displacement `y ↦ k(y) - (y, I)` is Lipschitz with constant `n (ρ/2)⁻¹ η`. -/
theorem realDisp_lipschitz (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hKr : IsRealOnReals K) {I : Fin n → ℝ} {η : ℝ}
    (hη : ∀ θ ∈ complexStrip n ρ, ‖K θ - unperturbedTorus I θ‖ ≤ η) (x x' : Fin n → ℝ) :
    ‖(realRestriction K x - (x, I)) - (realRestriction K x' - (x', I))‖ ≤
      n * (ρ / 2)⁻¹ * η * ‖x - x'‖ := by
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη 0 (fun i => by simpa using hρ))
  have hC : 0 ≤ (n : ℝ) * (ρ / 2)⁻¹ * η := by positivity
  have hd : ∀ y : Fin n → ℝ, HasFDerivAt (fun z => realRestriction K z - (z, I))
      (fderiv ℝ (realRestriction K) y - ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)) y := by
    intro y
    have h1 := (realRestriction_fderiv hρ hK hKr y).1.hasFDerivAt
    have h2 : HasFDerivAt (fun z : Fin n → ℝ => (z, I))
        (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)) y :=
      (hasFDerivAt_id y).prodMk (hasFDerivAt_const I y)
    exact h1.sub h2
  have key := (convex_univ (𝕜 := ℝ) (E := Fin n → ℝ)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => realRestriction K z - (z, I)) (C := (n : ℝ) * (ρ / 2)⁻¹ * η)
    (f' := fun y => fderiv ℝ (realRestriction K) y -
      ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))
    (fun y _ => (hd y).hasFDerivWithinAt)
    (fun y _ => ContinuousLinearMap.opNorm_le_bound _ hC fun v => by
      simpa using realDisp_fderiv_le hρ hK hKr hη y v)
    (Set.mem_univ x') (Set.mem_univ x)
  simpa using key

end RealDisp

section GoodActions

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε γ : ℝ} {gc : GConsts}

theorem disp_of_mem_good {I : Fin n → ℝ} (hI : I ∈ goodActions h B τ γ) (θ : Fin n → ℝ) :
    disp τ s₀ r₀ B h f gc ε γ (θ, I) =
      realRestriction (normTorus τ s₀ r₀ B h f gc ε γ (frequencyMap h I)) θ - (θ, I) := by
  unfold disp
  exact Set.indicator_of_mem (s := Set.univ ×ˢ goodActions h B τ γ) ⟨trivial, hI⟩ _

theorem disp_of_notMem_good {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z.2 ∉ goodActions h B τ γ) :
    disp τ s₀ r₀ B h f gc ε γ z = 0 := by
  unfold disp
  exact Set.indicator_of_notMem (fun hmem => hz hmem.2) _

/-- Blueprint `bp:p4:good-actions` (the claim after the definition). -/
theorem good_actions (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    ∀ I ∈ goodActions h B τ γ,
      frequencyMap h I ∈ OmegaGamma h B τ γ ∧ invFreq h B (frequencyMap h I) = I ∧
      ∀ θ : Fin n → ℝ, realInclusion₂ n (disp τ s₀ r₀ B h f gc ε γ (θ, I)) =
        normDisp τ s₀ r₀ B h f gc ε γ (frequencyMap h I) (fun i => (θ i : ℂ)) := by
  intro I hI
  have hI' : I ∈ goodActions h B τ γ := hI
  obtain ⟨hIB, -, hdio⟩ := hI
  have hω : frequencyMap h I ∈ OmegaGamma h B τ γ := ⟨⟨I, hIB, rfl⟩, hdio⟩
  have hinv : invFreq h B (frequencyMap h I) = I := (inverse_freq hD).2.2.2.2 I hIB
  refine ⟨hω, hinv, fun θ => ?_⟩
  obtain ⟨-, -, hKr, -⟩ := normalize hD hP hgc hSA hω
  have e : realInclusion₂ n (realRestriction (normTorus τ s₀ r₀ B h f gc ε γ (frequencyMap h I))
      θ) = normTorus τ s₀ r₀ B h f gc ε γ (frequencyMap h I) (fun i => (θ i : ℂ)) :=
    (isRealOnReals_iff.mp hKr θ).symm
  rw [disp_of_mem_good hI', map_sub, e, normDisp, hinv]
  rfl

theorem eta0_nonneg (hD : Data τ s₀ r₀ B h Lh) (hgc : gc.Pos) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    0 ≤ eta0 n τ s₀ r₀ gc ε γ := by
  have hA0 := Parameters.A0_pos (n := n) (τ := τ) hD.s₀_pos hD.r₀_pos hgc
  have := hSA.eps_nonneg
  unfold eta0
  positivity

theorem disjoint_goodActions_layerSet (hγ : 0 < γ) :
    Disjoint (goodActions h B τ γ) (layerSet B γ) := by
  rw [Set.disjoint_left]
  intro I hI hZ
  have h1 : 2 * γ ≤ Metric.infDist I Bᶜ := hI.2.1
  have h2 : Metric.infDist I Bᶜ ≤ γ := hZ
  linarith

/-- `‖disp‖ ≤ η₀` everywhere. -/
theorem norm_disp_le (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ‖disp τ s₀ r₀ B h f gc ε γ z‖ ≤ eta0 n τ s₀ r₀ gc ε γ := by
  by_cases hz : z.2 ∈ goodActions h B τ γ
  · obtain ⟨hω, -, hdisp⟩ := good_actions hD hP hgc hSA z.2 hz
    obtain ⟨-, -, -, -, -, -, -, hW⟩ := normalize hD hP hgc hSA hω
    have hρ : 0 < stripWidth s₀ / 8 := by have := stripWidth_pos hD.s₀_pos; positivity
    have := hW (fun i => (z.1 i : ℂ)) (realInclusion_mem_complexStrip hρ z.1)
    rw [← norm_realInclusion₂, show z = (z.1, z.2) from rfl, hdisp]
    exact this
  · rw [disp_of_notMem_good hz, norm_zero]
    exact eta0_nonneg hD hgc.toPos hSA

/-- `‖Dk - Dk⁰‖` in the form used by `map_lipschitz`: `n (s/16)⁻¹ η₀ = A₄ ε γ⁻²`. -/
theorem realDisp_const_eq (hD : Data τ s₀ r₀ B h Lh) (hγ : 0 < γ) :
    (n : ℝ) * (stripWidth s₀ / 8 / 2)⁻¹ * eta0 n τ s₀ r₀ gc ε γ =
      A4 n τ s₀ r₀ gc * (ε / γ ^ 2) := by
  have hs := stripWidth_pos hD.s₀_pos
  unfold A4 eta0
  field_simp
  ring

/-- Step `step:p4:ml-good` for two good actions, given the conclusion of `lip`. -/
theorem disp_sub_le_good_good (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ)
    (hlip : ∀ ω ∈ OmegaGamma h B τ γ, ∀ ω' ∈ OmegaGamma h B τ γ,
      ∀ θ ∈ complexStrip n (stripWidth s₀ / 32),
        ‖normDisp τ s₀ r₀ B h f gc ε γ ω' θ - normDisp τ s₀ r₀ B h f gc ε γ ω θ‖ ≤
          A3 τ s₀ r₀ B h Lh gc * ε / γ ^ 4 * ‖ω' - ω‖)
    {z z' : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z.2 ∈ goodActions h B τ γ)
    (hz' : z'.2 ∈ goodActions h B τ γ) :
    ‖disp τ s₀ r₀ B h f gc ε γ z - disp τ s₀ r₀ B h f gc ε γ z'‖ ≤ 1 / 4 * ‖z - z'‖ := by
  have hs₀ := hD.s₀_pos
  have hr₀ := hD.r₀_pos
  have hs := stripWidth_pos hs₀
  have hγ := hSA.gamma_pos
  have hρ : 0 < stripWidth s₀ / 8 := by positivity
  have hρ32 : 0 < stripWidth s₀ / 32 := by positivity
  obtain ⟨hω, hinv, hdisp⟩ := good_actions hD hP hgc hSA z.2 hz
  obtain ⟨hω', hinv', hdisp'⟩ := good_actions hD hP hgc hSA z'.2 hz'
  obtain ⟨hKd, -, hKr, -, -, -, -, hW⟩ := normalize hD hP hgc hSA hω
  have hW' : ∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      ‖normTorus τ s₀ r₀ B h f gc ε γ (frequencyMap h z.2) θ - unperturbedTorus z.2 θ‖ ≤
        eta0 n τ s₀ r₀ gc ε γ := by
    intro θ hθ
    have := hW θ hθ
    rwa [normDisp, hinv] at this
  -- the first term: the angle variable moves, the action is fixed
  have h1 : ‖disp τ s₀ r₀ B h f gc ε γ z - disp τ s₀ r₀ B h f gc ε γ (z'.1, z.2)‖ ≤
      A4 n τ s₀ r₀ gc * (ε / γ ^ 2) * ‖z.1 - z'.1‖ := by
    rw [show z = (z.1, z.2) from rfl, disp_of_mem_good hz, disp_of_mem_good hz]
    have := realDisp_lipschitz hρ hKd hKr hW' z.1 z'.1
    rwa [realDisp_const_eq hD hγ] at this
  -- the second term: the frequency moves, the angle is fixed
  have h2 : ‖disp τ s₀ r₀ B h f gc ε γ (z'.1, z.2) - disp τ s₀ r₀ B h f gc ε γ z'‖ ≤
      A3 τ s₀ r₀ B h Lh gc * (ε / γ ^ 4) * LambdaG s₀ r₀ B h * ‖z.2 - z'.2‖ := by
    rw [← norm_realInclusion₂, map_sub, hdisp z'.1, show z' = (z'.1, z'.2) from rfl, hdisp' z'.1,
      norm_sub_rev]
    have hl := hlip _ hω _ hω' _ (realInclusion_mem_complexStrip hρ32 z'.1)
    refine hl.trans ?_
    rw [mul_div_assoc, norm_sub_rev]
    have hΛ := (freq_map hD).2.2.2.2.1 z.2 hz.1 z'.2 hz'.1
    have hA3 : 0 ≤ A3 τ s₀ r₀ B h Lh gc * (ε / γ ^ 4) :=
      mul_nonneg (Parameters.A3_pos hs₀ hr₀ hgc.toPos).le
        (div_nonneg hSA.eps_nonneg (pow_pos hγ 4).le)
    calc _ ≤ A3 τ s₀ r₀ B h Lh gc * (ε / γ ^ 4) *
          (LambdaG s₀ r₀ B h * ‖z.2 - z'.2‖) := mul_le_mul_of_nonneg_left hΛ hA3
      _ = _ := by ring
  have hs6 := (smallness hD hgc.toPos hSA).2.2.2.2.2.1
  have hε4 : 0 ≤ ε / γ ^ 4 := div_nonneg hSA.eps_nonneg (pow_pos hγ 4).le
  have hε24 : ε / γ ^ 2 ≤ ε / γ ^ 4 := by
    rw [div_le_div_iff₀ (pow_pos hγ 2) (pow_pos hγ 4)]
    have : γ ^ 4 ≤ γ ^ 2 := pow_le_pow_of_le_one hγ.le hSA.gamma_le (by norm_num)
    exact mul_le_mul_of_nonneg_left this hSA.eps_nonneg
  have hA4 := (Parameters.A4_pos (τ := τ) hs₀ hr₀ hD.two_le hgc.toPos).le
  have hA3 := (Parameters.A3_pos (n := n) (τ := τ) (B := B) (h := h) (Lh := Lh) hs₀ hr₀
    hgc.toPos).le
  have hΛ0 := Parameters.LambdaG_nonneg (B := B) (h := h) hs₀ hr₀
  have hN1 : ‖z.1 - z'.1‖ ≤ ‖z - z'‖ := norm_fst_le (z - z')
  have hN2 : ‖z.2 - z'.2‖ ≤ ‖z - z'‖ := norm_snd_le (z - z')
  calc ‖disp τ s₀ r₀ B h f gc ε γ z - disp τ s₀ r₀ B h f gc ε γ z'‖
      = ‖(disp τ s₀ r₀ B h f gc ε γ z - disp τ s₀ r₀ B h f gc ε γ (z'.1, z.2)) +
        (disp τ s₀ r₀ B h f gc ε γ (z'.1, z.2) - disp τ s₀ r₀ B h f gc ε γ z')‖ := by
          rw [sub_add_sub_cancel]
    _ ≤ A4 n τ s₀ r₀ gc * (ε / γ ^ 2) * ‖z.1 - z'.1‖ +
        A3 τ s₀ r₀ B h Lh gc * (ε / γ ^ 4) * LambdaG s₀ r₀ B h * ‖z.2 - z'.2‖ :=
          (norm_add_le _ _).trans (add_le_add h1 h2)
    _ ≤ A4 n τ s₀ r₀ gc * (ε / γ ^ 4) * ‖z - z'‖ +
        A3 τ s₀ r₀ B h Lh gc * (ε / γ ^ 4) * LambdaG s₀ r₀ B h * ‖z - z'‖ := by
          gcongr
    _ = ((A3 τ s₀ r₀ B h Lh gc * LambdaG s₀ r₀ B h + A4 n τ s₀ r₀ gc) * (ε / γ ^ 4)) *
        ‖z - z'‖ := by ring
    _ ≤ 1 / 4 * ‖z - z'‖ := mul_le_mul_of_nonneg_right hs6 (norm_nonneg _)

/-- Step `step:p4:ml-mixed`: a good action and a boundary-layer action. -/
theorem disp_sub_le_mixed (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ)
    {z z' : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z.2 ∈ goodActions h B τ γ)
    (hz' : z'.2 ∈ layerSet B γ) :
    ‖disp τ s₀ r₀ B h f gc ε γ z - disp τ s₀ r₀ B h f gc ε γ z'‖ ≤ 1 / 2 * ‖z - z'‖ := by
  have hγ := hSA.gamma_pos
  have hz'g : z'.2 ∉ goodActions h B τ γ := fun hg =>
    Set.disjoint_left.1 (disjoint_goodActions_layerSet (h := h) (B := B) (τ := τ) hγ) hg hz'
  rw [disp_of_notMem_good hz'g, sub_zero]
  have hdist : γ ≤ ‖z - z'‖ := by
    have h1 : 2 * γ ≤ Metric.infDist z.2 Bᶜ := hz.2.1
    have h2 : Metric.infDist z'.2 Bᶜ ≤ γ := hz'
    have h3 := Metric.infDist_le_infDist_add_dist (x := z.2) (y := z'.2) (s := Bᶜ)
    rw [dist_eq_norm] at h3
    have h4 : ‖z.2 - z'.2‖ ≤ ‖z - z'‖ := norm_snd_le (z - z')
    linarith
  obtain ⟨-, -, -, -, -, -, hs7⟩ := smallness hD hgc.toPos hSA
  have hmin : min γ 1 ≤ γ := min_le_left _ _
  calc ‖disp τ s₀ r₀ B h f gc ε γ z‖ ≤ eta0 n τ s₀ r₀ gc ε γ := norm_disp_le hD hP hgc hSA z
    _ ≤ γ / 2 := by linarith [hs7.1, hs7.2]
    _ ≤ 1 / 2 * ‖z - z'‖ := by linarith

/-- The assembly of `bp:p4:map-lipschitz` from the conclusion of `bp:p4:lip` (a conditional helper;
`KAM.Head.map_lipschitz` is this lemma applied to `KAM.Head.lip`). -/
theorem map_lipschitz_of_lip (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ)
    (hlip : ∀ ω ∈ OmegaGamma h B τ γ, ∀ ω' ∈ OmegaGamma h B τ γ,
      ∀ θ ∈ complexStrip n (stripWidth s₀ / 32),
        ‖normDisp τ s₀ r₀ B h f gc ε γ ω' θ - normDisp τ s₀ r₀ B h f gc ε γ ω θ‖ ≤
          A3 τ s₀ r₀ B h Lh gc * ε / γ ^ 4 * ‖ω' - ω‖) :
    Disjoint (goodActions h B τ γ) (layerSet B γ) ∧
    (∀ z, ‖disp τ s₀ r₀ B h f gc ε γ z‖ ≤ eta0 n τ s₀ r₀ gc ε γ) ∧
    ∀ z ∈ (Set.univ ×ˢ (goodActions h B τ γ ∪ layerSet B γ)),
      ∀ z' ∈ (Set.univ ×ˢ (goodActions h B τ γ ∪ layerSet B γ)),
        ‖disp τ s₀ r₀ B h f gc ε γ z - disp τ s₀ r₀ B h f gc ε γ z'‖ ≤ 1 / 2 * ‖z - z'‖ := by
  have hγ := hSA.gamma_pos
  refine ⟨disjoint_goodActions_layerSet hγ, norm_disp_le hD hP hgc hSA, ?_⟩
  rintro z ⟨-, hz⟩ z' ⟨-, hz'⟩
  have hZ : ∀ {w : (Fin n → ℝ) × (Fin n → ℝ)}, w.2 ∈ layerSet B γ →
      disp τ s₀ r₀ B h f gc ε γ w = 0 := fun hw =>
    disp_of_notMem_good fun hg =>
      Set.disjoint_left.1 (disjoint_goodActions_layerSet (h := h) (B := B) (τ := τ) hγ) hg hw
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · exact (disp_sub_le_good_good hD hP hgc hSA hlip hz hz').trans
      (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
  · exact disp_sub_le_mixed hD hP hgc hSA hz hz'
  · rw [norm_sub_rev, norm_sub_rev z]
    exact disp_sub_le_mixed hD hP hgc hSA hz' hz
  · rw [hZ hz, hZ hz', sub_zero, norm_zero]
    positivity

/-- Blueprint `bp:p4:map-lipschitz`. -/
theorem map_lipschitz (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    Disjoint (goodActions h B τ γ) (layerSet B γ) ∧
    (∀ z, ‖disp τ s₀ r₀ B h f gc ε γ z‖ ≤ eta0 n τ s₀ r₀ gc ε γ) ∧
    ∀ z ∈ (Set.univ ×ˢ (goodActions h B τ γ ∪ layerSet B γ)),
      ∀ z' ∈ (Set.univ ×ˢ (goodActions h B τ γ ∪ layerSet B γ)),
        ‖disp τ s₀ r₀ B h f gc ε γ z - disp τ s₀ r₀ B h f gc ε γ z'‖ ≤ 1 / 2 * ‖z - z'‖ :=
  map_lipschitz_of_lip hD hP hgc hSA (lip hD hP hgc hSA)

end GoodActions

end KAM.Head

end
