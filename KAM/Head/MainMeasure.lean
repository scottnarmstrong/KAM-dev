/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.GoodActions
public import KAM.Frozen.Defs.FundamentalDomain
import KAM.Head.Frequency
import KAM.Head.Parameters
import KAM.Head.PreimageMeasure
import KAM.Measure.Lipeo
import KAM.Measure.Lipschitz
import KAM.Measure.McShane

/-!
# The measure of the complement at a given `γ`

Blueprint Part 4, `bp:p4:main-measure`. Under `(SA)` and `B ≠ ∅`,
`meas (F_B ∖ 𝒦(η₀)) ≤ C_meas γ` with `C_meas = 2 C_B⁺ + (9/2)ⁿ (2 C_B⁺ + L₊ⁿ C₃⁺)`.

* `KAM.Head.measure_diff_le_of_displacement`: the measure-theoretic half of the proof, for an
  abstract displacement `G₀` (steps `step:p4:mm-extension`, `step:p4:mm-complement` and the image
  bound of `step:p4:mm-count`). McShane's formula (`KAM.mcshane_prod`) extends `G₀` to a
  `1/2`-Lipschitz `Ḡ` with `‖Ḡ‖ ≤ η₀ ≤ 1/2`; `Ψ = id + Ḡ` is a bijection that is `3/2`-Lipschitz and
  maps `ℝⁿ × Zᶜ` onto itself (`KAM.lipeo_half`); a point of `F_B ∖ 𝒦(η₀)` is either in
  `[0,1)ⁿ × (B ∩ Z)` or in `Ψ([-1/2, 3/2]ⁿ × (Zᶜ ∖ A_γ))`, and the image is measured by
  `KAM.lip_image_prod` with `Λ = 3/2`.
* `KAM.Head.main_measure`: the application. Good actions lie on tori by `real_torus`, the bad
  actions are covered by the boundary layer (step `step:p4:mm-bad`) and by
  `KAM.Head.preimage_measure` applied to the G3 field of `GValid`; `measure_count_eq` is the
  arithmetic of `step:p4:mm-count`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace KAM.Head

section Abstract

variable {n : ℕ}

/-- The cube `[-1/2, 3/2]ⁿ` has volume `2ⁿ`. -/
theorem volume_cubeHalf (n : ℕ) :
    volume (Set.pi Set.univ fun _ : Fin n => Set.Icc (-(1 / 2 : ℝ)) (3 / 2)) =
      ENNReal.ofReal (2 ^ n) := by
  rw [volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- Steps `step:p4:mm-extension`, `step:p4:mm-complement` and the image half of
`step:p4:mm-count`: an abstract version of the measure estimate. If a displacement `G₀` is
bounded by `η ≤ 1/2`, `1/2`-Lipschitz on `ℝⁿ × (A ∪ Z)`, zero on `ℝⁿ × Z`, and `(θ, I) + G₀(θ, I)`
lies in `Cover` for `I ∈ A`, then `F_B ∖ Cover` lies in `[0,1)ⁿ × (B ∩ Z)` and the image of
`[-1/2, 3/2]ⁿ × (Zᶜ ∖ A)` under a `3/2`-Lipschitz map. -/
theorem measure_diff_le_of_displacement {B Z A : Set (Fin n → ℝ)}
    {Cover : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    {G0 : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} {η : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (hbound : ∀ z, ‖G0 z‖ ≤ η)
    (hlip : ∀ z ∈ Set.univ ×ˢ (A ∪ Z), ∀ z' ∈ Set.univ ×ˢ (A ∪ Z),
      ‖G0 z - G0 z'‖ ≤ 1 / 2 * ‖z - z'‖)
    (hGZ : ∀ z ∈ Set.univ ×ˢ Z, G0 z = 0)
    (hcover : ∀ z ∈ Set.univ ×ˢ A, z + G0 z ∈ Cover) :
    volume (fundamentalDomain B \ Cover) ≤
      volume (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1) ×ˢ (B ∩ Z)) +
        ENNReal.ofReal ((3 / 2) ^ (2 * n)) * (ENNReal.ofReal (2 ^ n) * volume (Zᶜ \ A)) := by
  set S : Set ((Fin n → ℝ) × (Fin n → ℝ)) := Set.univ ×ˢ (A ∪ Z) with hS
  -- McShane extension
  obtain ⟨Gb, hGbLip, hGbS, hGbB⟩ := (mcshane_prod (X := (Fin n → ℝ) × (Fin n → ℝ)) (S := S)
    (Λ := 1 / 2) (by norm_num) (φ := G0) (fun x hx y hy => by
      rw [← dist_eq_norm]; exact hlip x hx y hy)).2 η hη0 fun x _ => hbound x
  have hGb : ∀ x y, ‖Gb x - Gb y‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ := fun x y => by
    rw [← dist_eq_norm]; exact hGbLip x y
  -- the lipeomorphism
  obtain ⟨-, hup, -, hfix⟩ := lipeo_half hGb
  have hGbZ : ∀ x ∈ Set.univ ×ˢ Z, Gb x = 0 := fun x hx => by
    rw [hGbS x ⟨trivial, Or.inr hx.2⟩]; exact hGZ x hx
  have himg := hfix _ hGbZ
  -- the covering of the complement
  set Q : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-(1 / 2 : ℝ)) (3 / 2) with hQ
  have hsub : fundamentalDomain B \ Cover ⊆
      (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1) ×ˢ (B ∩ Z)) ∪
        (fun x => x + Gb x) '' (Q ×ˢ (Zᶜ \ A)) := by
    rintro y ⟨⟨hy1, hy2⟩, hyc⟩
    by_cases hZy : y.2 ∈ Z
    · exact Or.inl ⟨hy1, hy2, hZy⟩
    · right
      have hy : y ∈ (Set.univ ×ˢ Z)ᶜ := fun hm => hZy hm.2
      rw [← himg] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx2 : x.2 ∉ Z := fun hm => hx ⟨trivial, hm⟩
      have hxA : x.2 ∉ A := fun hm => by
        apply hyc
        have := hcover x ⟨trivial, hm⟩
        rwa [← hGbS x ⟨trivial, Or.inl hm⟩] at this
      refine ⟨x, ⟨fun i _ => ?_, hx2, hxA⟩, rfl⟩
      have h1 : ‖(Gb x).1 i‖ ≤ 1 / 2 :=
        ((norm_le_pi_norm (Gb x).1 i).trans ((norm_fst_le (Gb x)).trans (hGbB x))).trans hη
      rw [Real.norm_eq_abs, abs_le] at h1
      have h2 := hy1 i (Set.mem_univ i)
      have h3 : (x + Gb x).1 i = x.1 i + (Gb x).1 i := rfl
      rw [h3] at h2
      constructor <;> linarith [h2.1, h2.2]
  -- the measure count
  have hImg : volume ((fun x => x + Gb x) '' (Q ×ˢ (Zᶜ \ A))) ≤
      ENNReal.ofReal ((3 / 2) ^ (2 * n)) * volume (Q ×ˢ (Zᶜ \ A)) :=
    lip_image_prod fun x _ y _ => by
      have := hup x y
      simpa using this
  rw [Measure.volume_eq_prod, Measure.prod_prod, ← Measure.volume_eq_prod] at hImg
  rw [hQ, volume_cubeHalf] at hImg
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hImg))

end Abstract

section MainMeasure

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε γ : ℝ} {gc : GConsts}

/-- The arithmetic of `step:p4:mm-count` in `ℝ≥0∞`. -/
theorem measure_count_eq (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal x + ENNReal.ofReal ((3 / 2) ^ (2 * n)) *
        (ENNReal.ofReal (2 ^ n) * (ENNReal.ofReal x + ENNReal.ofReal y)) =
      ENNReal.ofReal (x + (9 / 2) ^ n * (x + y)) := by
  have hpq : ((3 / 2 : ℝ) ^ (2 * n)) * 2 ^ n = (9 / 2) ^ n := by
    rw [pow_mul, ← mul_pow]; norm_num
  rw [← ENNReal.ofReal_add hx hy, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hx (by positivity)]
  congr 1
  rw [← mul_assoc, hpq]

/-- Blueprint `bp:p4:main-measure`. -/
theorem main_measure {CB : ℝ} (hD : Data τ s₀ r₀ B h Lh) (hCB : Layer B CB)
    (hP : Pert s₀ r₀ B f ε) (hgc : GValid τ s₀ r₀ B h Lh gc)
    (hSA : SA τ s₀ r₀ B h Lh gc ε γ) (hne : B.Nonempty) :
    volume (fundamentalDomain B \ kamCover h f B r₀ τ (eta0 n τ s₀ r₀ gc ε γ)) ≤
      ENNReal.ofReal (Cmeas n Lh CB gc.C3 * γ) := by
  -- `B ≠ ∅` is a blueprint premise that the proof does not use
  have _ := hne
  have hγ := hSA.gamma_pos
  obtain ⟨hdisj, hbd, hlip⟩ := map_lipschitz hD hP hgc hSA
  have hη0 := eta0_nonneg hD hgc.toPos hSA
  have hη : eta0 n τ s₀ r₀ gc ε γ ≤ 1 / 2 := by
    obtain ⟨-, -, -, -, -, -, hs7⟩ := smallness hD hgc.toPos hSA
    linarith [hs7.1, hs7.2, min_le_right γ 1]
  have hGZ : ∀ z ∈ Set.univ ×ˢ layerSet B γ, disp τ s₀ r₀ B h f gc ε γ z = 0 := fun z hz =>
    disp_of_notMem_good fun hg => Set.disjoint_left.1 hdisj hg hz.2
  have hcover : ∀ z ∈ Set.univ ×ˢ goodActions h B τ γ,
      z + disp τ s₀ r₀ B h f gc ε γ z ∈ kamCover h f B r₀ τ (eta0 n τ s₀ r₀ gc ε γ) := by
    rintro ⟨θ, I⟩ ⟨-, hI⟩
    obtain ⟨hω, -, -⟩ := good_actions hD hP hgc hSA I hI
    refine (real_torus hD hP hgc hSA hω).2.2.2.2 ⟨θ, ?_⟩
    rw [disp_of_mem_good hI]
    exact (add_sub_cancel _ _).symm
  have habs := measure_diff_le_of_displacement (B := B) hη0 hη hbd hlip hGZ hcover
  refine habs.trans ?_
  -- the bad sets
  have hY : volume {I ∈ B | Metric.infDist I Bᶜ < 2 * γ} ≤
      ENNReal.ofReal (2 * CBplus CB * γ) :=
    (hCB (2 * γ) (by positivity)).trans (ENNReal.ofReal_le_ofReal (by
      have := le_CBplus CB; nlinarith))
  have hBad := preimage_measure hD hgc.g3 γ hγ
  have hBZ : B ∩ layerSet B γ ⊆ {I ∈ B | Metric.infDist I Bᶜ < 2 * γ} := fun I hI =>
    ⟨hI.1, by have : Metric.infDist I Bᶜ ≤ γ := hI.2; linarith⟩
  have hZA : (layerSet B γ)ᶜ \ goodActions h B τ γ ⊆
      {I ∈ B | Metric.infDist I Bᶜ < 2 * γ} ∪
        {I ∈ B | ¬ IsDiophantine γ τ (frequencyMap h I)} := by
    rintro I ⟨hIZ, hIA⟩
    have hIB : I ∈ B := by
      by_contra hnB
      exact hIZ (by
        show Metric.infDist I Bᶜ ≤ γ
        rw [Metric.infDist_zero_of_mem hnB]; exact hγ.le)
    by_cases h2 : Metric.infDist I Bᶜ < 2 * γ
    · exact Or.inl ⟨hIB, h2⟩
    · exact Or.inr ⟨hIB, fun hd => hIA ⟨hIB, not_lt.1 h2, hd⟩⟩
  have hv1 : volume (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1) ×ˢ
      (B ∩ layerSet B γ)) ≤ ENNReal.ofReal (2 * CBplus CB * γ) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    have h1 : volume (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1)) = 1 := by
      simpa using Real.volume_pi_Ico (a := fun _ : Fin n => (0 : ℝ)) (b := fun _ => 1)
    rw [h1, one_mul]
    exact (measure_mono hBZ).trans hY
  have hv2 : volume ((layerSet B γ)ᶜ \ goodActions h B τ γ) ≤
      ENNReal.ofReal (2 * CBplus CB * γ) + ENNReal.ofReal (Lplus Lh ^ n * max gc.C3 0 * γ) :=
    (measure_mono hZA).trans ((measure_union_le _ _).trans (add_le_add hY hBad))
  have hCB0 := CBplus_nonneg CB
  have hL : 0 ≤ Lplus Lh ^ n * max gc.C3 0 * γ :=
    mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_Lplus Lh)) n)
      (le_max_right _ _)) hγ.le
  calc _ ≤ ENNReal.ofReal (2 * CBplus CB * γ) + ENNReal.ofReal ((3 / 2) ^ (2 * n)) *
        (ENNReal.ofReal (2 ^ n) * (ENNReal.ofReal (2 * CBplus CB * γ) +
          ENNReal.ofReal (Lplus Lh ^ n * max gc.C3 0 * γ))) := by gcongr
    _ = ENNReal.ofReal (2 * CBplus CB * γ + (9 / 2) ^ n *
          (2 * CBplus CB * γ + Lplus Lh ^ n * max gc.C3 0 * γ)) :=
        measure_count_eq n (by positivity) hL
    _ = ENNReal.ofReal (Cmeas n Lh CB gc.C3 * γ) := by
        unfold Cmeas; congr 1; ring

end MainMeasure

end KAM.Head

end
