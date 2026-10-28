/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.MeasureActions
public import KAM.Planetary.TwoScale.MeasureScaled

/-!
# Two-scale KAM: the private conditional helper `meas_torus_of_limit` (`bpP:p3:meas-torus`)

Packages `stepP:p3:mt-split`, `mt-ext`, `mt-pre`, `mt-meas`, `mt-shell`, `mt-sum`. `TorusMeas`
bundles the proved outputs of `limit_actions_of_steps` and `limit_phi_real_of_steps` on the shared
witnesses (`i`, `Φ`, `D_* = i '' D₀`); the helper is conditional on it and is discharged by
`meas_of_iterative` (design finding N2, package P23-21).

The complement of `K_Ω = Φ(ℝⁿ × D_*)` in the angle cell over the open real tube `realTube D r`
is covered by the cell over `realTube D r ∖ D_*` and by the image under the rescaled cover `Φ_e`
of the enlarged cell times the closed shell `N_{ρ₂}(D_*) ∖ D_*` (existential distance
`∃ J ∈ D_*, ‖x - J‖ ≤ ρ₂`). Both pieces are controlled by `meas(realTube D r ∖ D_*)`, and the
total is at most `complementConstant n` times `a + b`.
-/

@[expose] public noncomputable section

open Set MeasureTheory Real

namespace KAM.Planetary

variable {n : ℕ} {D D₀ : Set (Fin n → ℝ)} {i : (Fin n → ℝ) → (Fin n → ℝ)}
  {Φ : Phase n → Phase n} {Ehat Rhat s : ℝ}

/-- The proved outputs of `limit_actions_of_steps` and `limit_phi_real_of_steps` used by the
measure estimate on the torus complement: the action data, `s ≤ 1/4`, `Ê ≤ 1/8`, the rescaled
defect constant `768 n Ê < 1/10` and the rescaled displacement `3/2 Ê` on `ℝⁿ × D_*`. -/
structure TorusMeas (D D₀ : Set (Fin n → ℝ)) (i : (Fin n → ℝ) → (Fin n → ℝ))
    (Φ : Phase n → Phase n) (Ehat Rhat s : ℝ) : Prop where
  acts : ActionsMeas D D₀ i Ehat Rhat
  R_pos : 0 < Rhat
  s_pos : 0 < s
  s_le : s ≤ 1 / 4
  E_le : Ehat ≤ 1 / 8
  lip : ∀ x ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)), ∀ y ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)),
    limitmap_data Rhat s ((Φ x - x) - (Φ y - y)) ≤
      768 * (n : ℝ) * Ehat * limitmap_data Rhat s (x - y)
  small : 768 * (n : ℝ) * Ehat < 1 / 10
  sup : ∀ x ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)),
    limitmap_data Rhat s (Φ x - x) ≤ 3 / 2 * Ehat

/-- `volume` of the angle box `∏ [a, b)`. -/
theorem volume_box (a b : ℝ) (hab : a ≤ b) :
    volume {θ : Fin n → ℝ | ∀ j, θ j ∈ Ico a b} = ENNReal.ofReal ((b - a) ^ n) := by
  have : {θ : Fin n → ℝ | ∀ j, θ j ∈ Ico a b} = Set.pi univ fun _ => Ico a b := by
    ext θ; simp
  rw [this, Real.volume_pi_Ico]
  simp [ENNReal.ofReal_pow (sub_nonneg.2 hab)]

namespace TorusMeas

variable (T : TorusMeas D D₀ i Φ Ehat Rhat s)
include T

/-- `realTube D r ∖ D_*` is controlled by `a + b` (`stepP:p3:mt-split`, `mt-shell`). -/
theorem volume_tube_diff :
    volume (realTube D (32 * Ehat * Rhat) \ i '' D₀) ≤
      ENNReal.ofReal (1 + (4 / 3 : ℝ) ^ n) *
        (volume (D \ D₀) + volume (realTube D (32 * Ehat * Rhat) \ D)) := by
  have hA := (meas_actions_of_limit T.acts).1
  have hsub : realTube D (32 * Ehat * Rhat) \ i '' D₀ ⊆
      (realTube D (32 * Ehat * Rhat) \ D) ∪ ((D \ D₀) ∪ (D₀ \ i '' D₀)) := by
    intro x hx
    by_cases hD : x ∈ D
    · by_cases h0 : x ∈ D₀
      · exact Or.inr (Or.inr ⟨h0, hx.2⟩)
      · exact Or.inr (Or.inl ⟨hD, h0⟩)
    · exact Or.inl ⟨hx.1, hD⟩
  set S₀ := volume (D \ D₀) + volume (realTube D (32 * Ehat * Rhat) \ D) with hS₀
  calc volume (realTube D (32 * Ehat * Rhat) \ i '' D₀)
      ≤ volume (realTube D (32 * Ehat * Rhat) \ D) +
          (volume (D \ D₀) + volume (D₀ \ i '' D₀)) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add_right (measure_union_le _ _) _))
    _ ≤ S₀ + ENNReal.ofReal ((4 / 3 : ℝ) ^ n) * S₀ := by
        have : volume (realTube D (32 * Ehat * Rhat) \ D) +
            (volume (D \ D₀) + volume (D₀ \ i '' D₀)) =
            S₀ + volume (D₀ \ i '' D₀) := by rw [hS₀]; ring
        rw [this]; gcongr
    _ = ENNReal.ofReal (1 + (4 / 3 : ℝ) ^ n) * S₀ := by
        rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]; ring

/-- The closed shell `N_{ρ₂}(D_*) ∖ D_*` lies in `realTube D r ∖ D_*` (`stepP:p3:mt-shell`). -/
theorem shell_subset :
    {I | ∃ J ∈ i '' D₀, ‖I - J‖ ≤ 2 * Ehat * Rhat} \ i '' D₀ ⊆
      realTube D (32 * Ehat * Rhat) \ i '' D₀ := by
  rintro x ⟨⟨J, ⟨I, hI, rfl⟩, hxJ⟩, hx⟩
  refine ⟨mem_realTube_of (T.acts.sub hI) ?_, hx⟩
  have h1 := T.acts.bd I hI
  have h2 : ‖x - I‖ ≤ ‖x - i I‖ + ‖i I - I‖ := by
    simpa using norm_add_le (x - i I) (i I - I)
  have := T.acts.pos
  nlinarith

/-- Preimage structure (`stepP:p3:mt-pre`): a point `y ∈ ℝⁿ × D_*` outside `K_Ω` with angle in
the unit cell is `Φ_e` of a point of the enlarged cell times the shell. -/
theorem preimage_mem {Ψ : Phase n → Phase n}
    (hΨ : ∀ x ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)), Ψ x = Φ x)
    {y : Phase n} (hy : y.2 ∈ i '' D₀) (hcell : ∀ j, y.1 j ∈ Ico (0 : ℝ) 1)
    (hKO : y ∉ Φ '' (univ ×ˢ (i '' D₀)))
    {x : Phase n} (hx : Ψ x = y) (hd : limitmap_data Rhat s (x - y) ≤ 2 * Ehat) :
    y ∈ Ψ '' ({θ : Fin n → ℝ | ∀ j, θ j ∈ Ico (-(Ehat * s / π)) (1 + Ehat * s / π)} ×ˢ
      ({I | ∃ J ∈ i '' D₀, ‖I - J‖ ≤ 2 * Ehat * Rhat} \ i '' D₀)) := by
  have hR := T.R_pos
  have hs := T.s_pos
  refine ⟨x, ⟨?_, ?_, ?_⟩, hx⟩
  · intro j
    have h1 : ‖x.1 - y.1‖ * (2 * π / s) ≤ 2 * Ehat := (le_max_left _ _).trans hd
    have h2 : ‖x.1 - y.1‖ ≤ Ehat * s / π := by
      have hp : 0 < 2 * π / s := by positivity
      calc ‖x.1 - y.1‖ ≤ 2 * Ehat / (2 * π / s) := (le_div_iff₀ hp).2 h1
        _ = Ehat * s / π := by field_simp
    have h3 := (norm_le_pi_norm (x.1 - y.1) j).trans h2
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le] at h3
    have := hcell j
    constructor <;> linarith [this.1, this.2]
  · refine ⟨y.2, hy, ?_⟩
    have h1 : ‖x.2 - y.2‖ / Rhat ≤ 2 * Ehat := (le_max_right _ _).trans hd
    rw [div_le_iff₀ hR] at h1
    simpa [mul_assoc, mul_comm] using h1
  · intro hx2
    exact hKO ⟨x, ⟨trivial, hx2⟩, by rw [← hΨ x ⟨trivial, hx2⟩, hx]⟩

/-- **`bpP:p3:meas-torus`** (private conditional helper): the part of the unit angle cell over
the open real tube `realTube D r`, `r = 32 Ê ρ̂`, missing `K_Ω = Φ(ℝⁿ × D_*)` has measure at most
`complementConstant n · (a + b)`. -/
theorem meas_torus_of_limit :
    volume (((univ ×ˢ realTube D (32 * Ehat * Rhat) : Set (Phase n)) \
        Φ '' (univ ×ˢ (i '' D₀))) ∩ {z : Phase n | ∀ j, z.1 j ∈ Ico (0 : ℝ) 1}) ≤
      ENNReal.ofReal (complementConstant n) *
        (volume (D \ D₀) + volume (realTube D (32 * Ehat * Rhat) \ D)) := by
  have hR := T.R_pos
  have hs := T.s_pos
  have hE0 := T.acts.E_nonneg
  have hlam0 : 0 ≤ 768 * (n : ℝ) * Ehat := by positivity
  set lam := 768 * (n : ℝ) * Ehat with hlam
  have hlam1 := T.small
  set ε := Ehat * s / π with hε
  have hε0 : 0 ≤ ε := by positivity
  have hπ := Real.pi_gt_three
  have hε1 : ε ≤ 1 / 96 := by
    rw [hε, div_le_iff₀ (by positivity)]
    nlinarith [T.s_le, T.E_le, mul_nonneg hE0 hs.le]
  obtain ⟨Ψ, hΨX, hΨlip, hΨinv⟩ := scaled_cover (n := n) (R := Rhat) (s := s) (lam := lam)
    (eta := 3 / 2 * Ehat) hR hs ⟨hlam0, by linarith⟩ (by positivity) T.lip T.sup
  have hΨinv' : ∀ y ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)), ∃ x, Ψ x = y ∧
      limitmap_data Rhat s (x - y) ≤ 2 * Ehat := by
    intro y hy
    obtain ⟨x, hx, hd⟩ := hΨinv y hy
    refine ⟨x, hx, hd.trans ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  set W := realTube D (32 * Ehat * Rhat) \ i '' D₀ with hW
  set S₀ := volume (D \ D₀) + volume (realTube D (32 * Ehat * Rhat) \ D) with hS₀
  have hWvol := T.volume_tube_diff
  set Cε : Set (Fin n → ℝ) := {θ | ∀ j, θ j ∈ Ico (-ε) (1 + ε)} with hCε
  set N : Set (Fin n → ℝ) := {I | ∃ J ∈ i '' D₀, ‖I - J‖ ≤ 2 * Ehat * Rhat} with hN
  set cell0 : Set (Fin n → ℝ) := {θ | ∀ j, θ j ∈ Ico (0 : ℝ) 1} with hcell0
  have hcover : ((univ ×ˢ realTube D (32 * Ehat * Rhat) : Set (Phase n)) \
        Φ '' (univ ×ˢ (i '' D₀))) ∩ {z : Phase n | ∀ j, z.1 j ∈ Ico (0 : ℝ) 1} ⊆
      cell0 ×ˢ W ∪ Ψ '' (Cε ×ˢ (N \ i '' D₀)) := by
    rintro y ⟨⟨⟨-, hy2⟩, hKO⟩, hcell⟩
    by_cases hy : y.2 ∈ i '' D₀
    · obtain ⟨x, hx, hd⟩ := hΨinv' y ⟨trivial, hy⟩
      exact Or.inr (T.preimage_mem hΨX hy hcell hKO hx hd)
    · exact Or.inl ⟨hcell, hy2, hy⟩
  have h1 : volume (cell0 ×ˢ W) = volume W := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, hcell0, volume_box 0 1 zero_le_one]
    simp
  have h2 : volume (Ψ '' (Cε ×ˢ (N \ i '' D₀))) ≤ ENNReal.ofReal (2 ^ n) * volume W := by
    have hl := lip_image_scaled (n := n) (R := Rhat) (s := s) (Λ := 1 + lam) hR hs
      (S := Cε ×ˢ (N \ i '' D₀)) (F := Ψ) (fun x _ y _ => hΨlip x y)
    refine hl.trans ?_
    rw [Measure.volume_eq_prod, Measure.prod_prod, hCε, volume_box _ _ (by linarith)]
    have hsh : volume (N \ i '' D₀) ≤ volume W := measure_mono T.shell_subset
    have hc : ENNReal.ofReal ((1 + lam) ^ (2 * n)) * ENNReal.ofReal ((1 + ε - -ε) ^ n) ≤
        ENNReal.ofReal (2 ^ n) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (by linarith) _), pow_mul, ← mul_pow]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by nlinarith) ?_ n)
      nlinarith
    calc ENNReal.ofReal ((1 + lam) ^ (2 * n)) *
          (ENNReal.ofReal ((1 + ε - -ε) ^ n) * volume (N \ i '' D₀))
        = (ENNReal.ofReal ((1 + lam) ^ (2 * n)) * ENNReal.ofReal ((1 + ε - -ε) ^ n)) *
          volume (N \ i '' D₀) := by ring
      _ ≤ ENNReal.ofReal (2 ^ n) * volume W := mul_le_mul' hc hsh
  calc _ ≤ volume (cell0 ×ˢ W ∪ Ψ '' (Cε ×ˢ (N \ i '' D₀))) := measure_mono hcover
    _ ≤ volume (cell0 ×ˢ W) + volume (Ψ '' (Cε ×ˢ (N \ i '' D₀))) := measure_union_le _ _
    _ ≤ volume W + ENNReal.ofReal (2 ^ n) * volume W := by rw [h1]; gcongr
    _ = (1 + ENNReal.ofReal (2 ^ n)) * volume W := by ring
    _ ≤ (1 + ENNReal.ofReal (2 ^ n)) * (ENNReal.ofReal (1 + (4 / 3 : ℝ) ^ n) * S₀) := by
        gcongr
    _ = ENNReal.ofReal ((1 + 2 ^ n) * (1 + (4 / 3 : ℝ) ^ n)) * S₀ := by
        rw [← mul_assoc, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add zero_le_one (by positivity : (0 : ℝ) ≤ 2 ^ n),
          ENNReal.ofReal_add zero_le_one (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ n),
          ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (complementConstant n) * S₀ := by
        gcongr
        unfold complementConstant
        linarith

end TorusMeas

end KAM.Planetary

end
