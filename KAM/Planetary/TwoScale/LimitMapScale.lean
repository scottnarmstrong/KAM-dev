/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.Lipschitz
public import KAM.Planetary.TwoScale.Constants
public import KAM.Planetary.Averaging.Setting
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Strip.RealRestriction

/-!
# Two-scale KAM: the rescaled norm and the rescaling maps (`bpP:p3:limitmap`)

The norm `limitmap_data R s (θ, I) = max (2π‖θ‖/s, ‖I‖/R)` of the source's rescaled coordinates
`S(I, θ) = (I/ρ̂₀, 2πθ/s₀)`, and the linear isomorphism `Fin (n + n) → 𝕜 ≃ 𝕜ⁿ × 𝕜ⁿ` realising it
as a max norm, so that `lip_sup` (`N = 2n`) applies in the scaled coordinates. Design package
P23-18.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

/-- Rescaled norm is a function, never a global Pi/Prod instance. Angles first. -/
def limitmap_data {n : ℕ} (R s : ℝ) (z : Phase n) : ℝ := max (‖z.1‖ * (2 * π / s)) (‖z.2‖ / R)

section Scale

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- Scaled coordinates `(ϑ, J) ↦ (s ϑ / 2π, R J)` out of `𝕜^(n+n)`. -/
def unsc (R s : ℝ) (z : Fin (n + n) → 𝕜) : (Fin n → 𝕜) × (Fin n → 𝕜) :=
  (fun i => ((s / (2 * π) : ℝ) : 𝕜) * z (Fin.castAdd n i),
    fun i => (R : 𝕜) * z (Fin.natAdd n i))

/-- Scaled coordinates `(θ, I) ↦ (2π θ / s, I / R)` into `𝕜^(n+n)`. -/
def sc (R s : ℝ) (w : (Fin n → 𝕜) × (Fin n → 𝕜)) : Fin (n + n) → 𝕜 :=
  Fin.append (fun i => ((2 * π / s : ℝ) : 𝕜) * w.1 i) (fun i => ((1 / R : ℝ) : 𝕜) * w.2 i)

theorem sc_unsc {R s : ℝ} (hR : R ≠ 0) (hs : s ≠ 0) (z : Fin (n + n) → 𝕜) :
    sc R s (unsc R s z) = z := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [sc, unsc, Fin.append_left]
    rw [← mul_assoc, ← RCLike.ofReal_mul]
    have : 2 * π / s * (s / (2 * π)) = 1 := by field_simp [Real.pi_ne_zero]
    rw [this]; simp
  · simp only [sc, unsc, Fin.append_right]
    rw [← mul_assoc, ← RCLike.ofReal_mul]
    have : 1 / R * R = 1 := by field_simp
    rw [this]; simp

theorem unsc_sc {R s : ℝ} (hR : R ≠ 0) (hs : s ≠ 0) (w : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    unsc R s (sc R s w) = w := by
  refine Prod.ext ?_ ?_
  · funext i
    simp only [sc, unsc, Fin.append_left]
    rw [← mul_assoc, ← RCLike.ofReal_mul]
    have : s / (2 * π) * (2 * π / s) = 1 := by field_simp [Real.pi_ne_zero]
    rw [this]; simp
  · funext i
    simp only [sc, unsc, Fin.append_right]
    rw [← mul_assoc, ← RCLike.ofReal_mul]
    have : R * (1 / R) = 1 := by field_simp
    rw [this]; simp

theorem unsc_sub (R s : ℝ) (z z' : Fin (n + n) → 𝕜) :
    unsc R s (z - z') = unsc R s z - unsc R s z' := by
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [unsc, mul_sub]

theorem sc_sub (R s : ℝ) (w w' : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    sc R s (w - w') = sc R s w - sc R s w' := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [sc, Fin.append_left, Pi.sub_apply, Prod.fst_sub, mul_sub]
  · simp only [sc, Fin.append_right, Pi.sub_apply, Prod.snd_sub, mul_sub]

theorem norm_append_le {α : Type*} [SeminormedAddCommGroup α] {m : ℕ} (u v : Fin m → α) :
    ‖(Fin.append u v : Fin (m + m) → α)‖ ≤ max ‖u‖ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]; exact (norm_le_pi_norm u i).trans (le_max_left _ _)
  · rw [Fin.append_right]; exact (norm_le_pi_norm v i).trans (le_max_right _ _)

theorem le_norm_append_left {α : Type*} [SeminormedAddCommGroup α] {m : ℕ} (u v : Fin m → α) :
    ‖u‖ ≤ ‖(Fin.append u v : Fin (m + m) → α)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have := norm_le_pi_norm (Fin.append u v : Fin (m + m) → α) (Fin.castAdd m i)
  rwa [Fin.append_left] at this

theorem le_norm_append_right {α : Type*} [SeminormedAddCommGroup α] {m : ℕ} (u v : Fin m → α) :
    ‖v‖ ≤ ‖(Fin.append u v : Fin (m + m) → α)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have := norm_le_pi_norm (Fin.append u v : Fin (m + m) → α) (Fin.natAdd m i)
  rwa [Fin.append_right] at this

theorem norm_ofReal_mul_pi (c : ℝ) (hc : 0 ≤ c) {m : ℕ} (v : Fin m → 𝕜) :
    ‖fun i => ((c : ℝ) : 𝕜) * v i‖ = c * ‖v‖ := by
  have : (fun i => ((c : ℝ) : 𝕜) * v i) = c • v := by
    funext i; simp [RCLike.real_smul_eq_coe_mul]
  rw [this, norm_smul, Real.norm_of_nonneg hc]

/-- The scaled norm is the max norm in the scaled coordinates. -/
theorem norm_sc {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (w : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ‖sc R s w‖ = max (‖w.1‖ * (2 * π / s)) (‖w.2‖ / R) := by
  have h1 : 0 ≤ 2 * π / s := by positivity
  have h2 : 0 ≤ 1 / R := by positivity
  have e1 := norm_ofReal_mul_pi (𝕜 := 𝕜) _ h1 w.1
  have e2 := norm_ofReal_mul_pi (𝕜 := 𝕜) _ h2 w.2
  apply le_antisymm
  · refine (norm_append_le _ _).trans ?_
    rw [e1, e2, mul_comm, one_div, ← div_eq_inv_mul]
  · refine max_le ?_ ?_
    · have := le_norm_append_left (fun i => ((2 * π / s : ℝ) : 𝕜) * w.1 i)
        (fun i => ((1 / R : ℝ) : 𝕜) * w.2 i)
      rw [e1] at this; rw [mul_comm]; exact this
    · have := le_norm_append_right (fun i => ((2 * π / s : ℝ) : 𝕜) * w.1 i)
        (fun i => ((1 / R : ℝ) : 𝕜) * w.2 i)
      rw [e2, one_div, ← div_eq_inv_mul] at this
      simpa only [sc, one_div] using this

theorem limitmap_data_eq_norm_sc {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (w : Phase n) :
    limitmap_data R s w = ‖sc R s w‖ := (norm_sc hR hs w).symm

theorem sc_incl (R s : ℝ) (w : Phase n) :
    sc R s (KAM.realInclusion₂ n w) = KAM.realInclusion (n + n) (sc R s w) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [sc]
  · simp only [sc, Fin.append_right, KAM.realInclusion_apply, KAM.realInclusion₂_apply]
    push_cast; rfl

theorem unsc_incl (R s : ℝ) (z : Fin (n + n) → ℝ) :
    unsc R s (KAM.realInclusion (n + n) z) = KAM.realInclusion₂ n (unsc R s z) := by
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [unsc]

theorem norm_unsc_fst_le {R s : ℝ} (hs : 0 ≤ s) (z : Fin (n + n) → 𝕜) :
    ‖(unsc R s z).1‖ ≤ s / (2 * π) * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [unsc, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (by positivity : 0 ≤ s / (2 * π))]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z _) (by positivity)

theorem norm_unsc_snd_le {R s : ℝ} (hR : 0 ≤ R) (z : Fin (n + n) → 𝕜) :
    ‖(unsc R s z).2‖ ≤ R * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [unsc, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hR]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z _) hR

theorem limitmap_data_nonneg {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (w : Phase n) :
    0 ≤ limitmap_data R s w := by
  rw [limitmap_data_eq_norm_sc hR hs]; exact norm_nonneg _

theorem limitmap_data_sub_le {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (u v : Phase n) :
    limitmap_data R s (u - v) ≤ limitmap_data R s u + limitmap_data R s v := by
  rw [limitmap_data_eq_norm_sc hR hs, sc_sub, limitmap_data_eq_norm_sc hR hs,
    limitmap_data_eq_norm_sc hR hs]
  exact norm_sub_le _ _

theorem limitmap_data_add_le {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (u v : Phase n) :
    limitmap_data R s (u + v) ≤ limitmap_data R s u + limitmap_data R s v := by
  have : u + v = u - (-v) := by abel
  rw [this]
  refine (limitmap_data_sub_le hR hs _ _).trans ?_
  have : limitmap_data R s (-v) = limitmap_data R s v := by
    unfold limitmap_data; simp
  rw [this]

theorem limitmap_data_eq_zero {R s : ℝ} (hR : 0 < R) (hs : 0 < s) {w : Phase n}
    (h : limitmap_data R s w = 0) : w = 0 := by
  rw [limitmap_data_eq_norm_sc hR hs] at h
  have h1 := norm_eq_zero.1 h
  have := unsc_sc (𝕜 := ℝ) hR.ne' hs.ne' w
  rw [← this, h1]
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [unsc]

theorem norm_le_limitmap_data {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (w : Phase n) :
    ‖w‖ ≤ max (s / (2 * π)) R * limitmap_data R s w := by
  have hK1 : 0 ≤ max (s / (2 * π)) R := le_max_of_le_right hR.le
  have h1 : ‖w.1‖ ≤ max (s / (2 * π)) R * limitmap_data R s w := by
    have : ‖w.1‖ * (2 * π / s) ≤ limitmap_data R s w := le_max_left _ _
    have h2 : ‖w.1‖ = s / (2 * π) * (‖w.1‖ * (2 * π / s)) := by field_simp
    rw [h2]
    exact mul_le_mul (le_max_left _ _) this (by positivity) hK1
  have h2 : ‖w.2‖ ≤ max (s / (2 * π)) R * limitmap_data R s w := by
    have : ‖w.2‖ / R ≤ limitmap_data R s w := le_max_right _ _
    have h3 : ‖w.2‖ = R * (‖w.2‖ / R) := by field_simp
    rw [h3]
    exact mul_le_mul (le_max_right _ _) this (by positivity) hK1
  exact max_le h1 h2

end Scale

end KAM.Planetary

end
