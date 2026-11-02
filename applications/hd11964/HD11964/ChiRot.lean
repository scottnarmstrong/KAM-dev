/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.ChiHD
public import HD11964.Glue

/-!
# HD 11964: the rotation invariance of `F` (HD11964-ROT, piece 1)

The bridge's `hFrot` for `F_i = approxIntegral₂ (castAdd i) χ₁ χ₂`, `χ₁ = χ*(P)`,
`G₂ = {P - ½ Π_S P, χ₁}`, `χ₂ = χ*(G₂)`.

* `chartCoeff_chartRot` (1a): for `P` rotation-invariant and `2π`-periodic in the angles,
  `P̂_k(chartRot θ w) = e(-k·(θ/2π)𝟙) P̂_k(w)` (the coefficient integrand is shifted by `θ/2π` in
  both variables, and the double integral of a `1`-periodic function is shift-invariant).
* `chiStar_rotInv`, `projS_rotInv`, `chiStar_anglePeriodic`, `projS_anglePeriodic` (1b): no
  condition on `S` is needed.
* `pb_comp_eq`, `dirDeriv_comp_eq`, `approxIntegral₂_comp_eq` (1c, 1d): invariance under a map with
  symplectic surjective derivative (`chartRot θ`, `· + fastShift m`), from the core's
  `fderiv_apply_hamiltonianVectorField_comp`.
* `chartPert_rotInv`, `chartPert_anglePeriodic` (1e).
* `FHD` and `rotInv_FHD` (1f): `hFrot` for HD 11964 on `openHD`.
* `noCrossing_HD_of_cellBounds` (1g): `noCrossing_of_cellBounds` with `O = openHD`, `F = FHD`; `hF`,
  `hFrot`, `O ⊆ chartSafe ν` and `R(D.d) ⊆ O` (from `D.d ≤ 1/500`) discharged.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real ContDiff

namespace HD11964.Cover

/-- `f` is invariant under every chart rotation at the points of `U`. -/
def IsRotInvOn {n : ℕ} (U : Set (Phase (n + n))) (f : Phase (n + n) → ℝ) : Prop :=
  ∀ θ : ℝ, ∀ w ∈ U, f (chartRot θ w) = f w

/-- `f` is `2π`-periodic in every fast angle at the points of `U`. -/
def IsAnglePeriodicOn {n : ℕ} (U : Set (Phase (n + n))) (f : Phase (n + n) → ℝ) : Prop :=
  ∀ m : Fin n → ℤ, ∀ w ∈ U, f (w + fastShift (a := n) (b := n) m) = f w

/-! ### Characters -/

theorem charE_add (k : Fin 2 → ℤ) (θ η : Fin 2 → ℂ) : charE k (θ + η) = charE k θ * charE k η := by
  simp only [charE, ← Complex.exp_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem charE_neg_mul (k : Fin 2 → ℤ) (θ : Fin 2 → ℂ) : charE (-k) θ * charE k θ = 1 := by
  simp only [charE, ← Complex.exp_add, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib,
    mul_neg, neg_add_cancel, Complex.exp_zero]

/-- Characters are `1`-periodic: `e(k·(θ + m)) = e(k·θ)` for `m ∈ ℤ²`. -/
theorem charE_add_int (k : Fin 2 → ℤ) (θ : Fin 2 → ℂ) (m : Fin 2 → ℤ) :
    charE k (θ + fun i => (m i : ℂ)) = charE k θ := by
  rw [charE_add]
  have h : charE k (fun i => (m i : ℂ)) = 1 := by
    rw [charE, show (2 * π * Complex.I * ∑ i, (k i : ℂ) * (m i : ℂ)) =
      ((∑ i, k i * m i : ℤ) : ℂ) * (2 * π * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h, mul_one]

/-! ### `withAngles` under the rotation and the lattice -/

theorem chartRot_fst_fast (θ : ℝ) (w : Phase (2 + 2)) (i : Fin 2) :
    fast (chartRot θ w).1 i = fast w.1 i + θ := by
  simp [chartRot, assemble, fast_append']

theorem withAngles_chartRot (θ : ℝ) (w : Phase (2 + 2)) (lam : Fin 2 → ℝ) :
    withAngles (chartRot θ w) lam = chartRot θ (withAngles w fun i => lam i - θ) := by
  simp only [withAngles, chartRot, assemble, fast_append', slow_append', sub_add_cancel]

theorem fastShift_snd (m : Fin 2 → ℤ) : (fastShift (a := 2) (b := 2) m).2 = 0 := rfl

theorem add_fastShift_snd (w : Phase (2 + 2)) (m : Fin 2 → ℤ) :
    (w + fastShift (a := 2) (b := 2) m).2 = w.2 := by
  simp [fastShift_snd]

theorem slow_add_fastShift_fst (w : Phase (2 + 2)) (m : Fin 2 → ℤ) :
    slow (w + fastShift (a := 2) (b := 2) m).1 = slow w.1 := by
  funext j
  simp [fastShift, slow]

theorem fast_add_fastShift_fst (w : Phase (2 + 2)) (m : Fin 2 → ℤ) (i : Fin 2) :
    fast (w + fastShift (a := 2) (b := 2) m).1 i = fast w.1 i + 2 * π * m i := by
  simp [fastShift, fast]

theorem withAngles_add_fastShift (w : Phase (2 + 2)) (m : Fin 2 → ℤ) (lam : Fin 2 → ℝ) :
    withAngles (w + fastShift (a := 2) (b := 2) m) lam = withAngles w lam := by
  simp only [withAngles, add_fastShift_snd, slow_add_fastShift_fst]

theorem withAngles_add_two_pi (w : Phase (2 + 2)) (lam : Fin 2 → ℝ) (m : Fin 2 → ℤ) :
    withAngles w (fun i => lam i + 2 * π * m i) =
      withAngles w lam + fastShift (a := 2) (b := 2) m := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j <;>
  simp [withAngles, assemble, fastShift]

theorem chartCoeff_add_fastShift (P : Phase (2 + 2) → ℝ) (k : Fin 2 → ℤ) (w : Phase (2 + 2))
    (m : Fin 2 → ℤ) : chartCoeff P k (w + fastShift (a := 2) (b := 2) m) = chartCoeff P k w := by
  simp only [chartCoeff, withAngles_add_fastShift]

/-! ### (1a) The Fourier coefficients under the rotation -/

/-- A `1`-periodic function has the same integral over `[0, 1]` after a shift. -/
theorem intervalIntegral_shift_periodic (f : ℝ → ℂ) (hf : Function.Periodic f 1) (c : ℝ) :
    ∫ x in (0 : ℝ)..1, f (x - c) = ∫ x in (0 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => f x) c]
  have h := hf.intervalIntegral_add_eq (-c) 0
  simpa [sub_eq_add_neg, add_comm] using h

/-- A function `1`-periodic in each variable has the same double integral over `[0, 1]²` after a
common shift. -/
theorem iint_shift_periodic (h : ℝ → ℝ → ℂ) (h0 : ∀ s t, h (s + 1) t = h s t)
    (h1 : ∀ s t, h s (t + 1) = h s t) (c : ℝ) :
    ∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1, h (t₀ - c) (t₁ - c) =
      ∫ t₀ in (0 : ℝ)..1, ∫ t₁ in (0 : ℝ)..1, h t₀ t₁ := by
  have inner : ∀ t₀ : ℝ, ∫ t₁ in (0 : ℝ)..1, h (t₀ - c) (t₁ - c) =
      ∫ t₁ in (0 : ℝ)..1, h (t₀ - c) t₁ :=
    fun t₀ => intervalIntegral_shift_periodic (fun t₁ => h (t₀ - c) t₁) (fun t => h1 _ t) c
  simp only [inner]
  exact intervalIntegral_shift_periodic (fun t₀ => ∫ t₁ in (0 : ℝ)..1, h t₀ t₁)
    (fun s => by simp only [h0]) c

theorem vec2_sub_const (t₀ t₁ c : ℝ) :
    (![(t₀ : ℂ), (t₁ : ℂ)] : Fin 2 → ℂ) =
      (fun _ => (c : ℂ)) + ![((t₀ - c : ℝ) : ℂ), ((t₁ - c : ℝ) : ℂ)] := by
  funext i
  fin_cases i <;> simp

/-- **(1a) The Fourier coefficients under the chart rotation.** -/
theorem chartCoeff_chartRot {U : Set (Phase (2 + 2))} {P : Phase (2 + 2) → ℝ} (k : Fin 2 → ℤ)
    (hsat : IsAngleSaturated U) (hP : IsRotInvOn U P) (hper : IsAnglePeriodicOn U P) (θ : ℝ)
    {w : Phase (2 + 2)} (hw : w ∈ U) :
    chartCoeff P k (chartRot θ w) =
      charE (-k) (fun _ => ((θ / (2 * π) : ℝ) : ℂ)) * chartCoeff P k w := by
  set c : ℝ := θ / (2 * π) with hc
  set h : ℝ → ℝ → ℂ := fun s t =>
    (P (withAngles w ![2 * π * s, 2 * π * t]) : ℂ) * charE (-k) ![(s : ℂ), (t : ℂ)] with hh
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have key : ∀ t₀ t₁ : ℝ,
      (P (withAngles (chartRot θ w) ![2 * π * t₀, 2 * π * t₁]) : ℂ) *
        charE (-k) ![(t₀ : ℂ), (t₁ : ℂ)] =
      charE (-k) (fun _ => (c : ℂ)) * h (t₀ - c) (t₁ - c) := by
    intro t₀ t₁
    have e1 : (fun i => (![2 * π * t₀, 2 * π * t₁] : Fin 2 → ℝ) i - θ) =
        ![2 * π * (t₀ - c), 2 * π * (t₁ - c)] := by
      funext i
      fin_cases i <;> simp [hc] <;> field_simp
    rw [withAngles_chartRot, e1, hP θ _ (hsat w hw _), vec2_sub_const t₀ t₁ c, charE_add, hh]
    ring
  have h0 : ∀ s t, h (s + 1) t = h s t := by
    intro s t
    have e : (![2 * π * (s + 1), 2 * π * t] : Fin 2 → ℝ) =
        fun i => (![2 * π * s, 2 * π * t] : Fin 2 → ℝ) i + 2 * π * ((![1, 0] : Fin 2 → ℤ) i) := by
      funext i
      fin_cases i
      · simp; ring
      · simp
    have e' : (![((s + 1 : ℝ) : ℂ), (t : ℂ)] : Fin 2 → ℂ) =
        ![(s : ℂ), (t : ℂ)] + fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℂ) := by
      funext i
      fin_cases i <;> simp
    simp only [hh]
    rw [e, withAngles_add_two_pi, hper _ _ (hsat w hw _), e', charE_add_int]
  have h1 : ∀ s t, h s (t + 1) = h s t := by
    intro s t
    have e : (![2 * π * s, 2 * π * (t + 1)] : Fin 2 → ℝ) =
        fun i => (![2 * π * s, 2 * π * t] : Fin 2 → ℝ) i + 2 * π * ((![0, 1] : Fin 2 → ℤ) i) := by
      funext i
      fin_cases i
      · simp
      · simp; ring
    have e' : (![(s : ℂ), ((t + 1 : ℝ) : ℂ)] : Fin 2 → ℂ) =
        ![(s : ℂ), (t : ℂ)] + fun i => (((![0, 1] : Fin 2 → ℤ) i : ℤ) : ℂ) := by
      funext i
      fin_cases i <;> simp
    simp only [hh]
    rw [e, withAngles_add_two_pi, hper _ _ (hsat w hw _), e', charE_add_int]
  unfold chartCoeff
  simp_rw [key, intervalIntegral.integral_const_mul]
  rw [iint_shift_periodic h h0 h1 c]

/-! ### (1b) `χ*` and `Π_S P` -/

theorem charE_chartRot_angles (k : Fin 2 → ℤ) (θ : ℝ) (w : Phase (2 + 2)) :
    charE k (fun i => ((fast (chartRot θ w).1 i / (2 * π) : ℝ) : ℂ)) =
      charE k (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ)) *
        charE k (fun _ => ((θ / (2 * π) : ℝ) : ℂ)) := by
  rw [← charE_add]
  congr 1
  funext i
  simp only [chartRot_fst_fast, Pi.add_apply]
  push_cast
  ring

/-- **(1b) `χ*` is rotation-invariant** for a rotation-invariant, angle-periodic `P` (no condition
on `S`). -/
theorem chiStar_rotInv {U : Set (Phase (2 + 2))} (S : Finset (Fin 2 → ℤ))
    (frq : (Fin 2 → ℝ) → Fin 2 → ℝ) {P : Phase (2 + 2) → ℝ} (hsat : IsAngleSaturated U)
    (hP : IsRotInvOn U P) (hper : IsAnglePeriodicOn U P) : IsRotInvOn U (chiStar S frq P) := by
  intro θ w hw
  unfold chiStar
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chartCoeff_chartRot k hsat hP hper θ hw, fast_chartRot, charE_chartRot_angles]
  linear_combination (chartCoeff P k w * (Complex.I * ∑ i, (k i : ℂ) * frq (fast w.2) i)⁻¹ *
    charE k (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ))) *
      charE_neg_mul k (fun _ => ((θ / (2 * π) : ℝ) : ℂ))

/-- **(1b) `Π_S P` is rotation-invariant** for a rotation-invariant, angle-periodic `P`. -/
theorem projS_rotInv {U : Set (Phase (2 + 2))} (S : Finset (Fin 2 → ℤ)) {P : Phase (2 + 2) → ℝ}
    (hsat : IsAngleSaturated U) (hP : IsRotInvOn U P) (hper : IsAnglePeriodicOn U P) :
    IsRotInvOn U (projS S P) := by
  intro θ w hw
  unfold projS
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chartCoeff_chartRot k hsat hP hper θ hw, charE_chartRot_angles]
  linear_combination (chartCoeff P k w * charE k (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ))) *
    charE_neg_mul k (fun _ => ((θ / (2 * π) : ℝ) : ℂ))

theorem charE_add_fastShift_angles (k : Fin 2 → ℤ) (w : Phase (2 + 2)) (m : Fin 2 → ℤ) :
    charE k (fun i => ((fast (w + fastShift (a := 2) (b := 2) m).1 i / (2 * π) : ℝ) : ℂ)) =
      charE k (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ)) := by
  have e : (fun i => ((fast (w + fastShift (a := 2) (b := 2) m).1 i / (2 * π) : ℝ) : ℂ)) =
      (fun i => ((fast w.1 i / (2 * π) : ℝ) : ℂ)) + fun i => (m i : ℂ) := by
    funext i
    simp only [fast_add_fastShift_fst, Pi.add_apply]
    push_cast
    field_simp
  rw [e, charE_add_int]

/-- **(1b) `χ*` is `2π`-periodic in the angles**, for every `P`. -/
theorem chiStar_anglePeriodic (S : Finset (Fin 2 → ℤ)) (frq : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (P : Phase (2 + 2) → ℝ) : IsAnglePeriodicOn univ (chiStar S frq P) := by
  intro m w _
  unfold chiStar
  simp only [chartCoeff_add_fastShift, add_fastShift_snd, charE_add_fastShift_angles]

/-- **(1b) `Π_S P` is `2π`-periodic in the angles**, for every `P`. -/
theorem projS_anglePeriodic (S : Finset (Fin 2 → ℤ)) (P : Phase (2 + 2) → ℝ) :
    IsAnglePeriodicOn univ (projS S P) := by
  intro m w _
  unfold projS
  simp only [chartCoeff_add_fastShift, charE_add_fastShift_angles]

/-! ### (1c, 1d) Invariance under maps with symplectic derivative -/

section Generic

variable {d : ℕ} {R : Phase d → Phase d} {A : Phase d →L[ℝ] Phase d} {O : Set (Phase d)}

/-- **(1c) Brackets of invariant functions are invariant.** -/
theorem pb_comp_eq (hA : ∀ u v, symplecticForm (A u) (A v) = symplecticForm u v)
    (hAs : Function.Surjective A) (hR : ∀ w, HasFDerivAt R A w) (hO : IsOpen O)
    (hRO : ∀ w ∈ O, R w ∈ O) {a b : Phase d → ℝ} (ha : DifferentiableOn ℝ a O)
    (hb : DifferentiableOn ℝ b O) (hai : ∀ w ∈ O, a (R w) = a w) (hbi : ∀ w ∈ O, b (R w) = b w) :
    ∀ w ∈ O, pb a b (R w) = pb a b w := by
  intro w hw
  have hn : ∀ᶠ x in 𝓝 w, x ∈ O := hO.mem_nhds hw
  have hRw : O ∈ 𝓝 (R w) := hO.mem_nhds (hRO w hw)
  exact fderiv_apply_hamiltonianVectorField_comp hA hAs (hR w) (hb.differentiableAt hRw)
    (hn.mono fun x hx => hbi x hx) (ha.differentiableAt hRw) (hn.mono fun x hx => hai x hx)

/-- **(1d) Directional derivatives along a fixed direction of invariant functions are
invariant.** -/
theorem dirDeriv_comp_eq (hR : ∀ w, HasFDerivAt R A w) (hO : IsOpen O) (hRO : ∀ w ∈ O, R w ∈ O)
    {v : Phase d} (hAv : A v = v) {χ : Phase d → ℝ} (hχ : DifferentiableOn ℝ χ O)
    (hχi : ∀ w ∈ O, χ (R w) = χ w) : ∀ w ∈ O, dirDeriv v χ (R w) = dirDeriv v χ w := by
  intro w hw
  have hn : ∀ᶠ x in 𝓝 w, x ∈ O := hO.mem_nhds hw
  have hcomp : fderiv ℝ (fun x => χ (R x)) w = (fderiv ℝ χ (R w)).comp A :=
    ((hχ.differentiableAt (hO.mem_nhds (hRO w hw))).hasFDerivAt.comp w (hR w)).fderiv
  have hloc : (fun x => χ (R x)) =ᶠ[𝓝 w] χ := hn.mono fun x hx => hχi x hx
  have heq : fderiv ℝ (fun x => χ (R x)) w = fderiv ℝ χ w := hloc.fderiv_eq
  unfold dirDeriv
  rw [← heq, hcomp, ContinuousLinearMap.comp_apply, hAv]

theorem differentiableOn_dirDeriv {χ : Phase d → ℝ} (hO : IsOpen O) (hχ : ContDiffOn ℝ ∞ χ O)
    (v : Phase d) : DifferentiableOn ℝ (dirDeriv v χ) O := fun y hy =>
  ((contDiffAt_dirDeriv v (hχ.contDiffAt (hO.mem_nhds hy))).differentiableAt
    (by simp)).differentiableWithinAt

/-- **(1d) `approxIntegral₂` of invariant generators is invariant**, under a map with symplectic
surjective derivative that fixes the action `I_k` and the angle direction `angleDir k`. -/
theorem approxIntegral₂_comp_eq (k : Fin d)
    (hA : ∀ u v, symplecticForm (A u) (A v) = symplecticForm u v) (hAs : Function.Surjective A)
    (hR : ∀ w, HasFDerivAt R A w) (hAk : A (angleDir k) = angleDir k)
    (hRk : ∀ y, (R y).2 k = y.2 k) (hO : IsOpen O) (hRO : ∀ w ∈ O, R w ∈ O)
    {χ₁ χ₂ : Phase d → ℝ} (h₁ : ContDiffOn ℝ ∞ χ₁ O) (h₂ : ContDiffOn ℝ ∞ χ₂ O)
    (h₁i : ∀ w ∈ O, χ₁ (R w) = χ₁ w) (h₂i : ∀ w ∈ O, χ₂ (R w) = χ₂ w) :
    ∀ w ∈ O, approxIntegral₂ k χ₁ χ₂ (R w) = approxIntegral₂ k χ₁ χ₂ w := by
  intro w hw
  have hd₁ := h₁.differentiableOn (by simp)
  have hd₂ := h₂.differentiableOn (by simp)
  have hD₁ := differentiableOn_dirDeriv hO h₁ (angleDir k)
  have hD₁i := dirDeriv_comp_eq hR hO hRO hAk hd₁ h₁i
  unfold approxIntegral₂
  rw [hRk, hD₁i w hw, dirDeriv_comp_eq hR hO hRO hAk hd₂ h₂i w hw,
    pb_comp_eq hA hAs hR hO hRO hD₁ hd₁ hD₁i h₁i w hw]

end Generic

/-! ### The two maps -/

theorem hasFDerivAt_add_fastShift (m : Fin 2 → ℤ) (w : Phase (2 + 2)) :
    HasFDerivAt (fun y : Phase (2 + 2) => y + fastShift (a := 2) (b := 2) m)
      (ContinuousLinearMap.id ℝ (Phase (2 + 2))) w :=
  (hasFDerivAt_id w).add_const _

theorem id_symplectic (u v : Phase (2 + 2)) :
    symplecticForm (ContinuousLinearMap.id ℝ (Phase (2 + 2)) u)
      (ContinuousLinearMap.id ℝ (Phase (2 + 2)) v) = symplecticForm u v := rfl

theorem id_surjective : Function.Surjective (ContinuousLinearMap.id ℝ (Phase (2 + 2))) :=
  Function.surjective_id

theorem chartRotCLM_angleDir (θ : ℝ) (i : Fin 2) :
    chartRotCLM θ (angleDir (Fin.castAdd 2 i)) = angleDir (Fin.castAdd 2 i) := by
  have hs : slow (angleDir (d := 2 + 2) (Fin.castAdd 2 i)).1 = 0 := by
    funext j
    simp [angleDir, slow, Pi.single_apply, Fin.ext_iff]
    omega
  have hne : ∀ a : Fin 2, ¬((a : ℕ) + 2 = (i : ℕ)) := fun a => by have := i.isLt; omega
  rw [chartRotCLM_apply, chartRotLin, hs]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j <;>
  simp [assemble, angleDir, fast, slow, Pi.single_apply, Fin.ext_iff, hne]

/-! ### (1e) The perturbation -/

/-- **(1e) `P` is rotation-invariant** on the chart domain. -/
theorem chartPert_rotInv {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) :
    IsRotInvOn (poincareProdDom n) (chartPert ν μ) := by
  intro θ w hw
  unfold chartPert hProd
  rw [liftChartHam_chartRot ν μ θ hw, fast_chartRot]

/-- **(1e) `P` is `2π`-periodic in the angles** on the chart domain. -/
theorem chartPert_anglePeriodic {n : ℕ} {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ) :
    IsAnglePeriodicOn (poincareProdDom n) (chartPert ν μ) := by
  intro m w hw
  have hs : fast (w + fastShift (a := n) (b := n) m).2 = fast w.2 := by
    funext i
    simp [fastShift, fast]
  unfold chartPert hProd liftChartHam
  rw [(poincareProd_lattice hν one_pos hw m).2, hs]

/-! ### (1f) HD 11964 -/

/-- HD 11964's first generator `χ₁ = χ*(P)`. -/
def chi1HD : Phase (2 + 2) → ℝ := chiStar modesHD (keplerFreq nu) (chartPert nu mu)

/-- HD 11964's `G₂ = {P - ½ Π_S P, χ₁}`. -/
def G2HD : Phase (2 + 2) → ℝ :=
  pb (fun y => chartPert nu mu y - projS modesHD (chartPert nu mu) y / 2) chi1HD

/-- HD 11964's second generator `χ₂ = χ*(G₂)`. -/
def chi2HD : Phase (2 + 2) → ℝ := chiStar modesHD (keplerFreq nu) G2HD

/-- HD 11964's approximate integrals `F_i = approxIntegral₂ (castAdd i) χ₁ χ₂`. -/
def FHD (i : Fin 2) : Phase (2 + 2) → ℝ := approxIntegral₂ (Fin.castAdd 2 i) chi1HD chi2HD

theorem add_fastShift_mem_openHD (m : Fin 2 → ℤ) {w : Phase (2 + 2)} (hw : w ∈ openHD) :
    w + fastShift (a := 2) (b := 2) m ∈ openHD := by
  obtain ⟨hΛ, hA⟩ := hw
  have hA' : chartAMD (w + fastShift (a := 2) (b := 2) m) = chartAMD w := by
    simp only [chartAMD, slow_add_fastShift_fst, add_fastShift_snd]
  exact ⟨by rw [add_fastShift_snd]; exact hΛ, by rw [hA']; exact hA⟩

theorem contDiffOn_chi1HD : ContDiffOn ℝ ∞ chi1HD openHD := contDiffOn_chi_HD.1

theorem contDiffOn_chi2HD : ContDiffOn ℝ ∞ chi2HD openHD := contDiffOn_chi_HD.2.1

theorem contDiffOn_G2HD : ContDiffOn ℝ ∞ G2HD openHD := by
  have hP := contDiffOn_chartPert_HD
  have hA : ContDiffOn ℝ ∞ (fun y => chartPert nu mu y - projS modesHD (chartPert nu mu) y / 2)
      openHD :=
    hP.sub ((contDiffOn_projS isOpen_openHD isAngleSaturated_openHD modesHD hP).div_const 2)
  exact fun y hy => (contDiffAt_pb (hA.contDiffAt (isOpen_openHD.mem_nhds hy))
    (contDiffOn_chi1HD.contDiffAt (isOpen_openHD.mem_nhds hy))).contDiffWithinAt

/-- A function rotation-invariant and periodic on `openHD`, smooth there. -/
structure InvHD (f : Phase (2 + 2) → ℝ) : Prop where
  rot : IsRotInvOn openHD f
  per : IsAnglePeriodicOn openHD f
  smooth : ContDiffOn ℝ ∞ f openHD

theorem invHD_chartPert : InvHD (chartPert nu mu) :=
  ⟨fun θ w hw => chartPert_rotInv nu mu θ w (openHD_subset_dom hw),
    fun m w hw => chartPert_anglePeriodic nu_pos mu m w (openHD_subset_dom hw),
    contDiffOn_chartPert_HD⟩

theorem invHD_chiStar {P : Phase (2 + 2) → ℝ} (hP : InvHD P) :
    InvHD (chiStar modesHD (keplerFreq nu) P) := by
  refine ⟨chiStar_rotInv _ _ isAngleSaturated_openHD hP.rot hP.per,
    fun m w _ => chiStar_anglePeriodic _ _ _ m w (mem_univ w), ?_⟩
  exact contDiffOn_chiStar isOpen_openHD isAngleSaturated_openHD hP.smooth
    (fun w hw => contDiffAt_keplerFreq nu (fast_ne_zero_of_mem_dom (openHD_subset_dom hw)))
    isModeSet_HD

theorem invHD_pb {a b : Phase (2 + 2) → ℝ} (ha : InvHD a) (hb : InvHD b) : InvHD (pb a b) := by
  have hda := ha.smooth.differentiableOn (by simp)
  have hdb := hb.smooth.differentiableOn (by simp)
  refine ⟨fun θ => pb_comp_eq (chartRotCLM_symplectic θ) (chartRotCLM_surjective θ)
      (hasFDerivAt_chartRot θ) isOpen_openHD (fun w hw => chartRot_mem_openHD θ hw) hda hdb
      (ha.rot θ) (hb.rot θ),
    fun m => pb_comp_eq id_symplectic id_surjective (hasFDerivAt_add_fastShift m) isOpen_openHD
      (fun w hw => add_fastShift_mem_openHD m hw) hda hdb (ha.per m) (hb.per m), ?_⟩
  exact fun y hy => (contDiffAt_pb (ha.smooth.contDiffAt (isOpen_openHD.mem_nhds hy))
    (hb.smooth.contDiffAt (isOpen_openHD.mem_nhds hy))).contDiffWithinAt

theorem invHD_chi1HD : InvHD chi1HD := invHD_chiStar invHD_chartPert

theorem invHD_G2HD : InvHD G2HD := by
  have hA : InvHD (fun y => chartPert nu mu y - projS modesHD (chartPert nu mu) y / 2) := by
    have hP := invHD_chartPert
    refine ⟨fun θ w hw => ?_, fun m w hw => ?_, ?_⟩
    · simp only [hP.rot θ w hw, projS_rotInv modesHD isAngleSaturated_openHD hP.rot hP.per θ w hw]
    · simp only [hP.per m w hw, projS_anglePeriodic modesHD _ m w (mem_univ w)]
    · exact hP.smooth.sub ((contDiffOn_projS isOpen_openHD isAngleSaturated_openHD modesHD
        hP.smooth).div_const 2)
  exact invHD_pb hA invHD_chi1HD

theorem invHD_chi2HD : InvHD chi2HD := invHD_chiStar invHD_G2HD

/-- **(1f) `hFrot` for HD 11964**: `openHD` and every `F_i` are invariant under every chart
rotation. -/
theorem rotInv_FHD (i : Fin 2) (θ : ℝ) {w : Phase (2 + 2)} (hw : w ∈ openHD) :
    chartRot θ w ∈ openHD ∧ FHD i (chartRot θ w) = FHD i w :=
  ⟨chartRot_mem_openHD θ hw,
    approxIntegral₂_comp_eq (Fin.castAdd 2 i) (chartRotCLM_symplectic θ) (chartRotCLM_surjective θ)
      (hasFDerivAt_chartRot θ) (chartRotCLM_angleDir θ i)
      (fun y => congrFun (fast_chartRot θ y) i) isOpen_openHD
      (fun _ hy => chartRot_mem_openHD θ hy) invHD_chi1HD.smooth invHD_chi2HD.smooth
      (invHD_chi1HD.rot θ) (invHD_chi2HD.rot θ) w hw⟩

theorem differentiableOn_FHD (i : Fin 2) : DifferentiableOn ℝ (FHD i) openHD :=
  contDiffOn_chi_HD.2.2 i

/-- **(1g) HD 11964: no orbit crossing from the cell bounds**: `noCrossing_of_cellBounds` with
`O = openHD` and `F = FHD`. `hF` and `hFrot` are proved; `R(D.d) ⊆ openHD` follows from
`D.d ≤ 1/500`. The cell bounds and the links of the layer's functions to `FHD` remain premises. -/
theorem noCrossing_HD_of_cellBounds :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      ∀ (D : DriftData 2), D.ok = true → (D.r : ℝ) = rTube → (D.d : ℝ) ≤ 1 / 500 →
      ∀ cells : List AffineCell, CoversReps cells D.d →
      ∀ (G Gr : Fin 2 → (Fin 2 → ℂ) → (Fin 6 → ℂ) → ℂ),
      (∀ i, ∀ w ∈ repSet cells D.d,
        fderiv ℝ (FHD i) w (hamiltonianVectorField (liftChartHam nu mu) w) =
          (G i (chartAngle w) (fun j => (cellCoord w j : ℂ))).re) →
      (∀ i, ∀ w ∈ repSet cells D.d,
        FHD i w - fast w.2 i = (Gr i (chartAngle w) (fun j => (cellCoord w j : ℂ))).re) →
      (∀ i, ∀ k ∈ cells, ∀ θ : Fin 2 → ℝ, ∀ u : Fin 6 → ℝ, (∀ j, |u j| ≤ 1) →
        ‖G i (fun i => (θ i : ℂ)) (cellMapC k.c k.toMx (fun j => (u j : ℂ)))‖ ≤ D.eta i) →
      (∀ i, ∀ k ∈ cells, ∀ θ : Fin 2 → ℝ, ∀ u : Fin 6 → ℝ, (∀ j, |u j| ≤ 1) →
        ‖Gr i (fun i => (θ i : ℂ)) (cellMapC k.c k.toMx (fun j => (u j : ℂ))) -
          (((D.lo i + D.hi i) / 2 : ℚ) : ℝ)‖ ≤ (((D.hi i - D.lo i) / 2 : ℚ) : ℝ)) →
      ∀ z₀ : Phase (2 * 2), IsPhysicalState nu z₀ →
        (∀ i, lamLo i ≤ keplerAction nu z₀ i ∧ keplerAction nu z₀ i ≤ lamHi i) →
        strongAMD nu z₀ ≤ cBar → 0 < totalMomentum z₀ →
        ∃ z : ℝ → Phase (2 * 2), z 0 = z₀ ∧
          IsMovingSolutionOn nu mu (Icc (-(D.T : ℝ)) D.T) z ∧
          MovingUniqueOn nu mu (Icc (-(D.T : ℝ)) D.T) z ∧
          ∀ t ∈ Icc (-(D.T : ℝ)) D.T,
            (∀ i, dStar ≤
              keplerAxis nu (z t) i * (1 - planeLength (keplerEccVector nu (z t) i))) ∧
            (∀ a : AdjIdx 2, dPair ≤ keplerAxis nu (z t) a.upperIdx *
                (1 - planeLength (keplerEccVector nu (z t) a.upperIdx)) -
              keplerAxis nu (z t) a.1 * (1 + planeLength (keplerEccVector nu (z t) a.1))) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) := by
  obtain ⟨dS, dP, hdS, hdP, h⟩ := noCrossing_of_cellBounds
  exact ⟨dS, dP, hdS, hdP, fun D hD hr hd cells hcov G Gr hG hGr hcG hcGr =>
    h D hD hr FHD openHD isOpen_openHD (region_subset_openHD hd) openHD_subset_chartSafe
      differentiableOn_FHD (fun i θ w hw => rotInv_FHD i θ hw) cells hcov G Gr hG hGr hcG hcGr⟩

end HD11964.Cover

end
