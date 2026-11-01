/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.AngleGraph
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The clock-triangular graph criterion (pure form)

Pure geometry, no certificate data. In an extended phase space with a clock (an action `I_l`
with `∂_{I_l} H` constant, e.g. a periodically forced system), the clock lemma
(`KAM.Certificate.clock_frequency`) makes the clock angle of an invariant torus exact:
`A_l(θ) = θ_l + c_l`. The angle map `A` is then **triangular**: its derivative has the rows
`e_l` for the clocks, and only the remaining (free) row `i` carries information. The torus is a
graph over the angles as soon as `∂_i A_i ≥ m > 0`; no bound on the other entries `∂_l A_i` of the
free row is needed. This is the criterion of the Moon's spin–orbit tori (SO-2 `checkSoGraph`,
SO-3 `LockAngle`), there with `n = 2`, free angle `0` and clock `1`.

* `IsClockTriangular A i c m`: `A : ℝⁿ → ℝⁿ` differentiable, commuting with `ℤⁿ`, with
  `A θ l = θ l + c l` for every `l ≠ i` and `∂_i A_i ≥ m > 0`.
* `IsClockTriangular.abs_slice_le`: on the line `s ↦ θ + s eᵢ`,
  `m |s' - s| ≤ |A_i(θ + s' eᵢ) - A_i(θ + s eᵢ)|`; `injective`, `surjective` (intermediate
  values and `A_i(θ + eᵢ) = A_i(θ) + 1`), `fderiv_injective` (triangular derivative);
  `invFun_clock`: the clock components of the inverse are `φ l - c l`.
* `IsClockAngleGraph k i c m`: `IsAnalyticAngleGraph k` together with the clock-triangular angle
  map; `isClockAngleGraph_of_clock` builds it from an analytic `k` with
  `k(θ + m) = k(θ) + (m, 0)`, the clock rows and the diagonal bound.

For `n ≥ 3` with several clocks of the same frequency `1` the frequency is resonant, so the
certified form (`ClockGraphCert.lean`) is of interest for `n = 2`; the pure statements hold for
every `n`.
-/

@[expose] public noncomputable section

open Set Function

namespace KAM.Application

variable {n : ℕ}

/-- Two points that agree off the coordinate `i` lie on one line `s ↦ θ + s eᵢ`. -/
theorem eq_add_single_of_forall_ne {i : Fin n} {θ θ' : Fin n → ℝ}
    (hcl : ∀ l, l ≠ i → θ' l = θ l) : θ' = θ + (θ' i - θ i) • Pi.single i 1 := by
  funext l
  by_cases hl : l = i
  · subst hl; simp
  · simp [hl, hcl l hl]

/-- **A clock-triangular angle map**: `A : ℝⁿ → ℝⁿ` is differentiable, commutes with `ℤⁿ`, its
components `l ≠ i` are the clocks `A θ l = θ l + c l`, and its free diagonal entry satisfies
`∂_i A_i ≥ m > 0` everywhere. -/
structure IsClockTriangular (A : (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin n) (c : Fin n → ℝ) (m : ℝ) :
    Prop where
  pos : 0 < m
  differentiable : Differentiable ℝ A
  add_int : ∀ θ (k : Fin n → ℤ), A (θ + fun l => (k l : ℝ)) = A θ + fun l => (k l : ℝ)
  clock : ∀ θ l, l ≠ i → A θ l = θ l + c l
  mono : ∀ θ, m ≤ fderiv ℝ A θ (Pi.single i 1) i

namespace IsClockTriangular

variable {A : (Fin n → ℝ) → (Fin n → ℝ)} {i : Fin n} {c : Fin n → ℝ} {m : ℝ}
  (h : IsClockTriangular A i c m)
include h

/-- The free component along the line `s ↦ θ + s eᵢ`. -/
theorem hasDerivAt_slice (θ : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => A (θ + t • Pi.single i 1) i)
      (fderiv ℝ A (θ + s • Pi.single i 1) (Pi.single i 1) i) s := by
  have hline : HasDerivAt (fun t : ℝ => θ + t • (Pi.single i 1 : Fin n → ℝ))
      (Pi.single i 1) s := by
    simpa using ((hasDerivAt_id s).smul_const (Pi.single i 1 : Fin n → ℝ)).const_add θ
  exact hasDerivAt_pi.1 ((h.differentiable _).hasFDerivAt.comp_hasDerivAt s hline) i

/-- Linear growth of the free component along `eᵢ`. -/
theorem mul_sub_le (θ : Fin n → ℝ) {s s' : ℝ} (hs : s ≤ s') :
    m * (s' - s) ≤ A (θ + s' • Pi.single i 1) i - A (θ + s • Pi.single i 1) i :=
  mul_sub_le_image_sub_of_le_deriv (f := fun t : ℝ => A (θ + t • Pi.single i 1) i)
    (fun t => (h.hasDerivAt_slice θ t).differentiableAt)
    (fun t => by rw [(h.hasDerivAt_slice θ t).deriv]; exact h.mono _) hs

/-- **The slice bound**: `m |s' - s| ≤ |A_i(θ + s' eᵢ) - A_i(θ + s eᵢ)|`. -/
theorem abs_slice_le (θ : Fin n → ℝ) (s s' : ℝ) :
    m * |s' - s| ≤ |A (θ + s' • Pi.single i 1) i - A (θ + s • Pi.single i 1) i| := by
  rcases le_total s s' with hs | hs
  · have := h.mul_sub_le θ hs
    rw [abs_of_nonneg (sub_nonneg.2 hs)]
    exact this.trans (le_abs_self _)
  · have := h.mul_sub_le θ hs
    rw [abs_sub_comm s' s, abs_of_nonneg (sub_nonneg.2 hs), abs_sub_comm]
    exact this.trans (le_abs_self _)

theorem injective : Injective A := by
  intro θ θ' hA
  have hcl : ∀ l, l ≠ i → θ' l = θ l := fun l hl => by
    have h1 := h.clock θ l hl
    have h2 := h.clock θ' l hl
    rw [hA] at h1
    linarith
  have he := eq_add_single_of_forall_ne hcl
  have hb := h.abs_slice_le θ 0 (θ' i - θ i)
  rw [← he, zero_smul, add_zero, hA, sub_self, abs_zero, sub_zero] at hb
  have h0 : |θ' i - θ i| = 0 :=
    le_antisymm (by nlinarith [abs_nonneg (θ' i - θ i), h.pos]) (abs_nonneg _)
  rw [abs_eq_zero.1 h0, zero_smul, add_zero] at he
  exact he.symm

/-- The integer shift along `eᵢ`. -/
theorem add_intCast_smul (θ : Fin n → ℝ) (k : ℤ) :
    A (θ + (k : ℝ) • Pi.single i 1) = A θ + (k : ℝ) • Pi.single i 1 := by
  have e : (k : ℝ) • (Pi.single i 1 : Fin n → ℝ) =
      fun l => (((Pi.single i k : Fin n → ℤ) l : ℤ) : ℝ) := by
    funext l
    by_cases hl : l = i
    · subst hl; simp
    · simp [hl]
  rw [e]
  exact h.add_int θ _

theorem surjective : Surjective A := by
  intro φ
  set θ₀ : Fin n → ℝ := fun l => φ l - c l
  set g : ℝ → ℝ := fun s => A (θ₀ + s • Pi.single i 1) i with hg
  have gc : Continuous g := continuous_iff_continuousAt.2 fun s =>
    (h.hasDerivAt_slice θ₀ s).continuousAt
  have gk : ∀ s (k : ℤ), g (s + k) = g s + k := fun s k => by
    have e : θ₀ + (s + k) • (Pi.single i 1 : Fin n → ℝ) =
        (θ₀ + s • Pi.single i 1) + (k : ℝ) • Pi.single i 1 := by
      rw [add_smul, add_assoc]
    simp only [hg, e, h.add_intCast_smul, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one]
  set k : ℤ := ⌊φ i - g 0⌋ with hk
  have h1 : g (0 + k) ≤ φ i := by
    rw [gk]; have := Int.floor_le (φ i - g 0); rw [← hk] at this; linarith
  have h2 : φ i ≤ g (0 + ((k + 1 : ℤ) : ℝ)) := by
    rw [gk]; have := Int.lt_floor_add_one (φ i - g 0); rw [← hk] at this
    push_cast; linarith
  have hle : (0 : ℝ) + k ≤ 0 + ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc hle gc.continuousOn ⟨h1, h2⟩
  refine ⟨θ₀ + s • Pi.single i 1, funext fun l => ?_⟩
  by_cases hl : l = i
  · subst hl; exact hs
  · rw [h.clock _ l hl]
    simp [θ₀, hl]

theorem bijective : Bijective A := ⟨h.injective, h.surjective⟩

/-- The clock rows of the derivative: `DA(θ) v` has components `v l` for `l ≠ i`. -/
theorem fderiv_apply_clock (θ v : Fin n → ℝ) {l : Fin n} (hl : l ≠ i) :
    fderiv ℝ A θ v l = v l := by
  set P : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) l
  have h1 : HasFDerivAt (fun θ => A θ l) (P.comp (fderiv ℝ A θ)) θ :=
    P.hasFDerivAt.comp θ (h.differentiable θ).hasFDerivAt
  have h2 : HasFDerivAt (fun θ => A θ l) P θ := by
    have e : (fun θ => A θ l) = fun θ : Fin n → ℝ => θ l + c l :=
      funext fun θ => h.clock θ l hl
    rw [e]
    exact P.hasFDerivAt.add_const (c l)
  exact congrArg (fun L => L v) (h1.unique h2)

/-- **The derivative is invertible** (it is triangular with diagonal `∂_i A_i ≥ m > 0` and `1`). -/
theorem fderiv_injective (θ : Fin n → ℝ) : Injective (fderiv ℝ A θ) := by
  intro u v huv
  set w := u - v with hw
  have hw0 : fderiv ℝ A θ w = 0 := by rw [hw, map_sub, huv, sub_self]
  have hcl : ∀ l, l ≠ i → w l = 0 := fun l hl => by
    rw [← h.fderiv_apply_clock θ w hl, hw0]; rfl
  have he : w = w i • Pi.single i 1 := by
    have := eq_add_single_of_forall_ne (θ := 0) (θ' := w) (fun l hl => by simpa using hcl l hl)
    simpa using this
  have hi : w i * fderiv ℝ A θ (Pi.single i 1) i = 0 := by
    have := congrFun hw0 i
    rw [he, map_smul] at this
    simpa using this
  have hwi : w i = 0 := by
    rcases mul_eq_zero.1 hi with h0 | h0
    · exact h0
    · exact absurd h0 (ne_of_gt (h.pos.trans_le (h.mono θ)))
  have : w = 0 := by rw [he, hwi, zero_smul]
  exact sub_eq_zero.1 this

/-- The clock components of the inverse: `A⁻¹(φ) l = φ l - c l` for `l ≠ i`. -/
theorem invFun_clock (φ : Fin n → ℝ) {l : Fin n} (hl : l ≠ i) : invFun A φ l = φ l - c l := by
  have h1 := h.clock (invFun A φ) l hl
  rw [Function.invFun_eq (h.surjective φ)] at h1
  linarith

end IsClockTriangular

/-- **A clock-triangular graph over the angles**: `k` is an analytic graph over the angles
(`IsAnalyticAngleGraph`) whose angle map `torusAngle k` is clock-triangular with free angle `i`,
clock offsets `c` and diagonal bound `m`. -/
structure IsClockAngleGraph (k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin n)
    (c : Fin n → ℝ) (m : ℝ) : Prop extends IsAnalyticAngleGraph k where
  triangular : IsClockTriangular (torusAngle k) i c m

/-- **The clock-triangular graph criterion** (pure form): an analytic real torus with
`k(θ + m) = k(θ) + (m, 0)` whose angle map has the clock components `A θ l = θ l + c l` (`l ≠ i`)
and the free diagonal bound `∂_i A_i ≥ m > 0` is an analytic graph over the angles. -/
theorem isClockAngleGraph_of_clock {k : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)} {i : Fin n}
    {c : Fin n → ℝ} {m : ℝ} (hk : AnalyticOnNhd ℝ k univ)
    (hper : ∀ θ (m : Fin n → ℤ), k (θ + fun i => (m i : ℝ)) = k θ + (fun i => (m i : ℝ), 0))
    (hm : 0 < m) (hclock : ∀ θ l, l ≠ i → torusAngle k θ l = θ l + c l)
    (hmono : ∀ θ, m ≤ fderiv ℝ (torusAngle k) θ (Pi.single i 1) i) :
    IsClockAngleGraph k i c m := by
  have hA : IsClockTriangular (torusAngle k) i c m :=
    ⟨hm, fun θ => (analyticOnNhd_torusAngle hk θ (mem_univ θ)).differentiableAt,
      torusAngle_add_int hper, hclock, hmono⟩
  exact ⟨isAnalyticAngleGraph_of_bijective hk hper hA.bijective hA.fderiv_injective, hA⟩

end KAM.Application
