/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.FirstExit
public import KAM.ODE.Continuation
public import KAM.EffectiveStability.Domains

/-!
# The continuation engine (track B)

Existence of a solution of `ẋ = F x` on an open interval strictly containing `[-T, T]`, together
with the confinement and drift bounds of an observable `g`, in two variants: a compact confinement
set (oscillator chart) and a compact action box for `ℝⁿ × U` with angle-periodic field (torus
chart). Both are derived from the maximal solution, `firstExit_box_of_deriv` and the continuation
theorems of `KAM.ODE`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set KAM.ODE

variable {n : ℕ}

/-- Abstract step shared by both variants: from a maximal solution whose observable `f` obeys the
stopped drift bound, and a continuation principle for the confinement region, get a real
`T₁ > T`. -/
theorem exists_confined_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {W : Set E} {x₀ : E} {Tm Tp : EReal} {z : ℝ → E}
    (hz : IsMaximalSolution F W x₀ Tm Tp z) {f f' : ℝ → Fin n → ℝ}
    {a b η : Fin n → ℝ} {T : ℝ} (hT : 0 ≤ T) (hη : ∀ j, 0 ≤ η j)
    (hmargin : ∀ j, a j + T * η j < b j) (hf0 : ∀ j, |f 0 j| ≤ a j)
    (hderiv : ∀ t ∈ eIoo Tm Tp, ∀ j, HasDerivAt (fun s => f s j) (f' t j) t)
    (hbound : ∀ t ∈ eIoo Tm Tp, (∀ j, |f t j| ≤ b j) → ∀ j, |f' t j| ≤ η j)
    (hright : (∀ t : ℝ, 0 ≤ t → (t : EReal) < Tp → ∀ j, |f t j| ≤ b j) → Tp = ⊤)
    (hleft : (∀ t : ℝ, Tm < (t : EReal) → t ≤ 0 → ∀ j, |f t j| ≤ b j) → Tm = ⊥) :
    ∃ T₁ : ℝ, T < T₁ ∧ Ioo (-T₁) T₁ ⊆ eIoo Tm Tp ∧
      ∀ t : ℝ, |t| ≤ T → t ∈ eIoo Tm Tp ∧
        ∀ j, |f t j - f 0 j| ≤ η j * |t| ∧ |f t j| ≤ a j + η j * T := by
  have hFE := firstExit_box_of_deriv (ordConnected_eIoo Tm Tp) (zero_mem_eIoo hz) hT hη hmargin hf0
    hderiv hbound
  have hbdd : ∀ t ∈ eIoo Tm Tp, |t| ≤ T → ∀ j, |f t j| ≤ b j := fun t ht htT j => by
    have := (hFE t ht htT j).2
    have h1 := hmargin j
    have h2 : η j * T = T * η j := mul_comm _ _
    linarith
  have hTp : (T : EReal) < Tp := by
    by_contra hle
    rw [not_lt] at hle
    have := hright fun t ht0 htp j => hbdd t
      ⟨lt_of_lt_of_le (hz.neg_lt) (by exact_mod_cast ht0), htp⟩
      (by rw [abs_of_nonneg ht0]; exact EReal.coe_le_coe_iff.1 (htp.le.trans hle)) j
    rw [this] at hle
    exact absurd hle (by simp)
  have hTm : Tm < ((-T : ℝ) : EReal) := by
    by_contra hle
    rw [not_lt] at hle
    have := hleft fun t htm ht0 j => hbdd t
      ⟨htm, lt_of_le_of_lt (by exact_mod_cast ht0) hz.pos_lt⟩
      (by rw [abs_of_nonpos ht0]; exact neg_le.1 (EReal.coe_le_coe_iff.1 (hle.trans htm.le))) j
    rw [this] at hle
    exact absurd hle (by simp)
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hTp
  obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.1 hTm
  have hTr : T < r := EReal.coe_lt_coe_iff.1 hr1
  have hqT : q < -T := EReal.coe_lt_coe_iff.1 hq2
  refine ⟨min r (-q), lt_min hTr (by linarith), fun t ht => ?_, fun t htT => ?_⟩
  · refine ⟨lt_trans hq1 (EReal.coe_lt_coe_iff.2 ?_), lt_trans (EReal.coe_lt_coe_iff.2 ?_) hr2⟩
    · have := ht.1; have := min_le_right r (-q); linarith
    · have := ht.2; have := min_le_left r (-q); linarith
  · have hmem : t ∈ eIoo Tm Tp := by
      have := abs_le.1 htT
      exact ⟨lt_of_lt_of_le hTm (EReal.coe_le_coe_iff.2 this.1),
        lt_of_le_of_lt (EReal.coe_le_coe_iff.2 this.2) hTp⟩
    exact ⟨hmem, hFE t hmem htT⟩

/-- The continuation engine, compact variant. -/
theorem exists_confined_solution_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {F : E → E} {W : Set E} (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W)
    (g : E → Fin n → ℝ) (hg : ∀ x ∈ W, DifferentiableAt ℝ g x)
    {a b η : Fin n → ℝ} {T : ℝ} (hT : 0 ≤ T) (hη : ∀ j, 0 ≤ η j)
    (hmargin : ∀ j, a j + T * η j < b j)
    (hK : IsCompact {x | ∀ j, |g x j| ≤ b j}) (hKW : {x | ∀ j, |g x j| ≤ b j} ⊆ W)
    (hdrift : ∀ x, (∀ j, |g x j| ≤ b j) → ∀ j, |fderiv ℝ g x (F x) j| ≤ η j)
    (x₀ : E) (hx₀ : ∀ j, |g x₀ j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ w : ℝ → E, w 0 = x₀ ∧
      (∀ t ∈ Set.Ioo (-T₁) T₁, w t ∈ W ∧ HasDerivAt w (F (w t)) t) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ j, |g (w t) j - g x₀ j| ≤ η j * |t| ∧ |g (w t) j| ≤ a j + η j * T := by
  have hab : ∀ j, a j ≤ b j := fun j => by
    have := hmargin j; have := mul_nonneg hT (hη j); linarith
  have hx₀W : x₀ ∈ W := hKW fun j => (hx₀ j).trans (hab j)
  obtain ⟨Tm, Tp, z, hz⟩ := (gen_maximal hW hF hx₀W).1
  have hcomp : ∀ t ∈ eIoo Tm Tp, ∀ j,
      HasDerivAt (fun s => g (z s) j) (fderiv ℝ g (z t) (F (z t)) j) t := by
    intro t ht
    have hzt := hz.isSolution t ht
    exact hasDerivAt_pi.1 ((hg _ hzt.1).hasFDerivAt.comp_hasDerivAt t hzt.2)
  obtain ⟨T₁, hT₁, hsub, hmain⟩ := exists_confined_aux hz (f := fun t => g (z t))
    (f' := fun t => fderiv ℝ g (z t) (F (z t))) hT hη hmargin (by simpa [hz.init] using hx₀)
    hcomp (fun t _ hb => hdrift (z t) hb)
    (fun h => (gen_continuation_compact hW hF hz hK hKW).1
      ⟨0, le_rfl, hz.pos_lt, fun t ht0 htp => h t ht0 htp⟩)
    (fun h => (gen_continuation_compact hW hF hz hK hKW).2
      ⟨0, le_rfl, hz.neg_lt, fun t htm ht0 => h t htm ht0⟩)
  refine ⟨T₁, hT₁, z, hz.init, fun t ht => hz.isSolution t (hsub ht), fun t htT j => ?_⟩
  simpa [hz.init] using (hmain t htT).2 j

/-- The continuation engine, torus variant: phase space `ℝⁿ × ℝⁿ`, domain `ℝⁿ × U`, angle-periodic
field, observable the action component. -/
theorem exists_confined_solution_periodic {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {F : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hF : ContDiffOn ℝ 1 F (Set.univ ×ˢ U))
    (hper : ∀ k : Fin n → ℤ, ∀ x ∈ (Set.univ : Set (Fin n → ℝ)) ×ˢ U,
      F (x + KAM.ODE.angleShift k) = F x)
    {a b η : Fin n → ℝ} {T : ℝ} (hT : 0 ≤ T) (hη : ∀ j, 0 ≤ η j)
    (hmargin : ∀ j, a j + T * η j < b j)
    (hbox : {J : Fin n → ℝ | ∀ j, |J j| ≤ b j} ⊆ U)
    (hdrift : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), x ∈ (Set.univ : Set (Fin n → ℝ)) ×ˢ U →
      (∀ j, |x.2 j| ≤ b j) → ∀ j, |(F x).2 j| ≤ η j)
    (x₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hx₀ : ∀ j, |x₀.2 j| ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ w : ℝ → (Fin n → ℝ) × (Fin n → ℝ), w 0 = x₀ ∧
      (∀ t ∈ Set.Ioo (-T₁) T₁, w t ∈ (Set.univ : Set (Fin n → ℝ)) ×ˢ U ∧
        HasDerivAt w (F (w t)) t) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ j, |(w t).2 j - x₀.2 j| ≤ η j * |t| ∧ |(w t).2 j| ≤ a j + η j * T := by
  have hab : ∀ j, a j ≤ b j := fun j => by
    have := hmargin j; have := mul_nonneg hT (hη j); linarith
  have hx₀W : x₀ ∈ (Set.univ : Set (Fin n → ℝ)) ×ˢ U :=
    ⟨trivial, hbox fun j => (hx₀ j).trans (hab j)⟩
  obtain ⟨Tm, Tp, z, hz⟩ := (gen_maximal (isOpen_univ.prod hU) hF hx₀W).1
  have hcomp : ∀ t ∈ eIoo Tm Tp, ∀ j,
      HasDerivAt (fun s => (z s).2 j) ((F (z t)).2 j) t := fun t ht j =>
    hasDerivAt_pi.1 (hz.isSolution t ht).2.snd j
  obtain ⟨T₁, hT₁, hsub, hmain⟩ := exists_confined_aux hz (f := fun t => (z t).2)
    (f' := fun t => (F (z t)).2) hT hη hmargin (by simpa [hz.init] using hx₀)
    hcomp (fun t ht hb => hdrift (z t) (hz.isSolution t ht).1 hb)
    (fun h => (gen_continuation_periodic hU hF hper hz (isCompact_actionBoxClosed b) hbox).1
      ⟨0, le_rfl, hz.pos_lt, fun t ht0 htp => h t ht0 htp⟩)
    (fun h => (gen_continuation_periodic hU hF hper hz (isCompact_actionBoxClosed b) hbox).2
      ⟨0, le_rfl, hz.neg_lt, fun t htm ht0 => h t htm ht0⟩)
  refine ⟨T₁, hT₁, z, hz.init, fun t ht => hz.isSolution t (hsub ht), fun t htT j => ?_⟩
  simpa [hz.init] using (hmain t htT).2 j

end KAM.EffectiveStability
