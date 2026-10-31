/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.Coords

/-!
# The symplectic form (blueprint-W `bpW:w3:omega`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:omega`.

`birkOmega ha hr : 𝔚 →L 𝔚 →L ℂ`, `Ω(w,w') = i Σ_{l≠0} sgn(l) w_l w'_{-l}`, in the weighted
coordinates at weight `(a, r)` (`0 ≤ a`, `0 ≤ r`; the blueprint takes `r = p`).

* `birkOmega_apply`, `norm_birkOmega_le` (`|Ω(w,w')| ≤ ‖w‖‖w'‖`), `birkOmega_antisymm`;
* `birkOmega_unit_neg`, `birkOmega_nondegenerate`: `Ω(ζ, e_{-l}) = i sgn(l) ζ_l` for the unit
  vectors
  `e_l = birkUnit a r l` (`ω_{a,r}(l) δ_l` in weighted coordinates), so `Ω(ζ,·) = 0 ⇒ ζ = 0`;
* `birkOmega_birkZ`: `Ω(𝒵x, 𝒵x') = Σ_j (q_j p'_j - p_j q'_j)` (also over `ℝ`:
  `birkOmega_birkZ_real`);
* `birkOmega_birkRho`: `Ω(ϱw, ϱw') = conj Ω(w,w')`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable {a r : ℝ}

/-- Cauchy–Schwarz for the pairing `l ↦ ‖u_l‖ ‖v_{-l}‖`. -/
theorem birkPair_summable (u v : BirkSpace) :
    Summable (fun l => ‖u l‖ * ‖v (birkNeg l)‖) ∧
      ∑' l, ‖u l‖ * ‖v (birkNeg l)‖ ≤ ‖u‖ * ‖v‖ := by
  have hv : Summable fun l => ‖v (birkNeg l)‖ ^ 2 :=
    birkNegEquiv.summable_iff.2 (lp_two_hasSum_sq v).summable
  have h := waveCauchySchwarz_tsum (f := fun l => ‖u l‖) (g := fun l => ‖v (birkNeg l)‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (lp_two_hasSum_sq u).summable hv
  refine ⟨h.1, h.2.trans ?_⟩
  have e1 : Real.sqrt (∑' l, ‖u l‖ ^ 2) = ‖u‖ := by
    rw [(lp_two_hasSum_sq u).tsum_eq, Real.sqrt_sq (norm_nonneg _)]
  have e2 : Real.sqrt (∑' l, ‖v (birkNeg l)‖ ^ 2) = ‖v‖ := by
    have : ∑' l, ‖v (birkNeg l)‖ ^ 2 = ‖v‖ ^ 2 :=
      (birkNegEquiv.hasSum_iff.2 (lp_two_hasSum_sq v)).tsum_eq
    rw [this, Real.sqrt_sq (norm_nonneg _)]
  rw [e1, e2]

/-- The summand of the symplectic pairing. -/
def birkOmegaTerm (a r : ℝ) (y y' : BirkSpace) (l : BirkIdx) : ℂ :=
  birkSgn l * birkCoord a r y l * birkCoord a r y' (birkNeg l)

theorem norm_birkOmegaTerm_le (ha : 0 ≤ a) (hr : 0 ≤ r) (y y' : BirkSpace) (l : BirkIdx) :
    ‖birkOmegaTerm a r y y' l‖ ≤ ‖y l‖ * ‖y' (birkNeg l)‖ := by
  unfold birkOmegaTerm
  rw [norm_mul, norm_mul, norm_birkSgn, one_mul]
  exact mul_le_mul (norm_birkCoord_le ha hr y l) (norm_birkCoord_le ha hr y' _) (norm_nonneg _)
    (norm_nonneg _)

theorem summable_birkOmegaTerm (ha : 0 ≤ a) (hr : 0 ≤ r) (y y' : BirkSpace) :
    Summable (birkOmegaTerm a r y y') :=
  Summable.of_norm_bounded (birkPair_summable y y').1 (norm_birkOmegaTerm_le ha hr y y')

theorem birkOmegaTerm_add_left (y₁ y₂ y' : BirkSpace) (l : BirkIdx) :
    birkOmegaTerm a r (y₁ + y₂) y' l = birkOmegaTerm a r y₁ y' l + birkOmegaTerm a r y₂ y' l := by
  simp only [birkOmegaTerm, birkCoord_add]; ring

theorem birkOmegaTerm_add_right (y y₁ y₂ : BirkSpace) (l : BirkIdx) :
    birkOmegaTerm a r y (y₁ + y₂) l = birkOmegaTerm a r y y₁ l + birkOmegaTerm a r y y₂ l := by
  simp only [birkOmegaTerm, birkCoord_add]; ring

theorem birkOmegaTerm_smul_left (c : ℂ) (y y' : BirkSpace) (l : BirkIdx) :
    birkOmegaTerm a r (c • y) y' l = c * birkOmegaTerm a r y y' l := by
  simp only [birkOmegaTerm, birkCoord_smul]; ring

theorem birkOmegaTerm_smul_right (c : ℂ) (y y' : BirkSpace) (l : BirkIdx) :
    birkOmegaTerm a r y (c • y') l = c * birkOmegaTerm a r y y' l := by
  simp only [birkOmegaTerm, birkCoord_smul]; ring

/-- (`bpW:w3:omega`) The symplectic form `Ω(w,w') = i Σ_{l≠0} sgn(l) w_l w'_{-l}` on `𝔚_{a,r}`,
a continuous bilinear form. -/
def birkOmega (ha : 0 ≤ a) (hr : 0 ≤ r) : BirkSpace →L[ℂ] BirkSpace →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun y y' => Complex.I * ∑' l, birkOmegaTerm a r y y' l)
      (fun y₁ y₂ y' => by
        simp only [birkOmegaTerm_add_left]
        rw [(summable_birkOmegaTerm ha hr y₁ y').tsum_add (summable_birkOmegaTerm ha hr y₂ y'),
          mul_add])
      (fun c y y' => by
        simp only [birkOmegaTerm_smul_left, tsum_mul_left]; ring)
      (fun y y₁ y₂ => by
        simp only [birkOmegaTerm_add_right]
        rw [(summable_birkOmegaTerm ha hr y y₁).tsum_add (summable_birkOmegaTerm ha hr y y₂),
          mul_add])
      (fun c y y' => by
        simp only [birkOmegaTerm_smul_right, tsum_mul_left]; ring))
    1 (fun y y' => by
      simp only [LinearMap.mk₂_apply, norm_mul, Complex.norm_I, one_mul]
      calc ‖∑' l, birkOmegaTerm a r y y' l‖ ≤ ∑' l, ‖birkOmegaTerm a r y y' l‖ :=
            norm_tsum_le_tsum_norm (summable_birkOmegaTerm ha hr y y').norm
        _ ≤ ∑' l, ‖y l‖ * ‖y' (birkNeg l)‖ :=
            Summable.tsum_le_tsum (norm_birkOmegaTerm_le ha hr y y')
              (summable_birkOmegaTerm ha hr y y').norm (birkPair_summable y y').1
        _ ≤ ‖y‖ * ‖y'‖ := (birkPair_summable y y').2)

theorem birkOmega_apply (ha : 0 ≤ a) (hr : 0 ≤ r) (y y' : BirkSpace) :
    birkOmega ha hr y y' = Complex.I * ∑' l, birkSgn l * birkCoord a r y l *
      birkCoord a r y' (birkNeg l) := rfl

/-- (`bpW:w3:omega`) `|Ω(w,w')| ≤ ‖w‖ ‖w'‖`. -/
theorem norm_birkOmega_le (ha : 0 ≤ a) (hr : 0 ≤ r) (y y' : BirkSpace) :
    ‖birkOmega ha hr y y'‖ ≤ ‖y‖ * ‖y'‖ := by
  rw [birkOmega_apply, norm_mul, Complex.norm_I, one_mul]
  calc ‖∑' l, birkOmegaTerm a r y y' l‖ ≤ ∑' l, ‖birkOmegaTerm a r y y' l‖ :=
        norm_tsum_le_tsum_norm (summable_birkOmegaTerm ha hr y y').norm
    _ ≤ ∑' l, ‖y l‖ * ‖y' (birkNeg l)‖ :=
        Summable.tsum_le_tsum (norm_birkOmegaTerm_le ha hr y y')
          (summable_birkOmegaTerm ha hr y y').norm (birkPair_summable y y').1
    _ ≤ ‖y‖ * ‖y'‖ := (birkPair_summable y y').2

/-- (`bpW:w3:omega`) `Ω` is antisymmetric. -/
theorem birkOmega_antisymm (ha : 0 ≤ a) (hr : 0 ≤ r) (y y' : BirkSpace) :
    birkOmega ha hr y' y = -birkOmega ha hr y y' := by
  rw [birkOmega_apply, birkOmega_apply, ← mul_neg, ← tsum_neg]
  congr 1
  rw [← birkNegEquiv.tsum_eq (fun l => birkSgn l * birkCoord a r y' l * birkCoord a r y (birkNeg
      l))]
  refine tsum_congr fun l => ?_
  simp only [birkNegEquiv, Equiv.coe_fn_mk, birkSgn_neg, birkNeg_birkNeg]
  ring

/-- The unit vector `e_l`: `(e_l)_{l'} = δ_{ll'}` in the actual coordinates at weight `(a,r)`. -/
def birkUnit (a r : ℝ) (l : BirkIdx) : BirkSpace := lp.single 2 l (RCLike.ofReal (ellWeight a r l.2)
    : ℂ)

theorem birkCoord_birkUnit (a r : ℝ) (l l' : BirkIdx) :
    birkCoord a r (birkUnit a r l) l' = if l' = l then 1 else 0 := by
  have h := ellWeight_cast_ne_zero (K := ℂ) a r l.2
  by_cases hl : l' = l
  · subst hl; simp [birkCoord, birkUnit, ellWeight_ne_zero]
  · simp [birkCoord, birkUnit, hl]

/-- (`bpW:w3:omega`) `Ω(ζ, e_{-l}) = i sgn(l) ζ_l`. -/
theorem birkOmega_unit_neg (ha : 0 ≤ a) (hr : 0 ≤ r) (ζ : BirkSpace) (l : BirkIdx) :
    birkOmega ha hr ζ (birkUnit a r (birkNeg l)) = Complex.I * birkSgn l * birkCoord a r ζ l := by
  rw [birkOmega_apply]
  have : ∀ l', birkSgn l' * birkCoord a r ζ l' * birkCoord a r (birkUnit a r (birkNeg l)) (birkNeg
      l') =
      if l' = l then birkSgn l * birkCoord a r ζ l else 0 := by
    intro l'
    rw [birkCoord_birkUnit]
    by_cases h : l' = l
    · subst h; simp
    · have : birkNeg l' ≠ birkNeg l := fun e => h (by simpa using congrArg birkNeg e)
      simp [this, h]
  simp only [this, tsum_ite_eq]
  ring

/-- (`bpW:w3:omega`) `Ω` is nondegenerate: `Ω(ζ, ·) = 0` implies `ζ = 0`. -/
theorem birkOmega_nondegenerate (ha : 0 ≤ a) (hr : 0 ≤ r) {ζ : BirkSpace}
    (h : ∀ v, birkOmega ha hr ζ v = 0) : ζ = 0 := by
  ext l
  have h1 := birkOmega_unit_neg ha hr ζ l
  rw [h] at h1
  have hs : birkSgn l ≠ 0 := fun e => by simpa [e] using norm_birkSgn l
  have hc : birkCoord a r ζ l = 0 := by
    have : Complex.I * birkSgn l * birkCoord a r ζ l = 0 := h1.symm
    simpa [Complex.I_ne_zero, hs] using this
  have h2 := birkCoord_mul_weight a r ζ l
  rw [hc, zero_mul] at h2
  simpa using h2.symm

/-- (`bpW:w3:omega`) `Ω(ϱw, ϱw') = conj Ω(w, w')`. -/
theorem birkOmega_birkRho (ha : 0 ≤ a) (hr : 0 ≤ r) (y y' : BirkSpace) :
    birkOmega ha hr (birkRho y) (birkRho y') = conj (birkOmega ha hr y y') := by
  rw [birkOmega_apply, birkOmega_apply, map_mul, Complex.conj_I, Complex.conj_tsum]
  rw [neg_mul, ← mul_neg, ← tsum_neg]
  congr 1
  rw [← birkNegEquiv.tsum_eq (fun l => birkSgn l * birkCoord a r (birkRho y) l *
    birkCoord a r (birkRho y') (birkNeg l))]
  refine tsum_congr fun l => ?_
  simp only [birkNegEquiv, Equiv.coe_fn_mk, birkSgn_neg, birkNeg_birkNeg, birkCoord_birkRho,
      map_mul,
    birkSgn_conj]
  ring

/-- (`bpW:w3:omega`) `Ω(𝒵x, 𝒵x') = Σ_j (q_j p'_j - p_j q'_j)` (`q_j`, `p_j` the weighted-coordinate
values at weight `(a, r)`). -/
theorem birkOmega_birkZ (ha : 0 ≤ a) (hr : 0 ≤ r) (x x' : WaveSpaceK ℂ) :
    birkOmega ha hr (birkZ x) (birkZ x') =
      ∑' j : ℕ+, (coeffW a r x.1 j * coeffW a r x'.2 j - coeffW a r x.2 j * coeffW a r x'.1 j) := by
  have hs := summable_birkOmegaTerm ha hr (birkZ x) (birkZ x')
  have h1 : Summable fun j : ℕ+ => birkOmegaTerm a r (birkZ x) (birkZ x') (true, j) :=
    hs.comp_injective (i := fun j : ℕ+ => ((true, j) : BirkIdx)) fun j k h => (Prod.mk.inj h).2
  have h2 : Summable fun j : ℕ+ => birkOmegaTerm a r (birkZ x) (birkZ x') (false, j) :=
    hs.comp_injective (i := fun j : ℕ+ => ((false, j) : BirkIdx)) fun j k h => (Prod.mk.inj h).2
  rw [birkOmega_apply]
  change Complex.I * ∑' l, birkOmegaTerm a r (birkZ x) (birkZ x') l = _
  rw [birk_tsum_split hs, ← h1.tsum_add h2, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  have h3 := birkSqrt2_sq
  have h4 := birkSqrt2_ne
  simp only [birkOmegaTerm, birkSgn, birkNeg, ite_true, Bool.false_eq_true, ite_false,
      Bool.not_true,
    Bool.not_false, birkCoord_birkZ_true, birkCoord_birkZ_false]
  field_simp
  ring_nf
  simp only [Complex.I_sq, h3]
  ring

/-- (`bpW:w3:omega`) For real `x, x'`: `Ω(𝒵x, 𝒵x') = Σ_j (q_j p'_j - p_j q'_j)`, the form
`Σ dq_j ∧ dp_j` of Definition `bpW:w0:eqmotion`. -/
theorem birkOmega_birkZ_real (ha : 0 ≤ a) (hr : 0 ≤ r)
    (x x' : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) :
    birkOmega ha hr (birkZ (birkReal x)) (birkZ (birkReal x')) =
      ((∑' j : ℕ+, (coeffW (K := ℝ) a r x.1 j * coeffW (K := ℝ) a r x'.2 j -
        coeffW (K := ℝ) a r x.2 j * coeffW (K := ℝ) a r x'.1 j) : ℝ) : ℂ) := by
  rw [birkOmega_birkZ, Complex.ofReal_tsum]
  refine tsum_congr fun j => ?_
  simp only [birkReal_apply, coeffW_complexifyLp]
  push_cast
  ring

end KAM.Wave

end
