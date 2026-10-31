/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Diag
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The two-sided coordinate space (blueprint-W `bpW:w3:space`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:space`.

`BirkIdx = Bool × ℕ+` indexes `l ∈ ℤ ∖ {0}` by `(sign, |l|)` (`true` is `l > 0`), and
`BirkSpace = ℓ²(BirkIdx; ℂ)` carries `𝔚_{a,r}` in *weighted coordinates*: the point `y` represents
`w_l = y_l / ω_{a,r}(|l|)` (`birkCoord a r y l`), so `‖y‖ = ‖w‖_{a,r}`. A map into `𝔚^+ = 𝔚_{a,p+1}`
is a map into `BirkSpace` read at the weight `p + 1`. The inclusion `𝔚_{a,r} ⊂ 𝔚_{a,r'}`
(`r' ≤ r`) is `birkEmbed`, the identity on actual coordinates, of norm `≤ 1`.

* `birkDiagCLM`: bounded diagonal multipliers on `ℓ²(ι; 𝕂)` for any index type.
* `birkRho`: the conjugate-linear isometric involution `ϱ(w)_l = conj w_{-l}`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

/-- `l ∈ ℤ ∖ {0}` as the pair `(l > 0, |l|)`. -/
abbrev BirkIdx : Type := Bool × ℕ+

/-- `𝔚` in weighted coordinates (blueprint `bpW:w3:space`): `ℓ²` over `ℤ ∖ {0}`. -/
abbrev BirkSpace : Type := lp (fun _ : BirkIdx => ℂ) 2

/-- The index `-l`. -/
def birkNeg (l : BirkIdx) : BirkIdx := (!l.1, l.2)

@[simp] theorem birkNeg_birkNeg (l : BirkIdx) : birkNeg (birkNeg l) = l := by
  simp [birkNeg]

@[simp] theorem birkNeg_snd (l : BirkIdx) : (birkNeg l).2 = l.2 := rfl

/-- The involution `l ↦ -l` as an equivalence. -/
def birkNegEquiv : BirkIdx ≃ BirkIdx where
  toFun := birkNeg
  invFun := birkNeg
  left_inv := birkNeg_birkNeg
  right_inv := birkNeg_birkNeg

/-- `sgn l ∈ {1, -1}`. -/
def birkSgn (l : BirkIdx) : ℂ := if l.1 then 1 else -1

@[simp] theorem birkSgn_neg (l : BirkIdx) : birkSgn (birkNeg l) = -birkSgn l := by
  cases l with | mk b j => cases b <;> simp [birkSgn, birkNeg]

theorem birkSgn_mul_self (l : BirkIdx) : birkSgn l * birkSgn l = 1 := by
  cases l with | mk b j => cases b <;> simp [birkSgn]

theorem norm_birkSgn (l : BirkIdx) : ‖birkSgn l‖ = 1 := by
  cases l with | mk b j => cases b <;> simp [birkSgn]

theorem birkSgn_conj (l : BirkIdx) : starRingEnd ℂ (birkSgn l) = birkSgn l := by
  cases l with | mk b j => cases b <;> simp [birkSgn]

/-- The frequency `λ'_l = sgn(l) λ_{|l|}`. -/
def birkLam (m : ℝ) (hm : 0 < m) (l : BirkIdx) : ℝ := (if l.1 then 1 else -1) * lam m hm l.2

/-- The coordinate `w_l = y_l / ω_{a,r}(|l|)` represented by `y` (blueprint `bpW:w3:space`). -/
def birkCoord (a r : ℝ) (y : BirkSpace) (l : BirkIdx) : ℂ :=
  y l / (RCLike.ofReal (ellWeight a r l.2) : ℂ)

theorem birkCoord_mul_weight (a r : ℝ) (y : BirkSpace) (l : BirkIdx) :
    birkCoord a r y l * (RCLike.ofReal (ellWeight a r l.2) : ℂ) = y l := by
  have := ellWeight_cast_ne_zero (K := ℂ) a r l.2
  exact div_mul_cancel₀ _ this

theorem birkCoord_add (a r : ℝ) (y y' : BirkSpace) (l : BirkIdx) :
    birkCoord a r (y + y') l = birkCoord a r y l + birkCoord a r y' l := by
  simp [birkCoord, add_div]

theorem birkCoord_smul (a r : ℝ) (c : ℂ) (y : BirkSpace) (l : BirkIdx) :
    birkCoord a r (c • y) l = c * birkCoord a r y l := by
  simp [birkCoord, mul_div_assoc]

theorem birkCoord_sub (a r : ℝ) (y y' : BirkSpace) (l : BirkIdx) :
    birkCoord a r (y - y') l = birkCoord a r y l - birkCoord a r y' l := by
  simp [birkCoord, sub_div]

theorem birkCoord_neg (a r : ℝ) (y : BirkSpace) (l : BirkIdx) :
    birkCoord a r (-y) l = -birkCoord a r y l := by
  simp [birkCoord, neg_div]

theorem birk_one_le_weight {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (j : ℕ+) :
    1 ≤ ellWeight a r j := by
  unfold ellWeight
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow h1 hr)
    (Real.one_le_exp (mul_nonneg ha (by positivity)))

theorem norm_birkCoord_le {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (y : BirkSpace) (l : BirkIdx) :
    ‖birkCoord a r y l‖ ≤ ‖y l‖ := by
  rw [birkCoord, norm_div, norm_ellWeight_cast]
  exact div_le_self (norm_nonneg _) (birk_one_le_weight ha hr l.2)

/-! ### Sums over `BirkIdx` -/

theorem birk_summable_iff {f : BirkIdx → ℝ} (hf : 0 ≤ f) :
    Summable f ↔ Summable (fun j : ℕ+ => f (true, j)) ∧ Summable (fun j : ℕ+ => f (false, j)) := by
  rw [summable_prod_of_nonneg hf]
  refine ⟨fun ⟨h, _⟩ => ⟨h true, h false⟩, fun ⟨h1, h2⟩ => ⟨fun b => ?_, Summable.of_finite⟩⟩
  cases b <;> assumption

theorem birk_tsum_split {f : BirkIdx → ℝ} (hf : Summable f) :
    ∑' l, f l = ∑' j : ℕ+, f (true, j) + ∑' j : ℕ+, f (false, j) := by
  rw [Summable.tsum_prod hf, tsum_fintype, Fintype.sum_bool]

theorem birk_hasSum_split {f : BirkIdx → ℝ} {s t : ℝ}
    (h1 : HasSum (fun j : ℕ+ => f (true, j)) s) (h2 : HasSum (fun j : ℕ+ => f (false, j)) t)
    (hf : Summable f) : HasSum f (s + t) := by
  rw [← h1.tsum_eq, ← h2.tsum_eq, ← birk_tsum_split hf]; exact hf.hasSum

/-! ### Diagonal multipliers on `ℓ²` over an arbitrary index type -/

section Diag

variable {ι : Type*} {K : Type*} [RCLike K]

theorem memℓp_lpDiag {μ : ι → K} {M : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M) (y : lp (fun _ : ι => K) 2) :
    Memℓp (fun j => μ j * y j) 2 := by
  refine memℓp_gen ?_
  have hs : Summable fun j => M ^ 2 * ‖y j‖ ^ 2 := (lp_two_hasSum_sq y).summable.mul_left _
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hs
  have h0 : 0 ≤ ‖μ j‖ := norm_nonneg _
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul]
  rw [mul_pow]
  gcongr
  exact hM j

/-- The bounded diagonal operator `y ↦ (μ_l y_l)` on `ℓ²(ι; 𝕂)` for `‖μ_l‖ ≤ M`. -/
def lpDiagCLM (μ : ι → K) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, ‖μ j‖ ≤ M) :
    lp (fun _ : ι => K) 2 →L[K] lp (fun _ : ι => K) 2 :=
  LinearMap.mkContinuous
    { toFun := fun y => ⟨fun j => μ j * y j, memℓp_lpDiag hM y⟩
      map_add' := fun y y' => by ext j; simp [mul_add]; rfl
      map_smul' := fun c y => by ext j; simp [mul_left_comm] }
    M
    (fun y => by
      have h0 := hM0
      have hsq : ‖(⟨fun j => μ j * y j, memℓp_lpDiag hM y⟩ : lp (fun _ : ι => K) 2)‖ ^ 2 ≤
          (M * ‖y‖) ^ 2 := by
        have := hasSum_le (fun j => ?_) (lp_two_hasSum_sq
          (⟨fun j => μ j * y j, memℓp_lpDiag hM y⟩ : lp (fun _ : ι => K) 2))
          ((lp_two_hasSum_sq y).mul_left (M ^ 2))
        · simpa [mul_pow] using this
        · simp only [norm_mul]
          rw [mul_pow]
          gcongr
          exact hM j
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _))
        two_ne_zero).1 hsq)

@[simp] theorem lpDiagCLM_apply (μ : ι → K) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, ‖μ j‖ ≤ M)
    (y : lp (fun _ : ι => K) 2) (j : ι) : lpDiagCLM μ hM0 hM y j = μ j * y j := rfl

theorem norm_lpDiagCLM_le (μ : ι → K) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, ‖μ j‖ ≤ M) :
    ‖lpDiagCLM μ hM0 hM‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ hM0 _

/-- A bounded operator acting diagonally with multiplier `μ` has `‖μ_j‖ ≤ ‖T‖`. -/
theorem norm_le_norm_of_lpDiag_apply [DecidableEq ι] {μ : ι → K}
    (T : lp (fun _ : ι => K) 2 →L[K] lp (fun _ : ι => K) 2)
    (hT : ∀ y j, T y j = μ j * y j) (j : ι) : ‖μ j‖ ≤ ‖T‖ := by
  have h1 : T (lp.single 2 j (1 : K)) = lp.single 2 j (μ j) := by
    ext i
    rw [hT]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have h2 := T.le_opNorm (lp.single 2 j (1 : K))
  rw [h1, lp.norm_single (by norm_num), lp.norm_single (by norm_num), norm_one, mul_one] at h2
  exact h2

/-- A diagonal map with unbounded multiplier is not a bounded operator. -/
theorem not_exists_lpDiag_of_unbounded [DecidableEq ι] {μ : ι → K}
    (hμ : ∀ B : ℝ, ∃ j, B < ‖μ j‖) :
    ¬ ∃ T : lp (fun _ : ι => K) 2 →L[K] lp (fun _ : ι => K) 2, ∀ y j, T y j = μ j * y j := by
  rintro ⟨T, hT⟩
  obtain ⟨j, hj⟩ := hμ ‖T‖
  exact absurd (norm_le_norm_of_lpDiag_apply T hT j) (not_le.2 hj)

end Diag

/-! ### The inclusion `𝔚_{a,r} ⊂ 𝔚_{a,r'}` -/

theorem norm_birkEmbedRatio_le_one {a r r' : ℝ} (h : r' ≤ r) (l : BirkIdx) :
    ‖(RCLike.ofReal (embedRatio a r a r' l.2) : ℂ)‖ ≤ 1 :=
  norm_embedRatio_cast_le_one (K := ℂ) (le_refl a) h l.2

/-- The inclusion `𝔚_{a,r} ⊂ 𝔚_{a,r'}` for `r' ≤ r`, the identity on actual coordinates
(`birkCoord_birkEmbed`). Used with `r = p + 1`, `r' = p` for `𝔚^+ ⊂ 𝔚`. -/
def birkEmbed (a r r' : ℝ) (h : r' ≤ r) : BirkSpace →L[ℂ] BirkSpace :=
  lpDiagCLM (fun l : BirkIdx => (RCLike.ofReal (embedRatio a r a r' l.2) : ℂ)) zero_le_one
    (norm_birkEmbedRatio_le_one h)

@[simp] theorem birkEmbed_apply (a r r' : ℝ) (h : r' ≤ r) (y : BirkSpace) (l : BirkIdx) :
    birkEmbed a r r' h y l = (RCLike.ofReal (embedRatio a r a r' l.2) : ℂ) * y l := rfl

theorem norm_birkEmbed_le (a r r' : ℝ) (h : r' ≤ r) : ‖birkEmbed a r r' h‖ ≤ 1 :=
  norm_lpDiagCLM_le _ _ _

theorem birkCoord_birkEmbed (a r r' : ℝ) (h : r' ≤ r) (y : BirkSpace) (l : BirkIdx) :
    birkCoord a r' (birkEmbed a r r' h y) l = birkCoord a r y l := by
  have h1 := ellWeight_cast_ne_zero (K := ℂ) a r l.2
  have h2 := ellWeight_cast_ne_zero (K := ℂ) a r' l.2
  simp only [birkCoord, birkEmbed_apply, embedRatio]
  push_cast
  field_simp

theorem birkEmbed_injective (a r r' : ℝ) (h : r' ≤ r) : Function.Injective (birkEmbed a r r' h) := by
  intro y y' hy
  ext l
  have := congrArg (fun z => birkCoord a r' z l) hy
  simp only [birkCoord_birkEmbed] at this
  have h1 := ellWeight_cast_ne_zero (K := ℂ) a r l.2
  simp only [birkCoord] at this
  exact (div_left_inj' h1).1 this

/-! ### The real structure `ϱ` -/

theorem memℓp_birkRho (y : BirkSpace) : Memℓp (fun l => starRingEnd ℂ (y (birkNeg l))) 2 := by
  refine memℓp_gen ?_
  have hs := (birkNegEquiv.summable_iff.2 (lp_two_hasSum_sq y).summable)
  simpa [Function.comp_def, birkNegEquiv, Real.rpow_two] using hs

/-- `ϱ(w)_l = conj w_{-l}` (blueprint `bpW:w3:coords`): a conjugate-linear isometric involution. -/
def birkRho : BirkSpace →ₛₗᵢ[starRingEnd ℂ] BirkSpace where
  toFun y := ⟨fun l => starRingEnd ℂ (y (birkNeg l)), memℓp_birkRho y⟩
  map_add' y y' := by ext l; simp; rfl
  map_smul' c y := by ext l; simp
  norm_map' y := by
    have h1 := lp_two_hasSum_sq (⟨fun l => starRingEnd ℂ (y (birkNeg l)), memℓp_birkRho y⟩ :
      BirkSpace)
    have h2 := (Equiv.hasSum_iff birkNegEquiv).2 (lp_two_hasSum_sq y)
    have h3 : HasSum (fun l => ‖(⟨fun l => starRingEnd ℂ (y (birkNeg l)), memℓp_birkRho y⟩ :
        BirkSpace) l‖ ^ 2) (‖y‖ ^ 2) := by
      simpa [Function.comp_def, birkNegEquiv] using h2
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.unique h3)

@[simp] theorem birkRho_apply (y : BirkSpace) (l : BirkIdx) :
    birkRho y l = starRingEnd ℂ (y (birkNeg l)) := rfl

@[simp] theorem birkRho_birkRho (y : BirkSpace) : birkRho (birkRho y) = y := by
  ext l; simp

theorem birkRho_injective : Function.Injective birkRho := fun y y' h => by
  simpa using congrArg birkRho h

theorem birkCoord_birkRho (a r : ℝ) (y : BirkSpace) (l : BirkIdx) :
    birkCoord a r (birkRho y) l = starRingEnd ℂ (birkCoord a r y (birkNeg l)) := by
  have h1 := norm_ellWeight_cast (K := ℂ) a r l.2
  simp only [birkCoord, birkRho_apply, birkNeg_snd, map_div₀]
  congr 1
  simp

theorem birkRho_birkEmbed (a r r' : ℝ) (h : r' ≤ r) (y : BirkSpace) :
    birkRho (birkEmbed a r r' h y) = birkEmbed a r r' h (birkRho y) := by
  ext l
  simp [birkEmbed_apply]

end KAM.Wave

end
