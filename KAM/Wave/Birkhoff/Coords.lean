/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.Space
public import KAM.Wave.Cubic.HamField

/-!
# Complex coordinates and real structure (blueprint-W `bpW:w3:coords`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:coords`.

`E^ℂ = ℓ^{a,p}_ℂ × ℓ^{a,p}_ℂ` is `WaveSpaceK ℂ` in weighted coordinates (max norm), and
`birkZ : E^ℂ →L[ℂ] 𝔚` is `(𝒵x)_{±j} = (q_j ± i p_j)/√2`. In weighted coordinates the formula is the
same at *every* weight `(a, r)` (`birkCoord_birkZ`), so the same map is the `𝒵` of
`E^ℂ_{a,p+1} → 𝔚^+`.

* `birkZ`, `birkZinv`, `birkZEquiv`: the `ℂ`-linear bijection with the inverse formulas;
* `norm_le_norm_birkZ`, `norm_birkZ_le`: `‖x‖_E ≤ ‖𝒵x‖ ≤ √2 ‖x‖_E`; `norm_birkZinv_le`;
* `birkRho_birkZ_real`, `exists_birkZ_of_birkRho_eq`: `𝒵` maps the real space onto the fixed set of
  `ϱ`
  (`birkReal` is the real inclusion `E_{a,p} ⊂ E^ℂ`), `birkCoord_mul_birkZ` for `w_j w_{-j}`.
The conjugate-linear isometric involution `ϱ` is `birkRho` of `KAM.Wave.Birkhoff.Space`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

/-- `√2` as a complex number. -/
abbrev birkSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

theorem birkSqrt2_sq : birkSqrt2 ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp

theorem birkSqrt2_ne : birkSqrt2 ≠ 0 := by
  have : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  exact Complex.ofReal_ne_zero.2 this

theorem norm_birkSqrt2 : ‖birkSqrt2‖ = Real.sqrt 2 := by
  simp [abs_of_nonneg (Real.sqrt_nonneg 2)]

theorem conj_birkSqrt2 : conj birkSqrt2 = birkSqrt2 := Complex.conj_ofReal _

/-- The parallelogram identity `|a + i b|² + |a - i b|² = 2(|a|² + |b|²)`. -/
theorem birk_parallelogram (a b : ℂ) :
    ‖a + Complex.I * b‖ ^ 2 + ‖a - Complex.I * b‖ ^ 2 = 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have := parallelogram_law_with_norm ℂ a (Complex.I * b)
  simp only [norm_mul, Complex.norm_I, one_mul] at this
  nlinarith [this]

theorem birk_sq_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := norm_add_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a + b), sq_nonneg (‖a‖ - ‖b‖)]

/-- The sequence `l ↦ (x₁_{|l|} + sgn(l) i x₂_{|l|})/√2`. -/
def birkZfun (x : WaveSpaceK ℂ) (l : BirkIdx) : ℂ :=
  (x.1 l.2 + birkSgn l * Complex.I * x.2 l.2) / birkSqrt2

theorem norm_birkZfun_sq_le (x : WaveSpaceK ℂ) (l : BirkIdx) :
    ‖birkZfun x l‖ ^ 2 ≤ ‖x.1 l.2‖ ^ 2 + ‖x.2 l.2‖ ^ 2 := by
  have h := birk_sq_le (x.1 l.2) (birkSgn l * Complex.I * x.2 l.2)
  have e : ‖birkSgn l * Complex.I * x.2 l.2‖ = ‖x.2 l.2‖ := by
    rw [norm_mul, norm_mul, norm_birkSgn, Complex.norm_I]; simp
  rw [e] at h
  unfold birkZfun
  rw [norm_div, norm_birkSqrt2, div_pow, Real.sq_sqrt (by norm_num)]
  rw [div_le_iff₀ (by norm_num)]
  linarith

theorem summable_birkZfun_sq (x : WaveSpaceK ℂ) : Summable fun l => ‖birkZfun x l‖ ^ 2 := by
  have hx1 := (lp_two_hasSum_sq x.1).summable
  have hx2 := (lp_two_hasSum_sq x.2).summable
  have hg : Summable fun l : BirkIdx => ‖x.1 l.2‖ ^ 2 + ‖x.2 l.2‖ ^ 2 := by
    rw [birk_summable_iff (fun l => by positivity)]
    exact ⟨hx1.add hx2, hx1.add hx2⟩
  exact Summable.of_nonneg_of_le (fun _ => by positivity) (norm_birkZfun_sq_le x) hg

theorem memℓp_birkZfun (x : WaveSpaceK ℂ) : Memℓp (birkZfun x) 2 := by
  refine memℓp_gen ?_
  simpa [Real.rpow_two] using summable_birkZfun_sq x

theorem birkZfun_add (x y : WaveSpaceK ℂ) (l : BirkIdx) :
    birkZfun (x + y) l = birkZfun x l + birkZfun y l := by
  simp only [birkZfun, Prod.fst_add, Prod.snd_add, lp.coeFn_add, Pi.add_apply]
  ring

theorem birkZfun_smul (c : ℂ) (x : WaveSpaceK ℂ) (l : BirkIdx) :
    birkZfun (c • x) l = c * birkZfun x l := by
  simp only [birkZfun, Prod.smul_fst, Prod.smul_snd, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- `‖𝒵x‖² = ‖q‖² + ‖p‖²` at the level of sequences. -/
theorem birkZfun_pair_sq (x : WaveSpaceK ℂ) (j : ℕ+) :
    ‖birkZfun x (true, j)‖ ^ 2 + ‖birkZfun x (false, j)‖ ^ 2 = ‖x.1 j‖ ^ 2 + ‖x.2 j‖ ^ 2 := by
  have h := birk_parallelogram (x.1 j) (x.2 j)
  have e : ∀ s : ℂ, ‖s‖ = 1 → ‖birkZfun x (true, j)‖ ^ 2 = ‖x.1 j + Complex.I * x.2 j‖ ^ 2 / 2 := by
    intro _ _
    simp only [birkZfun, birkSgn, ite_true, one_mul, norm_div, norm_birkSqrt2, div_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have e1 := e 1 (by simp)
  have e2 : ‖birkZfun x (false, j)‖ ^ 2 = ‖x.1 j - Complex.I * x.2 j‖ ^ 2 / 2 := by
    simp only [birkZfun, birkSgn, Bool.false_eq_true, ite_false, norm_div, norm_birkSqrt2, div_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    congr 3
    ring
  rw [e1, e2]; linarith

/-- `‖𝒵x‖² = ‖q‖² + ‖p‖²`. -/
theorem norm_sq_birkZfun (x : WaveSpaceK ℂ) :
    ‖(⟨birkZfun x, memℓp_birkZfun x⟩ : BirkSpace)‖ ^ 2 = ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 := by
  have h1 := lp_two_hasSum_sq (⟨birkZfun x, memℓp_birkZfun x⟩ : BirkSpace)
  have hs := summable_birkZfun_sq x
  have hsb := (birk_summable_iff (fun l => by positivity)).1 hs
  rw [← h1.tsum_eq]
  show ∑' l, ‖birkZfun x l‖ ^ 2 = _
  rw [birk_tsum_split hs, ← hsb.1.tsum_add hsb.2]
  have h2 : HasSum (fun j : ℕ+ => ‖x.1 j‖ ^ 2 + ‖x.2 j‖ ^ 2) (‖x.1‖ ^ 2 + ‖x.2‖ ^ 2) :=
    (lp_two_hasSum_sq x.1).add (lp_two_hasSum_sq x.2)
  rw [← h2.tsum_eq]
  exact tsum_congr fun j => birkZfun_pair_sq x j

/-- (`bpW:w3:coords`) The continuous linear map `𝒵 : E^ℂ → 𝔚`, `(𝒵x)_{±j} = (q_j ± i p_j)/√2`,
in weighted coordinates. -/
def birkZ : WaveSpaceK ℂ →L[ℂ] BirkSpace :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨birkZfun x, memℓp_birkZfun x⟩
      map_add' := fun x y => by ext l; exact birkZfun_add x y l
      map_smul' := fun c x => by ext l; exact birkZfun_smul c x l }
    (Real.sqrt 2) (fun x => by
      have h := norm_sq_birkZfun x
      have hm : max ‖x.1‖ ‖x.2‖ = ‖x‖ := (Prod.norm_def x).symm
      have h1 : ‖x.1‖ ≤ ‖x‖ := hm ▸ le_max_left _ _
      have h2 : ‖x.2‖ ≤ ‖x‖ := hm ▸ le_max_right _ _
      have hb : ‖(⟨birkZfun x, memℓp_birkZfun x⟩ : BirkSpace)‖ ^ 2 ≤ (Real.sqrt 2 * ‖x‖) ^ 2 := by
        rw [h, mul_pow, Real.sq_sqrt (by norm_num)]
        nlinarith [norm_nonneg x.1, norm_nonneg x.2]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hb)

@[simp] theorem birkZ_apply (x : WaveSpaceK ℂ) (l : BirkIdx) :
    birkZ x l = (x.1 l.2 + birkSgn l * Complex.I * x.2 l.2) / birkSqrt2 := rfl

theorem norm_sq_birkZ (x : WaveSpaceK ℂ) : ‖birkZ x‖ ^ 2 = ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 :=
  norm_sq_birkZfun x

/-- (`bpW:w3:coords`) `‖x‖_E ≤ ‖𝒵x‖`. -/
theorem norm_le_norm_birkZ (x : WaveSpaceK ℂ) : ‖x‖ ≤ ‖birkZ x‖ := by
  have h := norm_sq_birkZ x
  rw [Prod.norm_def]
  refine max_le ?_ ?_ <;>
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    nlinarith [norm_nonneg x.1, norm_nonneg x.2]

/-- (`bpW:w3:coords`) `‖𝒵x‖ ≤ √2 ‖x‖_E`. -/
theorem norm_birkZ_le (x : WaveSpaceK ℂ) : ‖birkZ x‖ ≤ Real.sqrt 2 * ‖x‖ :=
  (birkZ.le_opNorm x).trans (by
    gcongr
    exact (ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2) fun x => by
      have h := norm_sq_birkZ x
      have hm : max ‖x.1‖ ‖x.2‖ = ‖x‖ := (Prod.norm_def x).symm
      have h1 : ‖x.1‖ ≤ ‖x‖ := hm ▸ le_max_left _ _
      have h2 : ‖x.2‖ ≤ ‖x‖ := hm ▸ le_max_right _ _
      have hb : ‖birkZ x‖ ^ 2 ≤ (Real.sqrt 2 * ‖x‖) ^ 2 := by
        rw [h, mul_pow, Real.sq_sqrt (by norm_num)]
        nlinarith [norm_nonneg x.1, norm_nonneg x.2]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hb))

/-! ### The inverse -/

theorem birk_hasSum_sq_pair (w : BirkSpace) :
    HasSum (fun j : ℕ+ => ‖w (true, j)‖ ^ 2 + ‖w (false, j)‖ ^ 2) (‖w‖ ^ 2) := by
  have h := lp_two_hasSum_sq w
  have hb := (birk_summable_iff (fun l => by positivity)).1 h.summable
  have := (hb.1.add hb.2).hasSum
  convert this using 1
  rw [← h.tsum_eq, birk_tsum_split h.summable, hb.1.tsum_add hb.2]

/-- The sequences `q_j = (w_j + w_{-j})/√2`, `p_j = (w_j - w_{-j})/(i√2)`. -/
def birkZinvFst (w : BirkSpace) (j : ℕ+) : ℂ := (w (true, j) + w (false, j)) / birkSqrt2

/-- The sequence `p_j = (w_j - w_{-j})/(i√2)`. -/
def birkZinvSnd (w : BirkSpace) (j : ℕ+) : ℂ :=
  (w (true, j) - w (false, j)) / (Complex.I * birkSqrt2)

theorem norm_birkZinvFst_sq_le (w : BirkSpace) (j : ℕ+) :
    ‖birkZinvFst w j‖ ^ 2 ≤ ‖w (true, j)‖ ^ 2 + ‖w (false, j)‖ ^ 2 := by
  have h := birk_sq_le (w (true, j)) (w (false, j))
  unfold birkZinvFst
  rw [norm_div, norm_birkSqrt2, div_pow, Real.sq_sqrt (by norm_num), div_le_iff₀ (by norm_num)]
  linarith

theorem norm_birkZinvSnd_sq_le (w : BirkSpace) (j : ℕ+) :
    ‖birkZinvSnd w j‖ ^ 2 ≤ ‖w (true, j)‖ ^ 2 + ‖w (false, j)‖ ^ 2 := by
  have h := birk_sq_le (w (true, j)) (-w (false, j))
  rw [norm_neg, ← sub_eq_add_neg] at h
  unfold birkZinvSnd
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, norm_birkSqrt2, div_pow,
    Real.sq_sqrt (by norm_num), div_le_iff₀ (by norm_num)]
  linarith

theorem memℓp_birkZinv (w : BirkSpace) :
    Memℓp (birkZinvFst w) 2 ∧ Memℓp (birkZinvSnd w) 2 := by
  have hb := (birk_summable_iff (fun l => by positivity)).1 (lp_two_hasSum_sq w).summable
  have hg := hb.1.add hb.2
  exact ⟨memℓp_gen (by simpa [Real.rpow_two] using
      Summable.of_nonneg_of_le (fun _ => by positivity) (norm_birkZinvFst_sq_le w) hg),
    memℓp_gen (by simpa [Real.rpow_two] using
      Summable.of_nonneg_of_le (fun _ => by positivity) (norm_birkZinvSnd_sq_le w) hg)⟩

/-- The inverse of `𝒵`: `q_j = (w_j + w_{-j})/√2`, `p_j = (w_j - w_{-j})/(i√2)`. -/
def birkZinv : BirkSpace →L[ℂ] WaveSpaceK ℂ :=
  LinearMap.mkContinuous
    { toFun := fun w => (⟨birkZinvFst w, (memℓp_birkZinv w).1⟩, ⟨birkZinvSnd w,
        (memℓp_birkZinv w).2⟩)
      map_add' := fun w w' => by
        refine Prod.ext (lp.ext (funext fun j => ?_)) (lp.ext (funext fun j => ?_))
        · show (w (true, j) + w' (true, j) + (w (false, j) + w' (false, j))) / birkSqrt2 =
            (w (true, j) + w (false, j)) / birkSqrt2 + (w' (true, j) + w' (false, j)) / birkSqrt2
          ring
        · show (w (true, j) + w' (true, j) - (w (false, j) + w' (false, j))) /
              (Complex.I * birkSqrt2) =
            (w (true, j) - w (false, j)) / (Complex.I * birkSqrt2) +
              (w' (true, j) - w' (false, j)) / (Complex.I * birkSqrt2)
          ring
      map_smul' := fun c w => by
        refine Prod.ext (lp.ext (funext fun j => ?_)) (lp.ext (funext fun j => ?_))
        · show (c * w (true, j) + c * w (false, j)) / birkSqrt2 =
            c * ((w (true, j) + w (false, j)) / birkSqrt2)
          ring
        · show (c * w (true, j) - c * w (false, j)) / (Complex.I * birkSqrt2) =
            c * ((w (true, j) - w (false, j)) / (Complex.I * birkSqrt2))
          ring }
    1 (fun w => by
      rw [Prod.norm_def, one_mul]
      have h := birk_hasSum_sq_pair w
      refine max_le ?_ ?_ <;>
      · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
        refine hasSum_le (fun j => ?_) (lp_two_hasSum_sq _) h
        first | exact norm_birkZinvFst_sq_le w j | exact norm_birkZinvSnd_sq_le w j)

@[simp] theorem birkZinv_fst_apply (w : BirkSpace) (j : ℕ+) :
    (birkZinv w).1 j = (w (true, j) + w (false, j)) / birkSqrt2 := rfl

@[simp] theorem birkZinv_snd_apply (w : BirkSpace) (j : ℕ+) :
    (birkZinv w).2 j = (w (true, j) - w (false, j)) / (Complex.I * birkSqrt2) := rfl

theorem norm_birkZinv_le (w : BirkSpace) : ‖birkZinv w‖ ≤ ‖w‖ := by
  have := birkZinv.le_opNorm w
  refine this.trans ?_
  have hn : ‖birkZinv‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    rw [Prod.norm_def]
    have h := birk_hasSum_sq_pair w
    refine max_le ?_ ?_ <;>
    · rw [one_mul]
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
      refine hasSum_le (fun j => ?_) (lp_two_hasSum_sq _) h
      first | exact norm_birkZinvFst_sq_le w j | exact norm_birkZinvSnd_sq_le w j
  nlinarith [norm_nonneg w]

theorem birkZinv_birkZ (x : WaveSpaceK ℂ) : birkZinv (birkZ x) = x := by
  have h2 := birkSqrt2_ne
  have h3 := birkSqrt2_sq
  have hI := Complex.I_ne_zero
  refine Prod.ext ?_ ?_ <;> ext j
  · simp only [birkZinv_fst_apply, birkZ_apply, birkSgn, ite_true, Bool.false_eq_true, ite_false]
    field_simp
    linear_combination (-(x.1 j)) * h3
  · simp only [birkZinv_snd_apply, birkZ_apply, birkSgn, ite_true, Bool.false_eq_true, ite_false]
    field_simp
    linear_combination (-(Complex.I * x.2 j)) * h3

theorem birkZ_birkZinv (w : BirkSpace) : birkZ (birkZinv w) = w := by
  have h2 := birkSqrt2_ne
  have h3 := birkSqrt2_sq
  have hI := Complex.I_ne_zero
  ext ⟨b, j⟩
  cases b
  · simp only [birkZ_apply, birkZinv_fst_apply, birkZinv_snd_apply, birkSgn, Bool.false_eq_true,
      ite_false]
    field_simp
    linear_combination (-(w (false, j))) * h3
  · simp only [birkZ_apply, birkZinv_fst_apply, birkZinv_snd_apply, birkSgn, ite_true]
    field_simp
    linear_combination (-(w (true, j))) * h3

/-- (`bpW:w3:coords`) `𝒵` is a `ℂ`-linear bijection `E^ℂ ≃ 𝔚` (a continuous linear equivalence). -/
def birkZEquiv : WaveSpaceK ℂ ≃L[ℂ] BirkSpace :=
  ContinuousLinearEquiv.equivOfInverse birkZ birkZinv birkZinv_birkZ birkZ_birkZinv

theorem birkZEquiv_apply (x : WaveSpaceK ℂ) : birkZEquiv x = birkZ x := rfl

theorem birkZEquiv_symm_apply (w : BirkSpace) : birkZEquiv.symm w = birkZinv w := rfl

/-- `‖𝒵⁻¹ w‖_E ≤ ‖w‖ ≤ √2 ‖𝒵⁻¹ w‖_E`. -/
theorem norm_le_sqrt_two_mul_birkZinv (w : BirkSpace) : ‖w‖ ≤ Real.sqrt 2 * ‖birkZinv w‖ := by
  have := norm_birkZ_le (birkZinv w)
  rwa [birkZ_birkZinv] at this

/-! ### Coordinates at every weight -/

/-- (`bpW:w3:coords`) `(𝒵x)_{j} = (q_j + i p_j)/√2` in the actual coordinates at any weight. -/
theorem birkCoord_birkZ_true (a r : ℝ) (x : WaveSpaceK ℂ) (j : ℕ+) :
    birkCoord a r (birkZ x) (true, j) = (coeffW a r x.1 j + Complex.I * coeffW a r x.2 j) /
        birkSqrt2 := by
  simp only [birkCoord, birkZ_apply, birkSgn, ite_true, one_mul, coeffW_apply]
  ring

/-- (`bpW:w3:coords`) `(𝒵x)_{-j} = (q_j - i p_j)/√2`. -/
theorem birkCoord_birkZ_false (a r : ℝ) (x : WaveSpaceK ℂ) (j : ℕ+) :
    birkCoord a r (birkZ x) (false, j) = (coeffW a r x.1 j - Complex.I * coeffW a r x.2 j) /
        birkSqrt2 := by
  simp only [birkCoord, birkZ_apply, birkSgn, Bool.false_eq_true, ite_false, coeffW_apply]
  ring

/-- `w_j w_{-j} = (q_j² + p_j²)/2`. -/
theorem birkCoord_mul_birkZ (a r : ℝ) (x : WaveSpaceK ℂ) (j : ℕ+) :
    birkCoord a r (birkZ x) (true, j) * birkCoord a r (birkZ x) (false, j) =
      (coeffW a r x.1 j ^ 2 + coeffW a r x.2 j ^ 2) / 2 := by
  rw [birkCoord_birkZ_true, birkCoord_birkZ_false]
  have h := birkSqrt2_sq
  have h2 := birkSqrt2_ne
  field_simp
  rw [h]
  ring_nf
  simp [Complex.I_sq]

/-! ### Real points -/

/-- The real inclusion `E_{a,p} ⊂ E^ℂ` (in weighted coordinates, componentwise `ι`). -/
def birkReal : (lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) →L[ℝ] WaveSpaceK ℂ :=
  (complexifyLp.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (complexifyLp.comp (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem birkReal_apply (x : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) :
    birkReal x = (complexifyLp x.1, complexifyLp x.2) := rfl

theorem birkReal_injective : Function.Injective birkReal := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext ?_ ?_
  · simpa using congrArg reLp h1
  · simpa using congrArg reLp h2

/-- (`bpW:w3:coords`) `ϱ` fixes the image of the real space. -/
theorem birkRho_birkZ_real (x : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2) :
    birkRho (birkZ (birkReal x)) = birkZ (birkReal x) := by
  ext ⟨b, j⟩
  have h2 := birkSqrt2_ne
  cases b
  · simp [birkRho_apply, birkNeg, birkSgn, map_div₀, Complex.conj_ofReal]
  · simp [birkRho_apply, birkNeg, birkSgn, map_div₀, Complex.conj_ofReal]

/-- (`bpW:w3:coords`) Every `ϱ`-fixed point is `𝒵` of a real point: `𝒵` maps `E_{a,p}`
onto `{ϱ w = w}`. -/
theorem exists_birkZ_of_birkRho_eq (w : BirkSpace) (hw : birkRho w = w) :
    ∃ x : lp (fun _ : ℕ+ => ℝ) 2 × lp (fun _ : ℕ+ => ℝ) 2, birkZ (birkReal x) = w := by
  have h2 := birkSqrt2_ne
  have hI := Complex.I_ne_zero
  have hc : ∀ j : ℕ+, conj (w (true, j)) = w (false, j) := fun j => by
    have := congrArg (fun z : BirkSpace => z (false, j)) hw
    simpa [birkNeg] using this
  have hc' : ∀ j : ℕ+, conj (w (false, j)) = w (true, j) := fun j => by
    rw [← hc j, Complex.conj_conj]
  have re1 : ∀ j : ℕ+, conj ((birkZinv w).1 j) = (birkZinv w).1 j := fun j => by
    simp only [birkZinv_fst_apply, map_div₀, map_add, conj_birkSqrt2, hc, hc']
    rw [add_comm]
  have re2 : ∀ j : ℕ+, conj ((birkZinv w).2 j) = (birkZinv w).2 j := fun j => by
    simp only [birkZinv_snd_apply, map_div₀, map_sub, map_mul, conj_birkSqrt2, hc, hc',
      Complex.conj_I]
    field_simp
    ring
  have e1 : ∀ j : ℕ+, (((birkZinv w).1 j).re : ℂ) = (birkZinv w).1 j := fun j =>
    (Complex.conj_eq_iff_re.1 (re1 j))
  have e2 : ∀ j : ℕ+, (((birkZinv w).2 j).re : ℂ) = (birkZinv w).2 j := fun j =>
    (Complex.conj_eq_iff_re.1 (re2 j))
  refine ⟨(reLp (birkZinv w).1, reLp (birkZinv w).2), ?_⟩
  have hx : birkReal (reLp (birkZinv w).1, reLp (birkZinv w).2) = birkZinv w :=
    Prod.ext (lp.ext (funext fun j => e1 j)) (lp.ext (funext fun j => e2 j))
  rw [hx]
  exact birkZ_birkZinv w

end KAM.Wave

end
