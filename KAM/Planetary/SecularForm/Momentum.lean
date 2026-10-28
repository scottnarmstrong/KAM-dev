/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.ParameterIntegral
public import KAM.Planetary.SecularForm.ProductInterface
public import KAM.Planetary.Poincare.Symplectic
public import KAM.Planetary.Poincare.D25

/-!
# Secular form: exact orthogonality of the momenta (Lemma 64) and the identification

Blueprint P, Part 8 (`bpP:p8:lemma64`, `stepP:p8:l64-a` .. `l64-e`, `bpP:p8:identification`,
`stepP:p8:id-diff`, `id-avg`, `id-int`).  The momentum `p^{(i)}` of body `i` and its position
`q^{(i)}` depend on the angles only through `λ_i`; `m_i ν_i ∂_{λ_i} q^{(i)} = p^{(i)}` is the
decoupled Kepler field transported by the product chart (`pc_dec`, `product_chart`), the period
mean of `p^{(i)}` vanishes by periodicity of `q^{(i)}`, the cross means vanish by Fubini, and the
virial value comes from the single-planet means.  The moving and fixed perturbations differ by
`|Σ p^{(i)}|²/(2 m₀)`, whose average is `modelDelta`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

def momentum (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) : Fin 2 → ℝ :=
  bodyVector (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)).2 i
def position (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) : Fin 2 → ℝ :=
  bodyVector (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i

/-! ### Block calculus -/

/-- The slow data of planet `i` with its angle replaced by `s`. -/
def blk (x : Slow n) (i : Fin n) (s : ℝ) : Phase 2 := (![s, x.1 i], ![x.2.1 i, x.2.2 i])

theorem blk_mem {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) (s : ℝ) :
    blk x i s ∈ poincareDom := by
  have := hx i
  rw [planetBlock_assemble] at this
  simpa [poincareDom, poincareGamma, blk] using this

theorem assemble_mem {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (t : Vec n) :
    (assemble x.2.1 t x.2.2 x.1 : Phase (n + n)) ∈ poincareProdDom n := by
  intro i
  rw [planetBlock_assemble]
  exact blk_mem hx i (t i)

theorem position_eq_block (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) :
    position D x t i = (poincare (D.m i) (D.G*D.m0) (blk x i (t i))).1 := by
  have := poincareProd_block D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1) i
  rw [planetBlock_assemble] at this
  exact congrArg Prod.fst this

theorem momentum_eq_block (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) :
    momentum D x t i = (poincare (D.m i) (D.G*D.m0) (blk x i (t i))).2 := by
  have := poincareProd_block D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1) i
  rw [planetBlock_assemble] at this
  exact congrArg Prod.snd this

theorem position_update_ne (D : Data n) (x : Slow n) (t : Vec n) {i j : Fin n} (hij : i ≠ j)
    (s : ℝ) : position D x (Function.update t j s) i = position D x t i := by
  rw [position_eq_block, position_eq_block, Function.update_of_ne hij]

theorem position_update_self (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) (s : ℝ) :
    position D x (Function.update t i s) i = (poincare (D.m i) (D.G*D.m0) (blk x i s)).1 := by
  rw [position_eq_block, Function.update_self]

theorem momentum_update_self (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) (s : ℝ) :
    momentum D x (Function.update t i s) i = (poincare (D.m i) (D.G*D.m0) (blk x i s)).2 := by
  rw [momentum_eq_block, Function.update_self]

theorem continuous_momentum {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) :
    Continuous (fun t => momentum D x t i) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have h : Continuous fun s : ℝ => (poincare (D.m i) (D.G*D.m0) (blk x i s)).2 := by
    have hc : ContinuousOn (poincare (D.m i) (D.G*D.m0)) poincareDom :=
      (analyticOnNhd_poincare (D.hm i) hκ).continuousOn
    have hb : Continuous (blk x i) := by
      unfold blk
      refine Continuous.prodMk (continuous_pi fun k => ?_) continuous_const
      fin_cases k
      · exact continuous_id
      · exact continuous_const
    exact continuous_snd.comp (hc.comp_continuous hb (blk_mem hx i))
  have : (fun t : Vec n => momentum D x t i) =
      fun t => (poincare (D.m i) (D.G*D.m0) (blk x i (t i))).2 :=
    funext fun t => momentum_eq_block D x t i
  rw [this]
  exact h.comp (continuous_apply i)

/-! ### The Kepler field: position part -/

/-- The unit vector of the `c`-th momentum coordinate of body `i`. -/
def momSlot (i : Fin n) (c : Fin 2) : Fin (n * 2) → ℝ := Pi.single (finProdFinEquiv (i, c)) 1

/-- The momentum derivative of the Kepler part along one momentum coordinate. -/
theorem hasDerivAt_keplerPart_momentum (κ : ℝ) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    (z : Phase (n * 2)) (i : Fin n) (c : Fin 2) :
    HasDerivAt (fun r : ℝ => keplerPart κ m
      (z.1, z.2 + r • momSlot i c))
      (z.2 (finProdFinEquiv (i, c)) / m i) 0 := by
  unfold keplerPart
  have hterm : ∀ j ∈ Finset.univ, HasDerivAt (fun r : ℝ =>
      planeSq (bodyVector (z.2 + r • momSlot i c) j) / (2 * m j) -
        κ * m j / planeLength (bodyVector z.1 j))
      ((∑ c' : Fin 2, 2 * z.2 (finProdFinEquiv (j, c')) *
        (momSlot i c
          (finProdFinEquiv (j, c')))) / (2 * m j)) 0 := by
    intro j _
    have hc : ∀ c' : Fin 2, HasDerivAt (fun r : ℝ =>
        (z.2 + r • momSlot i c) (finProdFinEquiv (j, c')) ^ 2)
        (2 * z.2 (finProdFinEquiv (j, c')) *
          (momSlot i c
            (finProdFinEquiv (j, c')))) 0 := by
      intro c'
      have h1 : HasDerivAt (fun r : ℝ =>
          (z.2 + r • momSlot i c) (finProdFinEquiv (j, c')))
          (momSlot i c
            (finProdFinEquiv (j, c'))) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).mul_const
          (momSlot i c
            (finProdFinEquiv (j, c')))).const_add
          (z.2 (finProdFinEquiv (j, c')))
        simpa using this
      have := h1.fun_pow 2
      simpa using this
    have hs : HasDerivAt (fun r : ℝ =>
        planeSq (bodyVector (z.2 + r • momSlot i c) j))
        (∑ c' : Fin 2, 2 * z.2 (finProdFinEquiv (j, c')) *
          (momSlot i c
            (finProdFinEquiv (j, c')))) 0 := by
      have := HasDerivAt.fun_sum (u := Finset.univ) fun c' _ => hc c'
      simpa [planeSq, bodyVector] using this
    exact (hs.div_const (2 * m j)).sub_const _
  have hsum := (HasDerivAt.fun_sum hterm)
  refine hsum.congr_deriv ?_
  rw [Finset.sum_eq_single i]
  · have hmi := (hm i).ne'
    rw [Finset.sum_eq_single c]
    · simp [momSlot]
      field_simp
    · intro c' _ hc'
      have : finProdFinEquiv (i, c') ≠ finProdFinEquiv (i, c) := fun h => hc' (by
        have := finProdFinEquiv.injective h
        simpa using this)
      simp [momSlot, this]
    · simp
  · intro j _ hj
    have : ∀ c' : Fin 2, finProdFinEquiv (j, c') ≠ finProdFinEquiv (i, c) := fun c' h =>
      hj (by
        have := finProdFinEquiv.injective h
        simpa using (congrArg Prod.fst this))
    simp [momSlot, this]
  · simp

/-- The unit translation of the `k`-th angle. -/
def unitAngle (k : Fin n) : Phase (n + n) := (Fin.append (Pi.single k (1 : ℝ)) 0, 0)

theorem assemble_update_eq (x : Slow n) (t : Vec n) (k : Fin n) (r : ℝ) :
    (assemble x.2.1 (Function.update t k r) x.2.2 x.1 : Phase (n + n)) =
      assemble x.2.1 t x.2.2 x.1 + (r - t k) • unitAngle k := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · by_cases hjk : j = k
      · subst hjk; simp [assemble, unitAngle]
      · simp [assemble, unitAngle, hjk]
    · simp [assemble, unitAngle]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [assemble, unitAngle]

theorem field_eq_sum (D : Data n) (I : Vec n) :
    ((Fin.append (nu D I) 0 : Fin (n + n) → ℝ), (0 : Fin (n + n) → ℝ)) =
      ∑ k, nu D I k • unitAngle k := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [unitAngle, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [unitAngle, Prod.fst_sum, Finset.sum_apply]
  · simp [unitAngle, Prod.snd_sum, Finset.sum_apply]

theorem fderiv_keplerPart_momentum (κ : ℝ) {m : Fin n → ℝ} (hm : ∀ i, 0 < m i)
    {z : Phase (n * 2)} (hz : DifferentiableAt ℝ (keplerPart κ m) z) (i : Fin n) (c : Fin 2) :
    fderiv ℝ (keplerPart κ m) z (0, momSlot i c) = z.2 (finProdFinEquiv (i, c)) / m i := by
  have hl : HasDerivAt (fun r : ℝ => z + r • ((0 : Fin (n * 2) → ℝ), momSlot i c))
      ((0 : Fin (n * 2) → ℝ), momSlot i c) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      ((0 : Fin (n * 2) → ℝ), momSlot i c)).const_add z
  have hF : HasFDerivAt (keplerPart κ m) (fderiv ℝ (keplerPart κ m) z)
      (z + (0 : ℝ) • ((0 : Fin (n * 2) → ℝ), momSlot i c)) := by
    simpa using hz.hasFDerivAt
  have h1 := hF.comp_hasDerivAt (0 : ℝ) hl
  have h2 := hasDerivAt_keplerPart_momentum κ hm z i c
  exact h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => by
    simp only [Function.comp]
    congr 1
    exact Prod.ext (by simp) rfl))

theorem hasDerivAt_position {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (t : Vec n)
    (i : Fin n) :
    HasDerivAt (fun s => position D x (Function.update t i s) i)
      ((D.m i * nu D x.2.1 i)⁻¹ • momentum D x t i) (t i) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hwd : (assemble x.2.1 t x.2.2 x.1 : Phase (n + n)) ∈ poincareProdDom n :=
    assemble_mem hx t
  set w : Phase (n + n) := assemble x.2.1 t x.2.2 x.1 with hw
  have hΨ : DifferentiableAt ℝ (poincareProd D.m (D.G*D.m0)) w :=
    (analyticOnNhd_poincareProd D.hm hκ w hwd).differentiableAt
  set L := fderiv ℝ (poincareProd D.m (D.G*D.m0)) w with hL
  have hline : ∀ k, HasDerivAt (fun r => poincareProd D.m (D.G*D.m0)
      (assemble x.2.1 (Function.update t k r) x.2.2 x.1)) (L (unitAngle k)) (t k) := by
    intro k
    have hl : HasDerivAt (fun r : ℝ => w + (r - t k) • unitAngle k) (unitAngle k) (t k) := by
      simpa using (((hasDerivAt_id (t k)).sub_const (t k)).smul_const (unitAngle k)).const_add w
    have hF : HasFDerivAt (poincareProd D.m (D.G*D.m0)) L (w + (t k - t k) • unitAngle k) := by
      simpa using hΨ.hasFDerivAt
    refine (hF.comp_hasDerivAt (t k) hl).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun r => by simp [Function.comp, assemble_update_eq, hw]
  have hbody : ∀ k, HasDerivAt (fun r => position D x (Function.update t k r) i)
      (bodyVector (L (unitAngle k)).1 i) (t k) := by
    intro k
    have h1 : HasDerivAt (fun r => (poincareProd D.m (D.G*D.m0)
        (assemble x.2.1 (Function.update t k r) x.2.2 x.1)).1) (L (unitAngle k)).1 (t k) :=
      (hline k).fst
    rw [hasDerivAt_pi]
    intro c
    exact hasDerivAt_pi.1 h1 (finProdFinEquiv (i, c))
  have hself := hbody i
  have hother : ∀ k, k ≠ i → bodyVector (L (unitAngle k)).1 i = 0 := by
    intro k hk
    have h := hbody k
    have hc : (fun r => position D x (Function.update t k r) i) =
        fun _ => position D x t i := funext fun r => position_update_ne D x t hk.symm r
    rw [hc] at h
    exact h.unique (hasDerivAt_const _ _)
  have hf : fast w.2 = x.2.1 := by
    funext j
    simp [hw, fast, assemble]
  have hfield := pc_dec D hwd
  rw [(product_chart D).2.2 w hwd, hf, field_eq_sum, map_sum] at hfield
  have hreg := poincareProd_mem_regionProd D.hm hκ hwd
  have hK : DifferentiableAt ℝ (keplerPart (D.G*D.m0) D.m)
      (poincareProd D.m (D.G*D.m0) w) :=
    (analyticAt_keplerPart' _ _ fun j => by
      have := (hreg j).1
      simpa [bodyVector, poincareProd] using this).differentiableAt
  have hΛ : 0 < x.2.1 i := by
    have := (blk_mem hx i 0).1
    simpa [blk] using this
  have hν : 0 < nu D x.2.1 i := by
    have := D.hm i
    unfold nu
    positivity
  have hc : ∀ c, nu D x.2.1 i * bodyVector (L (unitAngle i)).1 i c =
      momentum D x t i c / D.m i := by
    intro c
    have h := congrArg (fun v => v.1 (finProdFinEquiv (i, c))) hfield
    simp only [hamiltonianVectorField, Prod.fst_sum, Finset.sum_apply, map_smul,
      Prod.smul_fst, Pi.smul_apply, smul_eq_mul] at h
    rw [Finset.sum_eq_single i] at h
    · have h2 := fderiv_keplerPart_momentum (D.G*D.m0) D.hm hK i c
      have h3 : (Pi.single (finProdFinEquiv (i, c)) (1 : ℝ) : Fin (n * 2) → ℝ) = momSlot i c :=
        rfl
      rw [h3, h2] at h
      exact h
    · intro k _ hk
      have := hother k hk
      have h4 : (L (unitAngle k)).1 (finProdFinEquiv (i, c)) = 0 := by
        have := congrFun this c
        simpa [bodyVector] using this
      exact mul_eq_zero_of_right _ h4
    · simp
  refine hself.congr_deriv ?_
  funext c
  have h := hc c
  simp only [Pi.smul_apply, smul_eq_mul]
  have hm := (D.hm i).ne'
  have hν' := hν.ne'
  field_simp
  field_simp at h
  linarith

/-! ### Averages over the angle cell -/

theorem avg_prod (f : Fin n → ℝ → ℝ) :
    avg (fun t : Vec n => ∏ k, f k (t k)) = ∏ k, ((2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, f k s) := by
  have h1 : ∫ t in cell n, ∏ k, f k (t k) = ∏ k, ∫ s in (0:ℝ)..2 * π, f k s := by
    unfold cell
    rw [volume_pi, Measure.restrict_pi_pi, integral_fin_nat_prod_eq_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_of_le (by positivity), integral_Icc_eq_integral_Ioc]
  have h2 : ((2 * π) ^ (-(n : ℤ)) : ℝ) = ∏ _k : Fin n, (2 * π)⁻¹ := by
    rw [zpow_neg, zpow_natCast, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  unfold avg
  rw [h1, h2, smul_eq_mul, ← Finset.prod_mul_distrib]

theorem mean_one : (2 * π)⁻¹ * ∫ _s in (0:ℝ)..2 * π, (1 : ℝ) = 1 := by
  simp
  field_simp

theorem avg_one (i : Fin n) (φ : ℝ → ℝ) :
    avg (fun t : Vec n => φ (t i)) = (2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, φ s := by
  have h := avg_prod (n := n) (fun k => if k = i then φ else fun _ => 1)
  have hp : (fun t : Vec n => ∏ k, (if k = i then φ else fun _ => (1:ℝ)) (t k)) =
      fun t => φ (t i) := by
    funext t
    rw [Finset.prod_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  rw [hp] at h
  rw [h, Finset.prod_eq_single i]
  · simp
  · intro k _ hk
    have : (if k = i then φ else fun _ => (1:ℝ)) = fun _ => 1 := by simp [hk]
    rw [this]
    exact mean_one
  · simp

theorem avg_two {j k : Fin n} (hjk : j ≠ k) (φ ψ : ℝ → ℝ) :
    avg (fun t : Vec n => φ (t j) * ψ (t k)) =
      ((2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, φ s) * ((2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, ψ s) := by
  have h := avg_prod (n := n) (fun l => if l = j then φ else if l = k then ψ else fun _ => 1)
  have hp : (fun t : Vec n => ∏ l, (if l = j then φ else if l = k then ψ else
      fun _ => (1:ℝ)) (t l)) = fun t => φ (t j) * ψ (t k) := by
    funext t
    rw [Finset.prod_eq_mul j k hjk]
    · simp [hjk.symm]
    · intro l _ hl
      simp [hl.1, hl.2]
    · simp
    · simp
  rw [hp] at h
  rw [h, Finset.prod_eq_mul j k hjk]
  · simp [hjk.symm]
  · intro l _ hl
    have : (if l = j then φ else if l = k then ψ else fun _ => (1:ℝ)) = fun _ => 1 := by
      simp [hl.1, hl.2]
    rw [this]
    exact mean_one
  · simp
  · simp

theorem avg_sum {ι : Type*} (s : Finset ι) {f : ι → Vec n → ℝ} (hf : ∀ c, Continuous (f c)) :
    avg (fun t => ∑ c ∈ s, f c t) = ∑ c ∈ s, avg (f c) := by
  unfold avg
  rw [integral_finsetSum _ fun c _ => (hf c).continuousOn.integrableOn_compact isCompact_cell,
    Finset.smul_sum]

theorem avg_const_mul (r : ℝ) (f : Vec n → ℝ) : avg (fun t => r * f t) = r * avg f := by
  unfold avg
  rw [integral_const_mul, smul_eq_mul, smul_eq_mul, mul_left_comm]

theorem avg_apply {f : Vec n → Fin 2 → ℝ} (hf : Continuous f) (c : Fin 2) :
    avg f c = avg (fun t => f t c) := by
  unfold avg
  have hi : Integrable f (volume.restrict (cell n)) :=
    hf.continuousOn.integrableOn_compact isCompact_cell
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) c).integral_comp_comm hi
  simp only [ContinuousLinearMap.proj_apply] at this
  simp [Pi.smul_apply, this]

theorem intervalIntegral_apply {g : ℝ → Fin 2 → ℝ} (hg : Continuous g) (c : Fin 2) :
    (∫ s in (0:ℝ)..2 * π, g s) c = ∫ s in (0:ℝ)..2 * π, g s c := by
  have hi : IntegrableOn g (Ioc 0 (2 * π)) := (hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) c).integral_comp_comm hi
  simp only [ContinuousLinearMap.proj_apply] at this
  rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le
    (by positivity), ← this]

/-! ### One-planet functions of the angle -/

/-- The momentum of planet `i` as a function of its own angle. -/
def pmom (D : Data n) (x : Slow n) (i : Fin n) (s : ℝ) : Fin 2 → ℝ :=
  (poincare (D.m i) (D.G*D.m0) (blk x i s)).2

/-- The position of planet `i` as a function of its own angle. -/
def ppos (D : Data n) (x : Slow n) (i : Fin n) (s : ℝ) : Fin 2 → ℝ :=
  (poincare (D.m i) (D.G*D.m0) (blk x i s)).1

theorem momentum_eq_pmom (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) :
    momentum D x t i = pmom D x i (t i) := momentum_eq_block D x t i

theorem continuous_pmom {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) :
    Continuous (pmom D x i) :=
  ((continuous_momentum hx i).comp (continuous_pi fun _ => continuous_id)).congr fun _ =>
    momentum_eq_pmom D x _ i

theorem hasDerivAt_ppos {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) (s : ℝ) :
    HasDerivAt (ppos D x i) ((D.m i * nu D x.2.1 i)⁻¹ • pmom D x i s) s := by
  have h := hasDerivAt_position hx (fun _ => s) i
  have hf : (fun r => position D x (Function.update (fun _ => s) i r) i) = ppos D x i :=
    funext fun r => position_update_self D x _ i r
  rw [hf] at h
  simpa [momentum_eq_pmom] using h

theorem ppos_periodic {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) :
    Function.Periodic (ppos D x i) (2 * π) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  intro s
  have := poincare_periodic (D.hm i) hκ (blk_mem hx i s) 1
  simpa [ppos, blk] using congrArg Prod.fst this

theorem integral_pmom {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) :
    ∫ s in (0:ℝ)..2 * π, pmom D x i s = 0 := by
  have hm : 0 < D.m i := D.hm i
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hΛ : 0 < x.2.1 i := by
    have := (blk_mem hx i 0).1
    simpa [blk] using this
  have hν : 0 < nu D x.2.1 i := by
    unfold nu
    positivity
  have hd : ∀ s, deriv (ppos D x i) s = (D.m i * nu D x.2.1 i)⁻¹ • pmom D x i s :=
    fun s => (hasDerivAt_ppos hx i s).deriv
  have hq : ContDiff ℝ 1 (ppos D x i) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun s => (hasDerivAt_ppos hx i s).differentiableAt, ?_⟩
    have : deriv (ppos D x i) = fun s => (D.m i * nu D x.2.1 i)⁻¹ • pmom D x i s := funext hd
    rw [this]
    exact (continuous_pmom hx i).const_smul ((D.m i * nu D x.2.1 i)⁻¹)
  have h0 := periodic_derivative_integral hq (ppos_periodic hx i)
  simp only [hd] at h0
  rw [intervalIntegral.integral_smul] at h0
  rcases smul_eq_zero.1 h0 with h | h
  · exact absurd h (inv_ne_zero (mul_pos hm hν).ne')
  · exact h

theorem mean_planeSq_pmom {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) :
    (2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, planeSq (pmom D x i s) =
      D.m i ^ 2 * (D.G * D.m0) / axis D x.2.1 i := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  exact (poincare_means (D.hm i) hκ (blk_mem hx i 0)).2.1

theorem nu_pos {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) : 0 < nu D x.2.1 i := by
  have hm : 0 < D.m i := D.hm i
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have hΛ : 0 < x.2.1 i := by
    have := (blk_mem hx i 0).1
    simpa [blk] using this
  unfold nu
  positivity

theorem continuous_planeDot_comp {f g : Vec n → Fin 2 → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun t => planeDot (f t) (g t) := by
  unfold planeDot
  exact continuous_finsetSum _ fun k _ =>
    ((continuous_apply k).comp hf).mul ((continuous_apply k).comp hg)

theorem avg_momentum {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) :
    avg (fun t => momentum D x t i) = 0 := by
  funext c
  rw [avg_apply (continuous_momentum hx i) c]
  have : (fun t : Vec n => momentum D x t i c) = fun t => pmom D x i (t i) c :=
    funext fun t => by rw [momentum_eq_pmom]
  rw [this, avg_one i (fun s => pmom D x i s c),
    ← intervalIntegral_apply (continuous_pmom hx i) c, integral_pmom hx i]
  simp

theorem avg_cross {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) {i j : Fin n} (hij : i ≠ j) :
    avg (fun t => planeDot (momentum D x t i) (momentum D x t j)) = 0 := by
  unfold planeDot
  have hcont : ∀ c : Fin 2, Continuous fun t : Vec n => momentum D x t i c * momentum D x t j c :=
    fun c => ((continuous_apply c).comp (continuous_momentum hx i)).mul
      ((continuous_apply c).comp (continuous_momentum hx j))
  rw [avg_sum Finset.univ (f := fun c t => momentum D x t i c * momentum D x t j c) hcont]
  refine Finset.sum_eq_zero fun c _ => ?_
  have : (fun t : Vec n => momentum D x t i c * momentum D x t j c) =
      fun t => pmom D x i (t i) c * pmom D x j (t j) c :=
    funext fun t => by rw [momentum_eq_pmom, momentum_eq_pmom]
  rw [this, avg_two hij (fun s => pmom D x i s c) (fun s => pmom D x j s c),
    ← intervalIntegral_apply (continuous_pmom hx i) c, integral_pmom hx i]
  simp

theorem avg_diag {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) :
    avg (fun t => planeSq (momentum D x t i)) =
      D.m i ^ 2 * (D.G * D.m0) / axis D x.2.1 i := by
  have : (fun t : Vec n => planeSq (momentum D x t i)) =
      fun t => planeSq (pmom D x i (t i)) := funext fun t => by rw [momentum_eq_pmom]
  rw [this, avg_one i (fun s => planeSq (pmom D x i s)), mean_planeSq_pmom hx]

theorem planeSq_sum_eq (v : Fin n → Fin 2 → ℝ) :
    planeSq (∑ i, v i) = ∑ i, ∑ j, planeDot (v i) (v j) := by
  simp only [planeSq, planeDot, Finset.sum_apply, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- Joint Lemma 64; no pair-collision guard is required. -/
theorem lemma64 (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) :
    (∀ t i, (D.m i * nu D x.2.1 i) •
      deriv (fun s => position D x (Function.update t i s) i) (t i) = momentum D x t i) ∧
    (∀ i, avg (fun t => momentum D x t i) = 0) ∧
    (∀ i j, i ≠ j → avg (fun t => planeDot (momentum D x t i) (momentum D x t j)) = 0) ∧
    (∀ i, avg (fun t => planeSq (momentum D x t i)) =
      D.m i ^ 4 * (D.G*D.m0)^2 / x.2.1 i ^ 2) ∧
    avg (fun t => planeSq (∑ i, momentum D x t i)) =
      ∑ i, D.m i ^ 4 * (D.G*D.m0)^2 / x.2.1 i ^ 2 := by
  have hd : ∀ i, avg (fun t => planeSq (momentum D x t i)) =
      D.m i ^ 4 * (D.G*D.m0)^2 / x.2.1 i ^ 2 := by
    intro i
    rw [avg_diag hx]
    have := (D.hm i).ne'
    have hκ := (mul_pos D.hG D.hm0).ne'
    have hΛ : x.2.1 i ≠ 0 := by
      have := (blk_mem hx i 0).1
      simpa [blk] using this.ne'
    unfold axis
    field_simp
  refine ⟨?_, avg_momentum hx, fun i j h => avg_cross hx h, hd, ?_⟩
  · intro t i
    rw [(hasDerivAt_position hx t i).deriv, smul_inv_smul₀]
    exact (mul_pos (D.hm i) (nu_pos hx i)).ne'
  · have hc : ∀ i j, Continuous fun t : Vec n =>
        planeDot (momentum D x t i) (momentum D x t j) := fun i j =>
      continuous_planeDot_comp (continuous_momentum hx i) (continuous_momentum hx j)
    have : (fun t : Vec n => planeSq (∑ i, momentum D x t i)) =
        fun t => ∑ i, ∑ j, planeDot (momentum D x t i) (momentum D x t j) :=
      funext fun t => planeSq_sum_eq _
    rw [this, avg_sum _ fun i => continuous_finsetSum _ fun j _ => hc i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [avg_sum _ fun j => hc i j, Finset.sum_eq_single i]
    · rw [← hd i]
      congr 1
      funext t
      exact (planeSq_eq_planeDot _).symm
    · intro j _ hj
      exact avg_cross hx hj.symm
    · simp

theorem lemma64_coordinates (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) :
    (∀ t i j, i ≠ j → deriv (fun s => position D x (Function.update t j s) i) (t j) = 0) ∧
    (∀ t i, (2*π)⁻¹ • (∫ s in (0:ℝ)..2*π, momentum D x (Function.update t i s) i) = 0) ∧
    (∀ t i, (2*π)⁻¹ * (∫ s in (0:ℝ)..2*π, planeSq (momentum D x (Function.update t i s) i)) =
      D.m i^2*(D.G*D.m0)/axis D x.2.1 i) := by
  refine ⟨fun t i j hij => ?_, fun t i => ?_, fun t i => ?_⟩
  · have : (fun s => position D x (Function.update t j s) i) = fun _ => position D x t i :=
      funext fun s => position_update_ne D x t hij s
    rw [this, deriv_const]
  · have : (fun s => momentum D x (Function.update t i s) i) = pmom D x i :=
      funext fun s => momentum_update_self D x t i s
    rw [this, integral_pmom hx i, smul_zero]
  · have : (fun s => planeSq (momentum D x (Function.update t i s) i)) =
        fun s => planeSq (pmom D x i s) :=
      funext fun s => by rw [momentum_update_self]; rfl
    rw [this, mean_planeSq_pmom hx i]

/-! ### The identification of the two models -/

def modelDelta (D : Data n) (I : Vec n) : ℝ :=
  (2*D.m0)⁻¹ * ∑ i, D.m i^4 * (D.G*D.m0)^2 / I i^2

theorem perturbation_diff (D : Data n) (x : Slow n) (t : Vec n) :
    perturbation D true (assemble x.2.1 t x.2.2 x.1) -
      perturbation D false (assemble x.2.1 t x.2.2 x.1) =
      (2 * D.m0)⁻¹ * planeSq (∑ i, momentum D x t i) := by
  simp only [perturbation, ite_true, Bool.false_eq_true, ite_false, fMov, fFix, momentum]
  rw [div_eq_inv_mul]
  ring

theorem continuous_planeSq_comp {g : Vec n → Fin 2 → ℝ} (hg : Continuous g) :
    Continuous fun t => planeSq (g t) := by
  unfold planeSq
  exact continuous_finsetSum _ fun k _ => ((continuous_apply k).comp hg).pow 2

theorem avg_add {f g : Vec n → ℝ} (hf : IntegrableOn f (cell n)) (hg : Continuous g) :
    avg (fun t => f t + g t) = avg f + avg g := by
  unfold avg
  rw [integral_add hf (hg.continuousOn.integrableOn_compact isCompact_cell), smul_add]

/-- Never subtract total Bochner averages without an integrability guard. -/
theorem identification (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) :
    Continuous (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1) -
      perturbation D false (assemble x.2.1 t x.2.2 x.1)) ∧
    avg (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1) -
      perturbation D false (assemble x.2.1 t x.2.2 x.1)) = modelDelta D x.2.1 ∧
    (IntegrableOn (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1)) (cell n) ↔
      IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n)) ∧
    (IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n) →
      secular D true x = secular D false x + modelDelta D x.2.1) := by
  have hfun : (fun t : Vec n => perturbation D true (assemble x.2.1 t x.2.2 x.1) -
      perturbation D false (assemble x.2.1 t x.2.2 x.1)) =
      fun t => (2 * D.m0)⁻¹ * planeSq (∑ i, momentum D x t i) :=
    funext fun t => perturbation_diff D x t
  have hcont : Continuous fun t : Vec n => (2 * D.m0)⁻¹ * planeSq (∑ i, momentum D x t i) :=
    continuous_const.mul (continuous_planeSq_comp
      (continuous_finsetSum _ fun i _ => continuous_momentum hx i))
  have hint : IntegrableOn (fun t : Vec n =>
      (2 * D.m0)⁻¹ * planeSq (∑ i, momentum D x t i)) (cell n) :=
    hcont.continuousOn.integrableOn_compact isCompact_cell
  refine ⟨hfun ▸ hcont, ?_, ?_, ?_⟩
  · rw [hfun, avg_const_mul, (lemma64 D hx).2.2.2.2]
    rfl
  · constructor
    · intro h
      rw [← hfun] at hint
      refine (h.sub hint).congr (Eventually.of_forall fun t => ?_)
      simp
    · intro h
      rw [← hfun] at hint
      refine (h.add hint).congr (Eventually.of_forall fun t => ?_)
      simp
  · intro hB
    have hdiff := (lemma64 D hx).2.2.2.2
    have hA : (fun t : Vec n => perturbation D true (assemble x.2.1 t x.2.2 x.1)) =
        fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1) +
          (2 * D.m0)⁻¹ * planeSq (∑ i, momentum D x t i) :=
      funext fun t => by rw [← perturbation_diff]; ring
    have hs : ∀ b, secular D b x =
        avg (fun t : Vec n => perturbation D b (assemble x.2.1 t x.2.2 x.1)) := fun b => by
      simp only [secular, secularAverage, avg, smul_eq_mul]
      rfl
    rw [hs, hs, hA, avg_add hB hcont, avg_const_mul, hdiff]
    rfl

end SecularForm
end KAM.Planetary

end
