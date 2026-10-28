/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Basic
public import KAM.Planetary.Poincare.Bijective
public import KAM.Planetary.Newtonian.Models
public import KAM.Frozen.Planetary.Defs.ProgradeElliptic
public import KAM.Frozen.Planetary.Defs.FastShift

/-!
# The Poincaré product chart

Blueprint P, Part 7 (`bpP:p7:product-def`, `bpP:p7:product-chart`): the body-wise Poincaré charts
`Ψ^{(n)} : Phase (n + n) → Phase (n * 2)`, with the fast block first.  The chart is the one-planet
chart on each block `planetBlock w i`, so analyticity, symplecticity, the lattice, the image and the
local-diffeomorphism property are inherited blockwise; the Kepler part of the two Newtonian models
decouples (`h(Λ) = -Σ κ² m_i³ / (2 Λ_i²)`).  `poincareProdCast` composes with the canonical
reindexing `phaseCast` to give an equal-dimension chart on `Phase (n * 2)`.
-/

@[expose] public noncomputable section

open Set Metric Real
open scoped ContDiff

namespace KAM.Planetary

open KAM KAM.Kepler

section ProductChart

variable {n : ℕ}

/-- The `i`-th planet's coordinates `((λ_i, ξ_i), (Λ_i, η_i))` of a point of `Phase (n + n)` (fast
block first). -/
def planetBlock (w : Phase (n + n)) (i : Fin n) : Phase 2 :=
  (![fast w.1 i, slow w.1 i], ![fast w.2 i, slow w.2 i])

/-- `bpP:p7:product-def`: `Ψ^{(n)}(w)`, the body-wise Poincaré charts, `κ = G m₀`. -/
def poincareProd (m : Fin n → ℝ) (κ : ℝ) (w : Phase (n + n)) : Phase (n * 2) :=
  (fun k => (poincare (m (finProdFinEquiv.symm k).1) κ (planetBlock w (finProdFinEquiv.symm k).1)).1
      (finProdFinEquiv.symm k).2,
   fun k => (poincare (m (finProdFinEquiv.symm k).1) κ (planetBlock w (finProdFinEquiv.symm k).1)).2
      (finProdFinEquiv.symm k).2)

def poincareProdDom (n : ℕ) : Set (Phase (n + n)) := {w | ∀ i, planetBlock w i ∈ poincareDom}

/-- `h(Λ) = -Σ κ² m_i³/(2Λ_i²)`. -/
def hProd (κ : ℝ) (m : Fin n → ℝ) (w : Phase (n + n)) : ℝ :=
  -∑ i, κ ^ 2 * m i ^ 3 / (2 * fast w.2 i ^ 2)

/-- `𝒦^{(n)}`. -/
def regionProd (m : Fin n → ℝ) (κ : ℝ) : Set (Phase (n * 2)) :=
  {z | ∀ i, (bodyVector z.1 i, bodyVector z.2 i) ∈ regionMK (m i) κ}

/-! ### Block calculus -/

/-- `simp` normalises `Fin.natAdd n i` to `i.addNat n` when both blocks have length `n`. -/
@[simp] theorem append_addNat {α : Type*} (u v : Fin n → α) (i : Fin n) :
    Fin.append u v (i.addNat n) = v i := by
  have : i.addNat n = Fin.natAdd n i := Fin.ext (Nat.add_comm _ _)
  rw [this]; exact Fin.append_right u v i

/-- Reassemble a family of planar phase points as a point of `Phase (n * 2)`. -/
def ofPlanets (P : Fin n → Phase 2) : Phase (n * 2) :=
  (ofBodies fun i => (P i).1, ofBodies fun i => (P i).2)

/-- Reassemble a family of planar phase points as a point of `Phase (n + n)` (fast block first). -/
def unblock (P : Fin n → Phase 2) : Phase (n + n) :=
  (Fin.append (fun i => (P i).1 0) (fun i => (P i).1 1),
   Fin.append (fun i => (P i).2 0) (fun i => (P i).2 1))

theorem poincareProd_eq_ofPlanets (m : Fin n → ℝ) (κ : ℝ) (w : Phase (n + n)) :
    poincareProd m κ w = ofPlanets fun i => poincare (m i) κ (planetBlock w i) := rfl

theorem bodyVector_ofPlanets_fst (P : Fin n → Phase 2) (i : Fin n) :
    bodyVector (ofPlanets P).1 i = (P i).1 := by
  show bodyVector (ofBodies fun i => (P i).1) i = _
  exact bodyVector_ofBodies _ i

theorem bodyVector_ofPlanets_snd (P : Fin n → Phase 2) (i : Fin n) :
    bodyVector (ofPlanets P).2 i = (P i).2 := by
  show bodyVector (ofBodies fun i => (P i).2) i = _
  exact bodyVector_ofBodies _ i

theorem ofPlanets_injective : Function.Injective (ofPlanets (n := n)) := by
  intro P Q h
  funext i
  refine Prod.ext ?_ ?_
  · rw [← bodyVector_ofPlanets_fst P i, ← bodyVector_ofPlanets_fst Q i, h]
  · rw [← bodyVector_ofPlanets_snd P i, ← bodyVector_ofPlanets_snd Q i, h]

theorem ofPlanets_bodyVector (z : Phase (n * 2)) :
    ofPlanets (fun i => (bodyVector z.1 i, bodyVector z.2 i)) = z := by
  unfold ofPlanets
  rw [ofBodies_bodyVector, ofBodies_bodyVector]

theorem planetBlock_unblock (P : Fin n → Phase 2) (i : Fin n) :
    planetBlock (unblock P) i = P i := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
    simp [planetBlock, unblock, fast, slow]

/-- `ofPlanets` as a continuous linear map. -/
def ofPlanetsCLM : (Fin n → Phase 2) →L[ℝ] Phase (n * 2) :=
  (ContinuousLinearMap.pi fun k : Fin (n * 2) =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (finProdFinEquiv.symm k).2).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Phase 2)
          (finProdFinEquiv.symm k).1)).prod
    (ContinuousLinearMap.pi fun k : Fin (n * 2) =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (finProdFinEquiv.symm k).2).comp
        (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Phase 2)
          (finProdFinEquiv.symm k).1))

theorem ofPlanetsCLM_apply (P : Fin n → Phase 2) : ofPlanetsCLM P = ofPlanets P := rfl

/-- The `i`-th block as a continuous linear map. -/
def blockCLM (i : Fin n) : Phase (n + n) →L[ℝ] Phase 2 :=
  (ContinuousLinearMap.pi fun k : Fin 2 =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + n) => ℝ)
        (![Fin.castAdd n i, Fin.natAdd n i] k)).comp
        (ContinuousLinearMap.fst ℝ (Fin (n + n) → ℝ) (Fin (n + n) → ℝ))).prod
    (ContinuousLinearMap.pi fun k : Fin 2 =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + n) => ℝ)
        (![Fin.castAdd n i, Fin.natAdd n i] k)).comp
        (ContinuousLinearMap.snd ℝ (Fin (n + n) → ℝ) (Fin (n + n) → ℝ)))

theorem blockCLM_apply (i : Fin n) (w : Phase (n + n)) : blockCLM i w = planetBlock w i := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
    simp [blockCLM, planetBlock, fast, slow]

theorem isOpen_poincareProdDom (n : ℕ) : IsOpen (poincareProdDom n) := by
  have : poincareProdDom n = ⋂ i, blockCLM i ⁻¹' poincareDom := by
    ext w; simp [poincareProdDom, blockCLM_apply]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_poincareDom.preimage (blockCLM i).continuous

theorem symplecticForm_ofPlanets (P Q : Fin n → Phase 2) :
    symplecticForm (ofPlanets P) (ofPlanets Q) = ∑ i, symplecticForm (P i) (Q i) := by
  unfold symplecticForm
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp [ofPlanets, ofBodies]

theorem symplecticForm_blocks (u v : Phase (n + n)) :
    symplecticForm u v = ∑ i, symplecticForm (planetBlock u i) (planetBlock v i) := by
  unfold symplecticForm
  rw [Fin.sum_univ_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [planetBlock, fast, slow, Fin.sum_univ_two]
  simp

/-- Nondegeneracy of the symplectic form. -/
theorem eq_zero_of_symplecticForm {d : ℕ} {u : Phase d} (h : ∀ v, symplecticForm u v = 0) :
    u = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have := h (0, Pi.single i 1)
    simpa [symplecticForm, Pi.single_apply] using this
  · have := h (Pi.single i 1, 0)
    simpa [symplecticForm, Pi.single_apply] using this

theorem analyticOnNhd_poincareProd {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ) :
    AnalyticOnNhd ℝ (poincareProd m κ) (poincareProdDom n) := by
  intro w hw
  have h : AnalyticAt ℝ (fun w : Phase (n + n) => fun i => poincare (m i) κ (blockCLM i w)) w :=
    analyticAt_pi_iff.2 fun i =>
      (analyticOnNhd_poincare (hm i) hκ _ (by simpa [blockCLM_apply] using hw i)).comp
        ((blockCLM i).analyticAt w)
  have := (ofPlanetsCLM.analyticAt _).comp h
  convert this using 1
  funext w
  simp [ofPlanetsCLM_apply, poincareProd_eq_ofPlanets, blockCLM_apply]

theorem hasFDerivAt_poincareProd {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) :
    HasFDerivAt (poincareProd m κ)
      (ofPlanetsCLM.comp (ContinuousLinearMap.pi fun i =>
        (fderiv ℝ (poincare (m i) κ) (planetBlock w i)).comp (blockCLM i))) w := by
  have hd : ∀ i, HasFDerivAt (poincare (m i) κ) (fderiv ℝ (poincare (m i) κ) (planetBlock w i))
      (blockCLM i w) := fun i => by
    rw [blockCLM_apply]
    exact (analyticOnNhd_poincare (hm i) hκ _ (hw i)).differentiableAt.hasFDerivAt
  have h1 : HasFDerivAt (fun w : Phase (n + n) => fun i => poincare (m i) κ (blockCLM i w))
      (ContinuousLinearMap.pi fun i =>
        (fderiv ℝ (poincare (m i) κ) (planetBlock w i)).comp (blockCLM i)) w :=
    hasFDerivAt_pi'.2 fun i => by
      rw [ContinuousLinearMap.proj_pi]
      exact (hd i).comp w (blockCLM i).hasFDerivAt
  have h2 := ofPlanetsCLM.hasFDerivAt.comp w h1
  convert h2 using 1
  funext w
  simp [ofPlanetsCLM_apply, poincareProd_eq_ofPlanets, blockCLM_apply]

theorem fderiv_poincareProd_apply {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) (u : Phase (n + n)) :
    fderiv ℝ (poincareProd m κ) w u =
      ofPlanets fun i => fderiv ℝ (poincare (m i) κ) (planetBlock w i) (planetBlock u i) := by
  rw [(hasFDerivAt_poincareProd hm hκ hw).fderiv]
  simp [ofPlanetsCLM_apply, blockCLM_apply]

/-- `bpP:p7:product-chart` (a). -/
theorem poincareProd_symplectic {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ) :
    IsSymplecticOn 1 (poincareProd m κ) (poincareProdDom n) := by
  intro w hw u v
  rw [fderiv_poincareProd_apply hm hκ hw, fderiv_poincareProd_apply hm hκ hw,
    symplecticForm_ofPlanets, one_mul, symplecticForm_blocks]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := poincare_symplectic (hm i) hκ _ (hw i) (planetBlock u i) (planetBlock v i)
  rw [this, one_mul]

theorem poincareProd_block (m : Fin n → ℝ) (κ : ℝ) (w : Phase (n + n)) (i : Fin n) :
    (bodyVector (poincareProd m κ w).1 i, bodyVector (poincareProd m κ w).2 i) =
      poincare (m i) κ (planetBlock w i) := by
  rw [poincareProd_eq_ofPlanets, bodyVector_ofPlanets_fst, bodyVector_ofPlanets_snd]

theorem planetBlock_shift (w : Phase (n + n)) (k : Fin n → ℤ) (i : Fin n) :
    planetBlock (w + fastShift (a := n) (b := n) k) i =
      (![(planetBlock w i).1 0 + 2 * π * (k i : ℝ), (planetBlock w i).1 1],
        (planetBlock w i).2) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> fin_cases j <;>
    simp [planetBlock, fast, slow, fastShift, Fin.append_left]

theorem poincareProd_lattice {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) (k : Fin n → ℤ) :
    w + fastShift (a := n) (b := n) k ∈ poincareProdDom n ∧
      poincareProd m κ (w + fastShift (a := n) (b := n) k) = poincareProd m κ w := by
  have hdom : ∀ i, planetBlock (w + fastShift (a := n) (b := n) k) i ∈ poincareDom := by
    intro i
    obtain ⟨h1, h2⟩ := hw i
    rw [planetBlock_shift]
    refine ⟨?_, ?_⟩
    · simpa using h1
    · simpa [poincareGamma] using h2
  refine ⟨hdom, ?_⟩
  rw [poincareProd_eq_ofPlanets, poincareProd_eq_ofPlanets]
  congr 1
  funext i
  rw [planetBlock_shift]
  exact poincare_periodic (hm i) hκ (hw i) (k i)

theorem poincareProd_eq_iff {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {w w' : Phase (n + n)} (hw : w ∈ poincareProdDom n) (hw' : w' ∈ poincareProdDom n) :
    poincareProd m κ w = poincareProd m κ w' ↔
      ∃ k : Fin n → ℤ, w' = w + fastShift (a := n) (b := n) k := by
  constructor
  · intro h
    have hb : ∀ i, ∃ k : ℤ, (planetBlock w' i).1 = ![(planetBlock w i).1 0 + 2 * π * k,
        (planetBlock w i).1 1] ∧ (planetBlock w' i).2 = (planetBlock w i).2 := by
      intro i
      have := congrArg (fun z => (bodyVector z.1 i, bodyVector z.2 i)) h
      simp only [poincareProd_block] at this
      exact (poincare_eq_iff (hm i) hκ (hw i) (hw' i)).1 this
    choose k hk using hb
    refine ⟨k, Prod.ext (funext fun j => ?_) (funext fun j => ?_)⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have := congrFun (hk i).1 0
        simpa [planetBlock, fast, fastShift, Fin.append_left] using this
      · have := congrFun (hk i).1 1
        simpa [planetBlock, slow, fastShift, Fin.append_right] using this
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have := congrFun (hk i).2 0
        simpa [planetBlock, fast, fastShift] using this
      · have := congrFun (hk i).2 1
        simpa [planetBlock, slow, fastShift] using this
  · rintro ⟨k, rfl⟩
    exact (poincareProd_lattice hm hκ hw k).2.symm

theorem poincareProd_mem_regionProd {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) : poincareProd m κ w ∈ regionProd m κ := by
  intro i
  rw [poincareProd_block]
  exact (poincare_elements (hm i) hκ (hw i)).1

theorem poincareProd_image {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ) :
    poincareProd m κ '' poincareProdDom n = regionProd m κ := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact poincareProd_mem_regionProd hm hκ hw
  · intro z hz
    have hs : ∀ i, ∃ p ∈ poincareDom, poincare (m i) κ p = (bodyVector z.1 i, bodyVector z.2 i) :=
      fun i => by
        have := (poincare_image (hm i) hκ).symm.subset (hz i)
        obtain ⟨p, hp, hpz⟩ := this
        exact ⟨p, hp, hpz⟩
    choose p hp hpz using hs
    refine ⟨unblock p, fun i => by rw [planetBlock_unblock]; exact hp i, ?_⟩
    rw [poincareProd_eq_ofPlanets]
    have : (fun i => poincare (m i) κ (planetBlock (unblock p) i)) =
        fun i => (bodyVector z.1 i, bodyVector z.2 i) := by
      funext i
      rw [planetBlock_unblock]; exact hpz i
    rw [this, ofPlanets_bodyVector]

theorem isOpen_poincareProd_preimage {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ) :
    IsOpen (poincareProdDom n ∩ poincareProd m κ ⁻¹' collisionFreeDomain n) :=
  (analyticOnNhd_poincareProd hm hκ).continuousOn.isOpen_inter_preimage (isOpen_poincareProdDom n)
    (isOpen_collisionFreeDomain n)

theorem analyticOnNhd_fMov_poincareProd {m : Fin n → ℝ} {G m0 : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : 0 < G * m0) :
    AnalyticOnNhd ℝ (fun w => fMov G m0 m (poincareProd m (G * m0) w))
      (poincareProdDom n ∩ poincareProd m (G * m0) ⁻¹' collisionFreeDomain n) :=
  (analyticOnNhd_fMov G m0 m).comp ((analyticOnNhd_poincareProd hm hκ).mono inter_subset_left)
    fun _ hw => hw.2

theorem analyticOnNhd_fFix_poincareProd {m : Fin n → ℝ} {G m0 : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : 0 < G * m0) :
    AnalyticOnNhd ℝ (fun w => fFix G m (poincareProd m (G * m0) w))
      (poincareProdDom n ∩ poincareProd m (G * m0) ⁻¹' collisionFreeDomain n) :=
  (analyticOnNhd_fFix G m).comp ((analyticOnNhd_poincareProd hm hκ).mono inter_subset_left)
    fun _ hw => hw.2

/-- (b): decoupling; `ν_i = κ² m_i³/Λ_i³`, `∂²h/∂Λ_i² = -3κ²m_i³/Λ_i⁴ ≠ 0`. -/
theorem keplerPart_poincareProd {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) :
    keplerPart κ m (poincareProd m κ w) = hProd κ m w := by
  rw [keplerPart_eq_sum]
  unfold hProd
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [poincareProd_block, (poincare_elements (hm i) hκ (hw i)).2.1]
  simp only [planetBlock]
  rw [neg_div]
  simp

theorem hasDerivAt_nu {m κ x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => κ ^ 2 * m ^ 3 / y ^ 3) (-3 * κ ^ 2 * m ^ 3 / x ^ 4) x := by
  have h : HasDerivAt (fun y => κ ^ 2 * m ^ 3 / y ^ 3)
      ((0 * x ^ 3 - κ ^ 2 * m ^ 3 * ((3 : ℕ) * x ^ (3 - 1))) / (x ^ 3) ^ 2) x :=
    (hasDerivAt_const x (κ ^ 2 * m ^ 3)).div (hasDerivAt_pow 3 x) (pow_ne_zero 3 hx)
  refine h.congr_deriv ?_
  field_simp
  norm_num
  ring

/-- (c): the two models share the chart. -/
theorem movingHamiltonian_poincareProd {m : Fin n → ℝ} {G m0 μ : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : 0 < G * m0) {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) :
    movingHamiltonian G m0 m μ (poincareProd m (G * m0) w) =
      hProd (G * m0) m w + μ * fMov G m0 m (poincareProd m (G * m0) w) := by
  rw [movingHamiltonian_split, keplerPart_poincareProd hm hκ hw]

theorem fixedHamiltonian_poincareProd {m : Fin n → ℝ} {G m0 ε : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : 0 < G * m0) {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) :
    fixedHamiltonian G m0 m ε (poincareProd m (G * m0) w) =
      hProd (G * m0) m w + ε * fFix G m (poincareProd m (G * m0) w) := by
  rw [fixedHamiltonian_split, keplerPart_poincareProd hm hκ hw]

theorem regionProd_one_iff {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (z : Phase (n * 2)) :
    z ∈ regionProd m 1 ↔ ProgradeElliptic m z := by
  constructor
  · intro h i
    obtain ⟨h1, h2, h3⟩ := h i
    refine ⟨hm i, h1, ?_, h3⟩
    simpa [energyMK, keplerEnergy] using h2
  · intro h i
    obtain ⟨-, h1, h2, h3⟩ := h i
    refine ⟨h1, ?_, h3⟩
    simpa [energyMK, keplerEnergy] using h2

/-! ### Local diffeomorphism -/

theorem poincareProd_fderiv_equiv {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) :
    ∃ A : Phase (n + n) ≃L[ℝ] Phase (n * 2),
      (A : Phase (n + n) →L[ℝ] Phase (n * 2)) = fderiv ℝ (poincareProd m κ) w := by
  have hs := poincareProd_symplectic hm hκ w hw
  set A := fderiv ℝ (poincareProd m κ) w with hA
  have hker : LinearMap.ker (A : Phase (n + n) →ₗ[ℝ] Phase (n * 2)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    refine eq_zero_of_symplecticForm fun v => ?_
    have := hs u v
    rw [one_mul] at this
    rw [← this]
    have hu' : A u = 0 := hu
    rw [hu']
    simp [symplecticForm]
  have hinj : Function.Injective (A : Phase (n + n) →ₗ[ℝ] Phase (n * 2)) :=
    LinearMap.ker_eq_bot.1 hker
  have hdim : Module.finrank ℝ (Phase (n + n)) = Module.finrank ℝ (Phase (n * 2)) := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun]
    omega
  have hsurj : Function.Surjective (A : Phase (n + n) →ₗ[ℝ] Phase (n * 2)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  refine ⟨ContinuousLinearEquiv.ofBijective A hker ?_, ?_⟩
  · exact LinearMap.range_eq_top.2 hsurj
  · exact ContinuousLinearMap.ext fun z => rfl

theorem poincareProd_localDiffeo {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {w : Phase (n + n)} (hw : w ∈ poincareProdDom n) :
    ∃ φ : OpenPartialHomeomorph (Phase (n + n)) (Phase (n * 2)), w ∈ φ.source ∧
      (φ : Phase (n + n) → Phase (n * 2)) = poincareProd m κ ∧
        AnalyticOnNhd ℝ φ.symm φ.target := by
  have hana := analyticOnNhd_poincareProd hm hκ
  obtain ⟨A, hA⟩ := poincareProd_fderiv_equiv hm hκ hw
  have hc : ContDiffAt ℝ ω (poincareProd m κ) w := (hana w hw).contDiffAt
  have hf' : HasFDerivAt (poincareProd m κ) (A : Phase (n + n) →L[ℝ] Phase (n * 2)) w := by
    rw [hA]; exact (hana w hw).differentiableAt.hasFDerivAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let φ0 := hc.toOpenPartialHomeomorph (poincareProd m κ) hf' hn
  let φ := φ0.restrOpen (poincareProdDom n) (isOpen_poincareProdDom n)
  have hcoe : (φ : Phase (n + n) → Phase (n * 2)) = poincareProd m κ := rfl
  refine ⟨φ, ⟨hc.mem_toOpenPartialHomeomorph_source hf' hn, hw⟩, hcoe, ?_⟩
  intro y hy
  have hxs : φ.symm y ∈ φ.source := φ.map_target hy
  have hx : φ.symm y ∈ poincareProdDom n := hxs.2
  obtain ⟨B, hB⟩ := poincareProd_fderiv_equiv hm hκ hx
  have hB' : HasFDerivAt φ (B : Phase (n + n) →L[ℝ] Phase (n * 2)) (φ.symm y) := by
    rw [hcoe, hB]
    exact (hana _ hx).differentiableAt.hasFDerivAt
  have hcd : ContDiffAt ℝ ω φ (φ.symm y) := by
    rw [hcoe]; exact (hana _ hx).contDiffAt
  exact (φ.contDiffAt_symm hy hB' hcd).analyticAt

/-! ### The equal-dimension chart -/

/-- F6: the equal-dimension chart `Phase (n*2) → Phase (n*2)` that Part 1's `IsChart` consumes
(`poincareProd` composed with the canonical reindexing; the body permutation stays inside
`poincareProd`). -/
def poincareProdCast (m : Fin n → ℝ) (κ : ℝ) : Phase (n * 2) → Phase (n * 2) :=
  poincareProd m κ ∘ phaseCast (Nat.mul_two n)

def poincareProdCastDom (n : ℕ) : Set (Phase (n * 2)) :=
  phaseCast (Nat.mul_two n) ⁻¹' poincareProdDom n

theorem poincareProdCast_symplectic {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ) :
    IsSymplecticOn 1 (poincareProdCast m κ) (poincareProdCastDom n) := by
  have h1 : IsSymplecticOn 1 (phaseCast (Nat.mul_two n)) (poincareProdCastDom n) :=
    fun z _ => phaseCast_symplectic (Nat.mul_two n) z (mem_univ _)
  have h := IsSymplecticOn.comp h1 (poincareProd_symplectic hm hκ)
    (fun z _ => (phaseCast (Nat.mul_two n)).differentiableAt)
    (fun z hz => ((analyticOnNhd_poincareProd hm hκ) z hz).differentiableAt)
    (fun z hz => hz)
  rw [mul_one] at h
  exact h

theorem analyticOnNhd_poincareProdCast {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ) :
    AnalyticOnNhd ℝ (poincareProdCast m κ) (poincareProdCastDom n) :=
  (analyticOnNhd_poincareProd hm hκ).comp
    ((phaseCast_analytic (Nat.mul_two n)).mono (subset_univ _)) fun _ hz => hz

theorem isOpen_poincareProdCastDom (n : ℕ) : IsOpen (poincareProdCastDom n) :=
  (isOpen_poincareProdDom n).preimage (phaseCast (Nat.mul_two n)).continuous

theorem poincareProdCast_eq_iff {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {z z' : Phase (n * 2)} (hz : z ∈ poincareProdCastDom n) (hz' : z' ∈ poincareProdCastDom n) :
    poincareProdCast m κ z = poincareProdCast m κ z' ↔
      ∃ k : Fin n → ℤ, z' = z + (phaseCast (Nat.mul_two n)).symm
        (fastShift (a := n) (b := n) k) := by
  unfold poincareProdCast
  simp only [Function.comp_apply]
  rw [poincareProd_eq_iff hm hκ hz hz']
  refine exists_congr fun k => ?_
  constructor
  · intro h
    apply (phaseCast (Nat.mul_two n)).injective
    rw [ContinuousLinearEquiv.map_add, ContinuousLinearEquiv.apply_symm_apply]
    exact h
  · intro h
    have := congrArg (phaseCast (Nat.mul_two n)) h
    rwa [ContinuousLinearEquiv.map_add, ContinuousLinearEquiv.apply_symm_apply] at this

end ProductChart

end KAM.Planetary

end
