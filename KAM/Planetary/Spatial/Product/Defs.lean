/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Planetary.Poincare.Product
public import KAM.Planetary.Spatial.Vector
public import KAM.Planetary.Spatial.Chart.Defs
public import KAM.Planetary.Spatial.Chart.Analytic

/-!
# The n-body spatial product chart: layout, block maps and definitions

Package LP-SP-PROD, `LP:MAIN L17 (533–578)` for `n` bodies, with `AMENDMENTS` N12; track LP,
non-frozen.

**Layout.** A point of the product domain is `w : Phase (n + (n + n))` (`n` fast pairs, `2n`
slow pairs), with the body-wise slot convention of LP-SP-CHART:

* `w.1 = (λ_1..λ_n | ξ_1..ξ_n | v_1..v_n)` (`fast w.1 = λ`, `slow w.1 = (ξ | v)`),
* `w.2 = (I_1..I_n | η_1..η_n | u_1..u_n)` (`fast w.2 = I`, `slow w.2 = (η | u)`).

So the `i`-th body block is the point `((λ_i, ξ_i, v_i), (I_i, η_i, u_i))` of `Phase 3`
(`spatialBlock`), and the slow part `slow w : Fin (n + n) → ℝ` is exactly the slow pair of
`Nekhoroshev.PartialBlock n (n + n)` (`fastAction`, `slowPair` of `KAM/Nekhoroshev/Partial/Setting`).
`spatialPoincareProd ν w : Phase (n * 3)` applies the one-body chart `spatialPoincare (ν i)` to
each block (body-major ordering of the `3n` Cartesian coordinates, `bodyVector3`).

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary

variable {n : ℕ}

/-! ### Definitions -/

/-- The `i`-th body's coordinates `((λ_i, ξ_i, v_i), (I_i, η_i, u_i))` of a point of
`Phase (n + (n + n))`. -/
def spatialBlock (w : Phase (n + (n + n))) (i : Fin n) : Phase 3 :=
  (![fast w.1 i, slow w.1 (Fin.castAdd n i), slow w.1 (Fin.natAdd n i)],
   ![fast w.2 i, slow w.2 (Fin.castAdd n i), slow w.2 (Fin.natAdd n i)])

/-- Reassemble a family of spatial one-body phase points as a point of `Phase (n * 3)`. -/
def ofSpatialBodies (P : Fin n → Phase 3) : Phase (n * 3) :=
  (ofBodies3 fun i => (P i).1, ofBodies3 fun i => (P i).2)

/-- Reassemble a family of one-body chart points as a point of `Phase (n + (n + n))`. -/
def unblockSpatial (P : Fin n → Phase 3) : Phase (n + (n + n)) :=
  (Fin.append (fun i => (P i).1 0) (Fin.append (fun i => (P i).1 1) (fun i => (P i).1 2)),
   Fin.append (fun i => (P i).2 0) (Fin.append (fun i => (P i).2 1) (fun i => (P i).2 2)))

/-- MAIN Lemma 17 for `n` bodies: the body-wise spatial Poincaré charts, `ν_i` the masses. -/
def spatialPoincareProd (ν : Fin n → ℝ) (w : Phase (n + (n + n))) : Phase (n * 3) :=
  ofSpatialBodies fun i => spatialPoincare (ν i) (spatialBlock w i)

/-- The product of the domains (44). -/
def spatialPoincareProdDom (n : ℕ) : Set (Phase (n + (n + n))) :=
  {w | ∀ i, spatialBlock w i ∈ spatialPoincareDom}

/-- The product image region: every body prograde with respect to `e₃` and of negative energy. -/
def spatialRegionProd (ν : Fin n → ℝ) : Set (Phase (n * 3)) :=
  {z | ∀ i, (bodyVector3 z.1 i, bodyVector3 z.2 i) ∈ spatialRegion (ν i)}

/-- The actions `I_i` of a chart point. -/
def spatialActions (w : Phase (n + (n + n))) : Fin n → ℝ := fast w.2

/-- `Γ_i = (ξ_i² + η_i²)/2`. -/
def spatialGammaBody (w : Phase (n + (n + n))) (i : Fin n) : ℝ := spatialGamma (spatialBlock w i)

/-- `Z_i = (u_i² + v_i²)/2`. -/
def spatialZBody (w : Phase (n + (n + n))) (i : Fin n) : ℝ := spatialZ (spatialBlock w i)

/-! ### Block calculus -/

theorem spatialPoincareProd_eq (ν : Fin n → ℝ) (w : Phase (n + (n + n))) :
    spatialPoincareProd ν w = ofSpatialBodies fun i => spatialPoincare (ν i) (spatialBlock w i) :=
  rfl

theorem bodyVector3_ofSpatialBodies_fst (P : Fin n → Phase 3) (i : Fin n) :
    bodyVector3 (ofSpatialBodies P).1 i = (P i).1 := by
  show bodyVector3 (ofBodies3 fun i => (P i).1) i = _
  exact bodyVector3_ofBodies3 _ i

theorem bodyVector3_ofSpatialBodies_snd (P : Fin n → Phase 3) (i : Fin n) :
    bodyVector3 (ofSpatialBodies P).2 i = (P i).2 := by
  show bodyVector3 (ofBodies3 fun i => (P i).2) i = _
  exact bodyVector3_ofBodies3 _ i

theorem ofSpatialBodies_injective : Function.Injective (ofSpatialBodies (n := n)) := by
  intro P Q h
  funext i
  refine Prod.ext ?_ ?_
  · rw [← bodyVector3_ofSpatialBodies_fst P i, ← bodyVector3_ofSpatialBodies_fst Q i, h]
  · rw [← bodyVector3_ofSpatialBodies_snd P i, ← bodyVector3_ofSpatialBodies_snd Q i, h]

theorem ofSpatialBodies_bodyVector3 (z : Phase (n * 3)) :
    ofSpatialBodies (fun i => (bodyVector3 z.1 i, bodyVector3 z.2 i)) = z := by
  unfold ofSpatialBodies
  rw [ofBodies3_bodyVector3, ofBodies3_bodyVector3]

theorem spatialBlock_unblockSpatial (P : Fin n → Phase 3) (i : Fin n) :
    spatialBlock (unblockSpatial P) i = P i := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
    simp [spatialBlock, unblockSpatial, fast, slow]

theorem spatialPoincareProd_block (ν : Fin n → ℝ) (w : Phase (n + (n + n))) (i : Fin n) :
    (bodyVector3 (spatialPoincareProd ν w).1 i, bodyVector3 (spatialPoincareProd ν w).2 i) =
      spatialPoincare (ν i) (spatialBlock w i) := by
  rw [spatialPoincareProd_eq, bodyVector3_ofSpatialBodies_fst, bodyVector3_ofSpatialBodies_snd]

/-- `ofSpatialBodies` as a continuous linear map. -/
def ofSpatialBodiesCLM : (Fin n → Phase 3) →L[ℝ] Phase (n * 3) :=
  (ContinuousLinearMap.pi fun k : Fin (n * 3) =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (finProdFinEquiv.symm k).2).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 3 → ℝ))).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Phase 3)
          (finProdFinEquiv.symm k).1)).prod
    (ContinuousLinearMap.pi fun k : Fin (n * 3) =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (finProdFinEquiv.symm k).2).comp
        (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) (Fin 3 → ℝ))).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Phase 3)
          (finProdFinEquiv.symm k).1))

theorem ofSpatialBodiesCLM_apply (P : Fin n → Phase 3) :
    ofSpatialBodiesCLM P = ofSpatialBodies P := rfl

/-- The slots of body `i` in `Fin (n + (n + n))`. -/
def blockSlots (i : Fin n) : Fin 3 → Fin (n + (n + n)) :=
  ![Fin.castAdd (n + n) i, Fin.natAdd n (Fin.castAdd n i), Fin.natAdd n (Fin.natAdd n i)]

/-- The `i`-th body block as a continuous linear map. -/
def spatialBlockCLM (i : Fin n) : Phase (n + (n + n)) →L[ℝ] Phase 3 :=
  (ContinuousLinearMap.pi fun k : Fin 3 =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + (n + n)) => ℝ)
        (blockSlots i k)).comp
        (ContinuousLinearMap.fst ℝ (Fin (n + (n + n)) → ℝ) (Fin (n + (n + n)) → ℝ))).prod
    (ContinuousLinearMap.pi fun k : Fin 3 =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + (n + n)) => ℝ)
        (blockSlots i k)).comp
        (ContinuousLinearMap.snd ℝ (Fin (n + (n + n)) → ℝ) (Fin (n + (n + n)) → ℝ)))

theorem spatialBlockCLM_apply (i : Fin n) (w : Phase (n + (n + n))) :
    spatialBlockCLM i w = spatialBlock w i := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
    simp [spatialBlockCLM, blockSlots, spatialBlock, fast, slow]

theorem isOpen_spatialPoincareProdDom (n : ℕ) : IsOpen (spatialPoincareProdDom n) := by
  have : spatialPoincareProdDom n = ⋂ i, spatialBlockCLM i ⁻¹' spatialPoincareDom := by
    ext w; simp [spatialPoincareProdDom, spatialBlockCLM_apply]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_spatialPoincareDom.preimage (spatialBlockCLM i).continuous

/-! ### The symplectic form in blocks -/

theorem symplecticForm_ofSpatialBodies (P Q : Fin n → Phase 3) :
    symplecticForm (ofSpatialBodies P) (ofSpatialBodies Q) = ∑ i, symplecticForm (P i) (Q i) := by
  unfold symplecticForm
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp [ofSpatialBodies, ofBodies3]

theorem symplecticForm_spatialBlocks (u v : Phase (n + (n + n))) :
    symplecticForm u v = ∑ i, symplecticForm (spatialBlock u i) (spatialBlock v i) := by
  unfold symplecticForm
  rw [Fin.sum_univ_add, Fin.sum_univ_add (a := n) (b := n)]
  simp only [spatialBlock, fast, slow, Fin.sum_univ_three, Finset.sum_add_distrib]
  simp
  ring

/-! ### The fast lattice -/

/-- The lattice shift of the product chart: `λ_i ↦ λ_i + 2π k_i`. -/
def spatialProdShift (k : Fin n → ℤ) (w : Phase (n + (n + n))) : Phase (n + (n + n)) :=
  w + fastShift (a := n) (b := n + n) k

theorem spatialBlock_shift (w : Phase (n + (n + n))) (k : Fin n → ℤ) (i : Fin n) :
    spatialBlock (spatialProdShift k w) i = spatialShift (k i) (spatialBlock w i) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> fin_cases j <;>
    simp [spatialBlock, spatialShift, spatialProdShift, fast, slow, fastShift, Fin.append_left,
      Fin.append_right]

end KAM.Planetary.Spatial

end
