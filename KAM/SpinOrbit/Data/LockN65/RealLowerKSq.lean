/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.RealLowerK
public import KAM.SpinOrbit.Data.LockN65.SegSupport

/-!
# The keyed lower-bound check with its square memoized (lock-owned)

`checkRealLowerBoundK_of_sq`: `checkRealLowerBoundK` from a memoized polynomial product of the
square `g g*` (`polyProduct … = some out`) and the check of the model with that product
substituted (`realLowerModelKOf`: the model of `realLowerModelK` with the square's `CertModel.mul`
replaced by the landed body of `mul_eq_of_polyProduct_cseg`). The pass modules then close the
check by one `exact` and one kernel run, with no rewriting inside the concrete model.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate CertArith

variable {α : Type} [CertArith α]

/-- The model of `realLowerModelK` with the square's polynomial product given as `out`. -/
def realLowerModelKOf (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey) (f : CertModel α)
    (m₀ : ℚ) (g : CertPoly α) (out : List (ErrTerm α) × α) : CertModel α :=
  let cfg' : ModelConfig α :=
    { cfg with advice := cfg.advice ++ [(key, ProductAdvice.direct)] }
  let a : CertModel α := ⟨0, g, ofInt 0⟩
  let b : CertModel α := ⟨0, g.conjSorted, ofInt 0⟩
  let gg : CertModel α :=
    ⟨a.deg + b.deg, truncPoly cfg'.cutoff out.1,
      upAdd (upAdd out.2 (errRadius W (out.1.map (truncErr cfg'.cutoff))))
        (upAdd (upAdd (crossUp (a.poly.supNormUp W) b.rad) (crossUp (b.poly.supNormUp W) a.rad))
          (upMul a.rad b.rad))⟩
  let G := CertModel.mul W cfg' key gg (CertModel.ofConst g.keyLen (ofInt (-2)) (ofInt 0))
  let c : α := ofRatUp (-2 * m₀)
  let len := if f.poly.terms.isEmpty then g.keyLen else f.poly.keyLen
  CertModel.add W (CertModel.add W (CertModel.add W f f.starModel) G)
    (CertModel.ofConst len c (upAdd c (neg (ofRatDown (-2 * m₀)))))

theorem realLowerModelK_eq_of_sq (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (f : CertModel α) (m₀ : ℚ) (g : CertPoly α) {out : List (ErrTerm α) × α}
    (h : CertModel.polyProduct W
      { cfg with advice := cfg.advice ++ [(key, ProductAdvice.direct)] } key g g.conjSorted =
        some out) :
    realLowerModelK W cfg key f m₀ g = realLowerModelKOf W cfg key f m₀ g out := by
  unfold realLowerModelK realLowerModelKOf
  simp only
  rw [mul_eq_of_polyProduct_cseg _ _ _ ⟨0, g, ofInt 0⟩ ⟨0, g.conjSorted, ofInt 0⟩ h]

/-- **The keyed lower-bound check from its memoized square.** -/
theorem checkRealLowerBoundK_of_sq {W : CertWeight} {cfg : ModelConfig α} {key : ProductKey}
    {f : CertModel α} {m₀ m : ℚ} {g : CertPoly α} {out : List (ErrTerm α) × α}
    (h : CertModel.polyProduct W
      { cfg with advice := cfg.advice ++ [(key, ProductAdvice.direct)] } key g g.conjSorted =
        some out)
    (hc : (decide (f.deg = 0) &&
      ble ((realLowerModelKOf W cfg key f m₀ g out).supBound W)
        (ofRatDown (2 * (m₀ - m)))) = true) :
    checkRealLowerBoundK W cfg key f m₀ m g = true := by
  unfold checkRealLowerBoundK
  rw [realLowerModelK_eq_of_sq W cfg key f m₀ g h]
  exact hc

/-- The square `g g*` as the model of `CertModel.mul` with its polynomial product given as `out`. -/
def sqModelOf (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey) (g : CertPoly α)
    (out : List (ErrTerm α) × α) : CertModel α :=
  let cfg' : ModelConfig α :=
    { cfg with advice := cfg.advice ++ [(key, ProductAdvice.direct)] }
  let a : CertModel α := ⟨0, g, ofInt 0⟩
  let b : CertModel α := ⟨0, g.conjSorted, ofInt 0⟩
  ⟨a.deg + b.deg, truncPoly cfg'.cutoff out.1,
    upAdd (upAdd out.2 (errRadius W (out.1.map (truncErr cfg'.cutoff))))
      (upAdd (upAdd (crossUp (a.poly.supNormUp W) b.rad) (crossUp (b.poly.supNormUp W) a.rad))
        (upMul a.rad b.rad))⟩

/-- The model of `realLowerModelK` from its parts: `f` and the scaled square `G`. -/
def realLowerModelKParts (W : CertWeight) (f : CertModel α) (g : CertPoly α) (m₀ : ℚ)
    (G : CertModel α) : CertModel α :=
  let c : α := ofRatUp (-2 * m₀)
  let len := if f.poly.terms.isEmpty then g.keyLen else f.poly.keyLen
  CertModel.add W (CertModel.add W (CertModel.add W f f.starModel) G)
    (CertModel.ofConst len c (upAdd c (neg (ofRatDown (-2 * m₀)))))

theorem realLowerModelK_eq_parts (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (f : CertModel α) (m₀ : ℚ) (g : CertPoly α) {out : List (ErrTerm α) × α}
    (h : CertModel.polyProduct W
      { cfg with advice := cfg.advice ++ [(key, ProductAdvice.direct)] } key g g.conjSorted =
        some out) :
    realLowerModelK W cfg key f m₀ g =
      realLowerModelKParts W f g m₀
        (CertModel.mul W { cfg with advice := cfg.advice ++ [(key, ProductAdvice.direct)] } key
          (sqModelOf W cfg key g out) (CertModel.ofConst g.keyLen (ofInt (-2)) (ofInt 0))) := by
  rw [realLowerModelK_eq_of_sq W cfg key f m₀ g h]
  rfl

/-- **The keyed lower-bound check from its parts**: the memoized square, the square's model `gg`,
the scaled square `G`, the model `f` and the whole model `H`, each given (in the pass modules: each
equal to a literal by its own kernel run), and the check on `H`. -/
theorem checkRealLowerBoundK_of_parts {W : CertWeight} {cfg : ModelConfig α} {key : ProductKey}
    {f f' gg G H : CertModel α} {m₀ m : ℚ} {g : CertPoly α} {out : List (ErrTerm α) × α}
    (h : CertModel.polyProduct W
      { cfg with advice := cfg.advice ++ [(key, ProductAdvice.direct)] } key g g.conjSorted =
        some out)
    (hgg : sqModelOf W cfg key g out = gg)
    (hG : CertModel.mul W { cfg with advice := cfg.advice ++ [(key, ProductAdvice.direct)] } key
      gg (CertModel.ofConst g.keyLen (ofInt (-2)) (ofInt 0)) = G)
    (hf : f = f') (hH : realLowerModelKParts W f' g m₀ G = H)
    (hc : (decide (f'.deg = 0) && ble (H.supBound W) (ofRatDown (2 * (m₀ - m)))) = true) :
    checkRealLowerBoundK W cfg key f m₀ m g = true := by
  subst hgg hG hf hH
  unfold checkRealLowerBoundK
  rw [realLowerModelK_eq_parts W cfg key f m₀ g h]
  exact hc

end KAM.SpinOrbit.Data.LockN65
