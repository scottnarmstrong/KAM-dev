/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Ring

/-!
# Coefficient classes for certificate polynomials (track B, B3-COEF)

`CertCoeff K` bundles a computable commutative ring `K` (decidable equality) with its real and
complex semantics, a rational embedding and a computable rational majorant `absUB` of the absolute
value. Instances: `ℚ` (identity semantics, `absUB = |·|`) and `QSqrt2` (`a + b√2`, exact ring
operations, `absUB = |a| + |b| · 141422/100000`).

The polynomial layer `Poly/*` is generic in `K`; its evaluation lemmas take any
`[Algebra K R]`, and the norm bounds take the Prop-class `CertNormLe K 𝕜`
(`‖algebraMap K 𝕜 k‖ ≤ absUB k`), with instances for `ℚ` over every `RCLike 𝕜` and for
`QSqrt2` over `ℝ` and `ℂ`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

/-- A coefficient domain for certificate polynomials. -/
class CertCoeff (K : Type) extends CommRing K where
  /-- decidable equality (kernel computable) -/
  decEq : DecidableEq K
  /-- real semantics -/
  toReal : K →+* ℝ
  /-- complex semantics -/
  toComplex : K →+* ℂ
  /-- the complex semantics is the real one -/
  toComplex_eq : ∀ k, toComplex k = ((toReal k : ℝ) : ℂ)
  /-- the rational embedding -/
  ofRat : ℚ →+* K
  /-- compatibility of `ofRat` with `toReal` -/
  toReal_ofRat : ∀ q : ℚ, toReal (ofRat q) = (q : ℝ)
  /-- a computable rational majorant of the absolute value -/
  absUB : K → ℚ
  /-- the majorant property -/
  abs_toReal_le : ∀ k, |toReal k| ≤ (absUB k : ℝ)

instance (priority := 900) certCoeffDecEq (K : Type) [CertCoeff K] : DecidableEq K :=
  CertCoeff.decEq

/-- The norm-compatibility of a `K`-algebra structure on `𝕜` with `absUB`. -/
class CertNormLe (K : Type) (𝕜 : Type*) [CertCoeff K] [RCLike 𝕜] [Algebra K 𝕜] : Prop where
  norm_le : ∀ k : K, ‖algebraMap K 𝕜 k‖ ≤ ((CertCoeff.absUB k : ℚ) : ℝ)

/-- The coefficient `q : ℚ` as an element of `K`. -/
def ratCoeff {K : Type} [CertCoeff K] (q : ℚ) : K := (CertCoeff.ofRat (K := K)) q

theorem algebraMap_ratCoeff {K : Type} {𝕜 : Type*} [CertCoeff K] [DivisionRing 𝕜] [Algebra K 𝕜]
    (q : ℚ) : algebraMap K 𝕜 (ratCoeff q) = (q : 𝕜) := by
  unfold ratCoeff
  exact eq_ratCast ((algebraMap K 𝕜).comp (CertCoeff.ofRat (K := K))) q

theorem ratCoeff_half_mul_two {K : Type} [CertCoeff K] :
    (ratCoeff (1 / 2) : K) * ((2 : ℕ) : K) = 1 := by
  unfold ratCoeff
  rw [← map_natCast (CertCoeff.ofRat (K := K)) 2, ← map_mul]
  norm_num

/-! ### The instance `ℚ` -/

@[default_instance] instance instCertCoeffRat : CertCoeff ℚ :=
  { Rat.commRing with
    decEq := inferInstance
    toReal := Rat.castHom ℝ
    toComplex := Rat.castHom ℂ
    toComplex_eq := fun k => by simp
    ofRat := RingHom.id ℚ
    toReal_ofRat := fun q => by simp
    absUB := fun q => |q|
    abs_toReal_le := fun q => by simp }

@[simp] theorem absUB_rat (q : ℚ) : CertCoeff.absUB q = |q| := rfl

@[simp] theorem ratCoeff_rat (q : ℚ) : (ratCoeff q : ℚ) = q := rfl

theorem norm_algebraMap_rat' {𝕜 : Type*} [RCLike 𝕜] (c : ℚ) :
    ‖algebraMap ℚ 𝕜 c‖ = |(c : ℝ)| := by
  rw [eq_ratCast (algebraMap ℚ 𝕜), ← RCLike.ofReal_ratCast, RCLike.norm_ofReal]

instance instCertNormLeRat (𝕜 : Type*) [RCLike 𝕜] : CertNormLe ℚ 𝕜 :=
  ⟨fun c => by rw [norm_algebraMap_rat']; simp⟩

/-! ### The instance `QSqrt2` -/

/-- The exact ring `ℚ(√2)`: `⟨a, b⟩` means `a + b√2`. -/
@[ext] structure QSqrt2 where
  /-- the rational part -/
  a : ℚ
  /-- the coefficient of `√2` -/
  b : ℚ
  deriving DecidableEq

namespace QSqrt2

instance : Add QSqrt2 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg QSqrt2 := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub QSqrt2 := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Mul QSqrt2 := ⟨fun x y => ⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩⟩
instance : Zero QSqrt2 := ⟨⟨0, 0⟩⟩
instance : One QSqrt2 := ⟨⟨1, 0⟩⟩
instance : NatCast QSqrt2 := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast QSqrt2 := ⟨fun n => ⟨n, 0⟩⟩

@[simp] theorem add_a (x y : QSqrt2) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : QSqrt2) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_a (x : QSqrt2) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : QSqrt2) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : QSqrt2) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : QSqrt2) : (x - y).b = x.b - y.b := rfl
@[simp] theorem mul_a (x y : QSqrt2) : (x * y).a = x.a * y.a + 2 * (x.b * y.b) := rfl
@[simp] theorem mul_b (x y : QSqrt2) : (x * y).b = x.a * y.b + x.b * y.a := rfl
@[simp] theorem zero_a : (0 : QSqrt2).a = 0 := rfl
@[simp] theorem zero_b : (0 : QSqrt2).b = 0 := rfl
@[simp] theorem one_a : (1 : QSqrt2).a = 1 := rfl
@[simp] theorem one_b : (1 : QSqrt2).b = 0 := rfl
@[simp] theorem natCast_a (n : ℕ) : (n : QSqrt2).a = n := rfl
@[simp] theorem natCast_b (n : ℕ) : (n : QSqrt2).b = 0 := rfl
@[simp] theorem intCast_a (n : ℤ) : (n : QSqrt2).a = n := rfl
@[simp] theorem intCast_b (n : ℤ) : (n : QSqrt2).b = 0 := rfl

instance : CommRing QSqrt2 where
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel x := by ext <;> simp
  sub_eq_add_neg x y := by ext <;> simp [sub_eq_add_neg]
  left_distrib x y z := by ext <;> simp <;> ring
  right_distrib x y z := by ext <;> simp <;> ring
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  mul_comm x y := by ext <;> simp <;> ring
  toNatCast := inferInstance
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp
  toIntCast := inferInstance
  intCast_ofNat n := by ext <;> simp
  intCast_negSucc n := by ext <;> simp
  npow := npowRec

/-- The embedding `a + b√2 ↦ a + b √2` into `ℝ`. -/
def realVal (x : QSqrt2) : ℝ := (x.a : ℝ) + (x.b : ℝ) * Real.sqrt 2

theorem sqrt_two_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- The ring homomorphism `QSqrt2 →+* ℝ`. -/
def qsqrt2RealHom : QSqrt2 →+* ℝ where
  toFun := realVal
  map_one' := by simp [realVal]
  map_mul' x y := by
    have := sqrt_two_sq
    simp only [realVal, mul_a, mul_b]
    push_cast
    linear_combination (-((x.b : ℝ) * y.b)) * this
  map_zero' := by simp [realVal]
  map_add' x y := by simp only [realVal, add_a, add_b]; push_cast; ring

/-- The rational embedding. -/
def ofRatHom : ℚ →+* QSqrt2 where
  toFun q := ⟨q, 0⟩
  map_one' := rfl
  map_mul' x y := by ext <;> simp
  map_zero' := rfl
  map_add' x y := by ext <;> simp

theorem sqrt_two_le : Real.sqrt 2 ≤ ((141422 / 100000 : ℚ) : ℝ) := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- The computable rational majorant `|a| + |b| · 141422/100000`. -/
def absUB (x : QSqrt2) : ℚ := |x.a| + |x.b| * (141422 / 100000)

theorem abs_realVal_le (x : QSqrt2) : |realVal x| ≤ ((absUB x : ℚ) : ℝ) := by
  have h2 := sqrt_two_le
  have h0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold realVal absUB
  push_cast at h2 ⊢
  calc |(x.a : ℝ) + (x.b : ℝ) * Real.sqrt 2|
      ≤ |(x.a : ℝ)| + |(x.b : ℝ) * Real.sqrt 2| := abs_add_le _ _
    _ = |(x.a : ℝ)| + |(x.b : ℝ)| * Real.sqrt 2 := by rw [abs_mul, abs_of_nonneg h0]
    _ ≤ _ := by gcongr

end QSqrt2

instance instCertCoeffQSqrt2 : CertCoeff QSqrt2 :=
  { (inferInstance : CommRing QSqrt2) with
    decEq := inferInstance
    toReal := QSqrt2.qsqrt2RealHom
    toComplex := Complex.ofRealHom.comp QSqrt2.qsqrt2RealHom
    toComplex_eq := fun k => rfl
    ofRat := QSqrt2.ofRatHom
    toReal_ofRat := fun q => by simp [QSqrt2.qsqrt2RealHom, QSqrt2.ofRatHom, QSqrt2.realVal]
    absUB := QSqrt2.absUB
    abs_toReal_le := QSqrt2.abs_realVal_le }

/-- `QSqrt2` is a real algebra through `toReal`. -/
instance instAlgebraQSqrt2Real : Algebra QSqrt2 ℝ := (CertCoeff.toReal (K := QSqrt2)).toAlgebra

/-- `QSqrt2` is a complex algebra through `toComplex`. -/
instance instAlgebraQSqrt2Complex : Algebra QSqrt2 ℂ :=
  (CertCoeff.toComplex (K := QSqrt2)).toAlgebra

instance : IsScalarTower QSqrt2 ℝ ℂ :=
  IsScalarTower.of_algebraMap_eq fun k => by
    exact CertCoeff.toComplex_eq (K := QSqrt2) k

theorem algebraMap_qsqrt2_real (x : QSqrt2) :
    algebraMap QSqrt2 ℝ x = (x.a : ℝ) + (x.b : ℝ) * Real.sqrt 2 := rfl

instance : CertNormLe QSqrt2 ℝ :=
  ⟨fun k => by
    rw [Real.norm_eq_abs]
    exact CertCoeff.abs_toReal_le k⟩

instance : CertNormLe QSqrt2 ℂ :=
  ⟨fun k => by
    change ‖CertCoeff.toComplex (K := QSqrt2) k‖ ≤ _
    rw [CertCoeff.toComplex_eq, Complex.norm_real, Real.norm_eq_abs]
    exact CertCoeff.abs_toReal_le k⟩

end KAM.EffectiveStability
