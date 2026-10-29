/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.Constants
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Rational mirrors of the isoenergetic KAM constants

The constants `isoC1`, `isoC2` of `KAM/Iso/Apost/Defs.lean` are real numbers built from `π`, `e`
and a real power. For `τ ∈ ℕ` every power is a natural power, and `c_R = max 1 (cohConst n τ)` is
the only constant containing `π` and `e`. Here:

* `cRUpQ n τ` is a rational upper bound of `c_R` from `π > 3.141592` and `e > 2.718`
  (`cR_le_cRUpQ`);
* every constant of the chain has a rational mirror (`mSizeQ`, `ThetaQ`, ..., `hatcStarQ`) with
  `c_R` replaced by `cRUpQ`, and a comparison lemma (`ThetaQ_ge`, ...) stating that the real
  constant is at most the mirror;
* `isoC1Q`, `isoC2Q` are the mirrors of `isoC1`, `isoC2` with `isoC1_le_isoC1Q`,
  `isoC2_le_isoC2Q`.

All mirrors are kernel-computable (`ℚ`, `max`, natural powers), so a concrete parameter package can
be evaluated by `decide +kernel`; see `isoC1Q_pilot`, `isoC2Q_pilot`.
-/

@[expose] public section

namespace KAM.Certificate

open KAM KAM.Apost KAM.Iso.Apost

/-! ### The coherence constant -/

/-- A kernel-computable upper bound for `c_R = max 1 (cohConst n τ)` (`π > 3.141592`,
`e > 2.718`). -/
def cRUpQ (n τ : ℕ) : ℚ :=
  max 1 ((2 * (3141592 / 1000000 : ℚ))⁻¹ * (τ / (2718 / 1000 * (3141592 / 1000000 : ℚ))) ^ τ *
    (8 * n / (3141592 / 1000000 : ℚ)) ^ n)

theorem cR_le_cRUpQ (n τ : ℕ) : KAM.Apost.cR n τ ≤ cRUpQ n τ := by
  have hπ : ((3141592 / 1000000 : ℚ) : ℝ) < Real.pi := by
    have := Real.pi_gt_d6
    push_cast
    linarith
  have he : ((2718 / 1000 : ℚ) : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    push_cast
    linarith
  have hπ0 : (0 : ℝ) < ((3141592 / 1000000 : ℚ) : ℝ) := by norm_num
  have he0 : (0 : ℝ) < ((2718 / 1000 : ℚ) : ℝ) := by norm_num
  unfold KAM.Apost.cR cRUpQ
  push_cast
  refine max_le_max le_rfl ?_
  unfold KAM.cohConst
  rw [Real.rpow_natCast]
  have h1 : ((2 : ℝ) * Real.pi)⁻¹ ≤ (2 * ((3141592 / 1000000 : ℚ) : ℝ))⁻¹ := by gcongr
  have h2 : (τ : ℝ) / (Real.exp 1 * Real.pi) ≤
      τ / (((2718 / 1000 : ℚ) : ℝ) * ((3141592 / 1000000 : ℚ) : ℝ)) := by gcongr
  have h3 : 8 * (n : ℝ) / Real.pi ≤ 8 * n / ((3141592 / 1000000 : ℚ) : ℝ) := by gcongr
  push_cast at h1 h2 h3 ⊢
  gcongr

/-! ### Mirrors of the constants of track K -/

section Mirrors

variable (n τ : ℕ) (M σK σB σT : ℚ)

def mSizeQ : ℚ := max 1 (max M (max σK (max σB σT)))
def ThetaQ : ℚ := 4 * n * mSizeQ M σK σB σT ^ 3
def CXQ : ℚ := 5 * (n : ℚ) ^ 2 * mSizeQ M σK σB σT ^ 5
def CTQ : ℚ := 2 * n * mSizeQ M σK σB σT ^ 2 * CXQ n M σK σB σT
def COmegaQ : ℚ := 2 * n * (n + 1) * cRUpQ n τ * mSizeQ M σK σB σT
def CsymQ : ℚ := mSizeQ M σK σB σT ^ 2 * COmegaQ n τ M σK σB σT
def CredQ : ℚ := 2 * n * (n + 1) * mSizeQ M σK σB σT ^ 2
def Cxi0Q : ℚ := 2 * n * mSizeQ M σK σB σT ^ 2 *
  (mSizeQ M σK σB σT * ThetaQ n M σK σB σT + cRUpQ n τ * CTQ n M σK σB σT)
def CGQ : ℚ := 6 * (n : ℚ) ^ 2 * mSizeQ M σK σB σT
def CBQ : ℚ := 2 * mSizeQ M σK σB σT ^ 2 * CGQ n M σK σB σT
def CDNQ : ℚ := 2 * n * mSizeQ M σK σB σT + mSizeQ M σK σB σT * CBQ n M σK σB σT
def CDXQ : ℚ := 2 * mSizeQ M σK σB σT ^ 3 +
  (mSizeQ M σK σB σT + n * ThetaQ n M σK σB σT) * CDNQ n M σK σB σT
def CDTQ : ℚ := 4 * n * mSizeQ M σK σB σT ^ 2 * CDXQ n M σK σB σT +
  2 * n * CDNQ n M σK σB σT * CXQ n M σK σB σT

/-! ### Mirrors of the constants of `KAM/Iso/Apost/Defs.lean` -/

def CYQ : ℚ := n * mSizeQ M σK σB σT * (2 * mSizeQ M σK σB σT ^ 2 + CDNQ n M σK σB σT)
def CDTbordQ : ℚ := CDTQ n M σK σB σT + 8 * n ^ 2 * mSizeQ M σK σB σT ^ 4 + 1 +
  CYQ n M σK σB σT
def hatCSQ : ℚ := max (Cxi0Q n τ M σK σB σT)
  (mSizeQ M σK σB σT * ThetaQ n M σK σB σT + 2 * n * cRUpQ n τ * mSizeQ M σK σB σT ^ 5)
def hatCxiNQ : ℚ := hatCSQ n τ M σK σB σT + 2 * n * cRUpQ n τ * mSizeQ M σK σB σT
def hatCgQ : ℚ := CTQ n M σK σB σT * hatCxiNQ n τ M σK σB σT +
  ThetaQ n M σK σB σT * hatCSQ n τ M σK σB σT +
  2 * n * mSizeQ M σK σB σT ^ 2 * ThetaQ n M σK σB σT
def hatCxiQ : ℚ := max (cRUpQ n τ * hatCgQ n τ M σK σB σT)
  (ThetaQ n M σK σB σT * hatCxiNQ n τ M σK σB σT)
def hatCDKQ : ℚ := 2 * mSizeQ M σK σB σT ^ 2 * hatCxiQ n τ M σK σB σT
def hatCDeltaQ : ℚ := max (hatCDKQ n τ M σK σB σT)
  (ThetaQ n M σK σB σT ^ 2 * hatCSQ n τ M σK σB σT)
def CPQ : ℚ := mSizeQ M σK σB σT ^ 2 + n + mSizeQ M σK σB σT ^ 3 + CXQ n M σK σB σT
def hatCpartialQ : ℚ := CPQ n M σK σB σT * hatCxiQ n τ M σK σB σT +
  2 * mSizeQ M σK σB σT ^ 2 * ThetaQ n M σK σB σT * hatCgQ n τ M σK σB σT
def hatClinQ : ℚ := CredQ n M σK σB σT * hatCxiQ n τ M σK σB σT +
  CsymQ n τ M σK σB σT * hatCgQ n τ M σK σB σT +
  ThetaQ n M σK σB σT * COmegaQ n τ M σK σB σT * hatCSQ n τ M σK σB σT
def hatCE1Q : ℚ := 4 * mSizeQ M σK σB σT ^ 2 * ThetaQ n M σK σB σT ^ 2 *
    hatClinQ n τ M σK σB σT +
  mSizeQ M σK σB σT * hatCDKQ n τ M σK σB σT ^ 2 +
  ThetaQ n M σK σB σT * hatCSQ n τ M σK σB σT * hatCpartialQ n τ M σK σB σT
def hatCE2Q : ℚ := n * ThetaQ n M σK σB σT ^ 2 *
  (2 * n * mSizeQ M σK σB σT + COmegaQ n τ M σK σB σT) * cRUpQ n τ * hatCgQ n τ M σK σB σT +
  mSizeQ M σK σB σT * hatCDKQ n τ M σK σB σT ^ 2
def hatCEQ : ℚ := max (hatCE1Q n τ M σK σB σT) (hatCE2Q n τ M σK σB σT)
def hatcStepQ : ℚ := 2 * ThetaQ n M σK σB σT ^ 3 * max (CsymQ n τ M σK σB σT)
  (mSizeQ M σK σB σT * CDTbordQ n M σK σB σT * hatCDeltaQ n τ M σK σB σT)
def hatcSumQ : ℚ := 4 * ThetaQ n M σK σB σT ^ 2 * hatCDeltaQ n τ M σK σB σT *
  max (n : ℚ) (max (CBQ n M σK σB σT) (mSizeQ M σK σB σT ^ 2 * CDTbordQ n M σK σB σT))
def hatcStarQ (μ ν : ℚ) : ℚ := max (2 ^ (2 * (2 * (τ + n) + 2)) * hatCEQ n τ M σK σB σT)
  (max (hatcStepQ n τ M σK σB σT * max 1 (2 / μ))
    (max (2 * hatcSumQ n τ M σK σB σT / μ)
      (4 * ThetaQ n M σK σB σT ^ 2 * hatCDeltaQ n τ M σK σB σT / ν)))

end Mirrors

/-- `δ₀ = min {1, (ρ - ρ_∞)/8}`. -/
def delta0Q (ρ ρinf : ℚ) : ℚ := min 1 ((ρ - ρinf) / 8)

/-- Rational mirror of `isoC1` (`τ ∈ ℕ`, `c_R` replaced by `cRUpQ`); the exponent `-2a` of `δ₀`
is `-(4 (τ + n) + 4)`. -/
def isoC1Q (n τ : ℕ) (ρ ρinf M σK σB σT μ ν γbar : ℚ) : ℚ :=
  ρ ^ (4 * τ) * max (γbar ^ 4)
    (hatcStarQ n τ M σK σB σT μ ν * (delta0Q ρ ρinf ^ (2 * (2 * (τ + n) + 2)))⁻¹)

/-- Rational mirror of `isoC2`. -/
def isoC2Q (n τ : ℕ) (ρ ρinf M σK σB σT : ℚ) : ℚ :=
  2 * hatCDeltaQ n τ M σK σB σT * ρ ^ (2 * τ) * (delta0Q ρ ρinf ^ (2 * (τ + n) + 2))⁻¹

/-! ### The real constants are bounded by their mirrors -/

section Compare

variable {n τ : ℕ} {M σK σB σT : ℚ}

local notation "P" => Params n (τ : ℝ) (M : ℝ) (σK : ℝ) (σB : ℝ) (σT : ℝ)

theorem aExp_cast (n τ : ℕ) : aExp n (τ : ℝ) = ((2 * (τ + n) + 2 : ℕ) : ℝ) := by
  unfold aExp kappa
  push_cast
  ring

theorem mSizeQ_ge (M σK σB σT : ℚ) :
    mSize (M : ℝ) (σK : ℝ) (σB : ℝ) (σT : ℝ) ≤ (mSizeQ M σK σB σT : ℝ) := by
  unfold mSize mSizeQ
  push_cast
  exact le_rfl

theorem ThetaQ_ge (_hP : P) : Theta n (M : ℝ) σK σB σT ≤ (ThetaQ n M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  unfold Theta ThetaQ
  push_cast
  gcongr

theorem CXQ_ge (_hP : P) : C_X n (M : ℝ) σK σB σT ≤ (CXQ n M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  unfold C_X CXQ
  push_cast
  gcongr

theorem CTQ_ge (hP : P) : C_T n (M : ℝ) σK σB σT ≤ (CTQ n M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  have h2 := CXQ_ge hP
  have h3 := one_le_C_X hP
  have h4 : 1 ≤ (CXQ n M σK σB σT : ℝ) := h3.trans h2
  unfold C_T CTQ
  push_cast
  gcongr

theorem COmegaQ_ge (_hP : P) : C_Omega n τ (M : ℝ) σK σB σT ≤ (COmegaQ n τ M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  have h2 := cR_le_cRUpQ n τ
  have h3 := one_le_cR (n := n) (τ := (τ : ℝ))
  have h4 : 1 ≤ (cRUpQ n τ : ℝ) := h3.trans h2
  unfold C_Omega COmegaQ
  push_cast
  gcongr

theorem CsymQ_ge (hP : P) : C_sym n τ (M : ℝ) σK σB σT ≤ (CsymQ n τ M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  have h2 := COmegaQ_ge hP
  have h3 := one_le_C_Omega hP
  have h4 : 1 ≤ (COmegaQ n τ M σK σB σT : ℝ) := h3.trans h2
  unfold C_sym CsymQ
  push_cast
  gcongr

theorem CredQ_ge (M σK σB σT : ℚ) :
    C_red n (M : ℝ) σK σB σT ≤ (CredQ n M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  unfold C_red CredQ
  push_cast
  gcongr

theorem Cxi0Q_ge (hP : P) : C_xi0 n τ (M : ℝ) σK σB σT ≤ (Cxi0Q n τ M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  have h2 := cR_le_cRUpQ n τ
  have h3 := one_le_cR (n := n) (τ := (τ : ℝ))
  have h4 : 1 ≤ (cRUpQ n τ : ℝ) := h3.trans h2
  have h5 := ThetaQ_ge hP
  have h6 := one_le_Theta hP
  have h7 : 1 ≤ (ThetaQ n M σK σB σT : ℝ) := h6.trans h5
  have h8 := CTQ_ge hP
  have h9 := one_le_C_T hP
  have h10 : 1 ≤ (CTQ n M σK σB σT : ℝ) := h9.trans h8
  unfold C_xi0 Cxi0Q
  push_cast
  gcongr

theorem CGQ_ge (_hP : P) : C_G n (M : ℝ) σK σB σT ≤ (CGQ n M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  unfold C_G CGQ
  push_cast
  gcongr

theorem CBQ_ge (hP : P) : C_B n (M : ℝ) σK σB σT ≤ (CBQ n M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  have h2 := CGQ_ge hP
  have h3 := one_le_C_G hP
  have h4 : 1 ≤ (CGQ n M σK σB σT : ℝ) := h3.trans h2
  unfold C_B CBQ
  push_cast
  gcongr

theorem CDNQ_ge (hP : P) : C_DN n (M : ℝ) σK σB σT ≤ (CDNQ n M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  have h2 := CBQ_ge hP
  have h3 := one_le_C_B hP
  have h4 : 1 ≤ (CBQ n M σK σB σT : ℝ) := h3.trans h2
  unfold C_DN CDNQ
  push_cast
  gcongr

theorem CDXQ_ge (hP : P) : C_DX n (M : ℝ) σK σB σT ≤ (CDXQ n M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  have h5 := ThetaQ_ge hP
  have h6 := one_le_Theta hP
  have h7 : 1 ≤ (ThetaQ n M σK σB σT : ℝ) := h6.trans h5
  have h2 := CDNQ_ge hP
  have h3 := one_le_C_DN hP
  have h4 : 1 ≤ (CDNQ n M σK σB σT : ℝ) := h3.trans h2
  unfold C_DX CDXQ
  push_cast
  gcongr

theorem CDTQ_ge (hP : P) : C_DT n (M : ℝ) σK σB σT ≤ (CDTQ n M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  have h5 := CXQ_ge hP
  have h6 := one_le_C_X hP
  have h7 : 1 ≤ (CXQ n M σK σB σT : ℝ) := h6.trans h5
  have h2 := CDNQ_ge hP
  have h3 := one_le_C_DN hP
  have h4 : 1 ≤ (CDNQ n M σK σB σT : ℝ) := h3.trans h2
  have h8 := CDXQ_ge hP
  have h9 := one_le_C_DX hP
  have h10 : 1 ≤ (CDXQ n M σK σB σT : ℝ) := h9.trans h8
  unfold C_DT CDTQ
  push_cast
  gcongr

theorem CYQ_ge (hP : P) : CY n (M : ℝ) σK σB σT ≤ (CYQ n M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  have h2 := CDNQ_ge hP
  have h3 := one_le_C_DN hP
  have h4 : 1 ≤ (CDNQ n M σK σB σT : ℝ) := h3.trans h2
  unfold CY CYQ
  push_cast
  gcongr

theorem CDTbordQ_ge (hP : P) :
    CDTbord n (M : ℝ) σK σB σT ≤ (CDTbordQ n M σK σB σT : ℚ) := by
  have h0 := mSizeQ_ge M σK σB σT
  have h1 := one_le_mSize (M := (M : ℝ)) (σK := (σK : ℝ)) (σB := (σB : ℝ)) (σT := (σT : ℝ))
  have h0' : (1 : ℝ) ≤ mSizeQ M σK σB σT := h1.trans h0
  have h2 := CDTQ_ge hP
  have h3 := CYQ_ge hP
  unfold CDTbord CDTbordQ
  push_cast
  gcongr

end Compare

end KAM.Certificate
