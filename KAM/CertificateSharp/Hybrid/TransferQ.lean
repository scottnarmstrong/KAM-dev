/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.Hybrid.G1
import Mathlib.Tactic.Linarith

/-!
# The exact rational mirror of the frame transfer (package C8c)

The transfer numbers of the certified first step are rational functions of rational data (no `π`,
no exponential): `c_Th = 2M₁`, `c_DTh = 2M₂` and the bounds of the step. The checker evaluates them
exactly; the casts are equalities.

* `FrameQ`, `FrameQ.toNum` and the casts of `g`, `β₁`, `b`, `n_Δ`, `n_Δᵗ` (Lemma `bp:p2s2hc:frames`,
  `KAM.Sharp2.Hybrid.FrameNum`);
* `dABQ`, `cast_dAB` (`KAM.Sharp2.Hybrid.dAB`);
* `KDataQ`, `StepNumQ`, `IsoNumQ` and the casts of `e₁`, `λ₀`, `λ₁`, `t₁`, `t_A`, `σ_{K,1}`, `σ_{B,1}`,
  the transferred initial values, `e₁` (iso) and `t_A^ext` (C8b's `KData`, `StepNum`, `IsoNum`).
-/

@[expose] public section

namespace KAM.CertificateSharp.Hybrid

open KAM.Sharp2.Hybrid KAM.Iso.Sharp2.Hybrid

/-- The rational numbers of Lemma `bp:p2s2hc:frames`. -/
structure FrameQ where
  ℓ : ℚ
  ℓt : ℚ
  β : ℚ
  ν : ℚ
  νt : ℚ
  d1 : ℚ
  d1t : ℚ

namespace FrameQ

variable (F : FrameQ)

/-- The real numbers. -/
noncomputable def toNum : FrameNum := ⟨F.ℓ, F.ℓt, F.β, F.ν, F.νt, F.d1, F.d1t⟩

def g : ℚ := F.ℓt * F.d1 + F.d1t * F.ℓ + F.d1t * F.d1
def β1 : ℚ := F.β / (1 - F.β * F.g)
def b : ℚ := F.β ^ 2 * F.g / (1 - F.β * F.g)
def nΔ : ℚ := F.β1 * F.d1 + F.ℓ * F.b
def nΔt : ℚ := F.β1 * F.d1t + F.ℓt * F.b

@[simp] theorem toNum_ℓ : F.toNum.ℓ = (F.ℓ : ℝ) := rfl
@[simp] theorem toNum_ℓt : F.toNum.ℓt = (F.ℓt : ℝ) := rfl
@[simp] theorem toNum_β : F.toNum.β = (F.β : ℝ) := rfl
@[simp] theorem toNum_ν : F.toNum.ν = (F.ν : ℝ) := rfl
@[simp] theorem toNum_νt : F.toNum.νt = (F.νt : ℝ) := rfl
@[simp] theorem toNum_d1 : F.toNum.d1 = (F.d1 : ℝ) := rfl
@[simp] theorem toNum_d1t : F.toNum.d1t = (F.d1t : ℝ) := rfl

theorem cast_g : F.toNum.g = (F.g : ℝ) := by
  simp only [FrameNum.g, g, toNum]; push_cast; ring
theorem cast_β1 : F.toNum.β1 = (F.β1 : ℝ) := by
  simp only [FrameNum.β1, β1, cast_g]; simp only [toNum]; push_cast; ring
theorem cast_b : F.toNum.b = (F.b : ℝ) := by
  simp only [FrameNum.b, b, cast_g]; simp only [toNum]; push_cast; ring
theorem cast_nΔ : F.toNum.nΔ = (F.nΔ : ℝ) := by
  simp only [FrameNum.nΔ, nΔ, cast_β1, cast_b]; simp only [toNum]; push_cast; ring
theorem cast_nΔt : F.toNum.nΔt = (F.nΔt : ℝ) := by
  simp only [FrameNum.nΔt, nΔt, cast_β1, cast_b]; simp only [toNum]; push_cast; ring

end FrameQ

/-- `Δ_ab` over `ℚ`. -/
def dABQ (F : FrameQ) (cTh cDTh d : ℚ) : ℚ :=
  F.nΔt * cTh * (F.ν + F.nΔ) + F.νt * (cDTh * d) * (F.ν + F.nΔ) + F.νt * cTh * F.nΔ

theorem cast_dAB (F : FrameQ) (cTh cDTh d : ℚ) :
    dAB F.toNum cTh cDTh d = (dABQ F cTh cDTh d : ℝ) := by
  simp only [dAB, dABQ, FrameQ.cast_nΔ, FrameQ.cast_nΔt]
  simp only [FrameQ.toNum]
  push_cast
  ring

/-- The rational certified data of `K`. -/
structure KDataQ where
  ℓ : ℚ
  ℓt : ℚ
  β : ℚ
  ν : ℚ
  νt : ℚ
  t : ℚ
  m : ℚ

/-- The real data. -/
noncomputable def KDataQ.toK (k : KDataQ) : KData := ⟨k.ℓ, k.ℓt, k.β, k.ν, k.νt, k.t, k.m⟩

/-- The rational step bounds. -/
structure StepNumQ where
  d0 : ℚ
  dinf : ℚ
  d1 : ℚ
  d1t : ℚ
  d0R : ℚ
  d1R : ℚ
  d1tR : ℚ
  lE : ℚ
  dE0 : ℚ
  o0 : ℚ
  dE0R : ℚ
  o0R : ℚ
  o1 : ℚ
  o1R : ℚ

namespace StepNumQ

variable (b : StepNumQ) (k : KDataQ)

/-- The real numbers. -/
noncomputable def toNum : StepNum :=
  ⟨b.d0, b.dinf, b.d1, b.d1t, b.d0R, b.d1R, b.d1tR, b.lE, b.dE0, b.o0, b.dE0R, b.o0R, b.o1, b.o1R⟩

def e1 (M2 : ℚ) : ℚ := b.lE + M2 / 2 * b.d0 ^ 2
def frS : FrameQ := ⟨k.ℓ, k.ℓt, k.β, k.ν, k.νt, b.d1, b.d1t⟩
def frR : FrameQ := ⟨k.ℓ, k.ℓt, k.β, k.ν, k.νt, b.d1R, b.d1tR⟩
def wB (nn M1 ℓ ℓt dE : ℚ) : ℚ := ℓt * (4 * nn * M1) * ℓ + dE * (2 * nn * ℓ + ℓt)
def lam0 (nn M1 : ℚ) (real : Bool) : ℚ :=
  let dE := if real then b.dE0R else b.dE0
  let o := if real then b.o0R else b.o0
  k.νt * k.β * dE + k.β ^ 3 * wB nn M1 k.ℓ k.ℓt dE * o
def lam1 (nn M1 M2 δ : ℚ) (real : Bool) : ℚ :=
  let F := if real then b.frR k else b.frS k
  let dE := nn * δ⁻¹ * b.e1 M2
  let o := if real then b.o1R else b.o1
  (F.νt + F.nΔt) * F.β1 * dE + F.β1 ^ 3 * wB nn M1 (F.ℓ + F.d1) (F.ℓt + F.d1t) dE * o
def t1 (nn M1 M2 δ cTh : ℚ) : ℚ :=
  min (k.t + dABQ (b.frS k) cTh (2 * M2) b.d0 + b.lam0 k nn M1 false)
      (((b.frS k).νt + (b.frS k).nΔt) * cTh * ((b.frS k).ν + (b.frS k).nΔ)) +
    b.lam1 k nn M1 M2 δ false
def tA (nn M1 M2 δ cTh : ℚ) : ℚ :=
  dABQ (b.frR k) cTh (2 * M2) b.d0R + b.lam0 k nn M1 true + b.lam1 k nn M1 M2 δ true
def sK1 (μ₁ : ℚ) : ℚ := k.ℓ + b.d1 + μ₁
def sB1 (μ₁ : ℚ) : ℚ := (b.frS k).β1 + μ₁

theorem frS_toNum : b.toNum.frS k.toK = (b.frS k).toNum := rfl
theorem frR_toNum : b.toNum.frR k.toK = (b.frR k).toNum := rfl

theorem cast_e1 (M2 : ℚ) : b.toNum.e1 M2 = (b.e1 M2 : ℝ) := by
  simp only [StepNum.e1, e1, toNum]; push_cast; ring

theorem cast_lam0 (nn M1 : ℚ) (real : Bool) :
    b.toNum.lam0 k.toK nn M1 real = (b.lam0 k nn M1 real : ℝ) := by
  cases real <;> simp only [StepNum.lam0, lam0, StepNum.wB, wB, toNum, KDataQ.toK] <;>
    push_cast <;> ring

theorem cast_lam1 (nn M1 M2 δ : ℚ) (real : Bool) :
    b.toNum.lam1 k.toK nn M1 M2 δ real = (b.lam1 k nn M1 M2 δ real : ℝ) := by
  cases real
  · simp only [StepNum.lam1, lam1, Bool.false_eq_true, ite_false, frS_toNum, StepNum.wB, wB,
      cast_e1, FrameQ.cast_nΔt, FrameQ.cast_β1, FrameQ.toNum_ℓ, FrameQ.toNum_ℓt, FrameQ.toNum_νt,
      FrameQ.toNum_d1, FrameQ.toNum_d1t]
    have h1 : b.toNum.o1 = (b.o1 : ℝ) := rfl
    rw [h1]; push_cast; ring
  · simp only [StepNum.lam1, lam1, ite_true, frR_toNum, StepNum.wB, wB, cast_e1,
      FrameQ.cast_nΔt, FrameQ.cast_β1, FrameQ.toNum_ℓ, FrameQ.toNum_ℓt, FrameQ.toNum_νt,
      FrameQ.toNum_d1, FrameQ.toNum_d1t]
    have h1 : b.toNum.o1R = (b.o1R : ℝ) := rfl
    rw [h1]; push_cast; ring

theorem cast_t1 (nn M1 M2 δ cTh : ℚ) :
    b.toNum.t1 k.toK nn M1 M2 δ cTh = (b.t1 k nn M1 M2 δ cTh : ℝ) := by
  have e2 : (2 : ℝ) * (M2 : ℝ) = ((2 * M2 : ℚ) : ℝ) := by push_cast; ring
  have hd : b.toNum.d0 = (b.d0 : ℝ) := rfl
  have hk : k.toK.t = (k.t : ℝ) := rfl
  simp only [StepNum.t1, t1, frS_toNum, cast_lam0, cast_lam1, e2, hd, hk, cast_dAB,
    FrameQ.cast_nΔt, FrameQ.cast_nΔ, FrameQ.toNum_ν, FrameQ.toNum_νt]
  push_cast
  ring_nf

theorem cast_tA (nn M1 M2 δ cTh : ℚ) :
    b.toNum.tA k.toK nn M1 M2 δ cTh = (b.tA k nn M1 M2 δ cTh : ℝ) := by
  have e2 : (2 : ℝ) * (M2 : ℝ) = ((2 * M2 : ℚ) : ℝ) := by push_cast; ring
  have hd : b.toNum.d0R = (b.d0R : ℝ) := rfl
  simp only [StepNum.tA, tA, frR_toNum, cast_lam0, cast_lam1, e2, hd, cast_dAB]
  push_cast
  ring

theorem cast_sK1 (μ₁ : ℚ) : b.toNum.sK1 k.toK μ₁ = (b.sK1 k μ₁ : ℝ) := by
  simp only [StepNum.sK1, sK1, toNum, KDataQ.toK]; push_cast; ring

theorem cast_sB1 (μ₁ : ℚ) : b.toNum.sB1 k.toK μ₁ = (b.sB1 k μ₁ : ℝ) := by
  simp only [StepNum.sB1, sB1, frS_toNum, FrameQ.cast_β1]; push_cast; ring

theorem cast_init1 (nn M1 M2 δ cTh : ℚ) :
    b.toNum.init1 k.toK nn M1 M2 δ cTh = ⟨((k.ℓt + b.d1t : ℚ) : ℝ), ((k.ν + (b.frS k).nΔ : ℚ) : ℝ),
      ((k.νt + (b.frS k).nΔt : ℚ) : ℝ), ((b.t1 k nn M1 M2 δ cTh : ℚ) : ℝ)⟩ := by
  simp only [StepNum.init1, frS_toNum, FrameQ.cast_nΔ, FrameQ.cast_nΔt, cast_t1]
  simp only [toNum, KDataQ.toK]
  push_cast
  rfl

end StepNumQ

/-- The rational isoenergetic numbers. -/
structure IsoNumQ where
  lH : ℚ
  dω : ℚ
  Mh1 : ℚ
  Mh2 : ℚ

namespace IsoNumQ

variable (q : IsoNumQ) (b : StepNumQ) (k : KDataQ)

/-- The real numbers. -/
noncomputable def toNum : IsoNum := ⟨q.lH, q.dω, q.Mh1, q.Mh2⟩

def e1 (M2 : ℚ) : ℚ := max (b.e1 M2) (q.lH + q.Mh2 / 2 * b.d0R ^ 2)
def tAext (nn M1 M2 δ cTh : ℚ) : ℚ :=
  max (b.tA k nn M1 M2 δ cTh + q.dω)
    (nn * (q.Mh1 * (b.frR k).nΔt + q.Mh2 * b.d0R * (k.νt + (b.frR k).nΔt)))

theorem cast_e1 (M2 : ℚ) : q.toNum.e1 b.toNum M2 = (q.e1 b M2 : ℝ) := by
  simp only [IsoNum.e1, e1, StepNumQ.cast_e1]; simp only [toNum, StepNumQ.toNum]; push_cast; ring

theorem cast_tAext (nn M1 M2 δ cTh : ℚ) :
    q.toNum.tAext b.toNum k.toK nn M1 M2 δ cTh = (q.tAext b k nn M1 M2 δ cTh : ℝ) := by
  simp only [IsoNum.tAext, tAext, StepNumQ.cast_tA, StepNumQ.frR_toNum, FrameQ.cast_nΔt]
  simp only [toNum, StepNumQ.toNum, KDataQ.toK]
  push_cast
  ring_nf

end IsoNumQ

end KAM.CertificateSharp.Hybrid

end
