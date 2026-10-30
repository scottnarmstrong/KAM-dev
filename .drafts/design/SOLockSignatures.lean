/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Barrier
public import KAM.CertificateSharp.V2.Engine
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# SO-LOCK: candidate signatures (design draft, NOT a KAM module, nothing frozen)

Statements of "the Moon stays locked in synchronous rotation forever" (D42, D45, route (a′), L1),
in the frozen physical model `soField` on `(q, p, φ)` (period-one units). The libration angle is
`ψ = q − φ`. All proofs are `sorry`; the numerical literals are PLACEHOLDERS (marked `-- DATA`) to
be fixed from the final LOCK-GEN data by the rules of the design doc §1.
-/

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit.Lock

/-! ## 1. The synchronous periodic orbit (meaning-carrying definitions) -/

/-- `ψ` is a synchronous periodic orbit of the physical model: `q(t) = φ(t) + ψ(φ(t))`,
`p(t) = 1 + ψ'(φ(t))`, `φ(t) = φ₀ + t` solves `soField`, i.e. `ψ'' = −∂_q V(φ + ψ, φ)`;
`ψ` is `C²`, one-periodic and odd (reversibility). -/
def IsSyncOrbit (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 ψ ∧ Function.Periodic ψ 1 ∧ (∀ φ, ψ (-φ) = -ψ φ) ∧
    ∀ φ, deriv (deriv ψ) φ = -soVq (φ + ψ φ) φ

open Classical in
/-- **The** synchronous periodic orbit ψ*, named explicitly (D45 addendum): the unique odd
one-periodic synchronous orbit (`lunarSyncOrbit_unique`; existence `lunarSyncOrbit_spec`). -/
def lunarSyncOrbit : ℝ → ℝ :=
  if h : ∃ ψ, IsSyncOrbit ψ then Classical.choose h else 0

/-- Existence (LOCK-PO, Banach contraction around an explicit rational centre). -/
theorem lunarSyncOrbit_spec : IsSyncOrbit lunarSyncOrbit := sorry

/-- Global uniqueness: every odd one-periodic synchronous orbit is ψ*. -/
theorem lunarSyncOrbit_unique (ψ : ℝ → ℝ) (h : IsSyncOrbit ψ) : ψ = lunarSyncOrbit := sorry

/-- Location of ψ* (forced libration ≈ 15.5″): explicit bounds on ψ* and ψ*′. -/
theorem lunarSyncOrbit_bound (φ : ℝ) :
    |lunarSyncOrbit φ| ≤ 13 / 1000000 ∧ |deriv lunarSyncOrbit φ| ≤ 1 / 10000 := sorry  -- DATA

/-! ## 2. The libration tube around ψ* -/

/-- The elliptic libration action around a curve `ψ`: `π(Ω X² + Y²/Ω)` with
`X = q − φ − ψ(φ)`, `Y = p − 1 − ψ'(φ)`. -/
def libAction (Ω : ℝ) (ψ : ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  π * (Ω * (x.1 - x.2.2 - ψ x.2.2) ^ 2 + (x.2.1 - 1 - deriv ψ x.2.2) ^ 2 / Ω)

/-- `Ω` for the lunar tube (≈ 2π ω₀, ω₀ = 0.0261687). -/
def lunarOmega : ℚ := 1644 / 10000  -- DATA

/-! ## 3. The headline theorem -/

/-- **The Moon stays locked in synchronous rotation forever.** Every initial state whose libration
action around the certified periodic orbit ψ* is below `11/1000` generates a unique global
solution of the physical model, which for all real times stays within libration angle `22/100`
turn and spin deviation `37/1000` of ψ*; in particular `|q − φ| < 1/4`. -/
theorem lunar_sync_lock (q₀ p₀ φ₀ : ℝ)
    (h₀ : libAction lunarOmega lunarSyncOrbit (q₀, p₀, φ₀) < 11 / 1000) :            -- DATA I_in
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ 22 / 100 ∧            -- DATA Rψ
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ 37 / 1000 ∧               -- DATA Rp
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := sorry

/-- Non-vacuity: the tube contains ψ* itself (and the real Moon's forced libration). -/
theorem lunar_sync_lock_nonvacuous (φ₀ : ℝ) :
    libAction lunarOmega lunarSyncOrbit
      (φ₀ + lunarSyncOrbit φ₀, 1 + deriv lunarSyncOrbit φ₀, φ₀) < 11 / 1000 := sorry

/-! ## 4. Parametric pieces (unfrozen helpers; hypotheses = conclusions of pending packages) -/

/-- A librational barrier: an invariant graph `I = P(α, φ)` of the polar action around a curve
`c`, transported to `soField`. `α` is the polar angle of `(√Ω X, Y/√Ω)` in turns. -/
structure LockBarrier (Ω : ℝ) (c : ℝ → ℝ) (Iin Iout : ℝ) where
  P : ℝ → ℝ → ℝ
  continuous : Continuous fun x : ℝ × ℝ => P x.1 x.2
  periodic_α : ∀ a φ, P (a + 1) φ = P a φ
  periodic_φ : ∀ a φ, P a (φ + 1) = P a φ
  invariant : KAM.ODE.IsInvariantSet soField Set.univ
    {x | 0 < libAction Ω c x ∧ libAction Ω c x =
      P (Complex.arg (((√Ω * (x.1 - x.2.2 - c x.2.2) : ℝ) : ℂ) * Complex.I +
          (((x.2.1 - 1 - deriv c x.2.2) / √Ω : ℝ) : ℂ)) / (2 * π)) x.2.2}
  lower : ∀ a φ, Iin ≤ P a φ
  upper : ∀ a φ, P a φ ≤ Iout
  pos : 0 < Iin

/-- LOCK-CONF: a librational barrier confines (solid torus, `gen_barrier`). -/
theorem lock_confinement {Ω Iin Iout : ℝ} {c : ℝ → ℝ} (hΩ : 0 < Ω) (hc : ContDiff ℝ 2 c)
    (B : LockBarrier Ω c Iin Iout) (x₀ : ℝ × ℝ × ℝ) (h₀ : libAction Ω c x₀ < Iin) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = x₀ ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, libAction Ω c (z t) < Iout) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = x₀ ∧ ∀ t, HasDerivAt y (soField (y t)) t) → y = z := sorry

/-- LOCK-CONF corollary: the action bound gives the coordinate bounds. -/
theorem abs_le_of_libAction_lt {Ω I : ℝ} {c : ℝ → ℝ} (hΩ : 0 < Ω) {x : ℝ × ℝ × ℝ}
    (h : libAction Ω c x < I) :
    |x.1 - x.2.2 - c x.2.2| ≤ √(I / (π * Ω)) ∧ |x.2.1 - 1 - deriv c x.2.2| ≤ √(Ω * I / π) := sorry

/-- LOCK-ASSEMBLY transfer: change of centre from `c` to `ψ` (triangle inequality in the
`Ω`-norm): `√𝓘_c ≤ √𝓘_ψ + √π (√Ω r + r'/√Ω)` when `|ψ − c| ≤ r`, `|ψ' − c'| ≤ r'`. -/
theorem sqrt_libAction_le {Ω r r' : ℝ} (hΩ : 0 < Ω) {c ψ : ℝ → ℝ}
    (hr : ∀ φ, |ψ φ - c φ| ≤ r) (hr' : ∀ φ, |deriv ψ φ - deriv c φ| ≤ r') (x : ℝ × ℝ × ℝ) :
    √(libAction Ω c x) ≤ √(libAction Ω ψ x) + √π * (√Ω * r + r' / √Ω) := sorry

/-! ## 5. The square-root primitive: semantics (LOCK-SQRT) -/

/-- Semantics of the new `HamExpr.sqrt a` node: the principal branch `w ^ (1/2)`. -/
def sqrtSem (w : ℂ) : ℂ := w ^ (1 / 2 : ℂ)

/-- Holomorphy off the slit; the checker certifies `0 < Re w` on the domain. -/
theorem differentiableAt_sqrtSem {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ sqrtSem w := sorry

theorem sqrtSem_sq (w : ℂ) : sqrtSem w ^ 2 = w := sorry

/-- The ball rule: if `|w − s²| ≤ r < s²` with `s > 0` rational, then
`|√w − s| ≤ r / s` (from `√w − s = (w − s²)/(√w + s)`, `Re √w ≥ 0`). -/
theorem sqrtSem_ball {w : ℂ} {s r : ℝ} (hs : 0 < s) (hr : r < s ^ 2)
    (h : ‖w - (s : ℂ) ^ 2‖ ≤ r) : ‖sqrtSem w - s‖ ≤ r / s := sorry

end KAM.SpinOrbit.Lock

end
