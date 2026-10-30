/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Barrier
public import KAM.SpinOrbit.Graph.Cert
public import KAM.CertificateSharp.V2.RouteARefinedEngine
public import KAM.Certificate.Model.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# SO-LOCK: candidate signatures (design draft, NOT a KAM module, nothing frozen)

Statements of "the Moon stays locked in synchronous rotation forever" (D42, D45, route (a′), L1),
in the landed physical model `soField` (approved for freezing in D40, not yet frozen) on `(q, p, φ)` (period-one units). The libration angle is
`ψ = q − φ`. All proofs are `sorry`. Literals: from LOCK-GEN-1 numbers by the rules of design §1.4
(provisional until the N = 65 certificate passes the kernel).
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

/-- Location of ψ* (forced libration ≈ 15.5″). Intended proof route (not yet proved) from rational majorants: the contraction
around 0 gives `|ψ*| ≤ η/(32 − L)`, `|ψ*′| ≤ (η + L|ψ*|)/4` with `η ≤ 4πεΣ_{m≠2}|A_m|`,
`L ≤ 16π²εΣ|A_m|` (design §2.1, §1.4). -/
theorem lunarSyncOrbit_bound (φ : ℝ) :
    |lunarSyncOrbit φ| ≤ 17 / 1000000 ∧ |deriv lunarSyncOrbit φ| ≤ 27 / 200000 := sorry

/-! ## 2. The libration tube around ψ* -/

/-- The elliptic libration action around a curve `ψ`: `π(Ω X² + Y²/Ω)` with
`X = q − φ − ψ(φ)`, `Y = p − 1 − ψ'(φ)`. -/
def libAction (Ω : ℝ) (ψ : ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  π * (Ω * (x.1 - x.2.2 - ψ x.2.2) ^ 2 + (x.2.1 - 1 - deriv ψ x.2.2) ^ 2 / Ω)

/-- `Ω` for the lunar tube (LOCK-GEN: the roundest elliptic polar coordinates at N = 65). -/
def lunarOmega : ℚ := 8 / 65

/-! ## 3. The headline theorem -/

/-- **The Moon stays locked in synchronous rotation forever.** Every initial state whose libration
action around the certified periodic orbit ψ* is below `129/10000` generates a unique global
solution of the physical model, which for all real times stays within libration angle `21/100`
turn and spin deviation `26/1000` of ψ*; in particular `|q − φ| < 1/4`. -/
theorem lunar_sync_lock (q₀ p₀ φ₀ : ℝ)
    (h₀ : libAction lunarOmega lunarSyncOrbit (q₀, p₀, φ₀) < 129 / 10000) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ 21 / 100 ∧
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ 26 / 1000 ∧
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := sorry

/-- Non-vacuity: the tube contains ψ* itself (and the real Moon's forced libration). -/
theorem lunar_sync_lock_nonvacuous (φ₀ : ℝ) :
    libAction lunarOmega lunarSyncOrbit
      (φ₀ + lunarSyncOrbit φ₀, 1 + deriv lunarSyncOrbit φ₀, φ₀) < 129 / 10000 := sorry

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

/-! ## 5. The square-root primitive (LOCK-SQRT): total, real-preserving semantics -/

/-- Semantics of the new `HamExpr.sqrt a` node, total like Lean's `0⁻¹ = 0`: `0` on the
nonpositive real axis, the principal root elsewhere. Maps reals to reals. -/
def sqrtE (z : ℂ) : ℂ := if z.im = 0 ∧ z.re ≤ 0 then 0 else z ^ (1 / 2 : ℂ)

/-- New proof case of the landed `HamExpr.exists_real_eval` (statement unchanged). -/
theorem sqrtE_ofReal (x : ℝ) : ∃ r : ℝ, sqrtE (x : ℂ) = (r : ℂ) := sorry

/-- Holomorphy on the slit plane, in particular on the certified region `0 < re`. -/
theorem differentiableAt_sqrtE {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ sqrtE z := sorry

theorem sqrtE_sq {z : ℂ} (hz : z ∈ Complex.slitPlane) : sqrtE z ^ 2 = z := sorry

theorem sqrtE_re_nonneg (z : ℂ) : 0 ≤ (sqrtE z).re := sorry

/-- Derivative rule used by the differentiation layer (`d√f = f′/(2√f)`). -/
theorem hasDerivAt_sqrtE {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt sqrtE (1 / (2 * sqrtE z)) z := sorry

/-- Ball rule (before outward rounding): `|z − s²| ≤ r < s²`, `s > 0` ⇒ `0 < re z` and
`|√z − s| ≤ r/s`. The `SlpOp.sqrt` ball step checks `r < s²` (the analogue of the `inv` test). -/
theorem sqrtE_ball {z : ℂ} {s r : ℝ} (hs : 0 < s) (hr : r < s ^ 2)
    (h : ‖z - (s : ℂ) ^ 2‖ ≤ r) : 0 < z.re ∧ ‖sqrtE z - s‖ ≤ r / s := sorry

/-- Pointwise model rule with a positive real anchor (audit F2): `‖W − s‖ ≤ d < s` puts `W` in the
right half-plane, so `|√f + W| ≥ s − d` without knowing the error. -/
theorem sqrtE_model_error {f W : ℂ} {s d ε : ℝ} (hs : 0 < s) (hd : 0 ≤ d) (hds : d < s)
    (hf : 0 < f.re) (hW : ‖W - (s : ℂ)‖ ≤ d) (hres : ‖f - W ^ 2‖ ≤ ε) :
    ‖sqrtE f - W‖ ≤ ε / (s - d) := sorry

section Witness

open KAM.Certificate

/-- The composition witness for `√g` (analogue of `ExpWitness`): the model polynomial `W`, the
rational anchor `s > 0` and margin `d < s`. -/
structure SqrtWitness (α : Type) where
  poly : CertPoly α
  anchor : ℚ
  margin : ℚ

variable {α : Type} [CertArith α]

/-- The checker (body: LOCK-SQRT): checks `0 ≤ d < s`, encloses `‖W − s‖ ≤ d` and
`‖g − W²‖ ≤ ε` on the strip (outward-rounded model arithmetic), checks `Re g > 0` on the strip
via `‖g − s²‖`-type bound, and returns the radius `ε/(s − d)` rounded up. -/
def sqrtWitnessRadius (n : ℕ) (W : CertWeight) (cfg : ModelConfig α) (g : CertModel α)
    (S : SqrtWitness α) : Option α := sorry

theorem sqrtWitness_sound [LawfulCertArith α] {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    {g : CertModel α} {gf : (Fin n → ℂ) → ℂ} (hg : g.Encloses n W.rho gf) (hdeg : g.deg = 0)
    {S : SqrtWitness α} {r : α} (hS : sqrtWitnessRadius n W cfg g S = some r) :
    (∀ θ ∈ complexStrip n W.rho, 0 < (gf θ).re) ∧
      (⟨0, S.poly, r⟩ : CertModel α).Encloses n W.rho (fun θ => sqrtE (gf θ)) := sorry

end Witness

/-! ## 6. Coordinates (LOCK-COORDS): exact maps, audit F3 -/

/-- Real polar pieces: `X = √(I/(πΩ)) sin 2πα`, `Y = √(IΩ/π) cos 2πα` on `z = ((α, φ), (I, J̃))`.
Two-form: `dY ∧ dX = dI ∧ dα` (frozen convention `Σ dIᵢ ∧ dθᵢ`). -/
def lockX (Ω : ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  Real.sqrt (z.2 0 / (π * Ω)) * Real.sin (2 * π * z.1 0)

def lockY (Ω : ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  Real.sqrt (z.2 0 * Ω / π) * Real.cos (2 * π * z.1 0)

/-- To the landed rotated frame `((Q₀, Q₁), (P₀, P₁))` (`soRotMap` then goes to physical):
`Q₀ = c + X`, `Q₁ = φ`, `P₀ = 1 + c′ + Y`, `P₁ = J̃ − c′(c′ + Y) + X c″`. -/
def lockToRotR (Ω : ℝ) (c : ℝ → ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (![c (z.1 1) + lockX Ω z, z.1 1],
   ![1 + deriv c (z.1 1) + lockY Ω z,
     z.2 1 - deriv c (z.1 1) * (deriv c (z.1 1) + lockY Ω z) +
       lockX Ω z * deriv (deriv c) (z.1 1)])

/-- Physical projection `(q, p, φ)` (= `soRotMap ∘ lockToRotR` without the clock action). -/
def lockToPhysicalR (Ω : ℝ) (c : ℝ → ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ × ℝ × ℝ :=
  (z.1 1 + c (z.1 1) + lockX Ω z, 1 + deriv c (z.1 1) + lockY Ω z, z.1 1)

/-- `K = H′ ∘ lockToRotR`. -/
def lockHamiltonianR (Ω : ℝ) (c : ℝ → ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  z.2 1 + (lockY Ω z) ^ 2 / 2 - (deriv c (z.1 1)) ^ 2 / 2 +
    lockX Ω z * deriv (deriv c) (z.1 1) + soV (z.1 1 + c (z.1 1) + lockX Ω z) (z.1 1) - 1 / 2

theorem lockToPhysicalR_eq (Ω : ℝ) (c : ℝ → ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    lockToPhysicalR Ω c z =
      ((lockToRotR Ω c z).1 0 + (lockToRotR Ω c z).1 1, (lockToRotR Ω c z).2 0,
        (lockToRotR Ω c z).1 1) := sorry

/-- The action is the elliptic libration action of the image. -/
theorem libAction_lockToPhysicalR {Ω : ℝ} (hΩ : 0 < Ω) (c : ℝ → ℝ)
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 ≤ z.2 0) :
    libAction Ω c (lockToPhysicalR Ω c z) = z.2 0 := sorry

/-- The inverse on the punctured plane: every physical point off the centre curve is hit, with
action `libAction` and angle `arg(Y/√Ω + i√Ω X)/2π`. -/
theorem lockToPhysicalR_surj {Ω : ℝ} (hΩ : 0 < Ω) (c : ℝ → ℝ) (x : ℝ × ℝ × ℝ)
    (hx : 0 < libAction Ω c x) :
    lockToPhysicalR Ω c
      (![Complex.arg ((((x.2.1 - 1 - deriv c x.2.2) / √Ω : ℝ) : ℂ) +
          ((√Ω * (x.1 - x.2.2 - c x.2.2) : ℝ) : ℂ) * Complex.I) / (2 * π), x.2.2],
       ![libAction Ω c x, 0]) = x := sorry

/-- **Conjugacy** (real points, `I > 0`): `lockToPhysicalR` maps `X_K` to `soField`. -/
theorem lock_conjugacy {Ω : ℝ} (hΩ : 0 < Ω) (c : ℝ → ℝ) (hc : ContDiff ℝ 3 c)
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < z.2 0) :
    fderiv ℝ (lockToPhysicalR Ω c) z (KAM.hamiltonianVectorField (lockHamiltonianR Ω c) z) =
      soField (lockToPhysicalR Ω c z) := sorry

/-- The rational sine centre `c(φ) = Σ_k cs_k sin 2π(k+1)φ` and its explicit complexification. -/
def lockCentre (cs : List ℚ) (φ : ℝ) : ℝ :=
  ((List.range cs.length).map fun k =>
    ((cs.getD k 0 : ℚ) : ℝ) * Real.sin (2 * π * (k + 1) * φ)).sum

def lockCentreC (cs : List ℚ) (φ : ℂ) : ℂ :=
  ((List.range cs.length).map fun k =>
    ((cs.getD k 0 : ℚ) : ℂ) * Complex.sin (2 * π * (k + 1) * φ)).sum

def lockCentreDC (cs : List ℚ) (φ : ℂ) : ℂ :=
  ((List.range cs.length).map fun k =>
    ((cs.getD k 0 : ℚ) : ℂ) * (2 * π * (k + 1)) * Complex.cos (2 * π * (k + 1) * φ)).sum

def lockCentreDDC (cs : List ℚ) (φ : ℂ) : ℂ :=
  ((List.range cs.length).map fun k =>
    -((cs.getD k 0 : ℚ) : ℂ) * (2 * π * (k + 1)) ^ 2 * Complex.sin (2 * π * (k + 1) * φ)).sum

/-- LOCK-GEN-1 centre: `−3/250000 sin 2πφ − 699/2000000000 sin 4πφ − 883/50000000000 sin 6πφ`. -/
def lunarLockCentre : List ℚ := [-3 / 250000, -699 / 2000000000, -883 / 50000000000]

theorem lockCentre_contDiff (cs : List ℚ) : ContDiff ℝ ⊤ (lockCentre cs) := sorry

/-- Complexified map to the rotated frame (uses `sqrtE`; equals `lockToRotR` at real points with
`I > 0`). -/
def lockToRotC (Ω : ℚ) (cs : List ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  let X := sqrtE (z.2 0 / (π * (Ω : ℂ))) * Complex.sin (2 * π * z.1 0)
  let Y := sqrtE (z.2 0 * (Ω : ℂ) / π) * Complex.cos (2 * π * z.1 0)
  (![lockCentreC cs (z.1 1) + X, z.1 1],
   ![1 + lockCentreDC cs (z.1 1) + Y,
     z.2 1 - lockCentreDC cs (z.1 1) * (lockCentreDC cs (z.1 1) + Y) +
       X * lockCentreDDC cs (z.1 1)])

theorem lockToRotC_ofReal {Ω : ℚ} (hΩ : 0 < Ω) (cs : List ℚ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ))
    (hI : 0 < z.2 0) :
    lockToRotC Ω cs ((fun i => (z.1 i : ℂ)), (fun i => (z.2 i : ℂ))) =
      ((fun i => ((lockToRotR Ω (lockCentre cs) z).1 i : ℂ)),
        (fun i => ((lockToRotR Ω (lockCentre cs) z).2 i : ℂ))) := sorry

/-- The transformed Hamiltonian as an expression (body needs the `.sqrt` constructor; LOCK-COORDS
writes it after LOCK-SQRT). -/
def lockHamExpr (Ω : ℚ) (cs : List ℚ) : KAM.Certificate.HamExpr 2 := sorry

/-- Eval identity, for all `Ω` and all `z`: purely algebraic (total `sqrtE`, no `sqrtE² = z` used).
It carries no analyticity claim; analyticity needs `0 < Ω` and the certified region. -/
theorem lockHamExpr_eval (Ω : ℚ) (cs : List ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (lockHamExpr Ω cs).eval z = soRotHC (lockToRotC Ω cs z) := sorry

/-- Clock: `∂_{J̃} K ≡ 1` on the certified region. Needs `0 < Ω`: for `Ω < 0` both sqrt operands lie
on the cut at real `I > 0` and `eval` is discontinuous there (audit 2, finding 2). -/
theorem lockHamExpr_clock (Ω : ℚ) (hΩ : 0 < Ω) (cs : List ℚ)
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) (hz : 0 < (z.2 0).re) :
    fderiv ℂ (lockHamExpr Ω cs).eval z (KAM.Certificate.phaseBasis (.inr 1)) = 1 := sorry

/-! ## 7. Certificate → barrier → headline (LOCK-GRAPH, LOCK-ASSEMBLY) -/

section Cert

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- A lock certificate: a graph certificate (angle `.1 0 = α` monotone, action `.2 0 = I` in
`[pLo, pHi]`) for the time-scaled `κ · lockHamExpr Ω cs`. -/
structure LockGraphCert (α : Type) where
  graph : SoGraphCert α
  Ω : ℚ
  cs : List ℚ
  κ : ℚ

variable {α : Type} [CertArith α]

/-- LOCK-GRAPH: a passing v2 certificate gives the physical librational barrier. -/
theorem lockBarrier_of_certV2 [LawfulCertArith α] (g : LockGraphCert α) (hΩ : 0 < g.Ω)
    (hκ : 0 < g.κ) (hham : g.graph.base.ham = .mul (.const g.κ) (lockHamExpr g.Ω g.cs))
    (hlo : 0 < (g.graph.pLo : ℝ) - g.graph.base.params.disp)
    {w : routeAV2.Wit} (hc : checkTorusCertificateV2 routeAV2 g.graph.base w = true)
    (hg : checkSoGraph g.graph = true) {ωstar : Fin 2 → ℝ}
    (hω : FreqEncloses 2 g.graph.base.freqBox ωstar)
    (hdio : IsDiophantine (g.graph.base.params.γ : ℝ) (g.graph.base.params.tau : ℝ) ωstar) :
    Nonempty (LockBarrier (g.Ω : ℝ) (lockCentre g.cs)
      ((g.graph.pLo : ℝ) - g.graph.base.params.disp)
      ((g.graph.pHi : ℝ) + g.graph.base.params.disp)) := sorry

/-- The rational literal check of design §1.4 (body: exact ℚ arithmetic with rational majorants
of `π`, `√Ω`, `√·`): `I_in`, `Rψ`, `Rp` are compatible with the barrier range `[lo, hi]`, the
orbit bounds `r₀, r₁` (on `|ψ*|`, `|ψ*′|`) and the centre `cs`. -/
def lockLiteralCheck (Ω : ℚ) (cs : List ℚ) (lo hi r₀ r₁ Iin Rψ Rp : ℚ) : Bool := sorry

/-- LOCK-ASSEMBLY, over a lawful backend: the headline shape from a passing certificate. -/
theorem lunar_sync_lock_of_cert [LawfulCertArith α] (g : LockGraphCert α) (hΩ : 0 < g.Ω)
    (hκ : 0 < g.κ) (hham : g.graph.base.ham = .mul (.const g.κ) (lockHamExpr g.Ω g.cs))
    {w : routeAV2.Wit} (hc : checkTorusCertificateV2 routeAV2 g.graph.base w = true)
    (hg : checkSoGraph g.graph = true) {ωstar : Fin 2 → ℝ}
    (hω : FreqEncloses 2 g.graph.base.freqBox ωstar)
    (hdio : IsDiophantine (g.graph.base.params.γ : ℝ) (g.graph.base.params.tau : ℝ) ωstar)
    {lo hi Iin Rψ Rp : ℚ}
    (hlo : (lo : ℝ) ≤ (g.graph.pLo : ℝ) - g.graph.base.params.disp)
    (hhi : (g.graph.pHi : ℝ) + g.graph.base.params.disp ≤ hi)
    (hlit : lockLiteralCheck g.Ω g.cs lo hi (17 / 1000000) (27 / 200000) Iin Rψ Rp = true)
    (q₀ p₀ φ₀ : ℝ) (h₀ : libAction (g.Ω : ℝ) lunarSyncOrbit (q₀, p₀, φ₀) < Iin) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ Rψ ∧
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ Rp ∧
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := sorry

end Cert

end KAM.SpinOrbit.Lock

end
