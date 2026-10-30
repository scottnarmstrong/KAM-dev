# Track SO: freeze proposal LOCK, the Moon stays locked forever (for owner review)

**Status: PROPOSAL ONLY. Nothing is frozen.** No file under `KAM/Frozen/`, `manifest/` or `KAM/Provider/` is created
or changed. Revision 3 (after design audits 1 and 2, see design §§9–10). Prepared 2026-10-30 by DESIGN-LOCK on `inp-lockdesign`. Design: [`SO-LOCK-DESIGN.md`](SO-LOCK-DESIGN.md).
Elaborated text: `.drafts/design/SOLockSignatures.lean` (only `sorry` warnings). Header, directory
(`KAM/Frozen/SpinOrbit/{Defs,Theorems}/`), namespace and manifest shape as in [`FREEZE-PROPOSAL-2.md`](../FREEZE-PROPOSAL-2.md).

## 0. Summary of recommendations
1. Freeze **three definitions** (`IsSyncOrbit`, `lunarSyncOrbit`, `libAction`) plus the literal `lunarOmega`, on top
   of the already-approved SO definitions (`soField`, `soV`, …; D40).
2. Freeze **four theorems**: `lunarSyncOrbit_spec`, `lunarSyncOrbit_unique` (these make the name ψ* canonical),
   `lunarSyncOrbit_bound` (location of ψ*), and the headline `lunar_sync_lock`.
3. Literals: `17/10⁶`, `27/200000` are the targets of the intended (not yet proved) contraction route with exact rational
   majorants (design §1.4, no data; the rational inequalities were checked by audit 2). `8/65`, `129/10000`,
   `21/100`, `26/1000` come from LOCK-GEN-1 (P ∈ [0.013238, 0.016258]) by the rules of design §1.4 and are
   **provisional** until the N = 65 certificate passes the kernel (as D40 did for the band).
4. Nothing about the certifier, polar coordinates, Ω-annulus, Fourier data or `HamExpr.sqrt` appears in any frozen text.

## 1. Candidate anchors (exact Lean text)

### 1.1 Definitions
```lean
/-- `ψ` is a synchronous periodic orbit: `q = φ + ψ(φ)`, `p = 1 + ψ'(φ)` solves `soField`;
`ψ` is `C²`, one-periodic and odd. -/
def IsSyncOrbit (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 ψ ∧ Function.Periodic ψ 1 ∧ (∀ φ, ψ (-φ) = -ψ φ) ∧
    ∀ φ, deriv (deriv ψ) φ = (soField (φ + ψ φ, 1 + deriv ψ φ, φ)).2.1

open Classical in
/-- The synchronous periodic orbit ψ* (unique by `lunarSyncOrbit_unique`). -/
def lunarSyncOrbit : ℝ → ℝ :=
  if h : ∃ ψ, IsSyncOrbit ψ then Classical.choose h else 0

/-- The elliptic libration action around a curve `ψ`. -/
def libAction (Ω : ℝ) (ψ : ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  π * (Ω * (x.1 - x.2.2 - ψ x.2.2) ^ 2 + (x.2.1 - 1 - deriv ψ x.2.2) ^ 2 / Ω)

def lunarOmega : ℚ := 8 / 65
```
(The signatures file writes the orbit equation as `-soVq (φ + ψ φ) φ`; for the freeze the `soField` form above is
recommended so only definitions approved for freezing (D40; not yet frozen) occur — Q2. Both are equal by the landed `soField_eq`.)

### 1.2 Theorems
```lean
theorem lunarSyncOrbit_spec : IsSyncOrbit lunarSyncOrbit
theorem lunarSyncOrbit_unique (ψ : ℝ → ℝ) (h : IsSyncOrbit ψ) : ψ = lunarSyncOrbit
theorem lunarSyncOrbit_bound (φ : ℝ) :
    |lunarSyncOrbit φ| ≤ 17 / 1000000 ∧ |deriv lunarSyncOrbit φ| ≤ 27 / 200000

/-- The Moon stays locked in synchronous rotation forever. -/
theorem lunar_sync_lock (q₀ p₀ φ₀ : ℝ)
    (h₀ : libAction lunarOmega lunarSyncOrbit (q₀, p₀, φ₀) < 129 / 10000) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ 21 / 100 ∧
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ 26 / 1000 ∧
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z
```
Reading: every initial state whose libration action around ψ* is below 0.0129 (libration up to ≈ 66° when the spin
is on ψ*; the tube is an ellipse in (ψ, p)) moves for all time within 0.21 turn (75.6°) of ψ* in angle and within
2.6 % of ψ*'s spin, and never reaches the separatrix (|ψ| = 1/4). ψ* is the unique **odd** synchronous orbit;
ψ* + 1/2 (the other orientation) is also an orbit, by symmetry.

## 2. Questions for the owner (recommended answers)
- **Q1** Characterise ψ* globally as the unique odd one-periodic synchronous orbit (no data in the statement)? **Yes.**
- **Q2** Write the orbit equation via `soField` (approved for freezing in D40) (not landed `soVq`)? **Yes.**
- **Q3** Accept the ellipse spin bound 2.6 % (true torus max ≈ 2.51 % with Ω = 8/65)? **Yes.**
- **Q4** Drop the trivially-true non-vacuity theorem (the tube contains ψ* itself)? **Drop.**
- **Q5** Freeze `lunarSyncOrbit_bound` (location; independent of the torus certificate)? **Yes** — it is the
  physical "forced libration ≈ 15″" content and pins ψ* numerically.
- **Q6** Literal rules of design §1.4, fixed from the final kernel-passed data? **Approve rules now.**
- **Q7** Keep the rational LOCK-GEN centre c for the coordinates (not in any frozen text) while the headline is
  stated around ψ*? **Yes** (transfer costs 0.6 % of √I).
- **Q8** (sub-orchestrator ruling, overnight) Accept replacing the unfrozen landed helper
  `HamExpr.nonvanishingOn_of_inv_good` by `HamExpr.nonvanishingOn_of_program_good` (extra `SlpSqrtGood` premise),
  the one landed statement change of LOCK-SQRT (design §4.2)? **Yes.**
