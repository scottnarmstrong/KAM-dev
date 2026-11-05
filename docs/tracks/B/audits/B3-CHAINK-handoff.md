# Handoff B3-CHAINK (branch inp-b3chaink)

## Files (all under KAM/EffectiveStability/)
Changed (generalized over `K` with `[CertCoeff K]`): `OscillatorStep{,/Remainder,/Drift}`,
`OscillatorChain{,/Basic,/Remainder,/Domain,/Drift}`, `OscillatorCheck`, `OscillatorChainCheck`,
`OscillatorPhysical`, `OscillatorChainPhysical` (now holds the shared core + the old theorem).
New: `OscillatorChainPhysicalDisc.lean` (disc theorem), `OscillatorChainPhysicalDiscSmoke.lean`,
`OscillatorQSqrt2Smoke.lean` (QSqrt2 one-step kernel check). Smokes `OscillatorStep/Smoke`,
`OscillatorChain/Smoke`, `OscillatorPhysicalSmoke`, `OscillatorChainPhysicalSmoke` are textually unchanged.
Largest file 307 lines. New modules need root regeneration (`KAM.lean` out of date: expected lint line).

## Approach (Part 1)
Followed B3-COEF: generic `…K` structure, old name an `abbrev` at ℚ:
`structure OscStepK (K : Type)` (gen/out : `CartPolyK K`; ρ δ ε order stay ℚ/ℕ), `abbrev OscStep := OscStepK ℚ`;
`OscStepCertK K n` / `abbrev OscStepCert n`; `OscChainCertK K n` / `abbrev OscChainCert n`.
All other names unchanged and now generic in `K` (`OscStepOK, OscLieOK, OscChainOK, OscDomOK, oscTail,
oscChainBound, oscChainTheta/Rem/Dom, oscChainMap/Inv, stepChart(Inv), stepRem, checkOscStep, checkOscChain,
oscStepOKB, oscChainOKB, oscDomOKB, cartFitsB`, soundness and confinement/physical theorems).
Instances: pure data (`OscStepK`, `oscTail`, `oscChainBound`, `OscStepOK`, `OscLieOK`, `OscChainOK`, `OscDomOK`,
`check*`, `*B`) need only `[CertCoeff K]`; defs over ℂ (`stepChart`, `stepRem`, `oscStepFlow`, `oscChainMap`, …) only
`[Algebra K ℂ]`; the theorems take the minimal subset of `[Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ]
[CertNormLe K ℝ] [CertNormLe K ℂ]` (enforced by the unused-section-variable linter via `omit … in`; no warnings).
Soundness theorems `checkOscStep_sound`/`checkOscChain_sound` take all five. Radii/ε/δ/bounds stay ℚ.
At K = ℚ every old statement is the instance (abbrevs unify; all four ℚ smokes and their `decide +kernel` unchanged).

Key signatures:
```
structure OscStepK (K : Type) where gen out : CartPolyK K; order : ℕ; ρ δ ε : ℚ
def OscChainOK (n) (Nact P : CartPolyK K) : List (OscStepK K) → CartPolyK K → Prop
def checkOscStep {K} [CertCoeff K] {n} (c : OscStepCertK K n) : Bool
theorem checkOscStep_sound {K} [CertCoeff K] {n} [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ]
  [CertNormLe K ℝ] [CertNormLe K ℂ] (c : OscStepCertK K n) (hc : checkOscStep c = true) (w₀) (hw₀) : …  (conclusion verbatim)
```
## Part 2 (OD-B18)
`oscillatorChain_physical` was split: `oscillatorChain_physical_core` (all premises of the physical theorem except
`hs3`, plus `hchart : ∀ w, (∀ i, |w.1 i - z₀.1 i| ≤ tail ∧ |w.2 i - z₀.2 i| ≤ tail) → ∀ j, oscillatorAction w.2 w.1 j ≤ a j`,
placed after `hz₀`); `oscillatorChain_physical` (statement UNCHANGED) is now a short wrapper proving `hchart` from the coordinate box.
`oscillatorChain_physical_disc` (new file) has the physical premises with `hs1, hs3` replaced by
`σ hσ0 hσ1 : a' i ≤ σ i ^ 2, hsσ : 2 σ² ≤ s², hs3' : (σ i + oscTail l)^2 ≤ a i` (hs0, hs2 kept; order:
`a' s d hs0 σ hσ0 hσ1 hsσ hs2 hs3' hd z₀ hz₀`), conclusion verbatim. Plane lemma `discPlane_sq_le`
(Cauchy–Schwarz, no sqrt): `q²+p² ≤ 2σ²`, `|dq|,|dp| ≤ e` ⇒ `(q+dq)²+(p+dp)² ≤ 2(σ+e)²`; `oscTail_nonneg_of` gives `e ≥ 0`.
Smoke `OscillatorChainPhysicalDiscSmoke`: `discSmoke_numbers` (a'=σ²=(1/12500)², tail ≤ 74/10⁹ ⇒ `(σ+tail)² ≤ (81/10⁶)²`, `norm_num`;
needs `0 ≤ tail`) and `discSmoke_zeroDrift` (two zero generators, harmonic oscillator, the disc theorem applied).

## QSqrt2 smoke
`OscillatorQSqrt2Smoke`: n = 2, H = I₀ − (√2/2)I₁ + (1/1000)(q₀²q₁ − q₁³/3), χ = 0, Nact = q₀ − (√2/2)q₁, P = cubic, L = 1:
`hhStepCert_check : checkOscStep hhStepCert = true := by decide +kernel`; `hhStepCert_drift` applies `checkOscStep_sound` over QSqrt2.
Kernel type checking 92 ms. ℚ timing: `harmonicChainCert_check` 173 ms new vs 187 ms old (b3coef tree): no slowdown.

## Checks
- Builds (b_build.sh, one module per call, no warnings): all 20 Oscillator modules above + the three new ones; and every module that
  imports one of them (15, unchanged, all build): TorusStep.Drift, TorusChain.{Basic,Remainder,Domain,Drift,Smoke}, TorusChain,
  TorusStep, TorusStep.Smoke, TorusCheck, TorusChainCheck, TorusPhysical, TorusChainPhysical, TorusChainPhysicalSmoke, TorusPhysicalSmoke.
- `scripts/lint_sources.sh`: all PASS except the expected `KAM.lean is out of date` line (new modules).
- Width check: `[]`. `main_shortname_check.py` (all 15 modules): "short-name check OK".
- No `set_option`, `sorry`, `axiom`, `native_decide` added.
- `#print axioms` (all `[propext, Classical.choice, Quot.sound]`): oscillatorStep_confinement, oscillatorChain_confinement,
  checkOscStep_sound, checkOscChain_sound, oscillatorChain_physical, oscillatorChain_physical_core, oscillatorChain_physical_disc,
  oscillatorStep_physical, discPlane_sq_le, discSmoke_numbers, discSmoke_zeroDrift, hhStepCert_check, hhStepCert_drift, harmonicCert_check.

## Notes / uncertainties
- `OscStepCert.Bmaj` is now `OscStepCertK.Bmaj` (dot notation `c.Bmaj` unchanged; the only explicit use was inside the file).
- New public names: `oscillatorChain_physical_core`, `oscillatorChain_physical_disc`, `discPlane_sq_le`, `hhStep*`, `discSmoke_*`.
- `oscillatorChain_physical_core` is an ordinary theorem whose `hchart` is a premise about the chart displacement (not a conclusion
  of the physical theorem); it is a helper, not a stand-in for a source result.
- No errata, no design signals (default heartbeats everywhere).

## AUDIT FOCUS (orchestrator)
Scope: `git diff inp-b3coef...HEAD` (B3-COEF itself was audited separately: B3-COEF-audit-1 PASS WITH NOTES).
1. ℚ preservation: every pre-existing statement in the 13 changed Oscillator* modules is, at K = ℚ, the old statement
   (abbrevs `OscStep := OscStepK ℚ` etc.); `oscillatorChain_physical`'s statement is textually unchanged.
2. Soundness over K: `checkOscStep_sound` / `checkOscChain_sound` conclusions verbatim; the instance set
   (`Algebra K ℝ/ℂ`, `IsScalarTower`, `CertNormLe K ℝ/ℂ`) cannot make a QSqrt2 checker pass with a wrong real meaning
   (e.g. a non-standard `Algebra QSqrt2 ℝ` instance); which instance does the QSqrt2 smoke actually use?
3. `oscillatorChain_physical_disc` (OD-B18): premises are only the physical ones with `hs1/hs3` replaced by the disc
   ones (`a' ≤ σ²`, `2σ² ≤ s²`, `(σ+tail)² ≤ a`); nothing conclusion-shaped; `oscillatorChain_physical_core`'s `hchart`
   is a genuine chart-displacement premise discharged by both wrappers; `discPlane_sq_le` correct.
4. Smokes: `decide +kernel` only; the QSqrt2 smoke's H is the intended HH-shaped polynomial.
