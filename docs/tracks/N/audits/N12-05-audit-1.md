# N12-05 independent package audit 1

Overall verdict: **PASS WITH NOTES** for N12-05, `bpN:p12:corrector`.
The rational calculus theorem and all eleven definitions satisfy the assigned design contract.
The notes concern the permitted stale generated root, totalized definitions outside the analytic
regime, and comparison ancestry. No blocking mathematical or implementation defect was found.

No frozen anchor is proved by this package. Provider/frozen type equality and seal-body probes
are **not applicable**: there is no provider export in scope. Neither `averaging_mean` nor
`averaging_most` is certified seal-ready by this report; their frozen bodies remain `sorry`.
Regularity, summability, envelope finiteness/measurability and derivative-series identities are
later package obligations, not conclusions of N12-05.

## Scope and authority

Audited worktree `/root/code/KAM-inp-n1205`, HEAD
`3ba47d7fddf71bbc57a60db8c0a092db44646d6f`.
Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, N12-05 handoff,
the N12 design (including row N12-05 and its proof plan), blueprint Part 12:99–110,
track-N statement conventions, relevant frozen averaging roots/definitions, and the two
DESIGN-N12 design audits. The design audits and standalone signatures are available under
`/root/code/KAM-inp`; the signatures appendix is also present in this worktree.
The user's explicit report destination overrides the generic brief's MAIN-worktree destination.

Comparisons performed:

- `git diff inp...HEAD`: Coefficients (336 lines) and Corrector (119 lines) are added.
  Git warns of multiple merge bases and selects `f390de8f741ebb8dab2d17ff12ec7f7e5b6d4f46`.
  The observed `inp` tip was `6e36995edb8c5fb4ee4ec0ed914f4a0c55a9b7f1`.
- `git diff inp-n1204...HEAD -- KAM/Nekhoroshev/Averaging/Corrector.lean`:
  the same complete new Corrector module. The current `inp-n1204` tip was
  `1e347889989f4d85f8d0444344c9e6164ffbb215`; its unfiltered triple-dot comparison
  includes unrelated inherited changes. These are not attributed to N12-05.
- `git diff HEAD^ HEAD --name-only`: only `KAM/Nekhoroshev/Averaging/Corrector.lean`.
  Parent `b59c006` is the N12-04 merge. Coefficients was inspected as an interface dependency,
  not independently recertified here.

Input SHA-256:

| Input | SHA-256 |
|---|---|
| Corrector.lean | `c9bd31034a592c321c8f58d2428c39c659b5fc46f22a5ccb06872a665314329d` |
| N12-LEAN-DESIGN.md | `d66059fe35c7b3f76307ae60df90aa3da66ea089cd3ec073b39cbe2ffd1b6370` |
| Main-worktree N12Signatures.lean | `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369` |
| p12-averaging.tex | `dd549dc5c3069e1a185767b5fa580d979963fa920a4b9e7939529047d13ebbfc` |

A mechanical comparison normalized whitespace and compared every definition body and the entire
`corrector` telescope/conclusion against both the standalone signatures and design appendix:
**12/12 matches against each authority**. The proof body is new; no extra binder is inserted.

## Declaration and definition classification

All declarations below belong to `KAM.Nekhoroshev`, all implement pieces of
`bpN:p12:corrector` at blueprint Part 12:99–110. Lines refer to Corrector.lean.
There are eleven definitions, one public theorem, no new structure, instance or abbreviation.

| Node / piece | Declaration / line | Verdict | Classification and reason |
|---|---|---|---|
| Rational divisor | `avgPsi`, 28 | PASS | Exact total real rational function `y/(y²+κ²)`; positive κ guarantees a nonzero denominator for every real y. |
| Rational derivative | `avgPsiD`, 29 | PASS | Exact `(κ²-y²)/(y²+κ²)²`; derivative interpretation is proved under κ>0. |
| Divisor calculus | `corrector`, 31 | PASS | Smoothness, derivative, both global bounds, residual identity and range, and all three guarded reciprocal bounds. Sole premise κ>0; valid strengthening dropping blueprint κ≤1. |
| Mode corrector | `avgU`, 86 | PASS | Existing coefficient at real inclusion times real divisor cast to ℂ times integer mode component. Exact order/types, no coefficient replacement. |
| Corrector sum | `avgW`, 89 | PASS | Negative complex character-weighted vector tsum; includes every mode. Zero mode is identically zero because `k j=0`. Total sum, with convergence a later obligation. |
| Corrector envelope | `avgWenv`, 93 | PASS | ENNReal sum of max-mode norm times β times absolute divisor. Infinite values retained. |
| Angle derivative envelope | `avgW1env`, 96 | PASS | Exact extra `2π |k|₁` factor; uses existing modeSize and Pi max norm. |
| Action derivative summand | `avgBterm`, 99 | PASS | Exact real summand with `2n/s` and `M₂ |k|₁`; no operator-norm substitution or hidden dimension factor. |
| Action derivative envelope | `avgBenv`, 104 | PASS | ENNReal sum of ofReal of the literal B summand. |
| Residual envelope | `avgRenv`, 106 | PASS | Exact `2π |k|∞ β κ²/(q²+κ²)` including resonant q=0. |
| Combined envelope | `avgPhiEnv`, 109 | PASS | Exact `(ε4/s) B + (ε2/s) W1 + R` in ENNReal, no toReal or finiteness assumption. |
| Residual | `avgResidual`, 113 | PASS | Literal inclusion of avgA minus real Fréchet derivative of avgW at `(ω,0)`; this is the angle contraction, with complex vector codomain. |

Whole-carrier check: the definitions are literal algebraic expressions for arbitrary inputs,
without a custom fallback branch or replacement law. Mathlib total division makes the rational
expressions defined even at κ=y=0, but the calculus theorem requires κ>0. `avgW` is a total
`tsum`; without summability its value is not asserted to be an analytic corrector. `fderiv` in
`avgResidual` is likewise totalized until differentiability is proved. `ENNReal.ofReal` truncates
negative terms outside the intended positive-parameter regime; on the source regime
`s>0`, `M₂≥0`, `ε≥0`, `κ>0`, all summands and multipliers are nonnegative and the formulas
are exactly the blueprint envelopes. These totalizations are the specified design bodies;
no theorem in this package relies on their values outside that regime. In particular there
is no asserted bound, finiteness, measurability or regularity of these arbitrary total extensions.

The all-mode sums agree with the blueprint's nonzero-mode sums because the zero mode vanishes.
This remains valid for n=0 as a definition (the Pi vector is zero); no spurious dimension
premise is introduced. The only theorem is scalar and has no n, h, f, analytic or rank premise.

## Proof review and hypotheses

The positive denominator is established for every real y (line 39), giving ContDiff.div at
lines 41–42. The quotient rule at lines 46–52 yields the declared derivative after polynomial
normalization. The sharp global divisor bound uses `(abs y-κ)²≥0`. The derivative bounds use
`abs(κ²-y²)≤y²+κ²`, followed by multiplication through strictly positive denominators.
The residual equality follows by field algebra; its nonnegativity and upper bound use κ²>0
and y²≥0. Every reciprocal-y bound is inside the `y≠0` branch, which supplies y²>0.
No conclusion-shaped premise, instance or bundle is assumed.

The direct import is only `Averaging.Coefficients`. A source traversal of its KAM import closure
found 50 modules, **no provider and no frozen theorem module**. All 18 reachable frozen
definition modules have manifest state SEALED. Thus no DRAFT_SORRY theorem enters the proof.
The proof's axiom receipt below independently excludes sorryAx.

DESIGN-N12 audit 1's missing termwise-derivative finding was resolved by design audit 2 in the
`wreg` signature. That obligation belongs to N12-06, and is neither assumed nor claimed here.
Blueprint Part 12:109's envelope regularity is assigned separately to `envelope_regular`.

## Independent verification

All audit-owned Lean/Lake operations were sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No resource override, clean, dependency update, cache fetch or generated-file edit was used.

Targeted gate:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1205 KAM.Nekhoroshev.Averaging.Corrector
[inp-gate] slot 2 acquired 08:41:21 for KAM.Nekhoroshev.Averaging.Corrector
Build completed successfully (3180 jobs).
exit 0
```

This is the targeted dependency-graph build using the existing overlay, not a clean rebuild.

Temporary probe `.lake/abi-scratch/N1205Audit.lean` imported Corrector and checked the entire
literal theorem statement by applying `KAM.Nekhoroshev.corrector hκ`. It also elaborated
`avgPsi κ 0 = 0` for arbitrary κ and `avgU h f κ 0 I = 0` for arbitrary h,f,κ,I,n.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1205Audit.lean
'KAM.Nekhoroshev.corrector' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

The sole new public theorem has exactly the allowed axioms. The first scratch invocation
printed the same axioms but exited 1 with `expected token` at the ∞ notation: the probe had
omitted `open scoped ContDiff`. Adding that scope to the scratch file fixed the probe;
production source was unchanged. No provider probe is applicable.

Kernel replay (one invocation, sole in-scope lemma module):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.Corrector
replaying KAM.Nekhoroshev.Averaging.Corrector
exit 0
```

Repository lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (491 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint complaint is exactly the exception permitted by the audit brief. KAM.lean was
not regenerated. This is an accepted exception, not an unqualified exit-0 lint claim.
Corrector has 119 physical lines (handoff's 118 is a harmless count discrepancy), module header,
copyright, public import, docstring and exposed public noncomputable section. A direct scan found
no forbidden escape, resource override or EuclideanSpace. No new instances or alternative norms.

Protected-path comparison:

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no diff; exit 0)
git diff --check inp...HEAD
(no whitespace errors; exit 0)
```

Both commands emitted the multiple-merge-base warning noted above. No protected path was
changed by N12-05 or this audit. The pre-existing untracked handoff was preserved. The temporary
probe was deleted; the only audit-created repository file is this report. Final report whitespace
validation uses `git diff --no-index --check /dev/null docs/tracks/N/audits/N12-05-audit-1.md`.

## Findings, uncertainties and errata

No new suspected blueprint defect, pinned-source erratum, frozen-statement defect or implementation
deviation was identified. The local blueprint and exact design signatures are the source authority
for this elementary calculus package; no fresh pinned-PDF audit is claimed. The already documented
Nei76 maximum-error correction and the later regularity/assembly obligations are outside N12-05.

The extension from 0<κ≤1 to all κ>0 is a proved strengthening explicitly allowed by the design.
The whole-carrier totalizations described above impose future summability/differentiability and
positivity gates; this package does not discharge or assume those gates. Do not interpret its PASS
as completion of `wreg`, `envelope_regular`, or either averaging root.

Files changed by auditor: this report only. Approach: direct statement/body comparison, adversarial
resonance and totalization review, explicit theorem/zero-mode probes, axiom inspection, targeted
build, kernel replay, source lint, and protected-path checks. **N12-05 accepted with the stated
nonblocking notes; no repair requested.**
