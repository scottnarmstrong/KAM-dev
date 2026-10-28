# Independent P11A-P5 audit 2 (delta)

**Delta verdict: PASS; Round 1 F1 is resolved. Overall authorized parametric package:
PASS WITH NOTES**, retaining Round 1 N1 and the inherited-history qualification below.
The amended denominator and the exported source rate supply the missing quantitative
interface for `stepP:p11:as-osc`. This receipt does not certify that consumer's proof or
seal P-FIXED; no provider or frozen theorem is delivered by these five modules.

## Scope and authority

Worktree `/root/code/KAM-inp-p11ap5`, HEAD
`798b999a67520b92bb55ebf904f9eee3541a1383`, baseline `cd561f17`.
Read the supplied package brief, AGENTS.md, PLAN.md, DECISIONS.md, AUDIT FOCUS,
Round 1 report, both handoffs including “Round 2 fix”, P11A design/node registry,
track P statement, the preparation blueprint, relevant frozen P-FIXED anchor and
current signature. The 23:20 ruling authorizes exactly the parenthesized `p11d1`.
The user's exact report destination overrides the generic brief's main-worktree path.

Audited only `KAM/Planetary/Preparation/{Fast,FastBridge,FastDivisor,FastParams,LogBounds}.lean`.
The complete delta `git diff cd561f17..HEAD` is one commit, changing only `Fast.lean`
(63 insertions, 15 deletions) and `FastParams.lean` (55 insertions, 26 deletions).
The other three modules are byte-unchanged. Round 1's unchanged-declaration ledger
continues to apply; all 40 current public theorems were independently axiom-checked.

Current `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` SHA-256:
`fd2c245ea48f1b99f36beb02bba0095e9a55b070be0eae178198fdf20011b9e9`.
The seven contiguous signed data declarations match that file, whitespace-normalized.
All other signed declarations in scope are unchanged from `cd561f17`, including `e4`.
The signed `avg_fast` and selected `p11FastData` remain outside the authorized core,
per the explicit scope ruling; their absence is not a finding.

## F1 resolution and proof fidelity

`Fast.lean:35` is exactly the amended signature at line 781:

```lean
def p11d1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) :=
  min (p11s1 C eps*C.sigma) (C.rz^2)
```

A fresh `rfl` probe verifies the parsed value is `min (s1*sigma) (rz^2)`.
`p11d1_le` now proves positivity and equality with the oscillator denominator up to
`sq`. The two comparisons in `fast_spec_at` retain their valid directions: transfer
of S1 to the oscillator hypothesis and transfer of its G bound to `p11eta1`.
Both comparisons now compare equal denominators. The bodies of `fast_spec_at` and
`avg_fast_of_spec` are unchanged; their complete theorem statements are byte-identical
to baseline. Rebuilding checks their proofs against the amended definition and the
new parameter lemmas. No new premise, field, instance, or conclusion-shaped assumption
was introduced.

`FastParams.lean:64` proves the uniform scalar lower bound
`c2 / K^(tau+1) <= d1`, with
`c2 = min (min rC (gamma/(4*L)) * sigma) (rz^2) > 0`.
It compares each branch of the actual minimum and uses `K >= 1`; no active-branch
selection or asymptotic equivalence is assumed. The restated `fast_rhs_lower` and
`fast_small_eventually` use this corrected minimum. Their source premises are unchanged;
smallness follows from `e4` with exponent `3*(tau+1)`. This conservative exponent is
only an intermediate smallness estimate, not the exported eta exponent.

`Fast.lean:406` states exactly:

```lean
theorem p11eta1_source_rate (hC : P11SecularSpec D C) :
    ∃ c eps1 : ℝ, 0 < eps1 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eps1 →
      p11eta1 C eps ≤ c * eps * Real.log (1 / eps) ^ (2 * C.tau + 1)
```

This is blueprint `p11-cp09-preparation.tex:108`, “with c=c(data)”, with real rpow
exponent `2*tau+1`. The witnesses precede `forall eps`; c is independent of eps.
The actual proof selects `eps1 = exp(-1)/C.MF` and

```
c3 = 6/(pi*C.sigma)
c  = 400*(1+n)*C.MF^2*c3^(2*C.tau+1)/(pi*C.gamma*c2).
```

All denominator factors and the displayed c are positive from `fast_consts`.
Combining `alpha1 = gamma/2*K^(-tau)` with the new d lower bound gives
`eta1 <= 400*(1+n)*eps*MF^2*K^(2*tau+1)/(pi*gamma*c2)`.
Since `MF >= 1`, `K <= c3*log(1/eps)`, giving the literal claimed rate.
The proof neither changes the epsilon power nor allows c to depend on epsilon.

Precision about positivity: the exported type explicitly requires `eps1 > 0`, not
`c > 0`. This matches the blueprint's stated upper bound; the displayed witness is
positive. A separate elaborated probe derives the version with both `c > 0` and
`eps1 > 0`, using `max c 1` and `min eps1 1`. Thus the handoff's positive-constant
reading loses no strength. No production declaration was changed by the auditor.

The scalar estimate bounds the same `p11eta1` already used in `P11FastSpec` for every
constructed A. Intersecting its threshold with `avg_fast_of_spec`'s threshold gives
both conclusions for the same eps and A; no new choice or map-dependent constant is
needed. This closes F1's interface obstruction to the slow stage. It does not establish
`as-osc` or the remaining physical assembly itself.

## Delta and node ledger

All names are in `KAM.Planetary`; locators below are in the audited directory.
Unchanged auxiliary declaration rows and definition classification are also recorded
in audit 1; their proof bodies have not changed in this delta.

| Node / declaration | Verdict | Reason / locator |
|---|---|---|
| sec-C data: `p11K1` | PASS | Fast:30; signed, unchanged. |
| sec-C data: `p11Alpha1` | PASS | Fast:32; signed, unchanged. |
| sec-C data: `p11s1` | PASS | Fast:33; signed, unchanged. |
| sec-C data: `p11d1` | PASS | Fast:35; exact amended body, parse checked. |
| sec-C data: `p11eta1` | PASS | Fast:36; signed body unchanged; F1 resolved. |
| sec-C data: `P11FastData` | PASS | Fast:38; exact signed data structure. |
| sec-C data: `P11FastSpec` | PASS | Fast:43; exact signed predicate. |
| support: `p11d1_le` | PASS | Fast:159; unchanged type, corrected positive denominator. |
| support: `fast_rhs_lower` | PASS | FastParams:25; restated for authorized d, no added premise. |
| support: `fast_d_lower` | PASS | FastParams:64; new source-denominator lower bound. |
| af-o2: `fast_small_eventually` | PASS | FastParams:94; actual S1 for amended d via e4. |
| af-apply: `oscHyp_fast` | PASS | FastBridge:159; unchanged oscillator application. |
| af-o1: `fast_divisor` | PASS | FastDivisor:109; unchanged source divisor bound. |
| af-concl: `fast_spec_at` | PASS | Fast:194; unchanged type/body, rebuild and replay checked. |
| avg-fast core: `avg_fast_of_spec` | PASS WITH NOTES | Fast:390; unchanged; N1 below. |
| avg-fast rate: `p11eta1_source_rate` | PASS | Fast:406; literal line-108 rate, uniform c. |
| e4: `e4` | PASS | LogBounds:30; signed, unchanged. |
| e4 first clause: `log_inv_ge_one` | PASS | LogBounds:22; unchanged. |
| P-FIXED anchor | Outside scope | No provider or seal-ready claim. |

## Definition classification and remaining note

No new def/abbrev/structure was added. The five scalar definitions are explicit total
real expressions, with all analytic positivity guards proved on their intended carrier.
Only `p11d1` changes, to the exact source minimum. No fallback or junk branch is used.
`P11FastData` contains only map/G/f1 data; its default is not used to prove existence.
`P11FastSpec` is the literal signed output predicate, not an assumed averaging result.
`p11Flat` remains whole-carrier concatenation `(J,y,x)`, and `P11SecularHReal` remains
the source reality predicate. There is no hidden norm, coordinate, or measure change.

**N1 retained:** the checked-out `Holomorphic.lean:79-80` still has only the real-part
clause of `P11SecularSpec`; the signature's amended clause at 688-690 also asserts
vanishing imaginary part. Consequently the unchanged explicit `hh : P11SecularHReal C`
remains a P2f integration dependency. It is exactly the authorized source reality
condition, as established in audit 1, not a new delta premise. The physical wrapper
cannot be claimed from this checkout until that integration is supplied.

No new suspected blueprint or pinned-source defect was found. The old signed-text
precedence defect is repaired under the 23:20 ruling, not silently normalized.
No additional mathematical deviation, heartbeat failure, or resource override occurred.

## Independent validation

All Lean/Lake commands were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`.
Let `M` denote the following five module arguments, in this exact order:

```text
KAM.Planetary.Preparation.Fast
KAM.Planetary.Preparation.FastBridge
KAM.Planetary.Preparation.FastDivisor
KAM.Planetary.Preparation.FastParams
KAM.Planetary.Preparation.LogBounds
```

1. Targeted compile gate:

```sh
env LEAN_NUM_THREADS=1 nice -n 5   /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh   /root/code/KAM-inp-p11ap5 $M
```

Exit **0**. Output includes `[inp-gate] slot 1 acquired 23:36:33` and
`Build completed successfully (9328 jobs).` Existing dependencies replay unused-variable,
unused-simp and deprecation warnings; no diagnostic originates in the five audited files.

2. Fresh untracked scratch probe:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP5Audit2.lean
```

Exit **0**, no errors or warnings. The probe proves the amended parse by rfl,
checks the literal exported rate type, derives the version with both constants positive,
and runs `#print axioms` on every one of the 40 public theorems in the five modules.
Each line has exactly the axiom set `[propext, Classical.choice, Quot.sound]`.
In particular the exact main-result output is:

```text
'KAM.Planetary.fast_spec_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.avg_fast_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11eta1_source_rate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fast_d_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Single-invocation kernel replay:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose $M
```

KERNEL_RESULT_PENDING

4. Source lint:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

LINT_RESULT_PENDING

Static checks: no forbidden proof token, option override or EuclideanSpace in the five
modules; all have copyright, module declaration, public imports, module docstring and
exposed public section. Line counts / maximum Unicode columns:

| Module | Lines | Max columns |
|---|---:|---:|
| Fast | 464 | 99 |
| FastBridge | 213 | 100 |
| FastDivisor | 175 | 100 |
| FastParams | 172 | 98 |
| LogBounds | 52 | 95 |

A repository-wide declaration search found no reused helper short name for any of the
five modules' explicit declarations. All remain in `KAM.Planetary`, without harmful
root shadow. Traversal of 282 reachable KAM modules found zero provider modules and
zero frozen theorem modules; no DRAFT_SORRY theorem enters the proofs.

## Diff integrity and handoff boundary

`git diff inp...HEAD` was inspected as requested. Current inp is
`a3874e60915dd1e1741516087dc0a6fdb7345534`; Git warns of multiple merge bases and
uses `4a6109378656730cc0b980bc99a04d661042ec0b`. The broad integration diff has
141 files, 24,044 insertions and 530 deletions; only the named P5 modules are audited here.

The protected-path three-dot comparison is **not empty**: inherited `KAM.lean`
regeneration and the N-HEAD-C seal/manifest state change remain, as in audit 1.
They are not Round 2 changes. `git diff cd561f17..HEAD -- KAM/Frozen manifest KAM.lean README.md`
is empty. The complete Round 2 delta touches only the two preparation files above.
`git diff --check` exits **0**. No state-changing Git operation was performed.
Only this report persists as an auditor edit; the scratch probe was deleted after use.

READY maud-p11ap5-2
