# SO-ABK independent audit 1

**Verdict: PASS WITH NOTES.** The three signed declarations match the draft surface, the
`Fixed.lean` slice is complete, and all twelve arithmetic laws are proved for the actual
operations without extra premises. The only validation notes are the permitted stale generated
`KAM.lean` and an inherited `PiHigh.lean` unused-simp warning. No frozen anchor is supplied or
sealed by this package; “seal-ready” is therefore inapplicable.

## Scope and authority

Audited 2026-10-29 in `/root/code/KAM-inp-soabk`, HEAD
`ba48549272c16d73a9597cd98dbec4fc31fc15a8`, against `inp`
`503064c9ac6b80b2e3e401f9419c6bf18811ef6e` using the full `git diff inp...HEAD`.
The diff adds only `KAM/Certificate/Arith/Fixed.lean` (213 lines).
The pre-existing untracked `docs/tracks/SO/audits/SO-ABK-handoff.md` was left untouched.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the SO-ABK handoff.
Applied its AUDIT FOCUS: only `Fixed.lean`, with dependencies read for context.
The controlling surface is `/root/code/KAM-inp/.drafts/design/SOSignatures.lean:137–143`
inside namespace `KAM.Certificate`; compared Revision 4
`/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md` §5,
§7 SO-ABK row, and Appendix A Backends (lines 722–728).
The project plan is `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`;
project scope is recorded in decision D30. I/N/P frozen-anchor and blueprint-node seal tests
are inapplicable to this explicitly scoped SO backend package.

The user’s exact report path overrides the generic brief’s MAIN-worktree destination.
Only this report and temporary probes under this worktree’s `.lake/abi-scratch/` were written.
All Lean/Lake checks were serial, with `LEAN_NUM_THREADS=1` and `nice -n 5`.

## Declaration and law review

Names below are relative to `KAM.Certificate`; law rows describe the fields supplied by
`instLawfulCertArithFixed`, not newly named standalone theorems.

| Node / location in Fixed.lean | Declaration | Verdict | Reason |
|---|---|---|---|
| Signed backend, 28–29 | `CertFixed` | PASS | Exactly `(P : ℕ)` with sole field `m : ℤ`; same fully qualified name and field as draft. |
| Signed data instance, 68–83 | `instCertArithFixed` | PASS | Exactly `(P : ℕ) : CertArith (CertFixed P)`; no premises. `noncomputable` does not alter the type or kernel reduction. |
| Signed laws, 88–171 | `instLawfulCertArithFixed` | PASS | Exactly `(P : ℕ) : LawfulCertArith (CertFixed P)` for the actual data instance; all twelve fields supplied. |
| Scale, 34 | `CertFixed.ulpDen` | PASS | Natural power cast to integer, exactly positive `2^P` for every natural precision. |
| Ceiling, 37 | `CertFixed.cdiv` | PASS | `-((-x) / d)`; ceiling interpretation used only with positive divisor. |
| Scale positivity, 39 | `CertFixed.ulpDen_pos` | PASS | Unconditional in P, including P = 0. |
| Scale cast, 42 | `CertFixed.ulpDen_cast` | PASS | Exact real power identification. |
| Floor bounds, 46–54 | `CertFixed.fdiv_bounds` | PASS | Arbitrary signed numerator; sole premise `0 < d` is necessary domain data. Uses Euclidean remainder bounds. |
| Ceiling bounds, 57–62 | `CertFixed.cdiv_bounds` | PASS | Arbitrary signed numerator and positive divisor; derives both endpoints from floor bounds at `-x`. |
| Denotation, 85–86 | `CertFixed.val_def` | PASS | Definitional equality on entire carrier, no additional premises. |
| Law, 89–94 | `val_ofInt` | PASS | Scaling by D and division by positive D cancel exactly. |
| Law, 95–104 | `ofRatUp_ge` | PASS | Ceiling of `q.num * D / q.den`, divided by D, is at least q for either sign. Rational denominator is positive. |
| Law, 105–114 | `ofRatDown_le` | PASS | Corresponding floor is at most q; no sign restriction on numerator. |
| Law, 115–119 | `add_err` | PASS | Exact integer addition; error zero. |
| Law, 120–123 | `val_neg` | PASS | Exact integer negation. |
| Law, 124–140 | `mul_err` | PASS | Universal signed operands; absolute floor error bounded by one ulp `1/D`. |
| Law, 141–145 | `val_abs` | PASS | Integer natAbs cast and positive denominator give exact absolute value. |
| Law, 146–149 | `upAdd_ge` | PASS | Exact addition gives equality, hence required upper bound. |
| Law, 150–160 | `upMul_ge` | PASS | Ceiling gives required upper bound; proof actually ignores both interface nonnegativity premises and works for all signs. |
| Law, 161–164 | `ble_sound` | PASS | Integer comparison transfers through division by positive D. |
| Law, 165–168 | `blt_sound` | PASS | Strict comparison similarly transfers. |
| Law, 169–171 | `beq_sound` | PASS | Integer equality gives equality of denotations. |
| Test aliases, 175–176 | `F64`, `F448` | PASS | Exact specializations of carrier, no fallback or extra mathematical claim. |
| Kernel examples, 178–209 | Eleven anonymous examples | PASS | Independently rerun, including true/false controls and production-size π enclosure. |

The draft structure text and both instance names/types agree exactly, including namespaces,
precision binders and the instance used by `LawfulCertArith`. There are no widened constants,
changed quantifiers, hidden instances supplying a hard proof step, or conclusion-shaped premises.
The separately named helpers implement elementary rounding identities, not substitutes for any
signed result. No provider/frozen seal-copy probe is applicable here.

For the potentially delicate multiplication step, put `D = 2^P > 0`, `x = a.m*b.m`, and
`k = x / D` in integer floor division. The proof establishes
`k*D ≤ x < k*D+D` for every integer x. Consequently
`-1/D < k/D - x/D² ≤ 0`, which implies the interface’s absolute error bound `≤ 1/D`.
A negative product is covered by precisely this argument; truncation toward zero is never assumed.
Ceiling division similarly gives `x ≤ cdiv x D * D`, so directed multiplication is sound
without sign assumptions. The two unused nonnegativity binders are harmless and strengthen
what the proof internally establishes.

## Definition classification

* `CertFixed P`: unrestricted integer mantissa carrier; denotation is exactly `m / 2^P`.
* `ulpDen`: exact positive scale, no precision-zero exception.
* `cdiv`: total integer function on every pair, with positive-divisor ceiling semantics.
  At zero or negative divisor its Lean integer-division value is still defined; no theorem claims
  positive-divisor ceiling bounds there, and no backend operation reaches those cases.
* `instCertArithFixed`: data definition. `ofInt` is exact scaling; rational conversions use positive
  canonical rational denominators; add, neg and upAdd are exact; mul floors and upMul ceilings;
  abs uses integer absolute value; errors are 0 and one ulp. Comparisons decide actual integer
  relations. There are no junk-value branches or finite-range overflow assumptions.
* `F64`, `F448`: public abbreviations for the two test precisions. `instLawfulCertArithFixed`
  is a proof of the interface laws, not an assumed bundle of those laws.

## Independent validation

### Targeted build

Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soabk KAM.Certificate.Arith.Fixed
```

Exit 0. Output:

```text
[inp-gate] slot 1 acquired 14:40:25 for KAM.Certificate.Arith.Fixed
⚠ [2840/2843] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one

Hint: Omit it from the simp argument list.
  [apply] simp [div_eq_mul_inv]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (2843 jobs).
```

The warning is in an unchanged dependency; no linter option was changed.

### Expected types, definitions, axioms and independent reduction

Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOABKAudit.lean
```

Final exit 0. The probe checked the exact expected types of the two signed instances, constructor
and projection, helper theorem statements and definitional bodies for scale, ceiling, denotation,
rounded multiplication and rational conversions. It also instantiated all twelve law projections
using the actual lawful instance. All eleven source examples were copied into the probe and
elaborated again, so this check does not rely only on cached build success.

Additional `decide +kernel` controls checked at P = 1:
`mul(-3,1).m = -2`, `upMul(-3,1).m = -1`, `mul(-3,-1).m = 1`,
`upMul(-3,-1).m = 2`, and downward/upward conversion of `-3/4` giving mantissas
`-2`/`-1`. At P = 0, `mul(-3,2).m = -6`. A false equality control rejects
mantissa `-1` for the negative floor product. All passed at default resource limits.

The initial scratch-only probe failed because its instance-valued example needed a
`noncomputable section` and copied aliases at root conflicted with the imported aliases after
opening the namespace. Correcting the probe context and reusing the imported aliases resolved
both; these were probe-construction errors, not package failures or namespace collisions in
production. The successful rerun is the evidence used above. Scratch file removed afterward.

Exact axiom output:

```text
'KAM.Certificate.instCertArithFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.instLawfulCertArithFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertFixed.ulpDen_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertFixed.ulpDen_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertFixed.fdiv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertFixed.cdiv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertFixed.val_def' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This covers both instances and every new named public theorem. In particular, no `sorryAx`
enters the actual arithmetic operations or lawful instance.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Arith.Fixed
```

Exit 0. Complete output:

```text
replaying KAM.Certificate.Arith.Fixed
```

There is one package module and no separate provider/lemma modules to add to this invocation.

### Lint, import quarantine and protected paths

`sh scripts/lint_sources.sh` exited 1 with exactly:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1307 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole lint failure is expressly allowed by the audit brief. Generated files were not edited.
`git diff --check inp...HEAD` exited 0 with no output.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exited 0 with no output.

Independent Python source scanning found 213 lines, maximum Unicode line length 100,
and no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace`
or `set_option` tokens. Module header, copyright, public imports, module docstring,
public section and exposed definitions are present. Public declarations remain within
`KAM.Certificate` or `KAM.Certificate.CertFixed`; no root declaration is introduced.
A declaration-name scan over all KAM and Mathlib Lean files found no other occurrence of
any new declaration short name (including helpers and the two aliases).

The complete project import closure from Fixed goes through PiEnclosure, Roots, Interface,
and PiHigh, then Mathlib. It imports no provider and no frozen theorem, hence no
DRAFT_SORRY anchor. No provider quarantine exception is needed.

## Uncertainties, errata and deviations

No suspected source or blueprint defect was found in this scope. No implementation deviation
from the signed backend surface was found. Exact addition and unrestricted signed rounding
are consistent with the design. The handoff’s production-backend choice is context; this audit
certifies the fixed backend slice, not a full replay-gate performance or accumulated-ulp result.
It does not establish the final certificate, lunar confinement, or any I/N/P frozen theorem.

The kernel examples verify their stated finite inputs, including P = 448 and Machin (50,15).
The handoff’s profiler timings were not remeasured or endorsed as performance guarantees.
Dependency mathematics was not separately re-audited beyond the interface, import closure,
axiom evidence and requested kernel replay. Remaining validation notes are only the unchanged
PiHigh warning and the permitted stale generated root.
