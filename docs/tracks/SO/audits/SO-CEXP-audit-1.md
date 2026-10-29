# SO-CEXP independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-socexp`.
Audited HEAD: `1aae34398e2921d3824618f00488adafc3fcbcdd`.
Comparison ref `inp`: `d628f39ee7320757e0345cb7af9b5c018af60c2c`.

**Overall: PASS WITH NOTES for the explicitly scoped arithmetic module.**
Both signed declarations pass exact signature, implementation and proof review. The module's
assigned arithmetic slice is complete. There is no frozen anchor/provider in this package, so
“seal-ready” and frozen seal-body substitution are not applicable. This is not a verdict that the
whole design-labelled SO-CEXP package is complete: the separately named test module is absent.
The other note is the expressly permitted stale generated root. A minor design wording issue
about `s = 0` is recorded below.

## Scope and authorities

Read the local `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local SO-CEXP handoff.
The user's explicit report path overrides the generic audit brief's main-worktree destination.
The handoff's AUDIT FOCUS limits the implementation audit to
`KAM/Certificate/Arith/ComplexExp.lean`; dependencies were inspected to establish the meanings
and applicability of its imported operations, rather than re-audited as this package's changes.
The SO-specific signed text and design supersede generic I/N/P blueprint/anchor instructions:

- `/root/code/KAM-inp/.drafts/briefs/offload-main/SO-CEXP.md` (two fixed declarations).
- `/root/code/KAM-inp/.drafts/design/SOSignatures.lean:284–315` (arithmetic contract and
  separately assigned SO-BALL completeness helper).
- `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, Revision 4,
  lines 39–59, 392, 416, 444, 515–518 and 869–900.
- `/root/code/KAM-inp-design-so/docs/tracks/SO/audits/SO-DESIGN-audit-3.md:39–57` (F10).

The full `git diff inp...HEAD` contains exactly one addition, the 76-line arithmetic module.
The initially untracked handoff is pre-existing audit input. No source, generated file,
manifest or git state was changed by the auditor. Only this report and temporary scratch
probes were written; the probes were removed after validation.

## Declaration-by-declaration results

All names in this table are under `KAM.Certificate`.

| Node / location | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| SO-CEXP / lines 26–28 | `certBallSquareIter` | PASS WITH NOTES | Extra public helper disclosed in handoff. Correct structural recursion: identity at zero, product of previous ball with itself at successor. Unique short name, exposed body, no additional assumptions. |
| SO-CEXP / lines 30–40 | `mem_certBallSquareIter` | PASS WITH NOTES | Extra public helper. Proves containment of `exp (2^s * v)` from initial exponential containment by induction and `CertBall.mem_times`; it does not assume the iterated conclusion. Unique short name. |
| Signed arithmetic contract / lines 46–53 | `certCExpReduced` | PASS | Header matches draft verbatim, under the exact signed namespace. Computes the full reduced ball, tests that rounded ball, evaluates the Taylor enclosure and performs exactly `s` certified squarings; failure returns `none`. |
| Signed arithmetic contract / lines 55–76 | `certCExpReduced_sound` | PASS | Header matches draft verbatim, including implicit binders and their order. Successful return plus input membership implies output membership, for arbitrary lawful backend, ball, `s`, `N` and point. No input-size premise added. |

There are no additional explicit public declarations, structures or abbreviations in the diff.
The two extra helpers are a disclosed interface expansion, not substitutes for either signed
result. All four short names occur as declarations exactly once across `KAM`; all are inside
`namespace KAM.Certificate`, with no root-level declaration shadowing.

## Definitions and whole-carrier behavior

`certBallSquareIter` is an actual finite ball computation on every `CertBall α` and natural
iteration count. Its compiled body uses `Nat.brecOn`, Lean's structural course-of-values
recursor, not well-founded recursion. Kernel `rfl` probes establish both recursion equations.

`certCExpReduced` is an actual law-free computation for every `CertArith α`, centre, radius
and natural parameter pair. It has no invented successful fallback or junk enclosure.
`none` means the rounded reduction failed its test. Success soundness is intentionally
conditional on `LawfulCertArith α` and membership of the input point; negative represented
input radii have no members, since norms are nonnegative. No positivity premise is hidden
or silently added. No theorem of eventual success for arbitrary rounded backends is claimed.
An unfolding `rfl` probe checks the entire signed algorithm body.

Error accounting in the proof:

1. Lines 63–64 use `mem_ofRat` to enclose the exact rational `2^(-s)`, including its
   outward-conversion error, and `mem_times` to enclose the scaled input point. Scaling
   centre errors and input-radius propagation therefore enter the reduced radius.
2. Line 65 derives the smallness premise from the test on that same rounded reduced ball.
   The imported small exponential theorem pays both Taylor-sum rounding and its remainder.
3. Lines 66–67 use the proved square-iteration helper. Each squaring is the full
   `CertBall.times`, whose radius contains the two radius-growth contributions and real/
   imaginary multiplication and addition errors. Nothing is reset to an exact-point ball.
4. Lines 68–74 cancel the nonzero power of two exactly in complex arithmetic and identify
   the returned pair through the successful-return equality. The false-test branch is
   excluded by that equality at lines 75–76.

The imported `LawfulCertArith` fields are the standing arithmetic soundness laws, not an
exponential conclusion bundled as a premise. The full KAM import closure is just this module,
`Arith.Roots`, `Arith.Interface`, and `Arith.PiHigh`. There are no provider imports or frozen
imports, hence no DRAFT_SORRY/SEALED import-state issue.

## Completeness boundary and design wording

**Test coverage remains unpaid outside the requested module scope.** Revision 4 design line
444 assigns SO-CEXP “Arith/ComplexExp, Tests/ComplexExp”; lines 515–518 and Appendix A lines
1934–1947 name five regression declarations: `cexpTest_zero_small`, `cexpTest_zero_large`,
`cexpTest_two_rejected`, `cexpTest_two_reduced`, and `cexpTest_large_pin`. There is no
`KAM/Certificate/Tests/ComplexExp.lean` (indeed no tests directory) in this checkout, and the
branch diff contains none of these tests. Thus the broader design-assigned package is not
complete as written. The narrow prover brief makes a sanity example optional; this omission
is not a failure of the two fixed declarations or the explicitly requested module slice.
Do not report the five design tests as supplied or independently passed.

`cexpHalvings` and `certCExpReduced_cexpHalvings_isSome` are explicitly assigned to **SO-BALL**
by the design Revision 4 table and the draft's completeness docstring. Their absence here is
not a missing theorem of this module. Downstream pins, composition, ball consumers and
SO-REPLAY cost measurements remain separate obligations; this audit establishes the primitive,
not their attachment or the lunar certificate.

**Minor documentation precision issue:** draft signatures lines 292–293, repeated in design
lines 877–878, say “`s = 0` is exactly the guarded small call.” On a general rounded backend,
lines 48–49 still form `CertBall.times input (CertBall.ofRat 1)` before testing; these operations
may enlarge the radius or round the centre. The backend laws do not assert that multiplication
by this ball is an identity. The wording is exact over an exact backend, or if understood as
the guarded call on the computed reduced ball, but does not establish equality with a direct
call/guard on the original ball for every backend. The implementation follows the mandated
algorithm and proves the correct signed theorem; no source repair is proposed in this audit.
No new mathematical source erratum or deviation from the two signed declarations was found.

## Independent validation receipts

All Lean/Lake commands were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No heartbeat, recursion-depth, or synthesis-budget override was used. No cache fetch, clean,
update, library rebuild from scratch, or package-directory mutation was performed.

### Targeted compile gate

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-socexp KAM.Certificate.Arith.ComplexExp
```

Exit **0**. Output:

```text
[inp-gate] slot 1 acquired 12:35:05 for KAM.Certificate.Arith.ComplexExp
⚠ [2840/2842] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one
Hint: Omit it from the simp argument list.
  [apply] simp [div_eq_mul_inv]
Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (2842 jobs).
```

The warning is in an unchanged dependency, not the audited file; no option was changed.

### Signature, body, recursion and axiom probes

A Python comparison extracted each signed header through the token preceding `:=` from the
implementation and the draft. Output:

```text
certCExpReduced VERBATIM HEADER MATCH: True
certCExpReduced_sound VERBATIM HEADER MATCH: True
lines: 76 max columns: 95
forbidden tokens: []
```

The namespace was independently checked against the draft and by fully qualified Lean names.
Temporary probe command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOCExpAudit.lean
```

Exit **0**. It checked the full generic definition type, a fresh theorem with the exact signed
soundness binders and conclusion applied directly to `certCExpReduced_sound h hw`, both
structural recursion equations by `rfl`, and the complete computation body by `rfl`.
A frozen `type_of%`/seal-body comparison is inapplicable: neither a frozen export nor provider
exists for SO-CEXP. The probe used no placeholder and produced:

```text
'KAM.Certificate.mem_certBallSquareIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certCExpReduced_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certBallSquareIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certCExpReduced' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`#print` also showed `certBallSquareIter` defined through `Nat.brecOn` and
`certCExpReduced` as the displayed finite let/if computation. No well-founded recursor occurs.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Arith.ComplexExp
```

Exit **0**. Complete output:

```text
replaying KAM.Certificate.Arith.ComplexExp
```

This single module contains both new theorem proofs and both definitions; there is no separate
new lemma/provider module requiring a second replay target.

### Repository lint and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted stale generated root:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1296 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The root was not regenerated. No substantive lint failure occurred.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit **0**, with empty output. `git diff --name-status inp...HEAD` reports only:

```text
A	KAM/Certificate/Arith/ComplexExp.lean
```

Static checks found no forbidden proof tokens, resource options, `EuclideanSpace`, or
`native_decide`; 76 lines and maximum 95 Unicode characters per line. Copyright, `module`,
public import, module docstring and exposed public section are present. Every new short name
has exactly one declaration across KAM. Scratch probes were removed. No frozen anchor,
manifest, generated root, README or production source was edited by this audit.

## Handoff

Files delivered: this report only. Arithmetic primitive and both proof bodies independently
validated; no implementation fix required. Carry forward the missing design-assigned test
module, the minor rounded-backend `s = 0` wording qualification, and the permitted stale-root
lint status. No claim of consumer completeness, performance validation or frozen theorem
closure is made.
