# SO-EXPR-A independent audit 1

Verdict: **PASS WITH NOTES** for the complete SO-EXPR-A / Expr/Basic slice.
All ten signed declarations pass. No frozen theorem anchor or provider is supplied by this
package, so frozen-provider equality and sealing are not applicable. This is an infrastructure
package verdict, not closure of the certificate checker or lunar theorem.

Audited HEAD: `0d5b57af7d12326977f66e187b08fe0c03106d0e`.
Observed `inp`: `b483160ac24125b350d36f9231f32175113bdc7a`;
three-dot merge base: `cc2ed0470cd7151ea238a6f916f8017665cafcbc`.
Read the full `git diff inp...HEAD`: only `KAM/Certificate/Expr/Basic.lean`, 208 additions.
The untracked prover handoff pre-existed the audit and was left untouched.
The explicit user report destination overrides the generic brief's MAIN-worktree destination.

Authorities read: worktree `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`;
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`; the package handoff and AUDIT FOCUS;
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean` §D, lines 574–630 and 689–702;
`/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md` Revision 4,
§1 decisions 1–4, §7 module graph, §8 package split, and Appendix A §D;
`/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`, including ruling O2.
The SO signed design governs this slice; no I/N/P theorem or blueprint node is implemented here.

## Declaration-by-declaration review

All declaration names below are prefixed by `KAM.Certificate.`. Line numbers refer to
`KAM/Certificate/Expr/Basic.lean`. “Signed” means exact source-header comparison with the
named draft, including explicit/implicit binders, order, hypotheses and conclusion. For
inductive/definition declarations the constructor list or full body was also compared exactly.

| Node | Lean declaration | Line | Verdict | Reason |
|---|---|---:|---|---|
| §D syntax | `HamExpr` | 35 | PASS | Signed; all 12 constructors, division included. |
| §D phase | `modePhase` | 50 | PASS | Signed; literal `2π` times integer-mode pairing. |
| §D denotation | `HamExpr.eval` | 55 | PASS | Signed; literal operations and action coordinates. |
| §D denominators | `HamExpr.NonvanishingOn` | 70 | PASS | Signed; recursive conditions on both operands plus each divisor. |
| Phase helper | `contDiff_modePhase` | 80 | PASS | Global complex smoothness of finite linear pairing, no premises. |
| §D holomorphy | `HamExpr.contDiffOn_eval` | 84 | PASS | Signed; structural induction, division uses both induction hypotheses and nonzero divisor. |
| Phase helper | `modePhase_add_int` | 104 | PASS | Exact integer multiple of `2π`; casts and finite sums checked. |
| §D periodicity | `HamExpr.eval_add_int` | 112 | PASS | Signed; unconditional for every expression and complex point. |
| Reality helper | `HamExpr.exists_real_eval` | 131 | PASS | Explicit real value by induction, including real totalized division. |
| §D reality | `HamExpr.eval_real` | 168 | PASS | Signed; unconditional imaginary-part equality. |
| §D domain | `certDomain` | 175 | PASS | Signed; geometric strip and action polydisc, exact rational casts. |
| §D openness | `isOpen_certDomain` | 180 | PASS | Signed; finite intersections of strict continuous inequalities. |
| §D translation | `certDomain_add_int` | 199 | PASS | Signed; imaginary angles unchanged and actions untouched. |

This exhausts all 13 explicit public declarations: ten signed declarations and three new helpers.
`phaseBasis` is imported from its existing module, not redeclared. SLP, jets, ball arithmetic,
and composition belong to other slices and are not missing SO-EXPR-A obligations.
No added premise, weakened conclusion, widened constant dependence, or substituted carrier found.

## Definition classification and attempted refutations

- `HamExpr`: free finite syntax, not a bundled assumption or conclusion-bearing structure.
- `modePhase`: intended period-one phase on the whole carrier. Imported `CertKey = List ℤ`
  denotes its first `n` entries, padding missing entries by zero; excess entries do not contribute.
  No shape premise is needed for the structural results.
- `HamExpr.eval`: exact structural denotation on every point. `/` is the field operation:
  at a zero divisor the value is zero. There is no custom conditional or alternate Hamiltonian.
  A Lean probe proves `(HamExpr.div (.const 1) (.const 0)).eval z = 0` and separately
  refutes its `NonvanishingOn Set.univ` for `n = 1`. Off-domain totalization therefore cannot
  supply the certified holomorphy premise. Design §1.1 explicitly says “`x/0 = 0` keeps both
  true even off the certified set”, so unconditional periodicity/reality are intentional.
- `HamExpr.NonvanishingOn`: concrete syntactic denominator predicate. Nested divisions in
  numerator and denominator are covered. `.pow a 0` still requires `a.NonvanishingOn S`,
  and multiplication by zero does not discard it; no pruning loophole is introduced here.
  It need not be equivalent to maximal semantic analyticity; the design deliberately requires
  every syntactic denominator, including removable ones, to be certified.
- `certDomain`: literal signed domain on all list inputs. Missing centres default to zero;
  missing radii default to zero, making the corresponding strict inequality impossible.
  Negative or zero widths/radii may yield empty domains; the structural lemmas remain valid.
  For `n = 0` the finite constraints are vacuous, consistently with the signed generality.
  These are specified data semantics, not proof-dependent junk values. Positivity and valid
  certificate shapes belong to downstream static checks, not to these structural theorems.

`ContDiffOn ℂ ⊤` is complex Fréchet smoothness, not merely real smoothness. On open `S` it
implies complex differentiability (holomorphy, hence analyticity in these finite-dimensional
complex spaces) and local `ContDiffAt ℂ 3` for the norm bridges. Both the differentiability
and local third-order consequences were elaborated in the scratch probe. The signed result
is not literally an `AnalyticOnNhd` export; none is required by this slice's contract.
The unused `hS` warning is benign: the actual within-set smoothness proof works even without
openness; retaining `hS` preserves the exact signed interface and permits local consequences.

No conclusion-shaped hypotheses or hidden theorem assumptions were found. Public helper
short names `contDiff_modePhase`, `modePhase_add_int`, `exists_real_eval` occur only in this
module across project declarations. Signed `eval_add_int` and `eval_real` share suffixes
with existing polynomial theorems under different namespaces; no new helper collision or
harmful root shadow occurs.

## Independent checks

All Lean/Lake invocations were sequential with `LEAN_NUM_THREADS=1`; all ran at nice level 5.
No source, generated root, README, frozen file, manifest, dependency package, or git state was
edited. Scratch probes were confined to `.lake/abi-scratch/` and removed after checks.

1. Full change and protected-path checks:

   ```sh
   git diff inp...HEAD
   git diff --check inp...HEAD
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   ```

   Full diff: one new 208-line module. Whitespace check exits 0; protected-path diff is empty.

2. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soexpr KAM.Certificate.Expr.Basic
   ```

   Exit 0. The gate itself invokes `nice -n 5 lake build`.

   ```text
[inp-gate] slot 1 acquired 12:40:41 for KAM.Certificate.Expr.Basic
⚠ [2896/2896] Replayed KAM.Certificate.Expr.Basic
warning: KAM/Certificate/Expr/Basic.lean:85:5: Variable name `hS` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hS

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (2896 jobs).
   ```

3. Signed-source comparison and elaborated probe:

   A Python comparison asserted exact equality of the ten declaration headers and all five
   syntax/definition bodies (including the inductive constructors). All ten printed `VERBATIM`.
   For each of the five signed theorems a fresh declaration copied its signed header and
   applied the actual export to every explicit binder, in order. Each additionally checked
   `example : type_of% @<actual export> := @<fresh signed declaration>`.
   No draft file or draft proof placeholder was imported.

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOExprAudit.lean
   ```

   Final exit 0. The initial scratch version passed a point explicitly to an implicit binder
   of `IsOpen.contDiffOn_iff`; this probe-only application was corrected and the entire probe
   rerun successfully. Production code was unchanged.
   Alongside signature and semantic checks, the probe printed axioms of every new theorem:

   ```text
'KAM.Certificate.contDiff_modePhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.contDiffOn_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modePhase_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.eval_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.exists_real_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.eval_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.isOpen_certDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certDomain_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Kernel replay, one invocation for the only new module:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Expr.Basic
   ```

   Exit 0; exact output:

   ```text
replaying KAM.Certificate.Expr.Basic
   ```

5. Repository lint (run after kernel replay, because the ABI checker itself invokes Lean):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the explicitly permitted generated-root exception. Exact output:

   ```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1297 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   ```

   No forbidden token, resource override, `EuclideanSpace`, `native_decide`, overlength line,
   or oversized-file finding in the audited module. Independent count: 208 lines, maximum
   line width 96 Unicode characters. Copyright, `module`, `public import`, module docstring,
   and `@[expose] public noncomputable section` are present.

6. Import quarantine: a recursive source-import scan visited 32 project modules. No provider
   and no DRAFT_SORRY frozen theorem was reachable. All 11 reachable frozen modules are
   SEALED definitions according to the live manifest:
   `ComplexStrip`, `DotC`, `GramMatrix`, `HamiltonianVectorFieldC`, `InvarianceError`,
   `IsPrimaryOnStrip`, `IsRealOnReals`, `NormalFrame`, `OmegaZero`, `Torsion`, `TorsionAverage`,
   all under `KAM/Frozen/Defs/`. This includes the direct frozen import `ComplexStrip`.

## Notes, uncertainties, errata and deviations

- The only build warning is the deliberately retained signed `hS` binder at line 85.
- The only lint failure is the permitted stale generated root. It was not regenerated.
- No suspected pinned-source or blueprint defect was found; no implementation deviation
  was found or introduced. The evaluation docstring's “only ever used” refers to certified
  analytic use: the unconditional structural lemmas intentionally also cover zero divisors,
  exactly as design §1.1 specifies. No change is required.
- This report certifies the Basic slice only. It does not certify denominator validation by
  future ball arithmetic, jet correctness, any downstream certificate consumer, or any frozen
  headline. In particular, preserving denominator-validation slots during later compiler
  pruning remains the separate obligation in design §1.4.

Final disposition: **PASS WITH NOTES**; no blocking finding. Only the requested audit report
was added to repository content by this auditor. All checks above were independently rerun,
not accepted from the prover's receipt.
