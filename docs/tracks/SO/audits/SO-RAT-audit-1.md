# SO-RAT independent audit 1

Overall verdict: **PASS WITH NOTES**. Both signed instances PASS; the assigned rational-backend slice is complete. The note is the expressly permitted stale generated `KAM.lean` lint failure. There is no frozen theorem anchor or provider in this package, hence no frozen seal to approve. This verdict does not approve SO-REPLAY or the lunar certificate.

Audited checkout: `/root/code/KAM-inp-sorat`, HEAD `9682cf5c737968f0d5bd8af897057de8acb76e02`. Compared the full `git diff inp...HEAD`: exactly one added file, `KAM/Certificate/Arith/Rat.lean`, 82 lines. The handoff was already untracked on entry. Only this report and the subsequently deleted audit scratch probe were written by the auditor. The explicit user report destination overrides the generic brief's main-worktree destination.

## Authority and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/SO/audits/SO-RAT-handoff.md`. Applied the handoff's narrower AUDIT FOCUS: audit only `Rat.lean`, using dependencies for interface context. Compared `/root/code/KAM-inp/.drafts/design/SOSignatures.lean:125–135` (namespace at line 57) and Revision 4 `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, §5 and Appendix A Backends, especially lines 710–720. Consulted `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md` for project scope.

The signed surface is precisely `KAM.Certificate.instCertArithRat : CertArith ℚ` and `KAM.Certificate.instLawfulCertArithRat : LawfulCertArith ℚ`, with the latter using the former instance. Both names and types match exactly. No added binder or premise. Fixed-point arithmetic, production backend selection, and production replay belong to other slices. Frozen I/N/P theorem signatures and track blueprint nodes are not implemented by this file; their seal-copy tests are inapplicable here.

## Declaration and law review

| Node / locator in Rat.lean | Lean declaration | Verdict | Reason |
|---|---|---|---|
| SO-RAT, 25–40 | `KAM.Certificate.instCertArithRat` | PASS | Exact signed name and type; all 15 fields implement total exact rational operations. |
| SO-RAT, 42–57 | `KAM.Certificate.instLawfulCertArithRat` | PASS | Exact signed name and type; all 12 laws proved, no external premise. |
| 43 | `val_ofInt` field | PASS | Integer-to-rational-to-real cast agrees with integer-to-real cast. |
| 44 | `ofRatUp_ge` field | PASS | Identity rational conversion, real inequality is reflexive. |
| 45 | `ofRatDown_le` field | PASS | Identity rational conversion, real inequality is reflexive. |
| 46 | `add_err` field | PASS | Rational cast preserves addition; absolute error and bound both zero. |
| 47 | `val_neg` field | PASS | Cast preserves negation. |
| 48 | `mul_err` field | PASS | Cast preserves multiplication; absolute error and bound both zero. |
| 49 | `val_abs` field | PASS | Rational absolute value casts to real absolute value. |
| 50 | `upAdd_ge` field | PASS | Exact addition yields equality, for all signed inputs. |
| 51 | `upMul_ge` field | PASS | Exact multiplication yields equality for all inputs; the interface's two nonnegativity premises are unused because this backend proves a stronger fact. |
| 52–53 | `ble_sound` field | PASS | Extracts the actual rational `≤` decision and transfers it through the cast. |
| 54–55 | `blt_sound` field | PASS | Extracts the actual rational `<` decision and transfers it through the cast. |
| 56–57 | `beq_sound` field | PASS | Extracts the actual rational equality decision and substitutes equal operands. |
| 59–60 | anonymous example 1 | PASS | `1/3 + 1/6 ≤ 1/2` returns true. |
| 62–63 | anonymous example 2 | PASS | False control: `1/3 + 1/3 ≤ 1/2` returns false. |
| 65–66 | anonymous example 3 | PASS | `(2/3)(3/4) < 1` returns true. |
| 68–69 | anonymous example 4 | PASS | `2 + -(4/2) = 0` returns true. |
| 71–72 | anonymous example 5 | PASS | Small complex exponential domain check returns true. |
| 74–76 | anonymous example 6 | PASS | Machin `(20,5)` midpoint / full half-width enclosure returns true. |
| 78–80 | anonymous example 7 | PASS | False control: midpoint / quarter-width enclosure returns false. |

The law fields are implementations of existing class projections, not newly declared helpers. Both comparison antecedents can hold for concrete inputs; none of the laws is made vacuous by an always-false backend comparison. `upMul_ge` is valid even without its interface sign hypotheses. Every anonymous example was copied verbatim, renamed solely for axiom printing, and independently re-elaborated with `decide +kernel` at default resource settings.

## Definition classification and imports

There are no new `def`, `abbrev`, or `structure` declarations. The data instance is the only new data definition: `val` is the usual rational-to-real cast; `ofInt` the integer cast; both rational conversions the identity; addition, negation, multiplication and absolute value the standard rational operations; error functions identically zero; upward operations exact addition and multiplication; comparisons actual decidable rational relations. These bodies describe the intended object on the entire carrier `ℚ`, including negative inputs. There are no junk branches or fallbacks. The lawful instance is a proof-valued record of these same operations' laws, not an assumed soundness oracle.

The complete transitive project import closure is `Rat`, `PiEnclosure`, `Roots`, `Interface`, `PiHigh`. No provider or frozen module occurs, hence no DRAFT_SORRY dependency or imported frozen manifest state to resolve. No other KAM source uses either new instance short name; no public helper, root declaration, or harmful root shadow was introduced. Definitions are in `KAM.Certificate`, under `@[expose] public section`.

## Independent checks

All Lean/Lake commands ran sequentially, with `LEAN_NUM_THREADS=1` and `nice -n 5`; lint inherited both settings for its ABI Lean subprocess. No library clean, update, cache fetch, generated-file edit, frozen edit, or state-changing git operation was performed.

### Targeted build — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sorat KAM.Certificate.Arith.Rat
```

```text
[inp-gate] slot 1 acquired 12:41:52 for KAM.Certificate.Arith.Rat
⚠ [2840/2843] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one
✔ [2843/2843] Built KAM.Certificate.Arith.Rat (4.6s)
Build completed successfully (2843 jobs).
```

The omitted warning hint suggests removing that unused argument; it is in an unchanged dependency, not Rat.lean. No resource override was used and no heartbeat failure occurred.

### Exact types, operation bodies, examples, and axioms — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/so_rat_audit.lean
```

The deleted scratch probe is reproduced below to make the check reviewable:

```lean
import KAM.Certificate.Arith.Rat
open KAM.Certificate KAM.Certificate.CertArith
example : CertArith ℚ := KAM.Certificate.instCertArithRat
example : @LawfulCertArith ℚ KAM.Certificate.instCertArithRat :=
  KAM.Certificate.instLawfulCertArithRat
example : type_of% @KAM.Certificate.instCertArithRat :=
  (show CertArith ℚ from KAM.Certificate.instCertArithRat)
example : type_of% @KAM.Certificate.instLawfulCertArithRat :=
  (show @LawfulCertArith ℚ KAM.Certificate.instCertArithRat from
    KAM.Certificate.instLawfulCertArithRat)
example (q : ℚ) : val q = (q : ℝ) := rfl
example (q : ℚ) : ofRatUp (α := ℚ) q = q := rfl
example (q : ℚ) : ofRatDown (α := ℚ) q = q := rfl
example (a b : ℚ) : addErr a b = 0 ∧ mulErr a b = 0 := ⟨rfl, rfl⟩
example (a b : ℚ) : upAdd a b = a + b ∧ upMul a b = a * b := ⟨rfl, rfl⟩
#print axioms KAM.Certificate.instCertArithRat
#print axioms KAM.Certificate.instLawfulCertArithRat
theorem auditExample1 : ble (upAdd (ofRatUp (α := ℚ) (1 / 3)) (ofRatUp (1 / 6))) (ofRatUp (1 / 2)) = true := by
  decide +kernel

theorem auditExample2 : ble (upAdd (ofRatUp (α := ℚ) (1 / 3)) (ofRatUp (1 / 3))) (ofRatUp (1 / 2)) = false := by
  decide +kernel

theorem auditExample3 : blt (upMul (ofRatUp (2 / 3 : ℚ)) (ofRatUp (3 / 4))) (ofInt (α := ℚ) 1) = true := by
  decide +kernel

theorem auditExample4 : beq (add (ofInt (α := ℚ) 2) (neg (ofRatDown (4 / 2)))) (ofInt 0) = true := by
  decide +kernel

theorem auditExample5 : certCExpSmall (⟨1 / 4, 1 / 4⟩ : CC ℚ) (1 / 4) = true := by
  decide +kernel

theorem auditExample6 : checkPiEnclosure (α := ℚ) ⟨(piLowRat 20 5 + piUpRat 20 5) / 2,
    (piUpRat 20 5 - piLowRat 20 5) / 2, 20, 5⟩ = true := by
  decide +kernel

theorem auditExample7 : checkPiEnclosure (α := ℚ) ⟨(piLowRat 20 5 + piUpRat 20 5) / 2,
    (piUpRat 20 5 - piLowRat 20 5) / 4, 20, 5⟩ = false := by
  decide +kernel

#print axioms auditExample1
#print axioms auditExample2
#print axioms auditExample3
#print axioms auditExample4
#print axioms auditExample5
#print axioms auditExample6
#print axioms auditExample7
```

Exact output:

```text
'KAM.Certificate.instCertArithRat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.instLawfulCertArithRat' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditExample1' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditExample2' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditExample3' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditExample4' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditExample5' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditExample6' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditExample7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Arith.Rat
```

Exact output:

```text
replaying KAM.Certificate.Arith.Rat
```

One invocation covers the sole new module; there is no separate lemma module in the diff.

### Source and protected-path checks

`git diff --check inp...HEAD` exited 0 with no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` was empty. `git diff --exit-code HEAD -- KAM/Certificate/Arith/Rat.lean KAM/Frozen manifest KAM.lean README.md` exited 0 with no output.

An independent Python scan found 82 lines, maximum line length 100 Unicode characters, and no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace`, or `set_option` in Rat.lean. Module header, copyright, public imports, module docstring, public section, and namespace all satisfy the repository rules.

### Full source lint — exit 1, permitted generated-root exception only

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1296 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The brief expressly permits the generated-root notice. Root regeneration remains the orchestrator's task; this audit left the generated file unchanged. No other lint failure appeared.

## Uncertainties, suspected defects, and deviations

No suspected SO-RAT source or blueprint defect, no added premise, and no implementation deviation found. The declarations complete precisely the exact-rational pre-gate backend assigned by Revision 4. No source erratum is asserted by this audit.

The `(20,5)` enclosure examples establish kernel computability for those inputs only. Production `(50,15)` replay, performance at production coefficient sizes, fixed-point selection, and final certificate soundness remain outside SO-RAT and were not tested or approved. The existing PiHigh unused-simp warning and stale generated root are the only validation notes. Dependency correctness beyond what the instance laws, axiom inspection and requested kernel replay establish was not separately re-audited.

Final cleanup removed `.lake/abi-scratch/so_rat_audit.lean`. Only the requested report is an auditor-created repository artifact. Final `git diff --check` checks passed.
