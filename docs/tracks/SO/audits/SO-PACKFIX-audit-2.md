# SO-PACKFIX independent audit 2

Date: 2026-10-30. Worktree: `/root/code/KAM-inp-sopackfixl`.
Audited HEAD: `5f3f6bb3f5070dea14f3def12522516e7e8ee423`.
Baseline `inp`: `c2a97537297a510507b081cc3a2089a6d239906e`.
Round-1 audited HEAD: `88696cfe32d70f1e4c5e6e44aa0f25556470ede7`.
Fix: `2b01c348f7a963538fcbf681ca4f50587401db2d`.

## Verdict

**PASS for round-1 F1; package PASS WITH NOTES.** Both missing compatibility exports are
restored with exactly their original names, binders, types, and bodies. All **130** original
public declarations of `Poly/{Packed,Advice,MulPacked}.lean` are now present with identical
source headers. No blocking finding remains in this delta audit.

The notes are the permitted stale generated root, round-1 N2's decoder-domain/documentation
qualifications, and N3's unreplicated performance measurements. N1's requested `spPack`
docstring correction is resolved; its guarded-domain qualification still applies.
This is an implementation-package verdict, not the sealing of a new frozen I/N/P anchor or
certification of a lunar numerical certificate.

| Node / declaration | Verdict | Reason |
|---|---|---|
| `Packed.lean:119`, `KAM.Certificate.packShiftAux` | PASS | Exact original header and recursive body restored; resolves from an importing client. |
| `Packed.lean:125`, `KAM.Certificate.packShiftAux_eq` | PASS | Exact original statement and proof restored; original explicit argument order elaborates. |
| `Sparse.lean:69–75`, `KAM.Certificate.spPack` | PASS | N1 docstring now explicitly states `base ≤ e.1` for every term; body unchanged. |
| All 130 original public declarations in Packed/Advice/MulPacked | PASS | Fresh source-header comparison and 129 exact-old-type elaboration examples; full `PackedAdvice` record identical. |
| `packShift_eq`, `intSlotsBound_sound` | PASS | No round-2 body or statement change; fresh builds/replay/axioms checked. |
| `checkPackedProduct_sound`, `CertPoly.mulPacked_sound`, `checkTorusCertificate_sound` | PASS | Round-1 soundness verdict retained; fresh replay and standard axioms confirmed. |
| `checkPackedSp_dense`, `packedRealProduct_sound` | PASS | Sparse bridge and consumer unchanged from round 1; rebuilt/replayed. |
| Frozen anchors / provider seals | N/A | None changed or introduced. |

## Scope and delta isolation

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied package audit brief,
the round-1 report, and the complete handoff including AUDIT FOCUS and Round 2.
Compared `git diff inp...HEAD` and isolated `git diff 88696cfe...HEAD`. Also consulted the
SO design §B′ and its F12–F14 guard contracts. The user explicitly permits a delta audit;
the round-1 declaration classifications and soundness review are retained for unchanged code.
Provider/frozen-type and seal-body probes do not apply to this infrastructure-only delta.
The user's exact worktree report destination overrides the generic brief's main-worktree path.

The full baseline diff touches five Lean files. The entire round-2 Lean delta is:

- `Poly/Packed.lean`: 27 added lines restoring the two declarations and explanatory docstring.
- `Poly/Sparse.lean`: four added / three removed comment lines documenting the precondition.

The other round-2 files are the round-1 report and nine added handoff lines. No other source
changed. A code-mask comparison, after removing the restored declarations, confirms identical
executable token sequences in Packed and Sparse against the round-1 HEAD. Advice, MulPacked,
and Tests/Packed are byte-identical to that HEAD (`git diff --exit-code` returned 0).
The balanced `packShift` body remains in use; restoration does not redirect it to the linear loop.

Definition classification: `packShiftAux` is a total recursive linear signed packing loop on
all widths, shifts, integer lists, and natural positive/negative accumulators. The empty case
returns their signed difference; each nonempty case adds the appropriately shifted signed part.
Its unconditional original theorem proves the whole-carrier specification
`(p : ℤ) - n + 2 ^ s * packSum w cs`. No default, new premise, instance, or bundled field was
introduced. The theorem proof is also byte-identical to `inp`. No other definition is added in
round 2. The `spPack` comment makes an existing proved precondition explicit; it adds no hypothesis
to any theorem and changes no fallback behavior.

## Public interface verification

A scratch Python inventory used `scripts/check_lean_modules.py`'s code mask to locate every
public `def`, `theorem`, `abbrev`, and `structure` in the three modules. Headers stop before
`:=`, recursive equation clauses, or `where`; their original source text was compared exactly.
The complete `PackedAdvice` record was separately compared, including all six fields.
Both restored declaration texts, including bodies, were separately compared byte for byte.

```text
Packed: 28 original headers identical; 46 current declarations
packShiftAux: body and header byte-identical to inp
packShiftAux_eq: body and header byte-identical to inp
Advice: 66 original headers identical; 71 current declarations
PackedAdvice complete record identical
MulPacked: 36 original headers identical; 40 current declarations
129 exact-old-header elaboration examples generated
```

For each non-structure original declaration the generated probe abstracts its exact original
binders over its original result type, then assigns `@<current export>`. It imports
`KAM.Certificate.Poly.MulPacked`, opens `KAM CertArith`, and uses namespace `KAM.Certificate`.
The two restored exports are included. An additional probe checks both fully qualified names,
applies `packShiftAux_eq w cs s p n` in the original order, proves the zero-accumulator equality
with balanced `packShift` for all widths and lists, and kernel-decides nonzero-shift/zero-width
signed packing and empty-list cases.

## Fresh validation receipts

All Lean/Lake commands ran sequentially with `LEAN_NUM_THREADS=1`. All builds used the compile
gate below (which executes `nice -n 5 lake build`); probes, replay, and lint used `nice -n 5`.
Lint was serialized too because its ABI check invokes Lean. No resource-budget override was used.
No clean build or dependency update was performed.

### Targeted builds

Each module was run separately, all exit **0**:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-sopackfixl <Module>
```

| Module | Exact success output |
|---|---|
| `KAM.Certificate.Poly.Packed` | `Build completed successfully (2903 jobs).` |
| `KAM.Certificate.Tests.Packed` | `Build completed successfully (2915 jobs).` |
| `KAM.Certificate.Poly.Advice` | `Build completed successfully (2905 jobs).` |
| `KAM.Certificate.Poly.Sparse` | `Build completed successfully (2907 jobs).` |
| `KAM.Certificate.Poly.MulPacked` | `Build completed successfully (2911 jobs).` |
| `KAM.Certificate.Tests.Negative` | `Build completed successfully (3251 jobs).` |
| `KAM.Certificate.Soundness` | `Build completed successfully (3318 jobs).` |

The existing warnings concern `Arith/PiHigh.lean:218` (unused simp argument),
`Expr/Basic.lean:85` (unused variable), `Sound/Static.lean:99,152` and `Sound/Ham.lean:68`
(unused section variables). No changed proof warned and no warning-suppression option was set.
Tests/Packed includes the sparse positive/bridge/rejection tests and the P2–P5 guard regressions;
it is unchanged from round 1 and was included in the fresh build and replay.

### Import, exact-type and axiom probes

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/so-packfix-r2/Signatures.lean
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/so-packfix-r2/Axioms.lean
```

Both final exits **0**. The 129-example signature probe emits only scratch unused-binder
warnings (336), with no errors. The axiom/helper probe emits exactly:

```text
KAM.Certificate.packShiftAux (w : ℕ) : ℕ → List ℤ → ℕ → ℕ → ℤ
KAM.Certificate.packShiftAux_eq (w : ℕ) (cs : List ℤ) (s p n : ℕ) :
  KAM.Certificate.packShiftAux w s cs p n = ↑p - ↑n + 2 ^ s * KAM.Certificate.packSum w cs
'KAM.Certificate.packShiftAux_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packShift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.intSlotsBound_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedSp_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedProduct_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.mulPacked_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All kernel-decided helper examples passed. No nonstandard axiom or `sorryAx` appeared.
The initial generated signature probe mistakenly treated a line beginning with absolute-value
notation as a recursive equation clause, truncating two result types and producing two syntax
errors. I corrected the audit generator to recognize equation clauses with `=>`, regenerated
all examples and the full header inventory, and reran successfully. No package source was changed.

### Kernel replay

One invocation, exit **0**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Certificate.Poly.Packed KAM.Certificate.Poly.Advice \
  KAM.Certificate.Poly.Sparse KAM.Certificate.Poly.MulPacked \
  KAM.Certificate.Tests.Packed KAM.Certificate.Tests.Negative \
  KAM.Certificate.Soundness
```

Exact output:

```text
replaying KAM.Certificate.Soundness
replaying KAM.Certificate.Tests.Negative
replaying KAM.Certificate.Tests.Packed
replaying KAM.Certificate.Poly.MulPacked
replaying KAM.Certificate.Poly.Sparse
replaying KAM.Certificate.Poly.Advice
replaying KAM.Certificate.Poly.Packed
```

### Lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with only the explicitly permitted generated-root exception:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1394 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Thus lint is **PASS WITH NOTES**, not an exit-zero pass. The generated root was left untouched.
Module hygiene, the frozen-anchor guard, and all 144 frozen declaration ABI hashes passed.

### Protected paths, module form and sizes

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
git diff --check
```

Each exit **0**, empty output. File sizes and maximum Unicode line widths:

| Changed Lean file | Lines | Maximum columns |
|---|---:|---:|
| `Poly/Packed.lean` | 651 | 99 |
| `Poly/Advice.lean` | 711 | 100 |
| `Poly/MulPacked.lean` | 535 | 98 |
| `Poly/Sparse.lean` | 478 | 99 |
| `Tests/Packed.lean` | 417 | 100 |

All meet the 1500-line and 100-column limits. Both round-2 modules retain the copyright,
`module`, public interface imports, module docstring, and `@[expose] public section`.
The restored definition is in that exposed public section. A forbidden-token search of the two
round-2 Lean modules found no escapes, resource overrides, provider imports or forbidden carrier.

## Source defects, deviations and retained limits

No new suspected pinned-source, blueprint, or frozen-statement defect was found. F1 was an
implementation-interface deviation and is fixed. N1's documentation now states the existing
lower-slot guard. Round-1 N2 remains: decoder acceptance need not match the old Boolean outside
its production guard, and Packed's “64 levels suffice for any list/length” wording is a practical
expectation, not a theorem for unbounded naturals; the proved fallbacks ensure correctness.
N3 remains: the data-bearing worker benchmark and CPU-hour projection were not independently
reproduced. The disclosed balanced dense-window implementation and dense fallback remain as
reviewed in round 1. This delta adds no analytic claim and changes no anti-carry or raw-length guard.

Repository edits are limited to this exact report. Scratch probes and logs were kept under
`.lake/abi-scratch/so-packfix-r2/` and removed after recording the receipts. No state-changing git
command, frozen edit, generated-file repair, or production-source repair was performed.
