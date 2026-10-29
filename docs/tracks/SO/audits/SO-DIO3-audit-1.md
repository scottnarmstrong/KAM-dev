# SO-DIO3 independent package audit 1

Verdict: **PASS WITH NOTES**. Both public theorems pass; all four signed declarations are present with the exact intended names, types and definition bodies. The CubicDiophantine slice is complete. The only hygiene exception is the brief-permitted stale generated `KAM.lean` (full lint result recorded below). No frozen theorem is being sealed by this package; provider/frozen seal-copy checks are therefore inapplicable.

Audit date: 2026-10-29. Worktree: `/root/code/KAM-inp-sodio3`.
Audited HEAD: `20bb4306d00a645873380c6dd7fad34693a09d9c`.
Comparison ref `inp`: `6cad95806f4dbeafc1933f733daf875fdb3b097a`.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/SO/audits/SO-DIO3-handoff.md`. The user's exact worktree report path overrides the generic brief's MAIN-worktree output instruction. The handoff limits substantive auditing to `KAM/Certificate/CubicDiophantine.lean`.

Compared with `/root/code/KAM-inp/.drafts/design/SOSignatures.lean`, namespace `KAM.Certificate` (line 57), §J lines 1290–1305; also `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, Revision 4, F1 and §J lines 1875–1890, package allocation line 446, and `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`. There is no local SO statement file or frozen SO theorem assigned to this package. The I/N/P theorem families are not its targets.

The full `git diff inp...HEAD` contains exactly the new 183-line CubicDiophantine module. The pre-existing untracked handoff was read and left unchanged. Only this report was added outside disposable scratch files.

## Declaration review

All names in this table have prefix `KAM.Certificate`; private helpers have Lean-generated private names.

| Node / declaration | Location in `KAM/Certificate/CubicDiophantine.lean` | Verdict | Reason |
|---|---|---|---|
| §J `cbrtTwo` | 31 | PASS | Exact signed real power definition of ∛2; no parameters or fallback. |
| §J `cubicFreq` | 34 | PASS | Exact signed `Fin 3 → ℝ` vector, in the specified coordinate order. |
| §J `cubicFreq_eq_algFreq` | 36–40 | PASS | Exact coefficient lists and real input; no premises. Finite coordinate simplification proves equality with landed `algFreq`. |
| §J `cubicFreq_isDiophantine` | 149–179 | PASS | Exactly `KAM.IsDiophantine (1 / 12) 2 cubicFreq`, without extra premises, instances or parameters. |
| `cbrtTwo_cube` (private) | 42–45 | PASS | Real power identity proves x³ = 2. |
| `cbrtTwo_bounds` (private) | 47–56 | PASS | Proves 5/4 < x < 63/50 from positivity and the cube identity. |
| `norm_form_zero` (private) | 58–80 | PASS | All integer triples covered; strong induction on the sum of natAbs, parity descent halves all three coordinates. |
| `norm_ne_zero` (private) | 82–86 | PASS | Nonzero triple implies nonzero integer norm; nonzeroness is an appropriate source premise. |
| `cubic_lower` (private) | 89–147 | PASS | Proves the height lower bound for every nonzero integer triple, rather than assuming any small-divisor conclusion. |

The signed draft's unqualified `IsDiophantine` resolves to `KAM.IsDiophantine`; the implementation spells out that same constant. Thus the qualification changes no signature. Both definitions were checked by `rfl` against their signed bodies; both theorem statements were independently restated and inhabited by the exact fully qualified exports. There are no universe or implicit parameter changes.

The toy modules following these four declarations in §J belong to `Tests/*`, not SO-DIO3 (design package table). Their absence here is not a missing part of this slice. This audit does not certify a toy torus, the general checker, or a lunar confinement theorem.

## Definitions and mathematical proof

The only new top-level definitions are `cbrtTwo : ℝ` and `cubicFreq : Fin 3 → ℝ`. Both are total, intended denotations on their whole carriers. `@[expose] public section` exposes their bodies. There are no new abbreviations, structures, classes, bundled laws, or arbitrary default values. The local `x` and `Q` in `cubic_lower` are algebraic expressions, not alternate objects substituted for the signed ones.

For norm nonvanishing, the equation `a³ + 2b³ + 4c³ − 6abc = 0` first forces a even, then b even, then c even. Substitution gives the same equation for the halves. Unless the halves are all zero their natAbs sum is strictly smaller, enabling strong induction. The proof does not assume irreducibility or rational independence.

For the height bound, lines 98–103 establish the exact adjugate identity N = βQ using x³ = 2. Integrality and N ≠ 0 give 1 ≤ |N|. Lines 116–142 prove |Q| ≤ 6S² for S = |a| + |b| + |c| using x < 63/50, x² ≤ 8/5 and triangle inequalities. Nonzero integral triples give S ≥ 1, so the denominator is positive; hence 1/(6S²) ≤ |β|. There is no division by an unproved nonzero Q.

Finally use (a,b,c) = (k₂,k₀,k₁), preserving the sum of absolute values. The Fourier dot product is β/2, producing exactly 1/12 and exponent 2. `Real.rpow_two` converts the landed real-exponent definition to the square used in the helper.

The signed explanatory comment mentions the finer intermediate bound `|Q| ≤ (1 + x)²|k|₁² < 6|k|₁²`. The implementation directly proves the sufficient `≤ 6S²` bound. This is a proof-route variation, not a weakened signed theorem or an unpaid assumption. No suspected false source or blueprint statement was found.

## Independent checks

All Lean/Lake commands were run serially with `LEAN_NUM_THREADS=1` and `nice -n 5`; no heartbeat, recursion-depth or synthesis-budget override was used. No dependencies were downloaded or modified and no clean build was requested.

Targeted compile gate:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sodio3 KAM.Certificate.CubicDiophantine
[inp-gate] slot 1 acquired 14:27:26 for KAM.Certificate.CubicDiophantine
Build completed successfully (2075 jobs).
exit 0
```

Independent signature, body and axiom probe, importing only `KAM.Certificate.CubicDiophantine`:

```lean
open KAM.Certificate
example : cbrtTwo = (2 : ℝ) ^ ((1 : ℝ) / 3) := rfl
example : cubicFreq = ![cbrtTwo / 2, cbrtTwo ^ 2 / 2, 1 / 2] := rfl
example : cubicFreq = algFreq 3 [[0, 1 / 2], [0, 0, 1 / 2], [1 / 2]] cbrtTwo :=
  KAM.Certificate.cubicFreq_eq_algFreq
example : KAM.IsDiophantine (1 / 12) 2 cubicFreq :=
  KAM.Certificate.cubicFreq_isDiophantine
example : ∀ k : Fin 3 → ℤ, k ≠ 0 →
    (1 / 12 : ℝ) / (∑ i, |(k i : ℝ)|) ^ (2 : ℝ) ≤
      |∑ i, (k i : ℝ) * cubicFreq i| :=
  KAM.Certificate.cubicFreq_isDiophantine
```

Command: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SODIO3Audit.lean`; exit 0. In addition to those examples the probe printed both definitions, checked both theorem types and ran `#print axioms` on every public export. Output:

```text
def KAM.Certificate.cbrtTwo : ℝ :=
2 ^ (1 / 3)
def KAM.Certificate.cubicFreq : Fin 3 → ℝ :=
![cbrtTwo / 2, cbrtTwo ^ 2 / 2, 1 / 2]
cubicFreq_eq_algFreq : cubicFreq = algFreq 3 [[0, 1 / 2], [0, 0, 1 / 2], [1 / 2]] cbrtTwo
cubicFreq_isDiophantine : KAM.IsDiophantine (1 / 12) 2 cubicFreq
'KAM.Certificate.cbrtTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cubicFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cubicFreq_eq_algFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cubicFreq_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.CubicDiophantine
replaying KAM.Certificate.CubicDiophantine
exit 0
```

There are no separate new lemma modules to pass to replay. Private helper proof terms are included in the replayed module.

Import traversal reaches only these project modules: `KAM.Certificate.CubicDiophantine`, `KAM.Certificate.Freq`, `KAM.Frozen.Defs.IsDiophantine`. The latter's manifest state is `SEALED` (definition). No provider or `DRAFT_SORRY` theorem is imported, directly or transitively through project modules. `KAM/Frozen/Iso/Theorems/IsoenergeticKam.lean:15,73` imports and uses this same `KAM.IsDiophantine`.

Static checks: 183 lines, maximum 95 Unicode characters per line; required copyright/module/public imports/module docstring/public section present. No forbidden token, resource override, `native_decide` or `EuclideanSpace`. A source search with `rg -n '\b(cbrtTwo|cubicFreq|cubicFreq_eq_algFreq|cubicFreq_isDiophantine)\b' KAM .lake/packages/mathlib/Mathlib --glob '*.lean'` found occurrences only in this module. All public declarations are under `KAM.Certificate`; no public short name collision or harmful root shadow was found.

`git diff --check inp...HEAD`: exit 0, empty output.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output.

Full lint, after all other Lean processes had completed:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1301 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The exit 1 is solely the explicitly permitted generated-root exception; there were no other lint findings. `KAM.lean` was not regenerated. The scratch probe was deleted after checking.

## Uncertainties, errata and deviations

No mathematical or signature uncertainty remains for the assigned module. No suspected pinned-source defect or meaning-changing blueprint defect was found. The direct height-bound route described above is the only implementation variation worth recording; it preserves the signed constant and theorem. No audit-introduced code deviation, frozen edit or statement repair occurred. All build, probe, replay and lint results above are independent reruns, not copied worker receipts.

The report's overall PASS WITH NOTES records only the generated-root hygiene exception; it does not assert completion of any downstream SO theorem or seal an anchor.
