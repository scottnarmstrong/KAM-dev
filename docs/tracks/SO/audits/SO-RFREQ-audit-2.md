# SO-RFREQ independent audit 2

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-sorfreq`.
Audited HEAD: `f318ec7614a8841efef1e5ff67385e59ee414f77`.
Comparison `inp`: `9fd72f92acceab80b1cb91ba74de449c0ea8b697`.

**Overall verdict: PASS WITH NOTES. The round-1 naming failure is closed.**
All six signed public declarations match Revision 6 exactly, the complete SO-RFREQ slice is
implemented, and the proofs have no added premises. The notes concern the permitted generated-root
lint exception and the boundary between this frequency interface and downstream numerical data.
There is no frozen theorem anchor or provider in this package; no anchor sealing is claimed.

## Authority and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the SO-RFREQ handoff including its
round-2 addendum, and audit 1. The user's exact worktree report destination overrides the generic
brief's MAIN-worktree destination. Audit scope is only `KAM/SpinOrbit/RotFreq.lean`;
read its dependencies to check meaning and provenance.

The SO design and signed lunar slice supply the package contract; there are no corresponding
I/N/P frozen theorem anchors or blueprint nodes to substitute for this unfrozen SO package.
Read owner ruling O5 at `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md:85-91`:
"adopt the rotated frame now", with frequency `(nu - 1, 1)`.
Revision 6's naming addendum is at
`/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md:82`.
The frequency discussion is at lines 471-479; the signed source is
`/root/code/KAM-inp-design-so/.drafts/design/SOSignaturesLunar.lean:314-342`,
inside `namespace KAM.SpinOrbit` (line 237).

At final verification, that signature and the handoff's copy at
`/root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean` are byte-identical, SHA256
`f898ee080a52c631387764a2b7d1ab18e2df79b50442b18e5e05aa43f3209c6c`.
The MAIN copy initially retained the old name and was synchronized externally during the audit.
The auditor edited neither copy. The design worktree's prose also had external changes;
the reviewed signed bytes above identify the exact declaration authority.

The full `git diff inp...HEAD` contains exactly three files: RotFreq (81 added lines), audit 1
(201), and the handoff (33). Its only Lean change is the scoped module.
Compared with round-1 implementation `eab2bb8b`, the entire current module is exactly the result
of replacing every `isDiophantine_smul` token by `soIsDiophantine_smul`, including its docstring
and the two callers. No type, premise, constant, or proof step changed.

## Declaration review

All public names below have prefix `KAM.SpinOrbit`. Header comparisons against the revised signed
source are byte-for-byte, including all binders and their order; the definition declaration and
body are byte-identical too. Fresh Lean declarations copied from those headers elaborate by
applying the corresponding export to exactly its explicit binders in order.

| Node / RotFreq line | Declaration | Verdict | Reason |
|---|---|---|---|
| SO-RFREQ / 28 | `lunarRotFreq` | PASS | Total intended `κ (ν - 1, 1)` on `ℝ × ℚ`, carrier `Fin 2 → ℝ`. |
| SO-RFREQ / 35 | `lunarRotFreqMinus_eq` | PASS | Exact signed coefficient list `[[-79 * κ / 3118, κ / 3118], [κ]]`; no added premise. |
| SO-RFREQ / 42 | `lunarRotFreqPlus_eq` | PASS | Exact signed coefficient list `[[79 * κ / 3118, -κ / 3118], [κ]]`; no added premise. |
| SO-RFREQ / 50 | `soIsDiophantine_smul` | PASS | Revised signed name; same arbitrary-dimensional positive scaling, constant `t * γ`. |
| SO-RFREQ / 67 | `lunarRotFreqMinus_isDiophantine` | PASS | Exactly `κ/42`, exponent 1, sole premise `0 < κ`; uses SO-ROTDIO minus theorem. |
| SO-RFREQ / 74 | `lunarRotFreqPlus_isDiophantine` | PASS | Same signed constant and premise; uses SO-ROTDIO plus theorem. |
| Internal / 30 | private `algFreq_two'` | PASS | Correct finite polynomial evaluation identity; no extra public surface. |
| Internal / 61 | private `lunarRotFreq_eq_smul` | PASS | Correct coordinatewise vector/scalar identity. |

No signed declaration is missing. No weakened conclusion, wider constant dependence, changed
carrier, conclusion-shaped premise, assumed proof step, or bundled substitute was found.

## Definition classification and mathematical checks

The only new definition is `lunarRotFreq`. Its body is exactly
`![(κ : ℝ) * (ν - 1), κ]` for every real `ν` and rational `κ`, including zero and negative
`κ`; there is no fallback or junk region. There are no new structures, instances, or abbreviations.
The positivity hypotheses occur only in the signed scaling and Diophantine statements.

`QuadraticDiophantine.lean:32-35,58-62` defines and identifies the landed `ν±`.
Subtracting 1 gives `ν₋ - 1 = (-79 + √5)/3118` and
`ν₊ - 1 = (79 - √5)/3118`. The coefficient lists therefore describe the exact rotated
vectors, scaled by `κ`, with second coordinate exactly `κ`. They do not encode the older
half-frequency vectors. The equalities hold for all rational `κ`.

The scaling proof pulls `t` out of the finite dot product, uses `|t| = t`, and multiplies the
original inequality by positive `t`. It needs no unlisted positivity assumption on `γ` or `τ`,
and works at all dimensions. The lunar proofs use precisely
`KAM.Certificate.lunarNuMinus_rot_isDiophantine` and
`KAM.Certificate.lunarNuPlus_rot_isDiophantine` from SO-ROTDIO
(`DiophantineTransfer.lean:106-116`), at constant `1/42` and exponent 1.

Both rational-box interfaces were freshly elaborated: if `(lo : ℝ) ≤ √5 ≤ hi` and
`checkAlgBox 2 <the signed coefficient list> lo hi box = true`, rewriting by the appropriate
`_eq` theorem and applying `algFreq_encloses` proves
`FreqEncloses 2 box (lunarRotFreq lunarNu± κ)`.
No actual lunar box, numerical radius bound, or final certificate is present in this signed
slice; those remain SO-DATA obligations. This verifies the exact enclosure interface and does
not claim a concrete numerical certificate or confinement theorem.

## Naming and import hygiene

An independent source scan masked comments/strings using `scripts/check_lean_modules.py`'s
`code_mask`, then scanned declaration names across all `KAM/**/*.lean` and
`.lake/packages/mathlib/Mathlib/**/*.lean`, without signature exemptions. Each of the six public
short names occurs as a declaration only at its intended line in RotFreq. In particular,
`soIsDiophantine_smul` has no collision with `KAM.Iso.Linear.isDiophantine_smul`.
All exports remain in `KAM.SpinOrbit`; there is no root declaration, alias, or harmful root shadow.

The local KAM import closure is exactly RotFreq, SpinOrbit.Freq, Certificate.Freq,
Certificate.DiophantineTransfer, Certificate.QuadraticDiophantine, and
Frozen.Defs.IsDiophantine. The sole frozen import is the definition `KAM.IsDiophantine`,
manifest state `SEALED`. There is no provider or frozen theorem import, and no DRAFT_SORRY anchor.
The module has 81 lines, maximum 97 Unicode characters per line, correct copyright/module/import/
docstring/public-section structure, and an exposed definition body. A direct source scan finds
no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace`, or `set_option`.

## Independent checks

All Lean/Lake/kernel invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No cache update, dependency modification, generated-file rewrite, or state-changing Git was run.

```text
git diff --stat inp...HEAD
 KAM/SpinOrbit/RotFreq.lean                |  81 ++++++++++++
 docs/tracks/SO/audits/SO-RFREQ-audit-1.md | 201 ++++++++++++++++++++++++++++++
 docs/tracks/SO/audits/SO-RFREQ-handoff.md |  33 +++++
 3 files changed, 315 insertions(+)

git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
[empty; exit 0]
git diff inp...HEAD --check
[empty; exit 0]

LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sorfreq KAM.SpinOrbit.RotFreq
[inp-gate] slot 1 acquired 15:13:22 for KAM.SpinOrbit.RotFreq
Build completed successfully (2199 jobs).
exit 0

LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SORFreqAudit2.lean
'KAM.SpinOrbit.lunarRotFreqMinus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqPlus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soIsDiophantine_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqMinus_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqPlus_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0

LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.RotFreq
replaying KAM.SpinOrbit.RotFreq
exit 0

python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sorfreq KAM.SpinOrbit.RotFreq
short-name check OK (no reused public short name)
exit 0
```

The scratch probe contained all five copied signed theorem headers with explicit-binder export
applications, five `example : type_of% @signed_<name> := @KAM.SpinOrbit.<name>` comparisons,
a definition-body `rfl` check, both enclosure applications, and the six `#print axioms` commands
whose full outputs appear above. Frozen seal-copy probes are inapplicable because this package
has no anchor/provider pair. The shared name checker result is corroborated by the independent
scan, avoiding the signature-exemption limitation found in audit 1.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1315 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

Lint's sole diagnostic is the brief's explicitly permitted generated-root staleness.
No substantive lint failure was found. `KAM.lean` was left untouched.

## Errata, deviations, and handoff

No suspected mathematical source, blueprint, or frozen-statement defect was found in the scoped
frequency package. The naming conflict documented in audit 1 is resolved by the coordinated
Revision 6 signature and implementation rename. The initially stale MAIN signature copy was
externally synchronized and is no longer a discrepancy. The handoff's round-2 addendum controls
its historical references to the old name. No deviation was introduced by this audit.

Remaining scope limits: no concrete lunar numerical box or final certificate was checked, no
frozen anchor was sealed, and no downstream barrier/confinement theorem is certified here.
These are outside the complete signed SO-RFREQ slice.

Only this report was added by the auditor. The temporary Lean probe was confined to
`.lake/abi-scratch/SORFreqAudit2.lean` and deleted after validation. Final checks:
`git diff --check` and `git diff --no-index --check /dev/null
/root/code/KAM-inp-sorfreq/docs/tracks/SO/audits/SO-RFREQ-audit-2.md` both exit 0;
the probe is absent, HEAD is unchanged, and Git status contains only this new untracked report.
