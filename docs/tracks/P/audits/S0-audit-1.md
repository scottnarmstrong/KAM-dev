# S0 independent package audit 1

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p14-s0`.
Audited HEAD: `988e2b3b5d00ed21f65b76510aa7bac8563e386c`.
Comparison: `git diff inp...HEAD`, with inp at `d9183adae208ecf2e726620694b69c8168e33006`.
Scope: only `KAM/Planetary/SecularBox/Numerics.lean`.

## Verdict

**Overall verdict: PASS WITH NOTES.** `KAM.Planetary.sb_numerics` passes statement fidelity, completeness, default-resource build, exact-type elaboration, axiom inspection and kernel replay. The sole note is the permitted stale generated `KAM.lean` lint failure. No implementation repair is required.

S0 is an ordinary library lemma, not a provider or frozen theorem. No frozen anchor is assigned to S0. Provider/frozen type equality and frozen seal-body probes are therefore not applicable. The contextual anchors `planetary.d25.secularBoxSafety.v1` and `planetary.d25.secularBoxAtCitedMasses.v1` are both `DRAFT_SORRY` in the current manifest and remain FROZEN_UNPROVED; this arithmetic certificate does not close them.

## Evidence and statement fidelity

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief, S0-handoff.md, track P statement section P-SECULAR-BOX (lines 566–667), the two contextual secular frozen theorem files, P14 design and its two design audits. The only new public declaration is:

| Node | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `bpP:p14:sb-numerics` | `KAM.Planetary.sb_numerics` | PASS | Exact closed real-rational conjunction; all 33 atomic conjuncts match blueprint N1–N7 and the source chain. |

The text between `theorem sb_numerics :` and `:=` is byte-identical in the implementation, `/root/code/KAM-inp/.drafts/design/P14Signatures.lean:386–410`, and `docs/tracks/P/design/P14-LEAN-DESIGN.md:918–942`. This is literal equality, including strictness, constants, parentheses, conjunction order and real carrier. Design node table line 214 assigns exactly this node to Numerics; package row S0 at line 386 assigns all N1–N7 and source-chain checks. No omitted node is assigned to this module.

Conjuncts are numbered left-to-right, splitting every `∧`:

| Blueprint row | Blueprint line | Conjuncts | Lean lines | Result |
|---|---:|---:|---:|---|
| N1 | 111 | 1–4 | 23–24 | PASS: both mass-ratio endpoints and both mass identities |
| N2 | 112 | 5–6 | 25 | PASS: both action-square comparisons |
| N3 | 113 | 7–8 | 26–27 | PASS: both weighted action-square comparisons |
| N4a | 114 | 9 | 28 | PASS: exact first eccentricity-square comparison |
| N4b | 115 | 10 | 29 | PASS: exact second eccentricity-square comparison |
| N4c | 116 | 11 | 30 | PASS: exact AMD sum identity |
| N5a | 117 | 12 | 31 | PASS: exact AMD/action quotient bound |
| N5b | 118 | 13–14 | 32–33 | PASS: chained equality and strict square bound both present |
| N6a | 119 | 15–18 | 34–35 | PASS: all four inner/outer axis comparisons |
| N6b | 120 | 19 | 36 | PASS: exact compact-region margin |
| N6c | 121 | 20–21 | 37 | PASS: equality and strict eccentricity-square margin |
| N6d | 122 | 22 | 38 | PASS: exact separation comparison |
| N7a | 123 | 23–24 | 39 | PASS: both radius identities |
| N7b | 124 | 25 | 40 | PASS: exact gap identity |
| N7c | 125 | 26–29 | 41–42 | PASS: equality plus all three comparisons; the source ≥ is exactly reversed as ≤ |
| N7d | 126 | 30 | 43 | PASS: pair-distance upper bound |
| Source chain | 130 | 31–33 | 44–46 | PASS: square comparison, product identity, strict AMD comparison; source > is exactly reversed as < |

All blueprint locations above are in `blueprint-P/parts/p14b-secular-box.tex`. Its parenthetical square-root implication at line 130 explains the rational check; it is not a separate rational conjunct or assigned S0 theorem. No variable action/eccentricity conclusion is claimed by this closed certificate. A separate Python `fractions.Fraction` evaluation of the 33 implemented expressions returned `Independent fractions.Fraction evaluation: 33/33 conjuncts true.` (exit 0).

### Expanded binder audit

| Binder | Classification | Source evidence |
|---|---|---|
| None (no explicit, implicit, instance or section binders) | No logical inputs | Blueprint lines 103–133 give closed rational facts; unused action notation in its prose adds no premise. |

Counts: SOURCE 0; STANDING 0; TYPING 0; RULED 0; EXCESS 0. Every scalar is ℝ; no project-owned alias, assumption bundle, witness, norm, constant-dependence issue or fallback is involved.

### Definition classification

No new `def`, `abbrev`, `structure`, instance or notation. BODY_MATCH, PUBLIC_CARRIER, WELL_DEFINEDNESS, CHARACTERIZATION and CHOICE_INDEPENDENCE: N/A (no definitions). The only proof body is `by norm_num`.

## Hygiene and independent validation

The file is 49 physical lines, below the 1500-line cap. Copyright, `module`, three `public import` commands, module docstring and `public section` are present. Imports are exactly `Mathlib.Tactic.NormNum`, `Mathlib.Basic.Real.Basic`, and `Mathlib.Tactic.Positivity`; none is a project provider or frozen theorem. Narrow imports are valid. No proof escape or resource override appears.

`rg -n '\bsb_numerics\b' KAM` returned only `KAM/Planetary/SecularBox/Numerics.lean:22:theorem sb_numerics :` (exit 0). The same word search in `.lake/packages/mathlib/Mathlib` returned no matches (exit 1). The declaration is inside `namespace KAM.Planetary`; no root declaration is introduced or shadowed.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
`git diff --check inp...HEAD`: empty, exit 0.
Initial status contained only the pre-existing untracked `docs/tracks/P/audits/S0-handoff.md`. No implementation or tracked repository file was edited by the auditor. Only this report and a temporary probe under `.lake/abi-scratch/` were written; the probe is removed after checks.

Validation commands and exact results follow. All Lean/Lake/checker invocations are serial, use `LEAN_NUM_THREADS=1` and `nice -n 5`; the build uses the required compile gate. No clean, cache download, package mutation, generated-root update or state-changing git command is used.

### Completed validation receipts

1. Targeted gated build:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s0 KAM.Planetary.SecularBox.Numerics
   ```

   Exit 0. Exact output:

   ```text
   [inp-gate] slot 1 acquired 17:53:20 for KAM.Planetary.SecularBox.Numerics
   Build completed successfully (978 jobs).
   ```

2. Exact-type and assembly probe, axiom inspection:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S0Audit1.lean
   ```

   The probe imported only `KAM.Planetary.SecularBox.Numerics`, printed axioms, copied the exact verified signature under fresh name `S0_signature_probe` with body `by exact KAM.Planetary.sb_numerics`, and elaborated:

   ```lean
   example : type_of% @KAM.Planetary.sb_numerics := @S0_signature_probe
   ```

   The signature copy has zero binders, so no application arguments are omitted. Exit 0; exact output:

   ```text
   'KAM.Planetary.sb_numerics' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   All new public theorems (one) were inspected; no `sorryAx` or project axioms.

3. Kernel replay (one invocation for the sole lemma module; no provider assigned):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Numerics
   ```

   Exit 0; complete output:

   ```text
   replaying KAM.Planetary.SecularBox.Numerics
   ```

4. Source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1; complete output:

   ```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (822 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   ```

   The only failure is the audit brief's explicitly permitted generated-root exception. Module hygiene, the frozen-anchor guard and all 144 frozen ABI checks pass. `KAM.lean` was left unchanged as required.

The temporary probe and redirected checker/lint logs were removed after copying these receipts. The implementation SHA-256 is `716b587f16668e01a1313ea94a394e290d2ba22291dbaaff69805b08a6969359`.

## Suspected defects, deviations and limits

No suspected blueprint defect or pinned-source erratum identified within S0. Blueprint decimal approximations are explicitly for orientation (lines 134–136); the audited claims use exact rational expressions. No source-PDF claim is certified here: the blueprint labels this certificate as new elementary arithmetic. No audit-introduced mathematical deviation. The source-chain square comparisons preserve exactly the design's declared rational route. The larger analytic, chart and flow obligations lie outside S0.
