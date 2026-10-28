# Independent package audit: N2-ZFIELD

Overall verdict: **PASS WITH NOTES**. All four infrastructure declarations pass. The only validation exception is the explicitly permitted stale generated `KAM.lean`. No mathematical or statement-fidelity defect was found.

## Scope and authority

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-n2z`.
HEAD: `ac46498bcb3b76c9d52a9689cd232172823d0eec`.
Compared `inp`: `25f3d65bb0d5a30674a6e5286c44befb321e7e9d`, using `git diff inp...HEAD`.
The entire branch delta is one added file, `KAM/Nekhoroshev/QcZero/ZeroField.lean` (85 lines).
Its SHA-256 is `06645db61b0435ac0d4f26ede567638095719932f222f09034d02c147035c4f6`.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package-audit brief, the worktree handoff and its AUDIT FOCUS,
the N2 design and its independent design audit, the original N2Signatures draft, the relevant Part-2
blueprint and track-N statement, the frozen N-ZERO anchor and its analytic/domain/field definitions,
and the reused domain, setting and holo-real interfaces. The signature draft and design audit are located
in `/root/code/KAM-inp`, respectively `.drafts/design/N2Signatures.lean` and
`docs/tracks/N/design/DESIGN-N2-design-audit-1.md`; they are not present at the handoff's implied local paths.
The report destination follows the user's explicit worktree path, overriding the generic brief's MAIN-path instruction.

**Frozen anchors:** none newly proved or sealed by this package. N-ZERO (`zero_perturbation`) is already
sealed in the baseline; its all-time orbit conclusion is outside this module's deliverables. Provider/frozen
ABI equality and fresh seal-body probes are therefore not applicable. This audit passes the zero-field
infrastructure; it does not claim another frozen closure.

## Declaration ledger

Names below are in `KAM.Nekhoroshev`; implementation locators are in ZeroField.lean.

| Node | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `stepN:p2:zd-zero` | `zd_zero`, L36–42 | PASS | Complex vanishing, real inclusion and Hamiltonian equality on the whole Wdom; exact design signature. |
| `stepN:p2:zd-diff` | `zd_diff`, L44–61 | PASS | Genuine HasFDerivAt with the composed action derivative at every Wdom point; frozen C³ is consumed directly. |
| `stepN:p2:zd-field` | `zd_field`, L63–70 | PASS | Correct frozen field `(frequencyMap h z.2, 0)`, with angles first and the negative angle derivative in the action component. |
| `bpN:p2:zero-deriv` | `zero_deriv`, L72–81 | PASS | All four blueprint clauses: equality, differentiability, derivative on arbitrary `(a,b)`, and field formula on Wdom. |

The blueprint authority is `blueprint-N/parts/p2-qc-zero.tex:69–79`, SHA-256
`ed9954f4a8313436ba58be47d1f061022b49cdf3ad04ba72b0c9467412dce73d`.
The draft authority is original N2Signatures.lean:136–165, SHA-256
`6f0af532d88555f0dd089b07298270823eecafd6d46efa540eeda7f8ef87a57a`.
All four theorem headers are text-identical to that draft; section variables and `include hR hs hh hf`
also agree. A disposable probe copied those exact declarations under fresh names and replaced each
body with `by exact KAM.Nekhoroshev.<name> hR hs hh hf` (plus `z hz` where present). All elaborate.
There is no changed binder, extra dimension bound, conclusion premise, norm, constant dependence or weakened domain.
`zd_diff`'s HasFDerivAt packaging supplies the blueprint's differentiability and derivative identity.

## Refutation checks and definitions

- At L39, `Data n R s 0 h f` is assembled from exactly the four existing source premises. Its fields are
  positivity of R and s and the two frozen analytic predicates; no field assumes a zero-field conclusion.
- `holo_real_e` obtains `f = 0` from the literal pointwise norm bound at size zero and supplies equality
  throughout Wdom. L41 uses the existing preimage-domain equality, so membership is not restricted to B(0,R).
- At L48–52, Wdom membership yields action membership in the real action domain via
  `realActionDomain_eq`. The frozen `IsAnalyticIntegrable` final conjunct is
  `ContDiffOn ℝ 3 (realPart h) (realActionDomain n R s)`; L51 consumes exactly this conjunct.
- The domain is open. L57–61 transfer a derivative using equality on an entire neighborhood, not merely
  equality at the point. Thus no junk total `fderiv` value is used to manufacture differentiability.
- L66–70 evaluate the genuine derivative on the frozen coordinate vectors. Action derivatives give
  frequency; angle derivatives vanish. The product order and Hamiltonian sign are correct.
- L79–81 package existing proved receipts without assuming any difficult step. All dimensions, including
  n=0, are retained. No quasi-convexity, nonzero frequency, derivative bound or ODE premise is introduced.

**New definitions classification:** no new `def`, `abbrev`, `structure`, instance or notation.
The reused `realPart`, `realHamiltonian`, `frequencyMap` and `hamiltonianVectorField` are the literal
frozen objects. Existing Wdom is `univ ×ˢ ball 0 (R+s)`; Data is the four-premise bundle described above.
All real and complex carriers are Fin-function spaces with their existing norms. No fallback is introduced.

## Independent validation receipts

Every Lean/Lake invocation was serial, with `LEAN_NUM_THREADS=1` and niceness 5. The build used the
prescribed gate; no clean, update, cache operation, source repair or generated-root regeneration occurred.
The lint subprocess inherits the same thread limit and niceness.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n2z KAM.Nekhoroshev.QcZero.ZeroField
   [inp-gate] slot 2 acquired 07:02:25 for KAM.Nekhoroshev.QcZero.ZeroField
   Build completed successfully (2895 jobs).
   exit 0
   ```

2. Exact-design application probes and axioms:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N2ZFieldAudit.lean
   'KAM.Nekhoroshev.zd_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.zd_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.zd_field' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.zero_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0; no warnings or errors
   ```

3. Kernel replay of the sole delivered lemma module (no provider module exists in this package):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.QcZero.ZeroField
   replaying KAM.Nekhoroshev.QcZero.ZeroField
   exit 0
   ```

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (440 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1 (sole failure: permitted stale generated root)
   ```

5. Static hygiene and integrity:

   - All 32 transitive project modules were traversed from the new module's imports: no provider or
     frozen theorem module is imported. Thus no DRAFT_SORRY theorem is imported; there is no imported
     frozen theorem whose manifest seal status must be relied upon.
   - No forbidden proof escape, resource override, or EuclideanSpace token in the delivered module.
     Copyright, module command, public import, module docstring and public section are present.
   - 85 lines; maximum line length 99 Unicode characters. No 100-character lint exception is needed.
   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   - `git diff --check inp...HEAD`: empty, exit 0.

## Defects, notes and limits

No suspected frozen-statement, scoped-blueprint or pinned-source defect was found. No deviation was introduced.
The Part-2 zero-field statement explicitly labels this direct argument as ours; this is not a fresh
pinned-PDF review of BM11. The design audit's unrelated kernel dependency/departure-inventory notes do not
change the four scoped zero-field statements and are not new findings against this package.

The expected stale KAM.lean is an integration note only; the auditor did not edit generated files.
No heartbeat or memory/design failure occurred. Nothing in this audit establishes subsequent orbit receipts
or any quantitative stability theorem. The only lasting file written is this report; the disposable probe
was removed. The pre-existing untracked prover handoff was preserved. No state-changing git command was used.
