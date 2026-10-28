# P5-CL independent package audit 1

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p5cl`.
Audited HEAD: `1061c4c7ae7db52a52c8af5ea2e6605229bb5b06`.
Comparison branch `inp`: `6e36995edb8c5fb4ee4ec0ed914f4a0c55a9b7f1`.

**Overall: PASS WITH NOTES.** `KAM.Planetary.local_real_complexification` is proved at the exact P5-CL design signature, with no added premise and clean axiom/kernel checks. The only hygiene exception is the expected stale generated `KAM.lean`. There is no frozen anchor or provider in this package, hence no frozen theorem is certified seal-ready by this report. The local infrastructure result itself passes.

## Scope and authority

Followed `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the worktree `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, and the handoff's AUDIT FOCUS. The user's exact output path overrides the generic brief's main-worktree output instruction. Production audit scope is only `KAM/Planetary/PGAssembly/ComplexLocal*.lean`; the three-dot diff contains one new file, `ComplexLocal.lean` (190 lines).

Statement authority: tracked `docs/tracks/P/design/P45-LEAN-DESIGN.md:1482–1486`, package row at line 484, analytic proof plan at lines 271–273, and gap allocation at line 414. Independently read the raw blueprint proof step `blueprint-P/parts/p5-pg-assembly.tex:33` (`stepP:p5:ext-loc`), its enclosing extension statement, and track-P statement conventions. The named draft signature is absent in this worktree; read `/root/code/KAM-inp/.drafts/design/P45Signatures.lean:785–789` instead and verified it agrees byte-for-byte with the tracked design signature and implementation telescope (split before `:=`). Consulted the three named design audits at their actual main-worktree `docs/tracks/P/design/DESIGN-P45-design-audit-{1,2,3}.md` paths; their local-complexification rows introduce no additional obligation or ruling. They are supporting evidence, not proof authority.

No frozen theorem is implemented here. Frozen/provider type equality and literal frozen seal-body probes are therefore N/A. An exact design-signature declaration with a fresh name was elaborated using the implementation and all its explicit binders, as detailed below. No draft signature file was imported.

## Declaration findings

Names below use prefix `KAM.Planetary.PGAssembly.` except the last row, which uses `KAM.Planetary.`. All helpers implement the coordinate power-series argument for `stepP:p5:ext-loc`; they do not claim the whole compact extension lemma.

| Node / role | Declaration (ComplexLocal.lean line) | Verdict | Reason |
|---|---|---|---|
| ext-loc / coefficient | `complexCoeff` (33) | PASS | Real multilinear coefficient evaluated on standard coordinate vectors. |
| ext-loc / complex multilinear extension | `complexSeriesTerm` (37) | PASS | Finite sum of coefficient-scaled coordinate-product continuous complex multilinear maps. |
| ext-loc / formal series | `complexSeries` (44) | PASS | The preceding maps assembled degree by degree, for every real formal series. |
| ext-loc / evaluation | `complexSeries_apply` (47) | PASS | Exact finite coordinate formula, all inputs allowed. |
| ext-loc / coefficient estimate | `abs_complexCoeff_le` (52) | PASS | Operator norm bound; every coordinate vector has norm at most one. |
| ext-loc / convergence estimate | `norm_complexSeries_le` (66) | PASS | Sup-norm bound `N^n * ‖p n‖`; finite index set has cardinality `N^n`. No positivity restriction on N. |
| ext-loc / real restriction | `complexSeries_realInclusion` (82) | PASS | Full multilinear identity for arbitrary real vectors in every slot, stronger than diagonal identity needed by the sum. |
| ext-loc / radius | `le_radius_complexSeries` (100) | PASS | Uniform scaled coefficient bound implies radius at least `t/(N+1)`; no hidden convergence assumption. |
| P5-CL / local extension | `local_real_complexification` (121) | PASS | Verbatim signature, positive radius and bound, complex differentiability and agreement on the entire real ball. |

### Binder and premise audit

For the main theorem, the following is the entire input telescope. No implicit project structure, typeclass instance, or predicate bundle adds a premise.

| Binder | Type | Bin | Authority |
|---|---|---|---|
| `{N}` | `ℕ` | TYPING | Design 1482; finite coordinate dimension, including zero. |
| `{f}` | `(Fin N → ℝ) → ℝ` | TYPING | Design 1482; literal real function carrier. |
| `{x}` | `Fin N → ℝ` | TYPING | Design 1482; expansion centre. |
| `hf` | `AnalyticAt ℝ f x` | SOURCE | Design 1483; blueprint local convergent real power series. |

Counts: SOURCE 1, STANDING 0, TYPING 3, RULED 0, EXCESS 0. `AnalyticAt` means existence of a genuine real formal multilinear power series with positive ball radius and the corresponding expansion; no desired complex extension is bundled in it. The existential `rho`, `M`, and `F` follow all inputs, preserving their permitted dependence on N, f, x and the analytic germ. All three conjuncts of the signature, their open-ball domains, complex scalar field and positivity conditions are retained.

Helper inputs are explicit: all have dimension N and real formal series p as typing data; degree n, index i, tuple m, and real tuple v are typing data in the relevant declarations. Only `le_radius_complexSeries` adds `{t : ℝ≥0}`, `{C : ℝ}`, and `hC : ∀ n, ‖p n‖ * (t : ℝ)^n ≤ C`. This is a separately named coefficient-to-radius estimate, not an additional assumption of local complexification. At line 129 the main proof produces hC from `norm_mul_pow_le_of_lt_radius`, then supplies it at line 134. No hard analytic bridge is assumed as a premise.

### Definition classification

All three new definitions are **literal algebraic constructions**, not characterization-defined choices. `complexCoeff` is evaluation on coordinate basis vectors; `complexSeriesTerm` is the displayed finite multilinear sum; `complexSeries` is the degree-indexed sequence of these maps. The complete bodies agree with their docstrings on the whole declared carriers. They contain no conditional/default branch and no arbitrary witness choice. The enclosing exposed public noncomputable section makes their bodies available for unfolding.

For each of these three definitions: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS. The evaluation and real-restriction theorems independently establish their intended equations. Empty-coordinate and degree-zero cases use genuine empty products/sums; the positive denominator N+1 avoids a division-by-zero fallback.

The existing `KAM.realInclusion` was inspected in `KAM/Strip/Analytic.lean:38–51`: it is the coordinatewise real-to-complex continuous linear inclusion and preserves the Pi max norm. No change of norm or carrier occurs.

## Independent proof review

The proof extracts p, r and the actual expansion from hf, chooses `0 < t < r`, and obtains bounded coefficients at t strictly below p's convergence radius. Each complex coefficient is bounded by the real operator norm; summing all `N^n` coordinate choices yields the complex multilinear estimate. Therefore q converges at least to `s=t/(N+1)>0`.

`F z = q.sum (z - realInclusion N x)` is complex differentiable on the ball of radius s by the power-series differentiability theorem and translation. Restricting to the closed ball of radius s/2, strictly inside that open ball, justifies continuity and compact boundedness. The witnesses are `rho=s/2` and `M=max B 0+1`. Compactness is used only for a finite-dimensional closed ball, not for an open domain.

For real y in the smaller ball, the proof establishes membership in both original and complex convergence balls, expands real tuples in the coordinate basis, and uses multilinearity to identify all q coefficients with the complex casts of p coefficients. The two genuine convergent sums then agree by HasSum uniqueness. No unproved real-analytic-to-holomorphic bridge, boundary convergence, or analytic continuation is imported.

## Reproduced checks

All Lean/Lake invocations were serialized, with `LEAN_NUM_THREADS=1` and nice priority 5. The build used the required compile gate; no clean, cache fetch, package update, generated root edit, or state-changing git command was run.

1. Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5cl KAM.Planetary.PGAssembly.ComplexLocal
[inp-gate] slot 1 acquired 08:41:56 for KAM.Planetary.PGAssembly.ComplexLocal
✔ [9053/9053] Built KAM.Planetary.PGAssembly.ComplexLocal (9.1s)
Build completed successfully (9053 jobs).
exit 0
```

The gate executes `nice -n 5 lake build` internally. The jobs count is Lake's dependency graph, not a simultaneous worker count; only the target was reported built.

2. Exact-signature and axioms probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5CLAudit1.lean
exit 0
```

The scratch file imported only `KAM.Planetary.PGAssembly.ComplexLocal`, opened `Set Metric`, copied the exact design declaration under `audit_local_real_complexification`, and used this proof body:

```lean
by
  exact KAM.Planetary.local_real_complexification hf
```

It also checked the reverse whole-type assignment:

```lean
example : type_of% @KAM.Planetary.local_real_complexification :=
  @audit_local_real_complexification
```

The six `#print axioms` outputs were:

```text
'KAM.Planetary.PGAssembly.complexSeries_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGAssembly.abs_complexCoeff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGAssembly.norm_complexSeries_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGAssembly.complexSeries_realInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGAssembly.le_radius_complexSeries' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.local_real_complexification' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation for the only new module (there is no provider):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.ComplexLocal
replaying KAM.Planetary.PGAssembly.ComplexLocal
exit 0
```

4. Source lint:

```text
LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (490 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

This is PASS under the brief's explicit stale-root exception, not an unqualified zero-exit lint pass. No other lint diagnostic occurred. `KAM.lean` was left untouched.

5. Static/protected-path checks:

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
git diff inp...HEAD --check
(no output; exit 0)
wc -l KAM/Planetary/PGAssembly/ComplexLocal*.lean
190 KAM/Planetary/PGAssembly/ComplexLocal.lean
```

Inspected every new definition and theorem and the full three-dot production diff. No sorry, admit, axiom, unsafe, opaque, resource-budget override or forbidden ambient space appears. Copyright, module command, public imports, module docstring, and exposed public section are present. Direct imports are Mathlib and `KAM.Strip.Analytic`. The recursive project import closure is Analytic, AnalyticSeries, AnalyticTaylor, Cauchy, Regularity, and `KAM.Frozen.Defs.ComplexStrip`; that definition is SEALED in `manifest/frozen-anchors.json:51–65`. No provider or DRAFT_SORRY theorem is reachable.

## Notes, uncertainties, errata and handoff

No suspected defect or deviation was found in the audited theorem or local power-series argument. No pinned external PDF claim is independently certified here: this package supplies a classical input by a direct proof, under the explicit local design signature.

The blueprint phrase at `p5-pg-assembly.tex:33`, “By compactness a Lebesgue number gives ... uniformly”, involves additional compact selection and gluing. Those are explicitly allocated to P5-CG/P5-ID in design lines 484–486. This local package does not close that entire blueprint step or the P-G root; this is a scope note, not a newly discovered source defect. There are no new errata to quote or record.

Only this report is a durable audit edit. The temporary probe was deleted after validation. The pre-existing untracked `P5-CL-handoff.md` was preserved. No production, frozen, manifest, generated or external-main-worktree file was edited. Required follow-up for integration is the orchestrator's normal generated-root refresh; no proof repair is requested for P5-CL.
