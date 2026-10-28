# B12 independent package audit 1

Date: 2026-10-28. **Overall verdict: FAIL (consumer completeness, F1).** The signed
fixed-schedule theorem is correct and signature-faithful; its proof, definition and axiom
checks pass. B12 does not yet supply the adapted-schedule selection required by the
approved design and B14 consumer. This is an implementation/interface gap, not a
refutation of parameter selection.

## Scope and snapshot

- Worktree: `/root/code/KAM-inp-p11b-b12`.
- HEAD: `9e4947207a610181e87337997a1f7e0cf18c991e`.
- Compared branch `inp`: `983fa887bea1c786de978aeffbbab517432a16f3`.
- `inp` advanced during the audit to `d67f98ce2d390e900d90c58f96b8555b28b04461`.
  The initial and rechecked live three-dot diffs are byte-identical; both use merge base
  `980388b435b56c1a548f7c9771a8f4c62033aba7`. HEAD and signed input stayed unchanged. A later live diff emitted a multiple-merge-base
  warning but selected that same base and remained byte-identical to the pinned initial diff
  (SHA256 `3ceb84bf9d578de831a8031a0b70c184af248e753df7ff32115bd925c6cbf2f2`).
- Compared with `git diff inp...HEAD`; all 16 changed files are additions:
  13 `Iteration*.lean` files (B10, separately audited), and the three B12 files below.
  Only `Selection*.lean` receives a proof-package verdict here, as instructed.
- Signed authority: `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean`, SHA256
  `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63`.
- Read AGENTS, PLAN, DECISIONS, package brief, B12 handoff, P11B design/node table,
  P11B design audits 1 and 2, relevant p11a3/p11a4 blueprint clauses, track-P statement
  and frozen interface definitions. Design-audit-1 F1/F2 were repaired in revision 2;
  its B10 real-collar supplier gate remains outside this B12-only audit.
- No frozen anchor is proved by this infrastructure package. Frozen/provider exact-type
  and seal-body tests are therefore not applicable to an anchor. Instead the signed
  declaration is independently re-elaborated from its signature text, under a fresh name,
  with `by exact parameter_selection d ε he hsmall f hf`, and checked by `type_of%`.
- The user’s exact report destination overrides the generic brief’s main-worktree
  destination. No tracked source, generated root, frozen file or manifest was edited.

## F1 — missing adapted selection for the downstream consumer

**Severity: blocking package completeness.** `Selection.lean:194–197` exports only
`Nonempty (SelectionOutput d f (adm_params d ε))`. `SelectionTests.lean:61–80`
likewise specializes the shared-stage estimates and fixed-cutoff finite-test theorem to
`adm_params`. There is no adapted selection export or generic full-output constructor
in the three audited modules.

The design’s coverage note at `docs/tracks/P/design/P11B-LEAN-DESIGN.md:256–259`
explicitly says that `fr-other` is discharged where **B10/B12/B13** apply their results
at the adapted radius. Blueprint `p11a4-limit-family.tex:39` states:
“Consequently ... parameter-selection ... hold verbatim with this s0”. The proof step
`fr-other` is at line 46. B10 supplies `inductive_lemma_adapted`
(`Iteration.lean:77–85`), but B12 does not continue that iteration to a selection output.

This matters immediately: signed `composition`, signature lines 712–715, returns
`SelectionComposition d f (selectionAdapted d ε)`. That structure extends
`SelectionOutput d f a` (signature line 668). The available fixed-schedule output
cannot furnish its parent record. The schedules have genuinely different radius and
initial-energy formulas (`Admissible.lean:60–66`): fixed lambdaMax/(n*C1) versus
sqrt(2*ε/(n*C1)), and ε+n*C1*s0^2/2 versus 2*ε. Positivity of ε does not identify them.
Reusing a different fixed iteration would also lose the required common witnesses.

An independent negative consumer probe, under the exact positive-ε consumer premises,
tries `exact parameter_selection d ε he.le hsmall f hf` at the adapted output type.
It exits 1 with:

```text
error: Type mismatch
  parameter_selection d ε (LT.lt.le he) hsmall f hf
has type
  Nonempty (SelectionOutput d f (adm_params d ε))
but is expected to have type
  Nonempty (SelectionOutput d f (selectionAdapted d ε))
```

**Required repair:** preserve the signed fixed theorem unchanged and add a distinctly
named adapted companion, or a generic selection-output assembler applied to both
constructed iterations. Generalize the fixed-cutoff test supplier as needed, using
the already available generic B10 stage/measure infrastructure. Return the entire
selection on the same adapted iteration; do not assume a good set, limit or output
record in a replacement source theorem. Audit that companion before declaring B12’s
consumer coverage complete. No signature or frozen-file change is required.

## Declaration and graph ledger

Names below are in `KAM.Planetary`. PASS is scoped to the stated declaration; the
package verdict remains FAIL because of F1. Local `ps-*` obligations need not be
separate exported declarations under the design’s node-table convention.

| Node / role | Declaration / location | Verdict | Reason |
|---|---|---|---|
| parameter-selection output | `SelectionOutput`, SelectionRecord:26 | PASS | Entire record body is byte-identical to the signature, including finite tests, common witnesses and Hinf/Kinf distinction. |
| cutoff implementation predicate | `SelectionCutoffSpec`, SelectionTests:30 | PASS | Actual smoothness, range, support and derivative bounds; explicit conditional helper data. |
| ps-iter/ps-H supplier | `selection_all_cutoffs`, SelectionTests:39 | PASS | Chooses each stage cutoff once from its compact nonempty set and positive scale, for all stages. |
| finite-test definition | `selectionFiniteTests`, SelectionTests:54 | PASS | Literal finite all-mode tests with fixed stage-of-mode extension. |
| ps-H extension supplier | `selection_stage_all`, SelectionTests:61 | PASS | Distinct conditional helper; smooth extension, equality on K_j and full required closeness bounds. |
| ps-H finite tests | `selection_tests_of_cutoffs`, SelectionTests:74 | PASS | Compactness, retention inclusion and measure for this same cutoff family at every finite stage. |
| norm supplier | `norm_selectionRe_le`, Selection:31 | PASS | Componentwise real-part contraction in Pi max norm. |
| geometric supplier | `selectionVarpi_le_half`, Selection:35 | PASS | Follows from the actual exponent with τ≥0. |
| collar supplier | `selectionReal_mem_collar`, Selection:47 | PASS | The same point witnesses membership at every positive collar radius. |
| nonzero-mode supplier | `selectionModeLength_pos`, Selection:53 | PASS | Sum of absolute coordinates is positive for a nonzero integer mode. |
| intersection supplier | `selection_Kinf_subset`, Selection:63 | PASS | Exact intersection projection. |
| ps-lim supplier | `selection_limit_series`, Selection:68 | PASS | Explicit conditional helper with separate name. Summability, uniform convergence, sums, continuity and both tails; no positive limiting collar assumed. |
| mode exhaustion | `selectionT_unbounded`, Selection:187 | PASS | T0≥1 and geometric growth exhaust all finite mode lengths. |
| parameter-selection, signed | `parameter_selection`, Selection:194 | PASS WITH NOTES | Header exactly matches signature, no added premise; fixed-schedule construction complete. Generated-root lint note; F1 prevents consumer-complete package release. |
| stepP:p11a:ps-iter | `parameter_selection`, Selection:198–205 | PASS | Constructs the iteration from raw data via `inductive_lemma`; inherited finite-chain fields give compact nonempty nested stages. |
| stepP:p11a:ps-lim | Selection:68–181, 206–207 | PASS | Applies B11 twice to Re Δω and Re Δh; geometric bounds give S_m and 4ε_m. |
| stepP:p11a:ps-H | Selection:208–259 | PASS | Same χ for all ν; proves Hinf=intersection, antitonicity, compactness, inclusion and continuity-from-above measure bound. |
| stepP:p11a:ps-dio | Selection:260–290 | PASS | On Hinf only: extension equality on K_m, tail S_m, shell bound and `limit_bridge` give frozen IsDiophantine with γ,τ. |
| fr-other consumer application | absent adapted selection | FAIL | Explicit B12 coverage requirement and signed B14 parent-output requirement remain unpaid (F1). |

The fixed-schedule node slice has no other missing graph obligation. The source’s
nonemptiness of Kinf is recoverable from the inherited compact nonempty nested chain;
a positive probe proves it using
`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`. Another probe
proves `volume d.K - ofReal d.loss ≤ volume o.Kinf` by `o.measure_H` and
`measure_mono o.H_subset`. The stronger intermediate tail bound
`selectionTail a m ≤ a.γ * selectionT a m ^ (-a.τ - 1)` is supplied by `iter_tail` and
used explicitly in the Diophantine proof. These are recoverable source clauses,
not missing premises or extra independent assumptions.

## Definition classification and proof review

- `SelectionOutput`: output packaging extending the constructed iteration. Every field
  is populated by proof; it is never a standing premise of `parameter_selection`.
- `SelectionCutoffSpec`: honest predicate over all stages, including the derivative
  bounds needed for the measure estimate. Stronger than the public output’s cutoff
  subset of fields, by design; it is constructed, not silently assumed by the source export.
- `selectionFiniteTests`: literal subset of d.K defined by all nonzero modes below
  Tν and the fixed cutoff extension at each mode’s first shell. No stage-dependent
  reselection and no junk fallback.
- Local `wt k = extended (min (modeStage k) ν)` is total and smooth for every mode.
  For every tested mode, `modeStage k ≤ ν`, so the cap is exactly removed. Applying
  the all-mode family-measure theorem to this capped family is legitimate; its good
  set is a subset of the required finite test set.
- Local frequency/energy sums are total `tsum` functions, with all convergence and
  analytic claims restricted to Kinf, where summability is proved. No claim relies on
  default values away from that carrier. No new abbreviations or norm instances.
- Conditional helpers openly take existing chain/iteration data; their distinct names
  do not replace source exports. The signed source export takes only raw standing
  data, perturbation, nonnegative ε and the specified smallness bound.

## Independent validation

All Lean/Lake commands were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The compile gate was allowed to wait; no clean, cache fetch, update or library restart
was performed.

1. Targeted gate:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b12 KAM.Planetary.WeakKAM.Selection
```

Exit **0**. Output included `[inp-gate] slot 3 acquired 22:54:58` and
`Build completed successfully (9201 jobs).` Replayed dependency warnings concerned
unused arguments, simp arguments and deprecated names; no build error or proof hole.

2. Signature, source-clause and axiom probe:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B12Audit.lean
```

Exit **0**. Independently copied the exact signed record and theorem header; the fresh
header was discharged with exactly the explicit arguments in order. The
`example : type_of% @b12AuditParameterSelection := @parameter_selection` elaborated.
Source-text comparison separately returned:

```text
SelectionOutput byte-identical: True
parameter_selection header byte-identical: True
```

`#print axioms` returned **`[propext, Classical.choice, Quot.sound]` for each** of:

```text
selection_all_cutoffs
selection_stage_all
selection_tests_of_cutoffs
norm_selectionRe_le
selectionVarpi_le_half
selectionReal_mem_collar
selectionModeLength_pos
selection_Kinf_subset
selection_limit_series
selectionT_unbounded
parameter_selection
```

These are all eleven new public theorems in the three audited files, not only the
three sampled in the prover handoff. The nonempty-intersection and measure-projection
examples also elaborated. No `sorryAx` dependency.

3. Negative consumer probe:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B12AdaptedConsumer.lean
```

Exit **1**, expected: exact type mismatch reproduced under F1 above. This is a
consumer-interface test, distinct from the successful signed fixed theorem probe.

4. Kernel replay:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Selection KAM.Planetary.WeakKAM.SelectionRecord KAM.Planetary.WeakKAM.SelectionTests
```

Exit **0**. Complete verbose output:

```text
replaying KAM.Planetary.WeakKAM.SelectionTests
replaying KAM.Planetary.WeakKAM.SelectionRecord
replaying KAM.Planetary.WeakKAM.Selection
```

5. Source lint:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1065 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No forbidden token, resource override, EuclideanSpace, oversize file, overlong line,
module, errata-render or protected-anchor error was reported. The generated root was
left untouched as required.

6. Static and protected-path checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp...HEAD`: empty, exit 0.
- Selection/SelectionRecord/SelectionTests have **328/87/128** lines and maximum
  **100/97/99** Unicode characters per line. All three have copyright, `module`,
  public imports, module docstrings, public sections and exposed relevant definitions.
- Independent transitive KAM import traversal visits 155 modules: no provider import,
  no frozen theorem import, no DRAFT_SORRY anchor. All 14 imported frozen modules
  are definitions recorded SEALED in the manifest (ActionNbhd, ComplexStrip,
  FrequencyMap, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine,
  IsPrimaryOnStrip, IsRealOnReals, OmegaZero, RealHamiltonian, SymplecticForm,
  Planetary CircularPoint, CircularTube and Phase).
- No repeated new declaration short name elsewhere in KAM; all new names are
  namespaced, with no root shadow. No ambient carrier or norm-instance substitution.

## Errata, deviations, uncertainty and handoff

No new pinned-source or frozen-statement defect was found. The known blueprint
ps-lim citation gap (design GAP-1) is handled by B11’s elementary continuous-series
bridge, consumed twice here. F1 is a missing implementation of the documented
adapted application, not an erratum to the signed fixed-schedule statement.

B10 and earlier supplier correctness beyond the imported interfaces is not re-audited;
B12 uses their actual built declarations, and all audited theorem axiom closures are
clean. This report does not seal an anchor or certify the campaign theorem. The
fixed theorem is usable at its stated type; package acceptance must wait for F1.

Temporary probes and replay logs were removed after recording results. Only this
report was created by the auditor in the repository; the pre-existing untracked
B12-handoff was preserved. No source repair or state-changing git operation.
