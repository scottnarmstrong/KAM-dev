# B12 independent package audit 2 — delta

Date: 2026-10-28. **Overall verdict: PASS WITH NOTES. Round-1 F1 is RESOLVED.**
The adapted selection required by signed composition is now supplied, without an added
source premise. The signed fixed-schedule theorem and output record are unchanged.
The note is the brief-permitted stale generated `KAM.lean`; this infrastructure package
seals no frozen anchor and does not establish the remaining composition theorem.

## Scope and authority

- Worktree and report destination: `/root/code/KAM-inp-p11b-b12` (the user's exact
  destination overrides the generic brief's main-worktree destination).
- Audited HEAD: `141f86ac0975de0a2fe929d598b21a36fc8d47ad`.
- Compared live `inp`: `a2c95a9339a7bf00c88b45ff27058eaa6f5b3be9`.
  `git diff inp...HEAD` warns of multiple merge bases and selects
  `980388b435b56c1a548f7c9771a8f4c62033aba7`, the same base as Round 1.
  On final recheck `inp` had advanced to
  `2d009059bbfb14a40c7d98e3f65765e3a6a9bc5b`; HEAD and the selected merge base stayed unchanged.
  The final three-dot diff SHA256 is
  `1ee532d90aa209e47138747cbe70862f111d2d232e6dda500ce65059ba5c14f8`.
  The three-dot inventory comprises 13 B10 Iteration modules, three B12 Selection
  modules and the two earlier audit/handoff documents. Only `Selection*.lean` is
  assigned a proof-package verdict here; B10 is a separately audited supplier.
- Inspected the three-dot B12 source diff and the complete fix diff
  `git show 141f86ac --`. The fix changes only Selection and SelectionTests:
  **106 insertions, 29 deletions**. SelectionRecord is unchanged since Round 1.
- Read AGENTS, PLAN, DECISIONS, the package audit brief, B12 handoff/AUDIT FOCUS,
  Round-1 report, `.drafts/handoff-B12.md` Round-2 fix, P11B design and design audits,
  relevant p11a3/p11a4 blueprint clauses, track-P conventions, the output record,
  actual B10 adapted export, budget context and frozen Diophantine definition.
- Signed authority: `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean`, SHA256
  `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63`.
  This agrees with Round 1. Provider/frozen exact-type and seal-body probes are
  inapplicable: B12 has no provider or frozen theorem export. The corresponding
  signed fixed header and exact adapted consumer type were independently elaborated.

## F1 closure, fidelity and common witnesses

`Selection.lean:335–349` now proves
`Nonempty (SelectionOutput d f (selectionAdapted d ε))` from exactly
`d, ε, 0 < ε, ε ≤ selectionAdmissible d, f, SelectionPerturbation d f ε`.
These are precisely the premises of signed `composition` at signature lines 712–715;
its result `SelectionComposition d f (selectionAdapted d ε)` extends this exact
SelectionOutput at signature line 668. No fixed/adapted schedule identification,
assumed good set, limit, output or independently supplied iteration is needed.
The formerly failing consumer-shape probe now elaborates with the direct term
`parameter_selection_adapted d ε he hsmall f hf`.

The companion first obtains `o` from `inductive_lemma_adapted` (line 339), obtains
admissibility and positive radius from `free_radius`, proves positive initial energy
as `2 * ε > 0`, and proves `t₀ ≤ 1` using `hA.t_le`, `1 ≤ sqrt n`, and `d.theta_le`.
It constructs the budget context with the schedule's definitional constant equalities.
Thus all conditions of the conditional generic helper are discharged from source
premises. Positivity of ε is already required by the adapted source/consumer.

`selectionOutput_of_iteration` (Selection:194–321) contains the former full assembly
proof, now parameterized by a schedule and its proved admissibility/budget data.
At line 285 its record sets `toSelectionIteration := o`. One cutoff family χ is
chosen once at lines 200–201; both finite-test and extension suppliers receive that
same χ and `o.toSelectionChain`. The frequency/energy limits both come from
`selection_limit_series cx o`. The fields `extended`, `modeStage`, finite tests,
Hinf, Kinf, tails and Diophantine conclusion all refer to those same objects.
There is no independent iteration or cutoff reselection in a field.
The helper's type does not separately export an equality to its input iteration;
common-witness preservation is explicit in its record construction, which suffices
for the signed parent record consumed by composition.

The retained intersection, continuity-from-above measure argument, and `limit_bridge`
argument are unchanged except for the justified schedule constant equalities and
nonnegative τ from the budget context. Hinf and Kinf remain distinct. The helper
assumes no output field; its iteration premise is explicit conditional implementation
data, supplied by the two source exports rather than added to either source theorem.

The signed SelectionOutput body and parameter_selection header are byte-identical
to the live signature. The original two fixed-schedule helper headers are unchanged.
The fixed theorem still covers ε = 0 and now applies the generic constructor to
`inductive_lemma`; no premise or conclusion changed. B12's part of `fr-other`
(design:256–259; blueprint p11a4:39,46) is discharged. This does not independently
certify the separately assigned B10/B13 parts of that graph node.

## Declaration and node ledger

All names are in `KAM.Planetary`. Locations refer to audited HEAD. Unchanged rows
carry forward Round-1 analytic review, with fresh signature/static/axiom/kernel checks.

| Node / role | Declaration / location | Verdict | Reason |
|---|---|---|---|
| Signed output | `SelectionOutput`, SelectionRecord:26 | PASS | Unchanged, exact signed record, including common finite tests and both limit sets. |
| Cutoff predicate | `SelectionCutoffSpec`, SelectionTests:30 | PASS | Unchanged honest smoothness/support/derivative specification. |
| ps-iter/ps-H supplier | `selection_all_cutoffs`, SelectionTests:39 | PASS | Same all-stage construction, one family. |
| Finite-test definition | `selectionFiniteTests`, SelectionTests:54 | PASS | Same literal all-mode tests at fixed modeStage. |
| Generic stage supplier | `selection_stage_close_of_adm`, SelectionTests:62 | PASS | New conditional helper: extension estimate plus admissibility closeness budget; no extra source premise. |
| Fixed stage supplier | `selection_stage_all`, SelectionTests:98 | PASS | Header unchanged; obtains fixed admissibility facts and applies generic supplier. |
| Generic finite tests | `selection_tests_of_adm`, SelectionTests:113 | PASS | Compactness, retention and measure for arbitrary admissible schedule with the selection constants. |
| Fixed finite tests | `selection_tests_of_cutoffs`, SelectionTests:165 | PASS | Header unchanged; fixed facts discharge generic helper conditions. |
| Norm supplier | `norm_selectionRe_le`, Selection:31 | PASS | Unchanged Pi max-norm contraction. |
| Geometric supplier | `selectionVarpi_le_half`, Selection:35 | PASS | Unchanged actual-exponent bound. |
| Collar supplier | `selectionReal_mem_collar`, Selection:47 | PASS | Unchanged positive-radius real-point membership. |
| Mode supplier | `selectionModeLength_pos`, Selection:53 | PASS | Unchanged nonzero-mode positivity. |
| Intersection supplier | `selection_Kinf_subset`, Selection:63 | PASS | Unchanged projection from intersection. |
| ps-lim | `selection_limit_series`, Selection:68 | PASS | Unchanged generic B11 double application, uniform convergence, sums, continuity and tails. |
| Mode exhaustion | `selectionT_unbounded`, Selection:187 | PASS | Unchanged geometric cutoff exhaustion. |
| Generic full assembly | `selectionOutput_of_iteration`, Selection:194 | PASS | Former assembly with one input iteration; all fields proved on same witnesses. |
| ps-iter | Both source exports, Selection:328,339 | PASS | Each obtains its actual coherent iteration from the matching B10 export. |
| ps-H | Generic assembly, Selection:200–253 | PASS | Shared χ; compact antitone finite tests, exact intersection and measure bound. |
| ps-dio | Generic assembly, Selection:255–284 | PASS | Same-mode extension equality and tail estimate feed limit_bridge on Hinf only. |
| Signed parameter-selection | `parameter_selection`, Selection:325 | PASS | Exact signed header; fixed source premises discharge generic helper. |
| Adapted fr-other / B14 parent | `parameter_selection_adapted`, Selection:335 | PASS | Exact adapted SelectionOutput, same consumer premises and common witnesses; F1 resolved. |

The new stage supplier uses `schedule_props` to bound the derivative sum by
`4 * (a.ε₀ / a.s₀) / a.t₀ ^ a.μ`, then applies `hA.closeness` after replacing
μ by its actual data value. No fixed-radius formula is used. The generic finite-test
proof retains the capped smooth family `wt k = extended (min (modeStage k) ν)`;
for tested modes the cap disappears. Its all-mode measure estimate is converted
using the explicit equalities `a.γ = selectionGamma d` and `a.τ = d.τ`, so it
bounds the actual finite tests at the supplied schedule, including the adapted one.

## Definitions and hygiene

There are **no new def/abbrev/structure declarations in the fix**. The unchanged
SelectionOutput is output packaging, never a source assumption; SelectionCutoffSpec
is a genuine conditional predicate; selectionFiniteTests is the intended subset of
K on its whole carrier. The local capped family is total and agrees with the desired
extension on every tested mode. The total tsum functions are used analytically only
on Kinf where convergence is proved. No fallback or junk value is used by a theorem.

Fresh declaration-name scanning across KAM found no repeated B12 public declaration
short name, including all four new theorem names; every export is namespaced, with
no root shadow. The three modules have copyright, module, public imports, module
docstrings and exposed public noncomputable sections. No forbidden token, ambient
carrier substitution, norm instance, provider import or resource override is introduced.

- Selection: **355 lines**, maximum **100** Unicode characters per line.
- SelectionRecord: **87 lines**, maximum **97**.
- SelectionTests: **178 lines**, maximum **99**.

The handoff's Round-2 phrase “Files ≤ 328 lines” is stale: Selection now has 355.
This is a documentation count discrepancy only; both the 1500-line hard cap and
100-column requirement pass. Likewise, the fixed helper wrappers consist of fact
extraction followed by one generic application, rather than literally one total line.

A fresh transitive KAM import traversal visits **155 modules**: no provider or frozen
theorem is imported. All **14** imported frozen modules are manifest-SEALED
**definitions** (ActionNbhd, ComplexStrip, FrequencyMap, HamiltonianVectorField,
HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero,
RealHamiltonian, SymplecticForm, Planetary CircularPoint, CircularTube and Phase).

## Independent validation

Every Lean/Lake invocation was serialized, with `LEAN_NUM_THREADS=1` and
`nice -n 5`; lint also ran after the other Lean processes completed. No clean,
cache fetch, package update, generated-root rewrite or state-changing git operation.

1. Targeted build:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b12 KAM.Planetary.WeakKAM.Selection
```

Exit **0**. Gate: `[inp-gate] slot 1 acquired 23:10:48 for KAM.Planetary.WeakKAM.Selection`.
Final output: `Build completed successfully (9201 jobs).` Replayed dependency warnings
concern unused arguments, simp arguments and deprecated names; no proof error.

2. Independent signature/consumer/axiom probe:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B12Audit2.lean
```

Exit **0**. The exact signed fixed header was copied under a fresh name and proved
with `exact parameter_selection d ε he hsmall f hf`; its `type_of%` equality probe
also elaborated. A separate example with exactly the signed composition premises
returns the exact adapted SelectionOutput via parameter_selection_adapted.
Independent text comparison output:

```text
SelectionOutput byte-identical: True
parameter_selection header byte-identical: True
selection_stage_all header unchanged: True
selection_tests_of_cutoffs header unchanged: True
```

`#print axioms` returned **`[propext, Classical.choice, Quot.sound]` for every one**
of the **15** public theorems in the three modules:

```text
norm_selectionRe_le
selectionVarpi_le_half
selectionReal_mem_collar
selectionModeLength_pos
selection_Kinf_subset
selection_limit_series
selectionT_unbounded
selectionOutput_of_iteration
parameter_selection
parameter_selection_adapted
selection_all_cutoffs
selection_stage_close_of_adm
selection_stage_all
selection_tests_of_adm
selection_tests_of_cutoffs
```

3. Kernel replay:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Selection KAM.Planetary.WeakKAM.SelectionRecord KAM.Planetary.WeakKAM.SelectionTests
```

Exit **0**. Complete verbose output:

```text
replaying KAM.Planetary.WeakKAM.SelectionTests
replaying KAM.Planetary.WeakKAM.SelectionRecord
replaying KAM.Planetary.WeakKAM.Selection
```

4. Source lint:

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

The generated root was left untouched. No forbidden token, resource override,
EuclideanSpace, module-format, line-length, file-size, frozen-anchor or ABI failure.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` and
`git diff --check inp...HEAD`: exit **0**, no diff/error output, apart from the
already recorded merge-base warning. No protected path changed.

## Errata, deviations and remaining limits

No new suspected pinned-source, blueprint or frozen-statement defect was found.
The known design GAP-1 in the ps-lim citation remains handled by the proved B11
continuous-series bridge, as in Round 1. No mathematical deviation was introduced
by this fix. The stale handoff line count is recorded above.

This is a delta package verdict: unchanged Round-1 proof review is carried forward;
imported B10/B11 and earlier supplier bodies are not independently re-audited here.
B12 now supplies its documented adapted consumer interface; this is not a proof of
B14 composition or a seal of a campaign anchor. No remaining B12 blocking finding.

Only this exact report was written as a deliverable. Temporary audit probe removed
after checks; tracked Lean sources, prior reports, handoff, generated files, frozen
files and manifest were preserved.
