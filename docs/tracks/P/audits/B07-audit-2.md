# B07 independent package audit 2 — delta

**Overall verdict: PASS WITH NOTES for B07b under the stated OVERNIGHT 18:17 ruling.**
The new `adm_choice_initial` companion attaches exactly A7 to the existing `adm_choice`
conclusion by consuming B06 `initial`. Signed declarations are unchanged. This is a package
verdict, not closure of the full `free-radius` blueprint node or any frozen theorem.
`free-radius` and `fr-other` remain NOT_STARTED pending B10/B12/B13.

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11b-b07`.
Only this report is an authorized repository edit; temporary probes are confined to
`.lake/abi-scratch/` and removed after use. The user's exact worktree destination overrides
the generic brief's main-worktree destination. No production source or git state is modified.

## Frozen inputs and scope

Tier 2 focused delta audit, with mechanical inventory, source/premise review, a separate
adversarial check of possible weakening or extra hypotheses, then sequential validation.
Round 1 remains the evidence for unchanged scalar proof internals; this round independently
checks the new attachment, all signed interfaces, imports, axioms and kernel replay.
No new public definition, abbreviation or structure is introduced.

```text
HEAD: 9dfe4773331018772857ff7a06ac534813ab1942
Delta baseline: bada4cf6 (round-1 report/handoff commit)
inp at initial comparison: b6dab3a6fc8453330a4abaa465a782e1aa713798
SHA256 KAM/Planetary/WeakKAM/Admissible.lean:
c88e2b4b48b0020ed9411a2df9a76064e3588eee0fe925333df5c4d37e77c4f8
SHA256 KAM/Planetary/WeakKAM/Initial.lean:
1521958286a897c690e13bba5a1085a11634735bf517124eb17974ab94f0f97e
SHA256 /root/code/KAM-inp/.drafts/design/P11BSignatures.lean:
e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63
SHA256 blueprint-P/parts/p11a3-iteration-selection.tex:
90251ed2045353dd2c9574b5f2c53588eb5762ea9dbc86ed9075c00bf8d9ad1c
SHA256 blueprint-P/parts/p11a4-limit-family.tex:
c88030106491131ffde29078d1f0919ae092592bf37e1bbc68a87ab087369b2b
```

Read AGENTS, PLAN, DECISIONS, the audit brief, handoff/AUDIT FOCUS, round 1, the relevant
P11B design mapping and live main-worktree coverage note, live canonical signature slice,
Track P statement, A7/free-radius blueprint text, B06's statement and attachment-relevant
proof, perturbation data, and imported frozen definitions. No frozen theorem is proved or
imported by this package, so provider/frozen type equality and seal-body tests do not apply.
The live signature hash differs from the historical round-1 report; the current B07 slice
was compared directly rather than trusting that older hash.

## Delta and signed interfaces

`git diff bada4cf6 HEAD --stat` and `--numstat` return:

```text
 KAM/Planetary/WeakKAM/Admissible.lean | 34 ++++++++++++++++++++++++++++++++++
 1 file changed, 34 insertions(+)
34  0  KAM/Planetary/WeakKAM/Admissible.lean
```

Precisely: one `public import ...Initial` at line 11 and a 33-line companion block at
283–315, before `free_radius`. Thus “appends 34 lines” is correct as an additive delta;
it is not a literal append to the end of the file. Removing only those two insertions
reproduces `git show bada4cf6:KAM/Planetary/WeakKAM/Admissible.lean` **byte for byte**.
All original definitions, the record, theorem statements and proof bodies are unchanged.

All 15 signed declarations match the current canonical slice after whitespace normalization,
including binder order, 12 definition bodies and all record fields. Fresh Lean examples
also apply both exports to the exact canonical theorem types. The companion has a distinct
name and does not replace or strengthen the premises of a signed export.

## Findings, refutation and ruling

**Round-1 A7 omission: resolved for `adm-choice` by the authorized companion.**
At `p11a3-iteration-selection.tex:215`, A7 says
“ε₀=ε+N C₁ s₀²/2, |R₀|≤ε₀” on the initial domain; line 222 obtains it from `initial`.
The companion at `Admissible.lean:287–294` has exactly the conclusion shape
`(adm_choice conclusion) ∧ (A7 identity) ∧ (A7 pointwise bound)`.
The domain is `selectionDomain d.strip s₀ (actionNbhd d.K t₀)`, with the actual
`adm_params d ε` radii; the remainder is the actual translated `selectionInitial d f`
minus the coordinate expression for the linear frequency term. Neither the norm,
carrier, coefficient `n / 2 * C₁`, nor quantifier over every domain point changes.

Relative to `adm_choice`, the only additions on the input side are the function `f`
and `hf : SelectionPerturbation d f ε`, literally the source premise of
`Initial.lean:158–161`. This record requires holomorphy, period-one periodicity, reality,
and the original perturbation bound (Data.lean:105–112); it does not assume A7, the
translated remainder estimate, or any desired scalar conclusion. Existing `he` and
`hsmall` are retained. The companion does not assume its radius bounds:

- `n ≥ 1` gives `sqrt n ≥ 1`, so `hA.t_le` gives `t₀ ≤ ϑ` (297–302).
- `hA.radius` gives `s₀ ≤ t₀/(8n) ≤ t₀ ≤ ϑ` (303–307).
- Positive λmax, n and C₁ give positive fixed s₀ (308–313), including at ε=0.
- Line 314 supplies `hf`, positive t₀, t₀≤ϑ, positive s₀ and s₀≤ϑ to
  `initial`; projection `.2.1` selects precisely its pointwise bound. `rfl` supplies
  the A7 identity. The first conjunct reuses the actual `adm_choice` proof.

Adversarial checks for a hidden remainder premise, narrower domain, absent radius
condition, altered error normalizer, or circular scalar input found none. No extra
holomorphy/periodicity/reality conclusions from B06 are claimed: the added conclusions
are exactly A7. This is actual consumption of B06, beyond mere import availability.

**Round-1 free-radius mismatch: explicitly deferred, not mathematically discharged.**
`p11a4-limit-family.tex:39` says the later results “hold verbatim”; line 46 is
`fr-other`. The current signed `free_radius` remains a scalar export. The live main
worktree design note, `/root/code/KAM-inp/docs/tracks/P/design/P11B-LEAN-DESIGN.md:255–259`,
records the main-orchestrator ruling “OVERNIGHT 18:17”: the companion repairs A7 and
“graph node `free-radius`/`fr-other` stays NOT_STARTED until B10/B12/B13 do.”
This agrees with the user's explicit ruling and overrides the older coverage mapping
for this delta acceptance. Both local and main-worktree `docs/graph/P/DEPGRAPH.md`
retain NOT_STARTED for the parent at line 26616 and `fr-other` at line 26714.
The local design copy lacks the appended coverage note; this report records the live
ruling without editing that copy or claiming downstream results exist.

The companion specializes the fixed radius, not the adapted radius. The adapted-radius
analytic A7 attachment and later consumer transfer are not proved by this delta, and
this verdict does not close the full `fr-list` or `free-radius` source conclusions.
No new source defect or counterexample was found. The residual is an authorized open
coverage obligation, not a new Lean proof failure.

## Node and declaration inventory

PASS for unchanged rows means delta/interface acceptance; round 1 supplies the scalar
mathematical audit. All names are in `KAM.Planetary`.

| Node / role | Declaration | Verdict | Evidence / scope |
|---|---|---|---|
| sel-data jet size | `selectionM₀` | PASS | Intended actual jet supremum; body unchanged. |
| explicit power-law constant | `selectionChat` | PASS | Signed body unchanged. |
| explicit power-law constant | `selectionCDio` | PASS | Signed body unchanged. |
| loss-choice | `selectionGamma` | PASS | Signed body unchanged. |
| adm-params | `selectionT₀` | PASS | Signed body unchanged. |
| adm-params | `selectiont₀` | PASS | Signed body unchanged. |
| adm-params | `selectionXi` | PASS | Signed body unchanged. |
| adm-params | `selectionThetaMax` | PASS | Signed body unchanged. |
| adm-params | `selectionLambdaMax` | PASS | Signed body unchanged. |
| adm-params | `selectionAdmissible` | PASS | Signed body unchanged. |
| adm-params | `adm_params` | PASS | Signed body unchanged. |
| free-radius schedule | `selectionAdapted` | PASS | Signed body unchanged. |
| scalar A1–A6 record | `SelectionAdmissibility` | PASS | Fields unchanged; does not include A7. |
| positivity helper | `selectionCN_pos` | PASS | Unchanged. |
| seminorm helper | `selectionDGVector_nonneg` | PASS | Unchanged. |
| jet-size helper | `selectionM₀_nonneg` | PASS | Unchanged. |
| geometric helper | `selectionAdm_diam_pos` | PASS | Unchanged. |
| scalar helper | `selectionChat_pos` | PASS | Unchanged. |
| scalar helper | `selectionCDio_pos` | PASS | Unchanged. |
| scalar helper | `selectionGamma_pos` | PASS | Unchanged. |
| cutoff helper | `selectionT₀_pos` | PASS | Unchanged. |
| collar helper | `selectiont₀_pos` | PASS | Unchanged. |
| weight helper | `selectionXi_pos` | PASS | Unchanged. |
| closeness helper | `selectionThetaMax_pos` | PASS | Unchanged. |
| ratio helper | `selectionLambdaMax_pos` | PASS | Unchanged. |
| threshold helper | `selectionAdmissible_pos` | PASS | Unchanged. |
| conditional scalar helper | `selectionAdmissibility_of_bounds` | PASS | Distinct conditional helper, unchanged. |
| adm-choice, ac-lam | `adm_choice` | PASS | Signed scalar export unchanged. |
| ac-list, A7 | `adm_choice_initial` | PASS | Original conclusion plus exactly A7; applies B06. |
| free-radius scalar export, fr-small | `free_radius` | PASS WITH NOTES | Signed scalar contract unchanged; parent remains open. |
| fr-list | helper plus `free_radius` | PASS WITH NOTES | Scalar list only; adapted analytic attachment not newly supplied. |
| fr-other | no theorem claimed | PASS WITH NOTES | Authorized downstream obligation, NOT_STARTED. |

Definition classification: no delta definitions. The unchanged 12 definitions and one
Prop structure retain their round-1 classification and current canonical bodies: one
actual jet supremum; explicit scalar constants and schedules; the output predicate
for A1–A6. The new theorem relies on none of their out-of-domain fallback values:
its fixed radius and all required denominators are positive from standing data.
No new conclusion-shaped hypothesis, namespace shadow or root declaration appears.

## Independent validation

All Lean/Lake invocations ran sequentially with `LEAN_NUM_THREADS=1` and niceness 5.
No clean, update, cache fetch, broad rebuild, resource override or generated-file repair
was requested. Gate waiting was respected.

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b07 KAM.Planetary.WeakKAM.Admissible
[inp-gate] slot 2 acquired 19:09:18 for KAM.Planetary.WeakKAM.Admissible
Build completed successfully (9109 jobs).
exit 0
```

The target and dependencies were replayed. Target diagnostics, unchanged in substance
from round 1 (line numbers shifted by the new import), were:

```text
warning: KAM/Planetary/WeakKAM/Admissible.lean:107:2: Try this: have
The goal is a proposition, so `have` is preferred over `haveI`.
warning: KAM/Planetary/WeakKAM/Admissible.lean:256:50: Variable name `he` is not explicitly referenced.
```

The other replayed warnings concern Schedule, CutoffTensor, CutoffScale, Cutoff,
FourierCutoffTail and StripBudget; these are inherited dependencies, outside this delta.
No warning was emitted for `adm_choice_initial`. The old handoff's blanket “no warnings”
claim remains inaccurate for the whole module.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B07Round2.lean
exit 0
```

The fresh probe imports only the target module, prints axioms for every public theorem,
elaborates the exact canonical types of `adm_choice` and `free_radius` with direct
applications of the real exports, and separately elaborates the literal companion
contract against `adm_choice_initial`. Exact axiom output:

```text
'KAM.Planetary.selectionCN_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionDGVector_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionM₀_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionAdm_diam_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionChat_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionCDio_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionGamma_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionT₀_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectiont₀_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionXi_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionThetaMax_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLambdaMax_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionAdmissible_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionAdmissibility_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.adm_choice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.adm_choice_initial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.free_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Admissible
replaying KAM.Planetary.WeakKAM.Admissible
exit 0
```

One kernel replay invocation, exactly the audited module.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (827 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

Only the brief's explicitly permitted stale generated-root exception failed lint.
Module-system, frozen-anchor and all 144 ABI checks passed. No root was regenerated.

Mechanical hygiene checks: the module has 358 lines (below 1500), maximum Unicode
line width exactly 100, and retains copyright, `module`, public imports, module docstring
and the exposed public noncomputable section. A full-file forbidden-token scan found
no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`, `EuclideanSpace` or
`_root_`. A declaration scan under KAM found each of the 17 public theorem short names
unique, including the sole new name `adm_choice_initial`. A recursive source-import
scan found 63 KAM modules, no provider and no frozen theorem imports. The new Initial
import introduces no DRAFT_SORRY anchor or provider. The frozen imports are definitions,
whose bodies were read for carrier/domain context; their guard results are below.

```text
git diff bada4cf6 HEAD --check
exit 0
git diff --check
exit 0
git diff bada4cf6 HEAD --exit-code -- KAM/Frozen manifest KAM.lean README.md
exit 0 (empty)
```

The required broader `git diff inp...HEAD` was inspected. It warns
“multiple merge bases, using b322eb9fc48c5a2443ea35342817ad047322b08b”. Its protected-path
comparison is empty for KAM/Frozen, manifest and README.md, but contains an inherited
49-line addition to KAM.lean. Thus the brief's whole triple-dot protected-path condition
is not literally empty; the package delta changes none of those paths. This is the
same inherited comparison-scope note as round 1, not a B07b mutation. The generated
root was left untouched.

## Closeout, uncertainties and deliverables

The additive-delta, signed-interface, source-premise, exact-A7, actual-B06-consumption,
unique-name, line-width, standard-axiom and kernel checks pass. Source lint is recorded
with its permitted generated-root exception. There is no open blocker for this ruled
B07b delta. No frozen anchor is sealed. Full free-radius/fr-list analytic coverage and
fr-other consumer transfer remain open as described above; no graph status is upgraded.

No new suspected pinned-source erratum, introduced mathematical deviation, or default
heartbeat failure was found. External Rus01/CP09 PDFs and B10/B12/B13 proofs were not
re-audited; this is a local blueprint/Lean delta audit, not a campaign theorem closure.
The older local design mapping and handoff must be read together with the recorded
main-orchestrator coverage ruling.

Only `/root/code/KAM-inp-p11b-b07/docs/tracks/P/audits/B07-audit-2.md` is delivered.
The temporary B07Round2 probe is removed. No production file, frozen file, manifest,
generated root, or main-worktree report is edited, and no commit is made.

