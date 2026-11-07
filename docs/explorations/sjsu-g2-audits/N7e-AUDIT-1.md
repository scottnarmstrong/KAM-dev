Audited commit: `55b51b998834b5c70bed604c6e7b6135468d06bb` (initial HEAD); SHA256: `KAM/EffectiveStability/Tube/Engine/DropChunk.lean=b46d0c01f7425b5fcaab47d1ccbafecb247db3692573c9f3c54acf1ba39e82d4`.

# N7e / N7-Engine part 5 — audit 1

**PASS WITH NOTES.** All four theorem statements and proofs satisfy the launch's checker contract. Additivity is exact, chunk coverage preserves every F entry, and the assembly concludes precisely the existing downstream `dropCheck` Boolean from checkable premises. The targeted build, every theorem's axiom check and the corrected exact-consumer/edge probe passed. The note is repository hygiene: the required lint exited 1 solely for stale generated roots. This is not a global lint pass or acceptance of production ledger certificates or T2-CONF.

## Scope and immutable inputs

The audited package is the single core module `Tube/Engine/DropChunk.lean` introduced by the launch commit. Read AGENTS, PLAN, DECISIONS, AUDIT-N7e-launch, AUDIT-PKG-brief, WORKER-RULES, BRIEF-N7-Engine, the DRAFT N7 handoff, and the required route/gate/ApproxIntegral context. The handoff currently describes parts through 4; the launch and actual part-5 declaration bytes control this review. This is a focused tier-2 statement/proof audit with a separate adversarial pass and hygiene checks. No implementation repair was authorized or made; no subagent was used.

The permission envelope is the user's report-only instruction plus the launch's expressly required targeted build and stdin axiom queries. No scratch source file was created. Only this report is authored; build-cache effects come from the requested validation. The pre-existing modified producer scripts and untracked generated ledger files belong to other workers and were left alone. No producer was run and no `KAM/EffectiveStability/SJSU/Ledger/**` module was built or imported by this audit.

Supporting context was read for the exact definitions, chunk indexing and downstream contract, rather than re-audited as a whole. Its snapshot hashes are:

| Context file | SHA256 |
|---|---|
| `Tube/Engine/Drop.lean` | `4e7780587db998a06de202cb83dc3f75cacc914194f19a09e0fac5fa53c9044c` |
| `Tube/Engine/BrChunk.lean` | `5b8aadb3f9e36c327900f87c079b6d9c89c3a0fd1b8024816d98f4ee26cda254` |
| `Tube/Check/BracketBound.lean` | `9b02ad2504627e8819edd158440c36cf6aee01f1dff2fca06efbda5bab7bdf1e` |

All paths in the table are relative to `KAM/EffectiveStability/`. All four files matched `git show 55b51b998:<path>` byte-for-byte before classification. All line references below refer to this snapshot.

## Statement and proof review

| Declaration | Exact obligation | Result |
|---|---|---|
| `sum_chunks_of_additive`, 27–43 | For any `S : List α → ℚ` satisfying the empty-list and append identities, `l.length ≤ m*n` gives `S l = Σ_{k<n} S (chunk l m k)`. | PASS |
| `dropSum_nil`, 45–47 | The existing dropped-part sum on an empty F list equals zero, with arbitrary remaining data. | PASS |
| `dropSum_append`, 49–53 | The existing dropped-part sum on `l₁ ++ l₂` equals the sum on the two lists, with identical H data, radius, cutoff and parameters. | PASS |
| `dropCheckC`, 55–59 | Exact rational decision of `dropSum ... (chunk Fl m k) Hl ≤ Dk`. | PASS |
| `dropCheck_of_chunks`, 62–72 | Nonnegative radius, full coverage, every required chunk check, and the rational total-claim comparison imply the original `dropCheck ... Fl Hl D = true`. | PASS |

**Additivity.** `Drop.lean:56–62` defines `dropSum` by nested list maps and rational sums. The outer axes are `[0,1]`; each axis contains a sum over F entries. For each fixed F entry, the expression depends on that entry, the axis, kind, H list and shift, but never on the complete F list. Thus `dropSum Fl` is a sum of fixed per-entry contributions. `dropF`, `dropH` and `dropC` contain absolute values, and `dropC` has a degree cutoff, but those operations act on individual terms. There is no rounding, maximum, norm or list-dependent normalization applied after the F sum. The proof's `map_append`, `sum_append` and `sum_map_add` exactly distribute that sum. The two additivity lemmas do not need `r ≥ 0`; they are algebraic identities for every rational radius.

**Coverage.** `BrChunk.lean:25–31` defines `chunk l m k = (l.drop (m*k)).take m` and proves its successor identity. The new induction splits `l` as `take m ++ drop m`, applies append additivity, and derives `length (drop m l) ≤ m*n` from `length l ≤ m*(n+1)`. `List.range_succ_eq_map` enumerates precisely the first block and all shifted remaining blocks. This partitions positions, preserving duplicates and order. A partial last chunk and extra empty chunks are safe. If `m=0` or `n=0`, coverage forces `l=[]`. There is no omitted-tail assumption, positivity restriction or divisibility requirement. For the launch's 87-entry list and size 4, 22 chunks cover all entries, with a final chunk of 3; the theorem does not hard-code either number.

**Assembly.** `dropCheck_of_chunks` unfolds the *existing* `Drop.dropCheck`, whose body at `Drop.lean:65–67` is `decide (0 ≤ r) && decide (dropSum ... Fl Hl ≤ D)`. It supplies the first conjunct from `hr`, rewrites the second using the proved additivity/coverage equality, obtains each chunk inequality from `hk`, sums those inequalities over exactly `List.range n`, and applies `hD`. Neither the radius guard nor the total budget is dropped. No new Boolean, renamed semantic predicate, cast, changed radius or altered data stands in for the original checker.

**Consumption.** `Drop.dropCheck_sound:217–239` accepts precisely that original Boolean. The stdin composition probe applies

```lean
dropCheck_sound (dropCheck_of_chunks hr hlen hk hD)
  hb hF hH w₀ hS0 hb0 hu φ
```

to the complete existing dropped-bracket inequality, retaining the same `Pb`, `HL`, `nH`, `r`, `L`, `Fl`, `Hl`, `D`, evaluation maps, point and packing-scale equalities. This is exactly `Check/BracketBound.reducedBracket_bound_of_drop`'s `hDrop` at lines 287–288 after specializing `μ = muF`, `ν = monOf`, the literal evaluation maps, and rational-to-real radius/budget casts. The new theorem produces the Boolean; the existing soundness theorem produces that analytic bound. The remaining kept-coefficient, differentiability, model-error, decomposition and tail hypotheses of BracketBound remain separate obligations.

## Hypotheses and refutation pass

These are generic algebra/checker results, not manifest-bound external-source anchors. SOURCE below denotes the structural/numerical contract requested by the launch. All data parameters are unrestricted typing data; no standing source theorem is assumed.

| Logical binder | Classification | Expanded content |
|---|---|---|
| `sum_chunks_of_additive.h0` | SOURCE | Structural identity `S [] = 0`. |
| `sum_chunks_of_additive.hadd` | SOURCE | Structural append additivity for every pair of lists. |
| `sum_chunks_of_additive` coverage binder | SOURCE | Decidable natural-number inequality `l.length ≤ m*n`. |
| `dropCheck_of_chunks.hr` | SOURCE | Decidable rational inequality `0 ≤ r`. |
| `dropCheck_of_chunks.hlen` | SOURCE | Decidable coverage of the actual F list. |
| `dropCheck_of_chunks.hk` | SOURCE | For every `k<n`, the exact rational chunk sum is at most `Dc k`, via its decidable Boolean. |
| `dropCheck_of_chunks.hD` | SOURCE | Decidable rational comparison `Σ_{k<n} Dc k ≤ D`. |

Counts: 7 SOURCE, 0 STANDING, 0 RULED, 0 EXCESS. The generic theorem's data binders are `α,S,m,n,l`; the two concrete additivity lemmas have only data binders. The assembly theorem's eleven implicit data binders are `Pb,HL,nH,r,L,Fl,Hl,m,n,Dc,D`. The generic identities `h0/hadd` are not left as native checker premises: the assembly proof supplies the concrete `dropSum_nil` and `dropSum_append`. `hk` and `hD` concern finite rational computations, not an assumed analytic bracket bound. Values of `Dc` outside `k<n` do not enter the result.

The separate adversarial pass attempted to break additivity using the degree branch/absolute values, omit a nonempty suffix using insufficient coverage, erase duplicate entries, exploit zero chunk size or count, omit the radius guard, or assume the original full-list estimate through a helper. Each candidate was refuted by the literal definitions and proof steps above. Independent position/rational arithmetic and the Lean edge/consumer probes provide additional checks. No surviving in-scope mathematical or statement finding was identified. There is no pending unrefuted mathematical warning.

The module docstring's exactness claim is justified at the generic level: summation is rational and exact, and each chunk is checked against its supplied claim. Actual producer rounding policies, numerical claim values, the historical 10 GB failure and the resource cost of production chunks were not measured here. The launch's approximate 75-line description is 76 actual lines; this has no mathematical or size-limit consequence.

## Verification receipts

Exactly one targeted build was invoked:

```text
.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Engine.DropChunk
exit 0
Build completed successfully (2951 jobs).
```

This is a warm build with replayed dependency warnings, not a clean-build timing experiment. The warning replay concerns dependency deprecations and unused arguments/tactics; no warning or default-heartbeat failure was attributed to DropChunk. The prescribed wrapper serializes through `.drafts/g2/lake.lock`, waits for memory, applies nice 5 and a 6 GB memory cap, and sets `LEAN_NUM_THREADS=2`. It was used unchanged; no direct Lake/Lean invocation, broad build, clean or resource override was used.

`.drafts/g2/g2lake env lean --stdin` imported only DropChunk and ran `#print axioms` for every theorem declared in it. Exit 0; complete output:

```text
'KAM.EffectiveStability.Tube.sum_chunks_of_additive' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.Tube.dropSum_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.Tube.dropSum_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.Tube.dropCheck_of_chunks' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The additional stdin probe checks the exact Boolean conclusion, the full composition with `dropCheck_sound`, duplicate preservation, a partial last chunk, an extra empty chunk, zero chunk size, rejection of insufficient coverage, the polymorphic empty-list equality and rejection of a negative radius. Its first invocation exited 1 solely because the auditor used `by decide` on `[].length ≤ 0*4` with a free element type: “Expected type must not contain free variables”. The two consumer examples produced no diagnostics. The empty-list coverage proof was corrected to `by simp`; no package source was changed. The corrected complete probe, run through `.drafts/g2/g2lake env lean --stdin`, waited approximately 21 minutes on the shared production lock and then returned **exit 0, no diagnostics**. No audit Lean/Lake command remains running.

Independent Python, importing no producer and using `fractions.Fraction`, flattened positional chunks and compared their signed rational sums for all lengths 0..40, sizes 0..10 and counts 0..44 satisfying coverage. Output:

```text
INDEPENDENT_POSITION_AND_RATIONAL_SUM_PASS 15949
PRODUCTION_COVERAGE_87_BY_4 True LAST_CHUNK_SIZE 3
```

Mechanical inspection: 76 lines, maximum 98 characters per line, required copyright/module/public imports/docstring/exposed public section present. Both imports are core Engine modules. No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`, proof escape, provider/draft/application-root import or `EuclideanSpace` appears in the target. Its analytic consumer retains `Fin 3 → ℝ` and `Fin 2 → ℝ`; the integer triples here index monomials.

The required `PYTHONDONTWRITEBYTECODE=1 .drafts/g2/lint_noabi.sh` was invoked once and ran to completion: **exit 1**. Complete diagnostic/test output, apart from unittest progress dots:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean, KAMSJSU/EffectiveStability/SJSU/Check.lean, KAMSJSU/EffectiveStability/SJSU/Confinement.lean, KAMSJSU/EffectiveStability/SJSU/Ecc.lean, KAMSJSU/EffectiveStability/SJSU/Ham.lean, KAMSJSU/EffectiveStability/SJSU/Initial.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/Br/Top0.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/Br/Top1.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/Br/Top2.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/F.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/H/Top0.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/H/Top1.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/H/Top2.lean, KAMSJSU/EffectiveStability/SJSU/Ledger/Top.lean, KAMSJSU/EffectiveStability/SJSU/Model.lean, KAMSJSU/EffectiveStability/SJSU/Obs.lean, KAMSJSU.lean, KAMSJSU/EffectiveStability.lean)
check_lean_modules: PASS (20732 Lean files, 0 comparator configurations)
----------------------------------------------------------------------
Ran 29 tests in 4.583s

OK
----------------------------------------------------------------------
Ran 8 tests in 0.008s

OK
FROZEN-ANCHOR GUARD OK
```

The sole lint failure is generated-root drift in the shared tree. Refutation of an in-scope source failure: the target and three context files match the pinned commit, the named target builds independently of generated roots, the module checker passes, and the anchor guard passes. This does not waive the failed root check: repository lint is **not green**. Suggested follow-up is orchestrator regeneration/checking of the roots when landing the corresponding modules; protected roots were not edited in this report-only audit. `abi_hashes` was skipped under WORKER-RULES' explicit lint amendment; the full `scripts/lint_sources.sh` was not substituted because its ABI step invokes Lake outside the required wrapper.

## Closeout boundary

At final integrity verification (7 November 2026, 02:50 UTC), HEAD remained `55b51b998834b5c70bed604c6e7b6135468d06bb` on `inp-sjsu-g2`. The target and all three context hashes remained exactly as recorded above; `git diff --exit-code 55b51b998 -- <the four paths>` returned 0 with no output. The only authored repository change is this report; the pre-existing producer changes and generated/untracked files remain outside this audit.

All in-scope statements, hypotheses, proof steps and requested validation receipts are classified and complete. No suspected new erratum in a pinned external source was found. No mathematical deviation was introduced. The launch's stdin instruction was used instead of the generic audit brief's scratch-file instruction, respecting the user's report-only constraint. The explicit worker lint amendment controls the ABI omission. The scoped PASS WITH NOTES does not certify the emitted production Drop checks, producer correctness, numerical eta, physical-model attachment or T2-CONF closure.

READY g2-audit-n7e-1
