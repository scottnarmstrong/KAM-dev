# SO-CSPLIT revision 2: independent delta design audit 3

**Overall verdict: PASS WITH NOTES.** Audit 2's blocking F1 is resolved at the signature level: `shadowRun_agree` now requires the retained set to lie inside the initial prefix. The old counterexample is excluded by that premise, and the intended imports caller can derive it from its existing checked plan and segment hypotheses. No new blocking defect was found in this delta. This verdict approves the revised design interface, not completion of its admitted proofs or production calibration.

## Scope and frozen inputs

Audited HEAD `d2b250c5e783d47a3e9771d91e7032b4b9ee4e4e`, parent `4bf0c5f5089fbe657eccc8e31f1a270bbfe824bc`. Read the revision delta, authoritative signatures, handoff delta, audit 2, AGENTS.md, PLAN.md, DECISIONS.md and `/root/code/KAM-inp/.drafts/briefs/inp-audit-design.md`. The focused report/scratch-only scope and refute-first method of the previous audits are retained. No implementation or git state was changed.

| artifact | SHA256 |
|---|---|
| `.drafts/design/SOCsplitSignatures.lean` | `42e25f3f5904e40af5ba7b6d01bfd7c741b41578539aa9a23e98705593e199e9` |
| `docs/tracks/SO/design/SO-CSPLIT.md` | `3420db9d2e1701503110be809e700db11a78d622ac45094ebfe43e76155b6047` |
| `.drafts/handoff-SO-CSPLIT.md` | `425171a60598689d6157523483289bf4707663df5e7f8fb6326eec64a1dd0084` |
| `scripts/spin_orbit/csplit_plan.py` | `60cfe0076098ee706546363a5829726fa06a622696354a763122c6828cadaf16` |

Signatures remain an ignored draft; their hash, rather than the commit alone, fixes this audit's authority. The file has 751 lines, 86 explicit declarations and 13 direct `sorry` bodies.

**Exact signature delta verified:** in memory, removed the two new theorems, restored the previous `shadowRun_agree` docstring and removed its added `hR` binder. The resulting bytes hash to **`c584c7afe06510071ca94dc26eb40664f8c8415819048b21de54d5b4f60f313a`**, exactly the revision-1 signature hash recorded in audit 2. Therefore every other definition, theorem statement and supplied proof—including `compose_eq`, `planOk`, `segPrefixOk`, `seed_stateMeta`, and both templates—is byte-identical to the previously audited artifact. This is stronger evidence than a comparison of displayed excerpts.

## Dispositions and signature ledger

Blueprint label is **N/A** for these computational interfaces. Their specifications are the landed `Expr/Compose` bodies and the checked plan/shadow definitions, rather than I/N/P mathematical blueprint statements. The unchanged declaration ledger from audit 2 is retained; the rows below cover every changed/new signature and its requested consumer interfaces.

All names are relative to `KAM.Certificate`. Line references refer to the hashed revision-2 signatures.

| signature / interface | line | verdict | reason |
|---|---:|---|---|
| `shadowRun_agree` | 325 | PASS | Adds exactly `hR : ∀ i, R i → i < σ.len`; retains the intended agreement conclusion and read conditions. Body remains admitted. |
| `shadowRun_agree_needs_hR` | 340 | PASS | Proves the exact two one-op runs and their failed agreement for the invalid retained set `True`. No admitted dependency. |
| `ComposeCkpt.imports_lt_seed_len` | 356 | PASS | Derives the new domain premise from checked imports, input-meta length and seed length. No admitted dependency. |
| `ComposeCkpt.planOk` | 280 | PASS | Unchanged; every segment's imports are strictly below its start. |
| `ComposeCkpt.segPrefixOk` | 229 | PASS | Unchanged; verifies input-meta length equals segment start and checked indices exist. |
| `ComposeCkpt.segOk` | 252 | PASS | Unchanged; its leading conjunct supplies `segPrefixOk` to the chain caller. |
| `seed_stateMeta` | 319 | PASS | Unchanged, proved; its length projection supplies the seed length. |
| `ComposeCkpt.compose_eq` | 384 | PASS | Unchanged exact landed output; existing hypotheses supply the new internal domain invariant. Body remains admitted. |
| `checkEnergy_of_ckpt` | 719 | PASS | Unchanged consumer of the same chain interface, with singleton wanted check and energy residual. |
| `checkInvariance_of_ckpt` | 733 | PASS | Unchanged consumer of the same chain interface, with derivative-slot wanted check and row residuals. |

**Audit-2 F1: RESOLVED.** The correction is an internal state-domain invariant, not a new assumption on the Hamiltonian or a conclusion-shaped premise. No weakened mathematical conclusion or replacement frozen object is introduced.

**Audit-2 N1: RESOLVED as an evidence-labeling/planner issue.** The design now calls the totals formatted-definition plus overhead estimates, lists the plan/cache allowance and product/module headers among the estimates, and preserves an actual emitted-tree byte/line-count gate. UTF-8 plan counting and dead-product memo filtering are implemented. The revised numerical totals reproduce below.

**Audit-2 N2: RESOLVED.** Summary decode costs are marked projected pending G4, the evaluated product count is 128 in the relevant tables, and the invariance recipe/package use `all_range_of_lt`. The lock section adds an explicit SO-KDEPTH2 dependency rather than claiming an already working lock jet bridge.

## Independent counterexample replay

Replayed the audit-2 example directly against the exact current definitions, without invoking either the designer's negative-test theorem or any admitted theorem:

```lean
σ = X = (⟨[], 0, 0, 0, []⟩ : ComposeState α)
R = fun _ => True
s = (⟨0, 1, [], [], []⟩ : SegSpec)
os = [.const 0 0 1]
```

The shadow and landed runs still succeed and disagree on slot 0's degree, yielding the same contradiction `(0 : ℤ) = 1` if agreement on `True` is asserted. That behavior is correct: the counterexample demonstrates why the additional premise is necessary.

Independently proved that the new premise is impossible for this example:

```lean
¬ (∀ i : ℕ, True → i < (⟨[], 0, 0, 0, []⟩ : ComposeState α).len)
```

Apply the proposed bound at index 0 to get `0 < 0`. Thus the old counterexample cannot instantiate the revised theorem. The replay and premise-rejection proofs have only `[propext, Classical.choice, Quot.sound]`; neither uses `sorryAx`.

The signature retains agreement only on old slots and faithfully computed new slots. Restricting old `R` to the initial prefix closes the precise failure exposed in audit 2: a skipped later slot can no longer become an obligation through membership in the original retained set. No second counterexample was found in this bounded delta check. The general induction is still proof work, not proved here.

## Intended caller and template consistency

Proved independently in scratch, without using `imports_lt_seed_len` or an admitted lemma, that the **actual chain hypotheses** entail:

```lean
∀ i, i ∈ s.imports → i < (ComposeState.seed W m C s.imports).len
```

Inputs were exactly `hplan : C.planOk p.ops.length = true`, the chain's existing `hseg`, an in-range segment index and the checked segment/meta lookups. The derivation was:

1. Extract `segPrefixOk` from the leading conjunct of `hseg j hj`.
2. Extract `m.len = s.start` from that prefix check. An absent next meta contradicts the successful check.
3. Obtain `s ∈ C.segs` from its checked lookup, then extract `i < s.start` for each import from `planOk`.
4. Project `ComposeMeta.len` from the proved `seed_stateMeta` equality to obtain `seed.len = m.len`.
5. Rewrite the bound to `i < seed.len`.

This independent theorem has no `sorryAx`. The designer's `imports_lt_seed_len` proves the same fact with Boolean membership; ordinary list membership converts to that form. No extra hypothesis needs to be added to `compose_eq` or to either certificate template.

The chain still projects the landed full composition to the requested ledger slots, with whole cached pairs tracked internally. Both templates retain the same `hplan` and `hseg`; only `wantedOk` and their final residual differ. The `hR` premise belongs to the internal segment comparison and is discharged there. The new helper therefore repairs proof feasibility while preserving every public consumer interface.

## Notes and remaining scope

### N1 — Informational: this remains a design with admitted core proofs

The same 13 theorem bodies are admitted: five comparator reflections, six M1 lemmas including `shadowRun_agree` and `compose_eq`, and two entry-table lemmas. The two newly added theorems are genuinely proved, but the energy/invariance template proofs still inherit `sorryAx` through the admitted chain. This is explicitly disclosed and allowed for the requested scratch signature artifact. Production modules must satisfy the repository's frozen-only sorry rule; this audit does not authorize landing these draft admissions.

Proposed follow-through: prove the existing package targets at default budgets and rerun the package/axiom checks. No further signature correction is requested by this delta audit.

### N2 — Informational: production cost and volume remain gated

The revised volume estimates reproduce:

| torus / budget | cfgFull / cfgLow segments | estimated bytes |
|---|---:|---:|
| lower / 75k | 38 / 70 | 10,372,136 |
| upper / 75k | 38 / 70 | 10,336,274 |
| lower / 150k | 20 / 33 | 8,510,417 |
| upper / 150k | 20 / 33 | 8,452,111 |

These are estimates, not actual emitted-tree receipts. CAL-1 G0–G5 and CAL-2 G6–G7 remain required; their dependency order is unchanged and consistent. The new lock SO-KDEPTH2 note is an explicit external dependency, not a result independently verified here. No lunar or lock production memory guarantee follows from signature elaboration.

## Verification and closeout

All Lean/Lake processes ran serially in this worktree with `LEAN_NUM_THREADS=1`, `nice -n 5`, and default heartbeat/depth budgets.

- **Required elaboration, once:** copied the authoritative file unchanged to `.drafts/scratch/SOCsplitSignatures.lean`; ran `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .drafts/scratch/SOCsplitSignatures.lean`. **Exit 0**, exactly 13 sorry warnings and no errors or other warnings. Warning declaration lines: 125, 128, 131, 134, 137, 303, 307, 314, 325, 377, 384, 561, 579.
- **Independent replay/discharge probe:** `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOCsplitAudit3.lean`. Final **exit 0**. Besides the copied draft's 13 warnings, the scratch premise-rejection theorem has an unused-instance warning. An initial scratch attempt incorrectly treated `Bool.and_eq_true` as an iff; the actual declaration is a proposition equality. Replacing that projection with `simp only [ComposeCkpt.segOk, Bool.and_eq_true]` fixed the probe without any option change.
- **Mathlib/Lean names:** `#check List.mem_of_getElem?` and `#check Bool.and_eq_true` passed with their actual types. All other names in the newly supplied proofs resolved in the successful exact-signature elaboration.
- **Planner replay:** ran `python3 -B -I scripts/spin_orbit/csplit_plan.py CENSUS B 0` for lower/upper and B = 75000/150000, each **exit 0**; results above. Planner AST parse passed. Full censuses and production kernel calibrations were not rerun.
- **Source hygiene:** `git diff --check inp...HEAD` passed. Live source lint and final report/input checks are recorded below. No new library Lean module was introduced, so direct signature elaboration is the applicable target; no library rebuild was performed.

Independent `#print axioms` results:

| result | axioms |
|---|---|
| audit counterexample replay | `[propext, Classical.choice, Quot.sound]` |
| audit rejection of the old R under hR | `[propext, Classical.choice, Quot.sound]` |
| audit derivation of hR from chain hypotheses | `[propext, Classical.choice, Quot.sound]` |
| `shadowRun_agree_needs_hR` | `[propext, Classical.choice, Quot.sound]` |
| `ComposeCkpt.imports_lt_seed_len` | `[propext, Classical.choice, Quot.sound]` |
| `seed_stateMeta` | `[propext, Classical.choice, Quot.sound]` |
| `shadowRun_agree` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `ComposeCkpt.compose_eq` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `checkEnergy_of_ckpt` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `checkInvariance_of_ckpt` | `[propext, sorryAx, Classical.choice, Quot.sound]` |

**Consumers: PASS for this delta. Definitions: PASS for this delta. Frozen objects: unchanged. Packages/calibration order: PASS at design level.** The reconstructed prior signature hash establishes that the previously audited product, sparse, stage, frame and checker contracts are untouched. The repository diff contains no implementation/frozen/manifest edits. No new external-source erratum or implementation deviation was found. The remaining proof and calibration obligations are the disclosed notes above, not unresolved signature blockers.

Final live lint: `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`, **exit 0**:

```text
check_lean_modules: PASS (1686 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

Final input hashes match the snapshot. Report whitespace and fence balance pass; temporary signature copy and audit probe are removed. The only remaining worktree change is `docs/tracks/SO/design/SO-CSPLIT-design-audit-3.md`.
