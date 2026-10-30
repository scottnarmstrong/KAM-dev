# SO-CSEG-A/B: audit request (segmented composition: definitions, agreement, chain, one-op segments, bridges)

**Scope.**
- Branch `inp-socsplit2`, worktree `/root/code/KAM-inp-socsplit2`.
- Packages SO-CSEG-A and SO-CSEG-B of the design `docs/tracks/SO/design/SO-CSPLIT.md` (revision 2; design
  audit 3 PASS WITH NOTES), §3.2–3.3 and §8.
- Plus `Kernel/SegOne.lean`: the deferred half of the L3 row, moved to this scope by the orchestrator. Its
  content is signatures §(C).
- No frozen file, manifest, README, `KAM.lean`/`KAM/Root` or landed definition was touched.

**All A/B declarations are proved, with no `sorry`.** The audited signature file's 11 admitted A/B declarations
are now theorems:
- the five comparator reflections (`eq_of_termsBeq`, `CertPoly.eq_of_segBeq`, `CertModel.eq_of_segBeq`,
  `eq_of_pairBeq`, `eq_of_cacheBeq`);
- `pushSlot_slot_lt`, `composeStep_congr`, `seed_slot_of_mem`, `shadowRun_agree`,
  `composeOpsAux_slot_persist`;
- `ComposeCkpt.compose_eq`.

The two remaining admitted signatures, `modelMatMul_eq_of_entries` and `gramModels_eq_of_entries`, belong to
SO-CSEG-L2.

## Files (all new)

| file | lines | content |
|---|---:|---|
| `KAM/CertificateSharp/Kernel/SegDefs.lean` | 344 | **A.** Comparators `keyBeq`, `SlpOp.segBeq`, `opsBeq`, `HamJet.segBeq`, `ccBeq`, `termsBeq`, `CertPoly.segBeq`, `CertModel.segBeq`, `pairBeq`, `cacheBeq`, `ComposeMeta.segBeq`, each with its reflection (`eq_of_keyBeq`, `SlpOp.eq_of_segBeq`, `eq_of_opsBeq`, `HamJet.eq_of_segBeq`, `eq_of_ccBeq`, `eq_of_termsBeq`, `CertPoly.eq_of_segBeq`, `CertModel.eq_of_segBeq`, `eq_of_pairBeq`, `eq_of_cacheBeq`(`_aux`), `ComposeMeta.eq_of_segBeq`). The instance `instDecidableEqCertFixedSeg`. The data `ComposeMeta`, `SegSpec`, `ComposeCkpt`. `SlpOp.fallible`, `stateMeta`, `pairOpt`, `slotPair`, `liveEff`, `SegSpec.ops`, `seed`, `shadowStep`, `shadowRun`. The checks `segPrefixOk`, `segResultOk`, `segOk`, `segsTile`, `ledgerAsc`, `exported`, `planOk`, `wantedOk`. |
| `KAM/CertificateSharp/Kernel/SegAgree.lean` | 393 | **A.** `AgreeOn`; slot persistence (`slot_of_cons`, `slot_of_cons_self`, `pushSlot_slot_lt`); `AgreeOn.retain`, `AgreeOn.of_push`; `composeStep_infallible`, `composeStep_push`; **`composeStep_congr`** (all 8 arms); `seed_len`, `seed_stateMeta`, `seed_slot_of_mem`, `seed_agree`; `live_cons_zero/succ`, `shadowStep_len`, `shadowRun_len`; **`shadowRun_agree`** (with the domain premise `hR`); `composeOpsAux_slot_persist(_le)`. |
| `KAM/CertificateSharp/Kernel/SegChain.lean` | 298 | **B.** `composeOpsAux_none/append`, `segsTile_cons`, `segsTile_start_ge`, `SegSpec.ops_getD/ops_length`, `segBoolImp`; `ComposeCkpt.imports_lt_seed_len` (the `hR` discharge); `ComposeCkpt.seg_step` (one segment); `ComposeCkpt.chain_go` (induction over the tiling); **`ComposeCkpt.compose_eq`**. |
| `KAM/CertificateSharp/Kernel/SegOne.lean` | 78 | **§(C), from L3.** `shadowStep_of_live`, **`ComposeCkpt.segOk_one_of`**, and the arm equations `composeStep_const_eq`, `composeStep_add_eq`, `composeStep_mul_eq`, `composeStep_char_eq`. |
| `KAM/CertificateSharp/Kernel/SegBridges.lean` | 82 | **B.** `all_range_of_lt`, `checkInvariance_eq_of_compose`, `checkEnergy_eq_of_compose`, and the assembly templates **`checkEnergy_of_ckpt`**, **`checkInvariance_of_ckpt`**. |
| `KAM/CertificateSharp/Tests/Seg.lean` | 220 | **Tests**, below. |

Every module is a Lean module: copyright, `module`, `public import`, module docstring and
`@[expose] public section`. Every file is at most 400 lines, as the design budgets, and every line is at
most 100 columns. There is no `sorry`, `axiom`, `admit`, `unsafe`, `opaque`, and no heartbeat or depth option.

## Signatures matched against the audited design

**Authority.** The audited signature file is revision 2, sha256 `42e25f3f…e199e9` (design audit 3, line 11). It
is kept unchanged as `.drafts/design/SOCsplitSignatures.rev2-audited.lean`.

**Textual comparison.** A normalized header comparison (binders and statement up to `:=`) of every
declaration it shares with the production modules found 59 shared declarations:
- **57 are verbatim identical.**
- **`eq_of_termsBeq`** has the identical statement. The comparison regex cuts the term-mode match into the
  header.
- **`shadowRun_agree_needs_hR`** has the identical statement with an explicit `{α : Type} [CertArith α]`, because
  it moved to the test file, outside the `variable` section.

**Design-name deviations (signed names renamed for the short-name rule; statements unchanged).**
The audit launcher refused the first request: the short names `pair` and `beq` are reused in Mathlib
(`WalkingPair`, `Tactic/Translate/Reorder`). Every use and the tests are updated. The remaining signatures
draft mentions none of these names, so it needed no change; it re-elaborates at rc = 0 with its 2 L2 `sorry`s.

| audited (signed) name | renamed to | why |
|---|---|---|
| `ComposeCkpt.pair` | `ComposeCkpt.slotPair` | short name `pair` reused in Mathlib |
| `SlpOp.beq` | `SlpOp.segBeq` | short name `beq` reused in Mathlib |
| `HamJet.beq` | `HamJet.segBeq` | the same short name `beq`; the checker reports it once `SlpOp.beq` is gone |
| `ComposeMeta.beq` | `ComposeMeta.segBeq` | the same, pre-empted |
| `SlpOp.eq_of_beq`, `HamJet.eq_of_beq`, `ComposeMeta.eq_of_beq` | `….eq_of_segBeq` | kept parallel to `CertPoly.eq_of_segBeq` and `CertModel.eq_of_segBeq` |

Each renamed declaration has exactly the audited statement and body, apart from the names of the renamed
functions it mentions. The design document §3.2–3.3 still uses the audited names, and this table governs.
SO-LOCK-COST's planned `jetBeq` is `HamJet.segBeq`.

**Other deviations** (additions only; no audited statement changed):
1. `composeOpsAux_slot_persist` has the exact audited statement. It is the `.1` of the new, stronger
   `composeOpsAux_slot_persist_le`, which also gives `st.len ≤ st'.len`.
2. `eq_of_cacheBeq` has the exact audited binder form. The recursion is `eq_of_cacheBeq_aux`.
3. `shadowRun_agree_needs_hR` (the audit-2 negative contract test) moved from `SegAgree` to `Tests/Seg.lean`
   to keep `SegAgree` within its 400-line budget.
4. Helper lemmas not in the signature file: `eq_of_ccBeq`, `ComposeMeta.eq_of_segBeq`, `slot_of_cons(_self)`,
   `AgreeOn.retain`, `AgreeOn.of_push`, `composeStep_push`, `seed_len`, `seed_agree`, `live_cons_zero/succ`,
   `shadowStep_len`, `shadowRun_len`, `composeOpsAux_none/append`, `segsTile_cons`, `segsTile_start_ge`,
   `SegSpec.ops_getD/length`, `segBoolImp`, `ComposeCkpt.seg_step`, `ComposeCkpt.chain_go`, and the four
   `composeStep_*_eq` arm equations. All are proved, with no premise beyond typing data.
5. The test toy is a verbatim copy, with renamed identifiers, of `Certificate/Tests/Compose.lean`'s toy. That
   file's definitions are in a non-`@[expose]` section, so the kernel cannot unfold them from another module.

**The remaining draft.** `.drafts/design/SOCsplitSignatures.lean` (sha256 `ec88f62f…e8c2`) now imports the
production modules and keeps only §(D) (L3), §(E) (L2) and the L2 bridges of §(F).
- It elaborates at default heartbeats: **rc = 0, exactly 2 sorry warnings** (`modelMatMul_eq_of_entries`,
  `gramModels_eq_of_entries`; both L2).

## Approach

**`composeStep_congr`.** The congruence is proved arm by arm:
- each arm reads only the metadata and the pairs of `opDeps op`;
- `AgreeOn.of_push` extends the agreement by the common new entry;
- the `sqrt` arm is handled by `split`, because its `find?` lambda carries the landed `BEq` instance.

**`shadowRun_agree`.** By induction on the operations:
- a **live or fallible** op uses `composeStep_congr` with `R ∪ {len}`;
- a **dead infallible** op compares the landed push against the placeholder, keeping `R` (inside the prefix by
  `hR`);
- the index shifts use `live_cons_succ`.

**The chain.** `seg_step` takes one segment from its start state to its stop state:
- **reads:** the prefix check supplies the reads, converted into `shadowRun_agree`'s index form via
  `SegSpec.ops_getD`;
- **seed and `hR`:** the seed agrees with the landed state on the imports, and `imports_lt_seed_len`
  discharges `hR`;
- **landed run:** it is spliced by `List.take_add` and `composeOpsAux_append`;
- **exports and meta:** the result check gives the exports and the output meta, through the reflections.

`chain_go` inducts over the remaining segments. Its invariant: the landed run on the prefix exists, carries the
boundary meta, and agrees with the ledger on the exports of the processed segments. An import of segment `j` is
exported by a segment in `take j`, because every segment in `drop j` starts at or after the current start
(`segsTile_start_ge`). `compose_eq` starts the induction from `planOk`'s initial meta and projects the wanted
slots through `wantedOk`, `find?` and `exported`.

## Builds

Each module was built alone through the compile gate (`inp_lake_build.sh`, one at a time), at default
heartbeats, with **rc = 0 and no warnings in these files**:

| module | build time |
|---|---:|
| `Kernel.SegDefs` | 3.3 s |
| `Kernel.SegAgree` | 3.7 s |
| `Kernel.SegChain` | 3.4 s |
| `Kernel.SegOne` | 2.6 s |
| `Kernel.SegBridges` | 2.8 s |
| `Tests.Seg` | 13 s |

(These are the rebuilds after the renames.)

No design signal arose in these modules. The two whnf-heartbeat signals of the design phase
(`simp`/`congr` over landed bodies) concerned §(E) proofs and were already handled there.

## Axioms (`#print axioms`, from a scratch file importing `Tests.Seg`)

| declaration | axioms |
|---|---|
| `ComposeCkpt.compose_eq`, `shadowRun_agree`, `composeStep_congr`, `ComposeCkpt.chain_go`, `ComposeCkpt.seg_step`, `ComposeCkpt.imports_lt_seed_len`, `ComposeCkpt.segOk_one_of`, `checkEnergy_of_ckpt`, `checkInvariance_of_ckpt`, `checkInvariance_eq_of_compose`, `checkEnergy_eq_of_compose`, `seed_slot_of_mem`, `composeOpsAux_slot_persist`, `shadowRun_agree_needs_hR`, `segTest_compose`, `segTest_seg1`, `segTest_badRadius` | `[propext, Classical.choice, Quot.sound]` |
| `HamJet.eq_of_segBeq`, `ComposeMeta.eq_of_segBeq` | `[propext, Quot.sound]` |
| `eq_of_pairBeq`, `eq_of_cacheBeq` | `[propext]` |

No result depends on `sorryAx`. In particular the templates no longer inherit it: they depended on the admitted
`compose_eq` in the draft.

## Tests (`KAM/CertificateSharp/Tests/Seg.lean`; `decide +kernel` in `ℚ`)

**The toy.** It has 11 operations: an action, constants, a scalar product, two characters sharing one witness
via `conjReflect`, sums, a product, an `exp` and an `inv` witness. The checkpoint has segments `[0,5)` and
`[5,11)`, wanted slot 10, ledger slots {0, 1, 10}, and its metas come from the landed `composeOps`.
- Dead infallible ops 2, 5, 6 are skipped.
- The fallible ops 3, 4 (char), 7 (exp) and 8 (inv) always run.

**Positive:**
- `segTest_plan`, `segTest_seg0`, `segTest_seg1`, `segTest_wanted`;
- `segTest_compose`: `Slp.compose … [10] = some [(C.slotPair W 10).1]`, obtained by **applying `compose_eq`**, with no
  evaluation of the composition in that proof.

**Negative** (`= false`):

| test | corruption |
|---|---|
| `segTest_badRadius` | an export with a wrong radius |
| `segTest_badNorm` | an export with a wrong cached norm |
| `segTest_missingImport` | a missing import |
| `segTest_deadRead` | a dead read (slot 9 not live but read by live slot 10) |
| `segTest_badCounter` | a wrong exp counter |
| `segTest_badCacheOrder` | a reversed cache |
| `segTest_badInitMeta` | a malformed initial meta (`planOk = false`) |
| `segTest_badTiling` | a non-tiling plan |

**Contract:** `shadowRun_agree_needs_hR`, the audit-2 counterexample. Without `hR` the agreement conclusion is
false.

**Jet:** `segTest_jetBeq` (a jet equal to itself), `segTest_jetBeq_ne` (one changed op gives `false`), and
`segTest_jet_eq` via `HamJet.eq_of_segBeq`.

## Lint and names

- **`sh scripts/lint_sources.sh`: rc = 1, for one expected reason.** The output is
  `KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/CertificateSharp.lean)`. Rule 10 forbids
  provers to edit the root, so it is regenerated at landing. The other checks pass:
  `check_lean_modules: PASS (1686 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (158 frozen declarations)`.
- **`main_shortname_check.py` on the six modules: `short-name check OK (no reused public short name)`, rc = 0**,
  after the renames below. My own helper `AgreeOn.mono` was also renamed `AgreeOn.retain`, to clear a Mathlib
  collision.

## Uncertainties and notes for the auditor

- **New instance.** `instDecidableEqCertFixedSeg` is a new global instance on the landed type `CertFixed P`,
  through the mantissa. It is design-sanctioned (design §3.3).
- **Unexercised code.** Production use goes through generated data, which is not part of this package.
  - The tests exercise `compose_eq` on a toy only.
  - `segOk_one_of` is proved generically but not exercised on a product-memoized op; that is L3 and DATA work.
- **Errata:** none in pinned sources.
