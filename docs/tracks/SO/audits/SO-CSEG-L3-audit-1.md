# SO-CSEG-L3 independent package audit 1

Overall verdict: **PASS WITH NOTES for the delivered ProductSplit module and tests.** All 14 production declarations match the authoritative design block; all 11 production theorems and eight test theorems have allowed axiom closure. The targeted build, fresh signature/consumer probes, and kernel replay pass. No blocking defect was found in the delivered product API.

**The complete SO-CSEG-L3 row of design §8 is not complete:** `Kernel/SegOne.lean` and its segment-level obligations are deferred to SO-CSEG-A/B by the audit focus. This report does not certify the segment chain, production memory gates, generated lunar certificates, a frozen anchor, or the final theorem. There is no provider or frozen theorem being sealed in this package; per-anchor seal verdict is N/A.

## Snapshot and authority

- Worktree/report destination: `/root/code/KAM-inp-csegl3`; this explicit user destination overrides the brief's generic main-worktree destination.
- HEAD: `d951b443dc9a6b3539489141439a1e3e018d6a2d`; current `inp`: `9446cfbd24176cbf38007012ea5a0271e208c443`; merge base: `7b86cf178eaaffba3a7a4205a561b41ef3660455`.
- Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the named audit-focus handoff, design §3.5/§8 and its calibration/consumer context, authoritative signatures §D, and the three inherited design audits.
- Compared `git diff inp...HEAD`: ten added files, 2454 lines. Besides the two Lean modules and two handoffs, the diff contains the inherited design, three design audits, and two untrusted census/planning scripts. The immediate delta `git diff --name-status c2a38f5b..HEAD` is exactly the two Lean modules and two handoffs. No landed declaration is modified.
- No I/N/P blueprint node specifies these computational helpers. Their authoritative source is `.drafts/design/SOCsplitSignatures.lean:417–547`, interpreted against the landed checker bodies. Searches for `SO-CSEG-L3`, `mulPacked_eq_of_parts`, and `checkPackedSp_of_groups` in the three blueprints found no matches. No unrelated mathematical node is credited.
- The draft signature file contains unrelated admitted design proofs. It was read as a specification and **never imported or elaborated wholesale** by this audit. Only its eleven exact §D theorem headers were copied to the fresh probe.

| artifact | SHA256 |
|---|---|
| `.drafts/design/SOCsplitSignatures.lean` | `42e25f3f5904e40af5ba7b6d01bfd7c741b41578539aa9a23e98705593e199e9` |
| `docs/tracks/SO/design/SO-CSPLIT.md` | `3420db9d2e1701503110be809e700db11a78d622ac45094ebfe43e76155b6047` |
| `KAM/CertificateSharp/Kernel/ProductSplit.lean` | `ef6d4591b07aa5605283356e88c2d0d105899c6bf5107ad355e8ac5510db1762` |
| `KAM/CertificateSharp/Tests/ProductSplit.lean` | `0dc6a155cee88a4152aacc253e288e036baa83118b8ff04a9417110c8ac51fcb` |

## Fidelity and declaration ledger

Extracting from `theorem CertModel.mulN_eq_of_polyProduct` through the end of §D and comparing with the production block through `expResidualProduct_eq_of_polyProduct` gives **IDENTICAL** after removing only surrounding blank space. Internal bytes, including all binders, bodies, proofs, and the three definitions, are unchanged. Production declaration lines equal source lines minus 385. The wrapper/module documentation is new; there is no signature or definition-body deviation.

All names below are in `KAM.Certificate`. P = `Kernel/ProductSplit.lean`; T = `Tests/ProductSplit.lean`. Verdicts concern the indicated computation, not a mathematical anchor.

| node / declaration | location | verdict | reason |
|---|---|---|---|
| M3 `CertModel.mulN_eq_of_polyProduct` | P:32 | PASS | Exact degree, truncation, packed error, truncation error and cached-norm cross terms. |
| F2 `polyProduct_eq_of_mulPacked` | P:42 | PASS | Nonconstant guards and exact advice key; returns `toErrTerms`, not raw polynomial terms. |
| F2 `CertPoly.mulPacked_eq_of_parts` | P:52 | PASS | All four real products and decodes, doubled mantissa precision, exact signs and radius sum. |
| F3 `packedRealProduct_eq_nil_left` | P:72 | PASS | Empty left factor returns `some ([], 0)` without consulting advice. |
| F3 `packedRealProduct_eq_nil_right` | P:78 | PASS | Corresponding right factor branch, including both-empty inputs. |
| F3 `packedRealProduct_eq_of_sparse` | P:84 | PASS | Nonempty inputs, both slot guards and the actual sparse check retained. |
| F3 `checkPackedSpPrefix` | P:93 | PASS | Literal complete non-shard conjunction; no dropped shape/order/length guard. |
| F3 `PackedAdvice.shardRange` | P:101 | PASS | Exactly the landed `List.range (spCount A + spCount B - 1)`. |
| F3 `checkShardAt` | P:105 | PASS | Same blocks, starting offset zero and `spMax` bounds as the landed check. |
| F3 `checkPackedSp_of_groups` | P:110 | PASS | Every actual shard is covered by a group whose entire check succeeds. |
| M3 `charResolve_eq_of_radius` | P:124 | PASS | Own key, cache miss, indexed witness and `forWitness 1 (expWit.length + c)` preserved. |
| M3 `expWitnessRadius_eq_of_pin` | P:134 | PASS | Exact pin ball and witness reduction parameters. |
| M3 `expWitnessRadiusOf_eq_of_residuals` | P:141 | PASS | Both exponential bounds, every `Fin n` residual, balanced sum and complete radius preserved. |
| M3 `expResidualProduct_eq_of_polyProduct` | P:156 | PASS | Exact `[1,j]` key, differentiated source polynomial and negated witness. |
| toy `splitTest_agree` | T:92 | PASS | Whole/split Boolean equality on two products, corrupted advice and descending slots; corrupted advice explicitly false. |
| toy `splitTest_shardRangeM` | T:104 | PASS | Five actual shards are precisely `[0,1,2,3,4]`. |
| toy `splitTest_groupsM` | T:108 | PASS | Distinct group proofs for `[[0,1,2],[3,4]]`, full cover. |
| toy `splitTest_realM` | T:119 | PASS | Grouped success consumed by sparse real-product lemma. |
| toy `splitTest_realM_whole` | T:125 | PASS | Direct whole computation proves the same value. |
| toy `splitTest_nil` | T:131 | PASS | Both empty-factor equations with bogus advice. |
| toy `splitTest_decodeM` | T:142 | PASS | Decode success proved independently; no reliance on the default failure value. |
| toy `splitTest_mulPackedM` | T:153 | PASS | Separately checked RR, three empty parts and decode assembled by the actual theorem. |
| deferred `ComposeCkpt.segOk_one_of` | design:433–438; signature:402 | NOT DELIVERED | Requires SegDefs/SegOne; remains A/B follow-up. |
| deferred `seed_slot_of_mem` | design:439–440; signature:314 | NOT DELIVERED | Segment seed theorem absent here. |
| deferred `shadowStep_of_live` | design:441–442; signature:394 | NOT DELIVERED | Shadow wrapper absent here. |
| deferred `composeStep` arm equations | design:445–452; §8 row | NOT DELIVERED | Production segment assembly still needs its A/B integration. |

## Independent soundness and consumer assessment

The landed sources are `Poly/Sparse.lean:383–403`, `Poly/MulPacked.lean:238–250,438–452`, `Model/Ops.lean:83–96`, `Expr/Compose.lean:69–77,113–125,148–185`, and `Model/Exp.lean:69–113`.

**Complex assembly.** `ma.1 × mb.1` supplies RR, `ma.2 × mb.2` supplies II, and the II integer coefficients are negated *before* their real decode. RI uses `ma.1 × mb.2`, IR uses `ma.2 × mb.1`, and each is decoded into the imaginary component. The same `2 * P` appears in all four real products and decodes; each decode uses its own advice scale. The concatenation order and upward conversion of the four rational remainder bounds are exactly the landed function. No associativity of rounded arithmetic, numeric equality oracle, lawful-backend premise, or altered normalizer is assumed. These are equations of computations for arbitrary `CertArith α`.

**Coverage and prefix.** A new generic probe proves by `rfl`:

```lean
checkPackedSp adv ea eb =
  (checkPackedSpPrefix adv ea eb && adv.shardRange.all (checkShardAt adv ea eb))
```

Thus the split is definitionally exact, including malformed/empty-range inputs. In `checkPackedSp_of_groups`, each `s` in that very range gets a witness `g ∈ groups` with `s ∈ g`; `hgroups` supplies the successful check at `s`. Duplicates, overlapping groups and extra shard indices cannot bypass a real shard: extra indices merely add work. No disjointness or exact group partition is required. The prefix retains shape, both positive dense lengths, strict order, both slot bounds and advice-window length. The sparse real-product lemma retains all guards needed to take that branch. Empty inputs correctly take the earlier zero branch; no invalid advice is promoted to nonempty success.

**Consumer witness.** Existing `splitTest_groupsM → splitTest_realM → splitTest_decodeM/splitTest_mulPackedM` demonstrates actual toy shard/decode assembly. The fresh probe additionally composes `polyProduct_eq_of_mulPacked` with `CertModel.mulN_eq_of_polyProduct`, and applies the resulting equation under the `.mul` arm of the *landed* `composeStep`, at its actual key `[0, st.len]` and actual operand pairs `st.slot W i`, `st.slot W j`. Both generic consumer theorems elaborate and have allowed axioms. This closes the requested product-to-landed-`mulN` connection without reducing the heavy product in the consumer proof.

Nothing is missing in the delivered product interface for separately proving shards and decode and then assembling the landed multiplication. Computing `toMants`, prefix/slot guards, lookup, `toErrTerms`, truncation/error terms and cached norms remains the generated caller's work, exactly as specified. The character/exp helpers similarly preserve the exact cache lookup, witness offsets, pin, residual index range and final radius; they do not assert segment success.

**Limits retained.** `SegDefs.lean` and `SegOne.lean` are absent in this worktree. Import-closure traversal finds 61 project modules, no provider, no draft-signature/SegDefs/SegOne dependency, and eleven frozen definition modules, all SEALED in the live manifest. ProductSplit directly imports only `KAM.Certificate.Expr.Compose`; it can land independently of the deferred segment helpers. Completing one-op `segOk` proofs is still required before claiming the entire §8 L3 route complete. The real-only toy assembly does not exercise nonzero II/RI/IR numerically; the generic theorem and replay check their exact formulas. No lunar-scale G4/G5 or memory guarantee follows from these tiny tests. The handoff's inference-heartbeat warning is retained: generated consumers should supply `ma`, `mb`, `pRR`…`pIR`, `tRR`…`tIR` explicitly as needed. No override was used here.

## Definitions

Every new definition is literal computational data or a literal wrapper. No structure, instance, abbreviation, choice-selected object or mathematical characterization-defined object is added.

For **each** definition in the following table: `BODY_MATCH: OK`; `PUBLIC_CARRIER: OK`; `WELL_DEFINEDNESS: N/A_LITERAL`; `CHARACTERIZATION: N/A_LITERAL`; `CHOICE_INDEPENDENCE: N/A`; `DEFINITION_VERDICT: PASS`.

| definition | classification / whole-carrier check |
|---|---|
| `checkPackedSpPrefix` | Literal Boolean conjunction, valid on every advice and input list. |
| `PackedAdvice.shardRange` | Literal finite range, including its natural-subtraction endpoint behavior. |
| `checkShardAt` | Literal landed shard application on every natural index. |
| `splitTestLay2` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestTarget2` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestA2` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestB2` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestAdv2` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestAdv2Off` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestLayM` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestTargetM` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestAM` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestBM` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestAdvM` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestRe` | Literal map from every mantissa list to its real fixed-point polynomial. |
| `splitTestW` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitTestBogus` | Literal test fixture (layout, advice, input list, weight or mapped polynomial); no logical premise. |
| `splitCheckTest` | Literal prefix/shard Boolean conjunction, on the full advice/list carrier. |
| `splitTestEa2` | Literal slot-term extraction of its named toy input. |
| `splitTestEb2` | Literal slot-term extraction of its named toy input. |
| `splitTestEaM` | Literal slot-term extraction of its named toy input. |
| `splitTestEbM` | Literal slot-term extraction of its named toy input. |
| `splitTestTRR` | Literal test decode with `getD []`; `splitTest_decodeM` proves this closed decode is successful before assembly. The default is unreachable in the exported toy success equation; this is not a surrogate mathematical object. |

## Verification receipts

All audit-owned Lean/Lake invocations ran sequentially, with `LEAN_NUM_THREADS=1`, `nice -n 5`, default heartbeats/depth, and the existing worktree overlay. Lint's ABI subprocess ran before the final probe. No library-wide rebuild, dependency update, cache fetch, frozen/generated-file edit, or state-changing git operation was performed.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-csegl3 KAM.CertificateSharp.Kernel.ProductSplit KAM.CertificateSharp.Tests.ProductSplit
   exit 0
   Build completed successfully (2965 jobs).
   ```

   The only replayed warning is the inherited unused `hS` at `KAM/Certificate/Expr/Basic.lean:93:5`; neither new module warns.

2. Required single kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.CertificateSharp.Kernel.ProductSplit KAM.CertificateSharp.Tests.ProductSplit
   exit 0
   replaying KAM.CertificateSharp.Tests.ProductSplit
   replaying KAM.CertificateSharp.Kernel.ProductSplit
   ```

3. Fresh untracked exact-signature and semantic probes:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOCsegL3Audit.lean
   exit 0
   ```

   First run: all eleven independently copied authoritative theorem headers accepted as `example`s proved by applying the corresponding production theorem to its explicit binders; all 19 public theorem axiom lists printed; generic prefix identity and packed-to-`mulN` composition passed. Final run adds the actual `composeStep` consumer proof: exit 0, no warnings/errors. The scratch file was removed after validation. Exact axiom output follows.

```text
'KAM.Certificate.CertModel.mulN_eq_of_polyProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.polyProduct_eq_of_mulPacked' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.mulPacked_eq_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedRealProduct_eq_nil_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedRealProduct_eq_nil_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedRealProduct_eq_of_sparse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPackedSp_of_groups' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charResolve_eq_of_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expWitnessRadius_eq_of_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expWitnessRadiusOf_eq_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expResidualProduct_eq_of_polyProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.splitTest_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.splitTest_shardRangeM' depends on axioms: [propext]
'KAM.Certificate.splitTest_groupsM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.splitTest_realM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.splitTest_realM_whole' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.splitTest_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.splitTest_decodeM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.splitTest_mulPackedM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.audit_prefix_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.audit_mulN_consume' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.audit_composeStep_consume' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   exit 1
   KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/CertificateSharp.lean)
   check_lean_modules: PASS (1688 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (158 frozen declarations)
   ```

   This is precisely the stale-generated-root exception permitted by the audit brief. All forbidden-token/escape, module, size, errata-rendering, frozen-anchor and ABI checks otherwise pass. The live count is 1688, rather than the handoff's 1686; this is a receipt-count correction, not a source defect. The root was deliberately left untouched.

5. Integrity and supplemental checks:

   ```text
   git diff --check inp...HEAD
   exit 0; no output
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md
   exit 0; no output
   ```

   The two Lean files have 163/167 total lines and maximum Unicode line widths 98/100. Module headers, `public import`, docstrings, exposed public section and namespace boundaries are present. The full lint checks forbidden admissions, escapes, resource overrides and provider quarantine. Import traversal finds no forbidden import. Both inherited Python scripts parse with `ast.parse`; their census, numerical estimates and planner calibration are not re-certified by this product-package audit.

## Binder ledger

All production statements have zero EXCESS inputs. Shared section binders are shown only for the seven theorems that actually depend on `α`; the subsequent rows enumerate each explicit and implicit theorem parameter against the authoritative source header. SOURCE includes explicitly specified computational data and memoized subcomputation equalities. These equalities are the purpose of distinctly named `_eq_of_…` assembly helpers; none claims an unconditional final certificate bound or hides an analytic proof step. There are no bundled Prop assumptions, standing-law hypotheses, or owner-ruling premises. `CertArith α` is operational backend typing, not `LawfulCertArith` or an assumed soundness theorem.

| declaration | binder | mode | bin | source |
|---|---|---|---|---|
| `CertModel.mulN_eq_of_polyProduct` | `α : Type` | shared implicit/instance | TYPING | §D context; source:417 |
| `CertModel.mulN_eq_of_polyProduct` | `[CertArith α]` | shared implicit/instance | TYPING | §D context; source:417 |
| `CertModel.mulN_eq_of_polyProduct` | `W` | explicit | SOURCE | signatures:417, exact header |
| `CertModel.mulN_eq_of_polyProduct` | `cfg` | explicit | SOURCE | signatures:417, exact header |
| `CertModel.mulN_eq_of_polyProduct` | `key` | explicit | SOURCE | signatures:417, exact header |
| `CertModel.mulN_eq_of_polyProduct` | `a` | explicit | SOURCE | signatures:417, exact header |
| `CertModel.mulN_eq_of_polyProduct` | `na` | explicit | SOURCE | signatures:417, exact header |
| `CertModel.mulN_eq_of_polyProduct` | `b` | explicit | SOURCE | signatures:417, exact header |
| `CertModel.mulN_eq_of_polyProduct` | `nb` | explicit | SOURCE | signatures:417, exact header |
| `CertModel.mulN_eq_of_polyProduct` | `out` | implicit | SOURCE | signatures:417, exact header |
| `CertModel.mulN_eq_of_polyProduct` | `h` | explicit | SOURCE | signatures:417, exact header |
| `polyProduct_eq_of_mulPacked` | `α : Type` | shared implicit/instance | TYPING | §D context; source:427 |
| `polyProduct_eq_of_mulPacked` | `[CertArith α]` | shared implicit/instance | TYPING | §D context; source:427 |
| `polyProduct_eq_of_mulPacked` | `W` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `cfg` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `key` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `a` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `b` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `P` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `rr` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `ii` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `ri` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `ir` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `out` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `ha` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `hb` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `hk` | explicit | SOURCE | signatures:427, exact header |
| `polyProduct_eq_of_mulPacked` | `hp` | explicit | SOURCE | signatures:427, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `α : Type` | shared implicit/instance | TYPING | §D context; source:437 |
| `CertPoly.mulPacked_eq_of_parts` | `[CertArith α]` | shared implicit/instance | TYPING | §D context; source:437 |
| `CertPoly.mulPacked_eq_of_parts` | `dec` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `W` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `P` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `rr` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `ii` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `ri` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `ir` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `a` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `b` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `ma` | implicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `mb` | implicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `pRR` | implicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `pII` | implicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `pRI` | implicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `pIR` | implicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `tRR` | implicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `tII` | implicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `tRI` | implicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `tIR` | implicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `hma` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `hmb` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `hRR` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `hII` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `hRI` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `hIR` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `htRR` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `htII` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `htRI` | explicit | SOURCE | signatures:437, exact header |
| `CertPoly.mulPacked_eq_of_parts` | `htIR` | explicit | SOURCE | signatures:437, exact header |
| `packedRealProduct_eq_nil_left` | `adv` | explicit | SOURCE | signatures:457, exact header |
| `packedRealProduct_eq_nil_left` | `W` | explicit | SOURCE | signatures:457, exact header |
| `packedRealProduct_eq_nil_left` | `P2` | explicit | SOURCE | signatures:457, exact header |
| `packedRealProduct_eq_nil_left` | `x` | implicit | SOURCE | signatures:457, exact header |
| `packedRealProduct_eq_nil_left` | `y` | explicit | SOURCE | signatures:457, exact header |
| `packedRealProduct_eq_nil_left` | `hx` | explicit | SOURCE | signatures:457, exact header |
| `packedRealProduct_eq_nil_right` | `adv` | explicit | SOURCE | signatures:463, exact header |
| `packedRealProduct_eq_nil_right` | `W` | explicit | SOURCE | signatures:463, exact header |
| `packedRealProduct_eq_nil_right` | `P2` | explicit | SOURCE | signatures:463, exact header |
| `packedRealProduct_eq_nil_right` | `x` | explicit | SOURCE | signatures:463, exact header |
| `packedRealProduct_eq_nil_right` | `y` | implicit | SOURCE | signatures:463, exact header |
| `packedRealProduct_eq_nil_right` | `hy` | explicit | SOURCE | signatures:463, exact header |
| `packedRealProduct_eq_of_sparse` | `adv` | explicit | SOURCE | signatures:469, exact header |
| `packedRealProduct_eq_of_sparse` | `W` | explicit | SOURCE | signatures:469, exact header |
| `packedRealProduct_eq_of_sparse` | `P2` | explicit | SOURCE | signatures:469, exact header |
| `packedRealProduct_eq_of_sparse` | `x` | explicit | SOURCE | signatures:469, exact header |
| `packedRealProduct_eq_of_sparse` | `y` | explicit | SOURCE | signatures:469, exact header |
| `packedRealProduct_eq_of_sparse` | `hx` | explicit | SOURCE | signatures:469, exact header |
| `packedRealProduct_eq_of_sparse` | `hy` | explicit | SOURCE | signatures:469, exact header |
| `packedRealProduct_eq_of_sparse` | `ha` | explicit | SOURCE | signatures:469, exact header |
| `packedRealProduct_eq_of_sparse` | `hb` | explicit | SOURCE | signatures:469, exact header |
| `packedRealProduct_eq_of_sparse` | `hs` | explicit | SOURCE | signatures:469, exact header |
| `checkPackedSp_of_groups` | `adv` | explicit | SOURCE | signatures:495, exact header |
| `checkPackedSp_of_groups` | `ea` | explicit | SOURCE | signatures:495, exact header |
| `checkPackedSp_of_groups` | `eb` | explicit | SOURCE | signatures:495, exact header |
| `checkPackedSp_of_groups` | `groups` | explicit | SOURCE | signatures:495, exact header |
| `checkPackedSp_of_groups` | `hpre` | explicit | SOURCE | signatures:495, exact header |
| `checkPackedSp_of_groups` | `hcover` | explicit | SOURCE | signatures:495, exact header |
| `checkPackedSp_of_groups` | `hgroups` | explicit | SOURCE | signatures:495, exact header |
| `charResolve_eq_of_radius` | `α : Type` | shared implicit/instance | TYPING | §D context; source:509 |
| `charResolve_eq_of_radius` | `[CertArith α]` | shared implicit/instance | TYPING | §D context; source:509 |
| `charResolve_eq_of_radius` | `n` | explicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `K` | explicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `wit` | explicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `W` | explicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `cfg` | explicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `pe` | explicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `cache` | explicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `k'` | explicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `c` | implicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `E` | implicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `r` | implicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `hc` | explicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `hw` | explicit | SOURCE | signatures:509, exact header |
| `charResolve_eq_of_radius` | `hr` | explicit | SOURCE | signatures:509, exact header |
| `expWitnessRadius_eq_of_pin` | `α : Type` | shared implicit/instance | TYPING | §D context; source:519 |
| `expWitnessRadius_eq_of_pin` | `[CertArith α]` | shared implicit/instance | TYPING | §D context; source:519 |
| `expWitnessRadius_eq_of_pin` | `n` | explicit | SOURCE | signatures:519, exact header |
| `expWitnessRadius_eq_of_pin` | `W` | explicit | SOURCE | signatures:519, exact header |
| `expWitnessRadius_eq_of_pin` | `cfg` | explicit | SOURCE | signatures:519, exact header |
| `expWitnessRadius_eq_of_pin` | `g` | explicit | SOURCE | signatures:519, exact header |
| `expWitnessRadius_eq_of_pin` | `E` | explicit | SOURCE | signatures:519, exact header |
| `expWitnessRadius_eq_of_pin` | `out` | implicit | SOURCE | signatures:519, exact header |
| `expWitnessRadius_eq_of_pin` | `h` | explicit | SOURCE | signatures:519, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `α : Type` | shared implicit/instance | TYPING | §D context; source:526 |
| `expWitnessRadiusOf_eq_of_residuals` | `[CertArith α]` | shared implicit/instance | TYPING | §D context; source:526 |
| `expWitnessRadiusOf_eq_of_residuals` | `n` | explicit | SOURCE | signatures:526, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `W` | explicit | SOURCE | signatures:526, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `cfg` | explicit | SOURCE | signatures:526, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `g` | explicit | SOURCE | signatures:526, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `E` | explicit | SOURCE | signatures:526, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `out` | explicit | SOURCE | signatures:526, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `mB` | implicit | SOURCE | signatures:526, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `mη` | implicit | SOURCE | signatures:526, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `rs` | implicit | SOURCE | signatures:526, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `hB` | explicit | SOURCE | signatures:526, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `hη` | explicit | SOURCE | signatures:526, exact header |
| `expWitnessRadiusOf_eq_of_residuals` | `hres` | explicit | SOURCE | signatures:526, exact header |
| `expResidualProduct_eq_of_polyProduct` | `α : Type` | shared implicit/instance | TYPING | §D context; source:541 |
| `expResidualProduct_eq_of_polyProduct` | `[CertArith α]` | shared implicit/instance | TYPING | §D context; source:541 |
| `expResidualProduct_eq_of_polyProduct` | `W` | explicit | SOURCE | signatures:541, exact header |
| `expResidualProduct_eq_of_polyProduct` | `cfg` | explicit | SOURCE | signatures:541, exact header |
| `expResidualProduct_eq_of_polyProduct` | `g₀` | explicit | SOURCE | signatures:541, exact header |
| `expResidualProduct_eq_of_polyProduct` | `E` | explicit | SOURCE | signatures:541, exact header |
| `expResidualProduct_eq_of_polyProduct` | `j` | explicit | SOURCE | signatures:541, exact header |
| `expResidualProduct_eq_of_polyProduct` | `out` | implicit | SOURCE | signatures:541, exact header |
| `expResidualProduct_eq_of_polyProduct` | `h` | explicit | SOURCE | signatures:541, exact header |

Elaborated outer-binder totals across eleven theorem headers: SOURCE=122, TYPING=14, STANDING=0, RULED=0, EXCESS=0. The nested residual index `j : Fin n` in `hres` is exactly source:530 (SOURCE); the local shard/group quantifiers in `hcover`/`hgroups` are exactly source:497–498 (SOURCE). All eight test theorems are closed statements with no theorem parameters or logical premises. No provider/frozen-type seal probe applies because no such anchor is delivered.

## Findings, errata, and closeout

- **N1 — Deferred segment scope:** retain the reassignment to SO-CSEG-A/B. ProductSplit itself passes; the original §8 L3 row remains partial until `SegOne` and the actual segment assembly are delivered and audited.
- **N2 — Cost applicability:** shard/decode independence is proved, but production G4/G5 and the downstream segment/recipe gates remain unrun here. No generated-tree, cgroup-memory or final-data receipt is substituted with a toy test or a compiling signature.
- **N3 — Hygiene receipt corrections:** lint exits 1 solely for the permitted generated-root staleness, and currently counts 1688 modules. No root regeneration is authorized in this report-only audit.

Suspected pinned external-source errata: none found. Suspected computational-source/signature defects: none found in §D. Statement/body deviations: none. Implementation deviations introduced by this auditor: none. The inherited historical FAIL design audits are superseded by audit 3 for interface readiness; their unrelated admitted M1 draft proofs are neither imported nor certified here.

Only this report is written to the source tree. Temporary Lean probes are deleted; protected paths and the production/draft input hashes are unchanged. This closes the requested independent audit of the delivered product module, with the explicit segment and calibration limitations above.
