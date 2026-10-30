# SO-CSEG-AB independent package audit 1

**Overall: PASS WITH NOTES for SO-CSEG-A, SO-CSEG-B and the delegated `SegOne` portion of L3.** No blocking implementation, signature, definition-body or axiom defect found. The generic computation-only chain and checker bridges are proved. **Frozen-anchor sealing: N/A**: this package has no provider export and seals no I/N/P or SO frozen theorem. This verdict does not certify production lunar/lock data, the full certificate or calibration gates.

## Scope, authority and snapshot

Focused tier-2, refute-first review under `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, AGENTS.md, PLAN.md and DECISIONS.md. The entire `SO-CSEG-AB-handoff.md` supplies the focus (there is no separate heading literally named AUDIT FOCUS). The user's explicit destination overrides the generic brief's main-worktree destination. Only this report and temporary files under this worktree's `.lake/abi-scratch/` are written; no implementation, generated root, manifest, frozen file or git state is changed.

- HEAD: `fd6c8d12d2fa971f3521e358fd3748d9e357448d`.
- Live comparison ref `inp`: `e6a8449294520ccbdf817e7f1a1c7321612aa5d7`.
- Merge base: `c2a38f5b6124e4d987397a0ae4cad9990c240807`.
- Reviewed `git diff inp...HEAD`: six new Lean modules and the handoff, 1,610 added lines. Source inspected in full, including all eight `composeStep_congr` arms, both shadow induction branches and the tiling induction.
- Computational specification: `docs/tracks/SO/design/SO-CSPLIT.md` revision 2, §§3.2–3.3, §3.5 and §8, plus its authoritative audited signatures below. As design audit 3 explicitly records, mathematical I/N/P blueprint labels and frozen provider/seal-type probes are N/A for these computational interfaces. There is no `docs/tracks/SO/statement.md`; the design and landed checker equations are the applicable local authority.

Snapshot SHA256 values:

| artifact | SHA256 |
|---|---|
| `KAM/CertificateSharp/Kernel/SegAgree.lean` | `96c99c76b44156aa9c862d6237534219986309d2f162d50717f0fb9e13173008` |
| `KAM/CertificateSharp/Kernel/SegBridges.lean` | `ace386c6da5a818dc85ff351174aa82919b0b9bf83c3a1da89640e8063ddde8b` |
| `KAM/CertificateSharp/Kernel/SegChain.lean` | `9d145e22a2f35d87448538cf2bbd6adc2f9bd3c17a69ef6682a62927370f1266` |
| `KAM/CertificateSharp/Kernel/SegDefs.lean` | `980556d1a8fb2e6d085d45a3630f4d3b542cb0af1f6fd7f0afb73d311af52075` |
| `KAM/CertificateSharp/Kernel/SegOne.lean` | `ef2e70060cca5a9fc543deb4bf20b6ca1b60d0ceeba5e04796ba2eeae0b3e9c8` |
| `KAM/CertificateSharp/Tests/Seg.lean` | `35a006c96a741073b6943111f9166106958c5e475118650512a093f22e2bfc46` |
| `docs/tracks/SO/audits/SO-CSEG-AB-handoff.md` | `186b08a0bfd1dafcbab26bf5867cf85ff7e8c293f483bdf47c419d3858899956` |
| `docs/tracks/SO/design/SO-CSPLIT.md` | `3420db9d2e1701503110be809e700db11a78d622ac45094ebfe43e76155b6047` |
| `.drafts/design/SOCsplitSignatures.rev2-audited.lean` | `42e25f3f5904e40af5ba7b6d01bfd7c741b41578539aa9a23e98705593e199e9` |

The audited signature hash is exactly `42e25f3f5904e40af5ba7b6d01bfd7c741b41578539aa9a23e98705593e199e9`, matching design audit 3. Normalization applied only the documented `pair → slotPair` and `beq/eq_of_beq → segBeq/eq_of_segBeq` renames. Of 59 shared declarations, 58 textual headers match under that normalization. The remaining negative-contract theorem moves `{α : Type} [CertArith α]` from its ambient section into its explicit header; its elaborated contract is unchanged. Every shared literal definition, structure and instance body matches after comment/whitespace removal and those renames: **33/33**. The equation-style `eq_of_termsBeq` header is parsed up to its first equation arm rather than into its proof.

## Refutation and proof review

**Whole-pair agreement.** `AgreeOn` retains length, both counters, the ordered character cache and complete `(model, cached norm)` pairs. `composeStep_congr` preserves these through every arm, including slot-number product advice, witness indices and the sqrt lookup keyed by `len`. Successful steps push one entry; no `rev.length = len` premise is secretly needed for persistence below the old length. The `char` arm observes the same cache; the remaining arms observe the same operands and relevant metadata.

**Dead operations and hR.** Only const/action/add/mul may be replaced by placeholders. Char/exp/inv/sqrt always run, even outside the explicit live list. In the dead branch, retaining an original future slot would invalidate agreement; `hR : ∀ i, R i → i < σ.len` prevents exactly this. `imports_lt_seed_len` derives hR from `planOk`'s strict import bound and `segPrefixOk`'s input length, and `seg_step` actually supplies that proof. The retained `shadowRun_agree_needs_hR` counterexample is kernel-replayed. An independent scratch probe also rejects hR for `R = True` at length zero and forces an omitted-live exp with an absent witness to return `none` in both `shadowStep` and `shadowRun`.

**Tiling and projection.** `seg_step` recovers the landed prefix run, output metadata and export pairs from the checked shadow run, with genuine landed slot persistence. `chain_go` derives that imports were exported earlier: a later exporting segment would start at or after the current boundary, contradicting the strict import bound. The final theorem starts with the actual empty landed state, reaches the entire program and projects any wanted list through checked ledger entries. Metadata checks include both counters and cache order; export checks include the degree, polynomial, radius and cached norm. Duplicate or missing ledger tricks do not bypass the checks; the final `find?` proof uses the same first-match semantics as `slotPair`.

**Consumers.** Both templates apply the proved `ComposeCkpt.compose_eq` to the actual certificate embedding, witnesses, weight, cfgFull and pi enclosure, then rewrite the literal-jet equality into the landed `checkEnergy`/`checkInvariance` definitions. They share hplan/hseg while varying wantedOk and the final energy/row residual. No outgoing theorem is assumed to prove itself. `segOk_one_of` assumes the prefix, one-step equation and result check, never its own full segOk conclusion; it is a legitimate decomposition helper. The toy's `segTest_compose` consumes compose_eq instead of deciding monolithic composition.

Premise classification: generic carriers, arithmetic/decidable-equality instances, dimensions and computational inputs are TYPING; the plan, segment, projection, agreement, reads, run equations and residuals are the explicit computational SOURCE contract in the audited signatures. Internal slot/tiling helpers state local conditional facts and are consumed with their premises proved by their callers. No excess premise was inserted into a signed public interface. No constants, analytic norms, Hamiltonian hypotheses or quantifier dependence were changed.

## Notes and adversarial dispositions

**N1 — Production scope remains open (informational).** The handoff itself says “The tests exercise `compose_eq` on a toy only” (lines 190–191). Generated production data and the product-memoized one-op consumer, L2/L3 remainder and CAL-1/CAL-2 are outside this diff. Refutation attempt: checked whether the generic templates or toy could themselves establish these production facts; they still require actual hjet, segment checks and residuals. Thus this is a retained scope boundary, not a code blocker. No production memory/time/volume guarantee follows here.

**N2 — Handoff premise wording is too broad (documentation only; confirmed).** Handoff line 77 says: “All are proved, with no premise beyond typing data.” For example, `ComposeCkpt.seg_step` (SegChain lines 112–122) explicitly assumes a checked plan, a landed prefix run, import agreement and a segment check; `composeStep_char_eq` assumes its memoized `charSlot` equation. Refutation attempt: these are intentionally conditional internal computational lemmas, and the chain supplies their premises; they are not conclusion-shaped replacements for an external source theorem. The code is sound, but the quoted sentence should say that these helpers add no premise to the audited public interfaces.

**Source/blueprint errata:** none found in this package's computational specification. No external mathematical source theorem is newly formalized here. Documented name changes, helper additions, movement of the negative test and delegation of SegOne are recorded deviations, with no signature weakening. No repair performed.

## Definition classification

All new objects are literal data or predicates, not objects selected by an unproved existence assertion. The 33 shared data/definition/instance bodies match the audited design. `AgreeOn` is a literal internal relation, not a theorem-shaped assumption bundle used in place of a source result.

- Comparators compare all intended fields and preserve list order; their reflection theorems establish actual equality. The new global `DecidableEq (CertFixed P)` uses mantissa equality and the landed `CertFixed.eq_of_m` theorem, exactly as the design permits.
- `ComposeMeta`, `SegSpec`, `ComposeCkpt` are explicitly untrusted input data. No structure field packages a missing theorem.
- `slotPair` has a deliberate zero off-ledger default matching landed `ComposeState.slot`. Missing wanted entries fail `wantedOk`, missing exports fail `segResultOk`, and imports are connected to earlier successful exports by the chain. The fallback does not invent a successful certified output.
- `seed` fills non-imported slots with zero and `shadowStep` fills dead infallible slots with zero by specification. Read checks plus agreement make those placeholders irrelevant to demanded outputs; fallible failures remain visible.
- `SegSpec.ops` uses the ordinary total drop/take semantics; checks enforce start/stop and program bounds wherever its faithful segment interpretation is required.
- Test definitions are deterministic finite rational fixtures and corruption functions. `segTestState.getD` is a test-only fallback, never a premise of generic soundness; all test Bool claims and the final chain application are kernel checked.

For every literal definition: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS and CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS.

## Declaration ledger

All names below are relative to `KAM.Certificate`; line numbers refer to the hashed HEAD files above. One row is provided for each new declaration (70 theorems, 49 definitions, 3 structures, 1 instance). Node identifiers are design roles, not fabricated mathematical blueprint nodes. Axiom codes: **S** = `[propext, Classical.choice, Quot.sound]`; **Q** = `[propext, Quot.sound]`; **P** = `[propext]`; **0** = no axioms; dash = not a theorem.

| design node / file:line | declaration | verdict | reason / axioms |
|---|---|---|---|
| A / agreement; `SegAgree.lean:32` | `ComposeState.AgreeOn` | PASS | def; — |
| A / agreement; `SegAgree.lean:38` | `ComposeState.slot_of_cons` | PASS | proved local computational fact / test; S |
| A / agreement; `SegAgree.lean:44` | `ComposeState.slot_of_cons_self` | PASS | proved local computational fact / test; S |
| A / agreement; `SegAgree.lean:50` | `pushSlot_slot_lt` | PASS | exact signed contract; S |
| A / agreement; `SegAgree.lean:54` | `ComposeState.AgreeOn.retain` | PASS | proved local computational fact / test; S |
| A / agreement; `SegAgree.lean:60` | `ComposeState.AgreeOn.of_push` | PASS | proved local computational fact / test; S |
| A / agreement; `SegAgree.lean:77` | `composeStep_infallible` | PASS | exact signed contract; S |
| A / agreement; `SegAgree.lean:84` | `composeStep_push` | PASS | proved local computational fact / test; S |
| A / agreement; `SegAgree.lean:125` | `composeStep_congr` | PASS | exact signed contract; S |
| A / agreement; `SegAgree.lean:191` | `seed_len` | PASS | proved local computational fact / test; S |
| A / agreement; `SegAgree.lean:194` | `seed_stateMeta` | PASS | exact signed contract; S |
| A / agreement; `SegAgree.lean:197` | `seed_slot_of_mem` | PASS | exact signed contract; S |
| A / agreement; `SegAgree.lean:207` | `seed_agree` | PASS | proved local computational fact / test; S |
| A / agreement; `SegAgree.lean:219` | `live_cons_zero` | PASS | proved local computational fact / test; Q |
| A / agreement; `SegAgree.lean:224` | `live_cons_succ` | PASS | proved local computational fact / test; Q |
| A / agreement; `SegAgree.lean:229` | `shadowStep_len` | PASS | proved local computational fact / test; S |
| A / agreement; `SegAgree.lean:237` | `shadowRun_len` | PASS | proved local computational fact / test; S |
| A / agreement; `SegAgree.lean:254` | `shadowRun_agree` | PASS | exact signed contract; S |
| A / agreement; `SegAgree.lean:368` | `composeOpsAux_slot_persist_le` | PASS | proved local computational fact / test; S |
| A / agreement; `SegAgree.lean:387` | `composeOpsAux_slot_persist` | PASS | exact signed contract; S |
| B / checker bridge; `SegBridges.lean:31` | `all_range_of_lt` | PASS | exact signed contract; Q |
| B / checker bridge; `SegBridges.lean:36` | `checkInvariance_eq_of_compose` | PASS | exact signed contract; S |
| B / checker bridge; `SegBridges.lean:44` | `checkEnergy_eq_of_compose` | PASS | exact signed contract; S |
| B / checker bridge; `SegBridges.lean:52` | `checkEnergy_of_ckpt` | PASS | exact signed contract; S |
| B / checker bridge; `SegBridges.lean:67` | `checkInvariance_of_ckpt` | PASS | exact signed contract; S |
| B / chain; `SegChain.lean:36` | `composeOpsAux_none` | PASS | proved local computational fact / test; S |
| B / chain; `SegChain.lean:41` | `composeOpsAux_append` | PASS | proved local computational fact / test; S |
| B / chain; `SegChain.lean:52` | `segsTile_cons` | PASS | proved local computational fact / test; Q |
| B / chain; `SegChain.lean:58` | `segsTile_start_ge` | PASS | proved local computational fact / test; Q |
| B / chain; `SegChain.lean:69` | `SegSpec.ops_getD` | PASS | proved local computational fact / test; P |
| B / chain; `SegChain.lean:75` | `SegSpec.ops_length` | PASS | proved local computational fact / test; Q |
| B / chain; `SegChain.lean:81` | `segBoolImp` | PASS | proved local computational fact / test; 0 |
| B / chain; `SegChain.lean:88` | `ComposeCkpt.imports_lt_seed_len` | PASS | exact signed contract; S |
| B / chain; `SegChain.lean:112` | `ComposeCkpt.seg_step` | PASS | proved local computational fact / test; S |
| B / chain; `SegChain.lean:203` | `ComposeCkpt.chain_go` | PASS | proved local computational fact / test; S |
| B / chain; `SegChain.lean:256` | `ComposeCkpt.compose_eq` | PASS | exact signed contract; S |
| A / M0–M1; `SegDefs.lean:44` | `keyBeq` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:49` | `eq_of_keyBeq` | PASS | exact signed contract; P |
| A / M0–M1; `SegDefs.lean:58` | `SlpOp.segBeq` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:69` | `SlpOp.eq_of_segBeq` | PASS | exact signed contract; Q |
| A / M0–M1; `SegDefs.lean:75` | `opsBeq` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:80` | `eq_of_opsBeq` | PASS | exact signed contract; Q |
| A / M0–M1; `SegDefs.lean:89` | `HamJet.segBeq` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:93` | `HamJet.eq_of_segBeq` | PASS | exact signed contract; Q |
| A / M0–M1; `SegDefs.lean:101` | `instDecidableEqCertFixedSeg` | PASS | instance; — |
| A / M0–M1; `SegDefs.lean:110` | `ccBeq` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:113` | `termsBeq` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:119` | `CertPoly.segBeq` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:122` | `CertModel.segBeq` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:126` | `pairBeq` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:129` | `cacheBeq` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:135` | `eq_of_ccBeq` | PASS | proved local computational fact / test; P |
| A / M0–M1; `SegDefs.lean:141` | `eq_of_termsBeq` | PASS | exact signed contract; P |
| A / M0–M1; `SegDefs.lean:150` | `CertPoly.eq_of_segBeq` | PASS | exact signed contract; P |
| A / M0–M1; `SegDefs.lean:155` | `CertModel.eq_of_segBeq` | PASS | exact signed contract; P |
| A / M0–M1; `SegDefs.lean:162` | `eq_of_pairBeq` | PASS | exact signed contract; P |
| A / M0–M1; `SegDefs.lean:166` | `eq_of_cacheBeq_aux` | PASS | proved local computational fact / test; P |
| A / M0–M1; `SegDefs.lean:177` | `eq_of_cacheBeq` | PASS | exact signed contract; P |
| A / M0–M1; `SegDefs.lean:186` | `ComposeMeta` | PASS | structure; — |
| A / M0–M1; `SegDefs.lean:194` | `SegSpec` | PASS | structure; — |
| A / M0–M1; `SegDefs.lean:203` | `ComposeCkpt` | PASS | structure; — |
| A / M0–M1; `SegDefs.lean:209` | `SlpOp.fallible` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:218` | `ComposeState.stateMeta` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:222` | `ComposeCkpt.pairOpt` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:227` | `ComposeCkpt.slotPair` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:231` | `SegSpec.liveEff` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:235` | `SegSpec.ops` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:240` | `ComposeState.seed` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:248` | `shadowStep` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:255` | `shadowRun` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:263` | `ComposeMeta.segBeq` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:267` | `ComposeMeta.eq_of_segBeq` | PASS | proved local computational fact / test; Q |
| A / M0–M1; `SegDefs.lean:278` | `ComposeCkpt.segPrefixOk` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:289` | `ComposeCkpt.segResultOk` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:301` | `ComposeCkpt.segOk` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:313` | `segsTile` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:318` | `ledgerAsc` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:323` | `ComposeCkpt.exported` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:329` | `ComposeCkpt.planOk` | PASS | def; — |
| A / M0–M1; `SegDefs.lean:339` | `ComposeCkpt.wantedOk` | PASS | def; — |
| delegated L3 / one-op; `SegOne.lean:28` | `shadowStep_of_live` | PASS | exact signed contract; S |
| delegated L3 / one-op; `SegOne.lean:36` | `ComposeCkpt.segOk_one_of` | PASS | exact signed contract; S |
| delegated L3 / one-op; `SegOne.lean:50` | `composeStep_const_eq` | PASS | proved local computational fact / test; S |
| delegated L3 / one-op; `SegOne.lean:56` | `composeStep_add_eq` | PASS | proved local computational fact / test; S |
| delegated L3 / one-op; `SegOne.lean:63` | `composeStep_mul_eq` | PASS | proved local computational fact / test; S |
| delegated L3 / one-op; `SegOne.lean:71` | `composeStep_char_eq` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:40` | `segToyW` | PASS | def; — |
| B / regression; `Seg.lean:42` | `segToyPi` | PASS | def; — |
| B / regression; `Seg.lean:45` | `segToyRound` | PASS | def; — |
| B / regression; `Seg.lean:48` | `segToyJ` | PASS | def; — |
| B / regression; `Seg.lean:53` | `segToyIPow` | PASS | def; — |
| B / regression; `Seg.lean:61` | `segToyRange` | PASS | def; — |
| B / regression; `Seg.lean:64` | `segToyCharE` | PASS | def; — |
| B / regression; `Seg.lean:69` | `segToyCos` | PASS | def; — |
| B / regression; `Seg.lean:72` | `segToyK` | PASS | def; — |
| B / regression; `Seg.lean:75` | `segToyProg` | PASS | def; — |
| B / regression; `Seg.lean:80` | `segToyInv` | PASS | def; — |
| B / regression; `Seg.lean:84` | `segToyWit` | PASS | def; — |
| B / regression; `Seg.lean:88` | `segToyCfg` | PASS | def; — |
| B / regression; `Seg.lean:94` | `segTestState` | PASS | def; — |
| B / regression; `Seg.lean:98` | `segTestSegs` | PASS | def; — |
| B / regression; `Seg.lean:101` | `segTestLedger` | PASS | def; — |
| B / regression; `Seg.lean:104` | `segTestCkpt` | PASS | def; — |
| B / regression; `Seg.lean:109` | `segTestOk` | PASS | def; — |
| B / regression; `Seg.lean:113` | `segTest_plan` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:115` | `segTest_seg0` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:117` | `segTest_seg1` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:119` | `segTest_wanted` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:122` | `segTest_compose` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:136` | `segTestCorrupt` | PASS | def; — |
| B / regression; `Seg.lean:140` | `segTest_badRadius` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:145` | `segTest_badNorm` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:149` | `segTest_missingImport` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:156` | `segTest_deadRead` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:163` | `segTest_badCounter` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:170` | `segTest_badCacheOrder` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:178` | `segTest_badInitMeta` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:185` | `segTest_badTiling` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:195` | `shadowRun_agree_needs_hR` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:211` | `segTestJet` | PASS | def; — |
| B / regression; `Seg.lean:213` | `segTest_jetBeq` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:215` | `segTest_jetBeq_ne` | PASS | proved local computational fact / test; S |
| B / regression; `Seg.lean:219` | `segTest_jet_eq` | PASS | proved local computational fact / test; S |

## Independent verification

Every audit Lean/Lake invocation ran serially with `LEAN_NUM_THREADS=1`, `nice -n 5` and default budgets. The gate wrapper itself runs `nice -n 5 lake build`; no clean, update, cache fetch or dependency rebuild was requested. Targeted build was up to date. No heartbeat, recursion-depth or synthesis override was introduced.

**Targeted build — exit 0:**

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-socsplit2 KAM.CertificateSharp.Kernel.SegDefs KAM.CertificateSharp.Kernel.SegAgree KAM.CertificateSharp.Kernel.SegChain KAM.CertificateSharp.Kernel.SegOne KAM.CertificateSharp.Kernel.SegBridges KAM.CertificateSharp.Tests.Seg
```

Output: `[inp-gate] slot 2 acquired 21:03:15`; `Build completed successfully (3265 jobs).` Two inherited warnings were replayed, in `KAM.Certificate.Arith.PiHigh:218` (unused simp argument) and `KAM.Certificate.Expr.Basic:93` (unused variable); none in the package.

**Exact signature / axioms / independent negative probes — exit 0:**

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOCsplit2Audit.lean
```

The scratch file imports Tests.Seg and reuses 25 exact revision-2 theorem headers under fresh examples, with only the documented name mapping; the production exports discharge them. It prints axioms of all 70 public theorems, with the per-declaration results recorded in the ledger: 50 S, 10 Q, 9 P, 1 axiom-free. No `sorryAx` or extra trust input. Three additional independent examples check the absent-witness fallible operation and exclusion of the old hR counterexample. Initial scratch failures were auditor scaffolding defects: omitted namespace opens for `opDeps`/`nopOp` and a docstring mistakenly scanned as a declaration named `per`. Corrected scratch re-elaborates without changing package sources or budgets. Scratch-only unused-tactic and overlapping-instance warnings do not affect the package.

**Kernel replay — exit 0, one invocation:**

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.CertificateSharp.Kernel.SegDefs KAM.CertificateSharp.Kernel.SegAgree KAM.CertificateSharp.Kernel.SegChain KAM.CertificateSharp.Kernel.SegOne KAM.CertificateSharp.Kernel.SegBridges KAM.CertificateSharp.Tests.Seg
```

Exact output:

```text
replaying KAM.CertificateSharp.Tests.Seg
replaying KAM.CertificateSharp.Kernel.SegBridges
replaying KAM.CertificateSharp.Kernel.SegOne
replaying KAM.CertificateSharp.Kernel.SegChain
replaying KAM.CertificateSharp.Kernel.SegAgree
replaying KAM.CertificateSharp.Kernel.SegDefs
```

**Hygiene:** all six modules have copyright, module, public imports, module docstring and exposed public section. Line counts: SegDefs 344; SegAgree 393; SegChain 298; SegOne 78; SegBridges 83; Tests.Seg 221, all below both 400 and 1500. Direct forbidden-token/override scan returned no matches. Public-name checker command:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-socsplit2 KAM.CertificateSharp.Kernel.SegDefs KAM.CertificateSharp.Kernel.SegAgree KAM.CertificateSharp.Kernel.SegChain KAM.CertificateSharp.Kernel.SegOne KAM.CertificateSharp.Kernel.SegBridges KAM.CertificateSharp.Tests.Seg
```

Exit 0: `short-name check OK (no reused public short name)`.

Local import closure scan covers 114 project modules: no provider, no frozen theorem, no DRAFT_SORRY import; all 19 reachable frozen definitions have manifest state SEALED. These inherited definitions are unchanged; this computational package does not re-audit their analytic source correspondence. Frozen guard and ABI verification are recorded with lint below.

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted generated-root mismatch. No root regeneration performed. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/CertificateSharp.lean)
check_lean_modules: PASS (1692 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

Protected-path command `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md` produced no output (exit 0). `git diff --check inp...HEAD` passed. Final input hashes and report whitespace are rechecked, scratch probes removed, and the only persistent worktree change is this report.

## Closeout

All new declarations classified; exact design signatures and bodies checked; chain/consumer proofs reviewed; public axioms and kernel replay checked; no unrefuted blocking finding. The conditional generic computational result is approved within scope. Production DATA, product-memoized consumers and calibration remain separate obligations. No frozen anchor is marked proved or seal-ready by this report.
