# SO-KDEPTH2 independent package audit 1

Verdict: **PASS WITH NOTES** for the compiler refactor, subject to the completed verification receipts below. No frozen anchor is sealed or promoted by this package. The performance conclusion is bounded to the tested lock and R2 programs; there is no proved logarithmic depth bound for arbitrary inputs.

## Scope and immutable inputs

Audit date: 2026-10-30. Worktree: `/root/code/KAM-inp-sokdepth2`. Audited HEAD: `588cd1e2bec6666ef6d7edca4244206565e7be45`; `inp` at initial inspection: `eb722cbc51ba0a6d84e3c8567fcba010df8eb6ab`; merge base: `7e8f8c0224ec6fd0fab2e3c9707c61076abe57d2`. The complete `git diff inp...HEAD` has six files: five Lean files and the handoff. The handoff's opening reference to “four Lean files” is a harmless count error.

The user's explicit report destination overrides the generic brief's MAIN-worktree destination. Only this report is edited outside `.lake/abi-scratch/maud-sokdepth2-1/`. No state-changing git, source repairs, generated-root edits, dependency changes, full rebuild, or subagents. All auditor Lean/Lake invocations are serialized, with `LEAN_NUM_THREADS=1` and niceness 5; builds use the prescribed gate. Other agents' processes outside this audit are outside this report's serialization claim.

Read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package-audit brief, the complete handoff including AUDIT FOCUS, and SO design revision 7 (`docs/tracks/SO/design/SO-LEAN-DESIGN.md`, especially derivative and denominator-slot contracts). D39 authorizes implementation changes while retaining statements and certificate format. `docs/tracks/SO/statement.md` and `blueprint-SO/` do not exist in this snapshot. There are no package frozen anchors, providers, or I/N/P blueprint nodes to seal: provider/frozen type-equality and seal-body probes are therefore N/A. The operational specifications are the old compiler and the SO derivative/nonvanishing contracts, not a substituted I/N/P theorem.

Method: focused, refute-first audit using the statement-audit and manuscript-audit principles. Acceptance criteria: exact old public headers; exact program/table simulation; retained domain checks; no new assumptions or trust escapes; targeted builds, theorem axiom census, kernel replay and lock-scale kernel evaluation; lint except the expressly permitted generated-root staleness. Performance is measured separately from mathematical equivalence.

SHA-256 snapshot (frozen-v1):

| File | SHA-256 |
|---|---|
| `KAM/Certificate/Expr/Ball.lean` | `3d947f54e381d7fbd8507f953a3a249c3d0bc651aa36ea2a2b9763b6434c8dec` |
| `KAM/Certificate/Expr/Diff.lean` | `099abaa84c6a500f8bf8e89ef51924b0d913f97fbc2688c1ce3005d0bd5c410a` |
| `KAM/Certificate/Expr/DiffBuf.lean` | `38a8ec32a76955221f85b74aa9bdec4e13a84b37c215a455b9ab25c3b4b7ef20` |
| `KAM/Certificate/Expr/DiffCompile.lean` | `59df2ca17a7ca6c31d148cb3c3158577e1043fc503697710ad211e827fc9ebd5` |
| `KAM/CertificateSharp/Ham/BallsTrig.lean` | `e241531ee5dc3852c42e3e9f47096cd0a25aeb50b7d8c5ec5dc450ecef393d7c` |
| `docs/tracks/SO/audits/SO-KDEPTH2-handoff.md` | `91f2a397dab400dfec4150e5f4ddfaf73f8d69f535cf2333e22cf515559c379c` |

## Findings and adversarial checks

No correctness blocker survived refutation.

1. **Emission order and slot identity — PASS.** `DiffBuf.lean:83` emits the scaling constant before multiplying its slot by the operand, matching `DiffBuild.lean:44`; zero constants and `none` follow the same branches. `DiffBuf.lean:377` emits inverse, square, cube, fourth power in specification order. At `DiffBuf.lean:431`, `let r0 := slpEmitB b (.sqrt A.v)` is followed by `let r1 := slpEmitB r0.1 (.inv b.len)`: `b.len` is the square-root slot, whereas `r0.1.len` would be the next slot. The latter possible off-by-one objection is refuted by inspection and `slpSqrtPreB_ofOpList`.
2. **Action/character guards — PASS.** At `DiffBuf.lean:233,248`, action first derivatives use `i = n + j`, characters use `i < n`, `i < n ∧ j < n`, and `i < n ∧ j < n ∧ l < n`. Missing key entries use the same existing `getD ... 0`. Dimensions, coefficient signs, `(2π)` degrees and multiplication order match the old nodes. Simulation covers arbitrary dimensions, keys and operand nodes; no validity-of-slot assumption is added.
3. **Full compiler preservation — PASS.** The literal conclusion at `DiffBuf.lean:572` is `slpCompileB e (SlpBuf.ofOpList s) = (SlpBuf.ofOpList (slpCompile e s).1, (slpCompile e s).2)`. This quantifies over every expression and initial list, not just empty programs or test expressions. It preserves the entire node, including all derivative tables, not merely evaluated values. Structural induction covers all 13 constructors; the power case includes exponent zero. `HamExpr.jet_eq` (`Diff.lean:61`) converts the actual production seed `⟨[.const 0 0 0], 1⟩` by definitional equality to `ofOpList [.const 0 0 0]` and transports the whole jet.
4. **Denominator/square-root validation — PASS.** A possible objection that equivalence preserves values but drops validation slots is refuted by equality of the entire program. Both subexpressions still compile before combining, including zero-product and zero-power cases. `Ball.lean:773` and `BallsTrig.lean:458` replace only prefix proof terms with rewriting by `jet_eq`; all original nonvanishing premises and conclusions remain. No semantic fallback is introduced.
5. **Lazy counter limitation — NOTE, explicitly retained.** Buffer emission is cons plus `b.len + 1`; the production path never calls the old appending compiler or `ofOpList` on a growing program. `opList` reverses only at output. However, the counter is a linear lazy addition chain, power compilation recurses on the exponent, and table/expression recursion remains. The package title “log-depth” is not an asymptotic theorem. The lock-scale measurements justify current use; they do not establish universal depth safety or 10,000-op behavior. The handoff acknowledges this at its “Limit” paragraph; no blocker is inferred from an unclaimed universal bound.
6. **Consumers — PASS within audited scope.** `Sound/Ham.lean:105–117`, `Sound/Energy.lean:60`, `Sound/Invariance.lean:105`, and `CertificateSharp/V2/HamClaim.lean:67–81` use the preserved semantic bridges. Searches for direct old-compiler unfolding in these consumer directories found only the intentionally repaired prefix proof in `BallsTrig`. Slot/program consumers remain valid because whole jets are equal. The downstream `Lock.Graph` build and consumer axiom probes pass. The handoff's full-library build is author evidence, not an independent full-library rerun here.

The 299-line declaration block from `def slpScaleNode` through `slpCompile_sound` is literally present in `DiffCompile.lean`; all 32 old public `Diff.lean` headers are byte-identical after relocating declarations. All 52 `Ball.lean` and 26 `BallsTrig.lean` declaration headers are unchanged. `DiffBuild.lean`, `DiffNode.lean`, and `DiffNodeSqrt.lean` are byte-identical to `inp`. These checks refute accidental premise, binder-order, carrier, and conclusion changes at the adaptation boundary.

## Declaration ledger

Every package declaration below has been inspected against either its byte-identical old declaration or the corresponding operational simulation contract. Names are in `KAM.Certificate` except the final sharp-ball bridge. “PASS” for a helper means its stated implementation contract, not closure of a campaign theorem. The ledger includes unchanged declarations in the relocated block and the retained facade for completeness.

| Contract / source | Declaration (line at frozen-v1) | Verdict | Reason / definition classification |
|---|---|---|---|
| SO nonvanishing contract | `HamExpr.nonvanishingOn_of_balls` (`Ball.lean:768`) | PASS | Header unchanged; only prefix proof rewritten via jet_eq. |
| Old facade / jet bridge | `HamExpr.jetAppend` (`Diff.lean:40`) | PASS | Literal old jet body under a distinct name; full carrier. |
| Old facade / jet bridge | `HamExpr.jet` (`Diff.lean:52`) | PASS | Header unchanged; buffer seed valid; whole body equals old jet by jet_eq. |
| Old facade / jet bridge | `HamExpr.jet_eq` (`Diff.lean:61`) | PASS | Unconditional equality for every n and expression, by total simulation. |
| Old facade / jet bridge | `slpCompile_prefix` (`Diff.lean:66`) | PASS | Old declaration and body unchanged. |
| Old facade / jet bridge | `zero_slot_val` (`Diff.lean:70`) | PASS | Old declaration and body unchanged. |
| Old facade / jet bridge | `slpOv_eq_val` (`Diff.lean:79`) | PASS | Old declaration and body unchanged. |
| Old facade / jet bridge | `list_getD_map` (`Diff.lean:86`) | PASS | Old declaration and body unchanged. |
| Old facade / jet bridge | `HamExpr.jet_v0` (`Diff.lean:90`) | PASS | Old header unchanged; semantic bridges rewrite jet_eq before old argument. |
| Old facade / jet bridge | `HamExpr.jet_d1` (`Diff.lean:95`) | PASS | Old header unchanged; semantic bridges rewrite jet_eq before old argument. |
| Old facade / jet bridge | `HamExpr.jet_d2` (`Diff.lean:113`) | PASS | Old header unchanged; semantic bridges rewrite jet_eq before old argument. |
| Old facade / jet bridge | `HamExpr.jet_d3` (`Diff.lean:141`) | PASS | Old header unchanged; semantic bridges rewrite jet_eq before old argument. |
| Buffer simulation | `SlpBuf` (`DiffBuf.lean:37`) | PASS | Operational storage pair; raw buffers may have inconsistent len; no unrestricted soundness claim. |
| Buffer simulation | `SlpBuf.ofOpList` (`DiffBuf.lean:42`) | PASS | Literal reverse and list length; creates the intended invariant. |
| Buffer simulation | `SlpBuf.opList` (`DiffBuf.lean:45`) | PASS | Literal reverse; defined on every raw buffer. |
| Buffer simulation | `SlpBuf.opList_ofOpList` (`DiffBuf.lean:47`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `SlpBuf.len_ofOpList` (`DiffBuf.lean:50`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `SlpSim` (`DiffBuf.lean:54`) | PASS | Literal operational relation, universally quantifying the initial list; helper only. |
| Buffer simulation | `slpEmitB` (`DiffBuf.lean:60`) | PASS | Literal cons/increment with returned pre-emission slot. |
| Buffer simulation | `slpEmitB_ofOpList` (`DiffBuf.lean:63`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpEmitB_ofOpList_fst` (`DiffBuf.lean:67`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpAddOB` (`DiffBuf.lean:72`) | PASS | Literal twin of `slpAddO`; same cases, order and slots. |
| Buffer simulation | `slpMulOB` (`DiffBuf.lean:78`) | PASS | Literal twin of `slpMulO`; same cases, order and slots. |
| Buffer simulation | `slpScaleOB` (`DiffBuf.lean:83`) | PASS | Literal twin of `slpScaleO`; same cases, order and slots. |
| Buffer simulation | `slpAddOB_ofOpList` (`DiffBuf.lean:89`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpMulOB_ofOpList` (`DiffBuf.lean:93`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpScaleOB_ofOpList` (`DiffBuf.lean:97`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpMapStB` (`DiffBuf.lean:111`) | PASS | Literal twin of `slpMapSt`; same cases, order and slots. |
| Buffer simulation | `slpMapStB_sim` (`DiffBuf.lean:119`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `SlpCompB` (`DiffBuf.lean:129`) | PASS | Literal buffer state-transformer type. |
| Buffer simulation | `slpPureB` (`DiffBuf.lean:132`) | PASS | Literal twin of `slpPure`; same cases, order and slots. |
| Buffer simulation | `slpCAddB` (`DiffBuf.lean:135`) | PASS | Literal twin of `slpCAdd`; same cases, order and slots. |
| Buffer simulation | `slpCMulB` (`DiffBuf.lean:141`) | PASS | Literal twin of `slpCMul`; same cases, order and slots. |
| Buffer simulation | `slpCScaleB` (`DiffBuf.lean:147`) | PASS | Literal twin of `slpCScale`; same cases, order and slots. |
| Buffer simulation | `slpPureB_sim` (`DiffBuf.lean:151`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpCAddB_sim` (`DiffBuf.lean:153`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpCMulB_sim` (`DiffBuf.lean:158`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpCScaleB_sim` (`DiffBuf.lean:163`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpTab1B` (`DiffBuf.lean:169`) | PASS | Literal twin of `slpTab1`; same cases, order and slots. |
| Buffer simulation | `slpTab2B` (`DiffBuf.lean:173`) | PASS | Literal twin of `slpTab2`; same cases, order and slots. |
| Buffer simulation | `slpTab3B` (`DiffBuf.lean:178`) | PASS | Literal twin of `slpTab3`; same cases, order and slots. |
| Buffer simulation | `slpTab1B_sim` (`DiffBuf.lean:182`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpTab2B_sim` (`DiffBuf.lean:186`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpTab3B_sim` (`DiffBuf.lean:190`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpFinishB` (`DiffBuf.lean:195`) | PASS | Literal twin of `slpFinish`; same cases, order and slots. |
| Buffer simulation | `slpFinishB_sim` (`DiffBuf.lean:202`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpConstNodeB` (`DiffBuf.lean:221`) | PASS | Literal twin of `slpConstNode`; same cases, order and slots. |
| Buffer simulation | `slpConstNodeB_ofOpList` (`DiffBuf.lean:225`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpActionNodeB` (`DiffBuf.lean:233`) | PASS | Literal twin of `slpActionNode`; same cases, order and slots. |
| Buffer simulation | `slpActionNodeB_ofOpList` (`DiffBuf.lean:237`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpCharNodeB` (`DiffBuf.lean:248`) | PASS | Literal twin of `slpCharNode`; same cases, order and slots. |
| Buffer simulation | `slpCharNodeB_ofOpList` (`DiffBuf.lean:260`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpCrossB` (`DiffBuf.lean:268`) | PASS | Literal twin of `slpCross`; same cases, order and slots. |
| Buffer simulation | `slpCrossB_sim` (`DiffBuf.lean:273`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpAddNodeB` (`DiffBuf.lean:277`) | PASS | Literal twin of `slpAddNode`; same cases, order and slots. |
| Buffer simulation | `slpAddNodeB_ofOpList` (`DiffBuf.lean:283`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpMulD3B` (`DiffBuf.lean:291`) | PASS | Literal twin of `slpMulD3`; same cases, order and slots. |
| Buffer simulation | `slpMulNodeB` (`DiffBuf.lean:303`) | PASS | Literal twin of `slpMulNode`; same cases, order and slots. |
| Buffer simulation | `slpMulNodeB_ofOpList` (`DiffBuf.lean:314`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpExpD3B` (`DiffBuf.lean:322`) | PASS | Literal twin of `slpExpD3`; same cases, order and slots. |
| Buffer simulation | `slpExpNodeB` (`DiffBuf.lean:328`) | PASS | Literal twin of `slpExpNode`; same cases, order and slots. |
| Buffer simulation | `slpExpNodeB_ofOpList` (`DiffBuf.lean:336`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpInvD3B` (`DiffBuf.lean:347`) | PASS | Literal twin of `slpInvD3`; same cases, order and slots. |
| Buffer simulation | `slpInvD3B_sim` (`DiffBuf.lean:353`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpInvTailB` (`DiffBuf.lean:360`) | PASS | Literal twin of `slpInvTail`; same cases, order and slots. |
| Buffer simulation | `slpInvTailB_ofOpList` (`DiffBuf.lean:370`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpInvPreB` (`DiffBuf.lean:377`) | PASS | Literal twin of `slpInvPre`; same cases, order and slots. |
| Buffer simulation | `slpInvPreB_ofOpList` (`DiffBuf.lean:384`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpInvNodeB` (`DiffBuf.lean:390`) | PASS | Literal twin of `slpInvNode`; same cases, order and slots. |
| Buffer simulation | `slpInvNodeB_ofOpList` (`DiffBuf.lean:394`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpSqrtD3B` (`DiffBuf.lean:401`) | PASS | Literal twin of `slpSqrtD3`; same cases, order and slots. |
| Buffer simulation | `slpSqrtD3B_sim` (`DiffBuf.lean:407`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Buffer simulation | `slpSqrtTailB` (`DiffBuf.lean:414`) | PASS | Literal twin of `slpSqrtTail`; same cases, order and slots. |
| Buffer simulation | `slpSqrtTailB_ofOpList` (`DiffBuf.lean:424`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpSqrtPreB` (`DiffBuf.lean:431`) | PASS | Literal twin of `slpSqrtPre`; same cases, order and slots. |
| Buffer simulation | `slpSqrtPreB_ofOpList` (`DiffBuf.lean:439`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpSqrtNodeB` (`DiffBuf.lean:446`) | PASS | Literal twin of `slpSqrtNode`; same cases, order and slots. |
| Buffer simulation | `slpSqrtNodeB_ofOpList` (`DiffBuf.lean:450`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpScaleNodeB` (`DiffBuf.lean:459`) | PASS | Literal twin of `slpScaleNode`; same cases, order and slots. |
| Buffer simulation | `slpScaleNodeB_ofOpList` (`DiffBuf.lean:463`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpExpScaleNodeB` (`DiffBuf.lean:469`) | PASS | Literal twin of `slpExpScaleNode`; same cases, order and slots. |
| Buffer simulation | `slpExpScaleNodeB_ofOpList` (`DiffBuf.lean:473`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpCombineB` (`DiffBuf.lean:480`) | PASS | Literal twin of `slpCombine`; same cases, order and slots. |
| Buffer simulation | `slpCombineB_ofOpList` (`DiffBuf.lean:486`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpPowNodeB` (`DiffBuf.lean:493`) | PASS | Literal twin of `slpPowNode`; same cases, order and slots. |
| Buffer simulation | `slpPowNodeB_ofOpList` (`DiffBuf.lean:497`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpTrigNodeB` (`DiffBuf.lean:505`) | PASS | Literal twin of `slpTrigNode`; same cases, order and slots. |
| Buffer simulation | `slpTrigNodeB_ofOpList` (`DiffBuf.lean:510`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpTrigCharB` (`DiffBuf.lean:517`) | PASS | Literal twin of `slpTrigChar`; same cases, order and slots. |
| Buffer simulation | `slpTrigCharB_ofOpList` (`DiffBuf.lean:521`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpDivNodeB` (`DiffBuf.lean:528`) | PASS | Literal twin of `slpDivNode`; same cases, order and slots. |
| Buffer simulation | `slpDivNodeB_ofOpList` (`DiffBuf.lean:531`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpCompileB` (`DiffBuf.lean:537`) | PASS | Literal twin of `slpCompile`; same cases, order and slots. |
| Buffer simulation | `slpCompileB_ofOpList` (`DiffBuf.lean:572`) | PASS | Exact buffer/program and result equality; all initial lists. |
| Buffer simulation | `slpCompileB_opList` (`DiffBuf.lean:591`) | PASS | Projection or structural simulation; no extra analytic premise. |
| Old `Diff.lean` | `slpScaleNode` (`DiffCompile.lean:37`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpScaleNode_sound` (`DiffCompile.lean:41`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpExpScaleNode` (`DiffCompile.lean:51`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpExpScaleNode_sound` (`DiffCompile.lean:55`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpCombine` (`DiffCompile.lean:64`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpCombine_sound` (`DiffCompile.lean:70`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpPowNode` (`DiffCompile.lean:84`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpPowNode_sound` (`DiffCompile.lean:88`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `negKey` (`DiffCompile.lean:109`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `modePhase_negKey` (`DiffCompile.lean:111`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpTrigNode` (`DiffCompile.lean:122`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpTrigChar` (`DiffCompile.lean:128`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpDivNode` (`DiffCompile.lean:134`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `JetSmoothOn.charFn` (`DiffCompile.lean:137`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpTrigNode_sound` (`DiffCompile.lean:141`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpTrigChar_sound` (`DiffCompile.lean:153`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpDivNode_sound` (`DiffCompile.lean:165`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `cos_eq_exp` (`DiffCompile.lean:174`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `sin_eq_exp` (`DiffCompile.lean:182`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpCompile` (`DiffCompile.lean:191`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `HamExpr.jetSmoothOn` (`DiffCompile.lean:225`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `HamExpr.nonvanishingOn_empty` (`DiffCompile.lean:229`) | PASS | Verbatim declaration and body. |
| Old `Diff.lean` | `slpCompile_sound` (`DiffCompile.lean:244`) | PASS | Verbatim declaration and body. |
| SO nonvanishing contract | `nonvanishingOn_of_ballsTrig` (`BallsTrig.lean:453`) | PASS | Header unchanged; only prefix proof rewritten via jet_eq. |

All new definitions are literal operational objects, rather than objects selected by a source uniqueness characterization: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A. No new classical selection or junk/default fallback is introduced. `SlpBuf` deliberately does not package a proof that `len = rev.length`; soundness is proved for canonical `ofOpList` inputs, and the only production seed is definitionally canonical. No theorem asserts correctness of arbitrary inconsistent raw buffers.

The file-local `slp_sim` macro (`DiffBuf.lean:212`) expands only the existing structural simulation tactics. It creates no unchecked declarations or new trust boundary.

Binder review of the two unconditional preservation results (expanded project objects are literal expressions, lists, buffers, nodes and jets):

| Declaration | Expanded binder | Bin | Justification |
|---|---|---|---|
| `slpCompileB_ofOpList` | `{n : ℕ}` | TYPING | Expression dimension. |
| `slpCompileB_ofOpList` | `(e : HamExpr n)` | TYPING | Arbitrary syntactic input. |
| `slpCompileB_ofOpList` | `(s : List SlpOp)` | TYPING | Arbitrary initial program. |
| `HamExpr.jet_eq` | `{n : ℕ}` | TYPING | Expression dimension. |
| `HamExpr.jet_eq` | `(e : HamExpr n)` | TYPING | Arbitrary syntactic input. |

Counts: SOURCE 0, STANDING 0, TYPING 5, RULED 0, EXCESS 0. Higher-order simulation lemmas explicitly take simulation hypotheses for their component computations (`SlpSim` expands to the literal input/output equality); these are compositional helper premises, supplied by the node proofs, and absent from the final preservation results. They are not substituted for a source theorem. Existing analytic premises (`IsOpen`, smoothness, `NonvanishingOn`, membership and dimension/index data) are retained exactly in the old public types.

## Independent verification receipts

All commands run from this worktree. Every command below uses `LEAN_NUM_THREADS=1`; every Lean/Lake process is started at niceness 5. Builds are through `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh`.

- Targeted build:
  `env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sokdepth2 KAM.Certificate.Expr.DiffBuf KAM.Certificate.Expr.Ball KAM.CertificateSharp.Ham.BallsTrig`
  exited 0, `Build completed successfully (3263 jobs).`
- Downstream build:
  same gate command with target `KAM.SpinOrbit.Lock.Graph` exited 0,
  `Build completed successfully (3548 jobs).`
  Both builds replayed existing dependency warnings (Basic, PiHigh, Sound/Static, Sound/Ham, ODE/Exit and sharp Corner/SupBound); no changed-file warning. These are targeted build validations, not claims that all jobs recompiled.
- Signature probe:
  `env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-sokdepth2-1/Signatures.lean`
  exited 0, no output. Generated 22 examples directly from the old theorem headers, each proved by the current export applied to exactly its explicit binders in order. The first scratch attempt placed local `Ph` notation before `n` was in scope and failed; moving the notation below the variable declaration corrected the probe, without changing package files or options.
- Axiom census:
  same command with `Axioms.lean` exited 0. All 115 public theorems in the five changed files, including all 40 new buffer theorems and `jet_eq`, plus four downstream soundness theorems: 119 outputs; 77 use `[propext, Classical.choice, Quot.sound]`, 28 use `[propext]`, 12 use `[propext, Quot.sound]`, two are axiom-free. No `sorryAx`, project axiom, or reduction oracle.
- Kernel replay:
  `env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Expr.DiffCompile KAM.Certificate.Expr.DiffBuf KAM.Certificate.Expr.Diff KAM.Certificate.Expr.Ball KAM.CertificateSharp.Ham.BallsTrig`
  exited 0, exact output:

```text
replaying KAM.CertificateSharp.Ham.BallsTrig
replaying KAM.Certificate.Expr.Ball
replaying KAM.Certificate.Expr.Diff
replaying KAM.Certificate.Expr.DiffBuf
replaying KAM.Certificate.Expr.DiffCompile
```

Key axiom output (the full census was checked, not just these samples):

```text
'KAM.Certificate.HamExpr.nonvanishingOn_of_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_v0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCompileB_ofOpList' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.nonvanishingOn_of_ballsTrig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.checkTorusCertificateSharp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.V2.checkTorusCertificateV2_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockBarrier_of_certV2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

PERFORMANCE_AND_LINT_PENDING

## Errata, deviations and closeout

No suspected pinned mathematical-source or blueprint defect found within this implementation-refactor scope. No new interpretation of an I/N/P frozen theorem is claimed. The existing SO design says `HamExpr.jet` “appends forward-mode derivative slots” (`SO-LEAN-DESIGN.md:241`); this remains correct extensionally, while its implementation now accumulates in reverse. The file split preserves the public import path. No audit repairs or deviations were introduced.

Closeout: REPORT_FINALIZATION_PENDING
