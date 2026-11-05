LOCK-DATA independent package audit 1, 2026-11-05 UTC.

**Overall verdict: PASS WITH NOTES.** No mathematical, premise-smuggling, codec-soundness, or frozen-statement-fit failure was found. The local source/axiom/type checks and all 17 selected leaf-module kernel replays passed; exact source elaboration also passed for GraphK and Seg.Checks. The notes concern incorrect handoff guidance about checker prefix selection, generated-root staleness, Phase B installation/application ownership/sealing, and the explicit scope of returned untracked data.

| Frozen anchor | Verdict | Reason / seal status |
|---|---|---|
| `KAM.SpinOrbit.lunar_sync_lock` | PASS WITH NOTES | N65 theorem bridges to the exact frozen telescope; the candidate and exact ordered-binder seal application elaborate with only the standard three axioms. The production headline provider is still the deliberately empty Phase A stub and must be installed in Phase B. No seal was performed. |
| `KAM.SpinOrbit.lunarSyncOrbit_spec` | PASS (seal-ready provider) | Prepared source at 41934621 elaborates and has exactly the frozen type; its seal copy and direct `type_of%` check pass. |
| `KAM.SpinOrbit.lunarSyncOrbit_unique` | PASS (seal-ready provider) | Exact `(ψ : ℝ → ℝ) (h : IsSyncOrbit ψ)` telescope and conclusion; no extra premise or restricted uniqueness domain. |
| `KAM.SpinOrbit.lunarSyncOrbit_bound` | PASS (seal-ready provider) | Exact arbitrary-φ bounds `17/1000000` and `27/200000`, including the derivative bound. |

Audit location: `/root/code/KAM-inp-lockdata`. This report follows the user's explicit destination, overriding the generic brief's main-worktree destination. Authority read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/SO/audits/LOCK-DATA-handoff.md`, especially AUDIT FOCUS and the replay/memory notes. The SO statement authority is `docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md` §1 and `SO-LOCK-DESIGN.md` §1, with `SO-CSPLIT.md` for the computation-only split interface. There is no `docs/tracks/SO/statement.md` or `blueprint-SO/` in this tree; I used those explicit SO authorities rather than silently substituting an I/N/P theorem.

Snapshot: data branch HEAD `83d67530bc704bc524864f7115c5692967f807b1`; comparison `git diff inp...HEAD`, with `inp = 23e1a9f916ddac3fb2b06f663f482663369183a9`. The last Lean/data change is `447772bf1cd2506da75b60501edc6fbf7d1a3c9a`. Prepared bridge/providers were read at `/root/code/KAM-inp-lockdesign`, HEAD `41934621edbf90aaeb0980d1594c59a8135b01c6`. All corresponding frozen SpinOrbit source files were compared byte-for-byte between the two worktrees: identical. The protected-path diff `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. No source, frozen file, manifest, root, or git state was changed by this audit. Only this report and temporary ABI scratch probes were written; generated build outputs are check artifacts.

The tracked Lean diff consists of 65 files, 63 named definitions/abbreviations and 165 named theorems, plus the derived equality instance and its anonymous example in `SegDecide`. All lie under `KAM/SpinOrbit/Data/LockN65/`. The materialized data tree has 13,668 Lean modules, including 13,603 symlinks. The source-content fingerprint is SHA256 `0ff3b744eb3488811251173675a56fb983a95fb2ffe1e2813a9562a51d7f8abc`, computed in sorted relative-path order by hashing each UTF-8 path, NUL, and raw SHA256 of its dereferenced bytes. This fixes the untracked data actually inspected; a commit alone does not pin those bytes.

The source import closure of `AssemblyN65` contains 13,665 LockN65 modules and 13,997 KAM modules altogether. It has no missing source modules, provider imports, frozen theorem imports, or DRAFT_SORRY dependencies. Its 32 imported manifest definitions are all SEALED. The three LockN65 modules outside that closure are `ErrRadiusTbl`, `ExpSplit`, and `SegRoutesProbe`; they are included in the tracked-theorem axiom probe. This audit did not replay the entire generated closure. The remote build and background sampling in the handoff remain separately attributed evidence; local checks below are the independent evidence obtained here.

The no-smuggling check passes at source level. `lunar_sync_lock_N65` has explicit binders `(q₀ p₀ φ₀ : ℝ)` and the one frozen action premise `h₀`. `lock_barrier` has no hypotheses. The latter applies `lockBarrier_of_certV2K` with discharged positivity, Hamiltonian identity, lower-action positivity, torus-check pass, graph-check pass, frequency enclosure, and the Diophantine theorem at γ = 1/67, τ = 1. The κ used by the certificate is `hamScale = 1000001/1000000`, and its Hamiltonian identity is supplied by `rfl`; it is not an unstated κ = 1 assumption. General helpers have computational equality/check premises or the explicit `CertifiedTorus` interface; these are discharged in the concrete chain, never exported as extra headline premises.

`lock_passes` preserves every conjunct: static, Hamiltonian bounds, embedding, invariance, energy, Gram and torsion go through `landedBase_check_of`; the Hamiltonian claim, all four frame-majorant checks, and the refined core go through `checkTorusCertificateV2_refined_of`. The refined witness is exactly `Sum.inr (Sum.inr refinedWit)`. `lockGraph_passes` supplies all four keyed graph conjuncts (strict strip margin, monotonicity, lower action, upper action). The graph soundness proof retains the same four real conclusions as landed `checkSoGraph_sound` and uses the lawful arithmetic/enclosure interfaces. Its only semantic adaptation is the independently selected product key `[7,0]`, `[7,1]`, `[7,2]`. No checker premise is removed.

The 187 full and 386 low composition segments are tied to their actual lists by kernel-decided lengths/plan checks. The universal segment claims enumerate all indices and reject the remaining indices by arithmetic contradiction. Energy and all four invariance rows consume the full checkpoint chain; Gram/torsion/frame consume the corresponding low stages. `CornerSplit` is exhaustive: `signLists 2` lists exactly four sign vertices; FrameN uses four rows and two columns, each at four vertices; FrameT uses two rows, each at four vertices. Splitting changes neither the corner checker nor its radius. The Ham jet is tied to the compiled expression by `lock_jet`; the ball pass is reconstructed from three contiguous checked segments. Packed-product shard/decode/remainder lemmas require monotone cuts, exact endpoints, and every per-piece equality; no omitted-slot convention is used to close a check.

The final assembly invokes the landed, explicitly conditional `lunar_sync_lock_of_barrier_check`, discharging the barrier and both range bounds. Its lower window is `13155/1000000`, not the older helper's `132/10000`; the new `lock_literalCheck65` rechecks the actual window. The frozen literals `129/10000`, `21/100`, `26/1000`, and strict `1/4`, the all-real-time quantifier, real derivative equation with `soField`, and uniqueness among all trajectories with the same initial point are retained. The frozen/landed orbit equation bridge uses `soField_eq`; predicate equality uses `funext` and `propext`, so the identical `Classical.choose` expressions select the same orbit. `libAction` and rational `lunarOmega = 8/65` agree definitionally. The fallback zero in each chosen-orbit definition is excluded by the landed existence/spec theorem; it is not used to prove confinement or the orbit specification.

Definition classification: all literal data are untrusted candidate objects fed to the actual checker. `tm`, `etF`, fixed precision/backend, rational/frequency/parameter constants, jet programs and index tables are direct encodings; `lockQ` is the actual refined numerical computation. No new structure bundles an unproved analytic assertion. `ballBeq`/`ballsBeq`, row/matrix/error-term comparators have equality-reflection proofs. `KeySep`, `ErrFree`, and `monoFrom` state the exact order/zero-error/monotonicity properties needed by their split lemmas. `pieceAt`, `cutPairs`, `levelNCseg`, and the natural-number chunk folds denote the advertised finite operations on their whole carriers.

The codecs are deliberately total decoders, not universal validity claims: malformed or oversized varints are bounded by the explicit 24-byte fuel; negative run/slot values use `toNat`; incomplete Fourier rows/pairs are dropped; zero denominators follow `mkRat`'s total semantics. Those cases do not assert an enclosure or bypass a check. The decoded object itself is checked. `weightTermTbl` defaults to zero out of range, but `errRadius_eq_tbl` requires all actual degrees below the exact table length, excluding that fallback in every equality-based use. The keyed graph models and their memo forms carry the complete landed error-radius formula; arbitrary memo values are constrained by exact product/model equalities. `FallbackMul` preserves the landed sound ball when a packed product fails; it does not return a zero error. The nine toy definitions in `SegRoutesProbe` are explicitly toy data, outside the headline closure.

The orphan `deriving instance DecidableEq for SlpOp` is structural decidable equality, introduced to kernel-decide long operation-list equalities. It contributes no proposition as an axiom and does not change `SlpOp` or its semantics. Its direct production importers in the reconstructed closure are generated segment modules (276 direct importers); it is not an analytic assumption. The instance's orphan status remains a disclosed maintenance note.

The following table inventories every named declaration in the tracked Lean diff. Names are relative to `KAM.SpinOrbit.Data.LockN65`; line numbers refer to this snapshot. PASS in this table is the statement/definition assessment, with validation and scope notes below. The generated families are reviewed separately in the subsequent node table.

| Node / file:line | Lean declaration | Verdict | Reason / definition classification |
|---|---|---|---|
| `AdvLookup.lean:28` | `adviceLookup_skip_cseg` | PASS | First-match lookup preserved; skipped prefix checked key-free. |
| `AdvLookup.lean:39` | `adviceLookup_at_cseg` | PASS | First-match lookup preserved; skipped prefix checked key-free. |
| `AdvLookup.lean:55` | `lock_advLow_blocks` | PASS | First-match lookup preserved; skipped prefix checked key-free. |
| `AdvLookup.lean:64` | `lock_advFull_blocks` | PASS | First-match lookup preserved; skipped prefix checked key-free. |
| `AdvLookupSub.lean:30` | `adviceLookup_subAdvice_cseg` | PASS | Witness sub-book lookup equals full-key lookup for every book. |
| `AdvLookupSub.lean:57` | `adviceLookup_forWitness_cseg` | PASS | Witness sub-book lookup equals full-key lookup for every book. |
| `AssemblyN65.lean:40` | `lock_literalCheck65` | PASS | Concrete discharged assembly; frozen literals and sole action premise retained. |
| `AssemblyN65.lean:46` | `lock_dio` | PASS | Concrete discharged assembly; frozen literals and sole action premise retained. |
| `AssemblyN65.lean:63` | `lock_barrier` | PASS | Concrete discharged assembly; frozen literals and sole action premise retained. |
| `AssemblyN65.lean:74` | `lunar_sync_lock_N65` | PASS | Concrete discharged assembly; frozen literals and sole action premise retained. |
| `BallChain.lean:30` | `ballBeq` | PASS | Definition: Exact ball/list equality reflection and contiguous three-segment reconstruction. |
| `BallChain.lean:33` | `ballsBeq` | PASS | Definition: Exact ball/list equality reflection and contiguous three-segment reconstruction. |
| `BallChain.lean:38` | `eq_of_ballBeq` | PASS | Exact ball/list equality reflection and contiguous three-segment reconstruction. |
| `BallChain.lean:46` | `eq_of_ballsBeq` | PASS | Exact ball/list equality reflection and contiguous three-segment reconstruction. |
| `BallChain.lean:55` | `ballsRev_append` | PASS | Exact ball/list equality reflection and contiguous three-segment reconstruction. |
| `BallChain.lean:71` | `segOk` | PASS | Definition: Exact ball/list equality reflection and contiguous three-segment reconstruction. |
| `BallChain.lean:77` | `ballsRev_of_segOk` | PASS | Exact ball/list equality reflection and contiguous three-segment reconstruction. |
| `BallChain.lean:89` | `balls_eq_of_segs` | PASS | Exact ball/list equality reflection and contiguous three-segment reconstruction. |
| `Core.lean:29` | `lock_core` | PASS | All four refined sites and scalar core checks supplied. |
| `CornerSplit.lean:33` | `signLists_two` | PASS | Exhaustive finite corner/row/column conjunction; no vertex dropped. |
| `CornerSplit.lean:37` | `rowCornerLeq_two` | PASS | Exhaustive finite corner/row/column conjunction; no vertex dropped. |
| `CornerSplit.lean:47` | `all_finRange_two` | PASS | Exhaustive finite corner/row/column conjunction; no vertex dropped. |
| `CornerSplit.lean:56` | `all_finRange_four` | PASS | Exhaustive finite corner/row/column conjunction; no vertex dropped. |
| `CornerSplit.lean:67` | `and_eq_true_of` | PASS | Exhaustive finite corner/row/column conjunction; no vertex dropped. |
| `DecSplit.lean:38` | `pieceAt` | PASS | Definition: Exact indexed partition and Option decode; monotone cuts and endpoint premises retained. |
| `DecSplit.lean:41` | `pieceAt_split` | PASS | Exact indexed partition and Option decode; monotone cuts and endpoint premises retained. |
| `DecSplit.lean:59` | `monoFrom` | PASS | Definition: Exact indexed partition and Option decode; monotone cuts and endpoint premises retained. |
| `DecSplit.lean:64` | `cutPairs` | PASS | Definition: Exact indexed partition and Option decode; monotone cuts and endpoint premises retained. |
| `DecSplit.lean:68` | `le_getLast_of_monoFrom` | PASS | Exact indexed partition and Option decode; monotone cuts and endpoint premises retained. |
| `DecSplit.lean:76` | `pieceAt_eq_flatten` | PASS | Exact indexed partition and Option decode; monotone cuts and endpoint premises retained. |
| `DecSplit.lean:89` | `filterMap_zip_range_eq_flatten` | PASS | Exact indexed partition and Option decode; monotone cuts and endpoint premises retained. |
| `DecSplit.lean:103` | `dyadicTerms_append` | PASS | Exact indexed partition and Option decode; monotone cuts and endpoint premises retained. |
| `DecSplit.lean:115` | `dyadicTerms_flatten` | PASS | Exact indexed partition and Option decode; monotone cuts and endpoint premises retained. |
| `DecSplit.lean:126` | `dyadicTerms_targetTerms_of_pieces` | PASS | Exact indexed partition and Option decode; monotone cuts and endpoint premises retained. |
| `DecSplit.lean:143` | `fst_targetPair` | PASS | Exact indexed partition and Option decode; monotone cuts and endpoint premises retained. |
| `EmbBridge.lean:27` | `checkEmbedding_of_parts` | PASS | All angle, action and derivative rows required by the landed checker. |
| `ErrRadiusTbl.lean:29` | `weightTermTbl` | PASS | Definition: Exact weight table and in-range degree checks exclude zero default. |
| `ErrRadiusTbl.lean:34` | `errRadiusTbl` | PASS | Definition: Exact weight table and in-range degree checks exclude zero default. |
| `ErrRadiusTbl.lean:37` | `errRadius_eq_tbl` | PASS | Exact weight table and in-range degree checks exclude zero default. |
| `ExpSplit.lean:27` | `expResidualUp_eq_of_parts` | PASS | Both scalar parts equal the landed residual formula. |
| `FallbackMul.lean:28` | `mulN_eq_of_polyProduct_none` | PASS | Failed packed product keeps full sound radius; model equality requires all fields. |
| `FallbackMul.lean:38` | `certModel_eq_of_parts` | PASS | Failed packed product keeps full sound radius; model equality requires all fields. |
| `Format.lean:32` | `lockPrecision` | PASS | Definition: Total literal codec; resulting certificate object is checked. |
| `Format.lean:35` | `LockBackend` | PASS | Definition: Total literal codec; resulting certificate object is checked. |
| `Format.lean:38` | `tm` | PASS | Definition: Total literal codec; resulting certificate object is checked. |
| `Format.lean:41` | `unzero` | PASS | Definition: Total literal codec; resulting certificate object is checked. |
| `Format.lean:47` | `natChunks` | PASS | Definition: Total literal codec; resulting certificate object is checked. |
| `Format.lean:50` | `ratOf` | PASS | Definition: Total literal codec; resulting certificate object is checked. |
| `Format.lean:52` | `unzero_test` | PASS | Total literal codec; resulting certificate object is checked. |
| `GraphChunk.lean:34` | `keyCmp_swap_lt` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:50` | `KeySep` | PASS | Definition: Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:52` | `mergeErrTerms_nil_right` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:56` | `mergeErrTerms_cons` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:60` | `mergeErrTerms_prefix_lt` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:73` | `mergeErrTerms_append_sep` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:115` | `mergeErrTerms_append_last` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:144` | `mergeErrTerms_single_lt` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:155` | `mergeErrTerms_single_stop` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:164` | `sumUp_flatten_of_maps` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:176` | `keyCmp_lt_trans` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:203` | `keyCmp_swap_gt` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:217` | `keySep_of_threshold` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:230` | `mergeErrTerms_append_run` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:243` | `mergeErrTerms_append_runK` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:254` | `mergeErrTerms_single_head` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:263` | `mergeErrTerms_single_lt'` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:269` | `truncPoly_of_all` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:274` | `map_truncErr_of_all` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:282` | `all_flatten_of` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:287` | `rowItems_append` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:291` | `toErrTerms_itemsPoly_map` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunk.lean:296` | `itemsPoly_map_toErr` | PASS | Exact merge/sum/truncation equations with checked separation/order premises. |
| `GraphChunkFixed.lean:29` | `ErrFree` | PASS | Definition: Zero addition-roundoff on CertFixed proved; errors not silently discarded. |
| `GraphChunkFixed.lean:31` | `ofInt_zero_fixed` | PASS | Zero addition-roundoff on CertFixed proved; errors not silently discarded. |
| `GraphChunkFixed.lean:35` | `weightTermUp_zero_fixed` | PASS | Zero addition-roundoff on CertFixed proved; errors not silently discarded. |
| `GraphChunkFixed.lean:41` | `sumPairsUp_zero_fixed` | PASS | Zero addition-roundoff on CertFixed proved; errors not silently discarded. |
| `GraphChunkFixed.lean:56` | `pairRounds_zero_fixed` | PASS | Zero addition-roundoff on CertFixed proved; errors not silently discarded. |
| `GraphChunkFixed.lean:61` | `foldr_upAdd_zero_fixed` | PASS | Zero addition-roundoff on CertFixed proved; errors not silently discarded. |
| `GraphChunkFixed.lean:69` | `errRadius_eq_zero` | PASS | Zero addition-roundoff on CertFixed proved; errors not silently discarded. |
| `GraphChunkFixed.lean:79` | `toErrTerms_errFree` | PASS | Zero addition-roundoff on CertFixed proved; errors not silently discarded. |
| `GraphChunkFixed.lean:84` | `mergeErrPair_errFree` | PASS | Zero addition-roundoff on CertFixed proved; errors not silently discarded. |
| `GraphChunkFixed.lean:92` | `mergeErrTerms_errFree` | PASS | Zero addition-roundoff on CertFixed proved; errors not silently discarded. |
| `GraphK.lean:29` | `checkSoGraphK` | PASS | Definition: Same four graph conclusions; only product keys parameterized. |
| `GraphK.lean:40` | `checkSoGraphK_sound` | PASS | Same four graph conclusions; only product keys parameterized. |
| `HamBridge.lean:28` | `checkHamBounds_of_parts` | PASS | Compiled jet, actual ball pass and complete bound check all required. |
| `HamBridge.lean:37` | `checkHamClaim_of_parts` | PASS | Compiled jet, actual ball pass and complete bound check all required. |
| `HamOk.lean:27` | `lock_hamBoundsOk` | PASS | Closed kernel-decided scalar checks on the certified literal ball state. |
| `HamOk.lean:31` | `lock_hamClaimOk` | PASS | Closed kernel-decided scalar checks on the certified literal ball state. |
| `Jet.lean:27` | `hamScale` | PASS | Definition: Literal expression/program/index data tied to actual compiler by JetEq. |
| `Jet.lean:30` | `lockHam` | PASS | Definition: Literal expression/program/index data tied to actual compiler by JetEq. |
| `Jet.lean:33` | `lockJetOps` | PASS | Definition: Literal expression/program/index data tied to actual compiler by JetEq. |
| `Jet.lean:36` | `lockJetLit` | PASS | Definition: Literal expression/program/index data tied to actual compiler by JetEq. |
| `JetEq.lean:26` | `lock_jet` | PASS | Kernel-decided compiler equality via reflected jet comparator. |
| `JetOps0.lean:23` | `jetOps0` | PASS | Definition: Literal program slice, included in the checked whole jet. |
| `JetOps1.lean:23` | `jetOps1` | PASS | Definition: Literal program slice, included in the checked whole jet. |
| `JetOps2.lean:23` | `jetOps2` | PASS | Definition: Literal program slice, included in the checked whole jet. |
| `LockGraphK.lean:37` | `lockBarrier_of_certifiedK` | PASS | Landed analytic barrier proof with keyed soundness substituted; no added headline premise. |
| `LockGraphK.lean:91` | `lockBarrier_of_certV2K` | PASS | Landed analytic barrier proof with keyed soundness substituted; no added headline premise. |
| `MemoBridge.lean:40` | `mul_mk_eq_of_polyProduct_cseg` | PASS | Restatement with field/cache equations; exact landed computation unchanged. |
| `MemoBridge.lean:51` | `composeStep_char_eq_of_cache_cseg` | PASS | Restatement with field/cache equations; exact landed computation unchanged. |
| `Num.lean:24` | `lockQ` | PASS | Definition: Actual refined numerical witness computation, not an assumed bound. |
| `PairCode.lean:23` | `pairsOf` | PASS | Definition: Total pair decoder; incomplete pair dropped, decoded advice still checked. |
| `PairCode.lean:27` | `pairsOf_test` | PASS | Total pair decoder; incomplete pair dropped, decoded advice still checked. |
| `Params.lean:24` | `rootLo` | PASS | Definition: Concrete rational candidates; positivity/enclosure/core checks supplied in chain. |
| `Params.lean:30` | `rootHi` | PASS | Definition: Concrete rational candidates; positivity/enclosure/core checks supplied in chain. |
| `Params.lean:37` | `freqCoeffs` | PASS | Definition: Concrete rational candidates; positivity/enclosure/core checks supplied in chain. |
| `Params.lean:41` | `freqBox` | PASS | Definition: Concrete rational candidates; positivity/enclosure/core checks supplied in chain. |
| `Params.lean:56` | `weight` | PASS | Definition: Concrete rational candidates; positivity/enclosure/core checks supplied in chain. |
| `Params.lean:62` | `params` | PASS | Definition: Concrete rational candidates; positivity/enclosure/core checks supplied in chain. |
| `Pass/Embedding.lean:34` | `lock_embedding` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/EmbeddingA0.lean:25` | `lock_embeddingA0` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/EmbeddingA1.lean:25` | `lock_embeddingA1` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/EmbeddingB0.lean:25` | `lock_embeddingB0` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/EmbeddingB1.lean:25` | `lock_embeddingB1` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/EmbeddingR0.lean:26` | `lock_embeddingR0` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/EmbeddingR1.lean:26` | `lock_embeddingR1` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/EmbeddingR2.lean:26` | `lock_embeddingR2` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/EmbeddingR3.lean:26` | `lock_embeddingR3` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/FrameL.lean:26` | `lock_frameL` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/FrameL0.lean:27` | `lock_frameL0` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/FrameL1.lean:27` | `lock_frameL1` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/FrameOm.lean:25` | `lock_frameOm` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/GraphH.lean:41` | `lock_graphHSq` | PASS | Closed graph check/equality; preserves the keyed SOS computation. |
| `Pass/GraphH.lean:49` | `lock_graphH` | PASS | Closed graph check/equality; preserves the keyed SOS computation. |
| `Pass/GraphL.lean:41` | `lock_graphLSq` | PASS | Closed graph check/equality; preserves the keyed SOS computation. |
| `Pass/GraphL.lean:49` | `lock_graphL` | PASS | Closed graph check/equality; preserves the keyed SOS computation. |
| `Pass/GraphM.lean:27` | `lock_graphM` | PASS | Closed graph check/equality; preserves the keyed SOS computation. |
| `Pass/GraphS.lean:25` | `lock_graphS` | PASS | Closed graph check/equality; preserves the keyed SOS computation. |
| `Pass/HamBounds.lean:30` | `lock_hamBounds` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/HamClaim.lean:30` | `lock_hamClaim` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Pass/Static.lean:25` | `lock_static` | PASS | Closed landed sub-check, or exact assembly of every required finite row. |
| `Passes.lean:48` | `lock_sqrtFive_mem` | PASS | All landed base/refined/frame and all four graph conjuncts assembled. |
| `Passes.lean:61` | `lock_freq` | PASS | All landed base/refined/frame and all four graph conjuncts assembled. |
| `Passes.lean:66` | `lock_frame` | PASS | All landed base/refined/frame and all four graph conjuncts assembled. |
| `Passes.lean:71` | `lock_passes` | PASS | All landed base/refined/frame and all four graph conjuncts assembled. |
| `Passes.lean:79` | `lockGraph_passes` | PASS | All landed base/refined/frame and all four graph conjuncts assembled. |
| `RealLowerK.lean:33` | `realLowerModelK` | PASS | Definition: Key-parameterized SOS model/check; lawful enclosure soundness retains exact error terms. |
| `RealLowerK.lean:47` | `checkRealLowerBoundK` | PASS | Definition: Key-parameterized SOS model/check; lawful enclosure soundness retains exact error terms. |
| `RealLowerK.lean:53` | `adviceLookup_append_of_isSome` | PASS | Key-parameterized SOS model/check; lawful enclosure soundness retains exact error terms. |
| `RealLowerK.lean:62` | `polyProduct_append_of_isSome` | PASS | Key-parameterized SOS model/check; lawful enclosure soundness retains exact error terms. |
| `RealLowerK.lean:70` | `checkRealLowerBoundK_sound` | PASS | Key-parameterized SOS model/check; lawful enclosure soundness retains exact error terms. |
| `RealLowerKSq.lean:30` | `realLowerModelKOf` | PASS | Definition: Exact model/product equalities tie all supplied memo parts to the keyed checker. |
| `RealLowerKSq.lean:47` | `realLowerModelK_eq_of_sq` | PASS | Exact model/product equalities tie all supplied memo parts to the keyed checker. |
| `RealLowerKSq.lean:58` | `checkRealLowerBoundK_of_sq` | PASS | Exact model/product equalities tie all supplied memo parts to the keyed checker. |
| `RealLowerKSq.lean:72` | `sqModelOf` | PASS | Definition: Exact model/product equalities tie all supplied memo parts to the keyed checker. |
| `RealLowerKSq.lean:84` | `realLowerModelKParts` | PASS | Definition: Exact model/product equalities tie all supplied memo parts to the keyed checker. |
| `RealLowerKSq.lean:91` | `realLowerModelK_eq_parts` | PASS | Exact model/product equalities tie all supplied memo parts to the keyed checker. |
| `RealLowerKSq.lean:106` | `checkRealLowerBoundK_of_parts` | PASS | Exact model/product equalities tie all supplied memo parts to the keyed checker. |
| `RemSplit.lean:36` | `natOfChunks` | PASS | Definition: Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:39` | `foldr_max_le_iff` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:44` | `packRangeMax_le_iff` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:65` | `packRangeMax_split` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:84` | `packRangeSum_split` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:89` | `packRangeMax_zero_size` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:92` | `packRangeSum_zero_size` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:97` | `packRangeMax_eq_cuts` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:114` | `packRangeSum_eq_cuts` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:129` | `sum_map_eq_of_forall₂` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:136` | `foldr_max_map_eq_of_forall₂` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:145` | `maxSlotDeg_eq_of_cuts` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `RemSplit.lean:157` | `remainderBound_eq_of_cuts` | PASS | Exact max/sum/remainder identities for arbitrary fuel, with full cut coverage. |
| `SegGraph.lean:39` | `levelNCseg` | PASS | Definition: Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:43` | `levelNCseg_nil` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:48` | `mergeRowsTree_succ_cseg` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:55` | `mergeRowsTree_add_cseg` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:61` | `mergeRowsLevel_append_cseg` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:70` | `length_mergeRowsLevel_cseg` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:79` | `levelNCseg_append` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:92` | `levelNCseg_flatten` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:106` | `adviceLookup_append_cseg` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:116` | `realLowerModel_eq_of_sq_cseg` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:134` | `etF` | PASS | Definition: Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:139` | `errTermsBeqCseg` | PASS | Definition: Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:145` | `eq_of_errTermsBeqCseg` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:156` | `eq_singleton_of_beq_cseg` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegGraph.lean:170` | `flatten_groups_cseg` | PASS | Exact balanced-merge regrouping and error-term equality reflection. |
| `SegRoutes.lean:40` | `CertModel.mul_eq_of_polyProduct` | PASS | Exact landed exp/inv/sqrt/mul equations; lookup/radius premises explicit. |
| `SegRoutes.lean:51` | `composeStep_exp_eq` | PASS | Exact landed exp/inv/sqrt/mul equations; lookup/radius premises explicit. |
| `SegRoutes.lean:61` | `composeStep_inv_eq` | PASS | Exact landed exp/inv/sqrt/mul equations; lookup/radius premises explicit. |
| `SegRoutes.lean:70` | `composeStep_sqrt_eq` | PASS | Exact landed exp/inv/sqrt/mul equations; lookup/radius premises explicit. |
| `SegRoutes.lean:80` | `invWitnessRadius_eq_of_delta` | PASS | Exact landed exp/inv/sqrt/mul equations; lookup/radius premises explicit. |
| `SegRoutes.lean:90` | `sqrtWitnessRadius_eq_of_residual` | PASS | Exact landed exp/inv/sqrt/mul equations; lookup/radius premises explicit. |
| `SegRoutesProbe.lean:29` | `sqrtToyW` | PASS | Definition: Explicit exact-rational toy only; not used as a lunar result. |
| `SegRoutesProbe.lean:30` | `sqrtToyPi` | PASS | Definition: Explicit exact-rational toy only; not used as a lunar result. |
| `SegRoutesProbe.lean:31` | `sqrtToyCfg` | PASS | Definition: Explicit exact-rational toy only; not used as a lunar result. |
| `SegRoutesProbe.lean:32` | `sqrtToyCos` | PASS | Definition: Explicit exact-rational toy only; not used as a lunar result. |
| `SegRoutesProbe.lean:33` | `sqrtToyK` | PASS | Definition: Explicit exact-rational toy only; not used as a lunar result. |
| `SegRoutesProbe.lean:34` | `sqrtTestWit` | PASS | Definition: Explicit exact-rational toy only; not used as a lunar result. |
| `SegRoutesProbe.lean:37` | `probeSt` | PASS | Definition: Explicit exact-rational toy only; not used as a lunar result. |
| `SegRoutesProbe.lean:41` | `probeQ` | PASS | Definition: Explicit exact-rational toy only; not used as a lunar result. |
| `SegRoutesProbe.lean:44` | `probeWit` | PASS | Definition: Explicit exact-rational toy only; not used as a lunar result. |
| `SegRoutesProbe.lean:46` | `probe_inv` | PASS | Explicit exact-rational toy only; not used as a lunar result. |
| `SegRoutesProbe.lean:58` | `probe_sqrt` | PASS | Explicit exact-rational toy only; not used as a lunar result. |
| `SegSupport.lean:43` | `mul_eq_of_polyProduct_cseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:55` | `eq_some_of_termsBeq_cseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:63` | `matMulEntry_one_cseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:69` | `matMulEntry_two_cseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:77` | `matMulEntry_four_cseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:87` | `gramEntryModel_two_cseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:98` | `gramBGModel_two_cseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:107` | `dyadicTerms_nil_cseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:112` | `eq_some_getD_cseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:123` | `rowBeqCseg` | PASS | Definition: Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:129` | `matBeqCseg` | PASS | Definition: Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:134` | `eq_of_rowBeqCseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:142` | `eq_of_matBeqCseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `SegSupport.lean:151` | `eq_some_pair_cseg` | PASS | Computational equations and comparator reflection; no analytic assumption. |
| `Site0B.lean:23` | `lock_site_b0` | PASS | Closed kernel-decided bite at the named refined site; no bound assumed. |
| `Site0D.lean:23` | `lock_site_d0` | PASS | Closed kernel-decided bite at the named refined site; no bound assumed. |
| `Site1B.lean:23` | `lock_site_b1` | PASS | Closed kernel-decided bite at the named refined site; no bound assumed. |
| `Site1D.lean:23` | `lock_site_d1` | PASS | Closed kernel-decided bite at the named refined site; no bound assumed. |
| `Site2B.lean:23` | `lock_site_b2` | PASS | Closed kernel-decided bite at the named refined site; no bound assumed. |
| `Site3B.lean:23` | `lock_site_b3` | PASS | Closed kernel-decided bite at the named refined site; no bound assumed. |
| `ZCode.lean:28` | `zvar` | PASS | Definition: Total bounded varint/zigzag/chunk decoder; checked decoded object is authoritative. |
| `ZCode.lean:35` | `unzig` | PASS | Definition: Total bounded varint/zigzag/chunk decoder; checked decoded object is authoritative. |
| `ZCode.lean:38` | `zdec` | PASS | Definition: Total bounded varint/zigzag/chunk decoder; checked decoded object is authoritative. |
| `ZCode.lean:43` | `zjoin` | PASS | Definition: Total bounded varint/zigzag/chunk decoder; checked decoded object is authoritative. |
| `ZCode.lean:47` | `zdecs` | PASS | Definition: Total bounded varint/zigzag/chunk decoder; checked decoded object is authoritative. |
| `ZCode.lean:49` | `zdec_test` | PASS | Total bounded varint/zigzag/chunk decoder; checked decoded object is authoritative. |
| `ZCode.lean:51` | `zdecs_test` | PASS | Total bounded varint/zigzag/chunk decoder; checked decoded object is authoritative. |
| `ZCodeX.lean:34` | `zkey` | PASS | Definition: XOR byte decoder; reversible data transform is supplementary to actual kernel checks. |
| `ZCodeX.lean:38` | `zvarX` | PASS | Definition: XOR byte decoder; reversible data transform is supplementary to actual kernel checks. |
| `ZCodeX.lean:48` | `zdecX` | PASS | Definition: XOR byte decoder; reversible data transform is supplementary to actual kernel checks. |
| `ZCodeX.lean:55` | `zdecsXAux` | PASS | Definition: XOR byte decoder; reversible data transform is supplementary to actual kernel checks. |
| `ZCodeX.lean:60` | `zdecsX` | PASS | Definition: XOR byte decoder; reversible data transform is supplementary to actual kernel checks. |
| `ZCodeX.lean:63` | `zdecsX_test` | PASS | XOR byte decoder; reversible data transform is supplementary to actual kernel checks. |
| `ZRows.lean:26` | `tmsOf` | PASS | Definition: Four-entry row decoder; trailing incomplete row discarded explicitly. |
| `ZRows.lean:30` | `tmsOf_test` | PASS | Four-entry row decoder; trailing incomplete row discarded explicitly. |
| `SegDecide.lean:26` | derived `instDecidableEqSlpOp` | PASS WITH NOTES | Structural decidable equality; disclosed orphan instance. |
| `SegDecide.lean:28` | anonymous list-equality example | PASS | Closed `decide +kernel`; no analytic conclusion. |

| Generated node | Declarations / content | Verdict | Reason / scope |
|---|---|---|---|
| Certificate/data | `base`, `graph`, `cert`, configurations, witness, embeddings, inverse/SOS polynomials | PASS | Untrusted literal objects; full checker and enclosure conclusions consumed. |
| Composition | `lockFullCkpt_segs_length`, `lock_fullPlan`, `lock_fullSegs`, low analogues, `lockLowCkpt.compose_eq` | PASS | 187/386 segments tied to full lists and every finite index; landed checkpoint bridges used. |
| Products | `Seg/Prod/M*` shard, decode, side-check and assembly theorems | PASS WITH NOTES | Exact landed product-check equations; every side check separate. Entire closure build is current; local kernel replay is selective. |
| Ledgers/memos | `Seg/Ledger*`, `Seg/Memo*`, radix/memo literals | PASS | Objects tied to actual products/states by equations; not trusted enclosures. |
| Energy/invariance | `lock_csEnergy`, `lock_csInvariance`, `lock_energyTail`, `lock_invRow0`–`3` | PASS | Actual full program, energy tail and all four rows required. |
| Gram/torsion | `lock_gramCheck`, `lock_csGram`, `lock_torsionModels`, `lock_csTorsion` | PASS | Actual low stages and matrix-entry equations feed the original checkers. |
| Frame N/T | `lock_csFrameN`, `lock_csFrameT`, per-row/column/vertex checks | PASS | Four sign vertices; four N rows, two N columns, two T rows. No reduced corner set. |
| Graph chunks | `GraphK/*`, `lock_gkLOut`, `lock_gkHOut`, range/chunk checks | PASS | Checked products, sorted/separated merges and full sup-bound computations feed `lock_graphL/H`. |
| Ball pass | `HamBalls`, `Ck*` and ball segment checks | PASS | Three contiguous segments equal the compiled program pass; literal compiler bridge retained. |

The exact frozen-type/seal probe passed (exit 0). To avoid a new module search prefix shadowing `KAM`, the final probe imports the four built frozen theorem modules and AssemblyN65 through the normal Lake path, then inserts the prepared FrozenBridge and three provider public sections verbatim from lockfreeze 41934621. It therefore elaborates the actual prepared proof text, with its original namespaces and declarations, without writing a production bridge/provider file. Direct examples check each of the three provider exports against `type_of% @KAM.SpinOrbit.<frozen export>`. Fresh copies of all four frozen telescopes test the prescribed seal bodies; the headline candidate is also applied with exactly `q₀ p₀ φ₀ h₀`, in order. The decisive candidate body is:

```lean
by
  rw [Lock.frozen_libAction_eq, Lock.frozen_lunarSyncOrbit_eq] at h₀
  rw [Lock.frozen_lunarSyncOrbit_eq]
  exact KAM.SpinOrbit.Data.LockN65.lunar_sync_lock_N65 q₀ p₀ φ₀ h₀
```

The second headline copy has the unchanged frozen telescope and body
`by exact LockDataAudit1.lunar_sync_lock q₀ p₀ φ₀ h₀`.
The frozen `soField` is the same constant throughout. No equality rewrite replaces the vector field.
The three other fresh seal bodies are exactly the respective provider export, `… ψ h`, and `… φ`.

Commands were run from `/root/code/KAM-inp-lockdata`, with `LEAN_NUM_THREADS=1`, one Lean/Lake/checker job at a time, under the shared kernel-probe lock. Each job was capped by `systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 nice -n 5`. Targeted builds used the compile gate; no heavy data theorem was rebuilt. The successful leaf build command was:

```sh
export LEAN_NUM_THREADS=1
systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 nice -n 5 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-lockdata KAM.SpinOrbit.Data.LockN65.AssemblyN65
```

Exit 0; final output: `Build completed successfully (17247 jobs).` It was preceded by the same capped `lake build --no-build KAM.SpinOrbit.Data.LockN65.AssemblyN65`, exit 0, same 17,247-job completion. Replayed linter warnings in dependency traces are warnings, not new proof failures. The gate acquired a slot; no build from scratch, cache operation, root regeneration or application-root build was run.

The same capped/gated driver built, individually and serially, frozen definitions `IsSyncOrbit`, `LunarSyncOrbit`, `LibAction`, `LunarOmega`, and frozen theorem modules `LunarSyncLock`, `LunarSyncOrbitSpec`, `LunarSyncOrbitUnique`, `LunarSyncOrbitBound`: all exit 0. Their manifest-bound `sorry` bodies were left unchanged; their types are used only as type references, not as proof suppliers. Three further light targets, `KAM.Frozen.SpinOrbit.Defs.LunarPLo`, `…Defs.LunarPHi`, `…Theorems.LunarWindow`, also exited 0 to fill the unrelated baseline ABI import gap.

For the final Lean probes and every successful checker invocation, the environment was:

```sh
export LEAN_NUM_THREADS=1
export LEAN_PATH="$(lake env printenv LEAN_PATH):/mnt/HC_Volume_106379410/kam-data/so-lock/remote-20261105/lock/lib/lean"
```

The environment query itself was run capped at nice 5 while holding the shared lock. The returned data directory was last, as required. There was no scratch KAM prefix in the successful checks. The exact binary was `/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, invoked on the temporary `SealFitInline.lean` and `Axioms.lean` inside `.lake/abi-scratch/LockDataAudit1/`. Both exited 0. The latter imports every tracked declaration-bearing module and prints every one of the 165 named theorem axiom lists, plus the derived equality instance. Every printed axiom set is a subset of `{propext, Classical.choice, Quot.sound}`; there is no `sorryAx`. Full successful output is retained below.

Initial scratch attempts with a partial scratch `KAM/` directory prepended to LEAN_PATH failed on missing `.olean` paths inside that directory, before checking the requested declarations. The corresponding unsuccessful checker loop was stopped. These are auditor import-path errors, superseded by the successful normal-path runs, not package counterexamples. No resource limit was raised to resolve them.

The full command `sh scripts/lint_sources.sh` ran to completion, exit 1. Its complete output is reproduced below. The module check and frozen-anchor guard passed. The root-parts finding is the expected generated-root staleness; it was not repaired. Its final ABI import error named missing `LunarPHi.olean`, not a type/hash mismatch. After the three light builds above, the isolated ABI recheck
`python3 -I scripts/abi_hashes.py /root/code/KAM-inp-lockdata manifest/frozen-anchors.json --check`
exited 0, with the exact output reproduced below. The expensive full lint script was not rerun, so this report does not describe that original exit code as green. Its only remaining substantive finding is generated-root staleness; the ABI gap was separately resolved and checked.

The independent dereferenced-source scan included every generated symlink target, unlike checks that enumerate only regular files. Results: 13,668 files; forbidden proof escapes/resource overrides: 0; module-format failures: 0; files over 1,500 lines: 0; non-import/URL lines over 100 Unicode characters: 0. Maximum file length: 1,461 lines (`Seg/Prod/M940ShOpsD01.lean`); maximum line width: 100. A separate `rg --follow` search for `native_decide`, `sorryAx`, `ofReduceBool`, `ofReduceNat`, `skipKernelTC`, declaration injection, runtime elaboration and `decide +native` had no matches. No `EuclideanSpace`, new analytic axiom, or resource override is present.

The Python comparison of all 2,003 files containing actual whitened row literals compared 2,210,596 row decodes and found no mismatch and no missing predecessor. The comparison used the source `lock_zx.py` mirrors `zdecx_row` and `zdec_row`, pairing the current literal blocks with the corresponding pre-whitening originals in `lean/{segd55z2,graphk3,dk,sosk,src,src_d}`. `AdvLow113` initially selected the historical `src_d` version (1,301 rows), which has a different chunk layout; the corresponding `src/AdvLow113.lean` has the same 44 rows and matches exactly. This is supplementary Python evidence, not a kernel theorem equating all codec inputs. There is no universal codec-equivalence lemma in the package; kernel soundness uses the actual decoded objects and their checked properties, so it does not assume that supplemental comparison.

A tooling documentation defect was independently verified: `docs/tracks/SO/audits/LOCK-DATA-handoff.md:201` says “`lake env leanchecker <Module>` replays only the listed modules' declarations.” In this toolchain that is false for names with descendants. `/root/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/LeanChecker.lean:109` selects `target.isPrefixOf m` whenever `--fresh` is absent; its own documentation at line 135 says “starting with”. Listing ONE module therefore does not ensure a single-module replay. The initial extra `GraphK` invocation expanded to its data descendants and was stopped without claiming success or a package counterexample. No resource budget was increased. Final successful checker invocations are leaf module names, and their complete logs each show exactly one module.

For `GraphK` and `Seg.Checks`, which have descendant modules, I instead copied the exact source bytes to `GraphKExact.lean` / `SegChecksExact.lean` inside the ABI scratch directory and ran the same capped, locked Lean binary with `-R <scratch-directory> <copy>`. Both exact-source elaborations exited 0 with no output; they re-elaborate and kernel-check those sources against the normal imported environment. These are source elaboration checks, not claims that the original module-only leanchecker command succeeded. The successful artifact-replay table intentionally excludes both prefix targets. This corrects the audit method without changing production code.

Suspected pinned-source or mathematical blueprint defects: none found in this delta. The historical candidate discussion in SO-LOCK-DESIGN uses earlier numerical sizes/window estimates, explicitly marked provisional; the current rational checks, actual certificate and unchanged frozen telescope control this result. Preserved package deviations are the lower graph window `13155/1000000`, separately keyed SOS copies, untracked external data links, and the orphan instance. This auditor introduced no mathematical deviation. The temporary import-path correction above changes only the audit setup.

Two handoff evidence-count notes should not be mistaken for mathematical findings: §5 says a 627-module sample, but its quoted 621 local plus 8 heavy entries sum to 629; this report does not certify that aggregate. It also mentions 29 modules outside the assembly closure and 26 quarantined stale hubs; the actual materialized source tree here has exactly 3 outside the closure. The fingerprint and the explicit local replay table fix the scope audited here independently of those historical counts.

The remaining production work is the authorized Phase B installation of the demonstrated headline provider, normal frozen-anchor seal operations, and orchestrator root regeneration. Phase B must also apply D51 application ownership to the headline provider and frozen anchor: the current `scripts/build_roots.json` assigns only `KAM.SpinOrbit.Data.LockN65` to KAMLunarLock, while the empty headline stub is currently core. Filling that stub with an AssemblyN65 import without updating ownership would introduce a forbidden core-to-application edge. No such edge exists in this audited delta. This is an integration requirement for Phase B, not a current mathematical failure. This report does not perform those operations or mark any DRAFT_SORRY anchor SEALED. The three prepared orbit providers have their exact frozen types; the headline bridge proof and its seal application have been checked without changing a frozen statement.

Final read-only snapshot checks confirmed that all four prepared bridge/provider source files are byte-identical to `git show 41934621:<path>`, that the dereferenced 13,668-file fingerprint above is unchanged, that `git status --porcelain --untracked-files=no` is empty, and that the protected-path branch diff is still empty.

Successful kernel replay commands used the capped/locked environment described above and the exact binary `/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanchecker --verbose <module>`. Each invocation listed ONE module, as required by the handoff, rather than the generic brief's multi-module invocation. The following are all the locally replayed modules; each successful log contains exactly the shown `replaying` line and no diagnostic. This validates the named module bodies, not every imported body.

| Module (prefix `KAM.SpinOrbit.Data.LockN65.`) | Exit | Complete checker output |
|---|---|---|
| `CornerSplit` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.CornerSplit` |
| `ZCodeX` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.ZCodeX` |
| `LockGraphK` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.LockGraphK` |
| `Passes` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.Passes` |
| `AssemblyN65` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.AssemblyN65` |
| `RealLowerK` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.RealLowerK` |
| `DecSplit` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.DecSplit` |
| `RemSplit` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.RemSplit` |
| `MemoBridge` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.MemoBridge` |
| `AdvLookupSub` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.AdvLookupSub` |
| `SegRoutes` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.SegRoutes` |
| `GraphChunk` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.GraphChunk` |
| `GraphChunkFixed` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.GraphChunkFixed` |
| `Seg.Chain` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.Seg.Chain` |
| `Seg.Checks.FrameN` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.Seg.Checks.FrameN` |
| `Seg.Checks.FrameT` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.Seg.Checks.FrameT` |
| `Seg.Checks.Torsion` | 0 | `replaying KAM.SpinOrbit.Data.LockN65.Seg.Checks.Torsion` |

Complete final seal-fit axiom output (the type examples and seal-copy elaborations produced no errors):

```text
'LockDataAudit1.lunar_sync_lock' depends on axioms: [propext, Classical.choice, Quot.sound]
'LockDataAudit1.lunarSyncOrbit_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'LockDataAudit1.lunarSyncOrbit_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'LockDataAudit1.lunarSyncOrbit_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.SpinOrbit.lunarSyncOrbit_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.SpinOrbit.lunarSyncOrbit_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.SpinOrbit.lunarSyncOrbit_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'LockDataAudit1.lunar_sync_lock_seal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Complete tracked-theorem and equality-instance axiom output:

```text
'KAM.SpinOrbit.Data.LockN65.adviceLookup_skip_cseg' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.adviceLookup_at_cseg' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_advLow_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_advFull_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.adviceLookup_subAdvice_cseg' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.adviceLookup_forWitness_cseg' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_literalCheck65' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_dio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_barrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lunar_sync_lock_N65' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.eq_of_ballBeq' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.eq_of_ballsBeq' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.ballsRev_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.ballsRev_of_segOk' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.balls_eq_of_segs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.signLists_two' does not depend on any axioms
'KAM.SpinOrbit.Data.LockN65.rowCornerLeq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.all_finRange_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.all_finRange_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.and_eq_true_of' does not depend on any axioms
'KAM.SpinOrbit.Data.LockN65.pieceAt_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.le_getLast_of_monoFrom' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.pieceAt_eq_flatten' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.filterMap_zip_range_eq_flatten' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.dyadicTerms_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.dyadicTerms_flatten' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.dyadicTerms_targetTerms_of_pieces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.SpinOrbit.Data.LockN65.fst_targetPair' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.checkEmbedding_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.errRadius_eq_tbl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.expResidualUp_eq_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mulN_eq_of_polyProduct_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.certModel_eq_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.unzero_test' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.keyCmp_swap_lt' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_nil_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_prefix_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_append_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_append_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_single_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_single_stop' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.sumUp_flatten_of_maps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.keyCmp_lt_trans' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.keyCmp_swap_gt' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.keySep_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_append_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_append_runK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_single_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_single_lt'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.truncPoly_of_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.map_truncErr_of_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.all_flatten_of' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.rowItems_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.toErrTerms_itemsPoly_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.itemsPoly_map_toErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.ofInt_zero_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.weightTermUp_zero_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.sumPairsUp_zero_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.pairRounds_zero_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.foldr_upAdd_zero_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.errRadius_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.toErrTerms_errFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrPair_errFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeErrTerms_errFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.checkSoGraphK_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.checkHamBounds_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.checkHamClaim_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_hamBoundsOk' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_hamClaimOk' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lockBarrier_of_certifiedK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lockBarrier_of_certV2K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mul_mk_eq_of_polyProduct_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.composeStep_char_eq_of_cache_cseg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.SpinOrbit.Data.LockN65.pairsOf_test' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.lock_embedding' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_embeddingA0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_embeddingA1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_embeddingB0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_embeddingB1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_embeddingR0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_embeddingR1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_embeddingR2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_embeddingR3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_frameL' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_frameL0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_frameL1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_frameOm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_graphHSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_graphH' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_graphLSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_graphL' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_graphM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_graphS' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_hamBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_hamClaim' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_static' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_sqrtFive_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_passes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lockGraph_passes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.adviceLookup_append_of_isSome' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.polyProduct_append_of_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.checkRealLowerBoundK_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.realLowerModelK_eq_of_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.checkRealLowerBoundK_of_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.realLowerModelK_eq_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.checkRealLowerBoundK_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.foldr_max_le_iff' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.packRangeMax_le_iff' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.packRangeMax_split' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.packRangeSum_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.packRangeMax_zero_size' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.packRangeSum_zero_size' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.packRangeMax_eq_cuts' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.packRangeSum_eq_cuts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.sum_map_eq_of_forall₂' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.foldr_max_map_eq_of_forall₂' does not depend on any axioms
'KAM.SpinOrbit.Data.LockN65.maxSlotDeg_eq_of_cuts' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.remainderBound_eq_of_cuts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.levelNCseg_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeRowsTree_succ_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeRowsTree_add_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mergeRowsLevel_append_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.length_mergeRowsLevel_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.levelNCseg_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.levelNCseg_flatten' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.adviceLookup_append_cseg' depends on axioms: [propext, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.realLowerModel_eq_of_sq_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.eq_of_errTermsBeqCseg' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.eq_singleton_of_beq_cseg' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.flatten_groups_cseg' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.CertModel.mul_eq_of_polyProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.composeStep_exp_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.composeStep_inv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.composeStep_sqrt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.invWitnessRadius_eq_of_delta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.sqrtWitnessRadius_eq_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.probe_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.probe_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.mul_eq_of_polyProduct_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.eq_some_of_termsBeq_cseg' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.matMulEntry_one_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.matMulEntry_two_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.matMulEntry_four_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.gramEntryModel_two_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.gramBGModel_two_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.dyadicTerms_nil_cseg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.eq_some_getD_cseg' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.eq_of_rowBeqCseg' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.eq_of_matBeqCseg' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.eq_some_pair_cseg' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.lock_site_b0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_site_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_site_b1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_site_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_site_b2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.lock_site_b3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Data.LockN65.zdec_test' does not depend on any axioms
'KAM.SpinOrbit.Data.LockN65.zdecs_test' does not depend on any axioms
'KAM.SpinOrbit.Data.LockN65.zdecsX_test' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.tmsOf_test' depends on axioms: [propext]
'KAM.SpinOrbit.Data.LockN65.instDecidableEqSlpOp' does not depend on any axioms
```

Complete original lint output (exit 1):

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAMLunarLock/SpinOrbit/Data/LockN65/DK.lean, KAMLunarLock/SpinOrbit/Data/LockN65/GraphK.lean, KAMLunarLock/SpinOrbit/Data/LockN65/Pass.lean, KAMLunarLock/SpinOrbit/Data/LockN65/Seg/Checks.lean, KAMLunarLock/SpinOrbit/Data/LockN65/Seg/Full.lean, KAMLunarLock/SpinOrbit/Data/LockN65/Seg/Gram.lean, KAMLunarLock/SpinOrbit/Data/LockN65/Seg/Low.lean, KAMLunarLock/SpinOrbit/Data/LockN65/Seg/Prod/Top.lean, KAMLunarLock/SpinOrbit/Data/LockN65/Seg/Rad.lean, KAMLunarLock/SpinOrbit/Data/LockN65/Seg/Top.lean, KAMLunarLock/SpinOrbit/Data/LockN65/Seg/Tors.lean, KAMLunarLock/SpinOrbit/Data/LockN65/Top.lean, KAMLunarLock.lean)
check_lean_modules: PASS (3648 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
/root/code/KAM-inp-lockdata/.lake/abi-scratch/tmp70ywkxxs.lean:1:0: error: object file '/root/code/KAM-inp-lockdata/.lake/build/lib/lean/KAM/Frozen/SpinOrbit/Defs/LunarPHi.olean' of module KAM.Frozen.SpinOrbit.Defs.LunarPHi does not exist
```

Complete successful isolated ABI recheck output (exit 0):

```text
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

Check execution record (UTC; the original lint ABI gap and the superseded scratch-path attempt are explained above):

```text
LOCK ACQUIRED 2026-11-05T00:56:18Z
START preflight 2026-11-05T00:56:18Z
END preflight rc=0 2026-11-05T00:58:08Z
START build 2026-11-05T00:58:08Z
END build rc=0 2026-11-05T00:58:34Z
START build-IsSyncOrbit 2026-11-05T00:58:34Z
END build-IsSyncOrbit rc=0 2026-11-05T00:58:41Z
START build-LunarSyncOrbit 2026-11-05T00:58:41Z
END build-LunarSyncOrbit rc=0 2026-11-05T00:58:46Z
START build-LibAction 2026-11-05T00:58:46Z
END build-LibAction rc=0 2026-11-05T00:58:51Z
START build-LunarOmega 2026-11-05T00:58:51Z
END build-LunarOmega rc=0 2026-11-05T00:58:54Z
START lint 2026-11-05T00:58:54Z
END lint rc=1 2026-11-05T01:11:31Z
START build-LunarPLo 2026-11-05T01:14:34Z
END build-LunarPLo rc=0 2026-11-05T01:14:36Z
START build-LunarPHi 2026-11-05T01:14:36Z
END build-LunarPHi rc=0 2026-11-05T01:14:38Z
START build-LunarWindow 2026-11-05T01:14:38Z
END build-LunarWindow rc=0 2026-11-05T01:14:40Z
START abi-final 2026-11-05T01:14:40Z
END abi-final rc=0 2026-11-05T01:14:51Z
START sealfit-final 2026-11-05T01:14:52Z
END sealfit-final rc=0 2026-11-05T01:14:58Z
START axioms-final 2026-11-05T01:14:58Z
END axioms-final rc=0 2026-11-05T01:15:01Z
START replay-final-CornerSplit 2026-11-05T01:15:01Z
END replay-final-CornerSplit rc=0 2026-11-05T01:15:25Z
START replay-final-ZCodeX 2026-11-05T01:15:25Z
END replay-final-ZCodeX rc=0 2026-11-05T01:15:48Z
START replay-final-LockGraphK 2026-11-05T01:15:48Z
END replay-final-LockGraphK rc=0 2026-11-05T01:16:12Z
START replay-final-Passes 2026-11-05T01:16:12Z
END replay-final-Passes rc=0 2026-11-05T01:16:49Z
START replay-final-AssemblyN65 2026-11-05T01:16:49Z
END replay-final-AssemblyN65 rc=0 2026-11-05T01:17:20Z
START replay-final-RealLowerK 2026-11-05T01:17:20Z
END replay-final-RealLowerK rc=0 2026-11-05T01:17:44Z
START replay-final-GraphK 2026-11-05T01:17:44Z
START exact-GraphK 2026-11-05T01:21:44Z
END exact-GraphK rc=0 2026-11-05T01:21:46Z
START exact-SegChecks 2026-11-05T01:21:46Z
END exact-SegChecks rc=0 2026-11-05T01:21:50Z
START replay-final-DecSplit 2026-11-05T01:21:50Z
END replay-final-DecSplit rc=0 2026-11-05T01:22:14Z
START replay-final-RemSplit 2026-11-05T01:22:14Z
END replay-final-RemSplit rc=0 2026-11-05T01:22:38Z
START replay-final-MemoBridge 2026-11-05T01:22:38Z
END replay-final-MemoBridge rc=0 2026-11-05T01:23:03Z
START replay-final-AdvLookupSub 2026-11-05T01:23:03Z
END replay-final-AdvLookupSub rc=0 2026-11-05T01:23:27Z
START replay-final-SegRoutes 2026-11-05T01:23:27Z
END replay-final-SegRoutes rc=0 2026-11-05T01:23:51Z
START replay-final-GraphChunk 2026-11-05T01:23:51Z
END replay-final-GraphChunk rc=0 2026-11-05T01:24:15Z
START replay-final-GraphChunkFixed 2026-11-05T01:24:15Z
END replay-final-GraphChunkFixed rc=0 2026-11-05T01:24:39Z
START replay-final-Seg.Chain 2026-11-05T01:24:39Z
END replay-final-Seg.Chain rc=0 2026-11-05T01:25:31Z
START replay-final-Seg.Checks.FrameN 2026-11-05T01:25:31Z
END replay-final-Seg.Checks.FrameN rc=0 2026-11-05T01:26:01Z
START replay-final-Seg.Checks.FrameT 2026-11-05T01:26:01Z
END replay-final-Seg.Checks.FrameT rc=0 2026-11-05T01:26:32Z
START replay-final-Seg.Checks.Torsion 2026-11-05T01:26:32Z
END replay-final-Seg.Checks.Torsion rc=0 2026-11-05T01:27:30Z
```

All auditor-created probe files and scripts under `.lake/abi-scratch/LockDataAudit1/` were removed after these outputs were incorporated. The report is the sole repository-source artifact created by this audit. No commit or other state-changing git command was used.

