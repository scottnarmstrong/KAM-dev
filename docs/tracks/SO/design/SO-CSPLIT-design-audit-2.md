# SO-CSPLIT revision 1: independent delta design audit 2

**Overall verdict: FAIL.** The new signature artifact elaborates, and audit 1's product and one-op contract defects are repaired. However, the newly explicit, admitted `shadowRun_agree` signature is false on its stated carrier. A kernel-checked counterexample satisfies all its premises and contradicts its conclusion. Correct this helper before assigning the M1 proofs. This is a design verdict, not a claim that a production theorem has been proved incorrectly.

## Scope and immutable inputs

Audited revision: `4bf0c5f5089fbe657eccc8e31f1a270bbfe824bc` (`git log -1`: “SO-CSPLIT rev 1: answer design audit 1 (F1-F4, N1-N4)”). Compared the complete revision delta against parent `a6c13677886761fa8f8dd3dd31dedfcccc3b2a4b`, and the branch diff `git diff inp...HEAD`. The current `inp` ref was `7e8f8c0224ec6fd0fab2e3c9707c61076abe57d2`; its merge base with this branch remains `7b86cf178eaaffba3a7a4205a561b41ef3660455`. No frozen, manifest, implementation Lean, generated-root, or README change occurs in the branch diff.

Read AGENTS.md, PLAN.md, DECISIONS.md, the exact audit brief, audit 1, the revised design, authoritative signatures and handoff delta. The permission envelope remains report-only plus temporary scratch artifacts; no repair or git mutation is authorized. Applied the focused manuscript-audit method already used in audit 1, with a separate refutation pass and explicit distinction between elaboration and truth.

SHA256 snapshot (all line references below refer to these bytes):

| artifact | SHA256 |
|---|---|
| `.drafts/design/SOCsplitSignatures.lean` | `c584c7afe06510071ca94dc26eb40664f8c8415819048b21de54d5b4f60f313a` |
| `docs/tracks/SO/design/SO-CSPLIT.md` | `8cc344010dd3dfa3a3afe3f1362f76949ece9eac79f82ed2f11a9929e2eba254` |
| `.drafts/handoff-SO-CSPLIT.md` | `74c8698a4f20e3a3f3505703481d929c55895337d81f09c8514339ab7e5318f6` |
| `scripts/spin_orbit/csplit_census.py` | `16fde357a93b3199fb8dbb43ab94bf398c6e99d06eddd3d9e03a135aa0cc929d` |
| `scripts/spin_orbit/csplit_plan.py` | `26fa8773d1d35217276e142fa92ff2da63227b457468726694eef6fd6d51008b` |
| audit 1 | `389fa0b973e6a3bf2e28ec8cb3843786a0b4189622bd1c7a6ade585f68172bef` |

The signatures file is an ignored draft, not committed by `4bf0c5f5`; its full hash is therefore part of this audit's authority. The Markdown explicitly gives that file precedence over its excerpts. It has 711 lines and 84 explicit declarations: 33 definitions, 3 structures, 1 instance, 47 theorems. Thirteen theorem bodies are `sorry`.

## Disposition of audit 1

| Audit-1 item | Delta verdict | Evidence / remaining qualification |
|---|---|---|
| F1: missing elaborating interface | RESOLVED as an artifact/elaboration defect | Scratch copy elaborated locally at defaults: exit 0, exactly 13 sorry warnings. All formerly prose-only interfaces are present. New semantic failure is audit-2 F1 below. |
| F2: product output carrier | RESOLVED | `polyProduct_eq_of_mulPacked` returns `out.1.toErrTerms`; `mulPacked_eq_of_parts` matches II negation and RI/IR placement. Both proved; no sorryAx. |
| F3: sparse product contract | RESOLVED | Separate empty-factor lemmas, nonempty sparse branch, exact non-shard prefix, exact block/max arguments and complete shard coverage. Proved; no sorryAx. |
| F4: one-op prefix/read checks | RESOLVED | `segOk_one_of` explicitly takes checked segment/meta lookups, the singleton slice, `hprefix`, shadow-step success and `hresult`. Proved; no sorryAx. |
| N1: plan/counts and complete bytes | PARTLY RESOLVED | Forced cuts and counts reproduce exactly; all four saved plan JSONs reproduce. Byte totals remain a mixture of formatted definitions and estimates, including more estimates than the prose admits; audit-2 N1. |
| N2: memory subtraction | RESOLVED as an evidence-labeling requirement | Detailed sections label the split a projection pending G4, with decimal GB versus cgroup GiB distinguished. No isolated decode or production memory result has been independently established. Summary wording still needs consistency; N2 below. |
| N3: calibration order | RESOLVED | CAL-1 G0–G5 after A/L3, with standalone probes; CAL-2 G6–G7 after L2/B. No dependency inversion remains. |
| N4: projection-dependent plan proof | RESOLVED | `planOk` has no wanted argument; `wantedOk` is per projection. The two assembly templates actually share the same hplan/hseg. |

## F1 — High / blocking: `shadowRun_agree` retains unsupported future slots

**Location:** signatures 294–296 and 323–334; design §3.3's agreement argument, especially the assertion “`R` is unchanged and `i ∉ R`.”

`ComposeState.AgreeOn W R st st'` compares slots only under **both** `R i` and `i < st.len`. It imposes no restriction on whether `R` contains future slots. The theorem nevertheless retains all of `R` in its final agreement set while the states' lengths grow. A previously unconstrained future slot can become an obligation even when its operation is dead and replaced by a placeholder.

Concrete counterexample, valid for arbitrary arithmetic backend and environment:

```lean
σ = X = (⟨[], 0, 0, 0, []⟩ : ComposeState α)
R = fun _ => True
s = (⟨0, 1, [], [], []⟩ : SegSpec)
os = [.const 0 0 1]
σ' = σ.pushSlot W zeroModel
```

All premises hold:

- Initial `AgreeOn`: equal metadata; the slot clause is vacuous since `σ.len = 0`.
- `hreads`: the sole op is infallible and absent from `s.live`; its live antecedent is false (and it has no dependencies).
- `hrun`: the shadow run pushes exactly `zeroModel` and succeeds.

The landed run pushes `constModel n 0 0 1`. In the final states slot 0 exists and belongs to `R`. Agreement would equate the whole pairs at slot 0 and hence their model degrees, giving **`(0 : ℤ) = 1`**. This does not depend on floating-point values, rounding, analytic interpretation, malformed data, or a resource limit.

**Independent refutation attempt:** checked whether the implicit section binders, the live-read condition, or `AgreeOn` itself bounds R to existing slots. None does. The original prefix was copied into a scratch probe and the four claims `audit_initial_agree`, `audit_reads`, `audit_shadow_success`, and `audit_conclusion_false` were proved from the exact definitions. Each has axioms `[propext, Classical.choice, Quot.sound]`, **without `sorryAx`**. The negative theorem does not invoke `shadowRun_agree` or any other admitted theorem. This confirms a false signature rather than a mere missing proof.

**Proposed corrected signature:** add an initial-domain invariant `hR` (or equivalently restrict the retained set and the old-slot alternative in hreads to the initial prefix). Keep the main checker statements unchanged:

```lean
theorem shadowRun_agree {α : Type} [CertArith α]
    (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (s : SegSpec)
    {os : List SlpOp} {R : ℕ → Prop} {σ X σ' : ComposeState α}
    (hR : ∀ i, R i → i < σ.len)
    (hagree : σ.AgreeOn W R X)
    (hreads : ∀ (k : ℕ) (hk : k < os.length),
      (s.live.contains (σ.len + k) || os[k].fallible) = true →
        ∀ a ∈ opDeps os[k], a < σ.len + k ∧
          (R a ∨ (σ.len ≤ a ∧
            (s.live.contains a || (os.getD (a - σ.len) nopOp).fallible) = true)))
    (hrun : shadowRun n K wit W cfg pe s (some σ) os = some σ') :
    ∃ X', composeOpsAux n K wit W cfg pe (some X) os = some X' ∧
      σ'.AgreeOn W (fun i => R i ∨
        (σ.len ≤ i ∧
          (s.live.contains i || (os.getD (i - σ.len) nopOp).fallible) = true)) X'
```

This is a proposed proof target, not a claimed completed proof. For the intended caller `R i := i ∈ s.imports`, `hR` is supplied by `planOk`'s import bound and `segPrefixOk`'s `m.len = s.start`, together with `seed_stateMeta`. It is an internal state-domain invariant, not a new hypothesis on the mathematical theorem or a conclusion-shaped assumption. Add the one-op example as a negative contract test and prove the corrected agreement theorem at default budgets before claiming the M1 chain is ready.

`ComposeCkpt.compose_eq` itself was not refuted: its import checks provide the missing invariant for an eventual correct proof. Its current admitted proof, and the two templates that consume it, remain unclosed.

## Notes

### N1 — Medium: volume totals are reproducible estimates, not complete emitted bytes

The revised planner now emits all segment rows and implements the forced one-op cuts. Fresh reruns on the current stored censuses give:

| torus / B | cfgFull segments / cuts / ledger models | cfgLow segments / cuts / ledger models | reported volume |
|---|---|---|---:|
| lower / 75k | 38 / 10,28 / 155 | 70 / 28 / 324 | 10,377,848 B |
| upper / 75k | 38 / 10,28 / 155 | 70 / 28 / 322 | 10,342,277 B |
| lower / 150k | 20 / 10,28 / 105 | 33 / 28 / 260 | 8,516,494 B |
| upper / 150k | 20 / 10,28 / 105 | 33 / 28 / 257 | 8,458,479 B |

Each full JSON result equals its saved `plan_{lower,upper}_{75000,150000}.json` byte-content interpretation. Thus audit 1's unreproducible count issue is fixed.

However, design §5's “complete emitted volume” and statement that only the reflected witness and module-header sizes remain estimates are still too strong:

- `csplit_plan.py:84` uses a fixed 400-byte allowance and repeated placeholder text `⟨000, 0, 0, [cacheRef]⟩` for metadata, rather than formatting the actual boundary metas. It counts segment-row Unicode characters with `len(x)`, not UTF-8 bytes. A sampled row is 87 characters but 91 UTF-8 bytes.
- `csplit_census.py:69–72` adds a fixed **200-byte** product-definition allowance; it does not emit complete product declarations. The term-row count is useful but is not a complete generated file receipt.
- `productMemoBytes` sums all packed products in all segment records without a liveness filter. The dead cfgLow slot 10 is correctly skipped by the plan but still contributes **6,401 B** to the lower product-memo volume. This is conservative overcounting, not a kernel correctness failure.
- `mods(nbytes)` predicts module counts from bytes divided by `1400 * 36`; it neither splits files nor checks actual line counts. The production cap still requires an emitted-file check.

**Fix:** call the present totals formatted-definition plus overhead estimates; list plans/metas and product headers among the estimates; filter dead-product memos if reporting evaluated products. Retain the existing final `du -b`/actual-file receipt and check every generated module's line count. No evidence here establishes that the lunar total approaches 50 MB, so this note does not block the architecture.

### N2 — Low: summary and package tables retain superseded claims/names

The detailed projection caveats and CAL split are sound improvements. The summary still says the isolated decode “cost[s] 26 s and 3.1 GB” without marking it a projection, and the L1c table still says 129 products per torus while the revised evaluated count is 128. The recipe still names `List.all_range_of`, whereas the actual helper is `all_range_of_lt`. Production signature authority is explicit, so these are editorial consistency issues, not additional false Lean contracts.

**Fix:** propagate the detailed sections' qualifiers and exact helper names into summary/recipe/package tables. G0–G7 remain future production gates; successful signature elaboration does not execute them.

## Declaration-by-declaration ledger

All names below are relative to `KAM.Certificate`. Blueprint label is **N/A** for every row: these are computational infrastructure definitions and equalities against the landed checker, not restatements of I/N/P mathematical blueprint nodes. Source abbreviations: **EQ** structural carriers in `Expr/Slp`, `Defs`, `Model/FixedEq`; **M1** `Expr/Compose` plus the explicitly specified shadow/ledger definitions; **L3** `Model/Ops`, `Poly/MulPacked`, `Poly/Sparse`, `Model/Exp`; **L2** `Gram`, `Torsion/Models`, `Frame/Majorants`; **CHECK** landed checker bodies and V2 assembly. The related blueprint searches found ODE/barrier consumers, not an SO-CSPLIT node; no unrelated label is substituted.

PASS means an acceptable design contract/carrier after source comparison and counterexample search. It is not proof closure: **D** marks an admitted theorem; **T** an elaborated theorem with a supplied proof; definitions/structures/instance are marked by kind. In particular, template T bodies still inherit `sorryAx` from the admitted chain.

| Declaration | Line | Kind | Blueprint / source | Verdict | Reason |
|---|---:|---|---|---|---|
| `keyBeq` | 35 | def | N/A / EQ | PASS | Ordered integer-list equality. |
| `eq_of_keyBeq` | 40 | T | N/A / EQ | PASS | Structural equality reflection. |
| `SlpOp.beq` | 49 | def | N/A / EQ | PASS | All eight constructors and payloads compared. |
| `SlpOp.eq_of_beq` | 60 | T | N/A / EQ | PASS | Constructor equality reflection. |
| `opsBeq` | 67 | def | N/A / EQ | PASS | Ordered operation equality. |
| `eq_of_opsBeq` | 72 | T | N/A / EQ | PASS | List equality reflection. |
| `HamJet.beq` | 81 | def | N/A / EQ | PASS | Program and every index table compared. |
| `HamJet.eq_of_beq` | 85 | T | N/A / EQ | PASS | Full jet equality, not a projection. |
| `instDecidableEqCertFixedSeg` | 93 | instance | N/A / EQ | PASS | Mantissa equality on CertFixed; no function/matrix instance. |
| `ccBeq` | 100 | def | N/A / EQ | PASS | Both real and imaginary leaves. |
| `termsBeq` | 103 | def | N/A / EQ | PASS | Ordered keys and complex coefficients. |
| `CertPoly.segBeq` | 109 | def | N/A / EQ | PASS | Entire term list. |
| `CertModel.segBeq` | 112 | def | N/A / EQ | PASS | Degree, radius and polynomial. |
| `pairBeq` | 116 | def | N/A / EQ | PASS | Includes cached norm. |
| `cacheBeq` | 119 | def | N/A / EQ | PASS | Includes ordered key, polynomial and radius. |
| `eq_of_termsBeq` | 125 | D | N/A / EQ | PASS | Faithful full-carrier equality reflection; proof remains draft. |
| `CertPoly.eq_of_segBeq` | 128 | D | N/A / EQ | PASS | Faithful full-carrier equality reflection; proof remains draft. |
| `CertModel.eq_of_segBeq` | 131 | D | N/A / EQ | PASS | Faithful full-carrier equality reflection; proof remains draft. |
| `eq_of_pairBeq` | 134 | D | N/A / EQ | PASS | Faithful full-carrier equality reflection; proof remains draft. |
| `eq_of_cacheBeq` | 137 | D | N/A / EQ | PASS | Faithful full-carrier equality reflection; proof remains draft. |
| `ComposeMeta` | 146 | structure | N/A / M1 | PASS | Copies non-slot metadata; no assumed proof. |
| `SegSpec` | 154 | structure | N/A / M1 | PASS | Untrusted segment indices and lists. |
| `ComposeCkpt` | 163 | structure | N/A / M1 | PASS | Untrusted metas and full-pair ledger. |
| `SlpOp.fallible` | 169 | def | N/A / M1 | PASS | char/exp/inv/sqrt always run. |
| `ComposeState.stateMeta` | 178 | def | N/A / M1 | PASS | Literal metadata projection. |
| `ComposeCkpt.pairOpt` | 182 | def | N/A / M1 | PASS | First-match lookup, optional absence. |
| `ComposeCkpt.pair` | 187 | def | N/A / M1 | PASS | Same off-ledger zero pair as slot. |
| `SegSpec.liveEff` | 191 | def | N/A / M1 | PASS | Live or fallible at the actual op. |
| `SegSpec.ops` | 195 | def | N/A / M1 | PASS | Exact drop/take slice. |
| `ComposeState.seed` | 200 | def | N/A / M1 | PASS | Dense reversed slots, same metadata. |
| `shadowStep` | 208 | def | N/A / M1 | PASS | Dead infallible placeholder only. |
| `shadowRun` | 215 | def | N/A / M1 | PASS | Fail-closed loop. |
| `ComposeMeta.beq` | 223 | def | N/A / M1 | PASS | All metadata fields. |
| `ComposeCkpt.segPrefixOk` | 229 | def | N/A / M1 | PASS | Bounds, S1, earlier available reads. |
| `ComposeCkpt.segResultOk` | 240 | def | N/A / M1 | PASS | Metadata plus valid, present full-pair exports. |
| `ComposeCkpt.segOk` | 252 | def | N/A / M1 | PASS | Prefix AND successful run/result. |
| `segsTile` | 264 | def | N/A / M1 | PASS | Contiguous ordered prefix tiling. |
| `ledgerAsc` | 269 | def | N/A / M1 | PASS | Strict slot ordering. |
| `ComposeCkpt.exported` | 274 | def | N/A / M1 | PASS | Actual containing segment and export list. |
| `ComposeCkpt.planOk` | 280 | def | N/A / M1 | PASS | Initial state, tiling, import/export and ledger checks. |
| `ComposeCkpt.wantedOk` | 290 | def | N/A / M1 | PASS | Per-projection ledger membership. |
| `ComposeState.AgreeOn` | 294 | def | N/A / M1 | PASS | Bounded slot agreement; future R membership unconstrained. |
| `composeStep_infallible` | 298 | T | N/A / M1 | PASS | Four arms return a push. |
| `pushSlot_slot_lt` | 303 | D | N/A / M1 | PASS | Earlier slots persist, including default lookup. |
| `composeStep_congr` | 307 | D | N/A / M1 | PASS | Exact metadata/read agreement; both success or failure. |
| `seed_slot_of_mem` | 314 | D | N/A / M1 | PASS | Imported in-range slot lookup. |
| `seed_stateMeta` | 319 | T | N/A / M1 | PASS | Seed metadata is exact. |
| `shadowRun_agree` | 323 | D | N/A / M1 | FAIL | False for R containing a skipped future slot; F1. |
| `composeOpsAux_slot_persist` | 337 | D | N/A / M1 | PASS | Only earlier slots claimed persistent. |
| `ComposeCkpt.compose_eq` | 344 | D | N/A / M1 | PASS | Correct intended full-run projection; proof blocked by F1. |
| `shadowStep_of_live` | 354 | T | N/A / M1 | PASS | Live op uses landed step. |
| `ComposeCkpt.segOk_one_of` | 362 | T | N/A / M1 | PASS | Explicit prefix, optional lookups, singleton run and result. |
| `CertModel.mulN_eq_of_polyProduct` | 377 | T | N/A / L3 | PASS | Landed cached-norm radius verbatim. |
| `polyProduct_eq_of_mulPacked` | 387 | T | N/A / L3 | PASS | Correct toErrTerms carrier. |
| `CertPoly.mulPacked_eq_of_parts` | 397 | T | N/A / L3 | PASS | II negation and RI/IR placement exact. |
| `packedRealProduct_eq_nil_left` | 417 | T | N/A / L3 | PASS | Empty left returns empty exact result. |
| `packedRealProduct_eq_nil_right` | 423 | T | N/A / L3 | PASS | Empty right returns empty exact result. |
| `packedRealProduct_eq_of_sparse` | 429 | T | N/A / L3 | PASS | Nonempty sparse branch with exact checked inputs. |
| `checkPackedSpPrefix` | 438 | def | N/A / L3 | PASS | Verbatim non-shard guard prefix. |
| `PackedAdvice.shardRange` | 446 | def | N/A / L3 | PASS | Complete landed shard range. |
| `checkShardAt` | 450 | def | N/A / L3 | PASS | Exact blocks and maxima. |
| `checkPackedSp_of_groups` | 455 | T | N/A / L3 | PASS | Prefix plus full coverage and every group check. |
| `charResolve_eq_of_radius` | 469 | T | N/A / L3 | PASS | Cache miss and exact own-key witness. |
| `expWitnessRadius_eq_of_pin` | 479 | T | N/A / L3 | PASS | Exact range-reduced pin. |
| `expWitnessRadiusOf_eq_of_residuals` | 486 | T | N/A / L3 | PASS | Both real bounds and finite residual sum. |
| `expResidualProduct_eq_of_polyProduct` | 501 | T | N/A / L3 | PASS | Correct derivative product key and error terms. |
| `matMulEntry` | 511 | def | N/A / L2 | PASS | Exact landed entry body. |
| `modelMatMul_eq_buildMat` | 517 | T | N/A / L2 | PASS | Definitional equality. |
| `modelMatMul_eq_of_entries` | 521 | D | N/A / L2 | PASS | Explicit rectangular row/column shape. |
| `matMulEntry_eq_of_products` | 528 | T | N/A / L2 | PASS | Correct key, finite sum and degree conversion. |
| `gramModels_eq_of_entries` | 539 | D | N/A / L2 | PASS | Landed triangular reuse. |
| `gramDefectRows_eq_of_entries` | 546 | T | N/A / L2 | PASS | Correct finite balanced row sums. |
| `gramCheck_eq_of_rows` | 561 | T | N/A / L2 | PASS | Shape and exact candidate/bounds residual. |
| `torsionModels_eq_of_stages` | 574 | T | N/A / L2 | PASS | All stage keys/shapes/order and final bordered matrix. |
| `frameNModels_eq_of_stage` | 608 | T | N/A / L2 | PASS | Reuses omega of [4,0]. |
| `all_range_of_lt` | 619 | T | N/A / CHECK | PASS | Finite all from bounded row proofs. |
| `checkInvariance_eq_of_compose` | 624 | T | N/A / CHECK | PASS | Exact d1 residual and error threshold. |
| `checkEnergy_eq_of_compose` | 632 | T | N/A / CHECK | PASS | Singleton v0 and landed energy predicate. |
| `checkGram_of_gramCheck` | 638 | T | N/A / CHECK | PASS | Exact cfgLow and sigmaB-minus-mu. |
| `checkTorsion_eq_of` | 644 | T | N/A / CHECK | PASS | Exact torsion average residual. |
| `checkFrameT_eq_of` | 652 | T | N/A / CHECK | PASS | Exact top-left torsion row-corner bounds. |
| `checkFrameN_eq_of` | 662 | T | N/A / CHECK | PASS | Both row and transpose-column bounds. |
| `checkEnergy_of_ckpt` | 679 | T | N/A / CHECK | PASS | Shared plan/segments; explicit jet and wanted check. |
| `checkInvariance_of_ckpt` | 693 | T | N/A / CHECK | PASS | Shared plan/segments; explicit derivative rows. |

## Consumer, frozen-object, definition and package verdicts

**Consumers — PASS for interface compatibility, blocked for proof completion by F1.** Re-read `LunarAssemblyV2.lean:106–123` in SO-DATA3 and `CertificateSharp/V2/Engine.lean:92–122`. The base assembly still takes Static, HamBounds, Embedding, Invariance, Energy, Gram and Torsion. Refined assembly additionally takes HamClaim, frame majorants and refinedCore; soundness additionally takes the frequency-box and Diophantine facts. The revised signatures deliver the same literal checker conclusions, with no change to arithmetic precision, loss constants, radii, energy, norms or consumer carriers. They do not close these independent obligations. SO-DATA3's assembly remains an external integration dependency rather than a new Lean module in this branch diff.

The templates use `c.cfgFull` for invariance/energy, and the Gram/torsion/frame helpers use `c.cfgLow` and the exact `σB - μ` / `σT - μ` margins. `torsionModels_eq_of_stages` was compared with the landed stage pipeline: `[4,0]` through `[4,9]`, `DGi` negation, omega applications, matrix shapes, border frequency and last-row derivative models all match. It has a proof by explicit rewriting and no admitted dependency. `frameNModels_eq_of_stage` reuses the omega of `[4,0]`, as the landed frame does. The final `checkFrameN_eq_of` supplies both normal and transposed-normal bounds, and `checkFrameT_eq_of` supplies the landed torsion corner rows.

The requested searches for `\Nref{bpN:p3:` in I/P again locate ODE/reduction/barrier uses (I Parts 5, 7, 8; P Parts 1, 6, 11b, 14a/b). They do not consume this computational API. No new ODE statement, solution predicate, or replacement of an I/N/P source theorem is introduced by this revision, so there is no new N Part 3 consumer applicability claim to approve.

**Frozen objects — PASS within this delta.** Re-read the literal frozen `InvarianceError`, `Iso/ExtendedTorsion` and `Iso/ExtendedTorsionAverage` and their use through the existing checker soundness layer. The bordered torsion's bottom row remains `DH(K) N`, not a parallel substitute; invariance remains the frozen `X_H(K) - DK ω`. No frozen solution predicate is redefined or assumed equal to a new one. The revision aims at exact computational equations, so it inherits the existing consumer bridge once those equations are genuinely proved. Frozen files and manifest are byte-unchanged in the branch diff; the live guard/ABI checks pass. This does not re-audit the entire previously landed analytic soundness proof.

**Definitions — PASS with the theorem-domain defect in F1.** The three structures contain only untrusted data. `pairOpt` fails explicitly on missing data; `segResultOk` rejects an absent export; the seed's total default agrees with `ComposeState.slot`. `segPrefixOk` verifies every live/fallible read and all slice/meta bounds; `planOk` separately enforces earlier imports, exports and initial state. Comparing entire pairs preserves cached norms without adding analytic norm-validity assumptions to a computational equality. The only new instance is on `CertFixed P` via its mantissa, not on a bare function or matrix. Comparator definitions include every field they are supposed to identify; their five admitted reflections remain proof work. The initial-domain fact needed by `shadowRun_agree` is not presently a structure field or theorem premise, which is exactly F1.

**Packages — PASS for the revised dependency schedule and stated size budgets.** A precedes B/L3; CAL-1 uses only A/L3 and standalone probe statements; L2 precedes CAL-2's integration checks; GEN/DATA follow both gates. G0–G5 do not require an already proved global chain, while G6/G7 can use the table/bridge API. The admitted chain work must still be repaired/proved before its consumers are certified. The 711-line draft interface is below 1500 lines, and the proposed production modules are below 400 lines. Generated files require their own actual line-count verification; the planner's volume heuristic does not enforce that cap. One heavy computation per module and serial capped landing builds remain future integration requirements, not completed changes in this diff.

## Checks and proof-status evidence

All Lean/Lake activity was serialized, using the worktree's own `.lake` build and `LEAN_NUM_THREADS=1`, `nice -n 5`. No override, broad build, clean, dependency update or cache operation was used.

1. **Exact signature elaboration, once.** Copied the untouched authoritative file to `.drafts/scratch/SOCsplitSignatures.lean`, then ran:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .drafts/scratch/SOCsplitSignatures.lean
   exit 0
   ```

   Exactly 13 warnings, all `declaration uses sorry`, at original lines 125, 128, 131, 134, 137, 303, 307, 314, 323, 337, 344, 521, 539. No errors, heartbeat/depth options, or additional warnings. This resolves the original elaboration requirement, but it does not establish truth of admitted declarations.

2. **Counterexample and API/axiom probe.** `.lake/abi-scratch/SOCsplitRefute.lean` used an exact copy of the authoritative definitions and added the four proofs described in F1. The final probe exited **0**. Its four independent refutation results use `[propext, Classical.choice, Quot.sound]` only. The copied draft produces its same 13 sorry warnings; the probe also reports an unused arithmetic-instance warning on `audit_reads`. The counterexample proofs do not depend on any copied admitted declaration.

   One initial probe attempt failed because `by decide` was applied to a goal containing free variables; it was replaced by the explicit definitional reduction `change 0 < 1; exact Nat.zero_lt_succ 0`. The final negative proof concludes by applying `congrArg (fun p : CertModel α × α => p.1.deg)` to the forced slot equality and contradicting `Int.zero_ne_one`. No budget was raised.

   The following Mathlib/Lean declarations were independently `#check`ed successfully: `List.foldl_append`, `List.take_append_drop`, `List.all_eq_true`, `List.mem_range`, `Option.isSome_some`, `Option.Rel`. All additional Mathlib references used in the complete 34 supplied proofs were resolved by the successful signature elaboration itself.

3. **Axioms of the main new surfaces, independently printed.**

   | result | actual axiom output |
   |---|---|
   | `HamJet.eq_of_beq` | `[propext, Quot.sound]` |
   | `polyProduct_eq_of_mulPacked` | `[propext, Classical.choice, Quot.sound]` |
   | `CertPoly.mulPacked_eq_of_parts` | `[propext, Classical.choice, Quot.sound]` |
   | `checkPackedSp_of_groups` | `[propext, Classical.choice, Quot.sound]` |
   | `ComposeCkpt.segOk_one_of` | `[propext, Classical.choice, Quot.sound]` |
   | `torsionModels_eq_of_stages` | `[propext, Classical.choice, Quot.sound]` |
   | `shadowRun_agree` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
   | `ComposeCkpt.compose_eq` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
   | `checkEnergy_of_ckpt` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
   | `checkInvariance_of_ckpt` | `[propext, sorryAx, Classical.choice, Quot.sound]` |

   Thus “34 supplied proofs” is an accurate direct-body census, not a count of 34 independently closed results: the assembly templates depend on the admitted chain. The design's admission list is explicit and is permitted only as the requested draft-signature audit artifact, not for production code.

4. **Planner replay.** Ran `python3 -B -I scripts/spin_orbit/csplit_plan.py CENSUS B 0` for both tori and B = 75000, 150000: **exit 0** each, results in N1. Parsed all four full outputs and compared them with the saved plan JSONs: all equal. Python AST parsing passed for both revised scripts. The 85-second full census/mirror computations were not rerun; current census contents are external input, not independently established byte-exact Lean evaluation. This audit verifies the changed planner and volume formulas against them.

5. **Live source lint.** Ran in this worktree, without the shared-environment wrapper used in audit 1:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   exit 0
   check_lean_modules: PASS (1686 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (158 frozen declarations)
   ```

   Forbidden-pattern, root and size checks were silent. No new library Lean module exists to target with `lake build`; the requested direct signature elaboration is the applicable check.

6. **Change hygiene.** `git diff --check inp...HEAD`: exit 0. The new report is checked separately as an untracked file; source/design/draft hashes are rechecked at closeout. All temporary signature copies, Lean probes and report-construction scratch are deleted. Final worktree change is only this report.

**Errata and deviations:** no new suspected defect in a pinned external mathematical source. F1 is a newly exposed design-signature defect. No implementation deviation was introduced. CAL-1/CAL-2, generated data, memory/CPU projections, lock costs, and final analytic theorem closure were not executed or certified by this delta audit.

**Closeout:** FAIL pending repair and proof of the `shadowRun_agree` domain invariant. Audit 1's F1–F4 artifact/product/one-op repairs are retained as resolved; the new F1 is not a renamed reopening of those defects. The source-facing computational strategy remains usable after that local contract correction, subject to the still-required proof and calibration gates.
