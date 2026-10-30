# SO-CSPLIT independent design audit 1

**Overall verdict: FAIL.** The strategy of proving the existing checker Bools by memoized computation is reasonable, and the shadow-fold argument has the right basic invariant. The supplied artifact is not an elaborating signatures file, however, and three proposed helper contracts need substantive correction before provers receive them. This verdict concerns design readiness, not the truth of the KAM theorem or the existing certifier's soundness.

## Scope, authority, and frozen inputs

Focused, refute-first design audit under `/root/code/KAM-inp/.drafts/briefs/inp-audit-design.md`, AGENTS.md, PLAN.md, DECISIONS.md (including D39), and the designer's handoff. The user authorized the report and temporary scratch probes only; no implementation, generated root, frozen file, manifest, git state, or external evidence was changed. The requested verdict vocabulary takes precedence over the brief's alternative `PASS WITH FIXES` vocabulary.

Snapshot: branch `inp-socsplit2`, HEAD `a6c13677886761fa8f8dd3dd31dedfcccc3b2a4b`; comparison `inp` = `7b86cf178eaaffba3a7a4205a561b41ef3660455`. `git diff inp...HEAD` contains exactly the 698-line design and the two new Python scripts (1045 added lines). The complete diff was inspected. There are no changes under `KAM/Frozen/` or `manifest/`.

SHA256 at audit start:

| input | SHA256 |
|---|---|
| `docs/tracks/SO/design/SO-CSPLIT.md` | `dbddbc72588a46fdfca466e65929362fbe502a7281d4ed84306b283c2d700c05` |
| `.drafts/handoff-SO-CSPLIT.md` | `e4b697482349b809a1be5ee3ebdb6a6bbfcb49aa9b09db6f95421abf0560b14e` |
| audit brief | `b8fd2d407996dd9b3afc49f4d7548d9aff2ca4a8eed138381f8c7e4bd3d5a1df` |
| `scripts/spin_orbit/csplit_census.py` | `5c83ec5badbeb8237f16260a283d3c3f7828bdca5bcc3a6ce2842b46c8d71b6d` |
| `scripts/spin_orbit/csplit_plan.py` | `43812f1af4ba1adb1194bbb41b2db195611406778ac64cdf895713e8965de9d1` |

All design line references below refer to this snapshot. Read-only sources checked include `Expr/Compose`, `Model/Ops`, `Poly/MulPacked`, `Poly/Sparse`, `Gram`, `Torsion/Models`, `CertificateSharp/Kernel/Prune`, `CertificateSharp/V2/Engine`, and the external SO-DATA3 `LunarAssemblyV2.lean` and `product-probes.md`.

## Signature ledger

There is no `blueprint-SO/` or `docs/graph/SO/` in this checkout and no blueprint I/N/P statement naming these computation helpers. Their source specifications are the landed function bodies, not the unrelated Track N Part 3 ODE statements. No blueprint label is invented here. `source body` in the table means blueprint label **N/A**, with the indicated existing implementation as authority.

`PASS` below means the mathematical contract or data carrier is consistent at design level; it does **not** mean that the supplied declaration elaborated. F1 applies to the entire proposed API. Names listed only in prose are inventoried separately below.

| Lean name | Blueprint / source specification | Verdict | Reason |
|---|---|---|---|
| `SlpOp.beq` | N/A; `Expr/Slp` constructors | FAIL | No definition or soundness contract; F1. |
| `opsBeq` | N/A; list equality | FAIL | No definition or explicit reflection theorem; F1. |
| `HamJet.beq` | N/A; `HamJet` fields | FAIL | No body; field comparison only described; F1. |
| `HamJet.eq_of_beq` | N/A; structural jet equality | PASS | Intended implication is correct if the preceding comparator is implemented faithfully. |
| `ComposeMeta` | N/A; `ComposeState` non-slot fields | PASS | Copies len, counters, cache without assuming agreement. |
| `SegSpec` | N/A; segment index data | PASS | Untrusted data; validity must be checked, not assumed. |
| `ComposeCkpt` | N/A; ledger and boundary data | PASS | Full `(model, norm)` pairs, no conclusion-shaped field. |
| `shadowStep` | N/A; `composeStep` | PASS | Skipping only the four infallible arms preserves the proposed computation invariant. Untyped `env` prevents elaboration; F1. |
| `ComposeState.seed` | N/A; `ComposeState.slot` | FAIL | Body and lookup/default behavior absent; F1. |
| `ComposeCkpt.compose_eq` | N/A; `Slp.compose` | PASS | Exact existing output, arbitrary requested ledger subset; needs complete definitions and binders under F1. |
| `gramModels_eq_of_entries` | N/A; `Gram.gramModels` | PASS | Correct triangular reuse, no erroneous symmetry assumption on rounded computations. |
| `gramDefectRows_eq_of_entries` | N/A; `Gram.gramDefectRows` | PASS | Same Fin-indexed balanced sum and row order. |
| `matMulEntry` | N/A; `modelMatMul` body | FAIL | Missing body and typed arguments; F1. |
| `modelMatMul_eq_of_entries` | N/A; `buildMat`, matrix lookup | FAIL | `M has shape r × c` is not Lean; rectangular shape predicate unspecified; F1. |
| `matMulEntry_eq_of_products` | N/A; `modelMatMul` | PASS | Correct product key, balanced `modelSum`, and degree conversion. |
| `torsionModels_eq_of_stages` | N/A; `Torsion/Models` | FAIL | Premises replaced by ellipsis and comments; no actual stage interface to audit; F1. |
| `CertModel.mulN_eq_of_polyProduct` | N/A; `Expr/Compose.mulN` | FAIL | Radius contains ellipses; intended equation agrees with source but target is incomplete; F1. |
| `polyProduct_eq_of_parts` | N/A; `Model/Ops.polyProduct` | FAIL | Returns the `mulPacked` representation instead of error terms; F2. |
| `packedRealProduct_eq_of_shards` | N/A; `Poly/MulPacked`, `Poly/Sparse` | FAIL | Incomplete guards and shard coverage; missing empty-input branch; F3. |
| `segOk_one_of` | N/A; S1–S4 at design 206–213 | FAIL | Step success and export equality do not imply S1/S2; F4. |
| `seed_slot_of_mem` | N/A; seed specification | PASS | Correct conditional lookup property if the seed uses exactly `C.pair` at imported indices. Must explicitly share its missing-entry default. |

Additional named planned API (no signature supplied; **FAIL for interface completeness under F1**):

| Lean name | Blueprint / source specification | Required contract |
|---|---|---|
| `segOk` | N/A; design S1–S4 | Total checked implementation of all four clauses. |
| `planOk` | N/A; design 215–221 | Checked tiling, initialization, ledger/import/export conditions. |
| `AgreeOn` | N/A; design 242–250 | Whole-pair agreement on a named index set plus equal metadata. |
| `composeStep_congr` | N/A; eight landed step arms | Same failure/success and agreement extension on valid reads. |
| `composeStep_infallible` | N/A; four landed infallible arms | Success, len increment, metadata preservation. |
| `shadow_agree` | N/A; shadow fold | Agreement propagated from seed to exports. |
| `polyBeq` | N/A; `CertPoly` carrier | Boolean equality plus reflection. |
| `modelBeq` | N/A; `CertModel` carrier | Include degree and radius as well as terms. |
| `pairBeq` | N/A; cached slot pair | Include norm; reflection. |
| `cacheBeq` | N/A; ordered cache list | Include key, polynomial, radius and order; reflection. |
| `checkInvariance_eq_of_compose` | N/A; landed check | Exact residual predicate on the returned derivative models. |
| `checkEnergy_eq_of_compose` | N/A; landed check | Exact residual predicate on `[v0]`, with existing energy convention. |
| `List.all_range_of` | N/A; finite Boolean conjunction | Explicit finite-index hypotheses and all/range conclusion. |
| `gramCheck_eq_some_of` | N/A; `gramCheck` | Include shape, candidate and final bounds, not merely entries. |
| `expWitnessRadius_eq_of_residuals` | N/A; landed witness checker | Exact pin, residual and remainder premises and output. |

`lower_jet`, per-stage/data equalities and final checker equalities are proposed generated instances, not supplied declarations. None has been proved or elaborated in this design.

## Findings and proposed corrections

### F1 — Blocking: no elaborating signature artifact

At 153–160, definitions and the theorem have no bodies; at 199–204 arguments are untyped; at 291 the shape premise is English; at 298 the binder list is an ellipsis; at 330–341 result terms and premises contain ellipses. The document has seven Lean fences and no module/import/namespace/variable envelope. The literal use of `meta` as a function name also parses as a keyword rather than the intended metadata projection.

**Refutation attempt:** treat the Markdown as a literate container and extract only its seven Lean blocks, rather than failing it merely for Markdown syntax. The extracted file still fails with syntax and unknown-identifier errors. This is not a heartbeat failure. Adding imports cannot supply missing definitions, omitted premises, or the English shape predicate.

**Fix:** supply a complete, module-form scratch-elaboratable signatures file, with explicit binders, actual definitions and `by sorry` only in temporary audit signatures. Use e.g. `stateMeta`, not bare `meta`. The production implementation must obey the frozen-only sorry rule. Every prose-only helper above needs an exact statement. A representative corrected matrix interface is:

```lean
-- Inside namespace KAM.Certificate; α, arithmetic instance and arguments explicitly bound.
def matMulEntry {α : Type} [CertArith α]
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (key : ProductKey) (m : ℕ) (A B : ModelMatrix α) (i j : ℕ) : CertModel α :=
  CertModel.toDeg W pe 0 (modelSum W pe (List.ofFn fun k : Fin m =>
    CertModel.mul W cfg (key ++ [i, j, k.val])
      (modelMatrixEntry A i k.val) (modelMatrixEntry B k.val j)))

-- In a section binding α, W, cfg, pe, key, r, m, c, A, B with the above types:
theorem modelMatMul_eq_of_entries {M : ModelMatrix α}
    (hrows : M.length = r)
    (hcols : ∀ row ∈ M, row.length = c)
    (h : ∀ i < r, ∀ j < c,
      matMulEntry W cfg pe key m A B i j = modelMatrixEntry M i j) :
    modelMatMul W cfg pe key r m c A B = M
```

The exact intended chain statement, with the formerly implicit environment made explicit, is:

```lean
-- Requires the new definitions C.planOk, C.segOk, C.pair to be supplied first.
theorem ComposeCkpt.compose_eq {α : Type} [CertArith α] [DecidableEq α]
    (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (C : ComposeCkpt α)
    {p : Slp} {wanted : List ℕ}
    (hplan : C.planOk p.ops.length wanted = true)
    (hseg : ∀ j < C.segs.length, C.segOk n p.ops K wit W cfg pe j = true) :
    Slp.compose n p K wit W cfg pe wanted =
      some (wanted.map fun i => (C.pair i).1)
```

For `CertModel.mulN_eq_of_polyProduct`, replace its ellipses by the landed radius verbatim:

```lean
-- Section binds W cfg key a na b nb and out with their landed types.
theorem CertModel.mulN_eq_of_polyProduct
    (h : CertModel.polyProduct W cfg key a.poly b.poly = some out) :
    CertModel.mulN W cfg key a na b nb =
      ⟨a.deg + b.deg, truncPoly cfg.cutoff out.1,
        upAdd (upAdd out.2 (errRadius W (out.1.map (truncErr cfg.cutoff))))
          (upAdd (upAdd (crossUp na b.rad) (crossUp nb a.rad))
            (upMul a.rad b.rad))⟩
```

These are proposed contract repairs, not a claim that the absent API was independently implemented. In particular, no faithful corrected `torsionModels_eq_of_stages` signature can be certified until all its stage hypotheses are actually supplied; copying its desired conclusion and inventing premises would evade this audit.

### F2 — High: product assembly has the wrong output carrier

At 337 the RHS is `some (⟨tRR ++ tII ++ tRI ++ tIR⟩, …)`. That is the output shape of `CertPoly.mulPacked`, which returns `Option (CertPoly α × α)`. The named LHS, `CertModel.polyProduct`, returns **`Option (List (ErrTerm α) × α)`**, by `Model/Ops.lean:83–97`. Its successful packed branch explicitly calls `out.1.toErrTerms`.

**Refutation attempt:** checked both declaration types in Lean and read both bodies. `CertPoly` is not definitionally a list of error terms; the missing conversion is real. Even a manually constructed list must have exactly the zero-error conversion and order used by the landed code.

**Fix:** either first prove the four-part equality for `CertPoly.mulPacked`, then use the following fully typed bridge (independently elaborated and proved, no sorry), or correct the original conclusion to `some ((⟨tRR ++ tII ++ tRI ++ tIR⟩ : CertPoly α).toErrTerms, …)`:

```lean
theorem polyProduct_eq_of_mulPacked {α : Type} [CertArith α]
    (W : CertWeight) (cfg : ModelConfig α) (key : ProductKey)
    (a b : CertPoly α) (P : ℕ) (rr ii ri ir : PackedAdvice)
    (out : CertPoly α × α)
    (ha : a.isConst = false) (hb : b.isConst = false)
    (hk : adviceLookup cfg.advice key = some (.packed P rr ii ri ir))
    (hp : CertPoly.mulPacked cfg.toMant W P rr ii ri ir a b = some out) :
    CertModel.polyProduct W cfg key a b = some (out.1.toErrTerms, out.2)
```

The four-part helper must also spell out the omitted decode premises exactly: II decodes `pII.1.map (fun t => (t.1, -t.2))` into the real component; RI and IR decode into the imaginary component. These are not interchangeable with RR's placement. The original ellipses prevent verification of those premises; do not interpret this as evidence that the author intended a wrong sign.

### F3 — High: sparse-product lemma does not specify a sufficient generic contract

At 338–341, `checkPackedSp guards` is not the landed API: `checkPackedSp` takes `adv`, `ea`, `eb`. `guards`, `SA`, `SB`, `mA`, `mB` and the shard groups are not tied to the actual inputs, nor is there a coverage premise for all required shard numbers. More concretely, `packedRealProduct` returns `some ([], 0)` immediately on either empty input (`MulPacked.lean:240`). The proposed unconditional RHS uses the advice target and remainder instead.

**Refutation attempt:** the missing `guards` might have meant the full `checkPackedSp adv ea eb = true`. That would repair the nonempty sparse branch, but would duplicate all shard work, defeating the intended split, and still leaves the empty branch. The lunar design expressly uses three empty complex parts per product (350–351), so the total-carrier issue cannot be dismissed as irrelevant.

**Fix:** use separate empty lemmas returning `some ([], 0)`, and for the nonempty branch use this independently proved bridge:

```lean
theorem packedRealProduct_eq_of_sparse (adv : PackedAdvice) (W : CertWeight)
    (P2 : ℕ) (x y : List (CertKey × ℤ))
    (hx : x.isEmpty = false) (hy : y.isEmpty = false)
    (ha : adv.la.allSlots x = true) (hb : adv.lb.allSlots y = true)
    (hs : checkPackedSp adv (adv.la.slotTerms x) (adv.lb.slotTerms y) = true) :
    packedRealProduct adv W P2 x y =
      some (adv.targetTerms, adv.remainderBound W P2)
```

To obtain `hs` cheaply, a separate generic assembly lemma must take the exact non-shard prefix of `Sparse.lean:395–405` and hypotheses for **every** `s` in
`List.range (adv.spCount adv.la.denseLen + adv.spCount adv.lb.denseLen - 1)`, using precisely `spBlocks … ea`, `spBlocks … eb`, `spMax ea`, and `spMax eb`. If grouping is retained, require that range to be covered by the concatenated groups. Check shape, positive dense lengths, ordering, slot bounds and rounded length in the prefix. No global instance or soundness reproof is needed.

### F4 — High: `segOk_one_of` cannot discharge S1 and S2

At 361–364 the only premises are the segment shape, one landed step's success, and metadata/export equality. S1 requires the *input* metadata length to equal `i`, and S2 requires valid, available earlier operands. Neither follows from the given premises.

**Concrete refutation:** take a one-op segment at `i` containing `.add i i`, with no imports and input state length `i`. The landed add always succeeds, reading the default zero pair at the forward/self references. Choose the next metadata and ledger output to match that result; `hop` and `hx` hold, but S2 requires `i < i`, which is false. The scratch theorem `forward_add_succeeds` proves the success part for arbitrary backend and state by `rfl`. Invalid input length gives a separate S1 failure.

**Refutation attempt:** a future `hplan` alone does not rescue this theorem: the stated `planOk` checks tiling and import/export structure, not operand dependency closure. The helper is generic and must either receive or verify the missing clauses. Restricting production data to well-formed cases does not prove its current signature.

**Fix:** factor `segOk` into an index/metadata-prefix check and a result check. A corrected contract schema is:

```lean
-- New segPrefixOk is defined as precisely S1 + S2 + all indexing bounds;
-- segResultOk is precisely the existing metadata and export comparison.
-- Every variable must be explicitly bound in the actual signatures file.
theorem segOk_one_of
    (hj : C.segs[j] = ⟨i, i + 1, [i], imps, [i]⟩)
    (hprefix : C.segPrefixOk ops j = true)
    (hop : composeStep n K wit W cfg pe
      (ComposeState.seed W (C.metas[j]) C imps) ops[i] = some st')
    (hresult : C.segResultOk W j st' = true) :
    C.segOk n ops K wit W cfg pe j = true
```

Supply explicit bounds for every `[...]` access, or checked optional lookups with their success premises. This schema is intentionally identified as a proposed API refactoring, not an already elaborated theorem; it must not be replaced by assuming `segOk` itself.

## Notes

### N1 — Medium: planner counts are prospective and byte counts are not complete emitted bytes

Fresh runs of the committed planner on the supplied censuses with `75000 0` reproduce the principal work totals, but not the advertised forced-cut plan:

| quantity | lower rerun | upper rerun | design |
|---|---:|---:|---|
| cfgFull segments | 37 | 37 | 38 |
| cfgFull ledger models | 157 | 157 | 155 |
| cfgFull ledger bytes | 2,512,239 | 2,508,870 | about 2.49 MB |
| distinct models across both chains | 386 | 384 | 384 |
| cfgLow segments | 70 | 70 | 70 |
| cfgLow ledger models | 324 | 322 | 324 / 322 |
| Gram entry theorems | 9 | 7 | 7 |

The first cfgFull boundary is 12, so the current planner does not isolate `[10,11)`. Its maximum segment costs are 111,638 / 110,687 (cfgFull), 94,333 / 93,382 (cfgLow), exceeding B until the proposed slot-28 rewrite split is implemented. The document acknowledges future forced cuts at 643, so these are not proof-soundness defects. Label the table as a projected amended plan and emit the actual plan before using its counts as receipts.

`csplit_census.py:80–83` adds a fixed **120-byte** header estimate to term-row bytes; it does not emit and count the actual degree, radius, cached norm, declarations, imports or metadata. Stage sizes are estimates by term count. Thus “exact emitted bytes” (63, 90, 534 onward) is too strong. Proposed fix: report term-row bytes separately, and measure the complete generated files before the 50 MB decision. The present discrepancy does not by itself establish that lunar data exceed 50 MB.

### N2 — Medium: product memory split is an unmeasured projection

The design appropriately declares its rate law a fit and requires G0–G7. Preserve that status. `product-probes.md` reports P1 as a complete product at 9.89 GB and RR as an `isSome` check at 6.78 GB; the difference is not a measurement of an isolated decode theorem. It includes decode, `toErrTerms`, truncation and error-radius work, under potentially different cache peaks. The design's “≤ 3.1 GB” decode and “none is larger” claims are not established bounds by subtraction. G4's production import closure and fully forced literal equality are therefore mandatory, as already proposed. Also distinguish RSS in decimal GB from the cgroup's `10G` limit and `memory.peak`.

### N3 — Medium: calibration order needs clarification

At 508–509 G6 exercises Gram/torsion entries and G7 a full energy recipe; at 647 the order places CAL before L2. Those gates need either the relevant L2/bridge implementation or explicit standalone probe proofs. Proposed fix: build the minimal L2 and B recipes before G6/G7, or split CAL into independent early and integration gates. This is not a demonstrated mathematical dependency cycle; it is an incomplete execution schedule.

### N4 — Low: sharing changes the plan-check proposition

At 264–265 the same `hseg` can be reused for `[v0]` and `d1Slots`, but the same literal `hplan` proof has a type mentioning its original `wanted`. Supply a cheap subset/monotonicity lemma for `planOk` or separately decide the two plan checks. No additional composition is needed.

## Consumer, frozen-object, definition and package verdicts

**Consumers: PASS in shape, blocked by F1–F4 for execution.** SO-DATA3's external `landedBase_check_of` takes exactly Static, HamBounds, Embedding, Invariance, Energy, Gram and Torsion. Its `checkTorusCertificateV2_refined_of` additionally needs HamClaim, frame majorants and refinedCore. The design correctly retains these independent obligations; proving the six heavy Bools alone does not certify a torus. `checkTorusCertificateV2_sound` additionally requires the frequency-box and Diophantine hypotheses. The external assembly file is unlanded relative to this diff and must be available before generated modules import it.

The requested grep of `\\Nref{bpN:p3:` in I/P was performed. Those consumers concern ODE existence, uniqueness, continuation, Hamiltonian reduction and barriers, not the proposed computation layer. No replacement of their carriers or solution predicates is proposed. Consequently these unrelated ODE uses do not provide fidelity labels or establish closure for SO-CSPLIT.

**Frozen objects: PASS for the proposed preservation strategy.** Read the literal `HamiltonianVectorFieldC`, `InvarianceError`, `Iso/ExtendedTorsion`, and `Iso/ExtendedTorsionAverage` definitions and the existing `CertifiedTorus` output. They use `Fin n → ℂ`, product phase coordinates, and the frozen bordered torsion with the `DH(K) N` last row. M1–M3 aim at exact equality of existing computations rather than alternate analytic predicates. No frozen definition or signed statement is changed. This audit does not reopen the previously proved analytic soundness layer.

**Definitions: PASS for the three data structures; incomplete for new computations.** No conclusion-shaped structure field or bare-function/matrix instance is introduced. The pair ledger is correctly designed to carry cached norms, and the state agreement includes cache order and radii. The chain proof's dead-arm argument agrees with the landed `const`, `action`, `add`, `mul` arms; fallible `char`, `exp`, `inv`, `sqrt` remain executed. Seed density, lookup defaults, total checked indexing, and comparator reflection still require definitions and proofs under F1. No norm-validity premise is needed merely to equate computations when whole cached pairs are tracked exactly.

**Packages: PASS for bounded module sizes and the core mathematical order; N3 for gating.** A precedes B/L3; L2 and L3 depend on the landed checker; generated data/assembly need the completed generic API. The planned modules are individually below 400 lines, hence below 1500. Generated literal modules also need explicit sharding below the cap; estimated total source volume is not a per-file check. The serial heavy-module prebuild is a sensible integration requirement, not implemented by this design diff. No heartbeat/depth override is accepted.

## Verification evidence and limitations

All Lean invocations were serialized with `LEAN_NUM_THREADS=1`, `nice -n 5`; no build, cleanup, cache download or dependency clone was requested. This worktree has no Lake build/dependency overlay. To avoid materializing dependencies here (the handoff records that previous incident), probes used the existing built environment with `lake -d /root/code/KAM-inp env lean ABSOLUTE_SCRATCH_PATH`. The seven implementation files used by the probes were independently compared with this worktree and were byte-identical. This is an explicitly bounded shared-environment check, not a claim that the worktree itself has been built.

1. Copied the original document unchanged to `.drafts/scratch/SO-CSPLIT.md`. Extracted its seven Lean fences into `.lake/abi-scratch/SO-CSPLIT-signatures.lean`; ran the extracted signature artifact **once**:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake -d /root/code/KAM-inp env lean \
     /root/code/KAM-inp-socsplit2/.lake/abi-scratch/SO-CSPLIT-signatures.lean
   exit 1
   :3:36: error: unexpected token 'def'; expected ':=', 'where' or '|'
   :55:35: error: expected token
   :76:21: error: unexpected token 'meta'; expected ')' or term
   ```

   Additional missing imports/identifiers were reported. The audit does not count running a Markdown file verbatim as a useful elaboration test. The extracted declarations already fail before any heavy kernel computation. No attempt was made to silently complete their definitions.

2. Separate source/API probe `SO-CSPLIT-probe.lean`: **exit 0**, no sorry warnings. Checked `List.foldl_append`, `List.take_append_drop`, `List.ofFn`, `List.finRange`, `Option.isSome_some`, `composeOps_eq`, `composeOpsAux_eq`, `buildMat_entry`, `CertModel.polyProduct`, `CertPoly.mulPacked`, `checkPackedSp`, `checkShardSp`, `HamJet`, `HamJet.prog`, `SlpOp`, `CertPoly.toErrTerms`, `CertModel.mulN`, `CertArith`, and `LawfulCertArith`. Proved the two corrected bridges in F2/F3 and `forward_add_succeeds`. For each:

   ```text
   #print axioms: [propext, Classical.choice, Quot.sound]
   ```

   No `sorryAx` was used. These are scratch repair/refutation probes; no main theorem of the proposed package exists yet for `#print axioms`.

3. `python3 -B -I scripts/spin_orbit/csplit_plan.py CENSUS 75000 0`: **exit 0** for lower and upper; fresh counts recorded in N1. Both Python files pass `ast.parse`. The full census, heavy kernel receipts and data-generation work were not rerun; receipt claims remain attributed to SO-DATA3 rather than represented as independent passes.

4. `scripts/lint_sources.sh`: **exit 0** with this worktree's sources and manifest, and a temporary scratch PATH wrapper routing its nested `lake` command to the same existing `/root/code/KAM-inp` environment. Exact output:

   ```text
   check_lean_modules: PASS (1686 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (158 frozen declarations)
   ```

   Root and forbidden-pattern checks were silent. The ABI result checks the built shared environment against this worktree's manifest; it does not imply a new build in this worktree. This routing was necessary to preserve the report/scratch-only scope and avoid Lake's automatic dependency initialization.

5. `git diff --check inp...HEAD`: **exit 0**. Final report whitespace and original-input hashes checked again at closeout. Temporary copies, probes and wrapper removed. No targeted `lake build` applies: this branch adds no Lean module, and a build cannot substitute for the failed signature-artifact test.

Suspected pinned-source errata: **none found**. Deviations: shared built environment and extraction of literate Lean blocks, explicitly documented above. No external mathematical source or full certifier proof was re-audited. The requested brief was followed as an infrastructure-design audit; the absent exact interfaces and source-level defects were retained rather than repaired in the design.

**Closeout:** FAIL remains until F1–F4 are corrected and the actual complete signatures elaborate at defaults. N1–N4 need dispositions before scaling generation; production memory remains contingent on G0–G7.
