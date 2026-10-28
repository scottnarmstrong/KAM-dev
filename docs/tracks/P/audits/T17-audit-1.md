# T17 independent package audit 1

Overall verdict: **PASS WITH NOTES**. The sole T17 export, `KAM.Planetary.remain`, passes exact signed-statement, proof, consumer-interface and kernel checks. The note is the expressly permitted stale generated root. This is acceptance of T17 infrastructure; no frozen theorem is proved or seal-ready as a result of this package alone.

## Scope and authority

Audited on 2026-10-28 in `/root/code/KAM-inp-p11c-t17`, HEAD `959be8bff9724af98634b2c364c57d5ef36db8dd`; comparison ref `inp` was `9fc6965a034a91dede3a0eaedd019e922f0a7b80`. Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, T17-handoff, P11C design and its independent design audit, the live standalone signatures, track-P statement, relevant frozen definitions and P-G statement, and the p11b/p12 source contracts.

The user's exact destination overrides the generic brief's instruction to write in the main inp worktree. The handoff explicitly restricts the audit to `KAM/Planetary/PlanarTorsion/TorsionBound.lean`. `git diff inp...HEAD` contains nine added Lean files (1,429 lines): T17 plus inherited Beta and seven Quartic files from T13/T6. HEAD itself adds only TorsionBound (32 lines). Those inherited implementations receive no independent package verdict here. Their loaded dependencies participate in the build, axiom and replay checks.

T17 source SHA-256: `55cb8ffb1626546dc7929284c8e755f25d9746330694b66e5fdb6445ee180405`.

## Declaration and node coverage

| Node / obligation | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `bpP:p11b:remain`, compact torsion bound | `KAM.Planetary.remain`, TorsionBound:23–30 | PASS | Signature text exactly equals standalone P11CSignatures:655–658, including p, K, hK, hn, hc order and the positive uniform lower bound. No added premise, carrier change, or wider constant dependence. |
| Signed copy / application | `t17_signed_copy` (disposable probe only) | PASS | Literal signed declaration with body `exact KAM.Planetary.remain p K hK hn hc` elaborates; `example : type_of% @t17_signed_copy := @KAM.Planetary.remain` elaborates. |
| Blueprint remark's remaining P-G clauses | No T17 export assigned | NOTE | p11b:224–226 clause (2) explicitly assigns joint analyticity, extension, periodicity, fast diffeomorphism and boundary collar to Part 12. These are not claimed closed by this compact-positivity lemma. |

Design node table: P11C-LEAN-DESIGN.md:137 maps precisely this node to T17; package row :223 specifies “remain via compact positivity; T13, Mathlib compact minimum.” The independent design audit :64 explicitly accepts this signed helper. Thus every graph node assigned to the scoped module is covered at the design's approved signed granularity. There are no additional unsigned graph-named exports.

No provider export or frozen anchor is assigned to T17. Consequently provider-versus-frozen-type and frozen seal-body probes are inapplicable; the signed copy/application probe is the corresponding interface check. P-G's `htorsion` was inspected for consumer compatibility, not treated as a theorem proved here.

## Proof and adversarial checks

For empty K, B=1 is positive and the universal bound is vacuous. For nonempty K, continuity of the determinant gives continuity of its absolute value. `IsCompact.exists_isMinOn` returns a minimizer a₀ **in K**, so hn at a₀ yields strict positivity of its absolute determinant. Minimality gives the required lower bound at every a in K. The actual Mathlib theorem was checked at `Mathlib/Topology/Order/Compact.lean:228–232`; no extra closedness, positivity or connectedness premise is hidden.

Nonvanishing and continuity are legitimate source premises for this specific compact-positivity helper, exactly as in p11b:225 and the signed interface. It does not assume a positive uniform lower bound. No validity of physical data or axis-cone membership is needed for this stronger abstract compact-set assertion: hn and hc explicitly guard the determinant on the entire K in use. No junk-value behavior is used to derive the bound.

Consumer check: design :227 and :270 place `remain` before T21/Part 12. A compact axis patch with nonzero determinant supplies hn; T13's entrywise analyticity on the axis cone supplies determinant continuity. The result restricts to any subset of K. Under the Part-12 identity beta(mu,I)=p11c_beta(p,a(I)) and a(I) in K, the same B works for every mu and I, precisely the frozen P-G `htorsion` conclusion (ProperlyDegenerateKAM.lean). Blueprint `p12-planar-assembly.tex:129` uses this same restriction and coordinate substitution. Those physical identities and patch construction remain consumer obligations; no completed consumer proof is asserted. The theorem promises existence of B, which suffices; consumers do not require a canonical chosen minimum or a numeric B uniform across p and K.

## Definition classification and namespace hygiene

T17 adds **no def, abbrev, structure, instance, notation, or fallback**. Its only public declaration is `KAM.Planetary.remain`. Existing `p11c_beta` is the T13 matrix, used directly, without a replacement definition. The proof uses determinant and absolute value on their ordinary total carriers. PlanarData and physical coefficient correctness belong to their existing owning packages.

The declaration is scoped inside `KAM.Planetary`, not at the root. A declaration-name scan found only this production `remain`; no reused public helper short name or harmful root shadow was introduced. No global instance was introduced. The transitive KAM import traversal found 204 modules, no provider import and no frozen theorem module. All 58 imported frozen definition anchors have manifest state `SEALED`; no DRAFT_SORRY anchor is imported.

## Fresh validation receipts

All Lean/Lake invocations launched by this audit were serialized and set `LEAN_NUM_THREADS=1`, with `nice -n 5`. Lint, which runs the ABI checker, was launched only after replay completed. No clean, dependency update, cache download, resource override or root regeneration was performed.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t17 KAM.Planetary.PlanarTorsion.TorsionBound
   ```

   Exit 0. Output includes `[inp-gate] slot 2 acquired 22:48:47 for KAM.Planetary.PlanarTorsion.TorsionBound` and `Build completed successfully (9250 jobs).` Replayed dependencies emit pre-existing unused-variable, deprecated-name and unused-simp warnings; T17 emits none. The count is Lake's target dependency graph, not a library-from-scratch build.

2. Signed signature and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T17Audit.lean
   ```

   Exit 0; both interface checks elaborate. Exact axiom output:

   ```text
   'KAM.Planetary.remain' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   `#print KAM.Planetary.remain` also confirms the actual body uses only the empty-set split and `IsCompact.exists_isMinOn`; no imported proof of physical nonvanishing is silently consumed. The signed declaration text was independently compared with the standalone file: `Exact signature text equality: True`.

3. Kernel replay (one invocation for the sole scoped lemma module):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.TorsionBound
   ```

   Exit 0. Exact output:

   ```text
   replaying KAM.Planetary.PlanarTorsion.TorsionBound
   ```

4. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the permitted generated-root discrepancy. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1058 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other lint failure occurred. The root was not regenerated.

5. Protected paths and whitespace:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   ```

   Both exit 0 with empty output. T17 has 32 total lines, maximum line length 97 characters; copyright, module, public imports, module docstring and exposed public section are present. Direct scans find no forbidden proof escape, resource option, or EuclideanSpace. The signed theorem is the only new public result, so its axiom check covers every T17 export.

## Findings, uncertainties and handoff

No substantive T17 defect, suspected pinned-source erratum, or blueprint contradiction was found. The source remark's broader Part-12 bookkeeping is intentionally outside the signed compact-positivity export, consistent with the design audit and consumer needs. No pinned PDF re-audit is claimed for this elementary compactness argument.

The generated root is stale because new modules are absent from its generated import list. The audit brief expressly permits that isolated lint condition and forbids editing KAM.lean; leave regeneration to integration. T13 is described as “in audit” by the handoff; this report does not certify its physical formula or the inherited T6 package. No frozen theorem closure follows from this report.

Only this report is a lasting audit edit. The pre-existing untracked T17-handoff.md is left untouched. Disposable probe and logs under this worktree's `.lake/abi-scratch/` are removed after recording their receipts. No git mutation, source repair, manifest edit, or change in the main inp worktree was performed.
