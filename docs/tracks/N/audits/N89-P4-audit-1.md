# Independent package audit: N89-P4

Audit date: 2026-10-28. Target HEAD: `1b99fed967f7fa5a58d12207eb13d2a077f31e5e`.

**Overall verdict: PASS WITH NOTES for the N89-P4 internal helper.** No frozen anchor is proposed for sealing. The only expected hygiene exception is the generated root import file, as detailed below.

## Scope and authority

Audited only `KAM/Nekhoroshev/Poschel/BlockStability.lean` (144 lines), as required by the handoff's AUDIT FOCUS. Both `git diff inp...HEAD` and `git diff inp-n89p3...HEAD` add exactly that file. The observed comparison refs are `inp=20c6eb074acfab86dc6f5b775479030b75c2a625` and `inp-n89p3=0eed89bf0d170e47b53f57f42972dadc1849efd0`.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, N89-P4 handoff, track-N statement, N89 design (especially §3 and the P4 row), both N89 design audits, the authoritative signature, and blueprint p9:74–107. Inspected the exact upstream theorem interfaces and the setting, block hypotheses, admissibility and frequency maximum consumed here, including frozen frequency/vector-field definitions. The explicit user path overrides the brief's generic main-worktree destination.

This package exports an internal helper, `KAM.Nekhoroshev.block_stab`; it contains no provider and seals no frozen anchor. Frozen-provider equality and a literal frozen seal body are therefore not applicable. The corresponding signature check instead copies the authoritative `block_stab` declaration under a fresh name and applies the production theorem to all explicit binders in order; a `type_of%` example also checks the whole polymorphic type.

Signature authority: `/root/code/KAM-inp/.drafts/design/N89Signatures.lean:496–510`, SHA-256 `01270a67c964001a1f6f86a2416ce572fee94f326c34cec43fcef7de0fea4b88`. The production declaration text before its proof is byte-identical to this signature. Production file SHA-256: `e3ab6167a36edf14c1a9a50fa0fdf255c0d34ee11b8349fd5f2225c742aa2028`.

## Declaration and node review

| Node / declaration | Lean implementation | Verdict | Evidence |
|---|---|---|---|
| `bpN:p9:block-stab` | `KAM.Nekhoroshev.block_stab`, L37–53 | PASS | Exact signature; arbitrary field agreeing on W, interval through zero, genuine derivative equation, initial block, unchanged constants and both norm conclusions. No orbit-containment premise. |
| `stepN:p9:bs-theta` | local `hTheta`, L111–131 | PASS | D={I0}, r=c.radius Λ, analytic K=c.K/√n, α=c.alpha Λ, L=√n M, p=9/8, q=9. Converts bottom subgroup to {0}; supplies nonresonance, Lipschitz, radius equality and bottom smallness from block_hyp. Exact time factor 5 and period-one exponential. |
| `stepN:p9:bs-res` | local `hEuc`, L82–109 | PASS | Same singleton and analytic cutoff, δ=c.delta Λ; all positivity, p≤3/2, Hessian, quasi-convexity, nonresonance, closeness, two smallness and three radius conditions supplied. Ω=B.maximum bounds the closed Euclidean ball of radius r/2. Time factor 288, m r² and exponential are unchanged. Full lattice gives the univ disjunct for all time. |
| `stepN:p9:bs-stop` | L66–81, L91–94, L121–124, L132–139 | PASS | Admissibility monotone in absolute time; Ω≥0 derived from the center bound. Both applications prove hconf for every contained orbit before invoking stopped_extension, with ϱ=r/2 strictly between zero and r, and the appropriate action norm. Returns singleton-strip containment, then uses hsub to obtain W containment. |

The final split `Λ=⊤ ∨ Λ≠⊥` versus its negation is exhaustive. In the second branch, `Λ≠⊤` and `Λ=⊥`; in the first, the full-lattice time disjunct or the nonbottom time inequality applies. Since S supplies n≥2, top and bottom are distinct; no dimension-zero overlap is used. The Euclidean estimate implies the ambient max-norm estimate through `isActionNorm_euclid.norm_le`.

The resonant smallness is explicitly `eps ≤ m*r²/2^10 = (9/8)/9*(m*r²/2^7)`. `conjExp (9/8)=9` is proved by arithmetic. No step assumes a stability conclusion through S, hblock, an instance or a bundled field. The only new public declaration is block_stab; all local proof facts are internal to it.

## Definitions and import classification

No new `def`, `abbrev`, `structure`, instance or notation is introduced. Local lets c and B are exactly the design's theoremCover and blockBall. Existing Theorem1Setting contains source regularity, bounds, quasi-convexity and standing numerical conditions, with no orbit conclusion. Existing blockAdm retains full rank and Ω=0 as infinite time through multiplication inequalities. Existing FrequencyBall.maximum is the supremum of frequency Euclidean norms on precisely the closed Euclidean ball; frequency_maximum supplies nonemptiness, attainment, upper bounds and its center bound. The proof relies on these certified properties, not on an unguarded supremum fallback.

A recursive scan of the 143 project-module import closure found no provider and no frozen theorem module; frozen imports are definitions only. Thus no DRAFT_SORRY theorem is imported, directly or transitively. Direct imports are BlockHypotheses, Nonresonant, ResonantStability and Transfer. No new consumer applicability gap was found.

## Source fidelity, uncertainties and deviations

No suspected new blueprint/source defect, changed hypothesis, numerical correction or deviation was found in this package. In particular `local_field` is unnecessary: hF already concerns the same total realH as the upstream API, and hsub restricts this equality to the singleton strip. There is no indicator-Hamiltonian substitution needing a derivative-locality proof here.

This audit checks implementation against the approved design evidence and local blueprint; it does not independently re-audit the pinned PDFs, re-prove imported packages or close N-HEAD-C, thm1, the downstream Part 10 bridge, or any frozen root. Earlier design findings F1/F2 were resolved by design revision 2 and do not alter block_stab's signature.

## Independent validation

Every Lean/Lake check was serialized within this audit, using `LEAN_NUM_THREADS=1` and `nice -n 5`. No build was cleaned, dependency cache fetched, frozen source edited, or git state changed.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89p4 KAM.Nekhoroshev.Poschel.BlockStability
   ```

   Exit 0. Exact gate and terminal success lines:

   ```text
   [inp-gate] slot 2 acquired 12:17:17 for KAM.Nekhoroshev.Poschel.BlockStability
   Build completed successfully (3324 jobs).
   ```

   Replayed warnings only: Gradient:168 (`hgr`), Maximal:249 (`hK`), Blocks:34–35 (`hK`), BlockHypotheses:281–282 (`S`, `hr`), ODE.Exit:36 (unused section instance), Transfer:174 (`hϱ`), Resonant:263,391 (`hPid`, `ht₁0`), Nonresonant:92 (`hn`), ResonantStabilityCore:37,62 (`hδ`, `hd0`). All are inherited unused-variable/section-variable warnings; none is from the audited file. No warning was suppressed.

2. Exact-signature and explicit-binder application probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89P4Audit.lean
   ```

   Exit 0; exact output:

   ```text
   'KAM.Nekhoroshev.block_stab' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   The fresh-name declaration uses the literal design type and proof `exact block_stab S heps heps0 hfb Λ hΛ hF hJ h0 hz hI hblock`. The additional probe `example : type_of% @audit_block_stab_signature := @block_stab` elaborates. All new public theorem exports (one) therefore have the required axiom result, with no sorryAx.

3. Kernel replay, one invocation for the only added theorem module:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Poschel.BlockStability
   ```

   Exit 0; exact output:

   ```text
   replaying KAM.Nekhoroshev.Poschel.BlockStability
   ```

4. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely for the permitted generated-root mismatch; exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (554 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The generated root was not regenerated. The source scan found no forbidden proof escapes, resource overrides, EuclideanSpace, overlong files or malformed modules in the package. The file has its copyright, module, public imports, docstring and public section, and contains 144 lines.

5. Protected paths and whitespace:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check
   git diff --no-index --check /dev/null /root/code/KAM-inp-n89p4/docs/tracks/N/audits/N89-P4-audit-1.md
   ```

   The protected-path diff and tracked whitespace check exit 0 with empty output. The no-index check exits 1 (the new file differs from /dev/null) with empty output and no whitespace diagnostics. The initial report whitespace check found an extra blank line at EOF, removed before final validation. Final status lists only the new audit report and the pre-existing untracked N89-P4-handoff.md. The audit probe `.lake/abi-scratch/N89P4Audit.lean` was deleted after successful elaboration. No production file was edited.

## Handoff

File authored: `/root/code/KAM-inp-n89p4/docs/tracks/N/audits/N89-P4-audit-1.md` only. **PASS WITH NOTES** is limited to this package and the expected generated-root lint exception; the helper satisfies its exact design contract. No frozen seal readiness or campaign closure is inferred.
