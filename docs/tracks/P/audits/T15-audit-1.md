# T15 independent package audit 1

Date: 2026-10-28. Scope: only `KAM/Planetary/PlanarTorsion/FrozenBridge.lean`.

## Verdict

**PASS WITH NOTES.** The one public theorem implements its exact approved conditional signature. T15 has no provider export or frozen theorem anchor to seal. This result does not close `birkhoff_form`, P-G, or the physical assembly obligations of T16.

Audited HEAD: `13dc66d499a5d115b8a248619603891095d64e83`; comparison ref `inp` at inspection: `e2088d57c609cc20f1033b70a41e064402222f53`. `git diff inp...HEAD` adds only the 118-line FrozenBridge module. The pre-existing untracked `T15-handoff.md` was read, not edited. The user's exact worktree-local report destination overrides the generic brief's main-worktree destination.

Authority read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, T15-handoff.md, P11C-LEAN-DESIGN.md (especially L62, L130–136, L163, L216–217, L257), DESIGN-P11C-design-audit-1.md (N2 and theorem row L59), `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` L547–560, blueprint-P/parts/p11b-planar-torsion.tex L205–222, docs/graph/P/DEPGRAPH.md L31211–31233, track-P statement's averaged premises, and the frozen definitions HasSecularBirkhoffForm, Phase, Assemble, SecularAverage and OscillatorAction. There is only one P11C design audit in this checkout.

## Declaration and node review

| Node / obligation | Lean declaration or fragment | Verdict | Reason |
|---|---|---|---|
| `bpP:p11b:birkhoff-form`, T15 portion | `KAM.Planetary.hasSecularBirkhoffForm_of_sixth_order`, L31–114 | PASS | Declaration header, from `theorem` to before `:=`, is byte-identical to standalone signature L547–560. Same P, carriers, binder order, constants, integrability premise, sixth-order premise, and frozen conclusion. |
| `stepP:p11b:bt-frozen`, domain conversion | Local `hsq`, `hlen`, L46–66 | PASS | Two disc inequalities imply L² < 2d²; positive d ≤ r0 ≤ r/√2 gives L < √2 r0 ≤ r, including the allowed equality at the outer radius. |
| `stepP:p11b:bt-frozen`, integrability | L67–68 | PASS | Applies hi on the original P, at every mu ∈ [0,mu0], I ∈ V, on every full r0 oscillator disc. No replacement law or integral convention. |
| `stepP:p11b:bt-frozen`, little-o clause | L69–114 | PASS | Positive delta=min(r0,√(eps/(32C))) works uniformly; full derivation below. No division by N, so zero is included. |
| “elementary disc conversion” in T15 dispatch row | Local `hsq`, `hlen`, `hL2`, `hL2'`, `h5` | PASS | No separate signature or graph node requires an exported elementary-conversion lemma. See disposition below. |
| Remainder of `bpP:p11b:birkhoff-form` and `stepP:p11b:bt-frozen` | T16 `birkhoff_form`, not delivered here | OUTSIDE T15 | Actual transformed physical averages, continuity/integrability derivation, and separate beta symmetry remain T16 obligations. T15 does not claim those results. |

All new public declarations are covered: exactly one theorem; no new def, abbrev, structure, instance or public helper theorem. `hi` and `he` are legitimate premises of the explicitly conditional, separately named conversion theorem approved in the design. They must be proved by the physical consumer, and are not accepted here as a proof of the physical Birkhoff theorem. The unused `hr` and `hmu` remain verbatim as required; no additional premise was introduced. In fact hr follows from hr0 and hrr, while the conversion itself also works on a nonpositive-mu0 parameter interval.

## Definitions, norm and proof soundness

Definition classification: **no new definitions**. The local lets are concrete arithmetic objects: delta is a positive minimum, N is the existing Pi/product max norm of (p,q), and L is the existing square-root-of-sum slow length. No selection, junk fallback or altered norm instance is introduced. The imported slow-length adapter is exactly √Σ(q_j²+p_j²); `Phase 2` is a product of two real Pi spaces. `(q,p)` is the correct slow phase order for `assemble I phi p q`; the frozen remainder uses `‖(p,q)‖`, as retained here.

Unfolding HasSecularBirkhoffForm gives precisely the two clauses proved at L67 onward. Integrability is over `[0,2π]^2` with the original P. The literal normalized secularAverage and action `(p_j²+q_j²)/2` are unchanged; the expansion keeps both `1/2` and the full double sum. No symmetry requirement is silently inserted into this predicate.

For any eps>0, C>0 ensures delta>0, delta≤r0 and delta²≤eps/(32C). Each p_j²,q_j²≤N², so L²≤4N². The disc condition gives L²<2delta². Thus

`L⁶ = L² (L²)² ≤ (2delta²)(4N²)² = 32delta² N⁴`,

and `C L⁶ ≤ (32C delta²)N⁴ ≤ eps N⁴`.

This is a valid sharper estimate than the blueprint's factor-64 route. It is not a changed constant in the public signature. The chosen delta is independent of mu and I, stronger uniformity than the pointwise frozen existential requires. No nonzero-phase restriction excludes the origin.

## Inline conversion and consumer disposition

Design L62 expressly says: “Proof-step rows name a local proof fragment in the listed theorem/package, not a new theorem”. Its node table L130–136 assigns the Birkhoff theorem and bt-frozen step across T15/T16; it contains no separate elementary-disc graph row. The actual graph record L31211–31233 is “The frozen clauses”, with no frozen anchor. Its literal conclusion includes physical continuity, average identification and separate symmetry in addition to the arithmetic conversion. T16 consumes the exported conditional predicate theorem after establishing those inputs, as required explicitly by design L257: “Apply T15 only afterwards.” Therefore no additional public arithmetic lemma is required by the present contract. Do not mark the whole physical graph step complete solely from this package.

## Notes, errata and deviations

N1 (existing design scheduling note, nonblocking): design L216 says “frozen definitions only”, but FrozenBridge imports Setting to obtain p11c_slowLength. This is exactly the correction already identified by DESIGN-P11C-design-audit-1.md N2 (L28), and also acknowledged by T1's audit. The actual dependency is Setting → FrozenBridge → Birkhoff. Only the imported **frozen** modules are definitions; no provider or frozen theorem is imported, even transitively.

No new suspected pinned-paper erratum or false blueprint assertion was found in the audited conversion. The factor 32 instead of 64 is a proved arithmetic refinement. No production-source, frozen-file, manifest, generated-root or README edit was made by this audit. Kernel/proof closure claims are limited to this conditional helper.

## Independent validation

All commands run from `/root/code/KAM-inp-p11c-t15`; at most one audit Lean/Lake invocation at a time, with `LEAN_NUM_THREADS=1`. No subagents, heartbeat overrides, library-wide build, cache update, or clean was used.

1. Targeted gate build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t15 KAM.Planetary.PlanarTorsion.FrozenBridge
```

Exit **0**, after waiting for the shared gate. Relevant exact output:

```text
[inp-gate] slot 2 acquired 18:24:28 for KAM.Planetary.PlanarTorsion.FrozenBridge
⚠ [9111/9111] Built KAM.Planetary.PlanarTorsion.FrozenBridge (21s)
warning: KAM/Planetary/PlanarTorsion/FrozenBridge.lean:33:5: Variable name `hr` is not explicitly referenced.
warning: KAM/Planetary/PlanarTorsion/FrozenBridge.lean:33:31: Variable name `hmu` is not explicitly referenced.
Build completed successfully (9111 jobs).
```

The wrapper executes `nice -n 5 lake build`. Additional replayed unused-variable warnings came from KAM.Kepler.Energy (hm,hκ), KAM.Planetary.Poincare.Chart (hm,hκ), and KAM.Kepler.Mass (hκ,hw,hm); no build errors.

2. Exact-signature and application probe:

A Python comparison of the full declaration header against standalone signatures L547–560 printed `Signature byte equality: True`. The scratch file `.lake/abi-scratch/T15Audit.lean` imports only FrozenBridge, copies that exact signature under `KAM.Planetary.t15AuditExactSignature`, and proves it using:

```lean
exact hasSecularBirkhoffForm_of_sixth_order P V r C mu0 hr hC hmu P0 Omega beta hi he r0 hr0 hrr
```

This checks application to every explicit binder in order against the literal signature/frozen-definition conclusion. Provider/frozen-theorem type-equality and seal-copy probes are otherwise **not applicable**: this package exports no provider or frozen theorem implementation.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T15Audit.lean
```

Exit **0**, exact output:

```text
'KAM.Planetary.hasSecularBirkhoffForm_of_sixth_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.t15AuditExactSignature' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.FrozenBridge
```

Exit **0**. Complete output:

```text
replaying KAM.Planetary.PlanarTorsion.FrozenBridge
```

One invocation, covering the sole new module (there are no additional new lemma modules).

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted stale generated root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (822 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The root was not regenerated. The module system, frozen guard and all 144 frozen ABI hashes pass. This known generated-file exception and the existing Setting dependency documentation note account for PASS WITH NOTES.

5. Static checks:

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output, exit 0. `git diff --check inp...HEAD` produced no output, exit 0. The new file has 118 total lines (below the 1500 LOC cap), the required copyright/module/public-import/docstring/public-section structure, and no forbidden proof escape, resource override, or EuclideanSpace token. A declaration scan found exactly `hasSecularBirkhoffForm_of_sixth_order`. A search of all KAM Lean sources found that public short name only at FrozenBridge L31, with no root-namespace duplicate/shadow.

A recursive source-import walk found 65 KAM modules in the closure, no `KAM.Provider.*`, and no frozen theorem module. All 48 imported frozen modules are under `Defs`; thus there is no DRAFT_SORRY theorem or SEALED theorem import to inspect. Direct imports are Mathlib, Setting and frozen HasSecularBirkhoffForm. The broader existing Setting closure is infrastructure, not a provider bypass.

Input SHA-256:

```text
c9bf3543fd1e70364ec545b40e32e3dcd19086032d5a11309d0e7aaee06da7c7  KAM/Planetary/PlanarTorsion/FrozenBridge.lean
34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079  /root/code/KAM-inp/.drafts/design/P11CSignatures.lean
```


## Final scope and cleanup

The signature probe and its local logs were deleted after their receipts were transcribed here. Final `git diff --check inp...HEAD` and `git diff --no-index --check /dev/null docs/tracks/P/audits/T15-audit-1.md` both exit 0 with no output. Final status contains only the new report and the pre-existing untracked T15-handoff.md. No tracked repository file was changed. Remaining uncertainty is consumer applicability: the future T16 proof must establish hi/he for its actual transformed perturbation; this audit neither implements nor independently validates that future assembly.
