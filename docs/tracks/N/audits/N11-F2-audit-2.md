# N11-F2 independent audit 2

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-nseal`.
Audited HEAD: `155e0f29ccd48ac507062c886ce04563946670b5`.
Comparison `inp`: `23a055ed6eaa23e4cc5d0d57c6f3c7c42cabdd32`.

## Verdict

**PASS WITH NOTES for N11-F2 and the F2-C1 integration delta. F2-C1 is CLOSED.**
Both F2 modules implement their amended signed contracts. The positive-c premise is now
explicit in the authorized iterative contract, and is proved from source scale positivity
in both normal-form branches. Its callers discharge those scales from the frozen theorem's
own data and the positive perturbation parameter. No added frozen premise or assumed
canonicity/confinement estimate was found.

The frozen `partialConvex_nekhoroshev` passes the fresh exact-type, binder-applied seal,
axiom and kernel checks recorded below. This F2 audit does **not** overturn the independent
seal audit's Q1 quarantine failure: `KAM.lean:1278` still imports its provider, contrary to
the literal AGENTS.md rule 9. The F2 modules themselves have no provider import.
Thus this is an accepted predecessor receipt, not an unconditional all-policy seal verdict.

## Scope and authority

Read AGENTS.md, PLAN, DECISIONS, the external package brief, F2 handoff including round 2,
audit 1, the N11 design row/node table, both design audits, the canonical-map and iterative
blueprint statements/proofs, the track-N statement, frozen partial-convex anchor and its
relevant definitions, and the landed positivity/caller chain.
The user's exact absolute report destination overrides the generic brief's main-worktree
instruction. Only this report is a persistent auditor edit; temporary probes/logs use
`.lake/abi-scratch/` and are removed.

The complete `git diff inp...HEAD` adds only four audit documents, 507 lines:
F2 audit 1 (198), F2 handoff (55), NSEAL-PARTIAL audit 1 (231), and its handoff (23).
No production Lean change appears in this three-dot diff. Therefore the inherited landed
code was inspected directly, rather than treating the empty Lean delta as validation.
Both `ExtFlow.lean` and `CanonicalMap.lean` are byte-identical to commit `1d5683c5`
(the audit-1 code). E1 flow/symplectic correspondence remains outside the F2 proof-review
scope; its proof terms are included in fresh axiom closure and kernel replay.
Downstream review is the requested positivity-discharge delta, not a replacement audit
of all N11 estimates.

External signatures SHA-256:
`fe33b7d1689fdfb8ea66242b975d2b44002039fc4aa25378313afc4bd59a8aeb`.
Published `docs/tracks/N/design/N11-SIGNATURES.md` SHA-256:
`e55d3046d41f749bd8ea50b531d189865fcabd13a6ff6e3c957b68ced919881c`.
The external file still has the old iterative signature without hc. The published signature
and `docs/campaign/LANE-N-LOG.md:6–14` explicitly record the 22:45 F2-C1 ruling adding hc
after hSL. This authorized amendment controls the iterative delta; the discrepancy is
reported, not silently normalized. Both signature sources agree on F2's canonical_map.

## Declaration and node ledger

Unqualified names below are in `KAM.Nekhoroshev`. Partial-module locators are relative
to `KAM/Nekhoroshev/Partial/`.

| Node / declaration | Location | Verdict | Evidence |
|---|---|---|---|
| Shared signed `extFlow` | ExtFlow:27 | PASS | Literal Part-5 flow of wfield b.c on Dom(R−ρ,s−σ); body equality by rfl. |
| `bpN:p11:canonical-map`, signed `canonical_map` | CanonicalMap:286 | PASS | Complete type equals both controlling signatures modulo whitespace; fresh copied-type probe elaborates. |
| Auxiliary `canonical_map_core` | CanonicalMap:179 | PASS | Distinct helper proves all signed clauses except canonicity without hc; does not replace signed export. |
| Clause (a), both holomorphic maps and both images | CanonicalMap:228 | PASS | flow_b at times ±1, same intermediate U and image domain. |
| Clause (a), angle/fast/slow displacements | CanonicalMap:233 | PASS | Component MVT with Cauchy bound; exact V/ρ, V/(eσ), b.c V/ρ. |
| Clause (b), integer shifts and reality | CanonicalMap:244,278 | PASS | Differentiated periodicity and uniqueness; actual real field and flow_real. |
| Clause (c), derivative | CanonicalMap:273 | PASS | flow_c on full gauge interior, exact factor 2V/(ρσ). |
| Clause (d), canonical identity | CanonicalMap:326 | PASS | E1 symplectic at proved/forwarded positive c, restricted to U. |
| Clause (e), inverses and smaller-domain image | CanonicalMap:263 | PASS | Both inverse identities and Φz∈U; no omitted inverse image on U. |
| `stepN:p11:it-map`, `iterative` | Iterative:44,94 | PASS | Exact published amended type; hc forwarded to canonical_map. |
| Normal-form positivity | NormalFormInduction:445,611,738 | PASS | nnf_c_pos derives hc from ExtNFHyp radii; both Case A and Case B discharge it. |
| M1/M2 callers | Nonresonant:368; Resonant:366 | PASS delta | nf receives existing ExtNFHyp, no new positivity premise. |
| N block construction | Block:240,278,308 | PASS delta | Positive radius from block_data; w=d(μ)/4>0; bundle constructed explicitly. |
| Frozen/provider partial theorem | provider:53; frozen anchor:48 | PASS type/discharge | No hc or surrogate positivity premise at frozen level; exact seal probe. Quarantine Q1 is separate. |

The design node table (`N11-LEAN-DESIGN.md:209`) assigns exactly
`bpN:p11:canonical-map` to the F2 theorem. No additional mapped step is missing.
The source's scaled displacement is proved internally by flow_a; the additional slow bound
V/(16kσ) follows from slowLoss and positive losses. The signed interface deliberately exports
the component bounds and derivative statement; the actual iterative consumer derives its
SL-based slow bound. No consumer needs an unprovided map clause.
The design-audit-1 inverse-image finding and the consumer map-interface findings are closed
in the landed exports, as described by design audit 2. Audit-1 F2-C1 was the only F2 package
failure; the old generated-root lint note is separately rechecked below.

## F2-C1 discharge, through the frozen source premises

1. `blueprint-N/parts/p11b-partial-nf.tex:4–6` fixes a “starting radius” r_B>0 and
   “physical slow width” w>0 and defines c=2π/(w/r_B)². The added hc is faithful scalar
   positivity, with no hidden analytic or canonical content. The source keeps c fixed
   through subsequent radius losses, and the Lean iteration does likewise.
2. `Iterative.lean:47` assumes precisely the authorized hc; line 94 passes it to
   canonical_map. `IterativeMap.lean:281` records that same scalar premise as NitHyp.nit_c;
   the bundle is constructed from the explicit iterative binders at Iterative:90–91.
3. The only production application of iterative is `nnf_iter` at
   NormalFormInduction:324. Its explicit hc is discharged at both of its applications:
   `nnf_step_at` at :611 and `nnf_caseB_step` at :738 use `nnf_c_pos ha`.
   The proof at :445–449 unfolds c and uses only ha.radius_pos, ha.slow_width_pos and π>0.
   Case A (including zero subsequent steps) and Case B are both covered.
4. `nf` at NormalForm:606 has the unchanged ExtNFHyp and smallness inputs. It chooses
   nnf_caseA/nnf_caseB, adding no hc binder. `nonresonant` and `resonant` pass their existing
   ExtNFHyp directly to nf. No assumption about the resulting transformation is smuggled
   into their source bundles.
5. `block_setting` at Domain:44–45 is literally the chosen r and w=d(μ)/4, where
   d(μ)=μ^partialDriftExponent n. In Block:263 d is positive by Real.rpow_pos_of_pos hμ.
   `block_data` supplies hr>0 at Block:274–275; it is proved from a positive covering
   radius at BlockData:226–228, ultimately positive numerical constants from source data.
   Block:278–279 proves w>0. The bundle at :308–329 sets radius_pos:=hr and
   slow_width_pos:=hwpos. The transport lemma also consumes these proved hr/hwpos at :335;
   it does not add a new external premise. The nonresonant/resonant branches receive
   this same hNF at :392 and :408.
6. Provider:90–97 constructs PartialData from exactly the frozen explicit premises.
   Positive g and m come from hdef (HasDefiniteFastPart), positive ρ and Mc are frozen
   binders, and μ>0 is the frozen quantified premise. Provider:100–105 proves positive
   d and initial numerical radius; threshold supplies the smallness comparisons, and
   provider:126,143 applies block. Neither PartialData nor the frozen/provider theorem
   has a new hc, positive block width, or conclusion-shaped premise.

Consequently every positivity premise used in this resolution is either an original source
premise already in ExtNFHyp/frozen data or a proved numerical consequence. The old c=0
standalone iterative counterexample is outside the explicitly amended contract; this audit
does not assert a degenerate c=0 canonical theorem.

## Definition classification and proof review

| F2 definition | Whole-carrier interpretation |
|---|---|
| `extFlow` | Exact signed wrapper. Generic flow chooses a solution on [−1,1] if one exists and otherwise returns its initial point (Canonical/Flow:54). F2 proves SmallField and gauge-interior membership before invoking trajectory facts; the fallback supplies no proof obligation. |
| private `extGauge` | Genuine continuous linear equivalence diag(σ⁻¹,ρ⁻¹), with positive losses guaranteeing units; norm equals scaled product max norm. |
| private `fastCLM` | Literal real-linear fast-coordinate projection on the full product carrier. |
| private `slowCLM` | Literal real-linear ordered q,p projection on the full product carrier. |

No other F2 def/abbrev/structure or global instance occurs. No custom norm is installed.
The proof constructs SmallField from vf and holomorphy, proves geometric gauge-interior
inclusions, and uses actual trajectories for MVT. Empty base sets only make guarded domain
assertions vacuous. Reality uses the real restriction on its open domain. There is no
conclusion-shaped premise or reuse of a public helper short name; production searches find
one extFlow, one canonical_map and one canonical_map_core, all in the intended namespace.

## Fresh validation

All auditor Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`;
the compile gate applies nice internally. No heartbeat/recursion override, library clean,
cache update or protected edit was used.

**Build.** Exact command:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-nseal KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev
```

Exit 0. Gate: `[inp-gate] slot 2 acquired 15:33:55 for KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev`.
Final output: `Build completed successfully (3369 jobs).`
This targeted dependency closure includes both F2 modules and the complete positivity chain.
Inherited tactic/unused-variable warnings were replayed; no F2 error or sorry warning.

**Fresh probe.** Exact command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11F2Round2.lean
```

Exit 0; no errors or warnings. Copied complete published canonical_map and iterative types
under fresh names, supplied all explicit binders in order by exact, and checked each with
`example : type_of% @audit_name := @actual_name`. Checked extFlow body by rfl and independently
proved c>0 from positive b.rB,b.w. Checked frozen/provider type equality and copied the full
frozen declaration under auditSeal with its exact 23-binder seal body. Mechanical comparison
of the FULL types (including every let and conclusion) matches the published signatures
modulo whitespace; canonical_map also matches the external signature.
Two preliminary scratch runs failed due to probe-generation errors (stopping at an internal
let assignment, then omitting `open KAM.NormalForm`); these were fixed in scratch only.
Only the final clean run is counted as validation.

Complete axiom output from the final run:

```text
'KAM.Nekhoroshev.canonical_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.canonical_map_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.iterative' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.nnf_c_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.nnf_step_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.nnf_caseB_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.nonresonant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.resonant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.block' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.auditSeal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.partialConvex_nekhoroshev' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Kernel replay.** One invocation, exact command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.ExtFlow KAM.Nekhoroshev.Partial.CanonicalMap KAM.Nekhoroshev.Partial.Iterative KAM.Nekhoroshev.Partial.NormalFormInduction KAM.Nekhoroshev.Partial.NormalForm KAM.Nekhoroshev.Partial.Nonresonant KAM.Nekhoroshev.Partial.Resonant KAM.Nekhoroshev.Partial.Block KAM.Provider.Nekhoroshev.PartialConvexNekhoroshev KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev
```

Exit 0. Complete output:

```text
replaying KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev
replaying KAM.Provider.Nekhoroshev.PartialConvexNekhoroshev
replaying KAM.Nekhoroshev.Partial.Block
replaying KAM.Nekhoroshev.Partial.Resonant
replaying KAM.Nekhoroshev.Partial.Nonresonant
replaying KAM.Nekhoroshev.Partial.NormalForm
replaying KAM.Nekhoroshev.Partial.NormalFormInduction
replaying KAM.Nekhoroshev.Partial.Iterative
replaying KAM.Nekhoroshev.Partial.CanonicalMap
replaying KAM.Nekhoroshev.Partial.ExtFlow
```

**Source lint / frozen guard / ABI.** Exact command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 0. Complete output:

```text
check_lean_modules: PASS (1336 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No generated-root exception was needed. Lint acceptance of the SEALED-provider root
import does not discharge the stricter prose quarantine condition.

**Static/import/protected checks.** F2 closure: 89 project modules, 23 frozen modules,
all registered SEALED, no provider or frozen theorem. Provider closure: 180 project modules,
40 frozen modules all registered SEALED, no frozen theorem and no other provider.
F2 source scan found no forbidden proof escapes, resource overrides or EuclideanSpace.
ExtFlow: 32 lines, maximum width 98; CanonicalMap: 333 lines, maximum width 100.
Both satisfy the module/interface/docstring/public-section convention.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty;
`git diff --check` passes. Final report whitespace check and probe cleanup are recorded
in the completion paragraph below.

## Notes, errata and limits

No new suspected pinned-publication erratum or mathematical blueprint defect was found.
The positive-c amendments are explicitly authorized source-positivity clarifications;
the extra ExtFlow module is the disclosed shared-definition split, used by F1 rather than
a duplicate definition. The stale external iterative signature is superseded by the
published 22:45 amendment and should not be used as the landed iterative contract.

The independent seal audit's Q1 persists: the generated root imports the SEALED provider,
while rule 9 permits only the frozen anchor. This audit neither repairs that generated file
nor treats lint acceptance as an owner ruling. NSEAL-PARTIAL A1 is addressed by the recovered
F2 audit-1 receipt plus this fresh closure of its sole consumer failure; no blanket approval
of all other packages or downstream I/P results is implied.

Completion: report whitespace check produced no diagnostics; `git diff --check` passed.
All auditor-created N11F2 scratch probes/logs were deleted. Final git status contains
only this untracked report; tracked sources and protected paths are unchanged by the auditor.
No commit, checkout, reset, staging operation, or other state-changing git command was used.
