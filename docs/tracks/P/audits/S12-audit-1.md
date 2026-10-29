# S12 independent package audit

Verdict for **both anchors: PASS WITH NOTES**. The ordinary library proofs are seal-ready: exact frozen-type checks and prospective seal bodies pass, with no additional hypothesis and no nonstandard axiom. The quarantined provider files are still empty stubs, and both manifest entries remain `DRAFT_SORRY`. This report does not claim that either frozen anchor is already sealed. Integration package Q must install the wrappers before sealing. The other note is the explicitly permitted stale generated root.

## Scope and authority

Audited worktree `/root/code/KAM-inp-p14-s12`, HEAD `52942a186338dc0c7bb81b9cfe462f59e57cfa34`, against `inp` at `bea4e8e486c920ad0f51758913e31756dd9e9554` using the full `git diff inp...HEAD`. The diff adds CitedMasses (62 lines), Safety (279), and Uniqueness (94). S12 itself is commit `52942a18`; Safety and Uniqueness are inherited S11/S10 changes, inspected here as part of the full diff and the seal chain. The supplied handoff was an existing untracked file and was preserved.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, S12-handoff.md, P14-LEAN-DESIGN.md (especially node table, S0–S12, Q, and seal recipes), both P14 design audits, `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`, track-P statement §P-SECULAR-BOX, blueprint-P/parts/p14b-secular-box.tex, and the two frozen theorems and relevant frozen definitions. The user's explicit output path overrides the generic brief's MAIN-worktree destination.

No production, frozen, manifest, generated, or provider file was edited. Temporary probes and logs were confined to `.lake/abi-scratch/` and removed after recording results. Only this report is an audit-created persistent file. No state-changing git command was run.

## Exact types and prospective seals

| Frozen anchor | Ordinary proof | Verdict | Evidence |
|---|---|---|---|
| `KAM.Planetary.secularBoxSafety` (`planetary.d25.secularBoxSafety.v1`) | `KAM.Planetary.sb_safety` | PASS WITH NOTES | Exact type and copied frozen declaration with prospective body pass; Q wrapper remains to be installed. |
| `KAM.Planetary.secularBoxAtCitedMasses` (`planetary.d25.secularBoxAtCitedMasses.v1`) | `KAM.Planetary.sb_cited` | PASS WITH NOTES | Exact type and copied frozen declaration with prospective body pass; Q wrapper remains to be installed. |

The scratch imported both frozen theorem modules and CitedMasses, then checked:

```lean
example : type_of% @KAM.Planetary.secularBoxSafety := @KAM.Planetary.sb_safety
example : type_of% @KAM.Planetary.secularBoxAtCitedMasses := @KAM.Planetary.sb_cited
```

It copied each complete frozen theorem telescope and conclusion under `S12Audit.prospective_<anchor>`, replacing only the proof with:

```lean
by exact KAM.Planetary.sb_safety saturn mu hsaturn hmu w0 hw0
by exact KAM.Planetary.sb_cited w0 hw0
```

These are the handoff's ordinary-library terms. All six explicit Safety binders and both Cited binders match, in order. The solution, uniqueness, regularity, conserved quantities, AMD bound, eccentricity bound, and every-phase radial/gap/barycentric clauses are preserved literally. The copied declarations' axiom lists exclude `sorryAx`, even though the probe also imports the still-draft anchors.

For every SIGNED public declaration introduced by the full diff (`sb_unique`, `sb_safety`, `sb_cited`), the probe also copied the original signature-file declaration with a proof applying the real theorem to its own binders, and checked `example : type_of% @signed_<name> := @KAM.Planetary.<name>`. All passed. Token comparison also found `sb_cited` and `sb_unique` identical to the signature text apart from whitespace; `sb_safety` omits only the redundant second `: ℝ` annotation on the upper interval endpoint, with identical elaborated type. No binder, carrier, constant, quantifier, or conclusion was weakened. `sb_unique` drops the competitor regularity premise exactly as approved in the design; the frozen wrapper retains it.

## Node and declaration ledger

Names below are in `KAM.Planetary`. Internal step rows are proof obligations of their parent, as specified by the design; they need no standalone public theorem.

| Node / declaration | Lean realization | Verdict | Reason |
|---|---|---|---|
| `bpP:p14:sb-cited` | `sb_cited`, CitedMasses:30 | PASS | Exact signed/frozen rational specialization of ordinary `sb_safety`. |
| `stepP:p14:sb-ci-1` | CitedMasses:60 | PASS | Closed interval certificate and positive mu discharged by `norm_num`; supplied w0/hw0 only. |
| Cited decimal identity; blueprint `stepP:p14:sb-ci-2` | `sbCited_mass_identity`, CitedMasses:26 | PASS | Literal `(4773/5000000)*(476/1591)=357/1250000`; closed `norm_num` proof. This step is absent from the design node table but its conclusion is established. |
| `bpP:p14:sb-safety` | `sb_safety`, Safety:156 | PASS | Exact signed/frozen statement; ordinary assembly from predecessors. |
| `stepP:p14:sb-th-1` | private `sbSafety_actions`, Safety:53 | PASS | Both fast actions strictly between required rational bounds; mass endpoints and axis bounds used. |
| `stepP:p14:sb-th-2` | private `sbSafety_amd`, Safety:94 | PASS | Chart identities and initial eccentricity bounds yield strict initial AMD bound. |
| `stepP:p14:sb-th-3` | private `sbSafety_mem`, Safety:111 | PASS | Derives initial S membership; no S-membership assumption on the anchor. |
| `stepP:p14:sb-th-4` | Safety:188–190, `sb_global` | PASS | Derives all-time solution, S membership, action and AMD conservation. |
| `stepP:p14:sb-th-5` | Safety:192–194, `sb_unique` | PASS | Same initial value, open convex U; unused competitor-regularity premise intentionally retained. |
| `stepP:p14:sb-th-6` | private `sbSafety_ecc`, Safety:129; application at 210–212 | PASS | Conserved action/AMD and chart relation give e<3/20. |
| `stepP:p14:sb-th-7` | Safety:229, `sb_smooth_prop` | PASS | Produces actual frozen SecularRegular including integrability and differentiability. |
| `stepP:p14:sb-th-8` | private `sbSafety_bridge`, Safety:151 | PASS | Actual bodyVector/ellipsePhase coordinate identity by extensionality. |
| `stepP:p14:sb-th-9` | private `sbSafety_rad`, Safety:142; 231–242 | PASS | Initial axis intervals transported by conservation; rational radius endpoints. |
| `stepP:p14:sb-th-10` | Safety:243–247 | PASS | Lower Saturn radius minus upper Jupiter radius is at least 399/200. |
| `stepP:p14:sb-th-11` | Safety:249–275 | PASS | Both index orders, Sun–planet and planet–planet, via barycentric difference identities and triangle inequalities. |
| `bpP:p14:sb-unique` | `sb_unique`, Uniqueness:60 | PASS | Exact signed helper; no regularity premise on competitor. |
| `stepP:p14:sb-un-1` | Uniqueness:69,78–88 | PASS | Agreement at zero; relative closure follows from both solutions' continuity. |
| `stepP:p14:sb-un-2` | private `sbUnique_local`, Uniqueness:32; 71–77 | PASS | Continuity puts competitor in open S near agreement, then ordinary ODE uniqueness. |
| `stepP:p14:sb-un-3` | Uniqueness:89–91 | PASS | Preconnectedness of convex U propagates the nonempty agreement interior to all U. |
| private arithmetic helper | `sbSafety_lt_of_sq`, Safety:38 | PASS | Nonnegative comparison endpoint and square inequality imply strict inequality. |
| private positive weights helper | `sbSafety_hm`, Safety:44 | PASS | Case split on two actual weights, using positive Saturn interval. |
| private AMD summand helper | `sbSafety_gamma_lt`, Safety:83 | PASS | Algebraic chart premises imply Gamma<c(1-d); not an assumed final theorem. |

This covers all 18 nodes the design table maps to the three diff modules, every new public declaration, and all new private theorem declarations. The unsigned extra export is a mass identity, not a renamed graph theorem with a weaker conclusion. Search of KAM found its short name only in CitedMasses; there is no reused public helper name or harmful root shadow.

## Definitions, assumptions, and chain

There is **no new `def`, `abbrev`, `structure`, or instance** in any of the three added files. Local proof `set` bindings denote the agreement set, positions, etc., rather than exported replacement objects. No fallback or junk-value construction is introduced.

The actual frozen `jupiterSaturnWeights` is `![1,saturn]`; SecularInputBox has positive actions, nonnegative Gamma below each action, the two axis intervals and the two eccentricity upper bounds. `exactSecularHamiltonian` is the frozen normalized secular integral, not a replacement Hamiltonian. `IsHamiltonianSolutionOn` requires actual differentiability and HasDerivAt; SecularRegular includes integrability and differentiability; PairBounds quantifies every distinct pair including the Sun. These definitions are reused literally. The proof derives the needed safety region and guards rather than exploiting total division, integral, square-root, or derivative defaults.

The recursive local-KAM import closure of CitedMasses contains 78 modules and all designed S0–S11 modules: Numerics, Chart, Covariance, Region, ParametricIntegral, Smooth, Rotation, Field, SlowFlow, GlobalFlow, Uniqueness, Safety. It contains **no Provider module and no Frozen theorem module**, so no DRAFT_SORRY or cross-provider dependency is hidden. Frozen imports in this chain are definition modules only.

S12 imports S11 and S0 directly. It repeats the closed rational certificates instead of projecting `sb_numerics`; this is mathematically equivalent and introduces no hypothesis. Safety similarly uses closed arithmetic where convenient. The designed analytic, rotation, reduced-flow, quadrature and uniqueness predecessors remain in the actual proof chain. In particular Safety derives the input premises for `sb_global` from hw0; it does not ask for an orbit, conservation, regularity, or the final bounds as input. Its retained unused hmu is required by the exact frozen interface. The stronger helper's unused competitor-regularity input is also deliberate.

## Independent checks

All Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. The targeted build used the mandated compile gate, whose inner command applies nice. No clean, update, cache download, broad rebuild, resource-budget override, or package edit was performed.

```text
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s12 KAM.Planetary.SecularBox.CitedMasses
exit 0
[inp-gate] slot 1 acquired 22:10:26 for KAM.Planetary.SecularBox.CitedMasses
⚠ [9123/9124] Replayed KAM.Planetary.SecularBox.Safety
warning: KAM/Planetary/SecularBox/Safety.lean:157:60: Variable name `hmu` is not explicitly referenced.
Build completed successfully (9124 jobs).
```

The job count includes the snapshot's already-built dependency jobs; this was a targeted module build.

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S12AuditProbe.lean
exit 0
'S12Audit.prospective_secularBoxSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
'S12Audit.prospective_secularBoxAtCitedMasses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_cited' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sbCited_mass_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An initial version of the SIGNED-signature harness omitted arguments when applying the three theorems inside their explicit binders; that run exited 1 with application type mismatches. Correcting the harness to apply the in-scope binders produced the successful run above. The exact-type and prospective frozen seal tests passed in both runs; this was not a package defect.

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.CitedMasses KAM.Planetary.SecularBox.Safety KAM.Planetary.SecularBox.Uniqueness
exit 0
replaying KAM.Planetary.SecularBox.Uniqueness
replaying KAM.Planetary.SecularBox.Safety
replaying KAM.Planetary.SecularBox.CitedMasses
```

The single invocation replayed all three changed ordinary modules. No implemented provider module exists to add to that invocation.

```text
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
exit 1
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1029 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The only lint failure is the explicitly permitted stale generated root. Module format, frozen-anchor integrity and all 144 elaborated ABI hashes pass. The nice setting and thread limit are inherited by the ABI subprocess; it ran after kernel replay had exited.

Static checks: all three modules have copyright, `module`, public imports, module documentation and public sections. Their line counts/max character widths are respectively CitedMasses 62/100, Safety 279/100 and Uniqueness 94/99. No forbidden proof escape, resource override, or EuclideanSpace occurs in these files. The inherited ParametricIntegral module has only a linter-option setting, not a resource override. Public declarations are namespaced; remaining Safety/Uniqueness helpers are private.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
exit 0; empty output

git diff --check inp...HEAD
exit 0; empty output
```

## Findings, limitations, and errata

1. **Integration note, not missing S12 mathematics:** both `KAM/Provider/Planetary/SecularBoxSafety.lean` and `.../SecularBoxAtCitedMasses.lean` contain headers/module documentation only. There is no actual `KAM.Provider.Planetary.secularBoxSafety` or `...secularBoxAtCitedMasses` export to inspect or kernel-replay. P14 design lines 400–408 assign wrappers to separate package Q. This audit verifies the handoff's ordinary terms and copied frozen bodies as explicitly permitted by the seal-key focus; the provider import/declaration and final manifest transition remain Q integration work. Do not interpret PASS as proof of the present frozen `by sorry` bodies.
2. **Permitted generated-root note:** record the exact lint result above; the root was not regenerated in this report-only audit.
3. No suspected pinned-source defect, blueprint falsehood, extra anchor premise, or mathematical implementation deviation was found. The earlier design-audit F1–F5 concern other P14 contracts and were closed by design audit 2; neither audit identified a defect in these two root signatures. The decimal-mass claim here is the pinned blueprint/statement's model instance, not a claim about observationally exact physical masses or full Newtonian dynamics.
4. This is an S12 seal-key audit with full branch-diff review, not a replacement for every predecessor's own statement audit. It independently checks the inherited Safety/Uniqueness signatures and proofs needed here, the ordinary import chain, actual axiom closure, and kernel replay. No new source research or source repair is asserted.

Closeout: the report has balanced code fences and no trailing whitespace; all 18 scoped design-node identifiers are present. Final status contains only this new report and the pre-existing untracked S12-handoff.md. Protected-path branch diff and whitespace checks remain empty. Audit scratch files were deleted.
