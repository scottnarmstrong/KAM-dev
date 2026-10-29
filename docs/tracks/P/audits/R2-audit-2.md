# R2 independent package audit 2 — delta audit

Overall verdict: **FAIL for the full requested R2 convergence contract (residual F1)**.
The compact common-neighbourhood analytic-flow part of F1 is now proved. The new theorem
passes statement/proof inspection, but neither its conclusion nor its finite-cover proof
establishes uniform Picard convergence on that assembled neighbourhood. The twelve original
declarations remain unchanged and retain their round-1 PASS. This is a completeness finding,
not a counterexample to the new analytic-flow theorem. No frozen anchor/provider is delivered
or seal-ready here; the signed Hamiltonian/symplectic theorem remains R3's responsibility.

## Scope, authority and delta

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-r2`.
HEAD: `79e90422b35bfd0cb1b00a8cfdf7051122f6dbf4`.
Round-1 comparison commit: `0182f219`.
Read AGENTS.md, PLAN.md, DECISIONS.md, the package-audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the AUDIT FOCUS in
`docs/tracks/P/audits/R2-handoff.md`, round-1 audit, `.drafts/handoff-R2.md` including its
Round 2 fix, P11C design and design audit 1, supplied signatures, Track P statement,
blueprint Part 11b, frozen Phase/HamiltonianVectorField definitions, and ODE solution and
uniqueness interfaces. This delta audit includes AnalyticCompact.lean as expressly requested
by the user, extending the original focus's Analytic.lean-only boundary.

`git diff 0182f219 HEAD` and `git diff 0182f219...HEAD` contain exactly one new file:
`KAM/Planetary/PlanarTorsion/RealFlow/AnalyticCompact.lean`, **124 insertions, 0 deletions**.
Thus “only appends” is true as additive package development: a separate new module is added;
no lines were appended to or changed in Analytic.lean. All previously tracked files, including
all twelve existing declarations, are byte-unchanged relative to 0182f219. The round-2 handoff's
approximate “135 lines” is stale; the actual committed module is 124 lines.

The required full `git diff inp...HEAD` was also inspected. At comparison `inp` was
`b8e023179635e643629844d102983e478c955c1e`; the diff contains eight added files,
1,171 insertions: the six RealFlow modules (including inherited R1 Local.lean), audit 1,
and the original handoff. Git warns of multiple merge bases, selecting
`ec23b835c48802c9afb977ff01f72600b82cca7f`; the other is
`e1a6d79dbc71cb183d0c04add2a0bbc8f2ac0b59`. This warning does not change the exact delta check.

SHA-256 inputs:

- Analytic.lean: `4b12359786595ba0e43887b162fb70e8dc3bea4baf23eb593f83c8ea14a9be4a`.
- AnalyticCompact.lean: `d5c3e0e348b1ff2af4ebeaf9becea34d73d580d4625d8d59d7895a26e7684a90`.
- P11C-LEAN-DESIGN.md: `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36`.
- `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`:
  `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079`.

The user's exact absolute output path overrides the generic brief's main-worktree destination.
Only this report is a lasting repository edit. No source repair, state-changing git, generated
root, README, frozen or manifest edit was made. Probe files are confined to this worktree's
`.lake/abi-scratch/` and removed after use.

## F1 reassessment: compact analytic flow proved; common Picard convergence unpaid

**Closed portion.** AnalyticCompact.lean:38–44 quantifies an arbitrary compact `K ⊆ W`
before choosing `U`, `T`, and one flow. Its assumptions are exactly openness of W, analyticity
of f on W, compactness of K and containment K ⊆ W. The conclusion includes
`IsOpen U`, `K ⊆ U`, `U ⊆ W`, `T > 0`, joint real analyticity on `Ioo (-T) T ×ˢ U`,
and initial value and actual `IsSolutionIn f W` for every y in U. No existence,
complexification, Lipschitz, convergence or uniqueness premise has been added.

The finite subcover is constructed at :50–51. The induction at :52–64 gives a strictly
positive common time, including the empty-compact case (empty cover and time 1).
At :65 C1 regularity is derived from analyticity, rather than assumed. At :68–75,
U ⊆ W follows from the local solution identity at time zero. The two-sided uniqueness
argument at :77–85 proves agreement on the entire common interval. At :97–107 the chosen
flow equals a single analytic local flow on an open product neighbourhood of each point;
this is genuine joint analyticity, despite the arbitrary chart selection. The final
solution proof transports the derivative using eventual equality on the open time interval.

**Residual material finding.** The user explicitly asks for “a common neighbourhood and time
with uniform Picard convergence and joint real analyticity.” Design :47 assigns
“compact common parameter domains, uniform Picard bounds and derivative convergence”; :208
assigns “real analytic parametric Picard convergence on common neighbourhoods”; :253 says
“use compactness to obtain a common neighbourhood, and prove analytic Picard convergence there.”
The new conclusion :41–44 contains no sequence of iterates, recurrence, convergence predicate,
or common error estimate. Its internal proof :45–48 uses only the existential analytic-flow
interface of `p11c_analytic_flow_fin`, which has already discarded the Picard witnesses and rates.
It patches solution limits, not the iterations or their convergence bounds. The handoff itself
states: “Not exposed: Picard iterates/uniform convergence as a statement”. Inspection also finds
no such compact-uniform proof internally.

The existing `P11cPicardData.lim_dist` (PicardComplex.lean:208–211) proves the estimate
`2 * M * T / 2 ^ k`, and `lim_unif` (:220–228) proves uniform convergence on **one**
`p11cDom n c T r` for supplied local data. They are valid local results. They do not identify
Picard iterates of the original real field over the finite union U, identify their limits
with the selected common flow, or assemble a uniform rate on that union. Merely having these
local convergence proofs in a dependency is not a proved compact-uniform convergence statement.

A concrete remaining target is: with U,T and the same analytic flow, define
`u₀(t,y)=y`, `uₖ₊₁(t,y)=y+t • ∫₀¹ f(uₖ(σ*t,y)) dσ`; prove these iterates are valid on the
common domain and `TendstoUniformlyOn (fun k => fun (t,y) => uₖ(t,y))
(fun (t,y) => Φ t y) atTop (Ioo (-T) T ×ˢ U)`, or a proved equivalent finite-chart formulation.
One possible route is to retain each chart's complexification/Picard data, identify its real
iterates with this recurrence, use uniqueness to identify the limits, and take the maximum
of the finitely many geometric constants. This is a proposed repair, not an audited proof.
Absence of a public convergence conjunct alone would not fail the “in proof or as export”
criterion; absence of that assembly in both places is what remains unpaid.

This narrows F1 rather than repeating the original missing-compactness diagnosis. Under a
contract asking only for a compact-neighbourhood analytic flow, the mathematical delta would
PASS. The present user explicitly includes uniform Picard convergence, so the complete R2
contract is not satisfied. No design reassignment or weakening is presumed.

## Declaration and consumer coverage

All declaration names below have namespace `KAM.Planetary`. Original lines refer to
Analytic.lean; the new theorem is in AnalyticCompact.lean.

| Node / duty | Declaration | Verdict | Reason |
|---|---|---|---|
| R2 coordinate map | `p11cPt` :37 | PASS retained | Original explicit real-linear inclusion unchanged. |
| R2 time coordinate | `p11cPt_zero` :45 | PASS retained | Original theorem unchanged. |
| R2 space coordinates | `p11cPt_succ` :48 | PASS retained | Original theorem unchanged. |
| R2 space inclusion | `p11cSp_p11cPt` :51 | PASS retained | Original theorem unchanged. |
| R2 time scaling | `p11cTimeScale_p11cPt` :54 | PASS retained | Original theorem unchanged. |
| R2 reality | `p11cIsReal_realInclusion` :62 | PASS retained | Original theorem unchanged. |
| R2 reconstruction | `p11c_eq_realInclusion` :65 | PASS retained | Original theorem unchanged. |
| R2 integral/ODE bridge | `p11c_hasDerivAt_of_integral_eq` :70 | PASS retained | Original theorem unchanged. |
| R2 local analytic flow | `p11c_analytic_flow_fin` :95 | PASS retained | Local complex Picard construction unchanged. |
| R2 Hamiltonian field | `p11c_hamField_analyticAt` :206 | PASS retained | Actual frozen field, unchanged. |
| R2 Phase adapter | `p11cPhaseEquiv` :215 | PASS retained | Original continuous linear equivalence unchanged. |
| R2 Hamiltonian flow | `p11c_analytic_hamiltonian_flow` :221 | PASS retained | R3 analytic/solution input unchanged. |
| R2 compact analytic flow / local e-ode bridge | `p11c_analytic_flow_compact_nbhd` :38 | PASS as stated | Common U,T; uniqueness gluing; joint analytic flow; source premises only. |
| R2/U5 common-domain Picard convergence | No compact-uniform declaration or internal assembly | FAIL, residual F1 | Local convergence exists; convergence over the assembled U is not proved. |
| R3 signed symplectic local flow | `real_analytic_hamiltonian_local_flow` | Outside delta | R2 supplies analytic/solution clauses; symplecticity still belongs to R3. |
| T9 compact displacement / time-one map | `bpP:p11b:flow`, `fl-bd`, `fl-an` | Outside delta | Common short-time analytic input now available; continuation and cubic estimates still belong to T9. |

No R2 declaration is SIGNED in the supplied signature file, so frozen/provider exact-type
and seal-body probes are inapplicable. The new helper does not claim to prove the full
symplectic signed theorem or the entire global-domain external fact in blueprint Part 11b:20.
Round 1's R3 projection compatibility is retained by byte identity; it is not counted as a
newly rerun signature probe.

For parameters, arbitrary finite n permits the augmented autonomous field
`(parameter,state)' = (0,f(parameter,state))` after a finite-coordinate continuous linear
identification. K can then range over both parameters and initial states. The new theorem
has no restriction excluding that application and no fixed-parameter choice of T. The
coordinate transport and proof that the parameter coordinates remain constant are not
separate exports here; downstream application must supply them. This is not proof of T9 or
an additional finding against the generic compact-flow statement.

## Definition and import classification

There is no new public def, abbrev, structure or instance in the delta. The proof-local U
is the actual finite union of chosen open balls. The proof-local Ψ chooses a chart containing
y and falls back to y outside U (:87–88). On U the chart exists; uniqueness makes its selection
irrelevant on the displayed time interval. The fallback is harmless because every analytic
and ODE claim is restricted to U and that interval. No claim depends on a junk branch.
Original definitions `p11cPt` and `p11cPhaseEquiv` remain unchanged and retain their intended
coordinate meaning on their full carriers.

The recursive KAM import closure now contains 47 modules, no provider, and exactly ten frozen
modules: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC,
IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, Planetary.Phase.
Each is SEALED in the manifest. No DRAFT_SORRY anchor is imported. The added uniqueness
interface is the actual two-sided `gen_uniqueness`, with analytic-to-C1 premises proved locally.
Mathlib is the external library dependency.

## Independent verification

All auditor Lean/Lake commands are serialized, with `LEAN_NUM_THREADS=1` and niceness 5.
The build uses the mandated compile gate, whose wrapper runs `nice -n 5 lake build`.
No heartbeat/recursion override, clean/update/cache command, full-library rebuild, or agent
was used. Waiting for the compile gate was allowed and did not trigger another Lean job.

### Targeted build — PASS, exit 0

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-r2 KAM.Planetary.PlanarTorsion.RealFlow.AnalyticCompact
```

Exact output:

```text
[inp-gate] slot 1 acquired 21:24:18 for KAM.Planetary.PlanarTorsion.RealFlow.AnalyticCompact
Build completed successfully (9093 jobs).
```

The job count is Lake's dependency graph report, not a request to rebuild the library from scratch.

### Public theorem axiom probe — PASS, exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/R2Audit2.lean
```

The probe imports AnalyticCompact and prints every public theorem from Analytic plus the
new theorem. Exact output:

```text
'KAM.Planetary.p11cPt_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPt_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cSp_p11cPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cTimeScale_p11cPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cIsReal_realInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_eq_realInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_hasDerivAt_of_integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_analytic_flow_fin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_hamField_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_analytic_hamiltonian_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_analytic_flow_compact_nbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay — PASS, exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.RealFlow.AnalyticCompact KAM.Planetary.PlanarTorsion.RealFlow.Analytic KAM.Planetary.PlanarTorsion.RealFlow.PicardData KAM.Planetary.PlanarTorsion.RealFlow.PicardComplex KAM.Planetary.PlanarTorsion.RealFlow.PicardOp
```

Exact output:

```text
replaying KAM.Planetary.PlanarTorsion.RealFlow.PicardOp
replaying KAM.Planetary.PlanarTorsion.RealFlow.PicardComplex
replaying KAM.Planetary.PlanarTorsion.RealFlow.PicardData
replaying KAM.Planetary.PlanarTorsion.RealFlow.Analytic
replaying KAM.Planetary.PlanarTorsion.RealFlow.AnalyticCompact
```

### Repository lint — exit 1; inherited failures, scoped source checks clean

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exact output:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-p11c-r2/KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77:101
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (894 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated-root diagnostic is the brief's permitted exception and was not repaired.
The frozen AmdConfinement line is a separate inherited failure, already present in audit 1,
and is not covered by that exception. Its bytes are unchanged; frozen files are read-only.
Thus full repository lint did not pass. Module-system validation, frozen-anchor guard and
all 144 ABI hashes did pass. The new compact module introduces no lint diagnostic.

### Static, namespace and protected-path checks — PASS

- New module: 124 physical lines, maximum line width 99 Unicode characters. Original
  Analytic.lean: 262 lines, maximum width 99. Both satisfy the 1,500-line and 100-column caps.
  Copyright, module declaration, public imports, module docstring and public exposed section
  are present. The cap of 100 is a line-width cap; the fix's 124 total lines are permitted.
- Comment-masked forbidden-token scan of both audited modules: no `sorry`, `admit`, `axiom`,
  `unsafe`, `opaque`, `EuclideanSpace`, or `set_option`. No resource-limit override is present.
- Declaration-site searches throughout KAM confirm all twelve original short names and the
  new `p11c_analytic_flow_compact_nbhd` each have exactly one definition/theorem site.
  There is no new public short-name collision, root declaration, instance or harmful shadow.
- `git diff --numstat 0182f219 HEAD` prints only
  `124  0  KAM/Planetary/PlanarTorsion/RealFlow/AnalyticCompact.lean`.
  `git diff --name-status 0182f219 HEAD` reports only that added file.
  `git merge-base --is-ancestor 0182f219 HEAD`: exit 0.
  A direct `git show 0182f219:<path>` byte comparison of Analytic.lean also passes.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: no diff, exit 0;
  only Git's already-recorded multiple-merge-base warning.
- `git diff --check inp...HEAD`: exit 0, same Git warning only.
- `git diff --check` and
  `git diff --no-index --check /dev/null /root/code/KAM-inp-p11c-r2/docs/tracks/P/audits/R2-audit-2.md`:
  exit 0. Report text has no control characters other than newline.

## Errata, deviations and limits

No new pinned-paper erratum, frozen-statement defect, or contradictory blueprint fact was
found. Primary PDFs were not re-audited; this is the requested delta Lean-package audit
against the supplied design, signature and blueprint contracts. The outstanding deviation
is precisely the residual uniform-convergence assembly in F1 above. The common analytic
neighbourhood and overlap-gluing defects of round 1 are resolved.

No implementation change was attempted. Build/axiom/kernel checks validate the submitted
claims; they do not add the missing convergence conclusion, prove R3 symplecticity, T9
continuation/displacement, or seal a frozen planetary headline. The local-to-compact
convergence argument described above remains proposed mathematical work. The original
round-1 lint issues are reported separately from this material completeness finding.

Final cleanup: auditor probe `.lake/abi-scratch/R2Audit2.lean` removed after successful use.
Final status contains only `?? docs/tracks/P/audits/R2-audit-2.md`; no tracked modification.
The exact requested report path and final whitespace/control-character checks passed.
