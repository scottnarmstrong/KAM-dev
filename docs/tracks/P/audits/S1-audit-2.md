# S1 independent package audit 2 — delta audit

Overall verdict: **PASS WITH NOTES** (generated-root lint exception only). **F1 is closed**: the two exported corollaries supply exactly the missing positive lower product and positive radius. The only hygiene exception is the generated root, expressly permitted by the audit brief. No frozen anchor is delivered or sealed by S1; provider/frozen-type and seal-body probes are inapplicable.

## Scope and comparison

Worktree and report destination: `/root/code/KAM-inp-p14-s1`. Audited HEAD: `a4e1937e7dd563f86b777e29d2aa9c59269f91f2`; `inp` at comparison: `ea31a1aa7688d687938216c4d39a75e247356cb4`. Read the governing AGENTS.md, PLAN.md, DECISIONS.md, package audit brief, S1 AUDIT FOCUS, round-1 report, Round 2 fix, original signature, relevant P14 design/audit rows, blueprint/packet contracts, Track P secular statement and frozen chart definitions/theorem interfaces. The explicit user destination overrides the brief's generic main-worktree destination.

`git diff inp...HEAD` contains Chart.lean and the round-1 audit/handoff documents. `git diff e48bd0cd HEAD` contains exactly **19 additions, zero deletions**, in Chart.lean only. These append two theorem declarations before the existing namespace/module terminators. A byte comparison deleting that sole block recovers the entire baseline file exactly; the original `sb_chart`, its signature and every prior proof are byte-unchanged. This delta audit retains the round-1 PASS results for those proofs and independently reruns module validation.

## Findings and declaration ledger

All names below are in `KAM.Planetary`; source path is `KAM/Planetary/SecularBox/Chart.lean`.

| Node / declaration | Verdict | Reason |
|---|---|---|
| bpP:p14:sb-chart / sb_chart, lines 51–139 | PASS | Original exact signature and proof retained; missing source clauses now exported by the two named corollaries. |
| stepP:p14:sb-ch-a | PASS, unchanged | Original radicand/root/eccentricity/Gamma algebra retained. |
| stepP:p14:sb-ch-b | PASS, unchanged | Original Cauchy–Schwarz and positive Jacobian retained. |
| stepP:p14:sb-ch-c | PASS, unchanged | Original squared identity, root sign and radius identity retained. |
| stepP:p14:sb-ch-d | PASS; F1 closed | Existing non-strict bounds plus the two new strict positivity exports give the complete literal conclusion. |
| sb_chart_axis_mul_one_sub_pos, lines 143–149 | PASS | Exactly `0 < secularAxis m w i * (1 - planeLength (secularEccVector w i))`. |
| sb_chart_radius_pos, lines 153–158 | PASS | Exactly `0 < planeLength (ellipsePosition m w i F)`. |
| private sbChart_planeLength_orbitalUnit, sbChart_planeSq_orbitalUnit, sbChart_identity | PASS, unchanged | No changes to the three previously audited private helpers. |

Both new telescopes have precisely `m : Fin 2 → ℝ`, `hm : ∀ i, 0 < m i`, implicit `w : Phase (2+2)`, and `hw : ∀ i, 0 < fast w.2 i ∧ 0 ≤ secularGamma w i ∧ secularGamma w i < fast w.2 i`. The selected `i`, and `F` for radius, instantiate the original universally quantified conclusions. No added hypothesis, endpoint exclusion, new instance, conclusion-shaped premise or carrier substitution occurs. In particular Gamma=0 remains allowed.

The lower-product proof unfolds the frozen axis `(Lambda/m)^2`, proves it positive from the existing action/mass premises, projects `e<1` from `sb_chart`, and applies `mul_pos`. The radius proof projects the existing lower radial bound and applies transitivity with that positive product. Thus both missing inequalities are proved rather than postulated. Their documentation explicitly cites the parent and step-d nodes.

Blueprint `blueprint-P/parts/p14b-secular-box.tex:149` requires “$\pl{q_i}>0$”; line 161 requires “$\pl q\ge a(1-e)>0$”. Packet `docs/graph/P/packets/P-p14b.nodes.md:713,844` has the same literal requirements. The new exports meet both clauses under the original hypotheses. The original design/signature's conjunction remains narrower by itself, as noted in round 1; its compatibility is preserved and the package now supplies the missing clauses through separately named public results. No design-file edit was made by this auditor.

## Definitions and static hygiene

No new `def`, `abbrev`, structure, instance or alternate object is introduced. The frozen definitions and the original local aliases are unchanged; there is no new fallback or junk-value reliance.

Whole-KAM declaration searches find exactly one declaration of each new short name, both inside `namespace KAM.Planetary`, with no root shadow. The module has **162 lines** (under 1500); the maximum line length is **99 Unicode characters**, with zero lines over 100. The header, `module`, public imports, module docstring and `public section` remain intact. No forbidden proof escape, EuclideanSpace, resource override or new import occurs. A recursive local KAM import check visits 48 modules and finds no provider or frozen theorem module, hence no DRAFT_SORRY import.

`git diff --check inp...HEAD` exits 0 with empty output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exits 0 with empty output. Chart SHA256: `26cd6716a754e9f2584964794d6083b40ff7412d84997e0838f96bac2b2168ad`.

## Independent validation

All Lean/Lake checks are serial, with `LEAN_NUM_THREADS=1` and `nice -n 5` (the prescribed build wrapper applies nice internally). No external campaign process is interrupted. Scratch probes and logs live only in `.lake/abi-scratch/` and are removed after recording their results.

1. Targeted incremental build (not a clean/library rebuild):

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s1 KAM.Planetary.SecularBox.Chart
   [inp-gate] slot 2 acquired 18:35:33 for KAM.Planetary.SecularBox.Chart
   Build completed successfully (9094 jobs).
   exit 0
   ```

2. Exact signature and public export axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S1Audit2.lean
   'KAM.Planetary.sb_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sb_chart_axis_mul_one_sub_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sb_chart_radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   The probe copies the original P14Signatures.lean sb_chart telescope under a fresh name and applies `KAM.Planetary.sb_chart m hm hw`. Two additional `example` declarations explicitly spell out the requested complete telescopes and assign the fully qualified new exports with `@`, verifying public visibility, all premises and exact conclusions without additional assumptions. All three public results use only the permitted axioms.

3. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Chart > .lake/abi-scratch/S1Audit2-leanchecker.log 2>&1
   replaying KAM.Planetary.SecularBox.Chart
   exit 0
   ```

4. Full repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/S1Audit2-lint.log 2>&1
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (822 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   Exit 1 is solely the generated-root exception explicitly permitted by the audit brief. The root is left untouched. The ABI subprocess inherits the single-thread setting and nice priority. No warnings or errors were emitted by the targeted build, signature probe or kernel replay.

Closeout: all prescribed checks completed independently; audit scratch probe/logs were deleted. Final repository status contains only the new `docs/tracks/P/audits/S1-audit-2.md`. Protected-path and production-file diffs remain empty, and report whitespace checks pass. No state-changing git command was used.

## Errata, uncertainty and limits

No new suspected pinned-source or blueprint mathematical defect, hypothesis deviation or default-heartbeat design signal was found. F1 was an omitted exported elementary consequence, now repaired without altering the original theorem. The existing design-signature omission is documented above; it is no longer an unpaid S1 package conclusion.

This verdict covers only the S1 chart algebra and its five owned graph rows. It does not prove either secular frozen theorem, regularity/integrability of the averaged Hamiltonian, or dynamical continuation. The auditor edits only this report; generated/frozen files, manifests, production Lean and existing reports/handoffs remain untouched.
