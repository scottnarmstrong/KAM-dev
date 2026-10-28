# S1 independent package audit 1

Overall verdict: **FAIL — incomplete literal S1 graph contract (F1).** The implemented `KAM.Planetary.sb_chart` has exactly the supplied signature and its existing proof is sound on inspection. It omits the explicit positive-radius conclusion required by `bpP:p14:sb-chart` and `stepP:p14:sb-ch-d`; that conclusion is also absent from the inline proof. The user's AUDIT FOCUS explicitly requires failure for an absent graph-row conclusion. This is a small completeness repair, not a counterexample to the implemented theorem.

Frozen anchors: **none delivered by S1; seal readiness not applicable.** The future `secularBoxSafety` and `secularBoxAtCitedMasses` anchors are not proved or sealed by this package. No provider/type-of-frozen or seal-body test applies to this ordinary helper.

## Scope and authority

Worktree: `/root/code/KAM-inp-p14-s1`. Audited HEAD: `ab0cbaf78cee6fa1ec54b11520104d8a67d6d578`; comparison `inp` at inspection: `de67213e831cc1bc77872f080fce92c2e2a7d0a0`. `git diff inp...HEAD` adds only the 143-line `KAM/Planetary/SecularBox/Chart.lean`. Production audit scope is exactly that file. The user's explicit absolute report destination overrides the generic brief's main-worktree destination.

Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, S1-handoff.md and its AUDIT FOCUS, P14 design (node table, row S1, proof plan and signature appendix), both P14 design audits, relevant Track P statement text, blueprint Part 14b, packet `P-p14b.nodes.md` rows for all five owned nodes, the original P14Signatures.lean sb_chart contract, the relevant frozen secular definitions and theorem interfaces, and the imported Kepler planar API. Earlier design approval is evidence about intended contracts, not a substitute for this completeness check.

## F1 — Missing positive radius in the literal source/graph contract

Blueprint `blueprint-P/parts/p14b-secular-box.tex:149` requires “$\pl{q_i}>0$”; line 161 explicitly concludes “$\pl q\ge a(1-e)>0$ ($a>0$)”. The packet parent `SOURCE_CONCLUSION` at line 713 ends with `¦q_i¦>0`; the step-d `SOURCE_CONCLUSION` at line 844 requires `a(1-e)<=¦q¦<=a(1+e) and ¦q¦>=a(1-e)>0`.

`Chart.lean:51–67` exports the radius identity and two non-strict bounds, but no `0 < planeLength (ellipsePosition m w i F)` or `0 < secularAxis m w i * (1 - planeLength (secularEccVector w i))`. Lines 118–119 establish `haxis`, lines 133–135 establish `hlen`, and lines 136–139 return only the five stated F-dependent conjuncts. Neither missing strict inequality is established as an inline local obligation. This is precisely the absent-conclusion case singled out by the handoff.

The inherited signature at `/root/code/KAM-inp/.drafts/design/P14Signatures.lean:412–424` and design appendix at `P14-LEAN-DESIGN.md:944` have the same omission. Design audit 2's `sb_chart` row says “positive radius follows from positive mass/action and e<1”. That mathematical implication is correct; it does not establish the literal inline obligation in this implementation. The handoff's assertion that all sb-ch-d obligations are complete therefore overstates the delivered slice.

Suggested repair: retain the exact existing sb_chart signature, and actually establish the strict lower product and positive radius inline from `haxis`, `he1`, and `hlen` (or supply a distinct public corollary covering the omitted source clauses, with ownership recorded). If the orchestrator elects to extend the ordinary signature, synchronize the design/signature and consumers explicitly. No frozen statement or definition change is needed or authorized here. This auditor made no production repair.

## Node and declaration ledger

All names below are in `KAM.Planetary`.

| Node / declaration | Lean locator | Verdict | Evidence |
|---|---|---|---|
| bpP:p14:sb-chart / sb_chart | Chart:51–139 | FAIL | Exact design signature; literal source positive-radius clause absent (F1). Existing conjunction is proved. |
| stepP:p14:sb-ch-a | Inline Chart:69–112 | PASS | hR > 0; hkpos and hk1; hGeq and hsqR discharge slow/radicand identities; hvsq/he2 give e²=1−k²; hk2 gives e²<1 and he1; positive k selects the correct square root; Gamma identity proved by field algebra. |
| stepP:p14:sb-ch-b | Inline Chart:106–117 | PASS | abs_planeDot_le and unit orbital length give both signs of x≤e; hJ unfolds the literal Jacobian; hJpos and hJ0 give lower bound and positivity. |
| stepP:p14:sb-ch-c | Chart:40–49,120–135 | PASS | sbChart_identity expands the two components with s=x/(1+k); k>0 discharges denominator; squared equality hsq and nonnegative length/positive Jacobian justify root selection; positive axis removes absolute value on scaling. Normalized vector is q/a because haxis>0. |
| stepP:p14:sb-ch-d | Inline Chart:136–139 | FAIL | Both non-strict radial bounds and both signs of Cauchy–Schwarz are present; positive lower product and positive radius absent (F1). |
| private sbChart_planeLength_orbitalUnit | Chart:31–33 | PASS | Trigonometric unit length for every real F. |
| private sbChart_planeSq_orbitalUnit | Chart:35–37 | PASS | cos²+sin²=1 component identity. |
| private sbChart_identity | Chart:40–49 | PASS | Pure conditional algebra helper, distinctly named and private; its relations are derived at call site, not assumed as source premises. |

## Definition and hypothesis classification

No new `def`, `abbrev`, `structure`, instance, or alternative carrier is introduced. Local `set` aliases L,G,k,xi,eta,R,v,e,u are literal expressions in the frozen objects; they introduce no fallback or junk-value reliance. Imported `secularRoot` is 1−Gamma/Lambda; `secularEccVector` is the frozen nonnegative-root scale of (xi,eta); `secularAxis` is (Lambda/m)²; Jacobian and ellipsePosition unfold literally. Positive L, positive radicand, positive 1+k, and positive mass/axis guard every division, root and sign-sensitive step used here. Circular points Gamma=0 remain included.

The full telescope matches the original design up to whitespace. `hm : ∀ i, 0 < m i` is already a signature/source premise, used only at Chart:119 for axis positivity. `hw` contains only the stated positive-action and ellipticity premises. There are no added premises, conclusion-shaped fields, enlarged constant dependence, or norm substitutions. The planar length remains the frozen Euclidean planar length on `Fin 2 → ℝ`, not the Pi norm.

## Independent validation

All Lean/Lake invocations are serial for this audit, with `LEAN_NUM_THREADS=1`, `nice -n 5`, and default proof resources. The shared compile gate may be occupied by unrelated campaigns; no external process was interrupted.

1. Targeted gated build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s1 KAM.Planetary.SecularBox.Chart
   [inp-gate] slot 1 acquired 17:50:44 for KAM.Planetary.SecularBox.Chart
   Build completed successfully (9094 jobs).
   exit 0
   ```

   This is the prescribed targeted incremental build, not a clean/library rebuild. No warnings were emitted.

2. Signature and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S1Audit1.lean
   'KAM.Planetary.sb_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
   'S1Audit.signature_copy' depends on axioms: [propext, Classical.choice, Quot.sound]
   'S1Audit.radius_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   `signature_copy` copies the complete original sb_chart telescope under a fresh namespace/name and uses exactly `KAM.Planetary.sb_chart m hm hw`. Independent whitespace-normalized comparisons against both the original signature and design appendix return `True`. There is only one new public theorem, so this covers every required public axiom inspection.

   The diagnostic `radius_positive` proof projects the existing conjunction, unfolds secularAxis and proves it positive using `(hw i).1` and `hm i`, rewrites by the radius identity, then applies `mul_pos` to positive axis and positive Jacobian. It has no extra premises. This confirms F1 is an omitted literal obligation, not an analytic/source obstruction; an auditor-created scratch corollary does not complete the delivered package.

3. Kernel replay (one invocation for the sole owned module):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Chart > .lake/abi-scratch/S1Audit1-leanchecker.log 2>&1
   replaying KAM.Planetary.SecularBox.Chart
   exit 0
   ```

4. Static hygiene and protected paths:

   ```text
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   exit 0; empty output
   git diff --check inp...HEAD
   exit 0; empty output
   ```

   Recursive inspection of local KAM imports found 48 modules, no provider module and no frozen theorem module. Consequently no DRAFT_SORRY/SEALED theorem import exception is needed. All imported frozen definitions remain literal and unchanged. A whole-KAM word search for `sb_chart` and `sbChart_*` found only this module's declaration/reference lines: no duplicate public short name or root declaration shadow. There is an explicit `namespace KAM.Planetary` around all four declarations.

   Chart.lean has 143 total lines, copyright/authors, `module`, public imports, module docstring and `public section`. There are no new definitions needing expose attributes. No forbidden tokens (sorry/admit/axiom/unsafe/opaque/EuclideanSpace/set_option), resource overrides, or oversized module were found in the scoped file.

5. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/S1Audit1-lint.log 2>&1
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (822 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   Exit 1 is solely the generated-root exception explicitly allowed by the audit brief. It is recorded rather than repaired. The scoped module passes hygiene; no generated or frozen file was edited. The ABI subprocess inherited `LEAN_NUM_THREADS=1` and nice priority and ran after the other Lean commands completed.

## Source/blueprint defects, uncertainties and deviations

F1 is an inherited design-signature/implementation completeness omission against a correct elementary blueprint requirement. Both earlier design audits' sb_chart rows acknowledged that radius positivity follows, but the actual proof does not establish the literal missing clause. No suspected pinned-paper mathematical erratum was identified; this blueprint lemma explicitly labels its formulas as our direct calculation, rather than a verbatim LP17 theorem. No counterexample, heartbeat failure, new hypothesis or carrier deviation was found.

This report validates only S1 chart algebra and its five owned graph rows. It does not establish smoothness of the averaged Hamiltonian, integrability, dynamical continuation, any provider, or either secular frozen theorem. No production source, generated root, frozen anchor, manifest, or pre-existing handoff was edited. Only this report persists; auditor-created scratch files are removed at closeout.

Snapshot hashes:

- Chart.lean: `8f12a12f64d4f619c826fbbd5897da343895aad4f62d6fbd27108a9299450699`.
- Original P14Signatures.lean: `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88` (the audited sb_chart slice matches the current appendix; historical whole-file hashes in older design audits are not treated as current).
- Blueprint Part 14b: `f14536c948f27bc9ccb330b5df0b482846696aa7ea10283d42ee2569be2d0ae7`.

Closeout: required build, exact-signature/axiom probe, kernel replay, and lint completed independently. Protected-path comparison remains empty. Report whitespace and code-fence checks pass. Repository status contains only this new report and the preserved pre-existing untracked S1-handoff.md. No state-changing git command was run.
