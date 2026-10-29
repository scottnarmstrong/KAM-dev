# B17 independent package audit 1

**Overall verdict: PASS WITH NOTES for the B17 slice.** The signed declarations match the canonical signatures; displacement, inverse-gamma and the pointwise power combination are proved with no added source premise. No blocking mathematical finding. The notes concern the permitted stale generated root, inherited build warnings, the changing comparison branch, and the explicit B20 uniformity boundary. No frozen anchor is proved or made seal-ready by this package.

## Scope and comparison

Audited only `KAM/Planetary/WeakKAM/Displacement.lean`, as instructed by `B17-handoff.md`. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package-audit brief, handoff, P11B design and both design audits, canonical signatures, relevant p11a4 statements/proofs, track-P statement, graph packet, and upstream interfaces/definitions. The user's exact worktree report path overrides the brief's generic main-worktree destination.

- HEAD: `ad0f5483090fd77980b64ebffb91d4ee617517b2`.
- Owned commits: `43527e96` (draft), `ad0f5483` (proof). `git diff HEAD~2 HEAD` contains only Displacement, 283 added lines; its protected-path diff is empty.
- Module SHA256: `95fb4b481f4e5f41e84175a4b68ad93dcc0a6b3f9bd0eb7ac64f5353396213ee`.
- Live canonical `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean` SHA256: `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63`. The design-audit historical hashes are snapshots, not the authority substituted for this live file.

Initially `git diff inp...HEAD` showed seven new files / 1330 lines: Displacement and the six inherited B16 Tori modules. B15 is already in that comparison base. The corresponding fixed base is `59edd171dd710945df5da652f50dd7269ea990bf`; its protected-path diff to HEAD is empty.

The shared `inp` advanced during this audit to `b327bf598423eddc6c28cac6a6f60dbeb38944d0`, after merging B16. `git merge-base --all` then reports both `77aeaaedefb8c519763a10dda787e95a8499c402` and `59edd171dd710945df5da652f50dd7269ea990bf`. A subsequent literal three-dot comparison warns `multiple merge bases, using 77aeaaedefb8c519763a10dda787e95a8499c402` and shows 35 files, including 20 inherited generated-root import additions. Thus the latest literal protected-path three-dot diff is **not empty for KAM.lean**; frozen files, manifest and README remain unchanged. Those root imports predate B17 (history includes `59edd171`, `d460bad0`, `6fd85111`, `8dfde479`). They are comparison ancestry noise, not an owned B17 change. Both comparisons and the isolated owned range were inspected; no unrelated package is certified by this report.

## Declaration and graph coverage

All names below are in `KAM.Planetary`. Locators without a filename refer to Displacement. Each signed header/body or structure field list was compared mechanically with the canonical file; all six are text-identical after removing theorem proof bodies. Fresh Lean probes additionally checked the definitions by `rfl`, the two theorem types/application bodies, and the record in both directions.

| Node / role | Declaration / locator | Verdict | Evidence |
|---|---|---|---|
| displacement definition | `selectionDelta`, L26 | PASS | Exact adapted-schedule Q0 times max of the two block coefficients; signed definition. |
| displacement coefficient | `selectionCDelta`, L29 | PASS | Exact explicit cDelta, including 128, pi, T0, and strip power; signed definition. |
| inverse coefficient | `selectionCGamma`, L32 | PASS | Exact cGamma with both branches and outer factor 2; signed definition. |
| gi-branches positivity | `disp_rho_pos`, L39 | PASS | Derives positive real rho from rho=1 or 2; no extra premise. |
| gi-branches first branch | `disp_inv_A`, L41 | PASS | Literal first-branch inverse upper bound; beta<=1 is the source condition. |
| gi-branches second branch | `disp_inv_B`, L65 | PASS | Exact inverse identity; exponent is -(mu+1)/rho, with positive bases. |
| `bpP:p11a:gamma-inverse` | `gamma_inverse`, L87 | PASS | Signed type; inverse min split combines the two branches with cGamma. |
| `stepP:p11a:gi-branches` | L41–109 | PASS | Complete in the helpers and proof, rather than a separately exported node theorem. |
| dp-tel angle restriction | `disp_angle_le`, L116 | PASS | Restricts the complex bound to real theta using limit_real and the isometric real inclusion. |
| dp-tel action restriction | `disp_action_le`, L127 | PASS | Same restriction for the action block; no lost base-action term since the complex limit is centered at zero. |
| dp-size auxiliary | `disp_Xi_ge`, L142 | PASS | Proves Xi>=2 from its explicit formula, enough for the requested Q0 bound. |
| `stepP:p11a:dp-size` | `disp_scalar`, L158 | PASS | All three bounds: Delta<=Q0/128, Delta<=2^-18, Delta<=cDelta sqrt(epsilon)/gamma. |
| `stepP:p11a:dpc-comb` | `selectionDelta_le_power`, L213 | PASS | Unsigned export states the literal pointwise Delta inequality, including cDelta*cGamma and exact beta exponent. |
| output record | `SelectionDisplacement`, L235 | PASS | Signed parent and all six fields exact; same inherited witnesses throughout. |
| `bpP:p11a:displacement` | `displacement`, L246 | PASS | Signed theorem constructs Nonempty output from d, positive admissible epsilon and source perturbation. |
| `stepP:p11a:dp-tel` | L255–279 plus L116–136 | PASS | Constructs L via limit_torus, consumes E2 from wbud_exported, and combines by Prod.norm_def. |
| `bpP:p11a:displacement-power` uniform export | B20 `displacement_power` | OUTSIDE B17 | Design package table L243/L246 assigns only pointwise powers to B17 and uniform powers to PolynomialBudget/B20. No closure claim for this full node here. |

The B17 slice is complete under that explicit package allocation: displacement, dp-tel, dp-size, gamma-inverse, gi-branches and pointwise dpc-comb. The global node table's `displacement_power` row must not be read as a B17 uniform-theorem completion receipt.

## Definitions and hypotheses

All three new definitions are honest total real formulas on their declared carriers. `selectionDelta` uses the epsilon-adapted schedule, including s0=sqrt(2 epsilon/(n C1)) and epsilon0=2 epsilon; it does not revert to the nonvanishing fixed-radius construction. Its total meaning outside positive admissible epsilon is the same signed formula; no theorem relies on a junk branch there. `selectionCDelta` and `selectionCGamma` are explicit scalar coefficients, with positivity of all relevant denominators/bases obtained from standing data when used. There are no new abbrevs, norm instances, substitute carriers or fallback constructions.

`SelectionDisplacement` is an output structure extending the entire `SelectionTori` witness. Its bound fields are conclusions populated by `displacement`; it is not a standing input that assumes the difficult proof. The conditional restriction helpers take `SelectionLimit`, use its actual limit bounds, and have distinct implementation names. The public source-facing theorem constructs that limit/torus itself through `limit_torus`. No conclusion-shaped source hypothesis or circular displacement premise was found.

At L171–203 the size proof establishes both max coefficients <=1/128, Q0<=2^-11 from weighted admissibility and Xi>=2, and the exact equality Q0/128=cDelta sqrt(epsilon)/gamma using free_radius. At L41–109 the beta exponent manipulation is valid for beta>0, mu>=1 and rho>0. The canonical pointwise hbeta premise supplies beta<=1; beta<=M is already standing data. No wider constant dependence was introduced.

The P11A constant bridge is explicit upstream: `FiniteMeasure.lean:79–87` proves `selectionCDio_eq` against `p11CDio`; L120–129 applies `power_law` with margin 2*gamma and the actual gammaStar. B17 uses exactly that `selectionCDio`/`selectionGamma` formula, not a free unspecified constant. `selectionCDelta` depends on n, mu, tau, strip, C1; `selectionCGamma` uses the listed geometric/numerical data through selectionChat and loss, without beta or h. Establishing the uniform same-key theorem, positive chosen constants, simultaneous lower budget, and final evaluation witness remains B20's obligation under the revised design F2 ruling.

Consumer inspection: signed `SelectionLipschitz` extends this exact record; `SelectionEvaluationOutput` inherits it through Lipschitz. B18/B19 retain block and scalar bounds, witnesses and adapted radius. B20 has both explicit coefficients and the exported pointwise Delta bound needed for its uniform assembly. That assembly is not assumed or certified here.

## Independent verification

Every Lean/Lake invocation was serial with `LEAN_NUM_THREADS=1` and `nice -n 5`; lint ran only after the probe and kernel replay completed. No resource override, library clean, cache fetch, update or package-directory edit was used.

1. Targeted compile gate, exit **0**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b17 KAM.Planetary.WeakKAM.Displacement
   ```

   Exact concluding output: `Build completed successfully (9214 jobs).` Dependency replay emitted existing unused-variable, unused-simp and deprecation warnings in upstream modules (including Schedule, CutoffTensor/Scale, IterationParam, MaximalStep and Nekhoroshev averaging). These are not B17 diagnostics; no Displacement diagnostic or heartbeat failure was observed. The handoff's clean scoped-module claim does not mean this independent build's entire dependency replay was warning-free.

2. Canonical signature/body and axiom probe, exit **0**, no warnings/errors:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B17Audit.lean
   ```

   The probe imported only Displacement, copied each signed definition under a fresh name and checked function equality by rfl; copied canonical theorem statements and supplied `by exact gamma_inverse d hbeta` / `by exact displacement d epsilon he hsmall f hf` with the actual original binder names; checked `type_of%` assignments; copied the exact signed structure under a fresh name and checked record conversion both ways. There is no provider/frozen seal body for B17, so the provider-vs-frozen probe is not applicable.

   Exact axiom output for **every** explicit new public theorem:

   ```text
'KAM.Planetary.disp_rho_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.disp_inv_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.disp_inv_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.gamma_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.disp_angle_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.disp_action_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.disp_Xi_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.disp_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionDelta_le_power' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.displacement' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation, exit **0**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Displacement
   ```

   Complete output: `replaying KAM.Planetary.WeakKAM.Displacement`. B17 has one module and no provider.

4. Full source lint, exit **1**, solely the explicitly permitted stale-root exception:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1133 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No generated file was regenerated. The guard and ABI subprocess completed successfully; no substantive lint failure was suppressed.

5. Mechanical and import checks:

   - 283 lines; maximum Unicode line length 99; all module/header/import/docstring/public-section requirements present. Definitions are in the exposed public noncomputable section.
   - Forbidden-token/override/EuclideanSpace search in Displacement: no matches. No new ambient norm or type instance.
   - All eight unsigned helper short names searched against all other KAM sources and Mathlib: no other declaration matches. All explicit declarations stay under KAM.Planetary; no root declaration or harmful root shadow is introduced.
   - Recursive project-import walk: no provider, no frozen theorem, and therefore no imported DRAFT_SORRY theorem. The 14 frozen modules in that closure are definitions, each manifest state SEALED: ActionNbhd, ComplexStrip, FrequencyMap, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, RealHamiltonian, SymplecticForm, CircularPoint, CircularTube, and Phase.
   - `git diff --check inp...HEAD`, fixed-base diff check, and `git diff --check HEAD~2 HEAD`: exit 0. The moving-base warning and protected-path comparison exception are disclosed above rather than silently ignored.

## Errata, deviations and limits

No suspected new pinned-source or blueprint defect was found in this slice. Blueprint p11a4:157–186 supplies the exact coefficients, telescoping, sizes and exponent used here. In dp-size the implementation proves the sufficient Xi>=2 rather than separately exporting Xi>=2^(tau+1); this is a valid shorter proof of the same endpoint inequalities. Pointwise max-norm bounds follow the design's explicit pointwise convention and give the stated uniform-in-theta bound without an unguarded supremum.

No B17 mathematical deviation or extra premise found. The known design-audit F1/F2 repairs remain intact at this interface; this report does not re-audit all inherited B15/B16 proofs, their full graph coverage, the later B20 uniform theorem, P11a5 assembly or P-FIXED. The frozen P-FIXED theorem remains outside this proof closure.

Only this report is a repository deliverable. The pre-existing untracked B17 handoff is preserved. The owned scratch probe and its three logs were removed after checks; no B17 audit probe remains. No state-changing git command was run.
