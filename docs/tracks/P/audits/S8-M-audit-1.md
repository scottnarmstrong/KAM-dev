# Independent S8-M package audit 1

Overall verdict: **PASS WITH NOTES**. Scope: the S8-M infrastructure module only; no frozen anchor is sealed or certified by this audit.

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-s8m`. Audited HEAD: `7499b26f33f4217bd1b54602b72627eb12cfec62`; inp: `872a014af58890f96058190624e431a0ed0228a5`; inp-s7r: `d56fb0e3cfdf350b5c04af50801e56a06d35706d`. Both `git diff inp...HEAD` and `git diff inp-s7r...HEAD` contain only the new 626-line `KAM/Planetary/SecularForm/Momentum.lean`. SHA-256: `f59d05ef4a8cc41395d8d87163ab60c3a792adfe49f651d37431824bd1104666`.

Read AGENTS.md, PLAN, DECISIONS, the supplied audit brief, handoff, P statement route item 4, blueprint p8 L89–106 and L182–194, P810 design S8-M allocation and corresponding interfaces, design audits 1–2, and relevant chart/domain/average definitions. The user-specified report path overrides the generic brief's main-worktree destination. Signature authority is `/root/code/KAM-inp/.drafts/design/P810Signatures.lean` (absent locally), SHA-256 `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`, matching design audit 2. Design audits are under `docs/tracks/P/design/`, not `audits/`.

## Statement and proof findings

No material statement or proof defect found. Whitespace-normalized theorem signatures of lemma64, lemma64_coordinates and identification and complete definition commands for momentum, position and modelDelta match the design exactly. Fresh probes use the design theorem text and apply the implemented export to D and hx; separate literal reference definitions check the three equations by rfl. There is no provider/frozen pair, so frozen-type/seal probes are inapplicable; these direct design-type probes test the actual assigned interface.

The derivative argument pays the Kepler-only field computation directly, transports it with pc_dec, and annihilates the other-body angle directions before dividing by positive m_i nu_i. It does not import the interaction Hamiltonian equations with their pair-collision premise. Periodic C1 position gives exact zero momentum mean. Fubini for separated scalar factors and the one-body virial theorem give the cross and diagonal averages; a finite double sum pays the total momentum square. The identification proof cancels the common potential pointwise, proves continuity of the remaining momentum polynomial and integrability on the compact cell, proves the iff, and only then adds averages under the stated integrability guard. No hard step is assumed.

The generic avg_prod/avg_one/avg_two statements are stronger than the continuous source applications. Their lack of integrability hypotheses is supported by the exact Mathlib scalar separated-product theorem (`Mathlib/MeasureTheory/Integral/Pi.lean:79`); it is not an illicit use of unguarded general additive Bochner linearity. avg_sum, avg_apply, intervalIntegral_apply and avg_add carry enough regularity at their uses.

## Declaration inventory

Names are relative to `KAM.Planetary.SecularForm`. Source nodes are `bpP:p8:lemma64`, steps `stepP:p8:l64-a` through `l64-e`, and `bpP:p8:identification`, steps `stepP:p8:id-diff`, `id-avg`, `id-int`. Ancillary helpers implement cuts of those nodes rather than new source theorems.

| Declaration | Line | Verdict | Node / reason |
|---|---:|---|---|
| `momentum` | 35 | PASS | Literal physical momentum block of the product chart; design signature L118–119. |
| `position` | 37 | PASS | Literal physical position block; design signature L120–121. |
| `blk` | 43 | PASS | Literal one-planet coordinate tuple; no extension or choice. |
| `blk_mem` | 45 | PASS | Derives the one-body chart domain from slowDom; p8 L90. |
| `assemble_mem` | 51 | PASS | The chart domain is independent of fast angles; no pair guard. |
| `position_eq_block` | 57 | PASS | Exact product-chart block identity. |
| `momentum_eq_block` | 63 | PASS | Exact product-chart block identity. |
| `position_update_ne` | 69 | PASS | Other-body angle independence; l64-a. |
| `position_update_self` | 73 | PASS | Own-angle block substitution. |
| `momentum_update_self` | 77 | PASS | Own-angle block substitution. |
| `continuous_momentum` | 81 | PASS | Analytic chart continuity on the full source domain. |
| `momSlot` | 103 | PASS | Literal coordinate unit vector in Cartesian momentum space. |
| `hasDerivAt_keplerPart_momentum` | 106 | PASS | Direct kinetic differentiation; potential is constant along momentum lines. |
| `unitAngle` | 166 | PASS | Literal fast-angle unit tangent, zero slow/action components. |
| `assemble_update_eq` | 168 | PASS | Exact affine fast-angle line. |
| `field_eq_sum` | 179 | PASS | Finite coordinate expansion of the source Kepler field. |
| `fderiv_keplerPart_momentum` | 188 | PASS | Differentiability guard converts the directional calculation; independently paid at use. |
| `hasDerivAt_position` | 205 | PASS | pc_dec + product_chart; other blocks vanish; obtains p/(m nu). |
| `avg_prod` | 291 | PASS | Unrestricted scalar separated-product identity from Mathlib integral_fin_nat_prod_eq_prod; total-integral semantics respected. |
| `mean_one` | 303 | PASS | Normalized constant interval integral is one. |
| `avg_one` | 307 | PASS | Separated product specialization; no unproved Fubini premise. |
| `avg_two` | 327 | PASS | Two distinct angle slots; generic scalar product identity. |
| `avg_sum` | 351 | PASS | Continuity supplies integrability on the compact cell. |
| `avg_const_mul` | 357 | PASS | Valid scalar linearity for the total integral. |
| `avg_apply` | 361 | PASS | Continuity supplies integrability before projection through the Bochner integral. |
| `intervalIntegral_apply` | 370 | PASS | Same guarded projection on the finite interval. |
| `pmom` | 381 | PASS | Literal one-body momentum, not a selected surrogate. |
| `ppos` | 385 | PASS | Literal one-body position. |
| `momentum_eq_pmom` | 388 | PASS | Exact product block formula. |
| `continuous_pmom` | 391 | PASS | Continuity derived from chart-domain regularity. |
| `hasDerivAt_ppos` | 396 | PASS | Own-angle specialization of hasDerivAt_position. |
| `ppos_periodic` | 404 | PASS | Exact 2π periodicity from poincare_periodic. |
| `integral_pmom` | 411 | PASS | C1 position plus periodic FTC; m nu nonzero is derived. |
| `mean_planeSq_pmom` | 436 | PASS | poincare_means virial identity, including circular points. |
| `nu_pos` | 442 | PASS | Mass and action positivity are derived/source standing data. |
| `continuous_planeDot_comp` | 451 | PASS | Generic finite polynomial continuity. |
| `avg_momentum` | 457 | PASS | Full-cell zero mean from own-angle zero mean; l64-b. |
| `avg_cross` | 467 | PASS | Independent angle factors and zero mean; l64-c. |
| `avg_diag` | 482 | PASS | Full-cell and one-angle virial means agree; l64-d. |
| `planeSq_sum_eq` | 489 | PASS | Finite double-sum expansion of the physical square. |
| `lemma64` | 497 | PASS | Exact design L123–131: all five conjuncts; l64-a through l64-e. |
| `lemma64_coordinates` | 538 | PASS | Exact design L717–721: other-angle derivative, interval zero mean, interval virial mean. |
| `modelDelta` | 557 | PASS | Literal (2m0)^(-1) sum m_i^4 (Gm0)^2/I_i^2; design L184–185. |
| `perturbation_diff` | 560 | PASS | Exact model difference globally; interaction potential cancels algebraically. |
| `continuous_planeSq_comp` | 568 | PASS | Generic finite polynomial continuity. |
| `avg_add` | 573 | PASS | Integrable first summand and continuous second summand; integrability supplied at use. |
| `identification` | 579 | PASS | Exact design L187–195: continuity, difference average, integrability iff, guarded secular identity. |

## Expanded premise audit

The three source exports share the same outer binders, with no instances or hidden proof bundles. Each row is counted once per export; the Data bundle is expanded below. Source: blueprint p8 L89–99, L182–187, p8 conventions and the design's standing physical data. Generic calculus helpers have their explicit regularity/inequality inputs shown in the inventory; they have distinct names and their inputs are supplied in the source-export proofs.

| Expanded binder / field | Bin | Source / interpretation |
|---|---|---|
| implicit n : Nat | TYPING | Fin n coordinate arity |
| D.G : Real | TYPING | gravitational constant carrier |
| D.m0 : Real | TYPING | central mass carrier |
| D.m : Fin n → Real | TYPING | planetary masses carrier |
| D.hG : 0 < G | STANDING | positive physical constant |
| D.hm0 : 0 < m0 | STANDING | positive central mass |
| D.hm : forall i, 0 < m i | STANDING | positive planetary masses |
| D.hn : 0 < n | STANDING | positive planet count in design Data |
| implicit x : Slow n | TYPING | (xi,Lambda,eta), Fin n real coordinate tuples |
| hx, expanded: forall i, 0 < Lambda_i | SOURCE | w in O_n, positive actions |
| hx, expanded: forall i, (xi_i^2+eta_i^2)/2 < Lambda_i | SOURCE | w in O_n, Gamma_i < Lambda_i |

Counts per source export: SOURCE 2, STANDING 4, TYPING 5, RULED 0, EXCESS 0. The conditional final implication of identification is a source conclusion (p8 L187), not an extra outer hypothesis. There is no coupling, collision, ordering, neighborhood, spectrum or desired-average input. Data fields contain no analytic or spectral result.

## Definition classification

Eight new definitions: momentum, position, blk, momSlot, unitAngle, pmom, ppos, modelDelta. All are literal formulas or coordinate constructions. The three design definitions have exact bodies; the five helpers have the literal meanings in the inventory. There is no choice, if/default fallback, fabricated witness, new Prop assumption bundle or characterization-defined object. Momentum/position/pmom/ppos use the existing total chart formula; all physical regularity and mean claims retain the full chart-domain guard. modelDelta is the design's total rational expression, with physical identities used only at positive actions.

For each of the eight: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS.

## Execution evidence

All auditor-controlled Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No budget override, clean, cache fetch, update or package edit was used.

1. Targeted build (exit **0**):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8m KAM.Planetary.SecularForm.Momentum
   [inp-gate] slot 2 acquired 11:59:12 for KAM.Planetary.SecularForm.Momentum
   Build completed successfully (9125 jobs).
   ```

   The gate wait was honored. Replayed upstream unused-variable warnings: Energy.lean L106 (hm,hκ); Poincare/Chart.lean L212,L247 (hm,hκ); Mass.lean L147,L157 (hκ), L500 (hw), L524 (hm,hκ); Hamiltonian/Algebra.lean L146 (hc); Hamiltonian/Chart.lean L193 (hc); D25.lean L99,L125 (hm), L126 (hw). No Momentum diagnostic.

2. Exact signatures, literal equations and all 39 public theorem axioms (exit **0**):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8MAudit.lean > .lake/abi-scratch/S8MAudit.out 2>&1
   ```

   Probe construction: import Momentum; open the same namespaces/scopes; copy the three named theorem types from the authoritative signature file under `example`, applying `SecularForm.<name> D hx`; copy the three named definition commands under `audit_<name>` and check pointwise equality by `rfl`; append `#print axioms KAM.Planetary.SecularForm.<name>` for each of the 39 theorem declarations enumerated in the inventory. All six examples elaborate without diagnostics. Full axiom output:

   ```text
'KAM.Planetary.SecularForm.blk_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.assemble_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.position_eq_block' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.momentum_eq_block' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.position_update_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.position_update_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.momentum_update_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_momentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.hasDerivAt_keplerPart_momentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.assemble_update_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.field_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.fderiv_keplerPart_momentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.hasDerivAt_position' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.mean_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.intervalIntegral_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.momentum_eq_pmom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_pmom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.hasDerivAt_ppos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.ppos_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.integral_pmom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.mean_planeSq_pmom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.nu_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_planeDot_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_momentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planeSq_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.lemma64' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.lemma64_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_planeSq_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.identification' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation (exit **0**):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.Momentum > .lake/abi-scratch/S8MKernel.out 2>&1
   replaying KAM.Planetary.SecularForm.Momentum
   ```

   All newly introduced lemmas are in that one module; no additional lemma module is omitted.

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/S8MLint.out 2>&1
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (553 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   ```

   Exit **1**, solely for the explicitly permitted stale generated-root exception. Module hygiene, frozen guard and ABI hashes pass; KAM.lean was not regenerated.

5. Static checks: `git diff --check inp...HEAD` exits **0**, no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exits **0**, no output. Both branch comparisons show exactly 626 additions in Momentum and no other tracked changes. Forbidden-token search in Momentum finds no sorry/admit/axiom/unsafe/opaque/set_option/EuclideanSpace. Its full 626-line length is below the 1500-line code cap; copyright, module, public imports, module docstring, `@[expose] public noncomputable section` are present. The 79-module project import closure has **zero providers and zero frozen theorem modules**, so no DRAFT_SORRY theorem is imported. Frozen definitions are consumed literally; no frozen/manifest/generated files are changed.


## Notes, errata and limits

1. The only allowed lint exception is a stale generated KAM.lean. It must remain unedited; no root-import repair is part of this audit.
2. Inherited candidate **E-P8-Fej50**, blueprint p8 L247 and design errata section: Fej04r p.50 prints the coefficient “mu_j^3 M_j^2 / Lambda_j^3” in the momentum derivative relation. Multiplication of nu by the planetary mass requires power four. The present proof uses m_i nu_i correctly. This is an inherited allegation from the locally pinned blueprint/design; no independent PDF re-audit was performed here. It is not a new source finding. No other suspected blueprint defect or implementation deviation was found.
3. This certifies the audited S8-M exports and helpers only. It does not certify any same-jets consumer, any frozen planetary headline, the complete Part 8 computation, or campaign closure. The blueprint's full-Hamiltonian formulation follows later by the existing split and scalar coupling; it is not an extra exported declaration promised by this package's exact signatures.
4. Repository writes by this audit are limited to this report and temporary `.lake/abi-scratch/` probes, removed after checks. Existing untracked S8-M-handoff.md is preserved. No state-changing git, generated-root edit, frozen edit, manifest edit or production edit was performed.
