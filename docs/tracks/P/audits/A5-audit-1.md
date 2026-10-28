# A5 independent package audit 1

Date: 2026-10-28. **Verdict: PASS WITH NOTES** for the A5 library package. No blocking mathematical, signature, completeness, or hygiene defect was found in the audited module. The notes are the permitted generated-root lint exception and a sound implementation-route deviation.

## Scope and authority

Audited only `KAM/Planetary/AMD/AngularMomentum.lean`, 139 lines, at HEAD `8d0d536bd0482e17f75f90c7243986bad65e9e98`. Initial comparison ref `inp`: `71fdb6c99567fab5e7e6c71a0a86d42641d9c9ff`. `git diff inp...HEAD` adds only this file. SHA-256: `072fe08dac74847c89b95626c489f8c3d18622c3cc8d7e17d8eb836cdff42be2`.

Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the worktree's A5-handoff.md including AUDIT FOCUS. The user's exact worktree report path overrides the generic brief's main-worktree destination. Also read the A5 design row (P14-LEAN-DESIGN.md:371), node rows :93 and :120–123, F5 proof plan :41–50, Appendix A signatures :625–628 and :738–741, both P14 design audits, blueprint p14a-amd-expsafe.tex:118–125 and x-calc :30, and corresponding graph packet records. Reviewed the relevant Track P statement formulas :460–470, frozen AMD confinement anchor and definitions, MovingODE, and Newtonian equation suppliers.

Current authoritative signature file: `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`, SHA-256 `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`. Both A5 public contract signatures are byte-identical to that file and the design appendix. Historical design-audit hashes were not treated as current authority.

**Per-anchor disposition:** A5 owns no frozen anchor or provider export (the angular-momentum graph record has FROZEN_FILE/FROZEN_DECL `-`). Provider=frozen-type and frozen seal-body probes are therefore inapplicable to A5. The downstream `KAM.Planetary.amdConfinement` anchor remains `by sorry`; this audit does not certify it seal-ready or close A6. A5's two contract exports pass exact-type and explicit-binder application probes instead.

## Declaration and proof-plan ledger

All unqualified names below are in `KAM.Planetary`; Lean line numbers refer to AngularMomentum.lean.

| Node / obligation | Lean declaration / location | Verdict | Evidence |
|---|---|---|---|
| bpP:p14:x-calc, A5 F5 wrapper | `interval_constancy`, :33–46 | PASS | Exact contract; only OrdConnected and pointwise HasDerivAt-zero premises. Covers arbitrary real intervals, including empty and singleton sets. |
| Ordered-pair cancellation, am-der | `sum_mass_mul_cross_fKernel`, :49–75 | PASS | Actual fKernel; equal distance denominators, antisymmetric cross products, vanishing diagonal, double-sum exchange. No premises. |
| am-eq algebra | private `cross_rate_eq`, :78–108 | PASS | Calls hamiltonianVectorField_moving with G=m0=1 at both coordinates; rewrites literal central and pair kernels; cancels the parallel terms by ring algebra. |
| stepP:p14:am-eq | `ang_mom` :114–115, :123 plus `cross_rate_eq` :88–105 | PASS | Reads the derivative and NoCollision directly from the frozen IsMovingSolutionOn body and uses the actual moving Hamiltonian equations. |
| stepP:p14:am-der | `ang_mom` :116–135; cancellation helper | PASS | Coordinate product rules, HasDerivAt.fun_sum, central torque zero, total-momentum self-cross zero, ordered-pair torque zero. |
| stepP:p14:am-const | `ang_mom` :113 and `interval_constancy` | PASS | Zero derivative is proved internally and then passed to the interval wrapper. |
| bpP:p14:ang-mom | `ang_mom`, :110–135 | PASS | Exact signature, literal frozen totalMomentum and IsMovingSolutionOn; no added source premise or changed quantifier. |

**A5 slice complete.** The package row requires the interval wrapper, angular-momentum theorem, and ordered-pair cancellation. The three named proof steps am-eq/am-der/am-const are all implemented, including the per-body derivative and both kinetic and force cancellations. No additional signature-file declaration is assigned to A5. The code does not call moving_ode itself: its needed derivative/domain information is already present in the frozen solution predicate. This is a direct projection of the same facts, with no omitted regularity or reconstruction obligation in A5.

**Constancy route deviation is sound.** Design :43–47 suggests converting to convexity and using Convex.is_const_of_fderivWithin_eq_zero. Instead, Lean :36–42 proves the ordered case a≤b on Icc a b⊆J. HasDerivAt supplies continuity on Icc and the right-within derivative on Ici x for every x∈Ico a b. Mathlib Analysis/Calculus/MeanValue.lean:360–364 requires exactly these local facts, with no derivative assumption outside J. Evaluating at b yields f b=f a. Lean :44–46 covers s≤t directly and t≤s by symmetry. Equality endpoints and singleton intervals are included; empty J has no endpoint pair to consider. No global constancy premise, open-interval premise, or UniqueDiff premise was added.

**Physical cancellation is literal.** The private identity kills cr(p_i/m_i,p_i) and cr(q_i,q_i); summing its kinetic remainder gives mu*((sum p_0)*(sum p_1)−(sum p_1)*(sum p_0))=0. For the force remainder, the helper's g_ji=−g_ij uses planeLength_sub_comm and cross antisymmetry. The filtered diagonal contributes zero. This proves conservation in the full moving system; it does not substitute averaged-system conservation or conservation of physicalAMD. General n and unrestricted masses/mu are stronger than the surrounding physical standing assumptions and match the design contract.

## Definitions and hypotheses

No new top-level def, abbrev, structure, instance, or replacement carrier is introduced. The sole local `set g` (:51–52) is the explicit ordered torque summand on all Fin n pairs. It has no artificial fallback. The algebraic cancellation helper holds even at colliding configurations under Lean's existing total division; it never uses a collision value to justify a physical derivative. The dynamics identity requires NoCollision and ang_mom obtains it from hz. Body indexing, Phase, planeCross, planeLength, totalMomentum, movingHamiltonian, and IsMovingSolutionOn remain the existing literal objects.

The helper premises are typing data or collision-free source data. `interval_constancy` is a distinctly named generic calculus helper; ang_mom proves its zero-derivative input rather than assuming it. No conclusion-shaped assumption is added to ang_mom.

## Hygiene and independent validation

All audit Lean/Lake calls were sequential with LEAN_NUM_THREADS=1, nice -n 5, and default resources. The targeted build used the required shared gate. No broad build, cache download, clean, package update, resource override, source repair, or state-changing git operation was performed.

Validation receipts follow.

Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-a5 KAM.Planetary.AMD.AngularMomentum
exit 0
[inp-gate] slot 1 acquired 16:21:47 for KAM.Planetary.AMD.AngularMomentum
Build completed successfully (9096 jobs).
```

The build replayed two existing unused-variable warnings from KAM/Kepler/Energy.lean:106:35 and :106:48 (`hm`, `hκ`). No warning or error originated in the audited module. “9096 jobs” is the targeted dependency-graph receipt, not a whole-library rebuild.

Exact-signature and explicit-binder probes:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/A5AuditProbe.lean
exit 0
'KAM.Planetary.interval_constancy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sum_mass_mul_cross_fKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ang_mom' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The probe copied the two contracts directly from P14Signatures.lean under fresh audit names, replaced the admitted bodies by `by exact interval_constancy hJ hf` and `by exact ang_mom hJ hz`, and checked `type_of% @audit_export := @export` and the reverse for each. No admitted signature theorem was imported. The probe also #checked constant_of_has_deriv_right_zero and confirmed the precise Icc-continuity/Ico-right-derivative supplier type quoted above. All six examples/declarations elaborated without diagnostics. The three printed exports exhaust the new public theorem inventory.

Kernel replay (one invocation; A5 has no provider module):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.AMD.AngularMomentum
exit 0
replaying KAM.Planetary.AMD.AngularMomentum
```

Static checks: `git diff --check inp...HEAD` exits 0 with no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. The module has a copyright header, module declaration, public imports, module docstring and exposed public noncomputable section; 139<1500 lines. No forbidden proof escape, resource override or EuclideanSpace occurs. All declarations are inside KAM.Planetary and cross_rate_eq is private. Searching all KAM Lean files found exactly one declaration of each new public short name, all in this module; no root-level declaration or namespace shadow was introduced.

A recursive source import scan found 50 KAM modules in the import closure and zero KAM.Provider modules or frozen theorem modules. Consequently no DRAFT_SORRY theorem is imported, and there is no imported frozen theorem whose SEALED status needs justification. Direct frozen imports are definitions only; the transitive closure includes further frozen definitions.

Source lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
exit 1
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (785 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The only lint failure is the exact generated-root exception permitted by the brief. README.md and KAM.lean were not regenerated or edited.

## Errata, deviations, limitations and closeout

No suspected pinned-source, blueprint, or frozen-statement defect was found within A5. No new source erratum is asserted. The proof-route departure is limited to the local right-derivative constancy supplier described above and the direct extraction of solution clauses instead of invoking the MovingODE equivalence; both preserve the exact statements and all proof-plan obligations. The cancellation helper's all-configuration algebraic generality is a strengthening, not a replacement of collision-free dynamics.

No heartbeat design signal occurred. No unverified proof claim remains for the scoped A5 exports. This audit does not independently re-audit all upstream supplier proofs, fetch pinned PDFs, alter graph proof-status records, or certify the still-admitted downstream confinement theorem. Kernel replay and axiom checks certify the scoped Lean proofs under the stated standard axioms.

Only this report was added persistently by the auditor. The pre-existing untracked A5-handoff.md was preserved. The A5AuditProbe.lean scratch file was deleted after validation; production sources, signatures, frozen files, manifest and generated files remain unchanged. Final checks confirmed unchanged source/signature hashes, no comparison diff in protected paths, clean comparison whitespace, and report formatting.
