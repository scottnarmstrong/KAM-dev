# A4 independent package audit 1

Date: 2026-10-28. **Overall verdict: PASS WITH NOTES. A4 slice COMPLETE.** No blocking finding in `KAM/Planetary/AMD/MovingODE.lean`. The note is the explicitly permitted stale generated root diagnostic. This is approval of the A4 helper package, not seal readiness of a frozen campaign theorem.

## Scope and authority

- Worktree: `/root/code/KAM-inp-p14-a4`; audited HEAD `84b11769c5856be30e66a6f1152264c36dc1599b`; comparison `inp` resolved to `7e495e5036e22a1b8fe3efcb43da465c5e1c45e5`.
- `git diff inp...HEAD`: exactly one new file, `KAM/Planetary/AMD/MovingODE.lean`, 49 lines. SHA-256: `f69603e2deb6518badfb45f40f8d085e85a024160872fff26e090ff4643ae96d`.
- Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the supplied local A4 handoff. The user's exact local report destination overrides the generic brief's main-worktree output instruction.
- Contract: `docs/tracks/P/design/P14-LEAN-DESIGN.md:117-119` (node assignments), `:370` (A4 package), and `:730-737` (Appendix A). The design explicitly makes proof-step rows internal obligations, not additional public declarations (`:85-87`).
- The original signature file is absent from this worktree; read `/root/code/KAM-inp/.drafts/design/P14Signatures.lean:207-213` instead. SHA-256: `cd28718f0ef82c8da477ff5be2985046d08d795614be4d36fd0b7e267de98dd7`. Design audits are under `docs/tracks/P/design/` in the main worktree, rather than the handoff's `audits/` path. Both audits accept `moving_ode`; revision 2 closes the unrelated earlier design findings.
- Read `blueprint-P/parts/p14a-amd-expsafe.tex:108-116`, the track-P statement, the relevant frozen definitions, and the downstream `AmdConfinement` anchor. No provider or frozen anchor is implemented by A4. Provider/frozen-type and seal-body probes are therefore inapplicable to this slice; a fresh copied-signature application probe was run instead.

## Declaration and node ledger

| Node / declaration | Lean declaration / proof location | Verdict | Reason |
|---|---|---|---|
| `bpP:p14:moving-ode` | `KAM.Planetary.moving_ode`, MovingODE.lean:28-45 | PASS | Signature text before `:=` is identical to both Appendix A and the original signature file. Implicit `{n : ℕ}`, explicit `m`, `mu`, conjunction order, fixed `G = m0 = 1`, `Phase (n * 2)`, and quantification over arbitrary sets `J` and curves `z` agree. No extra premise or weakened conclusion. |
| `stepP:p14:mo-reg` | Internal proof, MovingODE.lean:36-38 | PASS | Openness comes from `isOpen_collisionFreeDomain`; neighborhood analyticity of the literal moving Hamiltonian gives `ContDiffOn ℝ 2` on the open domain, then `KAM.ODE.ham_smooth_c1` gives the required C1 field. Both designed suppliers are consumed directly. |
| `stepP:p14:mo-eq` | Internal proof, MovingODE.lean:39-45 | PASS | Forward direction projects collision freedom and the same two-sided derivative. Reverse direction supplies membership in `Set.univ`, derives differentiability from analyticity at the collision-free point, and retains that derivative. No regularity or interval assumption is placed on `J`. |

The scoped declaration inventory is exactly one public theorem, `moving_ode`. A repository search finds no competing declaration of this name in `KAM`. All assigned A4 obligations are paid by its proof; there is no missing assigned definition, helper export, or provider.

## Definitions, hypotheses, and refutation checks

No new `def`, `abbrev`, `structure`, or instance is introduced: the new-definition classification is empty. The theorem assumes only typing data `n`, `m`, `mu`; it assumes none of its three conclusions.

The consumed carriers and predicates are literal:

- `Phase d` is `(Fin d → ℝ) × (Fin d → ℝ)`.
- `collisionFreeDomain n` is `{z | NoCollision z.1}` (Models.lean:40); `NoCollision` requires positive heliocentric radii and positive distances for every distinct pair.
- `IsMovingSolutionOn` is the frozen differentiability-guarded Hamiltonian solution predicate with momentum domain `univ`, conjoined with collision freedom at each queried time. `KAM.ODE.IsSolutionIn` requires domain membership and the same `HasDerivAt` at each queried time.
- The field is the frozen `hamiltonianVectorField` of the frozen `movingHamiltonian 1 1 m mu`. No alternative Hamiltonian, normalization, time scale, or collision fallback is substituted. The reverse bridge supplies the differentiability guard from `analyticOnNhd_movingHamiltonian` (Models.lean:319-325), so total `fderiv` behavior outside its differentiability locus cannot establish a spurious solution.

The unrestricted mass vector and coupling are exactly the audited design contract. Smoothness for fixed zero/negative masses still follows mathematically from the total scalar coefficient operations and collision-free position dependence; A4 asserts no physical positive-mass theorem without its physical hypotheses. Arbitrary `J`, including empty or singleton sets and closed endpoints, keeps the frozen two-sided derivative requirement unchanged.

Blueprint line 112 says, “The same holds for −H and −F.” Its proof at line 115 invokes the generic time-reversal result. The exact A4 signature covers the physical field; the previously approved design audits explicitly accept deriving the negative-field version by negation. A4 introduces no separate negative-Hamiltonian solution predicate and does not identify a negative-field trajectory with the unchanged physical predicate. No missing A4 export or blueprint contradiction follows from that sentence.

The recursive KAM import closure contains 48 modules and **no provider imports and no frozen theorem imports**. Its frozen imports are definitions. Thus neither a DRAFT_SORRY theorem nor a quarantined provider is used, directly or transitively. The downstream `KAM.Planetary.amdConfinement` anchor remains `DRAFT_SORRY`; it is not imported or sealed here.

## Independent validation

All Lean/Lake invocations were sequential, used `LEAN_NUM_THREADS=1`, and ran with `nice -n 5` (including lint's inherited priority). No clean, update, cache download, generated-root edit, or library-wide build was performed. The targeted build waited for the shared compile gate.

**Targeted build:**

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-a4 KAM.Planetary.AMD.MovingODE
[inp-gate] slot 2 acquired 15:42:12 for KAM.Planetary.AMD.MovingODE
⚠ [9090/9094] Replayed KAM.Kepler.Energy
warning: KAM/Kepler/Energy.lean:106:35: Variable name `hm` is not explicitly referenced.
warning: KAM/Kepler/Energy.lean:106:48: Variable name `hκ` is not explicitly referenced.
Build completed successfully (9094 jobs).
exit 0
```

The two pre-existing upstream linter warnings are the only build diagnostics; their standard remediation hints are omitted above. The job count is Lake's target dependency traversal, not a clean rebuild.

**Signature/application probe and complete new-theorem axiom inventory:**

The temporary `.lake/abi-scratch/A4Audit1.lean` imported only the production A4 module, copied the original contract under `audit_moving_ode`, and proved it by `by exact moving_ode m mu`. It also checked both `example : type_of% @audit_moving_ode := @moving_ode` and the reverse direction. The scratch never imported the admitted design signature file.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/A4Audit1.lean
'KAM.Planetary.moving_ode' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

**Kernel replay:** one invocation, covering the sole new module/declaration; no provider module exists in this slice.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.AMD.MovingODE
replaying KAM.Planetary.AMD.MovingODE
exit 0
```

**Source lint:**

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (784 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The exit status is caused solely by the stale generated root diagnostic, explicitly allowed by the audit brief. All other lint checks pass. The generated file was left untouched.

Static inspection finds no proof escape, `sorry`, resource override, `EuclideanSpace`, or excess line count. The module has its copyright, `module`, public imports, module docstring, and `@[expose] public noncomputable section`. No new definition needs an unfolding annotation. `git diff --check inp...HEAD` exits 0. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.

## Findings, errata, and limits

No blocking finding, suspected pinned-source defect, blueprint defect, or introduced mathematical deviation was found. This is a local proof/package audit against the supplied design and blueprint, not a new audit of the historical planetary sources. The generic proof-release risks for other P14 packages do not become A4 assumptions.

The only package-readiness note is the permitted generated-root staleness. No frozen theorem is certified seal-ready by this helper-only audit. The report is the sole persistent audit edit. The temporary probe was deleted after validation. Final status contains only the pre-existing untracked `A4-handoff.md` and this new report; final protected-file diff and whitespace checks pass.
