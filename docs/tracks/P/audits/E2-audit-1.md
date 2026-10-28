# E2 independent package audit 1

Audit date: 2026-10-28. **Overall verdict: PASS WITH NOTES**. Scope: only `KAM/Planetary/Exponential/Enlargement.lean`; one public theorem, no provider or frozen anchor delivered by E2. This is an E2 helper-package verdict, not a seal of P-EXP-SAFE.

## Snapshot and authority

- Worktree/report: `/root/code/KAM-inp-p14-e2/docs/tracks/P/audits/E2-audit-1.md`. The user's exact destination overrides the generic brief's main-worktree destination.
- HEAD `047abcbd2ba73dac224159527beb02b8dcb88b03`; inspected `inp` ref `ff90b30b9af90253cabe2e841aee0747709fbe1b`. `git diff inp...HEAD` adds only the 84-line Enlargement module. Handoff was already untracked and is preserved.
- Module SHA-256: `ba653cb93af42dd66920c830779981e8446f072db02f44ede2942d0e1ad7d0de`.
- Read AGENTS.md, PLAN, DECISIONS, the package audit brief, E2 handoff, P14 design and Appendix A, both design audits, blueprint p14a, track-P statement, frozen AMDBox/Admissible and P-EXP-SAFE, and imported E0 Setting definitions. The signature and design audits absent at the handoff's relative locations were read from `/root/code/KAM-inp/.drafts/design/P14Signatures.lean` and `/root/code/KAM-inp/docs/tracks/P/design/DESIGN-P14-design-audit-{1,2}.md`.
- Signature file SHA-256: `cd28718f0ef82c8da477ff5be2985046d08d795614be4d36fd0b7e267de98dd7`, matching revision-2 audit evidence.

## Declaration and obligation ledger

| Node / obligation | Lean declaration / location | Verdict | Reason |
|---|---|---|---|
| `bpP:p14:enlarge` | `KAM.Planetary.enlarge`, lines 31–82 | PASS | Statement text before `:=` is identical to signature lines 244–245 and design lines 767–768. Only implicit dimension, box and literal admissibility; witnesses precede any perturbation parameter or initial datum. All eight fields preserve E1–E3 and positivity/enlargement clauses. |
| `stepP:p14:en-lim` | internal to `enlarge`, lines 33–68 | PASS | Finite intersections of continuous strict inequalities at zero. Admissibility supplies positive lower actions, ecc<1, strict deficit, and distance>0. Radii and gaps use their source margin d to obtain strict slack above d/2, then weaken to ≤. Square root continuity is valid globally; division uses constant denominators. |
| `stepP:p14:en-choice` | internal to `enlarge`, lines 69–82 | PASS | The right-neighbourhood filter of zero is nontrivial. A common t>0 yields `(kappa,e,A)=(t,B.ecc+t,B.outerAMD+t)` and directly constructs every EnlargedData field. No conclusion assumed. |
| E2 slow-erosion positivity | `EnlargedData.amd_lt` supplied at line 77; E0 field | PASS WITH NOTE | Complete against the signed interface: there is no separate declaration in Appendix A, signature file, or node table. The positive numerator follows from outerAMD>0 and A>outerAMD. Positivity of the denominator also uses the standing n≥2 from p14a lines 5–6; see below. |

The design expressly states at lines 86–87 that proof-step rows are internal obligations, not separate declarations. Row E2 (line 375) therefore does not require additional public names. The generic provider/frozen type and seal-copy tests are inapplicable: E2 has no provider or anchor export. The scratch probes instead check the entire polymorphic helper type and the explicit-binder application `enlarge B hB`.

## Definitions, hypotheses and proof review

No new def, abbrev or structure exists in this change. E0's `EnlargedData` (Setting lines 58–67) is an inherited proposition containing precisely source geometric conditions; no analytic extension, confinement or theorem conclusion is hidden in a field. Its `amd_lt` is the literal strict AMD enlargement. Other imported Setting definitions retain their existing carriers; none is redefined or modified here. This audit is not a new independent E0 certification.

The theorem is stronger than the blueprint's standing dimension restriction: it holds for arbitrary n, including zero, for its stated geometric conclusion. It neither defines nor asserts positivity of the totalized quotient epsD at n=0. The blueprint formula `epsD=(sqrt(2*A)-sqrt(2*outerAMD))/sqrt(2*n)>0` (p14a line 177) uses n≥2. The prose “positivity ... is A⁺>A₁” (line 181; module docstring lines 19–20) is correct under those standing assumptions, not an unconditional equivalence on every n. A scratch proof independently checks the formula under n≥2. No missing signed E2 declaration, frozen defect, or blocking erratum results.

A static traversal of 66 KAM modules in the import closure found no provider, no frozen theorem module and no file containing `sorry`. Therefore no DRAFT_SORRY or provider dependency is used; there is no imported frozen-theorem manifest state to approve. Repository-wide declaration search found no second declaration named `enlarge`; its namespace is `KAM.Planetary`.

## Validation receipts

All Lean/Lake invocations below were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource override was used. The build wrapper supplies `nice -n 5` internally. It waited for the shared compile gate before acquiring slot 1 at 16:02:47 UTC.

1. Targeted build:
   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e2 KAM.Planetary.Exponential.Enlargement
   ```
   Exit 0: `Build completed successfully (9112 jobs).` Existing unused-variable warnings were replayed for Kepler/Energy:106; Poincare/Chart:212,247; Kepler/Mass:147,157,500,524. No Enlargement warning or default-heartbeat failure.

2. Full helper signature, explicit-binder application, erosion consequence and axioms:
   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E2Audit1.lean
   ```
   Exit 0. Probe contained the exact polymorphic expected type assigned to `@KAM.Planetary.enlarge`, a fresh theorem-shaped example with body `by exact KAM.Planetary.enlarge B hB`, and a proof of the literal epsD formula's positivity under n≥2, admissibility and EnlargedData. One harmless unused-variable warning concerned `hB` in the probe's expected-type binder. `#print axioms KAM.Planetary.enlarge` output:
   ```text
   'KAM.Planetary.enlarge' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```
   The printed type was:
   ```lean
   ∀ {n : ℕ} (B : AMDBox n), B.Admissible → ∃ kappa e A, EnlargedData B kappa e A
   ```
   This covers every new public theorem (one). The independently compared source telescope was text-identical to P14Signatures.lean, not merely definitionally equivalent.

3. Kernel replay, one invocation, only the delivered lemma module (no provider module exists):
   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.Enlargement
   ```
   Exit 0; complete output:
   ```text
   replaying KAM.Planetary.Exponential.Enlargement
   ```

4. Lint:
   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```
   Exit 1 solely for the brief-permitted generated-root exception. Complete output:
   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (784 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```
   Generated `KAM.lean` was left untouched as required. This is the hygiene reason for PASS WITH NOTES; no other lint failure was emitted.

5. Read-only checks: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output; `git diff --check inp...HEAD` exited 0 without output. The delivered file has 84 lines, a copyright header, `module`, public imports, module docstring and public section. Source inspection and lint found no forbidden proof escapes, resource overrides or EuclideanSpace. No new definition body requires exposure. Final report whitespace check passed; scratch probe and replay log were deleted.

## Handoff limits

Only this report persists from the audit; scratch probes are removed. No production, frozen, manifest, generated-root or README edits, no state-changing git, no new mathematical premises. No suspected pinned-source erratum or blueprint contradiction found in the E2 slice. The source comparison is against the pinned blueprint contracts, not a fresh PDF audit. E3–E12, E0 proof status and the eventual P-EXP-SAFE provider are outside scope.
