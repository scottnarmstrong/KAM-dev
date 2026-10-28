# Independent S8-J package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped S8-J implementation. All seven new public theorems pass statement/proof review. No frozen theorem is assigned to this package, so no anchor is declared seal-ready or closed. The notes concern the permitted stale generated root and an existing upstream name collision.

Audited HEAD `803cd10df26d8c97f2dc835e889c901156e8ecc8`, against `inp` at `31f0bfbf70c07b1eefd006237f331c00e003a0e5`, using `git diff inp...HEAD`. The entire branch delta is the new 167-line `KAM/Planetary/SecularForm/ModelTransfer.lean`. Audit scope is ONLY that module, as required by AUDIT FOCUS. The pre-existing untracked handoff was read and left unchanged. This report is in the package worktree at the user's explicitly requested absolute path, overriding the generic brief's main-worktree destination.

Read AGENTS.md, PLAN.md, DECISIONS.md, the shared package-audit brief, S8-J handoff, design Revision 2 (S8-J row, proof plan, node table, Appendix A), both design audits, shared `.drafts/design/P810Signatures.lean`, blueprint Part 8 (especially lines 17–35, 39–52, 180–207), and relevant track-P statement clauses. Read the frozen Birkhoff form, average, assembly and oscillator definitions, and the consumed S8-A/S8-M declarations. No online source lookup was needed: the authoritative comparisons are the local blueprint and audited design, not a fresh paper audit.

## Declaration review

Names below are relative to `KAM.Planetary.SecularForm`; line numbers refer to ModelTransfer.lean.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| Chart-domain adapter, line 32 | `mem_slowDom_iff'` | PASS | Unfolds the actual product Poincare domain into positive actions and `Gamma < I`; no extra premise. |
| Polydisc containment, line 37 | `realDisc_subset_slowDom` | PASS | Uses the literal radius bounds `r < action/2` and `r < sqrt(action)/16`; proves chart inclusion coordinatewise. No positivity assumption on r is needed when there is no point in the disc. |
| Local proof cut, line 63 | `jets_core` | PASS | Distinct conditional helper: local fixed-model integrability and chart containment give the average identity; positive-order derivatives remove the action-only constant. The source-specific exports prove its integrability premise. |
| `bpP:p8:same-jets#jets`, line 90 | `same_jets_on` | PASS | Exact design signature modulo whitespace only. One positive radius precedes all points, positive slow orders k, and all action orders l including zero. Full multilinear tensors retain all mixed-coordinate consequences. |
| `bpP:p8:same-jets`, line 111 | `same_jets` | PASS | Byte-identical design signature. Every action in the actual action image is represented by admissible axes, and the circular point is inside the supplied disc. |
| `bpP:p8:same-jets#transfer`, conditional helper, line 121 | `birkhoff_transfer` | PASS | Byte-identical design signature. Integrability equivalence and guarded average shift are explicit conditional premises, not an asserted physical theorem. Both directions preserve the frozen remainder bound, radii, parameters, Omega and beta. |
| `bpP:p8:same-jets#transfer`, line 154 | `same_jets_transfer` | PASS | Byte-identical design signature. Discharges both generic premises using S8-M identification on the supplied whole-disc chart domain. Only P0 changes, with the correct subtraction sign. |

The shared signature file has SHA-256 `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`, matching design audit 2. Independent extraction confirmed the last three signatures are byte-identical and `same_jets_on` differs only by whitespace (the advertised line break). A fresh Lean probe copied all four design statements as examples and proved them with exactly the explicit arguments, in order:

```lean
by exact same_jets_on D ha
by exact same_jets D hI k hk
by exact birkhoff_transfer hInt hAvg
by exact same_jets_transfer D hDom
```

Provider/frozen theorem type and seal-body probes are not applicable: there is no provider or frozen theorem export in S8-J. These four independent design-statement probes check the applicable implementation boundary instead.

## Proof and definition assessment

`jets_core` varies the slow coordinates while holding the action fixed. The preimage of the real open polydisc is a neighbourhood, on which identification and the supplied fixed-model integrability prove moving = fixed + modelDelta. Eventual equality transfers iterated derivatives, and `fderiv_add_const` removes the constant for positive order; this argument remains valid for total derivatives without assuming unproved smoothness. `same_jets_on` then varies the actions in another open preimage and applies eventual equality to every action derivative. It obtains integrability from `perturbation_analytic`, rather than from an assumed conclusion or a subtraction of nonintegrable Bochner averages.

For transfer, the frozen epsilon-delta witness satisfies `0 < d` and `d <= r0`, hence `d^2 <= r0^2`. Every smaller oscillator-disc point therefore satisfies the original hInt/hAvg guards. Rewriting the average and subtracting the action-only delta gives exactly the same residual and fourth-power norm bound in both directions, including at zero. No positivity of r0 or mu0 is silently added; empty/vacuous parameter cases are handled by the same universal statements. The `(q,I,p)` slow tuple matches frozen `(I,p,q)=(Lambda,eta,xi)`, with the same normalized `[0,2*pi]^n` integral.

No new `def`, `abbrev`, `structure`, instance, or public object is introduced in the audited file. Its two local `emb` lets are literal coordinate insertions into the existing slow product, continuous on their entire carriers and with no fallback values. Reused definitions are the literal physical perturbations, frozen average and Birkhoff predicate; there is no substitute model or altered normalizer. `Data` contains only positive physical/typing data. All ambient vectors are `Fin n -> R` or `Fin n -> C` via existing aliases, not EuclideanSpace.

The chart-domain premise of `same_jets_transfer` is weaker than the blueprint's analytic-polydisc premise, exactly as the revised design explicitly documents at lines 359–360. This is a valid stronger domain form: frozen integrability is transferred using identification, not inferred outside the analytic polydisc. The conditional helpers have distinct names, and neither their integrability hypothesis nor their average-shift hypothesis leaks into the physical export. No extra premise, wider constant dependence, weakened conclusion or conclusion-shaped assumption was found.

## Independent validation

All auditor-controlled Lean/Lake/checker operations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. The build used the required gate; no clean, update, cache download, generated-root regeneration, package modification or state-changing git operation was performed.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8j KAM.Planetary.SecularForm.ModelTransfer
   [inp-gate] slot 2 acquired 13:04:15 for KAM.Planetary.SecularForm.ModelTransfer
   Build completed successfully (9137 jobs).
   exit 0
   ```

   The gate runs `nice -n 5 lake build`. Replayed warnings concern existing upstream unused variables (Energy, Chart, Mass, Holomorphic, Hamiltonian Algebra/Chart, D25); no audited-file warning was emitted.

2. Design statement probe and axioms:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8JAudit.lean
   exit 0
   ```

   Exact axiom output:

   ```text
   'KAM.Planetary.SecularForm.mem_slowDom_iff'' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularForm.realDisc_subset_slowDom' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularForm.jets_core' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularForm.same_jets_on' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularForm.same_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularForm.birkhoff_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularForm.same_jets_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay (one invocation, only new module):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.ModelTransfer
   replaying KAM.Planetary.SecularForm.ModelTransfer
   exit 0
   ```

4. Lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (655 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole failing condition is the generated-root staleness explicitly permitted by the audit brief. No generated file was edited. All other lint checks passed.

5. Static checks:

   ```text
   git diff --check inp...HEAD
   exit 0, no output
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   exit 0, no output
   ```

   Recursive inspection of the 91-module KAM import closure found no provider and no frozen theorem module (hence no imported DRAFT_SORRY theorem). The new file contains no forbidden token, sorry, override, EuclideanSpace, or new instance; it has the copyright, module command, public imports, module docstring and public exposed section. It is 167 lines, below 1500, with no overlong Lean line reported by lint. The scratch probe is removed after validation. Only this report is written by the auditor outside `.lake/`.


## Notes, errata and scope

No suspected pinned-paper or blueprint defect was found in this scoped implementation. No frozen defect or auditor-introduced mathematical deviation was found. S8-J proves the allocated jets and Birkhoff-transfer interfaces; it does not close P-FIXED, torsion, any provider, or the entire prose corollary as a separate dynamics theorem.

Upstream integration note, confirmed statically: `AnalyticReal.lean:29` and `Symmetry.lean:344` both declare `KAM.Planetary.SecularForm.planetBlock_assemble` with different explicit arguments. The declarations are in the same namespace; a consumer combining those two module branches needs an upstream rename. S8-J imports the former through Analytic and avoids Symmetry, proving its small chart-domain adapter locally. This is a pre-existing integration defect outside the one-module audit, not a S8-J proof failure and not a pinned-source erratum. No combined-import elaboration or upstream repair is claimed.

Uncertainties: no unresolved proof or statement-fidelity finding within the assigned module. The upstream packages were inspected as consumed dependencies, not independently re-audited in full.
