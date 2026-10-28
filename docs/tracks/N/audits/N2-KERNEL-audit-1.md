# Independent audit: N2-KERNEL

Overall verdict: **PASS WITH NOTES**. All six new declarations pass mathematical, statement-fidelity,
definition-body, elaboration, axiom and kernel-replay checks. The notes are repository integration and
pre-existing documentation/lint issues, not missing mathematical premises or proof gaps.

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-n2k`. Independent auditor; no implementation edits.
Report destination follows the explicit user instruction, overriding the brief's generic main-worktree wording.

## Scope and pinned evidence

- HEAD: `75d84219b5ce7391ee62632f3ed858bcdf57ebe9`.
- Compared `inp`: `4f65a1f8055d14808ab27ed9bff2e18d69eac46c`.
- Merge base: `88983f74ff9952994d1de31d0ed671307437b563`.
- `git diff inp...HEAD` adds only `KAM/Nekhoroshev/QcZero/Kernel.lean`, 111 lines.
- Module SHA-256: `7e5f0c76113722c1b0391134b5d952e7af8208e5b3f0395c2813461a35a8d4db`.
- Handoff SHA-256: `37da7e8d5a96790b5efbbb386302be33458cf4839b5b69e3d1a60837eb02c8b3`.
- `blueprint-N/parts/p2-qc-zero.tex` SHA-256:
  `ed9954f4a8313436ba58be47d1f061022b49cdf3ad04ba72b0c9467412dce73d`.
- `docs/tracks/N/design/N2-LEAN-DESIGN.md` SHA-256:
  `42377b6eccc4cac2f9f35feaabd620ea56ded53d38052dfbff84ada06eb7a726`.
- `docs/tracks/N/design/DESIGN-N2-design-audit-1.md` SHA-256:
  `6c520a2b0dbf4233de6662972b6c6484d65fa74967680d58d8a20b4f545d680a`.
- Original design signatures: `/root/code/KAM-inp/.drafts/design/N2Signatures.lean`, SHA-256
  `6f0af532d88555f0dd089b07298270823eecafd6d46efa540eeda7f8ef87a57a`.
  This untracked draft is absent from the package worktree; the original was read without modification.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, handoff, design/proof plan, prior design audit,
Part-2 blueprint, Track-N statement, and relevant N-QC frozen theorem/definitions. All verdicts below concern
only Kernel. No N2-DERIV, N2-QC, N2-ZFIELD, N2-ZORBIT, I/P implementation or paper-wide audit is asserted.
The separate discovery and refutation passes found no material defect.

## Frozen-anchor boundary

**No new frozen anchor or provider is assigned to N2-KERNEL; seal readiness is not applicable.**
The design explicitly assigns infrastructure only. The existing related anchor
`nekhoroshev.quasiConvex_isoenergetic_derivative.v1`, export
`KAM.Nekhoroshev.quasiConvex_isoenergetic_derivative`, is manifest-SEALED and unchanged.
Its analytic derivative conclusion is distinct from this generalized algebraic matrix theorem.
No claim of newly sealing N-QC or N-ZERO is made. Provider-equals-anchor and seal-copy probes are therefore
N/A for this package, rather than omitted tests of an assigned seal.

The related frozen `IsStrictlyQuasiConvex` and `realPart` bodies were inspected, and their hashes match the
anchor's definition closure (`c26d3ca9660dcc5d35eeffd26ac391b7ac9f87917e5e8befaaef9e92fe5ab5df`
and `85abbe30196fa629c9be922f13e67fdf591a9d435d94e92a0e0e701c6dde1e7b`). Kernel imports neither them
nor any provider/frozen theorem: its only imports are the two Mathlib modules at lines 8–9.

## Declaration and node ledger

All names are in `KAM.Nekhoroshev`; lines refer to the pinned Kernel module.

| Node / source | Declaration | Verdict | Reason |
|---|---|---|---|
| `bpN:p2:qc-kernel`, blueprint lines 11–18 | `bordered_map` (27) | PASS | Literal CLM `(v,u) ↦ (freq·v, u freq + lam A v)` on the exact ordered product carriers. |
| Same displayed formula | `bordered_map_apply` (36) | PASS | Complete formula for every input and every matrix/scalar, without nondegeneracy restrictions. |
| `stepN:p2:qk-eqs`, line 20 | `qk_eqs` (45) | PASS | Both zero-output equations; removes unused nondegeneracy conditions. |
| `stepN:p2:qk-pair`, line 22 | `qk_pair` (53) | PASS | Pairing gives the literal nonsymmetric quadratic sum; nonvanishing forces v=0. |
| `stepN:p2:qk-scalar`, line 24 | `qk_scalar` (78) | PASS | Derives v=0 internally, then uses a nonzero frequency coordinate to force u=0. |
| `bpN:p2:qc-kernel`, lines 11–27 | `qc_kernel` (93) | PASS | Trivial kernel AND bijectivity; arbitrary real matrix, either nonzero sign of lambda. |
| `stepN:p2:qk-bij`, line 26 | `qc_kernel`, second conjunct | PASS | Same linear map, finite-dimensional domain/codomain with equal finrank; injectivity supplies surjectivity. |

Mechanical comparison found all five theorem signatures byte-identical to the design draft, including binder
order, implicit lambda, carriers, assumptions and complete conclusions. The definition body is byte-identical
as well. Exact-type application probes independently elaborated each copied signature against the actual export.
No existential constants, hidden constant dependencies, norms, Fourier normalizers or new instances occur.

## Expanded binder audit

SOURCE includes source data as well as propositions. Rows with several declarations apply separately to
each occurrence; nested hA binders are explicitly classified below. There are no project-owned Prop aliases
or bundled hypotheses to expand. No implicit typeclass hypotheses are introduced by these signatures.

| Declarations | Binder | Bin | Source / reason |
|---|---|---|---|
| All five theorems | `{n : ℕ}` | TYPING | Coordinate dimension; design decision 4 permits all n. |
| All five | `freq : Fin n → ℝ` | SOURCE | Blueprint lines 12–15, omega. |
| All five | `A : Matrix (Fin n) (Fin n) ℝ` | SOURCE | Blueprint line 12, arbitrary real matrix. |
| apply, eqs | `(lam : ℝ)` | SOURCE | Operator data; its formula/equations hold without nondegeneracy. |
| pair, scalar, kernel | `{lam : ℝ}` | SOURCE | Same scalar data, with precisely the design's implicit binder. |
| scalar, kernel | `hfreq : freq ≠ 0` | SOURCE | Blueprint line 14; used at scalar step line 24. |
| pair, scalar, kernel | `hlam : lam ≠ 0` | SOURCE | Blueprint lines 12, 22; no positivity strengthening. |
| pair, scalar, kernel | `hA` | SOURCE | Exactly the nonvanishing implication displayed at blueprint line 14. |
| Each hA occurrence | `v : Fin n → ℝ` | SOURCE | Universally quantified test vector in that implication. |
| Each hA occurrence | `(∑ i, freq i * v i) = 0` | SOURCE | Orthogonality premise of that implication. |
| Each hA occurrence | `v ≠ 0` | SOURCE | Nonzero-vector premise of that implication. |
| apply, eqs, pair, scalar | `(v : Fin n → ℝ)` | SOURCE | Input vector of the operator/kernel computation, lines 15, 20. |
| apply, eqs, pair, scalar | `(u : ℝ)` | SOURCE | Input scalar of that computation. |
| eqs, pair, scalar | `hz : bordered_map freq A lam (v,u) = 0` | SOURCE | Kernel-membership premise of proof step line 20. |

Counts of expanded binder occurrences, including the three nested binders per hA:

| Theorem | SOURCE | STANDING | TYPING | RULED | EXCESS |
|---|---:|---:|---:|---:|---:|
| bordered_map_apply | 5 | 0 | 1 | 0 | 0 |
| qk_eqs | 6 | 0 | 1 | 0 | 0 |
| qk_pair | 11 | 0 | 1 | 0 | 0 |
| qk_scalar | 12 | 0 | 1 | 0 | 0 |
| qc_kernel | 9 | 0 | 1 | 0 | 0 |

The quadratic nonvanishing hypothesis is a literal premise of this algebraic source lemma, not an assumed
proof of the analytic quasi-convexity theorem. Kernel membership is a legitimate premise of the local proof
steps; qc_kernel discharges it internally for arbitrary kernel elements. No conclusion-shaped hypothesis occurs.

## Definition classification

`bordered_map` is the sole new definition: **literal formula**, not characterization/choice-defined.
Its binders are dimension data n (TYPING) and source data freq, A, lam (SOURCE).
The first projection/sum produces the dot product; the second produces u times freq plus lam times A v.
The exported application theorem verifies both components on the entire product carrier.

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

No fallback, valid-locus restriction, arbitrary selected witness or invented off-domain value is present.
The enclosing `@[expose] public noncomputable section` exposes the definition as required.

## Proof scrutiny and attempted refutations

- **Nonsymmetric A / orientation:** lines 62–76 expand the exact sum `∑ i, ∑ j, v i * A i j * v j`.
  There is no transpose or symmetry step. Distributing and commuting real scalar products is sufficient.
- **Negative lambda:** only multiplication cancellation by `lam ≠ 0` is used. No sign argument is hidden.
- **Zero or small dimensions:** n=0 makes hfreq impossible, so qc_kernel is vacuous there; n=1 is valid even
  when the perpendicular quadratic premise has no nonzero test vector. Dropping n≥1 agrees with D-N2-1.
- **Local premise drops:** qk_eqs needs only zero output; qk_pair does not need hfreq. These strengthenings
  agree with the design and do not weaken any conclusion.
- **Finite-dimensional step:** lines 99–106 prove trivial kernel and injectivity of the exact underlying
  linear map. Lines 107–109 prove finrank equality of the two product spaces and apply
  `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` in the correct direction. Inspection of Mathlib
  `LinearAlgebra/FiniteDimensional/Lemmas.lean:204` confirms its finite-dimensional hypotheses on both spaces;
  here they are ordinary inferred instances for products of finite coordinate spaces. CLM coercions preserve
  the function in both conjuncts. No infinite-dimensional injective-to-surjective inference occurs.

All proposed mathematical failure modes were refuted by the source/proof comparison and fresh kernel replay.

## Verification receipts

All audit-started Lean/lake commands were sequential with `LEAN_NUM_THREADS=1` and niceness 5, including
lint's internally launched ABI probe (inheriting that environment/niceness). No clean, update, cache fetch,
resource-budget override or broad rebuild was invoked. The build's reported job total is Lake's dependency
job count, not a request to run simultaneous audit processes.

1. Targeted gated build:

   ```sh
   env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n2k KAM.Nekhoroshev.QcZero.Kernel
   ```

   Exit **0**. Output:

   ```text
   [inp-gate] slot 1 acquired 06:54:48 for KAM.Nekhoroshev.QcZero.Kernel
   Build completed successfully (2173 jobs).
   ```

2. Exact signature/body and axiom probe:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N2KernelAudit1.lean
   ```

   Exit **0**, no warnings/errors. The probe imported only Kernel. Five fresh theorems copied the design
   signatures with bodies applying the actual exports to all explicit binders in order:
   `freq A lam v u`; `freq A lam v u hz`; `freq A hlam hA v u hz`;
   `freq hfreq A hlam hA v u hz`; `freq hfreq A hlam hA`.
   A fresh definition copied the complete designed bordered_map body, with an equality to the exported
   definition proved by `rfl`. A Python extraction asserted byte equality of the original/implementation
   signatures and complete definition body before elaboration. It printed:
   `PASS: all five theorem signatures and complete definition body byte-identical to design draft`.

   Complete `#print axioms` output:

   ```text
   'KAM.Nekhoroshev.bordered_map' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.bordered_map_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.qk_eqs' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.qk_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.qk_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.qc_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.QcZero.Kernel
   ```

   Exit **0**. Output: `replaying KAM.Nekhoroshev.QcZero.Kernel`.

4. Source lint:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, with complete output:

   ```text
   Lean lines over 100 characters:
   /root/code/KAM-inp-n2k/KAM/Planetary/Hamiltonian/Liouville.lean:35:108
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (432 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The generated-root warning is the brief's expected exception. The 108-character Liouville docstring line
   is an additional repository lint failure, reproduced unchanged at the merge base and HEAD. The current
   inp tip has already removed this overlength line; `git diff inp...HEAD -- KAM/Planetary/Hamiltonian/Liouville.lean`
   is empty. It is not introduced by this package. Kernel has **111 total lines**, maximum Unicode line
   length **97**, all required module scaffolding, and no forbidden tokens or options. Package hygiene passes;
   the whole-worktree lint invocation does not pass, and is not represented as passing here.

5. Integrity checks:

   `git diff --check inp...HEAD` exits **0** with no output.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exits **0**, empty output.
   `git diff --name-only inp...HEAD` prints only `KAM/Nekhoroshev/QcZero/Kernel.lean`.
   The temporary audit probe is deleted after validation. No state-changing git command was used.

## Notes, source defects and closeout

- **Integration note:** regenerate KAM.lean through the orchestrator's normal generated-file workflow.
  The auditor did not edit it, README, frozen files or manifest.
- **Pre-existing lint note:** Liouville line 35 is outside package ownership and unchanged from the fork point.
  The current inp already contains its correction; do not weaken the package's lint rule or claim exit 0.
- **Pre-existing blueprint coordination defect:** Part-2 lines 5–6 say the kernel is “cited by track I as the
  isoenergetic gate”; Track-I `blueprint-I/parts/p3-iso-local-charts.tex:415` says its nonsingular-derivative
  argument “is not needed.” This is the same nonblocking issue recorded in the design and its independent
  audit. The module supplies reusable infrastructure; an active I dependency is not established here.
- **Source scope:** no suspected new pinned-paper erratum, frozen-statement defect or implementation deviation
  was found. This is a blueprint/design-to-Lean package audit, not a fresh BM11 PDF audit or a uniform inverse
  estimate. The harmless dimension/local-premise strengthenings are recorded above.
- **Handoff precision:** the implemented file has 111 lines, rather than the handoff's approximate 140;
  it contains exactly the claimed declarations. This has no mathematical effect.

Closeout: all assigned declarations and nodes pass; all required executable checks completed; global lint
exceptions and source coordination issue are explicit. Only this report is a lasting auditor-created file.
