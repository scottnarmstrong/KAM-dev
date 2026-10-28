# E10 independent audit 1

Overall verdict: **FAIL — incomplete assigned slice**. The six implemented theorems are sound, and the signed
`hnu` statement is exact. Finding F1 concerns the missing differentiability bridge, not a counterexample to any
implemented theorem. No frozen anchor is proved or seal-ready in this infrastructure package.

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p14-e10`; HEAD:
`4db06f49e391c9fa73f150f0917a0537312f310f`.
Substantive scope: only `KAM/Planetary/Exponential/Hamiltonian.lean` (102 lines).
Read AGENTS.md, PLAN, DECISIONS, the package audit brief, E10 handoff, P14 design and both design audits,
the original signature file, relevant blueprint/packet contracts, track statement and frozen definitions.
The user's explicit absolute report destination supersedes the generic brief's main-worktree destination.

## F1 — missing differentiability bridge (blocking slice completeness)

`blueprint-P/parts/p14a-amd-expsafe.tex:265` requires:
“Consequently, if $w\in\mathcal V$, $H^+_\nu$ is differentiable at $w$” as well as field equality.
The `stepP:p14:hn-field` proof at line 269 invokes differentiability of the chart Hamiltonian.
The packet `docs/graph/P/packets/P-p14a2.nodes.md`, node `stepP:p14:hn-field`, explicitly includes
`H_nu^+ is differentiable at w` in `SOURCE_CONCLUSION`.
`docs/tracks/P/design/DESIGN-P14-design-audit-2.md:72` approves the narrowed signed statement on the explicit
basis “field/differentiability bridges explicitly assigned to E10.” The E11 consumer at blueprint line 282
needs differentiability to construct the genuine N-system solution predicate.

The signed `hnu` at Hamiltonian.lean:50–71 proves only pointwise equality. The generic helper at lines 75–78
proves equality of totalized `fderiv`, and lines 81–84 prove equality of vector fields. Neither asserts or proves
differentiability. No declaration or proof in this module establishes a `DifferentiableAt`, `DifferentiableOn`
or `HasFDerivAt` conclusion, or invokes a differentiability-congruence bridge. Equality of totalized derivatives
alone is insufficient: two equal nondifferentiable functions also have equal totalized derivatives.

This is a small but literal missing obligation under the requested complete-slice criterion. Existing suppliers
make the repair straightforward: obtain chart differentiability from
`differentiableAt_movingHamiltonian` (Newtonian/Models.lean:335) composed with
`analyticOnNhd_poincareProd` (Poincare/Product.lean:168), using the chartSafe membership already established in
`hnu`. Transfer it across the neighborhood equality using `Filter.EventuallyEq.differentiableAt_iff`
(Mathlib/Analysis/Calculus/FDeriv/Congr.lean:138).
Add a distinct companion export preserving the signed `hnu` verbatim. A generic open-set differentiability
transfer plus the chart differentiability bridge is also a valid split. Do not assume differentiability of the
N-Hamiltonian as a premise. Openness of the actual working cylinder may remain E11's obligation, as the handoff
explicitly assigns it there; the present finding does not demand moving that obligation into E10.

## Declaration and node ledger

All names in this table are in `KAM.Planetary`.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| Cylinder inclusion helper | `workingCylinder_subset_enlargedCylinder` | PASS | Positive kappa gives the widened coordinate inequalities; strict slow bound implies the closed one. No extra geometry assumed. |
| `bpP:p14:hnu` (signed interface) | `hnu` | PASS for exact signature; FAIL for complete parent node | Telescope and conclusion text match the original signature exactly. Full blueprint parent additionally needs F1. |
| `stepP:p14:hn-eq` | `hnu` proof | PASS | Working ⊆ enlarged ⊆ chartSafe; actual chart splitting and real Kepler restriction; normalization cancels B0. No time rescaling. |
| `stepP:p14:hn-field`, derivative equality | `fderiv_eq_of_eqOn_open` | PASS | Generic neighborhood equality; openness and membership are legitimate local calculus premises. No differentiability premise is needed for this equality. |
| `stepP:p14:hn-field`, field equality | `hamiltonianVectorField_eq_of_eqOn_open` | PASS | Unfolds the frozen vector field and applies derivative equality; generic U supports the intended E11 specialization. |
| `stepP:p14:hn-field`, differentiability | No implementation / companion export | FAIL | F1: neither the signed equality nor the generic totalized derivative lemmas discharge this clause. |
| `stepP:p14:hn-field`, signs | `hamiltonianVectorField_neg` | PASS | All-point identity, stronger than the restricted blueprint statement; totalized derivative negation is valid. |
| `bpP:p14:sec-stopped#data`, signs | `degenerateHamiltonian_neg` | PASS | Exact negative of the frozen family, including its coupling argument; arbitrary a,b,mu,z. |
| `bpP:p14:sec-stopped#data`, integrable part | Imported `planetaryKeplerC` | PASS (reuse) | Existing Setting definition is the literal complex Kepler sum, not redefined in E10. |
| `bpP:p14:sec-stopped#data`, Hamiltonian family | Imported frozen `degenerateHamiltonian` | PASS (reuse) | Literal H0(fast z.2) + mu * P mu z. |

`hnu` is the only one of the six declarations with a supplied exact signature. The other five are separately
named implementation helpers, not unsigned exports masquerading as a complete graph-node conclusion.
Its arbitrary real mu and arbitrary n follow the signed contract; the source's positive-mu specialization is
available. The perturbation equality premise is the E7 supplier's conclusion, not an assumed Hamiltonian or
dynamical conclusion. No constant dependence is widened.

## Definitions, hypotheses and imports

E10 adds **no def, abbrev or structure**. Imported `Phase`, `fast`, `realPart`, `complexifyPhase`, the cylinders,
Kepler part and degenerate Hamiltonian retain their existing intended bodies. No new fallback or junk value
is introduced. The proof uses chart membership before applying the physical chart splitting.
The two generic equality helpers have distinct conditional names and legitimately accept equality on U.
No difficult dynamical estimate is bundled into a premise or instance.

Recursive inspection of the 111 reachable KAM source modules (including E10) found **no provider module and no
frozen theorem module**. Thus there is no DRAFT_SORRY theorem import or provider-quarantine violation in E10's
import closure. The ultimate `planetaryExponentialSafety` anchor remains `DRAFT_SORRY`; E10 neither imports nor
seals it. Provider/frozen type equality and seal-body probes are inapplicable here because E10 has no provider
export. They must be performed on the eventual provider package, not substituted by this helper audit.

## Independent validation

All Lean checks were serial with `LEAN_NUM_THREADS=1`; explicit build/probe/kernel commands used
`nice -n 5`, and the build used the prescribed gate.
No resource override, cache reset, package edit or git mutation was performed.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e10 KAM.Planetary.Exponential.Hamiltonian
   [inp-gate] slot 1 acquired 18:53:26 for KAM.Planetary.Exponential.Hamiltonian
   Build completed successfully (9157 jobs).
   exit 0
   ```

   Replayed upstream warnings: unused variables in Kepler/Energy, Poincare/Chart, Kepler/Mass and
   Exponential/RealDomain; deprecated `dif_pos` in Exponential/ComplexTube. No diagnostic from the audited file.

2. Exact signature and axioms probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E10Audit.lean
   exit 0
   ```

   A Python text comparison of `theorem hnu` through the type, before the body delimiter, against
   `/root/code/KAM-inp/.drafts/design/P14Signatures.lean:353` returned `hnu literal signature equal: True`.
   The probe copied that entire telescope and type under the fresh name `E10Audit.signature_hnu` and proved it
   by `exact KAM.Planetary.hnu B hB hd hB0 hP`. No admitted signature module was imported.
   All six `#print axioms` outputs were:

   ```text
   'KAM.Planetary.workingCylinder_subset_enlargedCylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.hnu' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fderiv_eq_of_eqOn_open' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.hamiltonianVectorField_eq_of_eqOn_open' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.hamiltonianVectorField_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.degenerateHamiltonian_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.Hamiltonian
   replaying KAM.Planetary.Exponential.Hamiltonian
   exit 0
   ```

   One invocation covers the sole audited module; there are no separate E10 lemma/provider modules.

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
   Lean lines over 100 characters:
   /root/code/KAM-inp-p14-e10/KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77:101
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (887 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The generated-root exception is explicitly permitted. The frozen 101-character line is an additional,
   pre-existing out-of-scope failure, not an E10 line-length failure; it was not edited. Global lint therefore
   does not pass literally. Audit execution deviation: lint was initially launched through plain `sh` rather
   than a `nice` wrapper. Its shell, ABI helper and associated Lake/Lean processes were subsequently set to
   niceness 5. No other Lean check overlapped it; the one-thread constraint was maintained.

5. Scoped static hygiene: 102 lines, zero lines over 100 characters, required copyright/module/public
   imports/docstring/public section present. No forbidden proof escape, resource override or EuclideanSpace.
   Exact declaration-name search across KAM and Mathlib found only these six declarations in E10; no reused
   public helper short name or root shadow found. `git diff --check inp...HEAD --
   KAM/Planetary/Exponential/Hamiltonian.lean` exited 0 (with the merge-base warning below).

## Comparison caveat and unchanged boundaries

The required `git diff inp...HEAD` was run. At inspection `inp` was
`df02e253a1f2b532e8636ef6b998f7b475ad3735`. Git reported:

```text
warning: inp...HEAD: multiple merge bases, using 62df27d9195579fb9ee1f4f7c29e7b9fceaff614
```

`git merge-base --all inp HEAD` returned that commit and `e2088d57c609cc20f1033b70a41e064402222f53`.
The selected comparison includes 161 changed files and is not an isolated E10 delta.
The literal required protected-path check is **nonempty**:

```text
git diff inp...HEAD --numstat -- KAM/Frozen manifest KAM.lean README.md
94  0  KAM.lean
2   1  KAM/Frozen/Planetary/Theorems/AmdConfinement.lean
1   1  manifest/frozen-anchors.json
```

This cannot be reported as a passing empty-diff check. For attribution only, `git diff HEAD^ HEAD --stat`
shows exactly the 102-line E10 addition, and `git diff --name-only HEAD^ HEAD -- KAM/Frozen manifest KAM.lean
README.md` is empty. Accordingly, no protected-file edit is attributed to the E10 commit. The broader comparison
must be reconciled by the orchestrator; this audit did not change the base, root, manifest or frozen files.

## Errata, deviations and limits

No suspected pinned-paper defect or false frozen statement was found. F1 is an implementation omission against
an explicit design/blueprint obligation. The sign statements and normalization agree with the pinned route.
The missing bridge is not supplied by successful compilation or axiom checks. No source repair was attempted.
Only this report persists from the audit; temporary probe/log files are removed after validation.
