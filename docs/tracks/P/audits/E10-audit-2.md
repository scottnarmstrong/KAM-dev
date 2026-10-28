# E10 independent audit 2 — delta audit

Overall verdict: **PASS WITH NOTES — F1 closed; E10's assigned infrastructure slice is complete.**
The notes concern inherited global lint/protected-path differences, not the new lemma.
No frozen anchor is proved or declared seal-ready by this infrastructure audit.

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p14-e10`.
Audited HEAD: `bf1657c67bca994d49c40f8bf8642109712ab127`.
Round-1 baseline: `7c9de2ac`.
Scope: only `KAM/Planetary/Exponential/Hamiltonian.lean` and the repair of round-1 F1.
The explicit user destination overrides the generic brief's main-worktree report destination.

Read the package brief, AGENTS.md, PLAN, DECISIONS, handoff, round-1 report, P14 design,
both design audits, original signed `hnu` telescope, blueprint/packet contracts, track statement,
relevant frozen definitions and ultimate exponential-safety anchor. Prior six-theorem semantic
verdicts are carried forward only after verifying their complete source bytes unchanged;
build, signature elaboration, all seven axiom checks, kernel replay and lint were rerun independently.

## Delta integrity

```text
git diff 7c9de2ac HEAD --stat
 KAM/Planetary/Exponential/Hamiltonian.lean | 29 +++++++++++++++++++++++++++++
 1 file changed, 29 insertions(+)

git diff 7c9de2ac HEAD --numstat
29  0  KAM/Planetary/Exponential/Hamiltonian.lean
```

The single zero-context hunk is `@@ -85,0 +86,29 @@`: one docstring, one theorem and its proof.
Thus the delta is additions only. Precisely, the block is inserted before the two existing sign
theorems; it is not a literal append at EOF. There are no replacements, deletions, changed imports,
or changes to existing declarations. Removing lines 86–114 recovers the baseline file byte for byte:

```text
prior file recovered byte-for-byte: True
baseline and recovered SHA256:
6c93878793dd758947590f16fadbc7c0cf9d5dde32c616a9276f3d81a8aa46cd
signed hnu literal type equality: True
```

The recovery comparison encoded the reconstructed Unicode text to UTF-8 before comparing bytes.
The signed telescope was compared literally with
`/root/code/KAM-inp/.drafts/design/P14Signatures.lean:353`, through the type before `:=`.
The full old file, including `hnu`'s proof and the other five proofs, is unchanged.

## F1 closure and source fidelity

`differentiableAt_hnu_field` at Hamiltonian.lean:89–113 concludes, for every `w ∈ U`,

```lean
DifferentiableAt ℝ H₁ w ∧ fderiv ℝ H₁ w = fderiv ℝ H₂ w ∧
  KAM.hamiltonianVectorField H₁ w = KAM.hamiltonianVectorField H₂ w
```

Its local lets are exactly the positive N-Hamiltonian at coupling `B0*mu` and
`movingHamiltonian 1 1 B.mass mu ∘ poincareProd B.mass 1`.
The domain parameters are any open `U ⊆ workingCylinder B kappa A`.
Taking `U = workingCylinder B kappa A` and inclusion `Set.Subset.rfl` gives the literal
differentiability and field equality at every point of V. This specialization was elaborated
in the independent scratch probe, retaining only V's source openness as a geometric premise.
The design identifies V using G=`fastBox B kappa`, D=`slowBall n A`, which is exactly the
definition of `workingCylinder` (Setting.lean:54). Proving its openness remains E11's obligation,
as expressly allowed in the handoff and round-1 F1. No differentiability premise is introduced.

The other premises are the original admissible B, source enlargement inequalities, positive B0,
and E7's perturbation agreement `hP`; the latter is unchanged from the signed `hnu` contract.
They do not assume differentiability of either Hamiltonian, a vector-field identity or a solution.
Arbitrary real mu and arbitrary n are stronger than the source's positive-mu, n≥2 specialization.
There are no new constants or widened constant dependencies.

The proof establishes actual chart differentiability at lines 105–110: working-cylinder membership
gives enlarged-cylinder and chartSafe membership via `real_domain`; positive masses follow from
admissibility. It composes `differentiableAt_movingHamiltonian` (Newtonian/Models.lean:335)
with `analyticOnNhd_poincareProd` (Poincare/Product.lean:168). Neighborhood equality, obtained
from the unchanged `hnu`, then transfers differentiability through
`Filter.EventuallyEq.differentiableAt_iff`. The two unchanged helpers supply derivative and field
equality. It therefore repairs exactly the gap between totalized derivative equality and actual
differentiability identified in round 1.

This discharges blueprint `p14a-amd-expsafe.tex:265,269`, packet
`P-p14a2.nodes.md:1156–1158`, and E10's explicit assignment in
`DESIGN-P14-design-audit-2.md:72`. It supplies the differentiability clause consumed at blueprint
line 282 when constructing the genuine N-system solution predicate. This is interface availability,
not a claim that E11 itself has been implemented or audited.

## Declaration ledger

All declarations are in `KAM.Planetary`; line numbers refer to the current module.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| Cylinder inclusion | `workingCylinder_subset_enlargedCylinder` (:40) | PASS | Complete prior proof byte-unchanged; source geometry. |
| `bpP:p14:hnu`, `stepP:p14:hn-eq` | `hnu` (:50) | PASS | Exact signed type and unchanged proof; actual normalized Hamiltonian equality. |
| `stepP:p14:hn-field`, derivative equality | `fderiv_eq_of_eqOn_open` (:75) | PASS | Prior generic local equality proof unchanged. |
| `stepP:p14:hn-field`, field equality | `hamiltonianVectorField_eq_of_eqOn_open` (:81) | PASS | Prior proof unchanged. |
| `stepP:p14:hn-field`, differentiability and field equality | `differentiableAt_hnu_field` (:89) | PASS | New companion proves the missing clause, including derivative/field equality; V specialization elaborates. |
| `stepP:p14:hn-field`, negative field | `hamiltonianVectorField_neg` (:116) | PASS | Prior all-point sign proof unchanged; combines with the Hamiltonian sign identity. |
| `bpP:p14:sec-stopped#data`, negative Hamiltonian | `degenerateHamiltonian_neg` (:122) | PASS | Prior exact negative-family proof unchanged. |
| `bpP:p14:sec-stopped#data`, integrable part | Imported `planetaryKeplerC` | PASS (reuse) | Existing literal Kepler sum; no new definition. |
| `bpP:p14:sec-stopped#data`, Hamiltonian | Imported frozen `degenerateHamiltonian` | PASS (reuse) | Existing literal `H0 (fast z.2) + mu * P mu z`. |

## Definitions, names and hygiene

No new `def`, `abbrev` or `structure`, and no new fallback or junk values. H₁/H₂ are local lets
with the intended literal bodies on their whole carriers. The sole new export has a distinct name.
Declaration-name searches across KAM and Mathlib found each of the seven short names only at its
own declaration in this module; no reused public helper short name or root shadow was found.
Recursive inspection of all 111 reachable KAM source modules found no provider or frozen theorem
import. Provider/frozen exact-type and seal-body probes are inapplicable: E10 exports no provider
and seals no anchor. The ultimate `planetaryExponentialSafety` anchor remains `DRAFT_SORRY`.

The module has 131 lines, maximum Unicode line length 100, and the required copyright, `module`,
public imports, module docstring and public section. No forbidden proof escape, resource override,
or EuclideanSpace occurs. No heartbeat design signal occurred.

## Independent checks

All Lean/Lake checks were serial, with `LEAN_NUM_THREADS=1` and niceness 5; the build used the
prescribed gate. No clean, update, cache download, package modification or git mutation was run.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e10 KAM.Planetary.Exponential.Hamiltonian
[inp-gate] slot 1 acquired 19:25:12 for KAM.Planetary.Exponential.Hamiltonian
Build completed successfully (9157 jobs).
exit 0
```

The gate invokes `nice -n 5 lake build`. Only upstream warnings were replayed: unused variables
in Kepler/Energy, Poincare/Chart, Kepler/Mass and Exponential/RealDomain; deprecated `dif_pos`
in Exponential/ComplexTube. No diagnostic came from the audited file.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E10Audit2.lean
exit 0
```

The probe copied the signed `hnu` type under a fresh name and supplied
`exact KAM.Planetary.hnu B hB hd hB0 hP`. A second fresh theorem stated the new conclusion on
the whole working cylinder and supplied
`exact KAM.Planetary.differentiableAt_hnu_field B hB hd hB0 hP hV Set.Subset.rfl hw`.
It did not import the admitted design-signature module. All seven axiom outputs were:

```text
'KAM.Planetary.workingCylinder_subset_enlargedCylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hnu' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_eq_of_eqOn_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hamiltonianVectorField_eq_of_eqOn_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableAt_hnu_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hamiltonianVectorField_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.degenerateHamiltonian_neg' depends on axioms: [propext, Classical.choice, Quot.sound]

LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.Hamiltonian
replaying KAM.Planetary.Exponential.Hamiltonian
exit 0
```

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
Lean lines over 100 characters:
/root/code/KAM-inp-p14-e10/KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77:101
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (887 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

Global lint does not literally pass: the generated-root complaint is the brief's allowed exception;
the frozen 101-character line is an additional inherited, out-of-scope failure already documented
in round 1. Neither was edited, and there is no E10 line-length or substantive source-lint failure.
The module-system, frozen-anchor and elaborated-ABI checks pass independently.

## Comparison caveat and limits

The required `git diff inp...HEAD` comparison was run (stat, scoped full module diff and protected paths).
At inspection `inp` was `f5376c6dffbc49d970aeb4f9b37796a46f764133`.
Git warned `multiple merge bases, using 62df27d9195579fb9ee1f4f7c29e7b9fceaff614`.
`git merge-base --all inp HEAD` returned that commit plus
`e2088d57c609cc20f1033b70a41e064402222f53` and `bd819d083124558f56762996622bf6f53fc263d1`.
The selected comparison includes 163 files and is not an isolated E10 delta.

```text
git diff inp...HEAD --numstat -- KAM/Frozen manifest KAM.lean README.md
94  0  KAM.lean
2   1  KAM/Frozen/Planetary/Theorems/AmdConfinement.lean
1   1  manifest/frozen-anchors.json
```

This literal protected-path check is nonempty, as in round 1. It is not a passing empty-diff check.
In contrast, `git diff 7c9de2ac HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
Only Hamiltonian.lean changed since that baseline; none of the inherited protected changes belongs
to the F1 repair. The orchestrator must reconcile the broader comparison before landing.
Both `git diff --check 7c9de2ac HEAD` and the scoped
`git diff --check inp...HEAD -- KAM/Planetary/Exponential/Hamiltonian.lean` exited 0.

No suspected pinned-source defect, false frozen statement or introduced mathematical deviation
was found. The implementation omission F1 is closed. Openness remains the explicitly assigned
E11 geometry obligation; no broader theorem or consumer closure is asserted. Only this report
persists from this audit; the scratch probe is deleted after validation.
