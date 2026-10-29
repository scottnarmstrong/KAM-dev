# GAP-I1c independent audit 2

Overall: **PASS WITH NOTES**. Both scoped parent nodes have literal source-hypothesis,
arbitrary-frequency exports in the new `_src` declarations. Audit 1 F1 is discharged.
The earlier `_anyOmega` declarations remain specialized helpers; they alone still do not
state the full source setting. No frozen theorem anchor is supplied or sealed by this package.

Audited 2026-10-29, worktree `/root/code/KAM-inp-gi1c`, HEAD
`7dce3d672c56bd76867c4134e80f917dfebd5ebd`, `inp`
`74976f317ab6852d2a7222801accf8ce39ba0615`.
The complete `git diff inp...HEAD` adds the 380-line
`KAM/Iso/Linear/FullRangeAnyOmega.lean`, the 212-line first audit, and the 39-line handoff;
no other tracked file differs. The merged GAP-I1a dependencies are already in the comparison
base. Only the requested Lean module is audited; imported bridge interfaces were inspected
as dependencies. This report's exact worktree path follows the prompt over the generic brief.

Read: AGENTS.md, PLAN, DECISIONS, package brief, tracked handoff and audit 1, the round-2
addendum in `.drafts/handoff-GAP-I1c.md:36-50`, track-I statement and Part123 design,
GAP-PLAN-I §2 and GAP-I1c, graph records at `docs/graph/I/DEPGRAPH.md:2389` and `:2712`,
and `blueprint-I/parts/p1-iso-linear.tex:30-45`, `:483-503`, `:566-590`.

## Node and declaration verdicts

Names below are in `KAM.Iso.Linear.AnyOmega`; locators are lines in the audited module.
No declaration in this new module is SIGNED in Appendix A. The signed landed `Linear.reduced`
and `Linear.perturbation_noA5` are unchanged. Provider/frozen-type equality and seal-body
checks are inapplicable: both graph records have `FROZEN_FILE: -` and `FROZEN_DECL: -`.

| Node or role | Declaration | Verdict | Reason |
|---|---|---|---|
| `bpI:p1:reduced` | `reduced_anyOmega_src`, :320 | PASS | Literal SettingSrc; arbitrary tested ω; all (a)-(d) conclusions. |
| `bpI:p1:perturbation-noA5` | `perturbation_noA5_anyOmega_src`, :343 | PASS | Literal SettingSrc, free real σ parameters; only tested-frequency restriction is its source norm bound; all (a)-(e). |
| Specialized reduced assembly | `reduced_anyOmega`, :129 | PASS as helper | Arbitrary tested ω, but retains stronger Setting; not the literal source export. |
| Specialized perturbation assembly | `perturbation_noA5_anyOmega`, :266 | PASS as helper | Same specialization; derives frame and torsion estimates internally. |
| `fi-dl` helper | `fi_dL_anyOmega`, :45 | PASS as helper | Genuine derivative identity with independent ω. |
| `fi-22` helper | `fi_LtOXN_anyOmega`, :71 | PASS as helper | Hamiltonian symplecticity and differentiated frame pairing give the signed identity. |
| `fi-blocks` helper | `fi_reduced_anyOmega`, :84 | PASS as helper | Block reduction is proved, not assumed. |
| `rd-expand` helper | `reducer_mulVec_isoResidual_anyOmega`, :102 | PASS as helper | Product rule, QP, QE and QL identities establish the residual formula. |
| Conditional `pt-xn` helper | `norm_normalField_sub_le_strip_anyOmega`, :186 | PASS as conditional helper | Takes frame estimates as intermediate inputs; not offered as a standalone literal graph-node export. |
| Conditional `pt-torsion` helper | `norm_torsion_sub_le_anyOmega`, :218 | PASS as conditional helper | Takes normal-frame/field bounds; parent derives those before application. |

The GAP-I1c plan maps exactly two parent nodes to this module. Both are established by the
`_src` exports. Conditional helpers do not enlarge the claimed graph slice. No new consumer
or signed interface is changed. This is package proof closure, not global graph bookkeeping
or closure of I-G1/I-HEAD.

## Why F1 is closed, and frequency fidelity

The source setting says “Let $n\ge2$ and $\tau\ge0$”
(`blueprint-I/parts/p1-iso-linear.tex:31`). `SettingSrc` has exactly those parameter ranges,
M positive, the open invariant domain, holomorphy/periodicity/reality and Hamiltonian bounds,
and a standing Diophantine frequency ω₀ (`SettingSrc.lean:34-50`). It has no σ fields.
`SettingSrc.setting` at :60-76 constructs the stronger Setting; its τ field is proved through
`SettingSrc.tau_ge` and `IsDiophantine.n_sub_one_le_tau`, not demanded of the caller.
Unlike audit 1's checkout, this bridge is present and imported through `FullRange`.
The new parent types contain neither its output nor a conclusion-shaped hypothesis.

For reduced, :338 chooses σK=σB=σT=1 only inside the proof; none occurs in the conclusion.
For perturbation, :364-374 uses `max σK 1`, `max σB 1`, `max σT 1` to supply positive internal
parameters. The input derivative/inverse bounds imply the enlarged bounds. The existing
`mSize_max_one` identity (`FullRange.lean:41-47`) gives equality of the old and enlarged
mSize. Inspection of `KAM/Apost/Constants.lean:66-121` confirms Θ, C_B, C_DN, C_DX, C_X and
C_DT depend on σ only through mSize. Thus both hω and smallness rewrite exactly, and every
output constant rewrites back exactly. No positivity premise or larger constant is exported.
In particular σT is an unrestricted real parameter of the `_src` theorem.

Printed elaborated types bind ω₀ with the outer source setting, then quantify a fresh tested
ω. Reduced imposes no restriction on tested ω; perturbation imposes only `‖ω‖ ≤ Theta ...`.
There is no equality, ray relation or Diophantine assumption linking tested ω to ω₀. The
standing frequency is legitimate because the source setting includes one, as the audit focus
explicitly allows. The Hamiltonian regularity, symplecticity, linMat bounds and Taylor estimate
supplied through Standing do not depend on the tested frequency. All directional identities
and bounds use the fresh ω. Both exports permit tested ω=0 subject to the displayed bound.

Setting data are outermost, with tested ω before r', ξ, ξω in reduced. Perturbation's r,δ
precede tested ω; β,d are implicit universals earlier than the prose list, and the free σ's
precede K. These permutations are among universal inputs; no existential constant acquires
additional dependence. Carriers are the required Fin-function spaces and matrix row-sum norm.

Reduced's matrix clause (a) implies its displayed “hence” vector formula by multiplication;
that formula is also explicitly proved as hQLω at :114-120. Unfolding isoResidual, bordOp and
isoLinError (`Defs.lean:99-125`) gives exactly the source signs and Δω=-ωξω convention.
The norm bound is unconditional, stronger than source (c). Its bordered-system implication is
pointwise, also stronger. Clause (d) retains the source's additional frame-invertibility
condition and the correct residual equivalence. Primary/reality assumptions on K are omitted
where unused, strengthening the local identities. The parenthetical Neumann sufficiency
reference in source (d) concerns the separate rd-consequence proof obligation, not an extra
premise silently supplied here.

Perturbation preserves all five conclusions, balls, shrunken strips and constants. The parent
obtains hb,hc,hdN from `frame_items` at :297, then hG', hKD, hAb, hXX and he at :298-305.
Thus the conditional helpers' hNN/hXX inputs are discharged internally. There is no A5,
bordered-twist, or proved dependency output in either literal parent signature.

## Definitions and totality

There are no new def, abbrev or structure declarations. The local set bindings are proof
abbreviations. Imported gramMatrix, normalFrame, torsion, invarianceError, IsDiophantine and
residual/operator definitions were inspected. Gram inverses have explicit IsUnit determinant
hypotheses on their relevant strips, with new-frame invertibility derived before use.
The residual inverse has the extra frame determinant hypothesis and proved reducer
invertibility. Holomorphy on open domains supplies actual derivatives. No fallback inverse,
derivative or junk definition is used to obtain the claimed conclusion.

## Independent validation

All Lean/Lake/checker work was serialized, `LEAN_NUM_THREADS=1`, nice level 5. No budget
or recursion override was used. Probe sources/logs were confined to `.lake/abi-scratch/`
and removed after recording results.

Targeted build (the gate invokes `nice -n 5 lake build`):

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gi1c KAM.Iso.Linear.FullRangeAnyOmega
[inp-gate] slot 1 acquired 05:33:38 for KAM.Iso.Linear.FullRangeAnyOmega
Build completed successfully (3205 jobs).
exit 0
```

Fresh declaration/application and axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPI1cAudit2.lean
```

Probe exit: **0**, no errors or warnings.

The probe prints elaborated types and axioms of all ten public theorems, and copies all four
parent statements under fresh names with direct application bodies listing every explicit
binder in order. The two source-wrapper statements contain no σ positivity or τ≥n−1 premise.
It additionally checks axioms of SettingSrc.setting and the Dirichlet exponent bridge.
Every one of these twelve declarations prints exactly (line wrapping normalized):

```text
[propext, Classical.choice, Quot.sound]
```

No sorryAx or other axiom occurs. This is an application/type probe of the actual unsigned
exports, not a claim of equality with a nonexistent frozen any-ω signature.

Kernel replay:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Linear.FullRangeAnyOmega
replaying KAM.Iso.Linear.FullRangeAnyOmega
exit 0
```

Lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1272 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

This is the brief's explicit permitted generated-root exception; no other lint failure was
reported. KAM.lean was not regenerated. ABI checking finished before the final Lean probe.

Additional static checks:

- `git diff --check inp...HEAD` and `git diff --check`: exit 0, empty output.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- Module length 380 lines; maximum Unicode line length 100; required module header,
  copyright, public imports, module docstring and public section present.
- No forbidden proof token, resource override, EuclideanSpace or new root declaration.
- All ten public theorem short names have exactly one declaration occurrence under KAM/.
- Recursive local import traversal reaches 76 KAM modules, no provider and no frozen theorem
  anchor. Imported frozen definitions are allowed. DRAFT_SORRY/SEALED theorem-state lookup
  is therefore vacuous. Main-result axiom inspection also covers the added bridge dependency.

## Notes, suspected defects, deviations and limits

N1, audit 1 F1: **resolved for the two new `_src` exports**. The old specialized exports still
have their original narrower types and must not be cited alone as literal source closure.

Documentation note: the tracked handoff still names only the old exports and says N1 is
“unchanged, not addressed here” (:32). The module's opening bullets (:21-22) likewise call
the specialized exports “literal”. Those descriptions are stale/incomplete for round 2;
the precise literal export names are the `_src` names in the table above. The untracked
round-2 handoff addendum documents them correctly. This is not a proof or statement blocker.

The source setting's phrase “This is exactly Assumption” at blueprint :39 has the pre-existing
τ-range presentation mismatch with track K; the imported Dirichlet bridge supplies the needed
implication. No new pinned-source erratum, false frozen statement, mathematical defect or
code deviation was found. No external PDF claim was independently re-audited in this scoped
package review. No production file, graph record, manifest or generated file was edited;
the only lasting audit write is this report.
