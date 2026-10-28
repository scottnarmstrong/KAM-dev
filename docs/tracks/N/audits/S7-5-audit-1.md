# S7-5 independent package audit 1

**Overall: PASS WITH NOTES.** The S7-5 design targets are proved with their exact signatures. `exists_orthProj` and `energy_core` each receive **PASS**. No frozen anchor is sealed by this infrastructure package; provider/frozen type and proposed seal-body probes are therefore inapplicable. The notes below limit graph-node and consumer claims, rather than require a proof repair.

## Scope and authority

Audited only `KAM/Nekhoroshev/Stability/Energy.lean`, as required by the handoff's AUDIT FOCUS. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff, design v2 B.6 and S7-5 row/proof plan, both design audits, blueprint-N Part 7, the corresponding graph entries, Track N's statement, and the relevant imported definitions/ODE interfaces. The user's explicit report location overrides the generic brief's main-worktree destination.

Snapshot:

- Worktree: `/root/code/KAM-inp-s75`.
- HEAD: `7ff4bf545d702d51cb9e7f7898273d39b3e2b1fd`.
- `inp` at intake: `1699a58fc52973a29e47f1636a414db9a7ffda8d`.
- `git diff inp...HEAD --stat`: `.drafts/handoff-S7-5.md` (29 added lines), `KAM/Nekhoroshev/Stability/Energy.lean` (332 added lines); 361 insertions total. S7-1 is inherited, not part of this audit.
- Energy SHA-256: `3769639d4d8fc956bfb1f920faf6e40fe79b480d07ebc7006fa5a719063f49c8`.

No subagents, state-changing git commands, frozen edits, root regeneration, dependency edits, or resource overrides were used. Auditor-started Lean/lake/checker invocations were serial, with `LEAN_NUM_THREADS=1` and nice level 5. Temporary probes were confined to this worktree's `.lake/abi-scratch/` and removed after checking. Only this report is retained as an auditor change; the pre-existing untracked handoff was preserved.

## Declaration ledger

All names below are in `KAM.Stability`; line numbers refer to `Energy.lean`. Private helper names are their source names, not stable public exports.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| p7:ext-linalg / resonance-data | `IsOrthProj` (30), including `idem`, `symm` | PASS | Idempotent, dot-product self-adjoint linear map; literal design structure. |
| p7:ext-linalg, S7-5 existence target | `exists_orthProj` (36) | PASS | Arbitrary real subspace, range containment, identity on the subspace, idempotence and symmetry; exact design type. |
| Extra public helper | `clm_eq_dot` (67) | PASS | Every continuous real linear functional is represented by its coordinate-basis values. No extra premise or norm change. |
| Private Taylor helper | `taylor_segment` (77) | PASS | Open-domain C² regularity and the full action segment yield the exact second-order remainder at an interior parameter. |
| p7:resonance-data | `resSpace` (140) | PASS | All integer resonance pairings vanish; arbitrary subset of the integer lattice. |
| p7:resonance-data | `IsCloseToRes` (143) | PASS | Euclidean distance bound expressed by an attained witness in the resonance subspace. |
| p7:resonance-data | `IsMConvex` (148) | PASS | Euclidean lower Hessian bound on the specified real domain, all real directions. |
| p7:resonance-data | `IsQuasiConvex` (152) | PASS | Strict gradient alternative OR non-strict curvature bound, exactly as in blueprint/design. |
| p7:resonance-data | `HessBound` (157) | PASS | Absolute bilinear Hessian estimate in Euclidean sizes, not a Pi sup-operator norm. |
| Extra public helper | `euclid_sq_eq_dot` (161) | PASS | Correct square identity, including dimension zero. |
| Extra public helper | `abs_dot_le_euclid` (167) | PASS | Cauchy–Schwarz for the actual dot product and Euclidean size. |
| Private differentiation helper | `HR_diffAt` (179) | PASS | Local equality on an open product transfers differentiability and derivative decomposition to the actual Hamiltonian. |
| Private differentiation helper | `theta_split` (198) | PASS | Correct theta-gradient splitting; action-only term vanishes. |
| Private orbit helper | `hasDerivAt_dot_snd` (211) | PASS | Hamiltonian sign and action component are correct for phase order `(theta, I)`. |
| p7:energy-core, steps ec-energy/ec-proj/ec-taylor | `energy_core` (237) | PASS | Exact v2 signature, all four conclusions and quantifiers, genuine Hamiltonian orbit, no strengthened source premise. |

## Statement fidelity and proof review

A whitespace-normalized comparison reports `True` for both theorem signatures (`exists_orthProj`, `energy_core`) and for the complete six structure/definition bodies (`IsOrthProj`, `resSpace`, `IsCloseToRes`, `IsMConvex`, `IsQuasiConvex`, `HessBound`) against design B.6, lines 1134–1199. The definition rewrap in the handoff is harmless. A Lean probe copied the two verbatim design theorem signatures under fresh names and supplied the proved exports; both elaborated successfully. These are design-interface probes, not frozen-anchor probes.

The projection proof uses the positive-definite dot bilinear form, proves nondegeneracy on the arbitrary subspace, constructs its projection along the orthogonal complement, and obtains symmetry from the two decompositions. It does not infer Euclidean orthogonality from the ambient Pi norm. No positivity-of-dimension assumption is required.

For `energy_core`:

1. Local equality `hHR` transfers C¹ regularity to `HR` at orbit points before applying `KAM.ODE.ham_energy`. Thus the totalized `fderiv` in the frozen Hamiltonian field has its intended derivative value.
2. With `Delta = I(t₁)-I(0)` and `c = Delta-P Delta`, idempotence gives `P c=0`. Symmetry and `hgP` annihilate the resonant gradient. The scalar observable `c dot I(t)` has derivative `-c dot thetaGradR f`; Cauchy–Schwarz and the interval mean-value inequality give the square bound. Cancellation handles positive Euclidean size; size zero is handled separately, with `B >= 0` derived from its bound at time zero. This works for negative time and `t₁=0` using `uIcc`.
3. The line restriction of `hR` is C² on the segment, with ordinary derivatives justified on the open preimage of `U`. The proof identifies both within-iterated derivatives before using the Lagrange remainder; endpoints and `Delta=0` are covered.
4. The Hessian lower bound in (d) is precisely the blueprint's conditional assumption on this segment/direction, rather than a concealed substitute for the entire theorem. Symmetry splits the initial gradient pairing; the energy identity and two Cauchy–Schwarz estimates yield the stated three terms.

Conclusion (b) uses any uniform upper bound `B` instead of a written supremum, as prescribed by the design. C¹ regularity and continuity of the orbit on the compact time segment make the blueprint's supremum finite and supply this specialization. There is no changed constant or dimension factor. The segment, regularity, projection, interval and orbit assumptions all come from the blueprint. No conclusion-shaped hypothesis was added.

## Definition classification and imported objects

- `IsOrthProj` is a genuine algebraic characterization of a Euclidean orthogonal projection. Its range is intentionally unspecified; `exists_orthProj V` attaches it to `V`.
- `resSpace` is the actual homogeneous resonance subspace. It contains zero and is closed in finite dimension. Thus the attained-witness definition of `IsCloseToRes` equals distance at most `delta`, including the boundary equality case. No positive-delta premise is silently needed for this equivalence.
- `IsMConvex`, `IsQuasiConvex`, and `HessBound` are literal local derivative predicates, not bundled proof conclusions. As in the design, they do not themselves impose holomorphy or regularity: their derivatives are total Lean `fderiv` expressions on the whole carrier, and analytic/regularity hypotheses are supplied at their mathematical uses. No argument in this module exploits a non-differentiable fallback. In particular `energy_core` separately requires C²/C¹ regularity and does not rely on these predicates to infer it.
- The frequency is the frozen `KAM.frequencyMap`, the real restriction is the frozen `KAM.Nekhoroshev.realPart`, and the Euclidean size is `sqrt(sum_i norm(x_i)^2)` from `Interfaces/Norms`. `hessR`, `thetaGradR`, `IsSolutionIn` and the Hamiltonian field are the inherited objects, not replacements.
- No other new definitions, abbreviations, structures or instances occur in Energy.

A recursive source-import check found 50 KAM modules, 19 frozen definition modules, zero provider modules and zero frozen theorem modules. Therefore no DRAFT_SORRY theorem is imported, and there is no imported theorem whose SEALED status needs an exception. The axiom receipts below independently exclude hidden use of `sorryAx` in the audited results.

## Nonblocking notes and scope limits

**N1 — external-node coverage.** Blueprint `blueprint-N/parts/p7-stability.tex:20` lists, besides existence/self-adjointness, “`norm(Pi v)_2 <= norm v_2`” and the projection/distance identity. The design's S7-5 target at `PART67-LEAN-DESIGN.md:1142` is specifically `exists_orthProj`, and that target is fully proved. Energy has no separately exported contraction or distance-identity lemma. Its proof of (b) validly avoids needing a contraction lemma through the scalar observable. The graph packet at `docs/graph/N/packets/N-p7.nodes.md:79` still classifies `ext-linalg` as EXTERNAL. This audit approves the delivered existence target and the actual uses, not a claim that every formula listed in the external node now has a named Lean theorem. Other consumers needing the distance identity must supply or locate it; do not infer its API availability from this package alone.

**N2 — reuse wording.** `Energy.lean:236` repeats the design docstring “reusable core; track I, Part 11”. Design v2 section 8 and its second audit correctly qualify I as prospective reuse, while `blueprint-N/parts/p11c-partial-stability.tex:89` says the canonical core “is not applied” and only its argument is repeated in the extended phase space. Likewise Part 7's closing paragraph and graph packet note at line 1250 retain broader consumer wording. These are documentation limitations already identified by the design audit, not proof defects or certified applications to an extended carrier. No I/N/P frozen headline is closed here.

No new suspected defect in a pinned primary source was established. This is a Lean package/design/blueprint audit, not a fresh PDF transcription audit. The scalar mean-value proof is a valid implementation choice within the design's Cauchy–Schwarz route; no mathematical source deviation was introduced by the auditor.

## Independent verification receipts

Targeted build (through the required compile gate):

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-s75 KAM.Nekhoroshev.Stability.Energy
[inp-gate] slot 2 acquired 06:43:19 for KAM.Nekhoroshev.Stability.Energy
Build completed successfully (3202 jobs).
exit 0
```

The gate runs `nice -n 5 lake build`. No new whole-library build was requested and no warnings were emitted.

Design signature and axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S75Audit.lean
'KAM.Stability.exists_orthProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.clm_eq_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.euclid_sq_eq_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.abs_dot_le_euclid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.energy_core' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0; no warnings or errors
```

Kernel replay (one invocation for the sole new module):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Stability.Energy
replaying KAM.Nekhoroshev.Stability.Energy
exit 0
```

Source lint (nice level and one-thread environment are inherited by its serial ABI-check subprocess):

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (427 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

This is PASS under the brief's explicit generated-root exception; the raw exit status is retained above. No other lint failure occurred. Energy has 332 physical lines and maximum line length 100 Unicode characters. Its module header, public imports, module docstring and exposed public section satisfy the module convention. Lint found no forbidden proof escape, resource override, code occurrence of `EuclideanSpace`, or size violation.

Final checks:

```text
git diff --check inp...HEAD
exit 0; no output
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
exit 0; no output
git diff --check -- docs/tracks/N/audits/S7-5-audit-1.md
exit 0; no output
```

Because this report is untracked, its trailing whitespace and balanced code fences were also checked directly with Python. The two auditor-created scratch files (`S75Audit.lean`, `S75-leanchecker.log`) were removed. Final status contains only the pre-existing untracked handoff and this new report. The audited module's SHA-256 remains the intake hash. No proof or statement repair is required for the delivered S7-5 targets; N1–N2 are the remaining scope/documentation limitations.
