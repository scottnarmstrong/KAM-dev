# GAP-ISM independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gism`.
Audited HEAD: `158682490fd4607248f9991d4458bca5e64e4501`.
Comparison ref `inp`: `ab86b8afe7bd9ea1d750a686045be1dd1951b1cb`.

**Overall: PASS WITH NOTES. All three requested graph nodes are CLOSABLE.**
The sole validation exception is the brief's explicitly permitted stale generated
`KAM.lean`. No proof, statement, definition, import, or source-fidelity defect was
found in the audited slice. This package adds node exports, not providers for
frozen theorem anchors; no frozen theorem is being declared newly seal-ready.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the AUDIT FOCUS in
`docs/tracks/I/audits/GAP-ISM-handoff.md`. The user's explicit absolute output path
overrides the generic brief's main-worktree destination.

Reviewed the entire `git diff inp...HEAD`: exactly one new file,
`KAM/Iso/LeftoverNodes.lean` (96 lines), containing exactly three public theorems
and no new definitions. Read the named frozen definitions, source graph records,
blueprint passages, track I statement, and relevant existing chart interfaces.
Existing dependency implementations were consulted to identify data and imports;
this report does not re-audit those packages or tracks N/P.

The three new declarations are UNSIGNED node exports: no signature/design entry
for these names was found in the worktree. They are therefore compared with the
literal graph/blueprint contracts, rather than treated as implementations of a
narrower signed statement. The Part 1–3 design's node table at
`docs/tracks/I/design/PART123-LEAN-DESIGN.md:211` maps the enclosing `tori` result
to `Charts/Tori` and treats its steps inside the proof (line 237); it does not
assign additional nodes to `LeftoverNodes`. The focused handoff assigns precisely
the following three nodes, all of which have exports. No missing declaration in
this slice was found. Existing signed declarations are unchanged.

## Node/declaration verdicts

| Node | Lean declaration and location | Verdict | Reason |
|---|---|---|---|
| `stepI:p6:k-pos` | `KAM.Iso.k_pos_node`, `KAM/Iso/LeftoverNodes.lean:33` | PASS; CLOSABLE | Both quotient positivity and determinant positivity, with κ > 0, Ω ≠ 0, and subtype L > 0. No Ω > 0 restriction and no determinant-value premise. |
| `stepI:p3:tori-patch` | `KAM.Iso.Charts.tori_patch_node`, `KAM/Iso/LeftoverNodes.lean:78` | PASS; CLOSABLE | Selects a member of the fixed finite cover and states all four requested inequalities, including the intermediate ε + δE/2 bound. Source patch/cover/uniform data precede ε, I₀, E. |
| `bpI:p7:sec-ham#data` | `KAM.Iso.sec_ham_data`, `KAM/Iso/LeftoverNodes.lean:44` | PASS; CLOSABLE | For every real μ, exports both set identities, openness, and the literal Hamiltonian and vector-field equations at every collision-free point. Definition correspondence is recorded below. |

### Positivity: hypotheses, order, proof

Graph: `docs/graph/I/DEPGRAPH.md:8136` (SOURCE_HYPOTHESES at 8143;
SOURCE_CONCLUSION at 8145). Blueprint:
`blueprint-I/parts/p6-kepler.tex:36`–47, especially 46–47.

The export fixes κ, Ω with `0 < κ`, `Ω ≠ 0` before quantifying over positive L,
matching the enclosing order. It proves
`0 < 3 * κ * Ω ^ 2 / L.val ^ 4 ∧ 0 < (keplerBorder κ Ω L).det`.
The enclosing frozen I-KEPLER uses Ω > 0; this step deliberately covers the
weaker Ω ≠ 0 hypothesis required by the focused graph contract. A fresh probe
also instantiated Ω = -1. The proof establishes Ω² > 0 from |Ω| > 0, uses L > 0,
then rewrites the determinant with landed `keplerBorder_det`. Its value is proved
by that dependency, not accepted as a theorem premise. No inverse or division at
zero is used. The matrix body at
`KAM/Frozen/Iso/Defs/KeplerBorder.lean:37` is the source matrix on all of its carrier.

### Patch choice: fixed data versus assumed conclusions

Graph: `docs/graph/I/DEPGRAPH.md:6373` (SOURCE_HYPOTHESES at 6380;
SOURCE_QUANTIFIERS at 6381; SOURCE_CONCLUSION at 6382). Blueprint:
`blueprint-I/parts/p3-iso-local-charts.tex:177`–200 (patch/cover),
359–368 (uniform constants), 372–391 (quantifiers and patch step).

`P, W, Ψ, δE, δm, ρc` and their `IsPatch` certificates, the cover certificate,
and ε₁ with its per-patch upper bound are fixed before ε, I₀, E. The source
family is represented by a finite set of centres, as in the existing `cover`
interface. No new constant is chosen after the variable point or energy.

The three data premises have specific source meanings:

- `hP` asserts the source definition of a patch, not the desired existence of a
  selected patch. In `KAM/Iso/Charts/Defs.lean:104`–126, the field `ball_h`
  (line 125) is exactly source (P3), blueprint line 183.
- `hcov` states that the already fixed balls cover `closure B'`, exactly the
  fixed family of `bpI:p3:cover` used in the source step.
- `hε₁` records the component ε₁ ≤ δE(c)/2 of the already fixed uniform minimum,
  blueprint lines 359–368.

These certify the source's fixed objects. The theorem does not assume a proved
dependency's selected-centre output, energy-window conclusion, torus existence,
or the target conjunction. It still proves the selection and every requested
inequality. It also does not purport to prove existence of the cover or uniform
constants: those remain their separate graph nodes. Their availability here is
consistent with the existing enclosing proof: `Charts/Tori.lean:289` obtains the
cover; lines 348–355 derive the same ε₁ bound before the energy-window argument.
No conclusion-shaped hypothesis was found.

After the fixed data, the binders are ε with ε < ε₁, I₀ in the closure, then E
with the energy discrepancy bound, as in the source. Source analyticity and
perturbation/ray assumptions are unnecessary for this step and are omitted;
η₁ is arbitrary fixed data. This generalization preserves the complete literal
conclusion when instantiated with the source data. In particular, `0 ≤ ε` is
already implied by `hE` and nonnegativity of absolute value. No source consumer
needs that hypothesis to be added back to this helper.

The real-slice expression is
`realPart h I = (h (toC I)).re` (`Confinement/Setting.lean:57`). It is source
h(I) under the standing real-on-reals assumption. Both the norm of I₀-c and the
cover's balls use the ambient sup norm, consistent with track I's conventions;
the physical radius below uses a different, explicitly Euclidean formula.

The proof unpacks the cover, applies (P3) at that point, obtains ε < δE/2 from
the fixed bound, and uses the scalar triangle inequality and linear arithmetic.
It proves the whole conjunction, not merely |E-h(c)| ≤ δE.

## Definitions audit for `bpI:p7:sec-ham#data`

Source: `blueprint-I/parts/p7-delaunay.tex:48`–49, referring to
`blueprint-I/parts/p0-conventions.tex:130`–149; graph
`docs/graph/I/DEPGRAPH.md:9800`–9823. The physical formulas also agree with
`docs/tracks/I/statement.md:180`–200. All μ below range over ℝ.

| Source object | Lean definition / expression (file:line) | Classification | Whole-carrier check |
|---|---|---|---|
| W_μ | `CollisionFree`, `KAM/Frozen/Iso/Defs/CollisionFree.lean:40`; set expression `KAM/Iso/LeftoverNodes.lean:45` | FAITHFUL | Predicate is exactly the conjunction of positive distances to both primaries, for every phase point. The export identifies this set with exclusion of both primary positions and proves openness. No separate named W definition is required. |
| a₁(μ) | `primary₁`, `KAM/Frozen/Iso/Defs/Primary1.lean:37` | FAITHFUL | Body `![-μ, 0]` for every real μ. |
| a₂(μ) | `primary₂`, `KAM/Frozen/Iso/Defs/Primary2.lean:36` | FAITHFUL | Body `![1 - μ, 0]` for every real μ. |
| rad | `radius`, `KAM/Frozen/Iso/Defs/Radius.lean:37`, with `radiusSq`, `RadiusSq.lean:36` in the same directory | FAITHFUL | `sqrt (∑ i, (q i)^2)` equals sqrt(q₀²+q₁²) for every q. Radicand is always nonnegative, including q = 0; no negative-square-root fallback is used. This is physical Euclidean length, not the ambient sup norm. |
| r_j | `radius (z.1 - primary₁ μ)` and `radius (z.1 - primary₂ μ)`, `KAM/Iso/LeftoverNodes.lean:46`, 53, 58–59 | FAITHFUL-WITH-NOTE | Source explicitly says “write r_j”; these literal expressions implement that notation on every phase point. There is no missing independent function or arbitrary branch. |
| H^R3_μ | `restrictedHamiltonian`, `KAM/Frozen/Iso/Defs/RestrictedHamiltonian.lean:42` | FAITHFUL | On its entire collision-free subtype, body is radiusSq(p)/2 + q₁p₀ - q₀p₁ - (1-μ)/r₁ - μ/r₂. Every denominator is positive on this carrier. No value at a collision is part of its public domain. |
| V_μ | `restrictedVectorField`, `KAM/Frozen/Iso/Defs/RestrictedVectorField.lean:41` | FAITHFUL | On the entire same subtype, body is ((p₀+q₁,p₁-q₀),(p₁,-p₀) - ((1-μ)/r₁³)•(q-a₁) - (μ/r₂³)•(q-a₂)). Signs and canonical momentum agree with source. Denominators are nonzero; no fallback. |

`sec_ham_data` literally includes all five clauses: positive-radius set identity
(lines 45–46), noncollision set identity (47–48), openness (49), defining
Hamiltonian equation (50–53), defining field equation (54–59). Subtype points
are quantified as arbitrary `z` and arbitrary collision-freedom witness `hz`,
so the equations cover all of W_μ. The defining equations and first identity
are reflexive; the other identity uses positivity/definiteness of radius, and
openness uses landed `isOpen_collisionFree`. The node does not additionally
assert the Hamiltonian derivative identity from the following `ham-eq` node.

No `def`, `abbrev`, or `structure` is introduced by this package. In particular
no replacement carrier, hidden analytic premise, or junk-valued object is added.

## Independent verification

All Lean-related commands were serialized, with `LEAN_NUM_THREADS=1` and
`nice -n 5`. Lint was run only after the build, probe, and kernel replay finished,
since its ABI check can invoke Lean. No library rebuild, cache manipulation,
package update, frozen edit, generated-root edit, or state-changing git was run.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gism KAM.Iso.LeftoverNodes
   ```

   Exit 0. Output began
   `[inp-gate] slot 1 acquired 06:13:22 for KAM.Iso.LeftoverNodes`
   and ended `Build completed successfully (9158 jobs).`
   Only replayed dependency warnings: `KAM/Kepler/Energy.lean:106:35` unused
   `hm`, `:106:48` unused `hκ`; `KAM/ODE/Exit.lean:36:0` unused section
   `[NormedSpace ℝ E]` in `KAM.ODE.gen_exit`. No audited-file warning.

2. Fresh application/signature and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPISMAudit.lean
   ```

   Exit 0. Probe imported only `KAM.Iso.LeftoverNodes`, copied each complete
   declaration header under a fresh audit name, and checked these bodies with
   all explicit binders in order:

   ```lean
   exact KAM.Iso.k_pos_node hκ hΩ L
   exact KAM.Iso.sec_ham_data μ
   exact KAM.Iso.Charts.tori_patch_node P W Ψ δE δm ρc hP hcov hε₁ hε hI₀ hE
   ```

   Additional examples used an ordinary real L with a separate proof L > 0,
   and Ω = -1. All elaborated at default resource limits. There is no provider
   or frozen anchor in this slice, so a provider/frozen `type_of%` equality or
   actual frozen seal-body probe is not applicable. The above application
   probes are not represented as such a seal.

   Exact `#print axioms` output:

   ```text
   'KAM.Iso.k_pos_node' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Iso.sec_ham_data' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Iso.Charts.tori_patch_node' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.LeftoverNodes
   ```

   Exit 0. Complete output: `replaying KAM.Iso.LeftoverNodes`.
   This is the only new lemma module; there are no provider modules to append.

4. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1267 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Only the explicitly allowed generated-root exception occurred. Left it
   untouched, as instructed. This accounts for the overall WITH NOTES verdict.

5. Static/import/protected-path checks:

   - `git diff --name-only inp...HEAD`: only `KAM/Iso/LeftoverNodes.lean`.
   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.
   - `git diff --check inp...HEAD`: exit 0, no output.
   - Python import-closure inspection: 112 reachable local modules, 53 frozen
     modules, all 53 SEALED according to `manifest/frozen-anchors.json`;
     zero provider imports and zero frozen theorem imports. Consequently no
     DRAFT_SORRY anchor is imported, even transitively.
   - Scoped token scan: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
     `EuclideanSpace`, or `set_option`. No resource override of any kind.
   - 96 total lines; maximum Unicode line width 98. Copyright, `module`,
     public imports, module docstring and `public section` are present.
     No new definition requires an `@[expose]` annotation.
   - Each of the three new public declaration short names occurs as a
     declaration only once under `KAM/`. Names remain in `KAM.Iso` or
     `KAM.Iso.Charts`; no root declaration or harmful shadow was introduced.
   - Probe was deleted after verification. Report is the only repository file
     written by this audit; the untracked handoff predated the audit.

## Uncertainties, errata, deviations

No suspected defect in the scoped blueprint formulas or frozen definitions was
found. No external pinned-source claim is newly proved by this package; the
source comparison here is with the local blueprint and frozen formulas.

Recorded generalizations: nonzero rather than positive Ω at the positivity step;
patch selection for arbitrary fixed valid patch/cover/uniform data without the
unused analytic/perturbation assumptions. The first is required by this audit's
literal graph contract; the second contains the source instance and preserves
all of its inequalities and quantifier dependencies. The omitted ε ≥ 0 premise
is redundant with `hE`. The r_j notation has no separate Lean declaration, as
permitted by the source's own notational usage and the focused definition-node
policy. No deviation was introduced by the auditor.

All three focused nodes can be marked closed on this evidence. That conclusion
does not change manifest states or establish any broader campaign theorem.
