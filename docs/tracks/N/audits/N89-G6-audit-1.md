# N89-G6 independent package audit 1

Verdict: **PASS WITH NOTES** for N89-G6 infrastructure (`sqrt`, `geom_formula`,
`geometric`). No frozen anchor is implemented or sealed by this package. No mathematical
or statement-fidelity blocker was found. The notes concern the permitted generated-root
lint exception, inherited warnings, and audit scope; this is not N-HEAD-C/root closure.

## Scope and authority

Audited HEAD `969207c41db6f27f287ccd61f98e6d66fc4c00ea` in
`/root/code/KAM-inp-n89g6`, following the supplied audit brief and AUDIT FOCUS.
Read AGENTS.md, PLAN.md, DECISIONS.md, the handoff, track-N statements,
N89 design Revision 2 (especially G6, Appendix A and proof obligations), and blueprint
Part 8 lines 138–180. The draft signatures and earlier design audits are absent at the
handoff's local paths; read the supplied signatures at
`/root/code/KAM-inp/.drafts/design/N89Signatures.lean` and both audits at
`/root/code/KAM-inp/docs/tracks/N/design/DESIGN-N89-design-audit-{1,2}.md`.
The second design audit resolves the earlier projection-interface and package-DAG findings.
No primary PDF was independently re-audited; source fidelity here means fidelity to
these supplied blueprint/design authorities.

`git diff inp...HEAD` reports multiple merge bases and selects
`f11c90357967f666b1673409df890dbcec823dff`; it contains Blocks (+58),
GeomFormula (+124), Geometric (+220). `inp` resolved to
`5991245cabc06e69ec900cb6006b45f72cc85eb0` when checked.
The focused comparison `git diff inp-n89g5...HEAD -- KAM/Nekhoroshev/ResonanceGeometry`
adds only the latter two files; Blocks is unchanged against G5
`8d7480bf24ca04be92d424125efe8d3757013ce2`. The unrestricted G5 comparison also
includes unrelated inherited packages and a generated-root change: those are outside
AUDIT FOCUS and are not certified by this report.

Audited files:

- `KAM/Nekhoroshev/ResonanceGeometry/GeomFormula.lean` (124 lines).
- `KAM/Nekhoroshev/ResonanceGeometry/Geometric.lean` (220 lines).

The user-specified report path in this worktree overrides the generic brief's main-worktree
destination. No repository source, generated file, frozen file, or manifest was edited.

## Declaration and node verdicts

Names below are in `KAM.Nekhoroshev`. Line numbers refer to the two files above.

| Node / obligation | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| `bpN:p8:sqrt` | `sqrt`, GeomFormula:23 | PASS | Exact design signature; both numerical bounds proved for A ≥ √2, including equality. |
| Projection norm scaling helper | `euclid_smul'`, GeomFormula:35 | PASS | All real scalars/vectors, including zero; proved by squared Euclidean norms. |
| `bpN:p8:geom-formula` | `geom_formula`, GeomFormula:41 | PASS | Exact design type with all five conjuncts; arbitrary real subspace, a valid strengthening of the blueprint lattice-span case. |
| `stepN:p8:gl-setup` helper | `lattice_addVector_eq`, Geometric:25 | PASS | Real span of subgroup plus cyclic generator equals the supremum of the real spans, on the whole carrier. |
| Zero-rank helper | `latticeDim_eq_zero_of_bot`, Geometric:38 | PASS | Direct reuse of the proved zero-lattice dimension. |
| Positive-rank helper | `ne_bot_of_dim_pos`, Geometric:40 | PASS | Positive rank excludes bottom; no additional assumption. |
| Zone-complement helper | `not_mem_zone`, Geometric:43 | PASS | For a nonzero lattice, complements the strict zone inequality to a non-strict lower bound. |
| Zone-membership helper | `lt_of_mem_zone`, Geometric:48 | PASS | Unfolds the intended strict inequality with the necessary nonzero-lattice guard. |
| `stepN:p8:gl-theta2` helper | `euclid_proj_line`, Geometric:55 | PASS | Genuine Euclidean line-projection norm identity; denominator avoided in the exported equation. |
| `stepN:p8:gl-theta` helper | `rank_one_facts`, Geometric:65 | PASS | Any rank-one lattice containing nonzero k has real span ℝk and volume ≤ ‖k‖; maximality is unnecessary (stronger). |
| `stepN:p8:gl-theta`, `gl-theta2` | `geometric_theta`, Geometric:85 | PASS | Rank-one branch; local λ₁ positivity is supplied by the main theorem's original positivity hypothesis. Other λ, E, A, and ratio assumptions are unnecessary here. |
| `stepN:p8:gl-setup` | `geometric_lattice`, Geometric:112–139 | PASS | Maximality supplies k outside the real span, d<n, a rank-(d+1) K-lattice, and a maximal extension of identical span. |
| `stepN:p8:gl-vol` | `geometric_lattice`, Geometric:140–149 | PASS | Equal-rank volume monotonicity and the added-vector identity give V₊≤V‖Qk‖≤VK. No short basis or saturation assumption. |
| `stepN:p8:gl-proj` | `geometric_lattice`, Geometric:150–181 | PASS | Zone inequalities give ‖Pω‖<L and ‖P₊ω‖≥AL; projection Pythagoras supplies the squared difference estimate before taking its square root. |
| `stepN:p8:gl-div` | `geometric_lattice`, Geometric:182–204 | PASS | Volume lower bound for ‖Qk‖, projection identity, Cauchy–Schwarz and reverse triangle inequality give the exact EKδ divisor bound. |
| `bpN:p8:geometric` | `geometric`, Geometric:206 | PASS | Exact design signature, binder order and constants. Both branches and the strict resonance-distance conclusion are retained; no premise added. |

There are **13 new public theorem declarations**, all covered above. No new definition,
abbreviation, structure, instance, or provider is introduced. The split into two small
modules preserves the public Geometric import path.

## Semantic and proof review

For `geom_formula`, q=k−P_V k is nonzero because k∉V. Its squared Euclidean norm
is positive. The candidate P_V w+cq lies in V+ℝk, and w minus that candidate is
orthogonal to both V and k. The unique-projector characterization proves the explicit
formula. Orthogonality gives the dot decomposition and Pythagoras; scalar norm scaling
gives the absolute-dot identity. Divisions by ‖q‖ and ‖q‖² are justified by positivity.

For part (a), the proof chooses a rank-one maximal K-lattice containing k. Rather than
choosing a primitive generator g explicitly, `rank_one_facts` applies volume monotonicity
to the cyclic subgroup generated by k, giving the same bound V≤‖k‖. This is a valid
proof implementation variation of blueprint p8:170, not a statement deviation.
The point is outside that lattice's zone; the line-projection identity proves the bound.

For part (b), all denominators are positive (lattice volumes ≥1 and λ_d>0).
With L=Kλ_d/V₊>0, the proof establishes s≥L√(A²−1) for the difference of projections.
Then ‖Qk‖L≥Kδ and |Pk·Pω|≤Kδ give
|k·ω|≥Kδ(√(A²−1)−1)≥EKδ. The branch d=n has no outside short vector,
as the earlier maximality theorem supplies d<n whenever such a vector is present.
For n=1 the ratio hypothesis is correctly vacuous. All arguments use explicit Euclidean
length on `Fin n → ℝ`, while retaining the ambient function max-norm convention.

No conclusion-shaped hypotheses or bundled hard proof assumptions were found.
The λ₁ positivity in the distinct `geometric_theta` helper is an original source
positivity assumption, discharged by `hlam 1 le_rfl hn` in `geometric`.

Definition classification: **none new in scope**. Checked the consumed interfaces:
`Lattice` is an integer additive subgroup; `lattice` its real span;
`integerReal` coordinate casting; `eBall` the Euclidean integer cutoff;
`proj` the uniquely characterized orthogonal projector; `compProj` its complement;
`resonanceDistance` the norm of the resonance-side projection, identified with distance
by upstream `projection_distance`; `volume_def` the Gram covolume;
`addVector` the subgroup supremum with the cyclic closure; `maximalK` the design's
same-rank K-lattice maximality. `zone` uses univ exactly at bottom,
`zoneStratum` restricts dimensions to 1,…,n, and `blocks` is the prescribed set difference.
These are existing intended objects, not fallback definitions introduced to prove G6.
This inspection is not a new full audit of G1–G5.

The recursive project import closure has 61 modules, no `KAM.Provider` module and
no frozen theorem module. All 19 imported frozen definitions are SEALED in the current
manifest. Hence no DRAFT_SORRY theorem enters. Provider/frozen type equivalence and
frozen seal-body probes are **not applicable**: no provider or target frozen anchor exists.
Instead the three exact design declarations were reconstructed under fresh names with
bodies applying the corresponding exports to their explicit binders in order.

## Independent validation

All Lean/Lake operations were sequential and used `LEAN_NUM_THREADS=1` and niceness 5.
No clean, cache download, dependency update, root regeneration, or budget override was used.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89g6 KAM.Nekhoroshev.ResonanceGeometry.Geometric
   [inp-gate] slot 2 acquired 09:39:35 for KAM.Nekhoroshev.ResonanceGeometry.Geometric
   Build completed successfully (3216 jobs).
   Exit 0.
   ```

   Replayed inherited unused-variable warnings: Gradient:168 (`hgr`), Maximal:249 (`hK`),
   Blocks:34 (`hK`) and :35 (`hlam`). No diagnostic in either audited file.

2. Signature checks and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89G6Audit.lean
   Exit 0.
   ```

   Complete signature text for `sqrt`, `geom_formula`, `geometric` matches the supplied
   design literally (including the let-bound V′ in `geom_formula`). Fresh copies elaborate
   with `exact sqrt A hA`, `exact geom_formula V k w hk`, and
   `exact geometric hn hK hE hA lam hlam hratio`, respectively. The probe imports only
   Geometric and declares `{n : ℕ}` with the corresponding namespace/open declarations.
   An initial auditor-generated probe mistakenly cut a declaration at its inner let `:=`;
   after fixing extraction to use the theorem-body delimiter, the full probe passed.
   That initial syntax failure was not a package failure.

   `#print axioms` output, with the common namespace prefix abbreviated:

   ```text
   sqrt:                    [propext, choice, Quot.sound]
   euclid_smul':             [propext, choice, Quot.sound]
   geom_formula:            [propext, choice, Quot.sound]
   lattice_addVector_eq:    [propext, choice, Quot.sound]
   latticeDim_eq_zero_of_bot: [propext, choice, Quot.sound]
   ne_bot_of_dim_pos:       [propext, choice, Quot.sound]
   not_mem_zone:            [propext, choice, Quot.sound]
   lt_of_mem_zone:          [propext, choice, Quot.sound]
   euclid_proj_line:        [propext, choice, Quot.sound]
   rank_one_facts:          [propext, choice, Quot.sound]
   geometric_theta:        [propext, choice, Quot.sound]
   geometric_lattice:      [propext, choice, Quot.sound]
   geometric:              [propext, choice, Quot.sound]
   ```

   Lean prints `choice` for the permitted choice axiom. No `sorryAx` or extra axiom.

3. Kernel replay (one invocation):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.ResonanceGeometry.GeomFormula KAM.Nekhoroshev.ResonanceGeometry.Geometric
   replaying KAM.Nekhoroshev.ResonanceGeometry.Geometric
   replaying KAM.Nekhoroshev.ResonanceGeometry.GeomFormula
   Exit 0.
   ```

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (495 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   Exit 1, solely for the explicitly permitted stale generated root.
   ```

   No overlong-line, oversized-file, forbidden-token, module, frozen-guard, or ABI failure.
   The generated root was left untouched as required.

5. Static checks:

   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty stdout,
     exit 0 (only the multiple-merge-base warning on stderr).
   - `git diff --check inp...HEAD`: exit 0, same merge-base warning only.
   - Forbidden-token/resource-override scan in both audited files: no matches.
   - Module headers, module docstrings, public imports, and public exposed section: present.
   - GeomFormula: 124 lines, maximum line length 99 characters.
   - Geometric: 220 lines, maximum line length 98 characters.

## Defects, deviations and limits

No new suspected blueprint or pinned-source defect was found. The arbitrary-subspace
projection statement is a harmless strengthening; the rank-one covolume proof variation
is described above. No frozen declaration needs correction. No default-heartbeat failure
or other design signal arose in the package.

The old handoff estimates (~135/~250 lines) are approximate; actual counts are 124/220.
Its warning summary was incomplete: the independent build replayed Gradient/Maximal
warnings as well as both Blocks unused-variable warnings. These do not affect the proof.
The sole generated-root lint exception remains an orchestrator
follow-up; this auditor does not edit KAM.lean.

Final validation: temporary auditor probes/logs were removed from `.lake/abi-scratch/`;
`git diff --check` passed. The only new auditor-owned repository file is this report;
the pre-existing untracked handoff was preserved.
