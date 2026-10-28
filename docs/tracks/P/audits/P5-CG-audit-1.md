# P5-CG independent package audit 1

Overall verdict: **PASS WITH NOTES** for P5-CG; all three public declarations PASS.
No frozen theorem is assigned to this package, so provider/frozen seal readiness is N/A.
This certifies the compact complexification helper, not P-G or the full extension/periodicity
assembly (P5-EX).

## Snapshot, scope, and evidence

- Worktree: `/root/code/KAM-inp-p5cg`; HEAD
  `670ab9ad3b6e490b61fbe051c295bab836d05e5b`.
- Compared with `inp` = `408ea7a6f026a1ecf1d0cf0e988bdc54494497f9`, using
  `git diff inp...HEAD`. Git warns of multiple merge bases and selects
  `687bf80264ad43ff3491e8bf2c8a9d9f7bc40456`; the other is
  `aa359d8fcbe90f6489dc2c4a3ccaf7b5a8e7f8ec`.
- AUDIT FOCUS restricts implementation review to
  `KAM/Planetary/PGAssembly/ComplexGlue*.lean`: exactly one file, 154 lines.
  HEAD's own commit changes only this file. Inherited P5-CL/P5-ID and track-N code are
  context/dependencies, not newly certified by this audit.
- Read AGENTS.md, PLAN, DECISIONS, the shared package audit brief, P5-CG handoff,
  track-P statement conventions, design row P5-CG (line 486), dependency plan (line 414),
  design signature (1489–1496), and design audits 1–3. Those audits reside in
  `docs/tracks/P/design/`, rather than the handoff's `audits/` location.
  The shared signatures are `/root/code/KAM-inp/.drafts/design/P45Signatures.lean:792–799`;
  the package worktree has no copy at `.drafts/design/P45Signatures.lean`.
- Mathematical source for this helper: `blueprint-P/parts/p5-pg-assembly.tex:29–36`,
  especially `stepP:p5:ext-loc` and `stepP:p5:ext-glue`. No external published theorem
  is being substituted for these supplied proof steps.
- SHA256 of ComplexGlue.lean:
  `ef49302e584340a54811ce0a8fef07397b4484b0a504fe2218f88ac8cd46f636`.
  Design SHA256: `2081360d5b6d017698094ddf521213c38892dcc06a37785e6632d04c36752eac`.
  Shared signatures SHA256:
  `f4c7752bf23b8b149e4e5c0f1fac5288b4c32c10d19c4a17d3afe79af1c13ca2`.

## Declaration results

All names below have prefix `KAM.Planetary.`.

| Node / role | Declaration (ComplexGlue line) | Verdict | Reason |
|---|---|---|---|
| ext-glue helper | `local_complexifications_agree` (34) | PASS | Derives equality on the full complex overlap from holomorphy and equality with the same real function. No positivity premises are needed: empty intersections are handled explicitly. |
| compact-cover helper | `exists_pos_le_finset` (66) | PASS | Produces a positive lower bound for all half-radii; includes the empty finset. |
| `stepP:p5:ext-loc`, P5-CG | `compact_real_complexification` (80) | PASS | Exact design signature, positive uniform radius and bound, holomorphy on the whole tube, equality at every real point of that tube. |

### Binder audit

Each row is one declared binder; grouped names are separated below. SOURCE refers to the
compact analytic extension contract (design 1489–1496; blueprint 33) or the explicitly
identified elementary substep of its proof (blueprint 33–34).

| Declaration | Binder | Bin | Justification |
|---|---|---|---|
| compact | implicit `N : ℕ` | TYPING | Arbitrary finite dimension; no hidden positive-dimension condition. |
| compact | implicit `X : Set (Fin N → ℝ)` | TYPING | Compact real set carrier. |
| compact | `hX : IsCompact X` | SOURCE | Compactness in ext-loc. |
| compact | implicit `f : (Fin N → ℝ) → ℝ` | TYPING | Scalar real function. |
| compact | `hf : AnalyticOnNhd ℝ f X` | SOURCE | Real analyticity at each point of the compact set. |
| agree | implicit `N` | TYPING | Finite dimension. |
| agree | implicit `f` | TYPING | Common real function. |
| agree | implicit `x` | TYPING | Real centre. |
| agree | implicit `y` | TYPING | Real centre. |
| agree | implicit `rx` | TYPING | Real radius. |
| agree | implicit `ry` | TYPING | Real radius. |
| agree | implicit `Fx` | TYPING | First complex extension. |
| agree | implicit `Fy` | TYPING | Second complex extension. |
| agree | `hFx` | SOURCE | Holomorphy on the first ball, blueprint 33–34. |
| agree | `hFy` | SOURCE | Holomorphy on the second ball. |
| agree | `hx` | SOURCE | Equality with f on the first real ball. |
| agree | `hy` | SOURCE | Equality with f on the second real ball. |
| finite bound | implicit `α : Type*` | TYPING | Arbitrary index carrier. |
| finite bound | instance `[DecidableEq α]` | TYPING | Finset operations; not an analytic/proof obligation. |
| finite bound | `ρ : α → ℝ` | TYPING | Radius family. |
| finite bound | `t : Finset α` | TYPING | Finite subcover index set. |
| finite bound | `h : ∀ x ∈ t, 0 < ρ x` | SOURCE | Positive local radii produced at ext-loc. |

Counts: compact SOURCE 2 / TYPING 3; agree SOURCE 4 / TYPING 8;
finite-bound SOURCE 1 / TYPING 4. All three have STANDING 0, RULED 0, EXCESS 0.
There are no assumption bundles or theorem-shaped predicates hiding inputs.
The two elementary helpers have their own names and are consumed with proved premises.

### Signature and application probes

The complete main theorem telescope through its conclusion is text-identical to both
shared S:792–799 and the design appendix (excluding the proof delimiter).
An untracked `.lake/abi-scratch/P5CGAudit.lean` imported ComplexGlue and copied that exact
signature under `P5CGAudit.signature`, with body:

```lean
by
  exact KAM.Planetary.compact_real_complexification hX hf
```

It also elaborated both directions:

```lean
example : type_of% @KAM.Planetary.compact_real_complexification := @P5CGAudit.signature
example : type_of% @P5CGAudit.signature := @KAM.Planetary.compact_real_complexification
```

Thus both explicit binders, `hX hf`, are sufficient in order. There is no assigned provider,
frozen theorem export, or seal body to check. No frozen theorem was edited or promoted.

## Proof and definitions

At 94, P5-CL is applied to the actual `hf x hx`. The compact half-ball cover (98–100)
has centres in X. The triangle estimate at 102–117 shows the entire action tube lies in
the union of the larger complex balls: distance to X is < r, distance of its selected
real centre to a covering centre is < ρᵢ/2, and r ≤ ρᵢ/2.

The overlap lemma (41–63) proves openness and preconnectedness by convexity. For a nonempty
complex intersection, taking the componentwise real part gives a point in both real balls
by contractivity of realPartCLM. That nonempty open real intersection is mapped into the
complex intersection, where both functions equal f. P5-ID's `real_slice_identity` is then
applied with all premises supplied. Unequal radii cause no midpoint problem.

At 122–131, G is proved equal to **each** chosen local function on its entire complex ball.
Consequently a potentially discontinuous choice of index does not obstruct holomorphy:
135–139 proves differentiability using a genuine open neighbourhood. Real agreement at
140–143 holds for every real point in the tube, including those outside X. The bound at
144–150 is supplied by one local bound and nonnegativity of all summands. M = 1 + Σ Mᵢ
is positive and uniform; r, M and G depend only on the initial data, before any point is given.
Empty X and dimension N = 0 need no additional assumptions.

No new top-level `def`, `abbrev`, `structure`, or instance is introduced.

| Local construction | Classification / verdict |
|---|---|
| `loc`, then choice of ρ, M, F (88–97) | Proof-local witness family; zero data off X carry only an impossible-condition implication. Cover centres are proved in X, so no off-X fallback is used for any required property. PASS. |
| `idx` (119–120) | Proof-local covering index; the zero fallback is unreachable on the whole union and hence on the tube, by hcover. PASS. |
| `G` (121) | Existential extension witness, required only on the tube; hG proves index-choice independence on the whole union. Its arbitrary off-union values are not claimed to extend f. PASS. |
| frozen `actionNbhd` | Literal existential tube in the max norm on `Fin N → ℂ`; exact intended carrier, no fallback. Manifest `kam.actionNbhd.v1` is SEALED and full-file hash matches. |
| existing `realInclusion`, `realPartCLM` | Coordinatewise inclusion and real part (Strip/Analytic:38–64); isometry/contractivity actually used in the proof. |

For new exported definitions: BODY_MATCH / PUBLIC_CARRIER / WELL_DEFINEDNESS /
CHARACTERIZATION / CHOICE_INDEPENDENCE are N/A (none introduced).
For the existential witness: all asserted properties and independence of covering-index
choice are proved on the entire asserted domain. No global canonical extension is claimed.

The recursive project import closure contains ComplexGlue, ComplexLocal, RealSlice,
Strip.Analytic/AnalyticSeries/AnalyticTaylor/Cauchy/Regularity and frozen definitions
ActionNbhd and ComplexStrip. Both frozen definitions are SEALED and their file hashes match.
There are no provider imports and no frozen theorem imports, including DRAFT_SORRY anchors.

## Independent checks

All Lean/Lake invocations below were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The build wrapper applies nice internally; no second Lean check ran while it was pending.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5cg KAM.Planetary.PGAssembly.ComplexGlue
   [inp-gate] slot 1 acquired 09:04:00 for KAM.Planetary.PGAssembly.ComplexGlue
   Build completed successfully (9056 jobs).
   exit 0
   ```

2. Signature/axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5CGAudit.lean
   'KAM.Planetary.local_complexifications_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.exists_pos_le_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.compact_real_complexification' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

3. Kernel replay, one invocation for the single in-scope lemma module:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.ComplexGlue
   replaying KAM.Planetary.PGAssembly.ComplexGlue
   exit 0
   ```

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (509 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The only failure is the exact stale generated-root exception allowed by the brief.
   No root regeneration was performed. In-scope forbidden-token/override scan is empty;
   154 physical lines, maximum Unicode line length 98 (below the 100-character limit).
   Copyright, `module`, public imports, module documentation and public section are present.

5. Protected paths and whitespace:

   - `git diff inp...HEAD -- KAM/Frozen manifest README.md`: empty, exit 0
     (apart from Git's multiple-merge-base warning).
   - The required literal `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
     is **not empty**: inherited KAM.lean changes add nine imports (eight track-N imports
     and ComplexLocal), committed in `aa359d8`, before P5-CG. This is an explicit
     whole-branch hygiene discrepancy, not silently counted as a passing empty diff.
   - `git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
     The audited P5-CG commit touches no protected paths.
   - `git diff --check inp...HEAD -- 'KAM/Planetary/PGAssembly/ComplexGlue*.lean'`:
     empty, exit 0 (apart from the same warning).
   - Full `git diff --check inp...HEAD`: exit 2, inherited
     `docs/tracks/N/audits/S7-8-audit-1.md:232: new blank line at EOF.`
     This is outside the explicitly restricted implementation scope.

## Notes, errata, deviations, and handoff

The overall PASS WITH NOTES preserves the two inherited comparison discrepancies above,
and the permitted stale-root lint failure. The in-scope implementation has no identified
statement-fidelity, proof, definition, axiom, import-quarantine or line-length defect.
No source premise or conclusion was changed, and no suspected mathematical source/blueprint
erratum was found in the audited steps. The contract is stronger than merely separate local
extensions: it supplies one holomorphic function on the tube and equality on its entire
real slice, exactly as designed. Periodicity and the remaining ext theorem conclusions
remain responsibilities of P5-EX and are not inferred here.

No repository file was edited except this report. The signature/axiom probe was deleted
from `.lake/abi-scratch/` after the checks. The pre-existing untracked P5-CG-handoff.md
was left untouched. No state-changing git command, frozen edit, generated-file edit,
resource override, cache reset or dependency update was performed.
