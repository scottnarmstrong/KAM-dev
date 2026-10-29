# S11 independent package audit 1

**Overall verdict: PASS WITH NOTES for S11 (`KAM.Planetary.sb_safety`).**
All eleven assigned proof steps are implemented. No extra premise, weakened conclusion,
conclusion-shaped hypothesis, or mathematical proof defect was found. The signed and frozen
statement-copy probes elaborate with only the three permitted axioms. The notes concern a
redundant type-annotation difference, the permitted generated-root staleness, inherited diff
contents, and a mistaken graph-prefix reference in the audit focus.

Scope: only `KAM/Planetary/SecularBox/Safety.lean`, HEAD
`a137e91024da5a0114a0c5753ec2c9e4e0d6a393`, compared with `inp`
`bea4e8e486c920ad0f51758913e31756dd9e9554`, on 2026-10-28.
The user's exact report path in this worktree overrides the generic brief's main-worktree
output instruction. No production source or git state was changed.

## Anchor boundary

| Anchor | Verdict for S11 contribution | Remaining boundary |
|---|---|---|
| `planetary.d25.secularBoxSafety.v1` | PASS WITH NOTES | Ordinary `sb_safety` proves the complete frozen telescope. The provider wrapper and actual anchor seal are outside this slice; manifest remains `DRAFT_SORRY`. |
| `planetary.d25.secularBoxAtCitedMasses.v1` | PASS WITH NOTES | S11 supplies the complete generic theorem needed by S12. The rational specialization, provider and seal are outside this slice; manifest remains `DRAFT_SORRY`. |

There is no S11 provider export to audit. Neither frozen anchor is claimed sealed by this
report. For the generic anchor, a fresh copy of its entire declaration, renamed
`auditS11Frozen`, successfully uses the exact six-argument body
`by exact sb_safety saturn mu hsaturn hmu w0 hw0`. A separate signed declaration copy and
`example : type_of% @auditS11Frozen := @sb_safety` also succeed. These probes import only
Safety, avoiding the unproved frozen theorem/provider stubs.

## Inputs and comparison

Read AGENTS.md, PLAN, DECISIONS, the package brief and handoff, P14 design row S11 and node
table, both P14 design audits, authoritative P14Signatures, track-P statement section
P-SECULAR-BOX, blueprint `p14b-secular-box.tex` and graph packet
`docs/graph/P/packets/P-p14b.nodes.md` (especially lines 2180–2529). Read both relevant frozen
anchors and their consumed definitions, including the input box, regularity, solution
predicate, actions/AMD/chart formulas and barycentric pair bounds. Inspected the actual
supplier signatures and proof applications from Chart, Smooth, GlobalFlow and Uniqueness.

The requested `git diff inp...HEAD` has seven added files and 1253 insertions: Safety, inherited
Field/SlowFlow/GlobalFlow/Uniqueness, and inherited S7 audit/handoff. Git warns
`multiple merge bases, using b8e023179635e643629844d102983e478c955c1e`.
The full comparison was reviewed; the scoped verdict applies only to Safety. S11's own two
commits (`54c7ec62`, `a137e910`) affect Safety alone. The pre-existing untracked S11 handoff
was preserved. The inherited S7 audit records earlier completeness failures; current Field
includes `sb_regular`, `sb_omega_continuousOn`, and `sb_omega_fast_angle`, so those historical
missing-export findings do not describe the present supplier source.

Safety SHA-256: `c02a62b584685fabcc996968c35d416e2ad54ecbcc0751aa47c84b98386f1225`.
Authoritative signature SHA-256:
`24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.

## Declaration and node ledger

Lean locations below are in Safety. All names are in `KAM.Planetary`; all helpers are private.

| Node / declaration | Lines | Verdict | Evidence |
|---|---|---|---|
| `bpP:p14:sb-safety` / `sb_safety` | 156–275 | PASS | Complete signed/frozen telescope: every real time, every phase F, existence, uniqueness, regularity, both conserved quantities, strict eccentricity and all geometry clauses. |
| `stepP:p14:sb-th-1` / `sbSafety_actions` | 53–80, 185 | PASS | Actual axis squares and positive actions give both strict 87/100 lower bounds and 23/10, 97/100 upper bounds. |
| `stepP:p14:sb-th-2` / `sbSafety_amd` | 94–108, 186 | PASS | Chart k identities, input eccentricities and per-planet bounds sum to AMD < 16373/2500000. |
| `stepP:p14:sb-th-3` / `sbSafety_mem` | 111–126, 187–189 | PASS | Nonnegative Gamma and AMD bound yield 50 Gamma < Lambda; actual input axis ranges lie strictly inside S. Supplies every global-flow hypothesis. |
| `stepP:p14:sb-th-4` / `sb_global` application | 188–190, 195, 229 | PASS | Global frozen Hamiltonian predicate, initial equality, S membership, constant actions and AMD, with the original Hamiltonian and mu. |
| `stepP:p14:sb-th-5` / `sb_unique` application | 191–193 | PASS | Full frozen U,v telescope preserved; competitor regularity is unnecessary, as already allowed by blueprint. Initial equality is transported in the correct direction. |
| `stepP:p14:sb-th-6` / `sbSafety_ecc` application | 129–139, 196–212 | PASS | Conservation gives Lambda > 87/100 and each Gamma < AMD bound; k > 2481/2500 and e² = 1-k² imply strict e < 3/20. |
| `stepP:p14:sb-th-7` / `sb_smooth_prop` application | 229 | PASS | S membership supplies literal frozen SecularRegular, including all-phase noncollision, positive Jacobians, integrability and differentiability. |
| `stepP:p14:sb-th-8` / `sbSafety_bridge` | 151–154, 268–274 | PASS | All m,w,F,i: bodyVector of ellipsePhase equals ellipsePosition. No ellipticity or orbit premise. |
| `stepP:p14:sb-th-9` / `sbSafety_rad`, local `hrad`, `hq0`, `hq1`, `hr` | 142–148, 213–237 | PASS | Conserved axes, chart radial bounds and eccentricity estimate give the individual endpoint products and common 1751/400..4439/400 interval. |
| `stepP:p14:sb-th-10` / local `hgap` | 238–241 | PASS | Saturn lower radius minus Jupiter upper radius yields 399/200 for every F. |
| `stepP:p14:sb-th-11` / local `hpp` and final cases | 243–275 | PASS | Reverse/ordinary triangle inequalities give planet-pair bounds; barycentric difference identities and Fin 3 cases cover Sun and both orientations. |
| `sbSafety_lt_of_sq` | 38–42 | PASS | Elementary square comparison under nonnegative upper comparator; negative lower argument also covered. |
| `sbSafety_hm` | 44–50 | PASS | Mass positivity derived from the closed saturn interval for both planets. |
| `sbSafety_gamma_lt` | 83–91 | PASS | Derives d < k from eccentricity squares, then Gamma < c(1-d); no hidden sign assumption on d needed. |

The focus's `stepP:p14:sb-sf-*` does not occur in the design node table, blueprint or graph
packet. The actual eleven S11 labels are `stepP:p14:sb-th-1` through `sb-th-11`
(design lines 261–271; blueprint lines 283–306). This is a locator typo, not an unproved family.
There are no unsigned public exports requiring a separate node-conclusion comparison.

## Definitions, hypotheses and proof review

Safety introduces **no def, abbrev, structure, class or instance**, public or private.
Its only public declaration is `sb_safety`; nine auxiliary theorems are private. Local `set b`
is the literal two ellipse positions used for the pair inequalities. No replacement object,
junk value or fallback is introduced.

Every helper premise is typing data or a source/algebraic fact proved at its call site.
In particular AMD, S membership, global existence and regularity are derived, not assumed
on the final theorem. Arithmetic is reproved inline with `norm_num`/`linarith` rather than
destructuring `sb_numerics`; this establishes the same rational facts and leaves no numerical
invoice unpaid. No positive lower bound on mu or smallness threshold is added. Circular data
remain included: the argument uses nonnegative Gamma and k ≤ 1, never division by eccentricity.
Positive masses/actions and chart regularity justify all total division/sqrt/fderiv uses.

The pair argument keeps the universal F after the universal time, so it does not replace
all-phase geometry by geometry along a selected anomaly. It uses exact barycentric relative
positions; the common translation cancels even though it depends on mu. The theorem concerns
the exactly averaged Hamiltonian, with no assertion that reconstructed ellipses solve the
Newton equations.

**Signature note.** The handoff says “signature copied verbatim.” Source line 157 instead has
`(31 / 100)` where authoritative signatures line 576 and the frozen anchor have
`(31 / 100 : ℝ)`. This is the sole textual header difference. The endpoint is already inferred
as real by Set.Icc; fresh declaration-copy/application and `type_of%` probes verify the exact
elaborated type without coercion, extra arguments or altered hypotheses. There is no semantic
signature deviation, but the verbatim-text claim is inaccurate. The unused signed `hmu` binder
is retained; the proof internally establishes a stronger fact without needing positivity.

The KAM transitive import closure contains 77 modules, including 54 frozen definition modules.
Every frozen module is manifest `SEALED`; no provider or frozen theorem is imported, directly
or transitively. All ten declaration short names occur exactly once in module-level KAM
declarations. All are within KAM.Planetary; no harmful root shadow or generic public helper
is introduced.

## Independent checks

All auditor Lean/Lake checks ran sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The targeted build used the prescribed compile gate, which itself applies nice. No resource
limit was overridden. These are independent reruns rather than prover receipts.

```text
$ env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s11 KAM.Planetary.SecularBox.Safety
[inp-gate] slot 1 acquired 22:01:43 for KAM.Planetary.SecularBox.Safety
warning: KAM/Planetary/SecularBox/Safety.lean:157:60: Variable name `hmu` is not explicitly referenced.
Build completed successfully (9123 jobs).
exit 0

$ env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S11Audit.lean
'KAM.Planetary.sb_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.auditS11Signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.auditS11Frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

The probe copies the entire signed declaration from P14Signatures lines 575–602, and the entire
frozen generic declaration; each body applies the production theorem to all six explicit
binders in order. No admitted scratch declaration was used. All new public theorems (one)
have only the permitted axioms.

```text
$ env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Safety
replaying KAM.Planetary.SecularBox.Safety
exit 0
```

This single invocation replays Safety, including its nine private proof helpers. There is no
provider module in the scoped package to add to the replay invocation.

```text
$ env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (986 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the stale generated root, explicitly permitted by the audit brief.
No other lint failure appeared. The generated root was not regenerated. The ABI subprocess
inherits the single-thread setting and nice priority; it ran after kernel replay completed.

Static checks: Safety has 279 lines, maximum Unicode line length 100. Copyright, module,
public imports, module docstring and public section are present. There are no new definition
bodies requiring exposure. No forbidden proof token, EuclideanSpace, resource override or
provider import occurs in Safety. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
is empty (exit 0, apart from Git's merge-base warning); `git diff --check inp...HEAD` passes.

## Source defects, deviations and uncertainties

No suspected mathematical defect in the pinned source, blueprint or frozen statement was
found. No mathematical deviation was introduced by this audit. The present review uses the
local pinned blueprint transcription and existing design audits; it does not claim a new
external-PDF source audit. The signature annotation and `sb-sf` locator differences above
are documentary notes. Kernel acceptance and type matching do not themselves seal either
frozen anchor or discharge the separate S12 specialization.

Only this report was added to repository source paths. The pre-existing handoff and all
production/frozen/generated files remain untouched. Auditor-owned scratch probes were removed
at closeout. The final status shows only this new report and the pre-existing untracked
S11 handoff; no tracked-file changes.
