# GAP-LREF independent audit 1

Auditor: maud-glref-1. Date: 2026-10-29 UTC. Worktree: `/root/code/KAM-inp-glref`.
Audited HEAD: `65b96b5b5cc9fd299ca7e9969e76c5ca1ed4252a`.
Initial comparison ref `inp`: `cda2ca291d9606c00a7ae5ba7fe376fb8218b3b4`.
The shared `inp` ref advanced during this audit; final observed ref was
`9ffcb3343be139ca6f003a42f0cab4ab6027fbb6`. A final fresh `git diff inp...HEAD`
is byte-identical to the initial saved diff (`cmp` exit 0), with merge base
`f38de76be1689652e630490c1007aac7dbd74080`; the audited patch and verdict did not change.
The complete `git diff inp...HEAD` is four files, 211 insertions: the three modules below
and three generated root imports. The initial untracked handoff was left untouched.

## Verdict

**FAIL on package hygiene: the protected `KAM.lean` diff is nonempty.** All eight theorem
exports **PASS for their assigned mathematical scope**. There is no theorem counterexample,
added mathematical premise, weakened source conclusion, or unproved bundle component in these modules.
No frozen theorem anchor is assigned to this package, so provider/frozen equality and seal-body
checks are not applicable; this audit does not certify any physical headline or seal an anchor.

The brief explicitly requires `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
to be empty. Instead, `KAM.lean:520,559,565` adds public imports of PeriodOneNodes,
LeftoverNodes and ConvNodes. These are exactly the package's modules, not inherited unrelated
changes. The handoff discloses regeneration, but supplies no explicit exception to the
protected-diff requirement or AGENTS rule 10 (“Never edit ... KAM.lean”). Its “Deviations:
none” claim therefore needs qualification. This is an integration-rule failure, separate
from the passing theorem audits and source lint. No protected file was repaired by this auditor.

## Authority and scope

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the supplied package audit brief, Track P
statement.md, and the handoff including its AUDIT FOCUS and overnight ruling. The user's exact
worktree report path overrides the generic brief's instruction to write in the main inp worktree.
Only these three Lean modules were audited as new code:

- `KAM/Planetary/Hamiltonian/PeriodOneNodes.lean` (85 lines).
- `KAM/Planetary/Newtonian/LeftoverNodes.lean` (96 lines).
- `KAM/Planetary/Nondegeneracy/ConvNodes.lean` (27 lines).

For every table row below I read the entire corresponding NODE record in
`docs/graph/P/DEPGRAPH.md`, including SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS and
SOURCE_CONCLUSION, and the cited blueprint statements and proof lines. The controlling
proposal is `/root/code/KAM-inp/docs/tracks/P/audits/LREF-P-audit-1.md:44-91`,
“Exact one-line bundle statements”; it is not present in this package checkout.
No independent SIGNED signature module or design table mapping additional nodes to these new
modules was found in the handoff, local drafts, or Track P designs (including the main inp
Track P design directory). The explicit eight-row handoff and ruling define this slice.
There is no SIGNED declaration requiring a different consumer-narrowing audit.
All seven proposed signatures match the landed signatures exactly after removing the theorem
name and whitespace; fresh Lean type comparisons and declaration copies also pass.
The cone lemma follows the eighth row's explicit positive-dilation contract.

## Per-node and declaration audit

Names in this table have prefix `KAM.Planetary.`. P1, P6 and P10 denote the respective
files `blueprint-P/parts/p1-hamiltonian-tools.tex`, `p6-newtonian-models.tex` and
`p10-nondegeneracy.tex`.

| Node / graph record | One named declaration / module line | Verdict | Literal conclusion, hypotheses and order |
|---|---|---|---|
| `stepP:p1:pc-c` / DEPGRAPH:2561-2588; P1:128-139 | `period_convert_bundle` / PeriodOneNodes:31 | PASS | Nine conjuncts give analyticity iff, derivative identity, derivative injectivity iff, pullback factor `(2π)*(2π)`, global zero-pullback iff, arbitrary shift-family `T` equivalence, injectivity modulo the parameter lattice, flow derivative iff, and frozen fast-shift identity. No analyticity or torus assumption added. κ, omega and T are fixed before the pointwise quantifiers; the flow fixes θ,v,t exactly as proposed. The two sides use frequencies omega/(2π) and omega with identical time. The nonzero linear bijection proves the reverse directions; no missing private helper remains. |
| `stepP:p6:pl-a` / DEPGRAPH:11168-11194; P6:39-47 | `planeLength_algebra` / LeftoverNodes:31 | PASS | v,w,c in source order. All seven source algebra clauses occur in one declaration, including the squared-length/dot identity and triangle inequality, without premises. |
| `stepP:p6:pl-b` / DEPGRAPH:11196-11221; P6:41,48 | `planeLength_norm_bounds` / LeftoverNodes:40 | PASS | Arbitrary v; both max-norm comparisons and the exact sqrt(2) factor in one declaration. Physical length is the frozen Euclidean length; ambient Pi norm is used only for the comparison. |
| `stepP:p6:pl-c` / DEPGRAPH:11223-11252; P6:42,49 | `planeLength_smooth_deriv` / LeftoverNodes:45 | PASS | v, its sole guard v≠0, then arbitrary h. Literal `ContDiffAt ℝ ∞` for length and reciprocal, followed by both evaluated Fréchet derivative formulas. The reciprocal expression is `-(v·h)/l(v)^3`, exactly the blueprint statement and the proposed signature; the graph's `-Dl/l²` is the equivalent chain-rule expression. Analyticity is used to prove the stated smoothness, not substituted for it. |
| `stepP:p6:dom-smooth` / DEPGRAPH:11315-11344; P6:54-59 | `hamiltonians_contDiffOn` / LeftoverNodes:59 | PASS | Both literal `ContDiffOn ℝ ∞` conclusions on W in one declaration; point z is quantified inside ContDiffOn. Stronger than the standing physical assumptions: any n and real parameters, without positivity restrictions. No extra conclusion-shaped regularity assumption. Openness of W supplies unique differentiability for the analytic-to-smooth conversion. |
| `stepP:p6:rc-pack` / DEPGRAPH:11977-12009; P6:160-177 | `reconstruction_pack` / LeftoverNodes:68 | PASS | Fixes G,m0,m,μ and their source signs, then arbitrary J,z and R1/R2 for each t∈J. First conclusion is the interval predicate with G absorbed exactly once into actualMasses; second is the all-time predicate conditional on J=univ. Includes μ=0. No openness, connectedness, continuity-in-time or uniformity premise imposed on J. Omits unnecessary n≥1 standing restriction, hence stronger. |
| `stepP:p6:ot-apply` / DEPGRAPH:12175-12203; P6:194-205 | `orbit_transfer_pack` / LeftoverNodes:83 | PASS | Both moving and fixed alternatives are implications under their own physical-torus and global NoCollision inputs, with arbitrary φ after them. Does not require both torus inputs simultaneously. All-time literal Newton/fixed predicates, barycentric maps, velocity factors and frequency/time placement agree. Shared sign assumptions come from the source's standing data; arbitrary ε and n strengthen it. |
| `bpP:p10:conv#data`, cone clause only / DEPGRAPH:17520-17551; P10:15-21 | `SecularForm.smul_mem_axes` / ConvNodes:23 | PASS (assigned clause only) | c>0, a∈axes n imply c•a∈axes n. Positivity and StrictMono are each multiplied by the same positive scalar. No physical/spectral data assumed. Arbitrary n strengthens n≥2. This proves dilation closure only; it does not state the full data node's action diffeomorphism, sorted spectrum, good sets, openness/convexity or norm facts. The complete `bpP:p10:conv#data` must not be marked closed solely from this export. |

Every assigned conclusion is now available as one named declaration. There are no additional
new public declarations outside these eight and no new HELPER exports. A repository-wide
scan of theorem/lemma/def/abbrev/structure declaration short names found exactly one declaration
for each of the eight names. Their namespaces are explicit and no root shadow is introduced.

## Definitions and proof soundness

There are **no new def, abbrev or structure declarations** in the three modules. Thus no new
object has a junk branch, fallback value, hidden premise field or changed carrier.
Relevant existing bodies were inspected to check the actual objects referred to by these signatures:

| Existing object | Classification and whole-carrier behavior relevant to the proof |
|---|---|
| Transport:132 `periodOne` | Literally κ precomposed with θ↦(2π)•θ for every κ. The inherited unconditional fderiv identity at Transport:188 handles nondifferentiable κ by proving nondifferentiability is preserved under the invertible precomposition; both total fderiv values are then zero. The bundle does not exploit an arbitrary fallback. |
| Frozen `Phase`, `bodyVector`, `planeSq`, `planeLength`, `planeDot` | Fin-function product, canonical coordinate extraction, sum of squares, its real square root, and scalar product. Correct on the entire carrier. Real.sqrt is always applied to a nonnegative squared length. |
| Models:39 `collisionFreeDomain`; frozen `NoCollision` | Exactly the phase points whose positional body vectors and pair differences have positive physical Euclidean lengths. |
| Frozen moving/fixed Hamiltonians and Hamiltonian vector field | Literal Newtonian Hamiltonians and field `(∂pH,-∂qH)`. Lean division is total; physical uses in reconstruction are collision guarded and mass denominators are positive. Smoothness for arbitrary mass parameters is valid because those divisions are constants as functions of phase. |
| Frozen `actualMasses`, barycentric positions and velocities | Sun mass m0, planet masses μ*m_i; positional denominator m0+μ*Σm_i positive under the stated source premises, including μ=0. Velocities divide by positive base masses. Same source maps on the full carrier; no conditional replacement map. |
| Frozen Newton interval/all-time/fixed predicates | Literal collision exclusion and both position/velocity derivative laws. The interval predicate absorbs G in its mass argument; the all-time predicate takes G separately. No change of physical law or time variable. |
| Frozen physical-torus predicate, symplectic form and fast shift | Actual analytic embedded Lagrangian/flow clauses, frozen symplectic sign and fast shift `((2πk,0),0)`. Only source torus premises are used for orbit transfer. |
| SecularForm.Basic:32 `Vec`, :47 `axes` | Vec is Fin n→ℝ; axes is exactly coordinatewise positivity and StrictMono. Positive dilation preserves both on every finite carrier, including n=0,1. No spectral premise is bundled into axes. |

The period bundle's local injectivity proof cancels a nonzero scalar; its symplectic identity
uses bilinearity of the frozen sum. Its zero-pullback iff uses the inverse scale to cover every
point. The planar and reconstruction bundles apply existing proved declarations with exactly
the source parameters. The new smoothness conversions use `∞`, not the stronger analytic order
`⊤`. The cone proof directly proves the two defining inequalities. No hard step is assumed.

The transitive project import traversal contains 79 KAM modules, including 53 frozen modules;
all 53 are manifest-state SEALED definitions. There is no imported frozen theorem module,
DRAFT_SORRY anchor or provider. All direct imports are public and the new files satisfy the
copyright/module/docstring/public-section conventions. No object body needs a new expose annotation.

## Independent validation

All audit-owned Lean/Lake/checker commands were serialized and inherited `LEAN_NUM_THREADS=1`.
The build gate invokes `nice -n 5 lake build`; the probe and kernel replay explicitly use
`nice -n 5`, and lint runs under nice as well (including its ABI child). No library rebuild,
clean, update, cache download or package-directory modification was requested. Other sessions
on this shared host were not launched or controlled by this audit.

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-glref KAM.Planetary.Hamiltonian.PeriodOneNodes KAM.Planetary.Newtonian.LeftoverNodes KAM.Planetary.Nondegeneracy.ConvNodes
```

Exit 0. Gate output: `[inp-gate] slot 1 acquired 03:21:26 for ...`.
Final output: `Build completed successfully (9125 jobs).`
No warnings in the three audited modules. Replayed unused-variable warnings belong to inherited
Algebra:146, Chart:193, Diophantine:124, Transport:55, Energy:106, Poincare.Chart:212,247
and Kepler.Mass:147,157,500,524. They are outside the changed-code scope.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-glref-1.lean
```

Exit 0, no errors or warnings. The scratch file imported only the three audited modules,
copied the seven exact proposal signatures under their lref names and proved each using its
landed export, and checked `example : type_of% @lref_name := @KAM.Planetary.export` for all
seven. It also proved the cone signature with the landed export and printed all eight axioms:

```text
'KAM.Planetary.period_convert_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planeLength_algebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planeLength_norm_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planeLength_smooth_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hamiltonians_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.reconstruction_pack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.orbit_transfer_pack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.smul_mem_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All eight have exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Hamiltonian.PeriodOneNodes KAM.Planetary.Newtonian.LeftoverNodes KAM.Planetary.Nondegeneracy.ConvNodes
```

Exit 0, single invocation. Output:

```text
replaying KAM.Planetary.Nondegeneracy.ConvNodes
replaying KAM.Planetary.Newtonian.LeftoverNodes
replaying KAM.Planetary.Hamiltonian.PeriodOneNodes
```

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 0. Complete output:

```text
check_lean_modules: PASS (1229 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated-root and errata-render checks passed silently. There was no stale-root exception
and no substantive lint violation. The passing generated-root check is consistent with the
handoff's regeneration; it does not waive the separate protected-path diff rule.

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest README.md
```

Both exit 0 with no output. The mandated broader protected-path command also exits 0 as a git
command, but its output is **not empty** (a failed audit assertion):

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Its only changes are:

```diff
+public import KAM.Planetary.Hamiltonian.PeriodOneNodes
+public import KAM.Planetary.Newtonian.LeftoverNodes
+public import KAM.Planetary.Nondegeneracy.ConvNodes
```

Direct scans of all three new modules found no forbidden proof escape, resource override or
EuclideanSpace token and no def/abbrev/structure. File line counts and maximum Unicode line
lengths are respectively 85/97, 96/96 and 27/95; all meet both caps. The complete three-dot
history contains no other production changes.

## Defects, deviations and remaining scope

- **Required integration correction:** the nonempty generated-root diff described above is the
  sole package failure found. The handoff explicitly records regeneration but says “Deviations:
  none”; the strict protected-path gate remains unpaid without an explicit controlling exception
  or an orchestrator integration change. This report makes neither change.
- **No suspected mathematical source or blueprint defect found** in the assigned clauses.
  The Part 10 text calls axes an “open convex cone”; the new theorem supplies positive dilation
  only, exactly the assigned missing clause. It must not be used as a reference for that node's
  unrelated full conclusion.
- Graph records still say NOT_STARTED / LEAN_REF `-` in this snapshot. This report supplies
  evidence for the seven step nodes and the one cone clause; it does not modify graph status.
- No fresh frozen theorem is proved here and there is no provider to seal. Conditional source
  orbit inputs do not establish any physical headline. No wider package or consumer audit is claimed.
- The audit introduced no source or statement deviation. Only this report was written in the
  repository; the scratch probe was deleted after its successful run. No state-changing git
  operation was performed. The initial untracked handoff remains unchanged.

Report validation: `git diff --check --no-index /dev/null docs/tracks/P/audits/GAP-LREF-audit-1.md`
exits 1 because the report is new, with no whitespace diagnostics; `git diff --check` exits 0.
