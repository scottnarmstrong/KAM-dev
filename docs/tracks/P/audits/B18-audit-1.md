# B18 independent package audit 1

**Overall verdict: PASS WITH NOTES.** Both signed theorems pass exact statement,
proof, consumption and axiom checks. All five mapped graph nodes are established.
The only outstanding hygiene item is the permitted stale generated-root lint
exception, whose complete result is recorded below. This is an infrastructure
package verdict; no frozen planetary theorem is newly sealed.

## Scope, authority and frozen inputs

Date: 2026-10-29 UTC. Tier-2, refute-first audit of **only**
`KAM/Planetary/WeakKAM/ParameterLipschitz.lean`. Read the repository rules, PLAN,
DECISIONS, common package-audit brief, B18 handoff, P11B design row B18 and node
rows, both P11B design audits, signed declarations, track-P statement, and source
`blueprint-P/parts/p11a4-limit-family.tex:192–206`. Earlier design findings F1/F2
are resolved by design audit 2; that design verdict is not treated as proof evidence.

The user's exact worktree report path overrides the common brief's main-worktree
parenthetical. Authorization: report-only edits and temporary local probes;
no repairs, commits, generated-file changes, or delegation. Acceptance criteria:
exact signed surface, complete mapped slice, no extra source-facing premises,
faithful output packaging, standard axioms, targeted build, kernel replay, and
hygiene with only the brief's explicit generated-root exception.

Snapshot V1:

| Input | Revision / SHA256 |
|---|---|
| HEAD | `1f061eb1e60db1c82bd8d9c2c64483a08da1cebe` |
| Compared `inp` | `3ad63f03c23dbf389faf960245f528c329c6b28c` |
| Git-selected merge base | `601636567629350384c65c33421e4efef34e39ff` |
| Other merge base | `ad0f5483090fd77980b64ebffb91d4ee617517b2` |
| ParameterLipschitz.lean | `86c088d497fd856e76dca8d1f4a6ddabf5cf5fdc3aabece6f856a374d33034ff` |
| `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean` | `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63` |
| P11B-LEAN-DESIGN.md | `b39ec4a5b9b976b355d6afe26047680ea2b1fbb1c86dd4073aa4428528961ea1` |
| p11a4-limit-family.tex | `c88030106491131ffde29078d1f0919ae092592bf37e1bbc68a87ab087369b2b` |

All line references below are to V1. The complete `git diff inp...HEAD` was
inspected, including the inherited B16/B17 additions. It contains eight new Lean
files, 1595 lines: ParameterLipschitz (265), Displacement (283), Tori (77),
ToriBridge (155), ToriField (101), ToriLimit (268), ToriReal (204), ToriStage (242).
`git diff 15d41662..HEAD --stat` isolates B18 to ParameterLipschitz alone.
Git warns: `inp...HEAD: multiple merge bases, using
601636567629350384c65c33421e4efef34e39ff`; this is retained, not silently resolved
by a different comparison. The inherited modules were inspected for context and
consumption; they are not independently recertified here.

## Signed declarations and complete node/declaration ledger

The theorem headers at lines 32–37 and 223–225 are **byte-identical** to their
signature-file headers at lines 784–789 and 827–829. The entire
`SelectionLipschitz` structure body at lines 90–96 is byte-identical to the signed
record at lines 819–825. Fresh Lean probes copy the signed theorem headers,
assemble their bodies using exactly their explicit arguments, and check type
compatibility in both directions. All pass.

| Node / role | Declaration / proof location | Verdict | Reason |
|---|---|---|---|
| Representation helper | `collar_real_sub`, 27–29 | PASS | Literal real-inclusion subtraction identity. |
| lf-stage analytic supplier | `collar_increment_lipschitz`, 32–88 | PASS | Exact signed `4 * e / t` bound on arbitrary K; no convexity or compactness premise. |
| lipschitz-family output | `SelectionLipschitz`, 90–96 | PASS | Same inherited family, separate and joint bounds exactly as signed. |
| Schedule helper | `lipFam_t_succ_le`, 104–110 | PASS | Collar radii decrease under the existing scalar context. |
| `stepP:p11a:lf-stage` | `lipFam_stage`, 113–150 | PASS | Literal increment difference bound `4 * selectionLimBound / t_(j+1)` for both retained parameters. |
| Positivity helper | `lipFam_alpha_nonneg`, 157–161 | PASS | Derived scalar nonnegativity; not an assumed estimate. |
| `stepP:p11a:lf-tel` | `lipFam_limit`, 193–211; stage setup 117–148 | PASS | Finite telescoping on the same chain; holomorphic increment with the literal bound; limit through `limit_uniform`. |
| `stepP:p11a:lf-sum` | `lipFam_limit`, 176–219 | PASS | Explicit summable nonnegative envelope; obtains parameter bound `2^-11`. |
| Conditional limit helper | `lipFam_limit`, 164–219 | PASS | Distinct helper assumes upstream scalar/limit data; all are supplied inside the source-facing constructor. |
| `stepP:p11a:lf-split` | `lipschitz_family`, 233–248 | PASS | Triangle inequality plus angle bound and the proved parameter bound on the same defect. |
| `bpP:p11a:lipschitz-family` | `lipschitz_family`, 223–261 | PASS | Exact signed constructor from raw source data; separate `2^-11` terms and joint `2^-10` max-norm bound. |

This covers all **8/8 explicit declarations** (seven theorems and one structure)
and all **5/5 mapped graph nodes** (parent plus lf-split/tel/stage/sum).
No unsigned export uses a graph node's name to hide a weaker conclusion.
Local names need not literally be `lf_split` etc.; the source goals occur at the
locations above, with their actual conclusions proved.

## Premise and definition audit

For `collar_increment_lipschitz`, the full binder inventory is:

| Binder | Bin | Source / meaning |
|---|---|---|
| `{n : ℕ}` | TYPING | Pi/Prod dimension, arbitrary including zero. |
| `K : Set (SelectionR n)` | SOURCE | Arbitrary retained set in lf-stage's local analytic claim. |
| `t : ℝ` | SOURCE | Collar radius. |
| `e : ℝ` | SOURCE | Supremum envelope. |
| `ht : 0 < t` | SOURCE | Positive stage radius. |
| `he : 0 ≤ e` | SOURCE | Nonnegative envelope. |
| `g : SelectionC n → SelectionPhaseC n` | SOURCE | Increment map, possibly any map satisfying the next premises. |
| `hg` | SOURCE | Holomorphic on the whole collar. |
| `hb` | SOURCE | Bound for every z in that collar; z and membership are universally quantified in the premise. |
| conclusion `b` | SOURCE | First real parameter. |
| conclusion `b ∈ K` | SOURCE | Source retained locus. |
| conclusion `b'` | SOURCE | Second real parameter. |
| conclusion `b' ∈ K` | SOURCE | Source retained locus. |

Counts including the conclusion's universal binders: SOURCE 12, STANDING 0,
TYPING 1, RULED 0, EXCESS 0. The absence of closedness/convexity is a valid
strengthening. No norm or dimensional convention changes.

For `lipschitz_family`, the outer binders are `{n}` (TYPING), `d` (STANDING
bundle expanded below), `ε` (SOURCE), `he` (SOURCE), `hsmall` (SOURCE), `f`
(SOURCE), and `hf` (SOURCE bundle expanded below). Their order is exactly signed:
no output family, iteration, estimate, or limit is accepted as an input.
Expanded logical inputs are:

| Field / premise | Bin | Source locator |
|---|---|---|
| `d.n_pos` | STANDING | sel-data (a), N >= 1. |
| `d.μ_pos` | STANDING | sel-data (a), mu >= 1. |
| `d.rho_mem` | STANDING | sel-data (a), rho in {1,2}. |
| `d.tau_nonneg` | STANDING | sel-data (a). |
| `d.tau_gap` | STANDING | sel-data (a), strict Diophantine exponent. |
| `d.compact` | STANDING | sel-data (b). |
| `d.positive_measure` | STANDING | sel-data (b). |
| `d.theta_pos` | STANDING | sel-data (b). |
| `d.theta_le` | STANDING | sel-data (b). |
| `d.strip_pos` | STANDING | sel-data (b). |
| `d.strip_le` | STANDING | sel-data (b). |
| `d.hessian_normalized` | STANDING | sel-data (b), C1 >= 1. |
| `d.beta_pos` | STANDING | sel-data (d). |
| `d.beta_le` | STANDING | sel-data (d), beta <= M. |
| `d.loss_pos` | STANDING | sel-data (b), epsilon-star > 0. |
| `d.loss_lt` | STANDING | sel-data (b), epsilon-star < volume K. |
| `d.holo` | STANDING | sel-data (c), whole U. |
| `d.real` | STANDING | sel-data (c), every real point in U. |
| `d.hessian` | STANDING | sel-data (c), operator norm <= C1 throughout U. |
| `d.finite_type` | STANDING | sel-data (d), existential derivative order <= mu for each unit c and y in K. |
| `d.top_bounds` | STANDING | sel-data (d), all orders 1 through mu+1, thickened K and unit tensor arguments. |
| `he` | SOURCE | situation S, epsilon > 0. |
| `hsmall` | SOURCE | situation S, epsilon <= admissible threshold. |
| `hf.holo` | SOURCE | sel-data (c), product strip/collar. |
| `hf.periodic` | SOURCE | sel-data (c), period 1, all integer shifts. |
| `hf.real` | SOURCE | sel-data (c), real slice of that product. |
| `hf.bound` | SOURCE | situation S, whole-domain norm <= epsilon. |

The 11 fields `μ, ρ, τ, ϑ, strip, C₁, β, M, loss, K, h` are the STANDING
numerical/geometric/function data from sel-data; none is a proof obligation.
Counting expanded logical inputs once: SOURCE 6, STANDING 21, TYPING 1
(dimension), RULED 0, EXCESS 0. Pure data also include source ε and f. Recursive
quantifiers in the fields above preserve their source order and domains; no
instance argument adds a mathematical assumption. Actual M0 is derived upstream,
not an additional free conclusion-shaped premise.

The distinct implementation helpers use constructed `WeakBudgetCtx`,
`SelectionComposition`, and `SelectionLimit` data conditionally. In particular,
`lipFam_limit` takes `hsum` and `hsumm`; this is not claimed as the source theorem.
At 226–235 the constructor produces its context via `free_radius` and
`weakBudgetCtx_of`, obtains both scalar premises via `param_lip_sum`, obtains
`L` via `displacement d ε he hsmall f hf`, and applies the limit helper to that
same L. Thus no hard step is moved into the public source theorem's premises.

**Definition classification:** no new `def`, `abbrev`, instance, selected object,
or totalized series is introduced. `SelectionLipschitz` is a literal output
record, extending the signed `SelectionDisplacement` with exactly two source
properties. It is not a standing assumption. Both fields and the entire inherited
witness are constructed by `lipschitz_family`. Its inherited `Kinf`, `defect`,
composition and limit are definitionally the same witnesses throughout.

`BODY_MATCH: OK`; `PUBLIC_CARRIER: OK`; `WELL_DEFINEDNESS: OK` (constructed
inhabitant); `CHARACTERIZATION: N/A_LITERAL`; `CHOICE_INDEPENDENCE: N/A`;
`DEFINITION_VERDICT: PASS`. No fallback or arbitrary new classical choice occurs.
Frozen `actionNbhd` is the existential strict max-norm collar, and frozen `Phase`
is the product of two real Pi spaces. They are consumed directly.

## Proof and adversarial refutation pass

The source lf-stage says: “Case |b-b'| < t_(j+1)/2” and “Case
|b-b'| >= t_(j+1)/2.” The implementation covers the equality endpoint in the
long case (44–49): two sup bounds give 2e, and the distance lower bound gives
`2e <= (4e/t) * distance`. No division by a parameter difference occurs.

In the short case (51–88), every segment point lies within distance < t/2 of
b. Its **closed** ball of radius t/2 therefore lies in the open t-collar.
`KAM.norm_fderiv_le_of_closedBall` is applicable there and gives `e/(t/2)`.
Inspection of `KAM/Strip/Cauchy.lean:53–84` confirms that the operator bound is
proved by unit complex lines and one-variable Cauchy; it has no factor n.
Restriction of scalars preserves the operator norm, and the real mean-value
bound applies on the segment. This does not require the segment to lie in K.
The case b=b' and even n=0 require no normalization by a zero vector.

At 121–148 the common input collar is `actionNbhd Kinf t_(j+1)`, contained in
the stage-j and stage-(j+1) parameter collars by Kinf's intersection identity
and the proved radius monotonicity. Real theta belongs to the half strip;
`iter_strip` and positive action radii supply the zero-section domain conditions.
The difference is holomorphic there and has exactly the inherited composition
increment bound. Thus there is no unsupported positive limiting collar.

At 176–219, set `v_j=(A_j+alpha_j)/t_(j+1) >= 0`. Positivity justifies
`max(A_j,alpha_j) <= A_j+alpha_j` and finite-sum domination by the actual tsum.
The finite-stage identity cancels the same initial `(theta,0)` at b and b'.
Pointwise convergence follows from `limit_uniform` at the real theta in s/4;
continuity of subtraction and norm passes the finite-stage inequality to L.
The scalar constant is explicitly bounded by
`4*(1+2^-11)*(2^-10/16) <= 2^-11`. Summability is a separately supplied proof,
so no totalized divergent tsum is being used.

The real reconstruction (235–243) cancels the initial zero-section value before
using the isometric real inclusion. The split at 244–248 uses angle and parameter
bounds for the same defect, and the joint norm at 253–261 is exactly the max of
the two real Pi norms. Both B19 consumer requirements are present on the same
record: `SelectionEvaluationOutput` extends it and uses this joint bound.
No narrowed signed conclusion needs an additional unproved consumer bridge.

Refutation attempts checked: disconnected/empty K; long-case equality endpoint;
coincident parameters; accidental Euclidean factor; wrong collar stage index;
lost real imaginary component; divergent-tsum shortcut; and unrelated output
witnesses. Each proposed defect is refuted by the cited proof or an exact-type
probe. No surviving mathematical blocker or unrefuted tentative finding remains.

## Verification and hygiene

All Lean/Lake/checker invocations were serialized with `LEAN_NUM_THREADS=1` and
`nice -n 5`. No simultaneous auditor Lean process, library clean/rebuild, package
mutation, cache fetch, heartbeat override, or source repair was performed.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b18 KAM.Planetary.WeakKAM.ParameterLipschitz
   ```

   Exit **0**. Output includes:

   ```text
   [inp-gate] slot 3 acquired 00:19:26 for KAM.Planetary.WeakKAM.ParameterLipschitz
   Build completed successfully (9215 jobs).
   ```

   Lake replayed existing dependency unused-variable/simp and deprecation
   warnings. No warning or elaboration design signal came from the audited file.

2. Exact signed assembly and axioms:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B18Audit.lean
   ```

   Exit **0**, no errors or warnings. Probe reconstruction: import the audited
   module; open Set/Real/MeasureTheory/Filter/Function/Metric and the source scopes;
   enter namespace `KAM.Planetary`, open KAM/KAM.Kepler and declare `{n : ℕ}`.
   Copy each signed theorem header under `b18Audit_<original-name>` and use:

   ```lean
   -- Body for the signed collar header:
   by exact collar_increment_lipschitz K t e ht he g hg hb
   -- Body for the signed family header:
   by exact lipschitz_family d ε he hsmall f hf
   -- For each of those two names:
   example : type_of% @b18Audit_collar_increment_lipschitz := @collar_increment_lipschitz
   example : type_of% @collar_increment_lipschitz := @b18Audit_collar_increment_lipschitz
   example : type_of% @b18Audit_lipschitz_family := @lipschitz_family
   example : type_of% @lipschitz_family := @b18Audit_lipschitz_family
   ```

   Then issue `#print axioms KAM.Planetary.<name>` for all seven public theorems.
   Complete axiom output:

   ```text
   'KAM.Planetary.collar_real_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.collar_increment_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lipFam_t_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lipFam_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lipFam_alpha_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lipFam_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lipschitz_family' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.ParameterLipschitz
   ```

   Exit **0**. Complete output:

   ```text
   replaying KAM.Planetary.WeakKAM.ParameterLipschitz
   ```

4. Lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1155 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Only the stale generated-root diagnostic fails, explicitly permitted by the
   common brief. Module checks, frozen guard and all 144 ABI hashes pass.

Static checks: 265 physical lines, maximum width **98**; copyright, `module`,
public imports, module docstring and exposed public section present. No forbidden
`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option`
token. All eight explicit short names occur exactly once in the project's
explicit declaration census. All declarations are in `KAM.Planetary`, with no
new root shadow. A recursively inspected **169-module project import closure**
contains no provider and no frozen theorem module, hence no DRAFT_SORRY import.
Its 14 frozen imports are definitions, not theorem anchors. No provider/frozen
seal-type test is applicable to this infrastructure-only slice.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: **empty**, apart
from the multiple-merge-base warning. `git diff --check inp...HEAD`: **exit 0**.
The module/signature/record comparisons, namespace/name scan, import walk and
forbidden-token scan were independently rerun in this worktree.

## Findings, errata and closeout

- **N1: permitted generated-root lint exception.** The orchestrator owns root
  regeneration. The source was not changed to remove this diagnostic.
- **N2: handoff source remark is imprecise, without a Lean defect.** The handoff
  says “the source says Lipschitz sums to 2^-10 in the statement.” The pinned
  source at p11a4:193–194 already states both separate 2^-11 terms and the joint
  2^-10 bound. Lean matches that exact display; there is no source/Lean deviation.
- No suspected pinned-source or blueprint mathematical defect was found. No
  deviation was introduced. Earlier design release gates are not re-audited as
  campaign-wide closure merely because this module builds and replays.

Both signed theorem exports pass; the record and all mapped steps pass. Only
this report is an audit deliverable. The pre-existing untracked B18-handoff.md
is preserved. Auditor-created scratch probes/data and temporary diff output are
removed after verification. No state-changing git command was used. Final
integrity and report-only status checks are recorded after completion below.

Final closeout: module, signature, design and blueprint SHA256 values still match
V1. Temporary `B18Audit.lean`, `B18-diff.txt` and the inherited-diff scratch output
were deleted. Final `git status --short` lists only this new report and the
pre-existing untracked handoff. `git diff --check` passes; the report has no
trailing whitespace, balanced code fences and a terminal newline. No required
B18 check is outstanding. The PASS WITH NOTES verdict records the allowed lint
exception and does not imply B19 or a frozen theorem is complete.
