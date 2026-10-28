# P5-SCALE independent package audit 1

Verdict: **PASS WITH NOTES** for P5-SCALE. All nine required declarations match the
specified signatures; the six additional helpers have sound proofs and no added source
premises. This is helper infrastructure, not a provider or a frozen-anchor seal.
`planetary.properlyDegenerateKAM.v1` remains `DRAFT_SORRY`; no P-G closure is claimed.

## Scope, frozen inputs, and authority

Focused (tier 2), refute-first audit of **only**
`KAM/Planetary/PGAssembly/Scales.lean`, lines 1–134, at HEAD
`e696db6daeb0c928ad637c32d609cc3c82e91d30`. Read AGENTS.md, PLAN.md,
DECISIONS.md, the package brief, handoff AUDIT FOCUS, track P statement,
blueprint p5, relevant frozen P-G statement/definitions, P45 design and its
four earlier design audits. The earlier audits are background, not substitutes
for this review. Applied manuscript-audit and lean-statement-audit methods.

The user's explicit output path overrides the brief's parenthetical main-worktree
instruction. Only this report and temporary `.lake/abi-scratch/` probes were written;
no source repair, git mutation, generated-file rewrite, or sealing was authorized.
Builds, probes, replay and lint are serialized with `LEAN_NUM_THREADS=1` and niceness 5.

Frozen-v1 SHA256 inventory:

| Input | SHA256 |
|---|---|
| Scales.lean | `8ff5b8acc11b84ef5ebcff298ecb3ca7b7f128d0babca80ca4a5a63df6b9d881` |
| worktree `docs/tracks/P/design/P45-LEAN-DESIGN.md` | `fe084af07ac93f216e4f98e0ff5284319c5a544ee6df073af2069e9639d47559` |
| `/root/code/KAM-inp/.drafts/design/P45Signatures.lean` | `6f3ac05b5f71bca24343c84aa3df51812acac3f518381c5ae9ef645b2355c402` |
| worktree `blueprint-P/parts/p5-pg-assembly.tex` | `f8a5bc1683f30fed2576d0bb1ab6d51a1e6f00c6bf78c180d5a32efb0cef9968` |
| worktree P5-SCALE-handoff.md | `5ab22d604584215bf9c0f6debf6bce75a34e7cb0324a280803e01366d6a1b9ea` |

The signature file is absent from this worktree; its exact main-inp absolute path
above was read. Earlier design audits are in main-inp `docs/tracks/P/design/`,
not the handoff's suggested `audits/` directory. Design lines 1547–1578 reproduce
the same nine declarations as signatures lines 850–881. Revision 4 concerns
extension agreement, not these scales.

## Comparison with inp and scope notes

`git diff inp...HEAD` was inspected as requested. At audit start `inp` was
`81bb576d2ebe1ee5c4cb309059b68d4b24148218`. Git warns:

```text
warning: inp...HEAD: multiple merge bases, using 29c1447c330f69985b055f759e35ce8654e57c3e
```

Consequently this triple-dot diff includes inherited integration work (49 files),
not just the P5-SCALE commit. The exact protected-path check
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**:
`KAM.lean` has 22 inherited added imports. Frozen files, manifest and README have
no diff. This is recorded, not silently waived as an empty check.
`git show --stat HEAD` and `git diff HEAD^ HEAD --name-only` independently show
that e696db6 changes only Scales.lean (134 added lines); it does not edit KAM.lean.
The protected-path discrepancy therefore survives the check as a branch-history
note, not a newly introduced P5-SCALE source defect. No unrelated package is
certified by this audit.

## Declaration and node ledger

All names below have prefix `KAM.Planetary.`; line references are to frozen-v1
Scales.lean. “PASS” here is the scoped declaration result, not seal-readiness of P-G.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| scales / growth helper | `log_power_dominated_large` (29) | PASS | Arbitrary lower cutoff M; derives strict comparison from little-o. |
| kam-cond#scales | `log_power_dominated` (45) | PASS | Exact signature; supplies required existence. |
| kam-hyp#C1 | `kam_c1` (51) | PASS | Exact max formula, period factors and coth exponent. |
| kam-cond#scales | `PGScales` (56), including constructor and projections | PASS | Three unconstrained real coordinates, not an assumed result. |
| kam-cond#scales | `pgTau` (61) | PASS | Exact n+1 formula with n=a+b. |
| kam-cond#scales | `pgK0` (63) | PASS | Exact 6/(width/60) and log-plus=max 1 log. |
| kam-cond#scales | `pgChat` (66) | PASS | Exact max of 2^13 n and 24^(tau+1)/3. |
| kam-cond#scales | `PGScaleSpec` (68) | PASS | All five output inequalities; constants unchanged. |
| positivity helper | `pgTau_pos` (76) | PASS | Holds even for zero dimensions. |
| positivity helper | `pgChat_pos` (79) | PASS | Positive second max branch. |
| source width helper | `pgWidth_pos` (82) | PASS | delta/2 positive from produced extension. |
| C1 helper | `one_le_kam_c1` (85) | PASS | First branch of max. |
| kam-cond#scales | `kam_cond` (87) | PASS | Exact type, only source PGData, proves all five clauses. |
| kam-cond#scales | `pgScales` (128) | PASS | Exact source-prescribed choice from proved existence. |
| selected witness specification | `pgScales_spec` (130) | PASS | Full specification of the exported choice. |

Mechanical extraction compared theorem headers through `:=` and complete
non-theorem declaration bodies, with identical text for all nine required names.
The transient probe copied the two exact theorem types under fresh names and
applied the production theorems, copied each formula under a fresh name and checked
its defining equality by `rfl`, checked the three structure projection equations,
and applied `pgScales_spec` to the actual exported `pgScales`. It also separately
reconstructed width positivity from `(pgExtension d).delta_pos`.
Provider/frozen type equality and seal-copy probes are N/A: no provider or seal is
in this package, and no draft frozen theorem was imported for the probe.

## Binder and assumption audit

| Declaration(s) | Expanded binder | Bin | Source / justification |
|---|---|---|---|
| both growth lemmas | implicit p : real | TYPING | Signature 850; scalar exponent carrier. |
| both growth lemmas | implicit A : real | TYPING | Signature 850; scalar coefficient carrier. |
| both growth lemmas | hp : 0 < p | SOURCE | Signature 850. |
| both growth lemmas | hA : 0 < A | SOURCE | Signature 850. |
| large helper only | M : real | TYPING | New unbounded helper; arbitrary cutoff, no proof hypothesis. |
| `pgTau_pos`, `pgChat_pos` | a : natural | TYPING | Dimension. |
| `pgTau_pos`, `pgChat_pos` | b : natural | TYPING | Dimension. |
| `pgWidth_pos`, `one_le_kam_c1`, `kam_cond`, `pgScales_spec` | implicit a : natural | TYPING | Dimension. |
| same four | implicit b : natural | TYPING | Dimension. |
| same four | d : PGData a b | STANDING | Signature 879; expanded source record below. |

Per growth lemma: SOURCE=2, TYPING=2 (large helper: 3), STANDING=0,
RULED=0, EXCESS=0. Per dimension helper: TYPING=2, other bins=0.
Per data helper/result: TYPING=2, STANDING=1 before source-record expansion,
RULED=0, EXCESS=0. There are no instance inputs or extra section assumptions.

`PGData` is inherited source data (`KAM/Planetary/PG/Setting.lean:44–78`),
compared with the literal binders of frozen `properlyDegenerateKAM`:

| Expanded field | Bin | Meaning / frozen-source correspondence |
|---|---|---|
| ha | SOURCE | 0<a. |
| hb | SOURCE | 0<b. |
| V | TYPING | Fast action set. |
| hV | SOURCE | V open. |
| hVc | SOURCE | V connected (includes nonemptiness). |
| hVb | SOURCE | V bounded. |
| W | TYPING | Neighbourhood set. |
| hW | SOURCE | W open. |
| hVW | SOURCE | closure V subset W. |
| hboundary | SOURCE | Existential positive A,d and all 0<t<d collar-volume bound. |
| r0 | TYPING | Radius. |
| mu0 | TYPING | Parameter endpoint. |
| B | TYPING | Torsion constant. |
| hr0 | SOURCE | Positive radius. |
| hmu0 | SOURCE | Positive endpoint. |
| hB | SOURCE | Positive torsion constant. |
| H0 | TYPING | Fast Hamiltonian function. |
| P | TYPING | Perturbation family. |
| P0 | TYPING | Average constant coefficient. |
| Omega | TYPING | Slow linear coefficient. |
| beta | TYPING | Slow matrix coefficient. |
| hP | SOURCE | Joint real analyticity on Icc 0 mu0 times closed cylinder. |
| hperiod | SOURCE | Periodicity on the cylinder, all integer fast shifts. |
| hfreq | SOURCE | Frozen HasFastDiffeomorphism: analyticity on W, open gradient image, exists C1 inverse with both identities and image membership. |
| hBNF | SOURCE | Frozen HasSecularBirkhoffForm: all mu,I; oscillator-disc integrability and epsilon-delta little-o remainder, including zero. |
| htorsion | SOURCE | Determinant absolute value bounded below by B on V. |
| hsymm | SOURCE | Symmetric beta on V. |

Expanded PGData counts: SOURCE=17, TYPING=10, STANDING=0, RULED=0,
EXCESS=0. The nested frozen predicates were read: no assumed scale, KAM torus,
smallness conclusion, or analytic-constant witness is hidden in them. This
establishes the relevant assumption boundary, not a repeat proof audit of P5-FD.

## Definition classification

| Object | Classification | Body / full carrier |
|---|---|---|
| kam_c1 | Literal formula | Source max expression; defined on every PGData. |
| PGScales | Numeric record | Three real fields; restrictions are proved separately. |
| pgTau | Literal formula | n+1 for all natural dimensions. |
| pgK0 | Literal formula | Source real log-plus formula for every record. Total real log agrees with required positive argument for chosen scales. |
| pgChat | Literal formula | Source max; positive for all dimensions. |
| PGScaleSpec | Literal output predicate | Conjunction of source scale inequalities, never an extra premise of kam_cond. |
| pgScales | Source-prescribed witness selection | `(kam_cond d).choose`; specification immediately proved by pgScales_spec. |

For all seven: BODY_MATCH=OK; PUBLIC_CARRIER=OK; DEFINITION_VERDICT=PASS.
For the first six: WELL_DEFINEDNESS=N/A_LITERAL;
CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A.
For pgScales: WELL_DEFINEDNESS=OK by kam_cond;
CHARACTERIZATION=OK by pgScales_spec; CHOICE_INDEPENDENCE=N/A to this
existential witness contract. The source does not define unique numerical scales:
it says “There are constants, chosen in this order.” This is neither an intrinsic
uniquely characterized object nor an assertion that all numerical choices are equal.
Every chosen witness satisfies the complete inequalities; uniqueness would be false
and is not needed. There is no fallback, default branch, assumed output, or deferred
characterization. Constants depend only on d (dimensions implicit), before r and mu.

## Proof review and refutation pass

At lines 31–43 the actual Mathlib theorem
`isLittleO_log_rpow_rpow_atTop p (s := 2)` permits every real p and requires
only 0<2. Its little-o bound with c=1/(2A)>0 gives
A(log K)^p <= K^2/2. Intersecting the eventual statements with K>=M and K>1
makes log K nonnegative and K^2 positive, so the strict target follows.
The unused hp is harmless signature preservation; no positivity requirement was
silently added to Mathlib's theorem.

At lines 88–126, let C=C1>=1, w=pgWidth d>0, chat>0 and p=2 tau+2>0.
Take K>=exp 1 with 9 chat (720/w)^p (log K)^p<K^2.
Then k0=C^2 K>=C^2, and the exact logarithmic identity gives
pgK0=(720/w) log K: 6/(w/60)=360/w and log(K^2)=2 log K.
Multiplication by positive C^4 proves the first strict scale inequality.
Writing x=4 chat C^2>0, k1=x+1 is positive and k1^2>x.
Taking G equal to the displayed maximum proves the final weak inequality exactly.
This reproduces the intended order k0, then k1, then G.

Adversarial second pass checked zero-dimensional numeric helpers, equality at the
log-plus threshold, negative/zero C or width, real-rpow multiplication, arbitrary
record values, hidden r/mu dependence, and missing inequalities. Negative/zero C
or width are excluded by proved max/extension properties. K>=exp 1 forces log K>=1,
so the max rewrite is valid; both bases of the real-rpow product are nonnegative.
No counterexample or surviving mathematical blocker was found.

P5-FD is consumed through actual `pgAnalytic d` and `pgCU` values, not an added
PGAnalyticSpec premise. Width positivity consumes the produced PGExtension field.
No additional analytic estimate is needed for this arithmetic existence proof.
The later evaluation and KAM-smallness assertions in blueprint lines 218–225 are
outside the SCALE split; this module proves the scale-constant clauses only, as
specified in the design row and handoff.

## Validation receipts

1. Targeted compile gate (exit **0**):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5scale KAM.Planetary.PGAssembly.Scales
   [inp-gate] slot 2 acquired 13:07:25 for KAM.Planetary.PGAssembly.Scales
   Build completed successfully (9126 jobs).
   ```

   Cached warnings were replayed from CompactLipschitz (unused hW), JetsPoly
   (unused simp arguments) and Jets (unused mu/I). The only Scales warning is:
   `Scales.lean:29:45: Variable name hp is not explicitly referenced.` The handoff
   locates it in log_power_dominated; the actual binder is in
   log_power_dominated_large. This receipt discrepancy has no proof impact.

2. Exact signature/body/projection and selected-witness probe (exit **0**):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5ScaleAudit.lean
   ```

   All nine textual comparisons passed; all fresh-type and defining-equation
   checks elaborated. An initial probe invocation exited 1 because the audit
   harness omitted `noncomputable section` for copied real-valued definitions.
   After restoring the production section setting, the identical checks passed
   with no errors or warnings. This was a probe-generation error, not a package
   elaboration failure. No production file was changed.

   `#print axioms` output was identical for every declaration listed here:

   ```text
   log_power_dominated_large
   log_power_dominated
   kam_c1
   PGScales
   pgTau
   pgK0
   pgChat
   PGScaleSpec
   pgTau_pos
   pgChat_pos
   pgWidth_pos
   one_le_kam_c1
   kam_cond
   pgScales
   pgScales_spec
   ```

   Exact output form for each fully qualified name:
   `'KAM.Planetary.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`.
   No sorryAx or project axiom occurs.

3. Kernel replay, one invocation (exit **0**):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.Scales
   replaying KAM.Planetary.PGAssembly.Scales
   ```

   Only Scales is a new module in the bounded package; no provider module exists.

4. Import quarantine and module checks: a recursive source import scan found
   **80 project modules**, **0 providers**, **0 frozen theorem imports**, and
   **20 frozen definition imports**. Every imported frozen definition has
   manifest state **SEALED**. No production route to a DRAFT_SORRY anchor was found.
   Scales has the required copyright, module command, public imports, module
   docstring and exposed public noncomputable section. It has 134 lines, no
   forbidden escape/resource override, no EuclideanSpace, and no global instance.

5. Repository lint (exit **1**, solely the permitted generated-root exception):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (660 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other lint diagnostic occurred. The generated root was left untouched.
   The ABI subprocess ran after kernel replay, under the same thread/niceness
   constraints; no audit Lean/Lake invocation overlapped another.

6. Final integrity: `git diff --check` exits **0**. All five frozen-v1 hashes
   above were recomputed and unchanged. The transient audit probe was deleted.
   Report fences balance, there is no trailing whitespace, and the file has
   a terminal newline. Final status contains only the pre-existing untracked
   P5-SCALE-handoff.md and the new P5-SCALE-audit-1.md; no tracked file was edited.

## Findings and source/blueprint consistency

- **N1, branch-history hygiene note (survived refutation check).** The requested
  protected-path triple-dot diff contains inherited generated-root additions.
  Comparing the actual package commit against its parent refutes attribution to
  P5-SCALE. Retain this distinction when integrating; do not call the literal
  triple-dot check empty. No repair was performed.
- **N2, expected generated-root note.** This helper is not yet listed in the
  generated root. The audit brief expressly allows the isolated stale-root
  lint exception and forbids auditors from regenerating KAM.lean.
- **N3, minor handoff warning-location discrepancy.** The unused hp warning is
  at line 29, not line 45. Its type is the exact copied source requirement;
  unused positivity does not weaken the result.

No new suspected pinned-paper erratum, blueprint defect, changed premise,
constant, norm, carrier or normalization was found in the audited scales.
For context only, design Revision 4 / prior audit R4-S1 already identifies
blueprint p5 line 30's phrase “P~ = P at real points” as too broad outside the
controlled closed cylinder. The current inherited PGExtension.agrees includes
the corrected closed-cylinder premise; Scales uses only delta_pos and does not
use that agreement clause. This audit neither repairs that upstream wording
nor independently re-audits the extension construction.

The blueprint's entire kam-cond lemma includes later parameter evaluation;
this package's narrower `#scales` contract is explicit in design lines 220–221
and package row 499. Its existential scale record is fully proved, including
positive k1 (also in the exact signature); no claim is made that the whole KAM
application or later parameter package has been audited here.

No substantive mathematical finding remains unrefuted or uncertain within
this scope. No agent was delegated work. No source/network lookup or external
communication was needed: the mathematical authorities were the pinned local
blueprint, signatures and checked local Mathlib source. No deviation was
introduced into the package.

## Closeout

All 15 public declarations classified; 0 mathematical blockers; 0 EXCESS inputs;
0 unauthorized axioms; exact signatures and literal bodies verified; targeted
build and kernel replay passed. Lint's isolated generated-root exception and
inherited triple-dot root diff remain explicit notes. No frozen declaration
was modified or sealed. The only delivered file is this report at the exact
requested worktree path. Overall **PASS WITH NOTES**, scoped to P5-SCALE.
