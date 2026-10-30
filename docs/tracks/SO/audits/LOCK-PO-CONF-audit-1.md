# LOCK-PO-CONF independent package audit 1

**Overall verdict: PASS WITH NOTES for LOCK-PO and the conditional LOCK-CONF package.**
The eight signed declarations match the controlling signature text, including complete definition
bodies and structure fields. All 58 new public theorems have standard-foundation axiom closure.
The four targeted builds and exact-type/body probes pass. Verification receipts below state the
kernel and lint results separately. No frozen SO anchor is present or sealed by this package;
`lock_confinement` proves the signed conditional helper, not the certificate-to-barrier producer
or the lunar confinement headline.

Auditor: `maud-lockpo-1`, 2026-10-30 UTC. Focused tier-2 audit: read every line of the four added
modules, compare statements and definitions with the design, perform a separate adversarial pass,
then run serialized verification. No subagents, external-source searches, production repairs,
commits, or state-changing git operations. User authorization fixes the report destination in
this worktree and overrides the generic brief's main-worktree destination.

## Frozen inputs and scope

- Package HEAD: `e780f59fb5d7808ab8713dfe2cf686264704815f`.
- Compared branch `inp`: `98ced4ab75d556db5dcbac5d5850f9c293b07940`.
- Merge base: `1283e0b62faa278f2f95162fea6c67b1577a3ee2`.
- `git diff inp...HEAD`: exactly four new Lean files, 923 added lines. A mechanical comparison
  confirmed each diff hunk equals the complete corresponding source file inspected here.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the requested external
  `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the full named handoff, and the original
  `.drafts/briefs/lock/PKG-LOCK-PO-CONF.md` in `/root/code/KAM-inp`.
- The supplied handoff contains **no `AUDIT FOCUS` section**. Used its complete stated scope and
  the original dispatch: LOCK-PO design §§1–2, LOCK-CONF §5, ownership table §6, exact signatures,
  and design-audit-1 notes N1/N4. No SO `statement.md`, SO blueprint directory, or SO frozen
  manifest entries exist in this checkout. Unrelated I/N/P frozen anchors are not package targets.
- Controlling design: `/root/code/KAM-inp-lockdesign/docs/tracks/SO/design/SO-LOCK-DESIGN.md`,
  revision 3, observed design checkout HEAD `1c647798121d9b75732824f6ac557f0a4a4ffda1`.
  Read relevant sections and design audit 1; checked later design-audit-3 dispositions for drift.
- Signatures: `/root/code/KAM-inp-lockdesign/.drafts/design/SOLockSignatures.lean`; byte-identical
  to `/root/code/KAM-inp/.drafts/design/SOLockSignatures.lean` (`cmp`, exit 0).
  Draft signatures were read as text; no draft signature module was imported into the probe.
- Existing untracked handoff was present before this audit and was left unchanged.

Snapshot SHA256 (frozen-v1):

| Input | SHA256 |
|---|---|
| `KAM/SpinOrbit/Lock/PO/Green.lean` | `a3046eb37afc076baa00c20aa6b11d6f9b827d03cd1a6768374dad2eaa043efd` |
| `KAM/SpinOrbit/Lock/PO/Contraction.lean` | `b9a429bc2832196d83bbd006bdd829348b8978647ed30e2ff4c049f5042a6be4` |
| `KAM/SpinOrbit/Lock/PO/Orbit.lean` | `9d60c414f08692c57dd4c904685181d13c2480b74ce8249907db3883599e9b71` |
| `KAM/SpinOrbit/Lock/Confine.lean` | `5653469d434a9fc42a5c84e5214e264439d365bd643f6ae266b363ce0cbc09d7` |
| Design | `7785225bb6f3d3985ae7719f3aecf107eb33302530147bbff5672935eb170c6d` |
| Signatures | `aa544d085056410f205df49c08a778e854ad79ea48ad158fffe5302c3d0cd60d` |
| Audit brief | `316d17309e362cccf5ee0c182cfe3142c9fad9cd4b8c295332d751d4a334d37d` |
| Handoff | `1d2df1ff20cafe0f6483387066aed3c162dd6f0e987adc8e59921f60ce034745` |

## Anchor/package verdicts and refutation results

| Target | Verdict | Scope |
|---|---|---|
| `lunarSyncOrbit_spec` | PASS | Unconditional C² odd one-periodic physical-model orbit. |
| `lunarSyncOrbit_unique` | PASS | Global uniqueness among exactly `IsSyncOrbit` functions; oddness retained. |
| `lunarSyncOrbit_bound` | PASS | Both literal bounds, for every real phase, with no extra premise. |
| `lock_confinement` | PASS WITH NOTES | Exact signed conditional helper; supplied barrier invariance is explicit and authorized. |
| Frozen SO anchors / headline `lunar_sync_lock` | N/A | No anchors or provider exports assigned; no sealing or headline closure asserted. |

No mathematical or statement-fidelity blocker survived the refutation pass.

**PO spine.** `Green.lean:46,96,138` proves Taylor control, the 1/32 and 1/4 Dirichlet estimates,
and half-integer zeros from oddness plus period one. The primitive formula is the design's
Green inverse; continuity premises pay for differentiating integrals. `Contraction.lean:178`
proves the actual sup-metric estimate with coefficient `soLip / 32`; the weaker 1/2 contraction
constant is then proved from a numerical bound rather than assumed. `poSet` is closed,
complete, and inhabited by zero. `Orbit.lean:112` derives C² regularity from the fixed-point
identity; `green_syncForce_eq` proves Dirichlet uniqueness with M=0, so every odd periodic
solution is that fixed point. There is no boundedness premise smuggled into the uniqueness
statement: boundedness of an arbitrary orbit is proved before constructing `toPoSet`.

**Numerical refutation attempt.** Recomputed all seven coefficient polynomials with Python
`fractions.Fraction`, independently of Lean's `norm_num`. The sum is approximately
0.6197295208238748 and the off-mode sum approximately 0.12349334284476096. Using the rational
π upper bound 31416/10000 gives L ≤ 0.03376315624360834 and η ≤ 0.0005353940265159194.
The implementation safely uses looser rational ceilings 3377/100000 and 5355/10000000.
Starting from 27/320000, its first improvement is exactly
`(5355/10000000 + (3377/100000)*(27/320000))/32`, approximately 0.0000168234169921875,
which is below 17/1000000. The derivative ceiling is exactly
`(5355/10000000 + (3377/100000)*(17/1000000))/4 = 0.0001340185225`, below 27/200000.
All comparisons were checked as exact fractions, as well as in the compiled Lean proof.
The alternate sharpening route changes no signed premise or conclusion. N1 is discharged.
The phase-shift counterexample ψ+1/2 does not refute the submitted uniqueness theorem because
it does not satisfy oddness; the correct restriction from N4 is preserved.

**CONF spine.** `Confine.lean:104` treats both argument branches and the real-axis endpoints.
For a nonzero point on the cut, negating the complex coordinate gives a local continuous
branch; period one of P identifies the two values. The centre I=0 never enters this argument.
`lockRegion` overlaps a positive-action collar with the angle-free core. At a frontier point,
I≥Iin>0; continuity and the lower bound on P force I=P. At the initial point I<Iin≤P, so it
is outside the invariant graph. The actual `gen_barrier` call (`Confine.lean:202–224`) supplies
all its premises with W=G=J=univ and `so_global_exists_unique`, proving strict confinement in
both time directions and the stated global uniqueness. No invariant-barrier producer is
claimed here. Inspected `KAM/ODE/Exit.lean:107,140`: invariance ranges over every solution on
every connected interval, and the barrier lemma yields all t in J, not only forward times.

### Nonblocking notes and suspected design defects

1. **Ownership wording, survived text re-check.** Signatures:110 calls
   `abs_le_of_libAction_lt` a “LOCK-CONF corollary”; design §5:500 says it gives coordinate
   bounds. However the controlling dispatch assigns CONF only the region/continuity/frontier/
   barrier application, and design §6:519 explicitly assigns both `abs_le_of_libAction_lt`
   and `sqrt_libAction_le` to **LOCK-ASSEMBLY**. Their absence here is consistent with the
   explicit package allocation, not an incomplete PO/CONF implementation. Assembly still owes
   both results. `lunarOmega` is also outside this package's dispatch.
2. **Handoff collision is stale, independently checked.** The handoff reports duplicate
   `libAction` on `inp-lockcoords`. Current sibling commit
   `60cd4c675db896464be3dd3941b999e90e31d5e5` deletes that definition from `Coords/Maps.lean`
   and imports `Lock.Confine` in `Coords/Inverse.lean`. The current short-name scan passes.
   This is read-only sibling evidence, not a claim that the sibling has been merged here.
3. **Rounded equality in the design, LOW editorial note.** At the hashed design §1.4:119,
   “Σ|Aₘ| = 0.61973” is not a literal exact equality: the exact coefficient sum is the rational
   near 0.6197295208238748 above. Treat the decimal as rounded (`≈`), or write a rational upper
   bound. Independently evaluating the exact polynomials refutes literal equality; the Lean
   implementation instead proves the valid upper bound 61974/100000. No proof here relies on
   the printed equality, and the signed final bounds remain valid.
4. Generated-root lint exception and the inherited `KAM.ODE.gen_exit` unused-section-variable
   warning are recorded in the verification receipt. No package-source warning was emitted.

These concern our design/handoff/integration text, not a pinned external mathematical source.
No pinned-source erratum or substantive implementation deviation was found. Proposed editorial
repairs are not applied during this report-only audit.

## Expanded signed-premise audit

The authority is the draft design contract, not an already frozen source theorem. Conditional
helpers are identified explicitly. TYPING includes object binders; SOURCE means an actual
premise of this exact design statement. Local quantifiers inside the fields retain their
original scope. Every logical structure field is expanded below; none is hidden as a theorem
closure claim.

| Target | Binder / expanded field | Bin | Exact contract |
|---|---|---|---|
| `lunarSyncOrbit_spec` | none | — | Signatures:45; unconditional. |
| `lunarSyncOrbit_unique` | `ψ : ℝ → ℝ` | TYPING | Signatures:48. |
| same | `h.1 : ContDiff ℝ 2 ψ` | SOURCE | `IsSyncOrbit`, signatures:34–37. |
| same | `h.2.1 : Periodic ψ 1` | SOURCE | Same predicate. |
| same | `h.2.2.1 : ∀ φ, ψ (-φ) = -ψ φ` | SOURCE | Same predicate; essential oddness. |
| same | `h.2.2.2 : ∀ φ, ψ'' φ = -soVq (φ+ψ φ) φ` | SOURCE | Same predicate; physical equation. |
| `lunarSyncOrbit_bound` | `φ : ℝ` | TYPING | Signatures:53–54; no bound premise. |
| `lock_confinement` | `Ω : ℝ` | TYPING | Signatures:104. |
| same | `Iin : ℝ` | TYPING | Same. |
| same | `Iout : ℝ` | TYPING | Same. |
| same | `c : ℝ → ℝ` | TYPING | Same. |
| same | `hΩ : 0 < Ω` | SOURCE | Signatures:104. |
| same | `hc : ContDiff ℝ 2 c` | SOURCE | Same. |
| same | `B.P : ℝ → ℝ → ℝ` | TYPING | `LockBarrier`, signatures:90–102. |
| same | `B.continuous` | SOURCE | Continuous on the entire real α–φ plane. |
| same | `B.periodic_α` | SOURCE | Period one for all α,φ. |
| same | `B.periodic_φ` | SOURCE | Period one for all α,φ. |
| same | `B.invariant` | SOURCE | Explicit conditional-helper premise, design §§1.5,5. |
| same | `B.lower` | SOURCE | ∀ α φ, Iin ≤ P α φ. |
| same | `B.upper` | SOURCE | ∀ α φ, P α φ ≤ Iout. |
| same | `B.pos` | SOURCE | 0 < Iin. |
| same | `x₀ : ℝ × ℝ × ℝ` | TYPING | Signatures:105. |
| same | `h₀ : libAction Ω c x₀ < Iin` | SOURCE | Same. |

Counts: SOURCE 14, STANDING 0, TYPING 8, RULED 0, EXCESS 0. The four constituents of
`IsSyncOrbit` and seven logical `LockBarrier` fields have all been exposed. The typed
invariance premise is permitted for this distinctly named conditional helper, and must be
produced by LOCK-GRAPH before using confinement for a source-level headline.

## Definition classification

All bodies match the intended whole-carrier object; no fabricated witness, active fallback,
or hidden typeclass premise was found. All are unfrozen implementation declarations.

| Definition / structure | Classification and total-carrier check |
|---|---|
| `lockPrim` | Literal interval integral; calculus theorems explicitly require continuity. |
| `greenD` | Literal primitive minus its interval-average constant; exact design formula. |
| `green` | Literal second primitive; odd/periodic inverse properties proved on their stated domain. |
| `soLip` | Literal physical Lipschitz majorant 16π²εΣ\|Aₘ\|. |
| `soEta` | Literal off-resonant diagonal forcing majorant 4πεΣ_{m≠2}\|Aₘ\|. |
| `syncForce` | Literal negative force along q=φ+d(φ), for every d and φ. |
| `poSet` | Literal closed subspace predicate on bounded continuous real functions. |
| `syncMap` | Constructed Green image; proofs establish boundedness, continuity, parity and periodicity. |
| `IsSyncOrbit` | Literal signed C²/periodic/odd/ODE predicate; not a result bundle. |
| `lunarSyncOrbit` | Signed choice definition; `exists_isSyncOrbit` makes its zero branch impossible on the entire parameter-free domain. `lunarSyncOrbit_spec` and `_unique` prove full characterization and choice independence. |
| `toPoSet` | Canonical rebundling of the original function; its norm bound is proved from the supplied equation, not assumed. |
| `syncFixed` | Mathlib fixed point on the proved nonempty complete space; existence and uniqueness supplied by the proved contraction. |
| `libAction` | Literal signed action formula on all Ω,c,x. Total division/derivative conventions do not provide geometric properties for Ω≤0 or rough c; geometric consumers require Ω>0 and C². |
| `LockBarrier` | Literal signed conditional certificate structure; invariant graph assumption remains explicit. |
| `lockW` | Literal Y/√Ω+i√ΩX; nonzero claim only under Ω>0 and I>0. |
| `LockBarrier.barrierValue` | Literal P(arg(lockW)/2π,φ); total at zero, but continuity only claimed where I>0. |
| `lockRegion` | Literal union of core and positive-action collar; avoids using the angle at the centre. |

For the literal definitions: BODY_MATCH OK, PUBLIC_CARRIER OK, WELL_DEFINEDNESS N/A_LITERAL,
CHARACTERIZATION N/A_LITERAL, CHOICE_INDEPENDENCE N/A, DEFINITION_VERDICT PASS.
For `lunarSyncOrbit`: BODY_MATCH OK, PUBLIC_CARRIER OK, WELL_DEFINEDNESS OK,
CHARACTERIZATION OK, CHOICE_INDEPENDENCE OK, DEFINITION_VERDICT PASS **as an unfrozen package
object**. The independent probe proves `∃! ψ, IsSyncOrbit ψ` from the actual implementation;
there is no pending existence or uniqueness obligation. This is not frozen-manifest approval.
The two instances are canonical `CompleteSpace poSet` and `Nonempty poSet`; neither assumes
an unproved analytic result.

## Declaration ledger

Every name below has prefix `KAM.SpinOrbit.Lock.` (including dotted suffixes). Locators refer
to frozen-v1 package HEAD above. Node labels are the design sections because no SO blueprint
node labels have been assigned. All rows were source-read; the 75 named public declarations
were axiom-checked, including all 58 public theorems. The two instances are also listed.

| Design node / file:line | Declaration | Verdict | Reason |
|---|---|---|---|
| §2.1, `Green.lean:46` | `taylor_two_abs_le` | PASS | Second derivative bound implies global second-order remainder estimate. |
| §2.1, `Green.lean:96` | `dirichlet_bound` | PASS | Half-integer Dirichlet endpoints give M/32 and M/4, with no C² surplus premise. |
| §2.1, `Green.lean:138` | `half_int_zero` | PASS | Oddness and integer translates imply every n/2 zero. |
| §2.1, `Green.lean:150` | `lockPrim` | PASS | Literal first integral. |
| §2.1, `Green.lean:152` | `hasDerivAt_lockPrim` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Green.lean:157` | `continuous_lockPrim` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Green.lean:160` | `lockPrim_zero` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Green.lean:163` | `lockPrim_neg_of_even` | PASS | Integral substitution proves odd primitive. |
| §2.1, `Green.lean:171` | `lockPrim_neg_of_odd` | PASS | Integral substitution proves even primitive. |
| §2.1, `Green.lean:179` | `lockPrim_periodic` | PASS | Explicit zero-mean premise is required and paid by consumers. |
| §2.1, `Green.lean:198` | `greenD` | PASS | Correct integration constant. |
| §2.1, `Green.lean:201` | `green` | PASS | Correct Green inverse formula. |
| §2.1, `Green.lean:203` | `continuous_greenD` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Green.lean:206` | `hasDerivAt_greenD` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Green.lean:210` | `hasDerivAt_green` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Green.lean:214` | `continuous_green` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Green.lean:217` | `greenD_even` | PASS | Odd forcing gives even first derivative. |
| §2.1, `Green.lean:221` | `green_odd` | PASS | Even derivative primitive is odd. |
| §2.1, `Green.lean:225` | `greenD_periodic` | PASS | Zero mean of odd periodic forcing proved. |
| §2.1, `Green.lean:232` | `green_periodic` | PASS | Second primitive zero mean proved with correct constant. |
| §2.1, `Contraction.lean:38` | `soVq_add_one_add_one` | PASS | Integer harmonics preserve diagonal period one. |
| §2.1, `Contraction.lean:48` | `soVq_neg_neg` | PASS | Correct force oddness. |
| §2.1, `Contraction.lean:57` | `soLip` | PASS | Correct 16π² factor in q derivative majorant. |
| §2.1, `Contraction.lean:60` | `soEta` | PASS | Correct off-mode sum; m=2 vanishes on diagonal. |
| §2.1, `Contraction.lean:62` | `soLip_nonneg` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Contraction.lean:65` | `soVq_sub_abs_le` | PASS | Global q-Lipschitz estimate from sine bound. |
| §2.1, `Contraction.lean:85` | `soVq_diag_abs_le` | PASS | Diagonal forcing bound with resonant mode deleted. |
| §2.1, `Contraction.lean:100` | `syncForce` | PASS | Exact physical-model force. |
| §2.1, `Contraction.lean:102` | `continuous_syncForce` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Contraction.lean:106` | `syncForce_periodic` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Contraction.lean:110` | `syncForce_odd` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Contraction.lean:114` | `syncForce_abs_le` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Contraction.lean:117` | `syncForce_sub_abs_le` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Contraction.lean:125` | `syncForce_abs_le_diag` | PASS | Triangle inequality with global Lipschitz and diagonal bounds. |
| §2.1, `Contraction.lean:138` | `poSet` | PASS | Exact sup-metric odd periodic function space. |
| §2.1, `Contraction.lean:140` | `isClosed_poSet` | PASS | Closed intersections of evaluation equalities. |
| §2.1, `Contraction.lean:150` | `instance : CompleteSpace poSet` | PASS | Canonical completeness or zero inhabitant; no analytic axiom. |
| §2.1, `Contraction.lean:152` | `instance : Nonempty poSet` | PASS | Canonical completeness or zero inhabitant; no analytic axiom. |
| §2.1, `Contraction.lean:156` | `green_syncForce_bound` | PASS | Dirichlet bound constructs bounded image. |
| §2.1, `Contraction.lean:165` | `syncMap` | PASS | All subtype and boundedness obligations proved. |
| §2.1, `Contraction.lean:174` | `syncMap_apply` | PASS | Direct calculus, symmetry or bound transport with the necessary explicit premise. |
| §2.1, `Contraction.lean:177` | `dist_syncMap_le` | PASS | Actual L/32 contraction estimate; sup metric unchanged. |
| §2.1, `Contraction.lean:204` | `soLip_le` | PASS | Numerically proved crude L≤16. |
| §2.1, `Contraction.lean:216` | `syncMap_contracting` | PASS | 1/2 contraction derived from L≤16. |
| §1.1–1.4 / §2.1, `Orbit.lean:36` | `IsSyncOrbit` | PASS | Signed predicate body identical. |
| §1.1–1.4 / §2.1, `Orbit.lean:43` | `lunarSyncOrbit` | PASS | Signed choice body identical; fallback eliminated by existence. |
| §2.1, `Orbit.lean:48` | `IsSyncOrbit.hasDerivAt_orbit` | PASS | C² supplies differentiability. |
| §2.1, `Orbit.lean:52` | `IsSyncOrbit.hasDerivAt_deriv` | PASS | C² and equation identify derivative. |
| §2.1, `Orbit.lean:60` | `green_syncForce_eq` | PASS | Dirichlet uniqueness with zero forcing difference. |
| §2.1, `Orbit.lean:79` | `abs_le_of_syncForce` | PASS | Global bound derived for arbitrary orbit. |
| §2.1, `Orbit.lean:85` | `toPoSet` | PASS | Rebundles u using proved bound; no boundedness hypothesis. |
| §2.1, `Orbit.lean:93` | `toPoSet_isFixedPt` | PASS | Actual orbit equation gives a fixed point. |
| §2.1, `Orbit.lean:105` | `syncFixed` | PASS | Constructed Banach fixed point. |
| §2.1, `Orbit.lean:107` | `syncFixed_eq` | PASS | Fixed point identity as functions. |
| §2.1, `Orbit.lean:112` | `syncFixed_isSyncOrbit` | PASS | C², parity, period and equation all established. |
| §2.1, `Orbit.lean:133` | `exists_isSyncOrbit` | PASS | Explicit fixed-point witness. |
| §1.1–1.4 / §2.1, `Orbit.lean:136` | `lunarSyncOrbit_spec` | PASS | Exact signed unconditional existence contract. |
| §2.1, `Orbit.lean:141` | `IsSyncOrbit.eq_syncFixed` | PASS | All odd periodic solutions are the same fixed point. |
| §1.1–1.4 / §2.1, `Orbit.lean:147` | `lunarSyncOrbit_unique` | PASS | Exact signed global odd-orbit uniqueness. |
| §2.1, `Orbit.lean:152` | `soLip_le_rat` | PASS | Safe rational ceiling, independently recomputed. |
| §2.1, `Orbit.lean:164` | `soEta_le_rat` | PASS | Safe rational off-mode ceiling, independently recomputed. |
| §2.1, `Orbit.lean:178` | `soForceBound_le_rat` | PASS | Safe 27/10000 crude force ceiling. |
| §2.1, `Orbit.lean:190` | `abs_le_of_syncForce_rat` | PASS | Two Dirichlet applications give both literal bounds. |
| §1.1–1.4 / §2.1, `Orbit.lean:213` | `lunarSyncOrbit_bound` | PASS | Exact signed phase-uniform value and derivative bounds. |
| §5, `Confine.lean:40` | `libAction` | PASS | Signed whole body identical. |
| §5, `Confine.lean:45` | `LockBarrier` | PASS (conditional) | Signed structure fields identical; conditional helper. |
| §5, `Confine.lean:59` | `lockW` | PASS | Correct inverse polar coordinate. |
| §5, `Confine.lean:66` | `LockBarrier.barrierValue` | PASS | Correct signed graph value. |
| §5, `Confine.lean:69` | `continuous_libAction` | PASS | C² gives continuity of c and deriv c. |
| §5, `Confine.lean:75` | `continuous_lockW` | PASS | C² gives continuity of both components. |
| §5, `Confine.lean:81` | `lockW_ne_zero` | PASS | Positive action excludes the centre when Ω>0. |
| §5, `Confine.lean:104` | `LockBarrier.P_arg_neg` | PASS | All argument branches and real-axis cases covered. |
| §5, `Confine.lean:124` | `continuousOn_P_arg` | PASS | Period-one P removes argument cut on positive action. |
| §5, `Confine.lean:153` | `lockRegion` | PASS | Exact core/collar region from design. |
| §5, `Confine.lean:156` | `isOpen_lockRegion` | PASS | Angle continuity used only in positive-action collar. |
| §5, `Confine.lean:173` | `frontier_lockRegion_subset` | PASS | Positive frontier points lie on exact invariant graph. |
| §5, `Confine.lean:202` | `lock_confinement` | PASS (conditional) | All gen_barrier premises supplied; exact signed helper type. |

## Verification receipt

All Lean/Lake checks were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No heartbeat, recursion-depth or synthesis-budget override. No library clean or cache update.
The gate commands target one package module per invocation; existing build artifacts were reused.

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-lockpo KAM.SpinOrbit.Lock.PO.Green
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-lockpo KAM.SpinOrbit.Lock.PO.Contraction
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-lockpo KAM.SpinOrbit.Lock.PO.Orbit
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-lockpo KAM.SpinOrbit.Lock.Confine
```

All exit 0, respectively:

```text
Build completed successfully (2771 jobs).
Build completed successfully (2892 jobs).
Build completed successfully (2893 jobs).
Build completed successfully (2890 jobs).
```

The last three replay the inherited warning at `KAM/ODE/Exit.lean:36:0`:
`automatically included section variable(s) unused in theorem KAM.ODE.gen_exit: [NormedSpace ℝ E]`.
No warning originates in the four audited files.

### Exact contracts and axioms

Mechanical text extraction compared complete bodies of `IsSyncOrbit`, `lunarSyncOrbit`,
`libAction`, the entire `LockBarrier` structure, and the four signed theorem headers through
`:=`. All eight are **IDENTICAL**, including names, binder order, implicitness, constants,
quantifiers and namespaces. Comments are not part of this comparison.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/LockAudit.lean
```

Exit 0, no warnings/errors. Probe SHA256:
`e63bc30159f4089d2123a0482cd209bd799c344f7afd31be4007cb2d1cf1ae05`.
The probe imports only the four production modules, checks copied signed definition bodies
by `rfl`, and elaborates the four copied signed theorem statements under fresh names with:

```lean
-- Bodies, with exactly the signed explicit binders in order:
by exact KAM.SpinOrbit.Lock.lunarSyncOrbit_spec
by exact KAM.SpinOrbit.Lock.lunarSyncOrbit_unique ψ h
by exact KAM.SpinOrbit.Lock.lunarSyncOrbit_bound φ
by exact KAM.SpinOrbit.Lock.lock_confinement hΩ hc B x₀ h₀
```

There is no provider/frozen seal probe to run: no provider or frozen anchor belongs to this
SO slice. The fresh-name signed-statement checks are the applicable exact-type assembly gate.
Additional sorry-free probes prove unique existence, the physical `soField_eq` equation bridge,
and the general Green value/derivative bounds by supplying their actual derivative, parity
and periodicity dependencies. No premise is deferred to an assumption-shaped wrapper.

`#print axioms` was run on all 75 named public declarations (58 theorems, 16 definitions,
one structure), plus the independent unique-existence probe. **Every one of the 76 lines**
reports exactly `[propext, Classical.choice, Quot.sound]`. Full output:

```text
'KAM.SpinOrbit.Lock.taylor_two_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.dirichlet_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.half_int_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockPrim' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.hasDerivAt_lockPrim' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.continuous_lockPrim' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockPrim_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockPrim_neg_of_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockPrim_neg_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockPrim_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.greenD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.green' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.continuous_greenD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.hasDerivAt_greenD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.hasDerivAt_green' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.continuous_green' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.greenD_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.green_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.greenD_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.green_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.soVq_add_one_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.soVq_neg_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.soLip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.soEta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.soLip_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.soVq_sub_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.soVq_diag_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.continuous_syncForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncForce_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncForce_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncForce_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncForce_sub_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncForce_abs_le_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.poSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.isClosed_poSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.green_syncForce_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.dist_syncMap_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.soLip_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncMap_contracting' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.IsSyncOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lunarSyncOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.IsSyncOrbit.hasDerivAt_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.IsSyncOrbit.hasDerivAt_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.green_syncForce_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.abs_le_of_syncForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.toPoSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.toPoSet_isFixedPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncFixed_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.syncFixed_isSyncOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.exists_isSyncOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lunarSyncOrbit_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.IsSyncOrbit.eq_syncFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lunarSyncOrbit_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.soLip_le_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.soEta_le_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.soForceBound_le_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.abs_le_of_syncForce_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lunarSyncOrbit_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.libAction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.LockBarrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.LockBarrier.barrierValue' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.continuous_libAction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.continuous_lockW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockW_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.LockBarrier.P_arg_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.continuousOn_P_arg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockRegion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.isOpen_lockRegion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.frontier_lockRegion_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lock_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'LockAudit.orbit_exists_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Lock.PO.Green KAM.SpinOrbit.Lock.PO.Contraction KAM.SpinOrbit.Lock.PO.Orbit KAM.SpinOrbit.Lock.Confine
```

Exit **0**, one invocation, output:

```text
replaying KAM.SpinOrbit.Lock.Confine
replaying KAM.SpinOrbit.Lock.PO.Orbit
replaying KAM.SpinOrbit.Lock.PO.Contraction
replaying KAM.SpinOrbit.Lock.PO.Green
```

This independently replays the four production modules in the kernel. It does not substitute
for the source-fidelity checks above.

### Lint, imports, protected paths, names

LINT_RECEIPT_PENDING

Direct and recursive import inspection reaches 14 KAM modules, no frozen modules, no providers,
and no DRAFT_SORRY anchor. Therefore no imported-frozen manifest state requires an exception.
Only the normal Mathlib/KAM foundations appear in the axiom closure above.

All four files have copyright, `module`, public imports, module docstring, public section and
exposed definitions through `@[expose] public noncomputable section`. Line counts are Green
249, Contraction 226, Orbit 220 and Confine 228; maximal line lengths respectively 99, 99, 96,
and 100 Unicode characters. No forbidden proof escape, budget override, `EuclideanSpace`,
`native_decide`, or root shadow was found.

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-lockpo KAM.SpinOrbit.Lock.PO.Green KAM.SpinOrbit.Lock.PO.Contraction KAM.SpinOrbit.Lock.PO.Orbit KAM.SpinOrbit.Lock.Confine
```

Exit 0: `short-name check OK (no reused public short name)`.

```sh
git diff --check inp...HEAD
git diff --quiet inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md
```

Both exit 0, no output. The protected-path diff is empty. No generated root was regenerated.

## Closeout and limits

All 75 named public declarations and both instances are classified; all signed contracts were
checked. No extra premise, weakened conclusion, widened constant dependence or meaning-changing
carrier was found. No production source was edited. The only retained audit artifact is this
report at the exact user-requested path; the pre-existing handoff remains untouched.

CLOSEOUT_RECEIPT_PENDING

The remaining certificate-to-barrier construction, coordinate transfer lemmas, literal checker,
actual lunar certificate kernel pass and frozen headline sealing are outside this package.
This audit does not promote any of those pending steps. LOCK-CONF remains conditional until
LOCK-GRAPH supplies its barrier, as the design explicitly requires.
