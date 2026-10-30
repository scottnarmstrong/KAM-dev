# LOCK-GRAPH independent package audit 1

**Verdict: PASS WITH NOTES for LOCK-GRAPH and its signed export
`KAM.SpinOrbit.Lock.lockBarrier_of_certV2`.** The implementation produces the physical
`LockBarrier.invariant`; no invariant barrier, physical orbit, clock identity or graph is assumed
by the signed theorem. The engine-generic core is usable by a new engine through a wrapper,
verified by elaborating a wrapper quantified over arbitrary `EngineV2`.

This is an unfrozen infrastructure-package verdict, not a frozen-anchor seal or a proof of
`lunar_sync_lock`, a passing numerical certificate, or the certified synchronous-orbit headline.
No LOCK-GRAPH frozen anchor exists. The general I/N/P brief's provider/frozen seal-copy test is
therefore inapplicable; the signed SO design signature is the exact statement authority here.
The only hygiene exception is the brief-permitted stale generated root, detailed below.

## Scope, authority and fixed inputs

Auditor `maud-lockgraph-1`, 2026-10-30 UTC. Read `AGENTS.md`, `docs/PLAN.md`,
`docs/DECISIONS.md` (especially D45), the supplied package-audit brief, handoff, SO-LOCK
revision-3 design and signed declarations, and the actual diff and dependencies.
The user's explicit report destination overrides the generic brief's MAIN-worktree destination.
Only this report and temporary `.lake/abi-scratch/` evidence were written; no implementation,
frozen, manifest, generated-root or git-state changes were made. No subagents were used.
The user's four extra-focus points are all checked below.

Snapshot v1:

- HEAD: `687e2da705c9fb034d091a7fba9d66d0ed0139b5`.
- `inp`: `7b86cf178eaaffba3a7a4205a561b41ef3660455`.
- Merge base: `e78c95b46ab1321ef5896600b7ee7fc9babfa351`.
- Full required comparison: `git diff inp...HEAD`, three new files, 683 added lines.
  This is the merge-base comparison, not an assertion that current `inp` equals the merge base.
- Handoff was already untracked when the audit began; it was read without modification.
- SO has no package blueprint or `docs/tracks/SO/statement.md` in this checkout. The design
  §§1.5, 3, 6 and its signatures govern this package; no I/N/P anchor is claimed by it.

| Input | SHA-256 at v1 |
|---|---|
| `KAM/SpinOrbit/Lock/Graph.lean` | `71e53cd713b81f13271ef007f8994b71cd812eb6360a77dd0beffb2bed4c7b29` |
| `KAM/SpinOrbit/Lock/Graph/Angle.lean` | `ebc30d1440bf96a64891097b9f2d1fea12c49e2f2e0f3ff3992504372bb881e6` |
| `KAM/SpinOrbit/Lock/Graph/Bridge.lean` | `1d6b38bfb82bcc9c679089293b04e4bb5cba45cb1ce82529fce93940538eafee` |
| `docs/tracks/SO/audits/LOCK-GRAPH-handoff.md` | `cd5a7bd2ea451fc0cdf7ded4dfa7335daf9ca8811e4333400a2bc4c10c209739` |
| `docs/tracks/SO/design/SO-LOCK-DESIGN.md` | `7785225bb6f3d3985ae7719f3aecf107eb33302530147bbff5672935eb170c6d` |
| `/root/code/KAM-inp/.drafts/design/SOLockSignatures.lean` | `aa544d085056410f205df49c08a778e854ad79ea48ad158fffe5302c3d0cd60d` |

The external signatures path is evidence only and was not edited. The theorem statement before
`:=` and the entire `LockGraphCert` structure match its §7 text byte-for-byte. A transient copy
of that exact theorem statement with body
`by exact lockBarrier_of_certV2 g hΩ hκ hham hlo hc hg hω hdio` elaborated, and
`example : type_of% @signed_copy := @lockBarrier_of_certV2` also elaborated.
No assertion of author-approved frozen status is inferred from the word “signed”.

Method: focused statement/proof audit with an adversarial second pass over the four requested
failure modes, then serialized validation. Imported coordinate/certifier theorems were checked
at their use sites and through axiom/kernel checks; this is not a fresh source audit of the
entire transitive mathematical library or of Celletti (1994).

## The four focus points

### (a) Invariance is produced, and the premises are accounted for

At v1 `Graph.lean:303–352`, the core extracts `Kinf` and `sinf` from `CertifiedTorus`, derives
strict monotonicity from `checkSoGraph_sound` and Cauchy transfer, and transfers the action bounds
with the stated `disp`. At `Graph.lean:79–264`, the exact-torus helper then:

1. Derives the unscaled invariance equation and exact clock, rather than assuming either.
2. Proves `hflow`, `hrflow`, and `hΦ` (`127–158`): the real torus solves the real Hamiltonian
   system, and its physical image solves `soField` by the chain rule and `lock_conjugacy`.
   All coordinate uses have `I > 0`; the trigonometric centre is proved C³ from C∞.
3. Constructs `P(a,φ) = realP Kinf (T.lockInv a (φ-c₀)) (φ-c₀)` (`198`), including continuity,
   both period-one laws, bounds and strict positive lower action.
4. Fills the actual invariant-set field (`227–264`). Starting with **any** solution `yy` on
   **any** order-connected time set `J`, and an initial graph point at `t₁`, it uses the
   polar inverse and `lockToPhysicalR_congr` to find a torus point with that physical image.
   The constructed curve `w(s)` is a `soField` solution at every real time.
   `gen_uniqueness isOpen_univ soField_contDiff.contDiffOn hJ ht₁ hy hsol hw0.symm ht`
   identifies `yy t` with `w t`; `hval` proves its graph membership.

The local `hS` in step 4 is membership at the initial time under the definition of
`IsInvariantSet` (`KAM/ODE/Exit.lean:107`); it is not an assumed invariance result.
`LockBarrier` is a result structure, not an input to any of the three barrier producers.
No local solution interval, global polar inverse, or continuity of principal `arg` is assumed.

The following tables give the five-bin premise classification. SOURCE means an explicit
parametric design premise; STANDING denotes backend laws or the established certificate
interface (with a producer specified), never an unpaid source theorem. TYPING is data formation.
There are no RULED repairs or EXCESS premises. The exact-torus and generic helpers have distinct
names and are internal conditional results; the signed export supplies their produced premises.

| Signed theorem binder | Bin | Evidence / meaning |
|---|---|---|
| `{α : Type}` | TYPING | Backend carrier, signed §7 |
| `[CertArith α]` | TYPING | Arithmetic operations/data, Interface.lean:30–46 |
| `[LawfulCertArith α]` | STANDING | Expand into the 12 laws in the next table |
| `g : LockGraphCert α` | TYPING | `graph`, `Ω`, `cs`, `κ` data; no proof fields |
| `hΩ` | SOURCE | Signed §7, positive polar parameter |
| `hκ` | SOURCE | Signed §7, positive time scale |
| `hham` | SOURCE | Signed §7, exact expression tie to κ·K |
| `hlo` | SOURCE | Signed §7, `0 < pLo - disp` |
| `{w : routeAV2.Wit}` | TYPING | Certificate witness data |
| `hc` | SOURCE | Signed §7, passing v2 check |
| `hg` | SOURCE | Signed §7, passing graph check |
| `{ωstar : Fin 2 → ℝ}` | TYPING | Exact reference frequency |
| `hω` | SOURCE | Signed §7, frequency-box membership |
| `hdio` | SOURCE | Signed §7, Diophantine premise at certificate γ,τ |

Expanded backend laws (each STANDING, `Arith/Interface.lean:49–70`):

| Law | Content |
|---|---|
| `val_ofInt` | Exact integer conversion |
| `ofRatUp_ge` | Rational upper conversion |
| `ofRatDown_le` | Rational lower conversion |
| `add_err` | Absolute addition error bound |
| `val_neg` | Exact negation |
| `mul_err` | Absolute multiplication error bound |
| `val_abs` | Exact absolute value |
| `upAdd_ge` | Upper addition |
| `upMul_ge` | Upper multiplication of nonnegative inputs |
| `ble_sound` | Sound non-strict comparison |
| `blt_sound` | Sound strict comparison |
| `beq_sound` | Sound equality comparison |

There are **12** laws in this checkout (the table is exhaustive). None mentions tori, barriers, dynamics or graph existence.
The signed theorem's expanded totals are SOURCE=8, STANDING=12, TYPING=5, RULED=0, EXCESS=0,
counting the law fields in place of the class binder.

| Generic-core binder | Bin | Producer / reason |
|---|---|---|
| `{α}`, `[CertArith α]`, `g`, `{ωstar}` | TYPING | Same data carriers as the signed theorem |
| `[LawfulCertArith α]` | STANDING | Same 12 laws, expanded above |
| `hΩ` | SOURCE | Same signed positivity premise |
| `hκ` | SOURCE | Same signed positivity premise |
| `hham` | SOURCE | Same exact Hamiltonian tie |
| `hlo` | SOURCE | Same positive widened lower action |
| `hs` | STANDING | Static conjunct of passing base check; supplied at Graph.lean:369 |
| `hnv` | STANDING | Domain safety from `checkHamBounds_sound hs ...`, Graph.lean:371 |
| `hg` | SOURCE | Same passing graph check |
| `hT` | STANDING | Exactly `CertifiedTorus`, proved by certifier soundness at Graph.lean:372 |
| `hdio` | SOURCE | Same reference-frequency premise |

`hnv` is an analytic domain-safety premise, not merely typing. Expanded recursively through
`HamExpr.NonvanishingOn` (`Expr/Basic.lean:76–86`), it requires denominator nonzero conditions
and positive real part of each sqrt operand, closed under the expression tree. It contains
no graph or physical invariance assertion. The signed theorem **proves** it internally; it
is not an extra signed theorem hypothesis. Likewise `hs` is the computational/static domain
interface. For the generic helper these are explicit, independently supplied interface premises.

`hT` expands literally as follows (`Certificate/Defs.lean:356–371`); each row is STANDING,
produced by `checkTorusCertificateV2_sound`, not a new assumption in the signed export:

| Expanded `CertifiedTorus` item | Role |
|---|---|
| `∃ Kinf` | Complex phase-valued torus witness |
| `∃ sinf` | Real frequency-scale witness |
| `1 < sinf` | Positive scale follows |
| `sinf < σω` | Upper scale bound (unused here) |
| `DifferentiableOn ℂ Kinf (complexStrip ... rhoInf)` | Holomorphy |
| `IsPrimaryOnStrip Kinf rhoInf` | Integer equivariance of angles and periodicity of actions |
| `IsRealOnReals Kinf` | Real phase points at real angles |
| `invarianceError c.H Kinf (sinf • ωstar) = 0` on strip | Certified Hamiltonian invariance, before transport |
| `c.H (Kinf θ) = E0` on strip | Energy identity (unused here) |
| `ball (Kinf θ) (μ/2) ⊆ c.D` on strip | Complex domain attachment |
| `‖DKinf θ‖ ≤ σK - μ/2` on strip | Derivative bound (unused here) |
| `‖Kinf θ - c.K θ‖ ≤ disp` on strip | Cauchy/value transfer |
| `‖sinf • ωstar - s • ωstar‖ ≤ disp` | Frequency closeness (unused here) |

The generic-core totals, before recursively expanding the two certificate-interface predicates,
are SOURCE=6, STANDING=15 (12 backend laws plus `hs`, `hnv`, `hT`), TYPING=4,
RULED=0, EXCESS=0. The table above spells out `hT`; `hnv` is the recursive expression-safety
predicate, not a hidden result bundle. `IsPrimaryOnStrip`, `IsRealOnReals`, `IsDiophantine`,
`invarianceError` and both real/complex Hamiltonian vector fields were read at their frozen
definitions: period one, ordinary Fin-function spaces, geometric strip, standard `(∂I,-∂θ)` sign.

### (b) Physical time uses the unscaled frequency

At `Graph.lean:99–113`, `invarianceError_const_mul` cancels κ using `hκ.ne'`.
The new frequency is `((κ : ℝ)⁻¹ * sinf) • ωstar`, exactly `(sinf/κ) • ωstar`, and the
Diophantine constant is also divided by κ. At `115–123`, `clock_frequency` is applied to the
**unscaled** Hamiltonian and equation, proving `(sinf/κ)*ωstar 1 = 1` and
`φ(θ)=θ₁+c₀`. Thus `ν=(sinf/κ)*ωstar 0`, and the physical solution is parametrized by
`(a+(t-t₁)*ν,b+(t-t₁))`. No residual κ multiplies `soField`.

Refutation attempt: retain the certificate frequency `sinf • ωstar` as physical frequency.
That would give clock derivative κ and would not match the equation supplied to
`clock_frequency`. The actual proof explicitly rescales both the invariance equation and
nonresonance before constructing any physical orbit, excluding design audit 2 finding 4.

### (c) Complex positivity and the argument branch

`Graph.lean:280–297` extracts safety of the **first X square root** from the complete
κ·K expression; its operand is `((1/Ω) I)/π`. Its real part is
`(((1/Ω : ℚ) : ℝ)/π) * Re I`, with a strictly positive prefactor by `hΩ`.
Consequently `NonvanishingOn c.D` gives `Re I > 0` on all of `c.D`, even if a coefficient
multiplying that subtree happens to vanish. This is syntactic safety, not nonvanishing of
the value of κ·K. At `328–330`, `μ>0` and `CertifiedTorus`'s ball inclusion place every
`Kinf θ` in `c.D` for every complex θ in the full certified strip. This proves `hKD` supplied
to the clock theorem. Merely having `I≥lo` at real angles is never used as its substitute.

For inversion, `LockAngle` has genuine positive derivative and degree-one periodicity.
Surjectivity is proved by integer bracketing and the intermediate value theorem; injectivity
by `graphAbs_sub_le` and `m>0`. Its chosen inverse is continuous and has the exact integer
shift laws (`Angle.lean:58–137`). No arbitrary/nonunique choice affects the result.

At `Bridge.lean:137–166`, strict `I>0` implies `s=√(I/π)>0`, and the physical complex coordinate
is proved equal to `s*(cos(2πα)+i*sin(2πα))`. The principal-argument theorem yields an integer
`k` with `arg(lockW)/2π = α-k`, including the endpoint convention on the argument cut.
`Graph.lean:199–203` proves `P(a-k,φ)=P(a,φ)`, and `214–217` uses precisely this equality.
No false real identity `arg(...)/(2π)=α`, or continuous principal argument, is used.
The inverse-surjectivity theorem used at `238` assumes positive `libAction`; that is supplied
by graph membership. The zero-radius singularity is excluded by the strict lower margin.

Adversarial checks of missing complex positivity, half-turn branch endpoints, arbitrary
integer winding, and zero polar radius all resolve by these explicit hypotheses/equalities;
no surviving mathematical finding was identified.

### (d) The core is engine-generic

`lockBarrier_of_certified` mentions neither `routeAV2`, its witness, its test nor its internal
constants. Its inputs are the common certificate output `CertifiedTorus`, static/domain safety,
and the graph/client premises. A fresh Lean probe quantified over arbitrary `E : EngineV2`
proved the same barrier conclusion from `checkTorusCertificateV2 E ... = true`:

```lean
have hc1 := hc
simp only [checkTorusCertificateV2, checkV2With, Bool.and_eq_true] at hc1
have hb : landedBase.check g.graph.base = true := hc1.1
have B := landedBase.sound hb hω
exact lockBarrier_of_certified g hΩ hκ hham hlo B.hs B.hH.1 hg
  (checkTorusCertificateV2_sound E hc hω hdio) hdio
```

The arbitrary-engine wrapper elaborated at default settings, exit 0. Therefore a future route
using this v2 interface needs only such a wrapper; no graph/clock/transport proof changes.
For a different base checker, its soundness must additionally supply the same `hs` and `hnv`
(e.g. through `BaseFacts`). **`CertifiedTorus` alone is not claimed to imply `hnv` or `hs`.**
This limitation is explicit and appropriate to the implemented interface.

## Declaration ledger

All names below are in `KAM.SpinOrbit.Lock`; `LockAngle.*` retains that nested namespace.
PASS rows mean statement and proof pass at this package's scope; they do not create frozen nodes.
Every named theorem in this table has exactly the three standard axioms reported below.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| LOCK-GRAPH / def | `lockRealPt` | PASS | Literal real-coordinate projection, all real x,y. |
| LOCK-GRAPH / theorem | `lockRealPt_eq` | PASS | Realness identifies the projection with the original complex point. |
| LOCK-GRAPH / theorem | `hasDerivAt_line_shift` | PASS | General normed real target; transports line derivative to arbitrary time. |
| LOCK-GRAPH / theorem | `lockBarrier_of_exact_torus` | PASS | Conditional exact-torus helper; produces the full physical invariant graph. |
| LOCK-GRAPH / structure | `LockGraphCert` | PASS | Exactly the four signed data fields, no proof premises. |
| LOCK-GRAPH / theorem | `re_action_pos_of_nonvanishingOn` | PASS | Positive Ω and X-radicand safety imply Re I>0 on the entire domain. |
| LOCK-GRAPH / theorem | `lockBarrier_of_certified` | PASS | Common certifier output and domain/static facts; no engine-specific premise. |
| LOCK-GRAPH / theorem | `lockBarrier_of_certV2` | PASS | Exact signed statement, all auxiliary obligations discharged internally. |
| LOCK-GRAPH / structure | `LockAngle` | PASS | Conditional monotone angle data; fully constructed in exact-torus proof. |
| LOCK-GRAPH / theorem | `sub_int_of_periodic` | PASS | All integer shifts from one-periodicity. |
| LOCK-GRAPH / theorem | `LockAngle.lockAngle_add_int` | PASS | Degree-one lift for every integer. |
| LOCK-GRAPH / theorem | `LockAngle.lockAngle_exists_inv` | PASS | Surjectivity by floor bracketing and IVT. |
| LOCK-GRAPH / theorem | `LockAngle.lockInv_unique` | PASS | Injectivity from a positive lower derivative. |
| LOCK-GRAPH / def | `LockAngle.lockInv` | PASS | Choice from proved existence; uniqueness proved before definition. |
| LOCK-GRAPH / theorem | `LockAngle.lockInv_spec` | PASS | Full right-inverse characterization. |
| LOCK-GRAPH / theorem | `LockAngle.lockInv_apply` | PASS | Left inverse and independence of chosen preimage. |
| LOCK-GRAPH / theorem | `LockAngle.continuous_lockInv` | PASS | Joint continuity, using uniform positive lower derivative. |
| LOCK-GRAPH / theorem | `LockAngle.lockInv_add_one` | PASS | Degree-one shift in the inverse angle. |
| LOCK-GRAPH / theorem | `LockAngle.lockInv_add_one_right` | PASS | Periodicity in clock angle. |
| LOCK-GRAPH / theorem | `LockAngle.lockInv_sub_int` | PASS | All integer winding corrections. |
| LOCK-GRAPH / def | `ofRealPt` | PASS | Literal coordinatewise real inclusion. |
| LOCK-GRAPH / theorem | `ofRealPt_add_smul` | PASS | Real-affine line identity. |
| LOCK-GRAPH / theorem | `fderiv_ofRealPt` | PASS | Conditional general bridge; requires genuine differentiability and local equality. |
| LOCK-GRAPH / theorem | `lockHamExpr_eval_ofRealPt` | PASS | Exact real Hamiltonian identity on I>0. |
| LOCK-GRAPH / theorem | `differentiableAt_lockHamExpr` | PASS | Holomorphy on Re I>0 with Ω>0. |
| LOCK-GRAPH / theorem | `fderiv_lockHamExpr_ofRealPt` | PASS | Produces bridge premises locally from I>0 and smooth centre. |
| LOCK-GRAPH / theorem | `hamiltonianVectorFieldℂ_lockHamExpr_ofRealPt` | PASS | Both coordinate directions and the negative action sign match. |
| LOCK-GRAPH / theorem | `lockToPhysicalR_congr` | PASS | Physical map ignores clock action; matches all other coordinates. |
| LOCK-GRAPH / theorem | `arg_lockW_lockToPhysicalR` | PASS | Angle modulo an integer, strictly positive radial factor. |

The exact-torus helper's logical inputs are positive Ω, κ, ρ, γ, m and lo; holomorphy,
primary equivariance, realness, κ·K invariance, full-strip positivity, Diophantine frequency,
real angle derivative bound, and real lower/upper action bounds. All are explicit and all are
supplied in the generic core. Its data binders are Kinf, seven real scalars, Ω, κ, cs and ωstar.
No hidden ambient Euclidean norm, altered strip convention, or widened dependence of constants
is introduced. The general line and derivative helpers deliberately prove conditional analytic
facts with distinct names; they are not substitutes for the signed result.

## Definition classification

| New definition / structure | Classification and whole-carrier check |
|---|---|
| `lockRealPt` | Literal projection of real parts, total at all Kinf,x,y; realness needed only in the separately proved equality. |
| `ofRealPt` | Literal inclusion, total on the complete real phase space. |
| `LockAngle` | Internal Prop structure: positive m, joint continuity, two lift/period laws, derivative identity, derivative lower bound. These conditions are proved for the actual torus in Graph.lean:172–188. |
| `LockAngle.lockInv` | Classical choice from proved global surjectivity, with injectivity already proved; `lockInv_spec` and `lockInv_apply` characterize it uniquely on all a,y. No fallback/default branch and no deferred uniqueness. |
| `LockGraphCert` | Literal signed data structure, exactly graph/Ω/cs/κ. |

For both literal functions and `LockGraphCert`: BODY_MATCH=OK, PUBLIC_CARRIER=OK,
WELL_DEFINEDNESS=N/A_LITERAL, CHARACTERIZATION=N/A_LITERAL, CHOICE_INDEPENDENCE=N/A,
DEFINITION_VERDICT=PASS. For `LockAngle`, the same applies as an internal literal predicate.
For `lockInv`: BODY_MATCH=OK, PUBLIC_CARRIER=OK, WELL_DEFINEDNESS=OK,
CHARACTERIZATION=OK, CHOICE_INDEPENDENCE=OK, DEFINITION_VERDICT=PASS at the unfrozen helper scope.
This does not purport to manifest or freeze its characterization. No `abbrev` was added.

## Independent validation

All Lean/Lake/checker activity was sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`;
the targeted build used the prescribed compile gate. No clean/update/cache fetch or library
rebuild was requested. Commands below ran in `/root/code/KAM-inp-lockgraph`.

1. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-lockgraph KAM.SpinOrbit.Lock.Graph`

   Exit 0. Gate acquired slot 1; final output: `Build completed successfully (3546 jobs).`
   Replayed upstream linter/deprecation warnings were present; none was in the three new files.

2. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Lock.Graph KAM.SpinOrbit.Lock.Graph.Angle KAM.SpinOrbit.Lock.Graph.Bridge`

   Exit 0. Exact output:

   ```text
   replaying KAM.SpinOrbit.Lock.Graph
   replaying KAM.SpinOrbit.Lock.Graph.Bridge
   replaying KAM.SpinOrbit.Lock.Graph.Angle
   ```

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/LOCK-GRAPH-audit.lean`

   Final exit 0. Probe contained the exact signed-statement copy/application and `type_of%`
   equality above, the arbitrary-EngineV2 composition wrapper, and `#print axioms` for all
   **24** new public theorems (every theorem row of the ledger). Every result printed:
   `depends on axioms: [propext, Classical.choice, Quot.sound]`.
   No `sorryAx` or project axiom. The multiline display for the complex-vector-field bridge
   has the same three names. Initial probe run exited 1 because the auditor tried the
   unsupported syntax `Bool.and_eq_true.mp`; replacing that scratch-only extraction by
   `simp only [...] at hc1; ... hc1.1` gave the successful arbitrary-engine test above.
   This was a probe-authoring error; no package code was changed.

4. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`

   Exit 1 solely for the permitted generated-root exception. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/SpinOrbit.lean)
   check_lean_modules: PASS (1685 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (158 frozen declarations)
   ```

5. `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-lockgraph KAM.SpinOrbit.Lock.Graph KAM.SpinOrbit.Lock.Graph.Angle KAM.SpinOrbit.Lock.Graph.Bridge`

   Exit 0: `short-name check OK (no reused public short name)`.

6. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md`

   Empty, exit 0. `git diff --check inp...HEAD`: empty, exit 0.
   Source sizes are 375, 142 and 166 lines. All three have copyright/module/public imports,
   module docstrings, an exposed public noncomputable section and Fin-function ambient spaces.
   Forbidden-token/resource-override scans have no new-code matches.
   A recursive KAM import scan found 296 modules, no provider imports and 24 manifested frozen
   definitions, all `SEALED`; no DRAFT_SORRY theorem is imported. Standard-axiom closure of all
   new theorems independently corroborates absence of a hidden frozen proof hole.

Scratch probes/logs were removed after their evidence was incorporated into this report.

## Notes, source defects and limits

**N1 — generated root:** the root-generation warning is the exact exception permitted by the
brief. `KAM.lean` and `KAM/Root/*` were left untouched under AGENTS rule 10.

**N2 — design omission, supplied in code:** SO-LOCK-DESIGN §3 describes
“the clock component of the unscaled frequency is exactly 1” (v1:313), but does not spell out
how the *whole complex torus strip* reaches the clock derivative's analytic domain. The code
supplies this through the certified ball inclusion and the X-radicand safety predicate.
No missing premise remains in the signed theorem. The suggested documentation clarification
is to record that chain, not to change any theorem statement. This is a design-exposition
omission, not a suspected defect in a pinned published mathematical source.

**N3 — scope of future routes:** a route with the common v2 base checks can use the tested
wrapper. An arbitrary certifier exporting only `CertifiedTorus` must also expose static/domain
safety, as the core's type visibly requires. No claim about an unimplemented future numerical
route or its success threshold is certified here.

No surviving mathematical blocker, unauthorized premise, weakened signed conclusion or
meaning-changing definition was found. There are no new suspected pinned-source errata or
implementation deviations. The limited duplication of inverse-angle infrastructure is a
maintenance note only. No owner decision or implementation repair was made during the audit.

Closeout: all 29 explicit new public declarations classified; all 24 theorem axiom checks,
exact signed statement application, arbitrary-engine composition, targeted build and kernel
replay passed; protected-path diff empty. Lint's generated-root exception is recorded above.
The package is ready for integration review within this unfrozen scope.
