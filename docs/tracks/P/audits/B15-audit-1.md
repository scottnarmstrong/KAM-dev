# B15 independent package audit 1

**Overall verdict: PASS WITH NOTES.** The complete B15 limit-map slice passes exact signatures, source fidelity, definition review, all 29 public-theorem axiom checks, targeted build and kernel replay. Notes are the explicitly permitted stale generated root and the inherited `KAM.lean` difference in the requested full-history comparison. No B15 mathematical or hygiene blocker was found.

| Source-facing result / anchor | Verdict | Scope |
|---|---|---|
| `KAM.Planetary.limit_map` / `bpP:p11a:limit-map` | PASS WITH NOTES | Exact signed B15 infrastructure theorem; implementation proof passes, generated-root notes below |
| `sec_limit_data`, `selectionEvaluation` | PASS | Exact signed literal definitions |
| Planetary frozen headline anchors | N/A | No B15 provider or seal; this audit does not promote a frozen anchor |

Audit date: 2026-10-28 (UTC). Scope: only `KAM/Planetary/WeakKAM/Limit*.lean`, as required by the handoff. This is a package proof audit, not a new audit or seal of a planetary headline anchor.

## Snapshot and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, `docs/tracks/P/audits/B15-handoff.md`, the B15 row and full relevant node/consumer contracts in `docs/tracks/P/design/P11B-LEAN-DESIGN.md`, both P11B design audits, canonical `P11BSignatures.lean`, track-P statement conventions, frozen `Phase`, `complexStrip` and `actionNbhd`, and the blueprint selection-data and limit-family statements/proofs. Applied the lean-statement-audit method. The explicit user path overrides the common brief's conflicting MAIN-worktree destination.

HEAD is `7042a93113c7bbf885cace84f7804d2795e6c929`; comparison branch `inp` is `ce5bc0c09a78b36777a59cdb8b93c5e544d380e6`. `git diff inp...HEAD` reports multiple merge bases and chooses `c8772e9761f9b01c04ae490d5a35975ebc95ca61`; the other merge base is `2d009059bbfb14a40c7d98e3f65765e3a6a9bc5b`. The requested three-dot diff has 44 files, 6083 insertions and 139 deletions. The mathematical review is confined to the three B15 files; the other paths are inherited scope/context, not newly certified here. Relative to the B14 merge `3c1a88ae`, exactly these three files change (583 added lines).

| Input | SHA256 |
|---|---|
| `Limit.lean` | `c68ef71a166f6fdb55cceccdcdeb167cfb1395b1a2bf2dad90ed95eb6f2f9bb5` |
| `LimitProps.lean` | `53eca09622ddfcdb81f32ccd6ceceda499ab009c90f6dd6e001212676fae491f` |
| `LimitSeries.lean` | `e4b6271db00fb17ba64943d7ac1f55e2cd511b4a130e464ff57bb5f4e872dff2` |
| `P11BSignatures.lean` | `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63` |
| `P11B-LEAN-DESIGN.md` | `b39ec4a5b9b976b355d6afe26047680ea2b1fbb1c86dd4073aa4428528961ea1` |
| `p11a4-limit-family.tex` | `c88030106491131ffde29078d1f0919ae092592bf37e1bbc68a87ab087369b2b` |

## Exact signed surface and graph coverage

Mechanical declaration extraction compares the two definition bodies, the entire `SelectionLimit` structure, and `limit_map`'s full header with the canonical signatures (comments around declarations excluded). All four are **exactly equal**, without binder or field normalization. The signature file remains design evidence; its proof holes were never imported. B15 has no provider export and no frozen theorem to seal; provider-to-frozen seal tests are therefore N/A. Instead the transient probe copies the signed `limit_map` header under a fresh name, applies `limit_map d ε he hsmall f hf`, and checks the full polymorphic types in both directions. Definition equations are checked by `rfl`.

| Design node | Implementation evidence | Verdict |
|---|---|---|
| `bpP:p11a:limit-map` | `Limit.lean:33–59,152–188`; all record fields constructed; signed raw-input `limit_map` | PASS |
| `stepP:p11a:lm-inc` | `LimitSeries.lean:76–135,158–171`; zero section in every domain; summable increments and uniform convergence | PASS |
| `stepP:p11a:lm-der` | `LimitSeries.lean:137–155,173–205`; fixed s/2 to s/4 Cauchy loss, derivative telescoping and uniform convergence | PASS |
| `stepP:p11a:lm-hol` | `LimitSeries.lean:208–218`; `KAM.uniform_limits` only after value and derivative convergence; reality in `Limit.lean:67–102` | PASS |
| `stepP:p11a:lm-bounds` | `LimitProps.lean:51–160`; `Limit.lean:104–146`; equivariance, separate sums, derivative bound and Lipschitz defect | PASS |
| `bpP:p11a:sec-limit#data` | `Limit.lean:27–30`; original-coordinate evaluation adds b in the action block; defect_spec identifies the translated zero-section map | PASS |

These are all six B15 node-table rows (design:128–133). Unsigned helpers have distinct implementation names; none masquerades as an unpaid source node. No graph edits were made.

The source's derivative proof at `p11a4-limit-family.tex:112` bounds coordinate derivatives and then pays a factor N for row sums. `selectionLim_dinc_bound` proves the stronger dimension-free operator bound using the already-proved Banach-valued complex-line Cauchy theorem (`KAM/Strip/Cauchy.lean`, `norm_fderiv_le_of_closedBall_bound`, `norm_fderiv_le_of_mem_complexStrip`). That theorem tests every unit direction in the actual Pi norm. This is a valid stronger route, with no Euclidean norm substitution or missing N factor. The final 2^-11 bound is independently inherited by restricting the full composition derivative defect along isometric inl; it is not obtained by summing that coarser Cauchy envelope.

Consumer check: B16 needs holomorphy, reality, the exact same finite-chain value/derivative limits, and bounds; all are fields of the unchanged `SelectionLimit`. B17 needs separate A/alpha displacement bounds. B18 needs angle Lipschitz and the telescoping increments: the record's uniform convergence, its inherited composition, and the public finite telescoping identity provide these. The blueprint `lf-tel` at lines 201–205 follows the same sequence. No consumer contract requires an off-section positive action radius or a limiting full phase Jacobian. Later consumer modules are absent from this checkout, so this certifies their signed input contracts, not their future proofs.

## Expanded input-binder audit

For the source-facing `limit_map`, the counts below cover each outer binder and every immediate field of its input bundles. TYPING includes scalar/function data; STANDING fields are the source's explicit standing selection assumptions, not iteration outputs. RULED=0 and EXCESS=0. Source locators are `p11a3-iteration-selection.tex:32–40` (`sel-data`) and `p11a4-limit-family.tex:25–50,100–108` (adapted-radius situation and limit map).

| Binder / expanded field | Bin | Source |
|---|---|---|
| implicit `n : ℕ` | TYPING | Number of angles/actions, sel-data(a) |
| `d : SelectionData n` | TYPING | Bundled scalar/geometric standing data; expanded below |
| `d.μ` | TYPING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.ρ` | TYPING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.τ` | TYPING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.ϑ` | TYPING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.strip` | TYPING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.C₁` | TYPING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.β` | TYPING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.M` | TYPING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.loss` | TYPING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.K` | TYPING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.h` | TYPING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.n_pos` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.μ_pos` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.rho_mem` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.tau_nonneg` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.tau_gap` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.compact` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.positive_measure` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.theta_pos` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.theta_le` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.strip_pos` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.strip_le` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.hessian_normalized` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.beta_pos` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.beta_le` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.loss_pos` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.loss_lt` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.holo` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.real` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.hessian` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.finite_type` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `d.top_bounds` | STANDING | sel-data(a)–(d), literal field in `Data.lean:64–102` |
| `ε : ℝ` | TYPING | Perturbation size in adapted-radius situation |
| `he : 0 < ε` | SOURCE | Strictly positive ε for the adapted radius |
| `hsmall : ε ≤ selectionAdmissible d` | SOURCE | Explicit admissible threshold |
| `f : SelectionPhaseC n → ℂ` | TYPING | Perturbing Hamiltonian on the specified domain |
| `hf : SelectionPerturbation d f ε` | TYPING | Bundle expanded in the following four rows |
| `hf.holo` | SOURCE | sel-data(c), holomorphic on strip × action collar |
| `hf.periodic` | SOURCE | sel-data(c), period one in angles |
| `hf.real` | SOURCE | sel-data(c), real on real phase points in the domain |
| `hf.bound` | SOURCE | sel-data(c), pointwise norm ≤ ε on the full domain |

Counts including the two bundle wrapper rows: TYPING=16, STANDING=21, SOURCE=6, RULED=0, EXCESS=0. The wrapper rows carry no additional logical condition.

The internal estimates are deliberately conditional helpers. Their shared inputs are `{d,f,a}` (typing/standing data), `cx : WeakBudgetCtx d a` (proved scalar budget package), `c : SelectionComposition d f a` (proved B14 composition output), `hb : b ∈ c.Kinf`, and the indicated angle-strip/stage/translation inputs. The latter are exactly the local source proof's domain premises; `θ,θ',ν,j,k,v,i,b` are typing data. The pure identities drop unnecessary context automatically, or explicitly with `omit cx`. No helper's input asserts its own limit, uniform convergence, limiting derivative, or Lipschitz conclusion.

The conditional `cx`/`c` inputs are not counted as raw source premises: they are internal produced dependencies, with a distinct assembly name `selectionLimit_of_composition`. The public `limit_map` constructs them using `free_radius`, `parameter_selection_adapted`, `weakBudgetCtx_of` and `selectionComposition_of_output`, then calls the assembly. `SelectionLimit` is output packaging, never an input to its own construction. The proof computes ε₀=2ε>0, keeps s₀=√(2ε/(n C₁)), and supplies the budget equalities by reflexivity. This rules out hidden conclusion-shaped assumptions at the source-facing boundary.

## Every explicit public declaration

All names below are in `KAM.Planetary`. Generated structure projections are covered by the exact whole-structure comparison and the constructed record fields.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| sec-limit data | `selectionEvaluation` (`Limit.lean:27`) | PASS | SIGNED literal original-coordinate evaluation `(θ,b)+u b θ`; exact body. |
| sec-limit data | `sec_limit_data` (`Limit.lean:30`) | PASS | SIGNED literal alias of selectionEvaluation; exact body. |
| limit-map | `SelectionLimit` (`Limit.lean:33`) | PASS | SIGNED output record; all fields exact, including inherited composition witnesses. |
| lm-* implementation | `selectionLim_real_im` (`Limit.lean:67`) | PASS | Reality of every finite composition passes componentwise to limit. |
| lm-* implementation | `selectionLim_defect_spec` (`Limit.lean:94`) | PASS | Exact real reconstruction of the zero-section limit; no reality assumed. |
| lm-* implementation | `selectionLim_defect_periodic` (`Limit.lean:104`) | PASS | Integer equivariance cancels the real identity defect. |
| lm-* implementation | `selectionLim_defect_lipschitz` (`Limit.lean:118`) | PASS | Convex-strip mean value bound for limit minus inl, then real isometry. |
| limit-map | `selectionLimit_of_composition` (`Limit.lean:152`) | PASS | Distinct conditional assembly; fills every new field and preserves input c. |
| limit-map | `limit_map` (`Limit.lean:179`) | PASS | SIGNED raw-input construction; all explicit binders supplied in order by probe. |
| lm-* implementation | `selectionLimDefect` (`LimitProps.lean:29`) | PASS | Real-part projection minus the real zero section; characterized by defect_spec. |
| lm-* implementation | `selectionReal_mem_complexStrip` (`LimitProps.lean:33`) | PASS | Real points belong to every positive-width strip. |
| lm-* implementation | `selectionLim_sub_mem` (`LimitProps.lean:42`) | PASS | Positive strip width gives s/4 ⊂ s/2. |
| lm-* implementation | `selectionLim_tendsto` (`LimitProps.lean:45`) | PASS | Pointwise specialization of uniform convergence. |
| lm-* implementation | `selectionLim_equivariant` (`LimitProps.lean:51`) | PASS | lm-bounds; translates remain in strip; uniqueness of limits preserves winding. |
| lm-* implementation | `selectionLim_angle_bound` (`LimitProps.lean:70`) | PASS | lm-bounds; continuous angle projection and summable nonnegative partial sums. |
| lm-* implementation | `selectionLim_action_bound` (`LimitProps.lean:82`) | PASS | lm-bounds; continuous action projection and summable nonnegative partial sums. |
| lm-* implementation | `selectionLim_fiber_diffAt` (`LimitProps.lean:97`) | PASS | Joint composition holomorphy restricts at the fixed parameter. |
| lm-* implementation | `norm_inl_apply` (`LimitProps.lean:109`) | PASS | Max product norm makes inl isometric; unique public short name in KAM. |
| lm-* implementation | `selectionLim_stage_fderiv` (`LimitProps.lean:113`) | PASS | Chain rule identifies the first N columns via composition with inl. |
| lm-* implementation | `selectionLim_derivative_bound` (`LimitProps.lean:123`) | PASS | lm-bounds; restrict full derivative defect to inl, then pass bound 2^-11 to limit. |
| lm-* implementation | `selectionLimStage` (`LimitSeries.lean:30`) | PASS | Literal zero-section composition of the same chain at the same parameter. |
| lm-* implementation | `selectionLimInc` (`LimitSeries.lean:35`) | PASS | Literal difference of adjacent stages. |
| lm-* implementation | `selectionLimDInc` (`LimitSeries.lean:40`) | PASS | Literal difference of adjacent complex Fréchet derivatives. |
| lm-* implementation | `selectionLimMap` (`LimitSeries.lean:45`) | PASS | Literal identity inclusion plus the increment series; convergence proved on the source locus. |
| lm-* implementation | `selectionLimDMap` (`LimitSeries.lean:50`) | PASS | Literal inclusion derivative plus derivative-increment series. |
| lm-* implementation | `selectionLimBound` (`LimitSeries.lean:55`) | PASS | Literal nonnegative stage envelope, (1+2^-11) max(A,alpha). |
| lm-* implementation | `selectionLimStage_zero` (`LimitSeries.lean:58`) | PASS | Definitional initial stage, no premises. |
| lm-* implementation | `selectionLimStage_eq_sum` (`LimitSeries.lean:61`) | PASS | Exact finite telescoping identity, any chain and parameter. |
| lm-* implementation | `selectionLim_mem` (`LimitSeries.lean:76`) | PASS | Retained parameter lies in every finite K; positive collars and action radii; iter_strip. |
| lm-* implementation | `selectionLim_diffOn` (`LimitSeries.lean:90`) | PASS | Composition holomorphy restricted to the zero-section fibre on s/2. |
| lm-* implementation | `selectionLim_diffAt` (`LimitSeries.lean:102`) | PASS | Open-strip specialization of diffOn. |
| lm-* implementation | `selectionLim_inc_bound` (`LimitSeries.lean:108`) | PASS | lm-inc; exact composition_increment bound on the larger strip s/2. |
| lm-* implementation | `selectionLim_bound_nonneg` (`LimitSeries.lean:116`) | PASS | Envelope nonnegativity from the scalar budget. |
| lm-* implementation | `selectionLim_bound_summable` (`LimitSeries.lean:122`) | PASS | max(A,alpha) ≤ A+alpha; consumes wbud_sums_Aα. |
| lm-* implementation | `selectionLim_dinc_bound` (`LimitSeries.lean:137`) | PASS | lm-der; operator Cauchy bound envelope/(s/4), stronger than coordinate N-factor bound. |
| lm-* implementation | `selectionLim_unif` (`LimitSeries.lean:158`) | PASS | lm-inc; uniform convergence of telescoping value series on s/4. |
| lm-* implementation | `selectionLim_stage_deriv_eq` (`LimitSeries.lean:173`) | PASS | Exact finite derivative telescoping, base derivative is inl. |
| lm-* implementation | `selectionLim_dunif` (`LimitSeries.lean:192`) | PASS | lm-der; summable derivative envelopes give uniform convergence on s/4. |
| lm-* implementation | `selectionLim_holo` (`LimitSeries.lean:208`) | PASS | lm-hol; fixed open strip and independently proved uniform derivative convergence. |

## Definition classification

There are nine explicit definitions and one output structure; no new abbrev, instance, or choice-defined object.

- `selectionLimStage`, `selectionLimInc`, `selectionLimDInc`: literal finite composition, value difference and derivative difference on their whole Lean carriers. `fderiv` has its standard total Lean meaning; differentiability is proved at every point where a derivative estimate is used.
- `selectionLimMap`, `selectionLimDMap`: literal sums of their named increment series, with initial value/inclusion derivative. These are implementation formulas on arbitrary raw chains, not assertions of convergence for arbitrary chains or outside the strip. Standard `tsum` totalization is never used to prove a source property: summability of norm envelopes and uniform convergence are proved first on every claimed retained-parameter/strip point. The source-facing record restricts all analytic claims to that exact locus. No custom zero/default branch occurs, and no off-source analytic claim is exported.
- `selectionLimBound`: literal numerical envelope, with nonnegativity and summability proved from the budget.
- `selectionLimDefect`: literal real-part projection minus identity. `selectionLim_real_im` and `selectionLim_defect_spec` prove its exact real reconstruction on the source locus; a spurious imaginary component is not silently discarded.
- `selectionEvaluation`: literal `(θ,b)+u b θ` for every u,b,θ. `sec_limit_data`: literal alias, no added predicate or hypothesis.
- `SelectionLimit`: exact signed output structure extending the same composition/selection/iteration witnesses. Every added field is populated, including equality between the actual limit derivative and the derivative series. No output field is repurposed as an input assumption of `limit_map`.

For each literal definition: BODY_MATCH=OK; PUBLIC_CARRIER=OK (literal implementation formulas, source properties restricted as explicitly typed); WELL_DEFINEDNESS=N/A_LITERAL; CHARACTERIZATION=N/A_LITERAL (the real reconstruction is additionally proved); CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS. For the output structure: BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=OK by the assembled inhabitant; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS.

## Static hygiene and protected paths

The three files have 193/166/224 physical lines, maximum line lengths 99/96/99 respectively (`Limit`, `LimitProps`, `LimitSeries`); all are below 1500 and 100. Each has copyright, `module`, public imports, module docstring and `@[expose] public noncomputable section`. All declarations remain in `KAM.Planetary`; no root declaration or harmful shadow is introduced. An anchored declaration-name scan over KAM finds exactly one occurrence of every new explicit short name, including `norm_inl_apply` and `selectionReal_mem_complexStrip`.

The forbidden-token scan of the audited files returns no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option`. The recursively traversed 161 project-module import closure contains no provider and no frozen theorem module at all, so neither a DRAFT_SORRY import nor an unquarantined provider is used. Frozen definitions are the actual imported definitions, not copies. No trust exception is required.

`git diff --check inp...HEAD`: exit 0, no whitespace errors (only the multiple-merge-base warning). `git diff inp...HEAD -- KAM/Frozen manifest README.md`: empty. The common brief's larger protected-path command is **not empty**: `KAM.lean` contains 34 inherited added imports for PlanarTorsion and WeakKAM iteration. These changes predate the B15-only delta. `git diff 3c1a88ae..HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty. This inherited generated-root difference is recorded as a note, not misreported as an empty full-history check; no protected file was edited by this auditor.

## Independent executable checks

Results of the serialized runs follow. All Lean/Lake/checker commands use `LEAN_NUM_THREADS=1` and `nice -n 5`. The build uses the mandated compile gate. No concurrent Lean/Lake/checker invocation was launched by this audit. No clean/update/cache fetch or generated-root rewrite was performed.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b15 KAM.Planetary.WeakKAM.Limit
```

Exit **0**. Relevant output:

```text
[inp-gate] slot 3 acquired 23:37:39 for KAM.Planetary.WeakKAM.Limit
Build completed successfully (9207 jobs).
```

The wait before slot acquisition was expected. Lake replayed upstream unused-variable/simp and deprecation warnings in existing dependency modules (including Schedule, CutoffTensor, CutoffScale, Cutoff, Nekhoroshev averaging, MaximalStep and IterationParam); these are not B15 proof failures. No B15 warning or design signal was observed. The shared build overlay was reused.

### Exact type/body probe and all public theorem axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B15Audit.lean
```

Exit **0**, with no elaboration errors or warnings. The reproducible probe consists of the `Limit` import, standard source opens, namespace `KAM.Planetary`, `{n : ℕ}`, these commands, and `#print axioms KAM.Planetary.<name>` for each of the 29 theorem rows in the declaration table:

```lean
example (u : SelectionR n → SelectionR n → Phase n) (b θ : SelectionR n) :
    selectionEvaluation u b θ = (θ,b) + u b θ := rfl
example (u : SelectionR n → SelectionR n → Phase n) :
    sec_limit_data u = selectionEvaluation u := rfl
theorem b15AuditSignedLimitMap (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) :
    Nonempty (SelectionLimit d f (selectionAdapted d ε)) := by
  exact limit_map d ε he hsmall f hf
example : type_of% @b15AuditSignedLimitMap := @limit_map
example : type_of% @limit_map := @b15AuditSignedLimitMap
```

Complete axiom output (including the copied signature theorem):

```text
'KAM.Planetary.selectionLim_real_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_defect_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_defect_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_defect_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLimit_of_composition' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limit_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionReal_mem_complexStrip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_angle_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_action_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_fiber_diffAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_inl_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_stage_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_derivative_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLimStage_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLimStage_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_diffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_diffAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_inc_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_bound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_bound_summable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_dinc_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_unif' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_stage_deriv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_dunif' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionLim_holo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.b15AuditSignedLimitMap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 29 public theorems and the independent signature-copy assembly have exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or project axiom occurs.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Limit KAM.Planetary.WeakKAM.LimitProps KAM.Planetary.WeakKAM.LimitSeries
```

One invocation, exit **0**. Complete output:

```text
replaying KAM.Planetary.WeakKAM.LimitSeries
replaying KAM.Planetary.WeakKAM.LimitProps
replaying KAM.Planetary.WeakKAM.Limit
```

### Repository lint, frozen-anchor guard and ABI

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1100 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole reported failure is the stale generated root, explicitly allowed by the common audit brief and handoff. Module checks, frozen-anchor guard, and all 144 elaborated frozen-declaration ABI hashes pass. No forbidden-token, oversize-file, overlong-line, errata-generation or module-format failure is reported. `KAM.lean` was not regenerated.

## Findings, uncertainties, errata and closeout

- **N1 — permitted generated-root lint exception.** The current root omits B15 and other newly available imports. The orchestrator owns regeneration; the exact stale-root output is preserved above.
- **N2 — inherited protected-path history.** The literal `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` check is nonempty because of inherited `KAM.lean` changes, not B15 edits. Both frozen/manifest preservation and the empty B15-only protected-path delta were independently checked. The multiple-merge-base warning is retained in the snapshot, so the selected comparison base is reproducible.
- **No new suspected pinned-source or blueprint defect.** In particular the stronger operator Cauchy estimate is a valid proof improvement, not a false blueprint claim or changed norm. No source deviation was introduced. The design-audit-1 F1/F2 findings concern earlier design interfaces and were resolved by design audit 2; neither is a B15 limit-map defect. The design's separate upstream and later-consumer gates are not certified merely by this package pass.
- **No theorem closure beyond this slice.** This establishes the exact B15 infrastructure exports and all six mapped graph obligations. It does not establish the invariant-torus dynamics, displacement powers, parameter-family bilipschitz/measure theorem, or any new frozen planetary seal.

Only `/root/code/KAM-inp-p11b-b15/docs/tracks/P/audits/B15-audit-1.md` is a new audit deliverable. `B15-handoff.md` was already untracked on entry and was preserved. All auditor-created probe/data/log files under `.lake/abi-scratch/` were deleted after their outputs were incorporated. No state-changing git command, production Lean edit, frozen edit, manifest edit, generated-file edit or build-cache/package mutation was performed by the auditor (apart from normal targeted build outputs). Final module/signature/design hashes still match the snapshot; the report declaration ledger covers all 39/39 explicit declarations, its code fences are balanced, and `git diff --check` passes.
