# B4-TCHECK independent audit 1

**Verdict: PASS WITH NOTES.** The one-generator torus Bool checker is sound and matches its assigned contract. No missing, weakened, or mis-indexed premise was found. Notes N1–N3 below concern documentation and scope, not proof validity. No frozen anchor is proved or sealed by this package: Track B is ordinary-theorem infrastructure under OD-B11/OD-B12.

Audited 2026-11-03 in `/root/code/KAM-inp-b4tcheck`. HEAD `e405b015ed10c666adf6a223d3cf8e1b35e98855`; comparison ref `inp` resolved to `8f9a0aea60b4c4d72761dae0528d80077897a6e0`. Assigned implementation commit: `5bf6bd3b3f14e57cf2a77944b40c24c922e6aeb3`. `TorusCheck.lean` SHA256: `3aa5c518d0362df9747aa0dd5bec1e7c783430242a38ff59a07b10e748e05fb1`.

## Authority and scope

Read AGENTS.md, PLAN.md, DECISIONS.md, the package-audit brief, B4-TCHECK handoff and AUDIT FOCUS, B4-TCHECK/common prover briefs, B SPEC/FREEZE-PROPOSAL/OWNER-DECISIONS, the OscillatorCheck template, and the TorusStep source chain. The explicit user path overrides the generic audit brief's main-worktree destination. Only this report is a repository edit; probes were confined to `.lake/abi-scratch/` and removed.

`git diff inp...HEAD` contains seven added files (785 lines): TorusCheck; inherited TorusStep, Drift, Remainder and Smoke; and the two handoffs. Commit `5bf6bd3b3` itself adds only the 176-line TorusCheck file. All five Lean modules were inspected and kernel-replayed. The declaration rows below distinguish the assigned checker from the inherited supplier. This is not a fresh audit of every earlier transitive analytic theorem.

There is no assigned I/N/P frozen export or Track B frozen anchor, no B blueprint directory or `docs/tracks/B/statement.md`. The controlling exact statement is the package brief plus `torusStep_confinement`, with SPEC and the proposed B1-T as the downstream contract. Provider/frozen type-equality and seal-body probes are therefore inapplicable. Instead an independent probe specialized the conclusion directly from TorusStep and elaborated `checkTorusStep_sound c hc w₀ hw₀` against it.

## Assigned declarations

All names in this and subsequent tables are in `KAM.EffectiveStability`.

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| B4-TCHECK data | `TorusStepCert` | PASS WITH NOTES | Exactly the requested data fields; no Prop, function witness, instance or trajectory field. N1 concerns field comments. |
| B4-TCHECK majorant | `TorusStepCert.torusBmaj` | PASS | Exact `ftSupBound (ftAdPow χ L H) πub lam (replicate n ρ)`. |
| B4-TCHECK checker | `checkTorusStep` | PASS | Total computable conjunction, 18 global checks and 8 checks for each index below n. |
| B4-TCHECK soundness | `checkTorusStep_sound` | PASS | Only proof hypotheses are acceptance and the initial box; exact full specialized supplier conclusion. |
| B4-TCHECK smoke data | `torusSmokeCert` | PASS | Requested integrable n=1 certificate, all literals match the handoff. |
| B4-TCHECK acceptance | `torusSmokeCert_check` | PASS | `by decide +kernel`; independently re-elaborated. |
| B4-TCHECK smoke consequence | `torusSmokeCert_zeroDrift` | PASS | Correct existential zero-drift projection from soundness. It intentionally does not restate every flow clause. |

## Premise-by-premise comparison

Write `ρl = List.replicate n c.ρ`, `bl = c.b`, and interpret `a,b,η,r` by `getD i 0` cast to ℝ. Every scalar certificate parameter is interpreted by its rational cast, with `πub,lam` already rational in the supplier.

| Supplier premise | Checker evidence / proof bridge | Verdict |
|---|---|---|
| `hH,hχ,hP` | Three `ftFitsCheck n` checks, passed through `ftFits_of_check`. | PASS |
| `hA` | `ftActOnly c.Nact`. | PASS |
| `hL,hid` | `1 ≤ c.L`; exact `ftEqCheck (ftLieSum χ H L) (ftAdd Nact P)`. | PASS |
| `hσ',hρ',hδc,hε0,hε` | `0<σ'`, `0<ρ'`, `0<δc`, `0≤ε`, `ε≤1/2`, in ℚ. | PASS |
| `hπ` | Stronger decidable check `ftPiUB≤πub`; `pi_le_ftPiUB.trans (Rat.cast_le.2 hπ)`. | PASS |
| `hx,hlam` | Exact rational `2*πub*σ<1`, `1/(1-2*πub*σ)≤lam`, cast to ℝ. No logarithmic or exponential approximation. | PASS |
| `ρl,hρl` | Replicated radius list; `i.2` establishes in-range lookup, so all coordinates equal ρ. | PASS |
| `hJ,hφ` | Per-index bounds for `ftDJ i χ` by `ε*σ'`, and `ftDφ i χ` by `ε*ρ'`, using the same πub, lam, ρl. | PASS |
| `hεb,hT` | `0<εb`, `0≤T`. | PASS |
| `bl,hbl` | Uses exactly `c.b`; equality to the interpreted b is reflexive. | PASS |
| `hbr` | `b_i≤r_i`. | PASS |
| `hσσ',hdom1` | `σ'<σ`; `b_i+εb+ρ'≤ρ`. | PASS |
| `hσc,hr3` | `δc+σ'/2<σ`; `r_i+δc+ρ'/2<ρ`. | PASS |
| `hη` | `0≤η_i`. | PASS |
| `hdrift` | `ftAngleDriftBound P i πub c.b + torusBmaj/(L! * δc) ≤ η_i`. `Rat.cast_le`, rational division/natural factorial casts, and unfolding `torusBmaj` produce the exact real inequality. | PASS |
| `hmargin` | Strict `a_i+T*η_i<b_i`, with the same i and interpreted lists. | PASS |
| `w₀,hw₀` | Remaining input point and exactly `abs(w₀.2 j)≤a_j`. | PASS |

The right-nested conjunction is destructured in the same order as its construction. `List.all_eq_true` and `List.mem_range` give checks for each `Fin n` via `hall i i.2`; there is no index shift. In particular the angle derivative is not confused with the action derivative in the proof. The denominator is exactly factorial times Cauchy width, without an extra scale, missing factorial, or changed sign. Positivity of δc and `L≥1` are checked before application.

The full conclusion retains `T₁>T`, the chart initial value, physical Hamiltonian equation on `Ioo (-T₁) T₁`, agreement with every solution on every order-connected interval containing zero, chart-image identity, drift and level bounds for every `|t|≤T`, including endpoints. No extra analytic, divisor, flow, or confinement premise is hidden in a certificate field.

No `FTFits Nact` check is required: the supplier has no such premise, `ftActOnly` gives angle independence on the actual carrier, and the exact formal identity is checked. Missing optional list lengths likewise do not create an escape: zero padding is the declared interpretation at every producer and consumer, and excess entries do not acquire a new coordinate. The n=0 case uses the same empty coordinate family, without assuming a positive dimension.

## Definition classification

| Definition / structure | Classification on the whole carrier |
|---|---|
| `TorusStepCert` | Pure finite data, deliberately allowing invalid certificates. No validity proof fields. |
| `TorusStepCert.torusBmaj` | Total rational majorant expression; invalid inputs are rejected by the checker premises when used for soundness. |
| `checkTorusStep` | Total computable Bool, rational arithmetic plus finite polynomial/list operations and decidable comparisons. No real comparison or choice. |
| `torusSmokeCert` | Literal record, with the accepted integrable polynomial and zero generator/remainder. |
| Inherited `torusChart`, `torusChartInv` | Real time ±1 flow functions on the specified complex strip, not a newly claimed global diffeomorphism. Relevant inverse identities are proved on the guarded domains. |
| Inherited `torusRem` | Literal complex flow pullback minus finite Lie sum, with guarded holomorphy and bounds. |
| Inherited `ftActOnly` | Total finite Bool test: k entries, e and s all zero. No semantic fallback. |
| Inherited `torusSmokeH` | Literal FT polynomial representing J₀²/2. |

The surrounding `noncomputable section` does not make the checker noncomputable. Scratch definitions outside such a section successfully compiled calls to both `checkTorusStep` and `torusBmaj`.

## Inherited delta declarations

These implement the supplier chain described by their module docstrings and handoff, rather than additional B4-TCHECK obligations.

| Node | Declaration | Verdict / note |
|---|---|---|
| B4-TSTEP charts | `torusChart` | PASS, real time-one map. |
| B4-TSTEP charts | `torusChartInv` | PASS, real time-minus-one map. |
| B4-TSTEP endpoint | `torusStep_confinement` | PASS within supplier comparison and replay scope. |
| Strip bridge | `strip_le_log_lam` | PASS, derives the logarithmic strip bound from the rational sufficient checks. |
| Remainder object | `torusRem` | PASS, exact remainder expression. |
| Real inclusion | `ftEvalC_realInclusion₂` | PASS, complexification equals real evaluation. |
| Real inclusion | `ftEvalC_realInclusion₂_im` | PASS, zero imaginary part. |
| Majorant bridge | `norm_ftEvalC_le_of_strip` | PASS, guarded strip bound. |
| Small field | `smallField_of_ftBounds` | PASS, hJ/hφ supply the correct coordinate scales. |
| Remainder regularity | `differentiableOn_torusRem` | PASS, holomorphy on the half gauge interior. |
| Remainder bound | `norm_torusRem_le` | PASS, B/L! bound from the Lie integral remainder. |
| Real remainder | `torusRem_realInclusion₂` | PASS, real-flow compatibility. |
| Normal form test | `ftActOnly` | PASS, finite data predicate. |
| Normal form semantics | `ftEvalR_actOnly` | PASS, angle independence; no FTFits premise added. |
| Pullback identity | `torusRemainder_eq` | PASS, exact Lie-sum identity identifies P plus the real remainder. |
| Drift | `torusDrift_le` | PASS, polynomial derivative bound plus B/(L!δc). |
| Smoke object | `torusSmokeH` | PASS, literal polynomial. |
| Smoke consequence | `torusStepSmoke_zeroDrift` | PASS, integrable zero-drift instance. |

## Mechanical checks

For all Lean/Lake calls, including lint's internal ABI Lean invocation, the final completed checks used this prefix:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

Calls were serialized. An initial lint preflight was terminated before its ABI phase and restarted under this prefix; no successful lint result is claimed from the terminated run. No budgets were overridden, cache fetched, library cleaned, frozen file edited, or generated root regenerated.

1. Targeted build, prefix followed by:

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b4tcheck KAM.EffectiveStability.TorusCheck
```

Exit 0:

```text
[inp-gate] slot 1 acquired 02:53:25 for KAM.EffectiveStability.TorusCheck
Build completed successfully (2995 jobs).
```

2. Independent scratch probe, prefix followed by `lake env lean .lake/abi-scratch/B4TCheckAudit.lean`: exit 0. It compiled ordinary computable wrapper definitions, checked the independent specialized supplier conclusion, and re-proved acceptance with `decide +kernel`. A second serialized run extended the probe to every public theorem in the inherited delta as well; exit 0. Complete axiom output of that run:

```text
'KAM.EffectiveStability.checkTorusStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusSmokeCert_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusSmokeCert_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusStep_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusStepSmoke_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusDrift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.strip_le_log_lam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.ftEvalC_realInclusion₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.ftEvalC_realInclusion₂_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_ftEvalC_le_of_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.smallField_of_ftBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.differentiableOn_torusRem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.norm_torusRem_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRem_realInclusion₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.ftEvalR_actOnly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusRemainder_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusDrift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, prefix followed by:

```sh
lake env leanchecker --verbose KAM.EffectiveStability.TorusCheck KAM.EffectiveStability.TorusStep KAM.EffectiveStability.TorusStep.Drift KAM.EffectiveStability.TorusStep.Remainder KAM.EffectiveStability.TorusStep.Smoke
```

Exit 0, complete output:

```text
replaying KAM.EffectiveStability.TorusStep
replaying KAM.EffectiveStability.TorusStep.Remainder
replaying KAM.EffectiveStability.TorusStep.Smoke
replaying KAM.EffectiveStability.TorusStep.Drift
replaying KAM.EffectiveStability.TorusCheck
```

4. Lint: prefix followed by `sh scripts/lint_sources.sh`.

Exit 1 solely for the explicitly permitted stale generated root; complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (4534 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 3.937s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The lunar application is outside this package and was not built as a side effect. The permitted generated-root exception is retained for the orchestrator.

5. `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b4tcheck KAM.EffectiveStability.TorusCheck`: exit 0, `short-name check OK (no reused public short name)`.

6. `git diff --check inp...HEAD`: exit 0, no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: no output. All five changed Lean files have copyright, module declaration, public imports, module docstring and exposed public section; counts are 176, 139, 130, 167 and 58 lines respectively. Explicit width scan found no line over 100 characters. Forbidden-token/override scan found no match in those files. Smoke proof uses kernel evaluation, with no native reduction bridge.

7. Recursive KAM import inspection: 83 modules; no Provider import; the 20 reachable frozen files are definitions, all manifest state SEALED. No frozen theorem, including any DRAFT_SORRY anchor, is imported. Main exports and smoke results have only the three permitted axioms.

## Notes, uncertainties and errata

**N1 — field documentation, nonblocking.** `TorusCheck.lean:42` says “small-field action scale” for σ', while line 44 says “small-field angle scale” for ρ'. The actual checks at lines 80–81 and `smallField_of_ftBounds` use σ' for the angle component ∂Jχ and ρ' for the action component ∂φχ. These two comments are swapped. Line 64 calls r “coordinate radii of the oscillator ball”; here r bounds torus action coordinates for Cauchy-disc inclusion. Correct those comments when convenient; no type or proof change is needed. These are package documentation defects, not suspected defects in a pinned mathematical source.

**N2 — scope.** This is a one-generator checker and an integrable zero-generator smoke instance. It does not certify a numerical planetary example, a chain of normalizations, an original physical box, or a frozen theorem. Optional producer divisor diagnostics are absent as authorized by OD-B12. The inherited B4-TSTEP dependency remains a separately scoped analytic package.

**N3 — timing.** The handoff's 19.4 ms kernel type-check timing was not independently remeasured. Acceptance and kernel replay were independently checked; no performance conclusion depends on the quoted time.

No additional pinned-source or blueprint defect was found in the assigned checker comparison. No source PDF was needed for this exact wrapper audit; the analytic supplier's published-source provenance was not independently re-established here. No implementation deviations were introduced by the auditor.
