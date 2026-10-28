# N12-12 independent package audit 1

Overall verdict: **PASS WITH NOTES** for N12-12. Both `identity` and `pointwise` pass the design/source-contract and proof review. This is an infrastructure package, with no provider export and no frozen anchor proved or seal-ready by this change. The two averaging roots remain outside this audit.

## Scope and authority

Audited in `/root/code/KAM-inp-n1212`, HEAD `fa46131ca85a0c3f5bc7e9617679d202049a291a`, against `inp` / merge base `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`. `git diff inp...HEAD` adds exactly Identity (186 lines), PointwiseModes (186), and Pointwise (282), 654 lines total. The handoff is an existing untracked input. No production or protected file was edited.

Read AGENTS, PLAN, DECISIONS, the package audit brief, N12-12 handoff and AUDIT FOCUS, N12 design row/proof plan/Appendix A, both design audits (actual location `docs/tracks/N/design/`), `/root/code/KAM-inp/.drafts/design/N12Signatures.lean`, Part 12 blueprint, track N statements, relevant averaging frozen roots/definitions and consumed interfaces. User’s exact worktree report destination overrides the generic brief’s main-worktree destination.

Also inspected `git diff inp-n1206...HEAD` as the focus requests. That older branch comparison includes 110 files, including already integrated unrelated packages; it is not the N12-12 patch. Only the three new modules in `inp...HEAD` are audited; PointwiseModes is included because the new Pointwise directly relies on its modewise argument. No independent re-audit of N12-06/10b or unrelated packages is claimed.

## Declaration and node ledger

All names below belong to `KAM.Nekhoroshev`. Locations are in `KAM/Nekhoroshev/Averaging/<module>.lean`. Every new public declaration has a row; the private `contDiffOn_freq''` (PointwiseModes:36) was also inspected and supplies ordinary real C² frequency regularity from the explicit C³ source hypothesis.

| Node | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| bpN:p12:identity (Q) | `avgCorrectionQ` (Identity:38) | PASS | Literal design definition; sum of real directional derivatives of complex corrector. |
| support | `continuousOn_avgA` (Identity:47) | PASS | Read slow component of the ε=1 C¹ field; exact avgA. |
| support | `continuousOn_avgFreq` (Identity:53) | PASS | Read fast component at ε=0; no frequency nonvanishing assumption. |
| support | `continuousOn_avgB` (Identity:60) | PASS | Subtract frequency from fast component at ε=1. |
| support | `continuousOn_avgCorrectionQ` (Identity:67) | PASS | C¹ corrector on open domain plus continuous avgA/avgB; M₂ derived by compact bounds. |
| support | `continuousOn_avgResidual` (Identity:75) | PASS | Actual residual definition, same derived M₂; no extra premise. |
| support | `differentiableAt_avgW` (Identity:83) | PASS | C¹ on open domain gives genuine real Fréchet differentiability. |
| support | `mem_eIoo_of_le` (Identity:97) | PASS | Maximal left endpoint is below zero and u≤t<T₊. |
| support | `orbit_hasDerivAt` (Identity:104) | PASS | Domain membership and two-sided derivative from avgMaximal_spec. |
| support | `orbit_continuousOn` (Identity:111) | PASS | Continuity of actual chosen maximal solution on [0,t]. |
| support | `orbit_mapsTo` (Identity:116) | PASS | Every valid orbit point belongs to avgDomain. |
| bpN:p12:identity; id-eq/id-chain/id-div | `identity` (Identity:128) | PASS | Exact design signature; real inclusion, minus ε²Q and plus εr; FTC. |
| support | `differentiableAt_avgFreq` (PointwiseModes:45) | PASS | Real C³ integrable Hamiltonian gives differentiable frequency. |
| support | `differentiableAt_avgQ` (PointwiseModes:52) | PASS | Finite mode dot frequency, differentiable on actionBall. |
| support | `differentiableAt_avgU` (PointwiseModes:58) | PASS | Actual coefficient/divisor product; κ>0 guards rational regularizer. |
| support | `norm_avgU_le'` (PointwiseModes:73) | PASS | Coefficient decay, max norm of real-cast k; holds throughout actionBall. |
| support | `continuousAt_avgBterm` (PointwiseModes:87) | PASS | Continuity on valid action ball, not an assertion about arbitrary outside extensions. |
| support | `avgBterm_nonneg'` (PointwiseModes:97) | PASS | Source quantitative majorant is nonnegative for M₂≥0 and s>0; arbitrary I is valid. |
| support | `isOpen_eIoo` (PointwiseModes:105) | PASS | Generic EReal endpoint interval is open; no standing data required. |
| stepN:p12:pw-lambda | `mode_bound` (PointwiseModes:110) | PASS | pw-lambda first half: chain rule and right-derivative fencing with |İ|≤2ε/s. |
| support | `continuousOn_bterm_orbit` (PointwiseModes:175) | PASS | Continuous term on the actual orbit, sufficient for termwise measurability. |
| support | `ofReal_norm_tsum_le` (Pointwise:38) | PASS | Generic ENNReal triangle bound; separates infinite RHS and summable-norm cases. |
| support | `ofReal_norm_integral_le` (Pointwise:49) | PASS | Continuous Bochner integrand, 0≤u≤t; interval integral norm bounded by nonnegative integral on [0,t]. |
| stepN:p12:pw-lambda | `lambda_orbit_le` (Pointwise:73) | PASS | pw-lambda: mode_bound then Tonelli using each mode’s AEMeasurability; same RHS for every u. |
| bpN:p12:pointwise; pw-q/pw-sum | `pointwise` (Pointwise:134) | PASS | Exact design signature; pw-q and pw-sum yield 2εŴ(I₀)+ε∫Φ̂ with unchanged constants. |

## Fidelity and proof applicability

Both theorem telescopes/conclusions equal the supplied design signatures exactly after whitespace normalization and restoring the section-bound explicit `d`. No extra hypothesis, changed carrier, constant, norm, law or dependency order was introduced. `identity` drops the blueprint’s κ≤1 restriction, as the approved design already does: this is a valid strengthening. The equality takes place in complex Pi space after the isometric real inclusion. `pointwise` bounds all u∈[0,t] by one RHS, the approved equivalent formulation of the compact-time maximum bound. It does not interchange a supremum and initial-data integration.

`identity` differentiates ιI−εw along the actual chosen maximal trajectory. The field identity comes from `fbounds`; `wreg` supplies genuine differentiability on the open phase domain. The derivative is εr−ε²Q. Continuity of r and Q follows from C¹ corrector regularity and continuous field components. Interval integrability is established before the FTC and integral subtraction. The initial value is supplied by `avgMaximal_spec`; ordinary derivatives hold at both endpoints because the whole segment lies in the open maximal interval.

`mode_bound` applies the right-derivative fencing theorem to U_k(I(u)), with comparison derivative (2ε/s)b_k(I(u)). The M₂≥0 fact is derived from the row-sum bound at zero and n≥1, not assumed separately. The action derivative estimate is the final conjunct of the revised `wreg` interface; `htraj` supplies exactly its G guard. The field bound pays |İ|≤2ε/s. `lambda_orbit_le` sums these estimates with Tonelli after proving each mode measurable along the orbit, using |character|=1 and coefficient decay. No envelope measurability is silently assumed.

For `pointwise`, wreg gives |Q|≤(2/s)(Ŵ₁+B̂) and |r|≤R̂ on G. Continuous Q,r along the trajectory justify the Bochner-to-lintegral estimates. Nonnegative integrals on [0,u] are enlarged to [0,t]. The lambda variation contributes ε(2/s)B̂, Q contributes ε(2/s)(Ŵ₁+B̂), and r contributes R̂, recovering exactly Φ̂=ε(4/s)B̂+ε(2/s)Ŵ₁+R̂. `le_lintegral_add` has the correct direction for the final upper bound even without envelope measurability.

`AveragingData` contains only dimension, positivity, analytic and intrinsic rank source premises. The Hessian/row bound in pointwise is the explicit design quantitative input, not the desired drift. Both modules consume N12-06 (`wreg`) and N12-10b (`avgMaximal_spec` / Flow) as designed. Transitive source import walk visits 75 KAM modules and finds zero provider imports and zero frozen theorem imports. There is consequently no imported DRAFT_SORRY theorem or provider quarantine violation to classify.

## Definition classification

The only new definition is exposed `avgCorrectionQ` (Identity:38). It is the literal design expression
`fderiv ℝ (avgW h f κ) z (avgB f z, 0) + fderiv ℝ (avgW h f κ) z (0, avgA f z)`.
It is exactly the sum of the angle and action directional derivatives of the complex corrector. There is no conditional branch, replacement law or custom fallback. On the full intended domain with κ>0, all derivatives have been proved genuine; outside that domain Lean’s total `fderiv` convention is inherited, with no theorem relying on invalid values. No new abbreviation, structure or ambient norm instance is introduced.

## Independent checks

All explicit Lean/Lake checks were run sequentially; build, probe and replay used `LEAN_NUM_THREADS=1`. The compile gate was allowed to wait. One queued build was stopped before acquiring a slot to ensure lint’s internal ABI elaboration completed before the build started; it was then restarted successfully. No simultaneous Lean checks were launched by this audit.

1. Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1212 KAM.Nekhoroshev.Averaging.Pointwise
[inp-gate] slot 2 acquired 10:38:33 for KAM.Nekhoroshev.Averaging.Pointwise
Build completed successfully (3227 jobs).
exit 0
```

The target transitively covers all three package modules. Output replayed only upstream warnings from PicardFamilies (unused section variables / haveI style), LocalDependence (unused variables), and CorrectorRegular (deprecated `Measurable.ennreal_tsum`). No warning in the three audited modules.

2. Signature/axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1212Audit.lean
exit 0
```

The probe copies both theorem signatures literally from the delivered design file under fresh names, applies the production theorem to all explicit arguments in order, and checks `example : type_of% @audit_identity := @identity` and the analogous pointwise example. Both pass. Independent text comparisons also return `True` for both telescopes/conclusions (modulo section-bound d and whitespace), and `True` for literal `avgCorrectionQ` definition equality. Provider-to-frozen and seal-body probes are inapplicable because no provider or anchor body is submitted by N12-12; design-signature probes are used instead.

The following is the exact per-name axiom result, with the common namespace suppressed in the left column only. The actual probe prints each name as `KAM.Nekhoroshev.<name>`:

| Public theorem | `#print axioms` output |
|---|---|
| `continuousOn_avgA` | `[propext, Classical.choice, Quot.sound]` |
| `continuousOn_avgFreq` | `[propext, Classical.choice, Quot.sound]` |
| `continuousOn_avgB` | `[propext, Classical.choice, Quot.sound]` |
| `continuousOn_avgCorrectionQ` | `[propext, Classical.choice, Quot.sound]` |
| `continuousOn_avgResidual` | `[propext, Classical.choice, Quot.sound]` |
| `differentiableAt_avgW` | `[propext, Classical.choice, Quot.sound]` |
| `mem_eIoo_of_le` | `[propext, Classical.choice, Quot.sound]` |
| `orbit_hasDerivAt` | `[propext, Classical.choice, Quot.sound]` |
| `orbit_continuousOn` | `[propext, Classical.choice, Quot.sound]` |
| `orbit_mapsTo` | `[propext, Classical.choice, Quot.sound]` |
| `identity` | `[propext, Classical.choice, Quot.sound]` |
| `differentiableAt_avgFreq` | `[propext, Classical.choice, Quot.sound]` |
| `differentiableAt_avgQ` | `[propext, Classical.choice, Quot.sound]` |
| `differentiableAt_avgU` | `[propext, Classical.choice, Quot.sound]` |
| `norm_avgU_le'` | `[propext, Classical.choice, Quot.sound]` |
| `continuousAt_avgBterm` | `[propext, Classical.choice, Quot.sound]` |
| `avgBterm_nonneg'` | `[propext, Classical.choice, Quot.sound]` |
| `isOpen_eIoo` | `[propext, Classical.choice, Quot.sound]` |
| `mode_bound` | `[propext, Classical.choice, Quot.sound]` |
| `continuousOn_bterm_orbit` | `[propext, Classical.choice, Quot.sound]` |
| `ofReal_norm_tsum_le` | `[propext, Classical.choice, Quot.sound]` |
| `ofReal_norm_integral_le` | `[propext, Classical.choice, Quot.sound]` |
| `lambda_orbit_le` | `[propext, Classical.choice, Quot.sound]` |
| `pointwise` | `[propext, Classical.choice, Quot.sound]` |

All 24 public theorems have only the permitted axioms; no `sorryAx`.

3. Kernel replay:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.Identity KAM.Nekhoroshev.Averaging.PointwiseModes KAM.Nekhoroshev.Averaging.Pointwise
replaying KAM.Nekhoroshev.Averaging.Pointwise
replaying KAM.Nekhoroshev.Averaging.PointwiseModes
replaying KAM.Nekhoroshev.Averaging.Identity
exit 0
```

This is one invocation with all three module names; it independently replays the submitted module declarations.

4. Source lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (554 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failing condition is the explicitly permitted stale generated root; it was not regenerated. The initial `sh scripts/lint_sources.sh` run produced the same result; the final rerun above applies the requested single-thread environment and nice priority to its internal ABI elaboration as well. Thus lint is PASS under the audit brief’s named exception, not an unqualified exit-0 claim.

5. Static checks:

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
git diff --check inp...HEAD
(no output; exit 0)
```

All three files have copyright, `module`, `public import`, module docstring and `@[expose] public noncomputable section`. Line counts are 186/186/282, below 1500. Comment-masked forbidden-code scan found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or resource override; module/lint checks cover repository policy. Import closure has no provider or frozen theorem. Final report-only worktree check and probe removal are recorded below.

Probe `.lake/abi-scratch/N1212Audit.lean` and audit-created kernel/lint logs were removed after recording results. Final `git diff --check` and `git diff --check --no-index /dev/null docs/tracks/N/audits/N12-12-audit-1.md` returned no diagnostics (exit 0). Final status has only the new audit report and the pre-existing untracked handoff; tracked files are unchanged. The report was written at the user’s exact requested absolute path, not in `/root/code/KAM-inp`.

## Notes, uncertainties and errata

- The helper split `Identity → PointwiseModes → Pointwise` is an implementation-only DAG refinement. It preserves public main names and exact signatures; duplicated differentiability/value bounds avoid modifying previously audited files. No blocker.
- `identity` keeps unused ε positivity; `pointwise` keeps unused ε≤1, κ≤1 and t≥0 premises exactly as approved. Their non-use does not add a hidden premise or weaken the design contract.
- No new suspected pinned-source or blueprint defect was found. Existing qualification at Part 12:109, “all Borel; the pointwise sums of nonnegative continuous functions,” concerns the valid action domain; these proofs establish termwise continuity only at valid points.
- Inherited source issue E-NAVG-NEI-17 is quoted at Part 12:298: Nei76 p.1298 (17), “sup_t z(t)=∫_{U′}h”. In general only sup∫≤∫sup holds. This package implements the declared repair by bounding every time simultaneously before any integration over initial data. This audit checks that blueprint repair, without claiming a new independent PDF verification or source erratum discovery.
- No source restriction or frozen statement was changed. No anchor closure, global stopped estimate, measure bound, or final averaging theorem is certified by this package audit.
