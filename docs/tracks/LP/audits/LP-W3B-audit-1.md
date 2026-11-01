# LP-W3B independent package audit 1

Audited HEAD: `a290ce18af2f4ef6e37110c1875e04e201eb2472`.
Comparators: `inp=e0262014209bf3b092a103c335b1b4614610d20e`,
`inp-lp=a23001689062e936f0c6c2785bbf545af50a864f`.

Scope: `git diff inp...HEAD`, with mathematical acceptance restricted to
`git diff inp-lp...HEAD -- KAM`: seven new modules (1,025 lines) and seven generated imports
in `KAM/Root/Planetary.lean`. Nothing in LP is frozen; provider/frozen-type equality and seal-copy
probes are inapplicable. This is acceptance of the bounded statements, not a seal or headline audit.

Read AGENTS.md, PLAN.md, DECISIONS.md, the supplied general audit brief, LP-W3B-handoff,
LP-NRR/LP-CONF handoffs and component briefs, SPEC, MAIN L13–L14 and normative AMENDMENTS
(N2/N4/N6 in particular). The exact requested aggregate brief
`/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-W3B.md` does not exist; the local packages directory
also has no LP-W3B.md. The two component briefs explicitly identified by the combined handoff
supply the bounded statements used below. This missing aggregate document is a scope note,
not evidence of an uninspected additional statement. Prior LP-W1B audit D1 was checked for the
stated adapter boundary; dependencies were inspected only at their interfaces and relevant uses.

## LP-NRR — PASS WITH NOTES

The six items of LP-NRR are implemented. `lp_stopped_drift` constructs the analytic bundle,
trace identity and scalar smallness; it does not assume these as new inputs to its exported
statement. Constants `μ₀,c,T₀,s,σ,w` are existentially quantified before `μ`, `I0`, block,
interval, physical curve and chart curve. Dependence is only on `n,ν,L,δ,γ,τ,D₀` and standing
proofs. A compact subset of the chamber is more general than a compact family supplied through
semimajor axes. The coordinate lower bound need only hold on the actual centre set `L_δ`;
it is not necessary to bound all of U for the centred complex Kepler estimate.

**N1, applicability boundary (nonblocking).** The theorem supplies the source stopped estimate
with D1's expressly permitted chart lift, outer `realDom` localization and stopped slow membership.
There is no separate `IsMovingSolutionOn` binder: the assumed chart ODE and projection already
supply the curve data used by the adapter, so this is stronger than requiring both. It is not an
unconditional theorem for a bare physical solution. `realDom` entails an outer action tube,
not the improved half-radius estimate. The slow ball premise is the engine's stopped input,
not a claimed consequence. LP-LIFT/LP-PS must still construct these inputs and connect this result
to CONF's `hstop`; this package does not perform that assembly.

Normalization: `lpKepler=planetaryKeplerC/(2π)`, frequency `ν³/I³/(2π)`, perturbation
`μ fc(unrescale)/(2π)`, and unrescaling `((2πθ,ℓq),(I,ℓp))` agree literally with L13.
The existing adapter uses `b.c=2π/ℓ²` and the indicator Hamiltonian field on the open `realDom`.
The trace is proved on that whole open domain, so the local field equality applies in unchanged
physical time. No signed/absolute AMD convention is interchanged here.

Widths: `s₀=b₀=R/16`, `r_s=min(4r_g,R/4)`, `s=σ=s₀/π`, `w=2b₀`,
`ρ=min(r_s,Imin)/2`. Thus `r=D₀√μ≤ρ<r_s`, `r_s≤4r_g`, `w<4b₀`,
`2πs<2π(s+σ)=4s₀`, and `max(r_s,4s₀,4b₀)<R/2`.
The Fourier estimate uses the positive extra strip σ: equality at the larger strip does not
remove N6's strict margin at the engine strip. The radius is strictly inside the constructed
fixed action tube, not merely at its boundary. These choices all precede μ.

`lpExtNFHyp` was checked field by field against `Partial/Setting.lean`:

| Engine field | Supplier / check |
|---|---|
| n_pos, k_pos | n≥2, k=n |
| radius_pos, slow_width_pos, s_pos, K_pos | Positive widths/radius; K≥1 |
| alpha_pos, L_nonneg, p_gt, eps_pos | α=γ/(2π)K^(-τ)>0; sum Lipschitz bound≥0; p=2; ε=M₂μ>0 |
| symmetric | Literal module {0} |
| hol, real | Kepler holomorphy off coordinate zero; reality on real points |
| nr, lip | Centre Diophantine conversion; uniform complex frequency Lipschitz estimate |
| divisor_size | KLr≤α/2, exactly p=2 |
| slow | 64π n s r≤w², exactly k=n |
| pert | ext_class on the engine domain at s |
| bound | WBound at s, ε=coth(πσ)^n M μ/(2π), paid from strip s+σ |
| cutoff | 6≤2πKs |

`lp_scale_choice` supplies `hsmall` with denominator `2^7 * conjExp 2 * K = 256K`,
the scalar fields, radius smallness and the comparison to engine time
`s r/(5ε) exp(2πKs/6)`. No finite-cutoff persistence claim (35) is used.

Every new theorem is listed below; all names are in `KAM.Planetary.StrongAMD`.

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| Kepler | lpKeplerLip_nonneg | PASS | Nonnegative sum for positive masses, including total arithmetic at Imin=0. |
| Kepler | lp_re_ge_of_mem_polyNbhd | PASS | Coordinate real-part bound from the sup ball. |
| Kepler | lp_norm_ge_of_mem_polyNbhd | PASS | Real part bounded by complex norm. |
| Kepler | lp_ne_zero_of_mem_polyNbhd | PASS | Positive Imin rules out poles. |
| L13.1 | lpKepler_differentiableOn | PASS | Holomorphy on the requested centred neighbourhood. |
| L13.1 | lpKepler_real | PASS | Exact real trace, even at totalized coordinate zeros. |
| L13.1 | lpKepler_freq | PASS | Correct derivative with nonzero-coordinate premise. |
| L13.1 | lpKepler_freq_real | PASS | Correct period-one centre frequency. |
| L13.1 | lpKepler_freqLipschitz | PASS | Sum bound uniform in the centre; stronger assumptions on centre positivity are typing/domain data. |
| L13.2 | lpKepler_isNonresonant | PASS | {0}, modeSize and γ/(2π)K^(-τ) preserved. |
| L13.3 | lpUnrescaleC_extCx | PASS | Exact complexification of real unrescaling. |
| L13.3 | lpUnrescaleC_differentiable | PASS | Complex linear map, all real scales. |
| L13.3 | lpUnrescaleC_shift | PASS | One engine period maps to the physical 2π fast shift. |
| L13.3 | lpUnrescaleC_mem_complexTube | PASS | Fast, angular and both slow blocks mapped to D5 with ℓrB=w. |
| L13.3 | lpTube_mono | PASS | R/2 tube included in positive R tube. |
| L13.3 | lpPert_dom_mem | PASS | Domain form of the containment lemma. |
| L13.3 | lpPert_extClass | PASS | Holomorphy, periodicity and real trace, without assuming engine-class output. |
| L13.3 | lpPert_sup_le | PASS | μ≥0 gives μM/(2π) bound. |
| L13.3 | lpPert_wbound | PASS | Fourier loss paid once by positive σ. |
| Scalar | lp_coth_pos | PASS | Positive argument, positive sinh and cosh. |
| Scalar | lpM₂_pos | PASS | σ,M positive, including arbitrary n. |
| L13.5 | lpTrace | PASS | Literal trace on b.realDom b.rB, no orbit-specific restriction. |
| L13.4 | lpExtNFHyp | PASS | All twenty source fields supplied as above; no normal-form output assumed. |
| Compactness | lp_exists_lower_bound | PASS | Handles empty K and empty Fin carrier; positive uniform bound. |
| L13.6 | lp_stopped_drift | PASS WITH NOTES | Correct constants, r/2 and horizon; explicit localization boundary N1. |

## LP-CONF — PASS WITH NOTES

`strongFirstExit_of_stopped_drift` is distinctly named and explicitly documented as a conditional
helper, exactly as its brief permits. Its only added analytic premise is `hstop`: for every interval
and solution from z₀, strict stopped physical/tube/margin conditions up to t imply only endpoint
action drift ≤r/2. It assumes neither existence to T, improved AMD margin, barrier compactness nor
uniqueness. This is the L13/L12 stopped estimate used at the intended intermediate layer, rather
than a disguised final confinement statement. The strict antecedent follows MAIN (40); the brief
explicitly authorizes this choice. A closed-form stopped estimate supplies it by weakening strict
inequalities, so the helper is stronger than the brief's closed-antecedent version.

The proof uses open V=`firstExitTube`, improved C=`firstExitCore`, and N=positive star radii.
C⊆V uses r,δ>0. The apparent strict-energy issue in sequential closedness is paid:
C lies in `BarrierState ν U (δ/2)`, the barrier theorem supplies E_i≤−c with c>0, and energy is
continuous at every limiting point of N. Only after establishing physicality of the limit does
the proof invoke continuity of the actions and of B on the open chamber. It does not assume that
the entire physical region is closed, or that C is globally closed through stellar collisions.

Inside V, `hstop` gives r/2, conservation via (17) gives
`C(t)≤B(I(t))−δ+n r/2+Ω_B(r/2)`, and monotonicity plus the budget gives margin ≥3δ/4.
The same compact U and its same modulus are used throughout. The local helper needs only the
closed r-ball about the actual initial action in U; it need not repeat the global N2 construction
of that U or an additional r_g hypothesis. Both time directions use uIcc. On the maximal-solution
interval intersected with [-T,T], the two exit lemmas establish the core bounds. Barrier compact
continuation excludes an endpoint at or before ±T; endpoints are included in the resulting Icc.
Uniqueness is exactly the frozen `MovingUniqueOn` quantification over every open convex local
interval containing 0, by `gen_uniqueness_inter` with the certified interval.

Omitting μ≥0 is a genuine strengthening: the reused smooth ODE and momentum identities hold
for all real μ; no physical positive-mass assertion is claimed off that regime. The hstop
premise is still an explicit obligation to be discharged by LP-PS, not an audited consequence here.

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| L14 | firstExitCore_subset_tube | PASS | Both strict improvements use positive δ,r. |
| Restriction | movingSolutionOn_mono | PASS | Restricts both ODE and collision-free solution clauses. |
| Continuity | continuousAt_actionVector | PASS | Correct physical-state neighbourhood. |
| Continuity | continuous_totalMomentum' | PASS | Polynomial physical angular momentum. |
| Continuity | continuousAt_strongAMD | PASS | Sum of actions minus absolute total momentum. |
| Continuity | continuousAt_keplerEnergy' | PASS | Positive limiting radius excludes the only variable pole. |
| Continuity | continuousAt_strongGap | PASS | Threshold continuous at chamber action vector. |
| L14 open set | isOpen_firstExitTube | PASS | Ball containment puts current actions in open chamber. |
| L14 limiting set | firstExitCore_closed | PASS | Relative sequential closedness in N; negative energy recovered uniformly. |
| L14 helper | strongFirstExit_of_stopped_drift | PASS WITH NOTES | Correct conditional first-exit, existence, closed endpoints and frozen uniqueness; assembly remains external. |

## Definition classification and edge cases

All ten new definitions/structures are exposed through the section attribute and use Fin-function
carriers. There are no new abbreviations. The facade introduces no declaration.

| Object | Whole-carrier classification / boundary behaviour | Verdict |
|---|---|---|
| lpKepler | Literal inherited rational Kepler expression divided by nonzero 2π. Lean division totalizes coordinate poles; holomorphy/frequency claims exclude those poles. No theorem uses pole values as physical Kepler data. | PASS |
| lpKeplerLip | Literal finite sum of 3ν³/[2π(Imin/2)^4]. Imin=0 gives zero by field totalization; actual Lipschitz theorem requires Imin>0. Empty index sum is zero. | PASS |
| lpFrequency | Literal ν_i³/I_i³. Total at I_i=0; centre use explicitly has positive actions/nonzero coordinates. | PASS |
| lpUnrescaleC | Literal linear coordinate formula. At ℓ=0 collapses slow coordinates, with no claimed inverse; containment requires positive block widths and radius. n=0 gives the unique empty-coordinate map. | PASS |
| lpPert | Literal scaled composition. μ=0 gives zero; negative μ is allowed for class/trace statements, while upper estimates require μ≥0. No fallback branch. | PASS |
| LPChartTube | Exactly exists_strongTube's analytic, trace, periodic and sup-bound outputs. No drift/normal-form/confinement field. Empty core can give vacuous data, but no centre exists to exploit it. | PASS |
| lpM₂ | Literal coth(πσ)^n M/(2π). σ=0 uses Lean's total division; positivity and Fourier uses require σ>0. n=0 leaves exponent zero; no dimension shortcut is used by the engine. | PASS |
| lpBlock | Raw PartialBlock constructor with centre I0, entire secularBall, radius r and width w. Invalid/zero widths are representable, as in the engine record; all uses obtain positive values before division/inversion. | PASS |
| firstExitTube | Literal physical, strict action and strict AMD-margin conjunction. Nonpositive r makes the tube empty; physical totalizations outside the carrier are excluded explicitly. No general openness claim without chamber control. | PASS |
| firstExitCore | Literal physical, half-radius and 3δ/4-margin conjunction. Negative r makes it empty; degeneracies r=0 or δ≤0 are not used by the exit theorem. Relative closedness only, with positive limiting radii. | PASS |

## Hygiene and validation

All Lean/Lake processes in this audit were serial. The build wrapper was inspected: it
acquires a compile-gate slot and invokes exactly
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake build <Module>`
once per module. No heartbeat, synthesis or recursion override was used.

1. Exact targeted build command (exit 0):

```sh
/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-thr KAM.Planetary.StrongAMD.Confinement KAM.Planetary.StrongAMD.NonresonantReuse.Kepler KAM.Planetary.StrongAMD.NonresonantReuse.Pert KAM.Planetary.StrongAMD.NonresonantReuse.PertClass KAM.Planetary.StrongAMD.NonresonantReuse.Hyp KAM.Planetary.StrongAMD.NonresonantReuse.Drift KAM.Planetary.StrongAMD.NonresonantReuse
```

Observed success output, one line per target in that order:

```text
Build completed successfully (9128 jobs).
Build completed successfully (9153 jobs).
Build completed successfully (9214 jobs).
Build completed successfully (9215 jobs).
Build completed successfully (9277 jobs).
Build completed successfully (9279 jobs).
Build completed successfully (9280 jobs).
```

These are targeted builds using the existing snapshot, with cached dependency replay, not fresh
library rebuilds. The package-local warning is
`NonresonantReuse/Pert.lean:137:51: This simp argument is unused: Fin.append_left`.
Other replay warnings occur in existing ODE.Exit, AMD.Closure, Kepler.Energy/ Mass,
Poincare.Chart, Exponential.RealDomain/ComplexTube and Nekhoroshev.Stability.Gradient.
No error or package proof-budget failure occurred. No source was changed to suppress a warning.

2. Exact designated lint command (exit 0):

```sh
/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-thr
```

Observed output:

```text
check_lean_modules: PASS (3692 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The file-hash-only application exception is the lint tool's explicit scope; no application was built.

3. Exact independent short-name command (exit 0):

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-lp-thr KAM.Planetary.StrongAMD.Confinement KAM.Planetary.StrongAMD.NonresonantReuse KAM.Planetary.StrongAMD.NonresonantReuse.Kepler KAM.Planetary.StrongAMD.NonresonantReuse.Pert KAM.Planetary.StrongAMD.NonresonantReuse.PertClass KAM.Planetary.StrongAMD.NonresonantReuse.Hyp KAM.Planetary.StrongAMD.NonresonantReuse.Drift
```

Output: `short-name check OK (no reused public short name)`.

4. Axiom probe imports the two public facades and runs `#print axioms` on every one of the 35
new public theorems listed in the declaration tables. Exact command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/lp_w3b_audit1.lean
```

Exit 0. All 35 results have exactly the allowed standard axioms:

```text
'KAM.Planetary.StrongAMD.firstExitCore_subset_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.movingSolutionOn_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.continuousAt_actionVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.continuous_totalMomentum'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.continuousAt_strongAMD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.continuousAt_keplerEnergy'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.continuousAt_strongGap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.isOpen_firstExitTube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.firstExitCore_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.strongFirstExit_of_stopped_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lp_exists_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lp_stopped_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lp_coth_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpM₂_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpTrace' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpExtNFHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpKeplerLip_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lp_re_ge_of_mem_polyNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lp_norm_ge_of_mem_polyNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lp_ne_zero_of_mem_polyNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpKepler_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpKepler_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpKepler_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpKepler_freq_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpKepler_freqLipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpKepler_isNonresonant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpUnrescaleC_extCx' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpUnrescaleC_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpUnrescaleC_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpUnrescaleC_mem_complexTube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpTube_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpPert_dom_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpPert_extClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpPert_sup_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lpPert_wbound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The temporary probe was deleted after the check.

5. Kernel replay was already run by the launcher according to the task. Its output and exit code
were not visible in this audit. It was not rerun, and no independently observed leanchecker result
is claimed. There was no reason from the inspected proof terms/statements to repeat it.

6. Static checks: all seven modules have copyright headers, `module`, public imports, module
docstrings and public sections. Lengths: Confinement 269, facade 23, Kepler 215, Pert 146,
PertClass 103, Hyp 134, Drift 135; all below 1500. Token inspection finds no sorry, admit,
axiom, unsafe, opaque, forbidden budget override or EuclideanSpace in the new Lean code.
Production imports contain no provider, DRAFT_SORRY theorem, application root or generated root part.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has no output;
`git diff --check` has no output (exit 0). The only changed root part adds exactly the seven
package imports, as recorded in the handoff; the auditor did not regenerate it.

## Source defects, deviations and combined verdict

No mathematical defect found in MAIN L13–L14 as amended. The quoted MAIN L14 phrase
“improves the action bound to r/4” is superseded for this route by N6's “improvement is to r/2”;
this is an explicit amendment, not a new erratum.

Accepted deviations: sum rather than max for lpKeplerLip (valid larger uniform constant), no unused
ν argument on lpPert, max M 1 for a positive perturbation bound, strict stopped antecedent as
permitted by the CONF brief, all-real μ for CONF, and source localization retained as explicit
premises in NRR. No new conclusion-shaped hypothesis is hidden in an instance or structure.

Documentation note: the new module docstrings identify LP/non-frozen status and source ranges,
but omit SPEC §4's exact phrase “the statement surface is proposed in
docs/tracks/LP/FREEZE-PROPOSAL.md”. Some supporting theorem docstrings use package item numbers
rather than repeating a literal LP:MAIN tag. This has no effect on the elaborated statements.

Combined verdict: **PASS WITH NOTES**, for LP-NRR and LP-CONF at the precise package-diff scope.
The notes are the missing aggregate brief, retained chart/localization and hstop assembly obligations,
and documentation metadata. No new frozen theorem or unconditional LP headline is approved by this audit.
Only this report is retained; temporary axiom probes are removed after checking. No source repair,
state-changing git command, or generated-root edit was performed by the auditor.
