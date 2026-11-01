# W8 independent package audit 2

Date: 2026-11-01. Auditor: maud-wpr-2.

**Overall: PASS WITH NOTES for W8 and the provider of `wave.nlw2.v1`, within the requested W8 scope.** The exact provider and proof types pass; the proposed seal body elaborates in a temporary copy. Round-1 F1 and F2 are repaired at the actual source instance; N1's previously missing source results are supplied. No W8 proof blocker was found. This does not independently re-audit W5, W6 or W7, and does not authorize bypassing their separate package gates. No seal edit was made. The frozen export remains **FROZEN_UNPROVED (`DRAFT_SORRY`)** until the owner-approved seal is performed.

## Snapshot, authority and scope

Worktree `/root/code/KAM-inp-wpr` (physical cwd supplied as `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpr`). HEAD `d91269e80d528e33d7f937cc8eac832daa3baca8`; comparison `inp` and merge base `698fd38075bb3d814749ecfeae94a919cac3743e`. Used `git diff inp...HEAD`. The W8-only diff (paths `KAM/Wave/Assembly` and `KAM/Provider/Wave/Nlw2.lean`) has SHA-256 `e1f7fd9d296623840532c7355178cff2871ec4adce5d142124a86770678ee2a0`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, W8-R2/PREP/ASM/FINAL handoffs, `git show inp-w8a:docs/tracks/W/audits/W8-audit-1.md`, `docs/tracks/W/W-STATEMENTS.md`, the frozen theorem and meaning-bearing definitions, and `blueprint-W/parts/w8-assembly.tex`. Applied the lean-statement-audit skill. `W8-handoff.md` is absent; the user's replacement focus in `W8-R2-handoff.md` controls. The user-specified report destination supersedes the generic brief's main-worktree destination.

Reviewed all 22 Assembly modules plus the provider: **4503 physical lines, 264 public declaration commands (196 theorems including the provider, 68 definitions/abbreviations/structure commands)**. Every Assembly module is transitively imported by Nlw2Proof. Other changed files in the branch diff include W5 action-angle/initial and W6 iteration modules, plus the generated `KAM/Root/Wave.lean`; their mathematical implementations are outside this audit. Imported interfaces were inspected where W8 consumes them.

Manifest identity: `wave.nlw2.v1`, contract `wave.nlw2` version 1; export `KAM.Wave.nlw2`; implementation `KAM.Provider.Wave.Nlw2` / `KAM.Provider.Wave.nlw2`; state `DRAFT_SORRY`; author approval D41 / W-STATEMENTS rev 1 at `ffcbdb93`. Source: blueprint-W rev 1 / P96-W pp. 272–273, 289, with the D30/W-A2 weakenings. ABI hash `eca3aee797e9040ce3fde0e946ce30e10fe8550faa413b6a83fc9abda495ddb7`; prefix `b2962b367741a5f5e42202a09b1c4908e36416e12687ca3528b77379a3a6a9b5`; suffix `9fbcbc092ac5275ee83355be1725aec08622915482639ba4d88d69383961d4f6`. All 12 definition-closure file hashes were recomputed and match. The lint guard checks the frozen bytes and ABI below.

Snapshot SHA-256 values:

| Artifact | SHA-256 |
|---|---|
| Frozen Nlw2.lean | `9ce65519e3108c55e50565b268e7138d5a47ed68fbfade07166d0641b2e2dde6` |
| manifest/frozen-anchors.json | `8859fe7f8bae7ca904585d0b72a6c23601d848c66febefdc7e5c74adb2300555` |
| blueprint-W/parts/w8-assembly.tex | `dfe5c696903edc33308c3dcbe38198c872f3bfa71e2de61cd39573fffdda46f0` |

## Round-1 disposition and notes

**F1 repaired, with an API-splitting note.** `ShellIter.lean:239` now states `IsFreqPair` with `ε₁ = 3 * w6Gamma * α_n` and `ε₂ = 4 * ε_{0,n}` separately, supplied by `w6WaveFamilyJ`; it uses `w6ExclusionJ` for the same family. These are the literal constants of `w8-assembly.tex:212–217`, rather than the former weaker normal-frequency decay. The declaration `w8_w6General` itself still does not contain a tori conjunct. That portion is a separate, unconditional theorem `w8ShellToriKam` at line 262. For the source perturbation, `w8_toriData` supplies every argument of the local `w8tori` expansion to W6's full Birkhoff-coordinate `w6Tori`; the shape, embedding, continuity and invariance proofs actually consume it. Thus the complete label is implemented across these declarations; a claim that `w8_w6General` alone literally has every conjunct would remain inaccurate.

**F2 repaired on the source carrier, not a certification of the arbitrary wrapper.** `ShellEmbed.lean:44` fixes `w8AA ξ w = aaMap 1 1 (aaOfReal ξ) w`; `w8Kshell_eq` at line 59 identifies `w8Kshell w8AA (w8HW hm n)` with `w8KOfBirk m hm (w8Psi hm n ξ)`. `ShellTorus.lean:331` proves `w8Psi_ball`: for every `ξ ∈ Γ_n` and every real angle, reality, `birkPi Ψ ∈ birkRealBall1`, and `birkZR (birkPi Ψ) = Ψ`. Together with `w8KOfBirk_of_mem` this removes the zero branch at **every source shell point**. `w8KOfBirk_eq_gamma` proves the second source formula as well. Consumers explicitly supply these facts, including the two distinct shell arguments in family injectivity.

The unrestricted definitions `w8KOfBirk` and `w8Kshell A H` still have invented zero/off-domain or arbitrary-A semantics. They are generic implementation wrappers, not globally faithful definitions of the manuscript object. Their unrestricted public-carrier source-definition verdict remains FAIL; this audit passes only the actual source instance restricted to `ξ ∈ Γ_n`, as specifically requested by R2. No downstream theorem may discard that restriction or interpret arbitrary `A` as the source map. No current source-facing W8 conclusion does so.

**N1 mathematically repaired; stale prose remains.** `w8HW hm n` constructs the source prep hypotheses from `m > 0` and shell arithmetic using `w6PrepHyp_initial`. The old conditional `_of_initial` lemmas are no longer substituted for shell-data closure. `w8_shellEmbedding`, `w8_shellClose`, `w8_shellInv`, `w8_shellInvCont`, `w8_patchContK`, and `w8_injective` supply the formerly missing results without a StepSmooth premise. `nlw2_proof` assembles them. Historical comments remain misleading, e.g. `Consts.lean:23–26` says four constants have “no Lean definition yet”; `Patch.lean:18–20` says the iteration “has no Lean form yet”; `PatchInst.lean:36–37` calls the action-angle map “a parameter here: it is not in this base”. `UpstreamW6`, `ShellIter`, `ShellTorus` and `ShellEmbed` now supply them. These are documentation notes, not mathematical gaps.

## Every W8 label

Labels below are `bpW:w8:*`; names are in `KAM.Wave` unless qualified. PASS on a label means the indicated collection of declarations implements it at the source instance, not that every generic helper independently has the full label's type.

| Label / source lines | Declarations | Verdict | Evidence / scope |
|---|---|---|---|
| ext-inner / 59–64 | w8ext_hasDerivAt_inner, w8ext_inner_eq_tsum, w8ext_summable_abs_mul, w8ext_tsum_add, w8ext_abs_inner_le | PASS | Actual ℓ² pairings, summability and derivative; subtraction via Mathlib. |
| ext-mono / 65–68 | w8ext_antitoneOn_Icc, w8ext_monotoneOn_Icc, w8ext_hasDerivAt_exp_mul | PASS WITH NOTES | Icc/endpoint-derivative specialization used by W8; generic interval result remains Mathlib's. |
| ext-compact / 69–71 | w8ext_bounded_Icc, w8ext_continuous_of_analyticAt | PASS | Compact bounds and analytic continuity. |
| ext-exp / 72–76 | w8ext_exp_eq_one_iff, w8ext_norm_exp_I, w8ext_const_of_intValued, w8ext_eq_zero_of_bounded_mul | PASS | Period-one exponential/integer convention. |
| ext-sqrt / 77–78 | w8ext_abs_sqrt_sub_le | PASS | Positive a, nonnegative a+b; exact denominator. |
| ext-dist / 79–81 | w8ext_infDist | PASS | Strict superlevel open; vanishing and distance comparison. |
| ext-rpow / 82–86 | w8ext_rpow, w8ext_rpow_le_rpow, w8ext_tendsto_const_mul_rpow | PASS | Correct positivity/exponent scopes. |
| ext-local / 87–94 | w8ext_continuousOn_of_local, w8ext_clm_comp_analyticOnNhd, w8ext_fderiv_clm_comp, w8ext_le_of_tendsto | PASS | Local continuity, chain rule and limiting inequalities. |
| const / 100–115 | Consts definitions; w8Upstream, w8T0W | PASS WITH NOTES | Literal constants at actual upstream instance; stale comments noted. |
| shells / 117–130 | w8tn, w8Rn, w8alpha, w8rn, w8rhoXi, w8rho, w8epsSharp, w8kappa, w8eps0, w8alphaHat, w8Pi | PASS | Dyadic ratio, exponents, and strict infDist margin agree. |
| shell-data / 132–174 | w8_shellData_sizes, ShellGeom results, w8_shellData_init, w8_shellData_prep, w8HW | PASS | All numerical premises and actual initial perturbation supplied, including smoothing and field bound. |
| sharp-prep / 178–196 | w8_epsFlat_shell, w8_sharpPrep | PASS | Sharp positive size and admissible starting interval; source instance H=w8HW. |
| shell-iter / 198–210 | w8ShellSeqData/Start/Gamma/Omega/Nu/Family/Excl/Etor/EpsOm/TorusKam; w8Psi | PASS | Actual iteration with shell-dependent starting size; A composed in w8Psi. |
| w6-general / 212–229 | w8_w6General, w8ShellToriKam, w8_toriData and local w8tori | PASS WITH NOTES | Exact frequency constants; tori exported/consumed separately, not a conjunct of w8_w6General. |
| etor / 231–246 | w8_etor | PASS | E₄κ=E₅t^(1/64)≤7/256; frequency error ≤α/(70L_A)≤α. |
| freq-shell / 248–271 | w8_freqShell, w8ShellGamma_subset_D, w8ShellOmega_tendsto | PASS | H1 limit, 7/(8L_A) co-Lipschitz bound, divisors, Lipschitz ν and Borel Γ_n. |
| torus-shape / 275–312 | w8TK_differentiableOn, w8TK_close, w8_torusShape_bounds/real/coord/deriv, w8XC_periodic, w8Xang_periodic, w8Xang_lipschitz, w8Psi_ball | PASS | Complex X/y holomorphy from TK components, normal bound from full w8tori(iv); real formulas, full integer periodicity, derivative bound and ball inclusion. |
| Kshell / 314–321 | w8AA, w8Kshell_eq, w8KOfBirk_of_mem, w8KOfBirk_eq_gamma, w8Psi_ball | PASS WITH NOTES | Exact source map on Γ_n×ℝ²; unrestricted wrapper not certified as source definition. |
| shell-embedding / 323–353 | w8_shellEmbedding; w8Kshell_analytic/injMod/fderiv_injective | PASS | Every frozen embedding conjunct; derivative proof through differentiable left inverse, not an assumed inverse derivative. |
| shell-close / 355–381 | w8_shellClose, w8_shellDist, w8_gammaR_bounds, w8_gamma_arith, w8_tan_arith | PASS | Same E₇ and 2ρ bounds; extra √2 paid by smaller t exponent. |
| shell-inv / 383–409 | w8_shellInv, w8_shellInvCont | PASS | Full coefficient derivatives and joint continuity; all reduction premises produced. |
| patch / 413–422 | w8GammaW, w8NuW, w8KW at w8HF/w8AA | PASS | Union; unique shell index; prescribed zero off Γ. |
| patch-local / 424–436 | w8_patchLocal, w8_patch_of_mem | PASS | Open disjoint neighborhoods, exact piece identification including K. |
| boundaries / 438–445 | w8Pi_isOpen/disjoint/sep_of_ne, volume_w8Rn_diff_w8Pi_le | PASS | Strict trimmed shell and 7α_nt_n boundary cost. |
| patch-cont / 447–461 | w8_patchCont, w8_patchContK | PASS | Borel, positive-quadrant/radius inclusion, ν and K continuity. |
| unique / 465–489 | isAnalyticCoeffSolution_unique | PASS | Only two analytic coefficient solutions and equality at zero; energy cancellation uses genuinely summable products. |
| winding / 491–501 | winding_rate_eq | PASS | Exactly positive amplitudes, continuous phases and bounded drifts; amplitude continuity retained though unused. |
| nu-injective / 503–515 | w8_nuInjective | PASS | Same-shell co-Lipschitz bound and different-shell margins actually supplied. |
| injective / 517–543 | w8_injective, w8_shell_freq_eq, w8_orbit_eq_of_meet | PASS | Equal initial point → equal coefficient orbit → equal Birkhoff phases → equal frequencies/actions → integer angle difference. |
| nlw2-proof / 547–624 | nlw2_proof | PASS | Exact frozen type, single source premise; all conjuncts assembled. |
| frozen provider | KAM.Provider.Wave.nlw2 | PASS | Exact Expr type, body nlw2_proof hm; provider replay clean; quarantine intact. |
| check/deviations / 626 onward; ext/shell-sec/iter-sec/tori-sec/patch-sec/inj-sec/proof-sec | explanatory sections | PASS WITH NOTES | Organization/provenance, not additional theorem labels; proof-route variations and stale prose recorded here. |

## Hypothesis audit and actual consumption

Root type, **separately for `nlw2_proof` and `KAM.Provider.Wave.nlw2`**:

| Expanded binder | Bin | Source / interpretation |
|---|---|---|
| implicit m : ℝ | TYPING | bpW:w0:mass; real mass parameter. |
| explicit hm : 0 < m | SOURCE | bpW:w0:mass; W-STATEMENTS rev 1. |

Per root: SOURCE 1, STANDING 0, TYPING 1, RULED 0, EXCESS 0. No hidden instance or proof bundle in the root. Existentials r₀,C,τ,η,Γ,ν,K are chosen after m and before I/θ; γ is allowed to depend on I. The positivity binder hI and Γ-membership in clause (3) occur in the conclusion, and positivity is also produced by the inclusion clause. Frozen IsAnalyticTorusEmbedding expands to periodicity, analytic maps, injectivity modulo integers, injective fderiv; all four are proved. IsClassicalSolution expands to continuous u,ut,ux,utt,uxx, the prescribed derivatives and equation on ℝ×[0,π], and both Dirichlet boundary values; W2's exact clause5 conclusion is consumed unchanged. Period 1, weighted E_{1,1}, max-norm action balls, γ_I scope and ENNReal density ratio are preserved.

`W8ShellPrep` is a transparent specialization of W6PrepHyp. For sharp-prep/shell iteration it describes the source instruction to run prep-step; it is **proved**, not assumed, at the final source instance. Each row below is a SOURCE input for that generic preparatory problem, `w8-assembly.tex:144–147,178–185`. No one of these rows is an additional root premise.

| Expanded input | Bin | Production at source instance |
|---|---|---|
| meas: Π_n measurable | SOURCE | w8_shellData_prep. |
| sub: ξ∈Π_n → ‖ξ‖≤1/2 | SOURCE | w8_shellData_prep. |
| hα: 0<α_n | SOURCE | w8_shellData_prep. |
| hα0: α_n≤α₀ | SOURCE | w8_shellData_prep. |
| hr: 0<r_n | SOURCE | w8_shellData_prep. |
| smooth.holoP on Π_n∖Ξ | SOURCE | initial perturbation via w6PrepHyp_initial inside w8HW. |
| smooth.holoX on Π_n∖Ξ | SOURCE | same. |
| smooth.deriv_eq: dP=stepSymp(X,·) | SOURCE | same; actual Hamiltonian field identity. |
| per: P(w+stepTau i)=P(w) | SOURCE | same. |
| real: StepReal w → Im(P w)=0 | SOURCE | same. |
| hε: 0<εSharp | SOURCE | w8_shellData_prep. |
| hεγ: εSharp≤γα_n | SOURCE | w8_shellData_prep. |
| bound: ∃ ε₀,ε₁≥0 with ε₀+λ ε₁≤εSharp and field sup/Lipschitz estimates | SOURCE | initial perturbation at the shell parameters and w8EpsIn_shell_sharp. |

Logical field count after expanding IsSmoothing: SOURCE 13, STANDING 0, RULED 0, EXCESS 0 (ordinary m,n,P,X and carriers are TYPING). The last existential is a norm-bound predicate: its ε₀,ε₁ are bound witnesses, not universally given extra data. Its five conjuncts are ε₀≥0, ε₁≥0, budget bound, pointwise field bound, and parameter-difference bound; all remain inside that SOURCE norm premise. W8UpstreamConsts has four numerical TYPING fields and four positive-sign SOURCE properties, realized by w8Upstream; no instance carries a hard W8 result.

Internal conditional helpers retain distinct names and their displayed inputs. In particular `_of_initial`, `_of_pieces`, `_of_birk` and `w8_freq_eq_of_shape` are not standalone source-label closure. Their hard inputs would be EXCESS if promoted into the root statement. The final code actually eliminates them:

| Consumer | Producer supplying its hard input |
|---|---|
| generic shell W6 APIs | w8HW constructs the full H from initial perturbation; w8_epsFlat_shell supplies starting interval. |
| full Birkhoff w6Tori | w8_toriData supplies interval, positive t, action-angle parameter bounds and radius condition. |
| w8_shellInv_of_birk | w8Psi_ball supplies reality/balls; actual fderiv chain gives hder; W6 tori(iii) plus w8_birkEmbed_comp gives heq. |
| w8_shellInvCont_of_birk | W6 tori(ii) plus w8Psi_ball for every parameter/angle. |
| w8_patchContK_of_pieces | w8_shellInvCont on every shell. |
| w8_freq_eq_of_shape | w8_coord_true, w8_sqrt_pos, w8_torusShape_bounds and actual continuity of w8TK. |
| w8_injective_of_pieces | w8_patchEmb, w8_patchInv, the proved orbit/frequency reduction and w8_nuInjective. |
| reconWave_clause5 | w8_patchEmb, w8_patchClose's size bound with C₃, w8_patchInv. |
| nlw2_proof | All of the above plus w8_density, w8_dioph, w8_freqLimit; no hS/hSm. |

The two proofs with substantial changed routes were checked in the code: injectivity of DK follows from the differentiable left inverse at K(θ), with its smallness proved before differentiating; the positive real amplitude forces Re(h+DXh)=0, then the 1/2 norm bound forces h=0. Closeness uses the finite weighted tangential sum (bound 22), `(1/4+2π)√t e`, the normal part and π<3.15 to retain 162. The √2 transport loss is explicitly absorbed using √2·t^(3/2)≤t^(33/64) when 2t≤1. No conclusion-shaped premise is inserted in either source theorem.

## Definitions: body, carrier and choice

Every definition/abbreviation/structure appears individually in the inventory below. Classification by exhaustive groups:

| Group | Classification / assessment |
|---|---|
| W8UpstreamConsts; w8Upstream | Numerical parameter record plus actual upstream instance; four sign fields only, no hidden analytic conclusions. |
| Consts numerical definitions; w8EpsIn; w8T0W; w8Eps0W | Literal numerical formulas/aliases; all source uses at m>0 and the fixed actual instance. No shell/action-dependent widening of global constants. |
| w8tn/Rn/alpha/rn/rhoXi/rho/epsSharp/kappa/eps0/alphaHat/Pi | Literal shell formulas/predicate; strict infDist agrees with current W7 shellInner. |
| W8ShellPrep | Transparent source prep-hypothesis predicate, expanded above; not a disguised W8 conclusion. |
| w8ShellSeqData/Start/Gamma/Omega/Nu/Family/Excl/Etor/EpsOm/TorusKam | Actual W6 iteration and outputs, specialized to shell starting size; Family uses the repaired J family. Source H is constructed. |
| w8TK/Psi/Phase/Yact/Xang/XC, w8AA, w8HF | Actual source torus, components, errors, action-angle map and proved source input family; literal maps/aliases, no arbitrary witness selection. |
| w8Gam1, w8CubicG | Actual Birkhoff time-one map and cubic raw field waveShift∘waveGw; exact coordinate equation proved by w8CubicG_apply. |
| w8ShellIdx | Least shell via Nat.find, default 0 outside shell union. On positive-t₀ shell carrier existence and uniqueness follow from shell disjointness; w8ShellIdx_eq proves the full identification. No arbitrary non-unique family choice. |
| w8PatchSet/Nu/K; w8Gammas/Nus/GammaW/NuW/KW | Literal union/patch formulas; zero off Γ is explicitly prescribed by blueprint patch. At Γ the shell index is proved correct and source pieces are supplied. |
| w8KOfBirk and generic w8Kshell A H | Generic totalized wrappers; FAIL if asserted to define the source object on their unrestricted public carriers. No blanket source-definition PASS. |
| w8Kshell w8AA (w8HW hm n) restricted to ξ∈Γ_n | BODY_MATCH OK; PUBLIC_CARRIER OK on this source carrier; WELL_DEFINEDNESS OK by w8Psi_ball; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS on source carrier. Both source formulas proved; fallback unreachable. |

For all literal formula/alias groups other than the explicitly flagged unrestricted wrappers: BODY_MATCH OK; PUBLIC_CARRIER OK at the indicated source parameters; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS. For ShellIdx, its characterization on the source carrier is w8ShellIdx_eq, and choice independence is OK by uniqueness of shell membership. This audit does not claim that the generic off-source numerical or torus extensions encode additional manuscript objects.

## Mechanical checks and protection

Every Lean/Lake/leanchecker invocation initiated here was serialized under the exact user cap:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

1. **Provider kernel replay**, run independently because omitted by launcher:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env leanchecker --verbose KAM.Provider.Wave.Nlw2
```

Exit **0**; exact output `replaying KAM.Provider.Wave.Nlw2`. Log `/tmp/w8-audit2-provider-replay.log`. Assembly replay and name checks were already run by the launcher per the user's explicit instruction; their unseen output is not quoted or independently certified here. No redundant Assembly replay was needed.

2. **Targeted build**, through the serial W compile gate:

```sh
/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpr KAM.Provider.Wave.Nlw2
```

The driver wraps its single `lake build KAM.Provider.Wave.Nlw2` with the exact cap above. Exit **0**; final output `Build completed successfully (3796 jobs).` Log `/tmp/w8-audit2-build.log`. This target transitively covers every Assembly module. Cached upstream unused-simp warnings were printed; no W8 elaboration failure, heartbeat override, or memory failure occurred. No library-wide rebuild/clean was requested.

3. **Exact type / seal-copy / every-theorem axiom probe**:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/W8Audit2.lean
```

Exit **0**. Probe imports the anchor and provider only in scratch; it elaborates both
`example : type_of% @KAM.Wave.nlw2 := @KAM.Provider.Wave.nlw2` and
`example : type_of% @KAM.Wave.nlw2 := @KAM.Wave.nlw2_proof`.
It copies the entire frozen declaration under fresh name `w8AuditSeal`, replacing only the body with `by exact KAM.Provider.Wave.nlw2 hm` (hm is the only explicit outer binder). Lean metaprogram output:

```text
Expr equality proof=true, provider=true
```

`#print axioms` was run on every one of the 195 Assembly theorem names, the provider, and the seal-copy: **197 outputs, all exactly `[propext, Classical.choice, Quot.sound]`**. In particular:

```text
'KAM.Wave.nlw2_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Wave.nlw2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w8AuditSeal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Log `/tmp/w8-audit2-probe.log`. The inventory's axiom column `S` records this exact output for each individual theorem. The frozen draft itself was not promoted by this probe and still contains its one permitted sorry. Scratch source is deleted before handoff.

4. **Lint**, only through the mandated wrapper and itself run inside the cap (so any ABI subprocess inherits it):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpr
```

Exit **0**. Exact output:

```text
check_lean_modules: PASS (4042 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

Log `/tmp/w8-audit2-lint.log`. No generated-root exception was needed.

5. **Static protection / imports**. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Only the frozen anchor imports `KAM.Provider.Wave.Nlw2`. Source-import traversal of the 448 reachable KAM files from W8/provider found **no frozen theorem imports** and no illicit provider imports. Thus there is no transitive dependency on the draft anchor or another provider. Provider's required short name `nlw2` is the deliberate duplicate, not an unreviewed naming exception. The unchanged anchor already imports its registered provider, but its body is still `by sorry`.

`rg -n '\b(sorry|admit|axiom|unsafe|opaque)\b|set_option|EuclideanSpace' KAM/Wave/Assembly KAM/Provider/Wave/Nlw2.lean` has no matches. Every scoped file has the required module header/interface/docstring/public section; maximum length **375 lines** (ShellTorus). No forbidden root/generated/frozen edit was made by this auditor. The branch's Root/Wave addition is generated-root integration reported by the producer, not an auditor edit.

## Errata, deviations and uncertainty

No new mathematical falsehood in the pinned W8 blueprint was established. The handoff's alternate proof of derivative injectivity, sharper tangential estimate and explicit √2 accounting are proof-route variations with unchanged source conclusions. External monotonicity wrappers specialize the generic Mathlib theorem; full generic fact is not being re-proved. API splitting of w6-general and the generic totalized K wrapper are recorded above and must not be silently described as stronger statements.

The historical W7 inner-shell warning in PREP is stale at this snapshot: current shellInner uses strict infDist, and the required inner-shell inclusion is supplied directly. No old interface defect is carried forward as an open issue. Stale module prose should be updated by the owning prover/orchestrator; no implementation repair or ledger edit is authorized in this audit.

Validation is for the exact snapshot above and the W8 assembly/source-consumption boundary. W5 action-angle/initial, W6 iteration/tori, W7 measure and earlier analytic inputs retain their own independent source-audit obligations. Kernel replay and standard axioms do not discharge those semantic obligations. In particular this W8 verdict must not be represented as a fresh independent audit of those out-of-scope packages. No closure claim is made for the unsealed frozen export.

## Full declaration inventory

One row per public declaration command, with its source node or role. All theorem rows have axiom result `S = [propext, Classical.choice, Quot.sound]` from the live probe. `N/A` denotes a definition/abbreviation/structure, classified above. CONDITIONAL PASS validates a separately scoped helper, never a source-label substitution. Generic wrapper notes retain the unrestricted-carrier limitation described above.

| File:line | Declaration (kind) | Node / role | Verdict / reason | Axioms |
|---|---|---|---|---|
| Clauses.lean:51 | `w8_defect_rate_eq` (theorem) | nlw2-proof: density/Diophantine/limit | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Clauses.lean:60 | `w8tn_tendsto_rpow` (theorem) | nlw2-proof: density/Diophantine/limit | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Clauses.lean:72 | `w8_shell_defect` (theorem) | nlw2-proof: density/Diophantine/limit | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Clauses.lean:89 | `w8_density` (theorem) | nlw2-proof: density/Diophantine/limit | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Clauses.lean:107 | `w8NuW_of_mem` (theorem) | nlw2-proof: density/Diophantine/limit | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Clauses.lean:116 | `w8_dioph` (theorem) | nlw2-proof: density/Diophantine/limit | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Clauses.lean:138 | `w8_freqLimit` (theorem) | nlw2-proof: density/Diophantine/limit | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Consts.lean:43 | `W8UpstreamConsts` (structure) | const / shells | PASS as numerical record; actual constants supplied by w8Upstream. | N/A |
| Consts.lean:60 | `w8cA` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:63 | `w8CStar` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:66 | `w8CF` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:69 | `w8Rho1` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:72 | `w8CKp` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:75 | `w8M` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:78 | `w8SigmaP` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:81 | `w8Sigma0` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:86 | `w8E1` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:89 | `w8E3` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:92 | `w8E4` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:96 | `w8E5` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:99 | `w8E6` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:102 | `w8E7` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:106 | `w8T0` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:111 | `w8Tau` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:114 | `w8R0` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:117 | `w8C3` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:120 | `w8C` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:123 | `w8Eta` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:129 | `w8tn` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:132 | `w8Rn` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:135 | `w8alpha` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:138 | `w8rn` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:141 | `w8rhoXi` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:144 | `w8rho` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:147 | `w8epsSharp` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:151 | `w8kappa` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:155 | `w8eps0` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:159 | `w8alphaHat` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:163 | `w8Pi` (def) | const / shells | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Consts.lean:167 | `w8kappa_eq` (theorem) | const / shells | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Etor.lean:35 | `measTheta0_le_inv_eight_LA` (theorem) | etor | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Etor.lean:43 | `one_lt_measLA` (theorem) | etor | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Etor.lean:56 | `w8_rpow_one_sub_exp` (theorem) | etor | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Etor.lean:65 | `w8_etor` (theorem) | etor | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:39 | `w8ext_hasDerivAt_inner` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:47 | `w8ext_inner_eq_tsum` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:58 | `w8ext_summable_abs_mul` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:63 | `w8ext_tsum_add` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:68 | `w8ext_abs_inner_le` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:75 | `w8ext_antitoneOn_Icc` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:85 | `w8ext_monotoneOn_Icc` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:95 | `w8ext_hasDerivAt_exp_mul` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:106 | `w8ext_bounded_Icc` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:111 | `w8ext_continuous_of_analyticAt` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:118 | `w8ext_exp_eq_one_iff` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:123 | `w8ext_norm_exp_I` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:130 | `w8ext_const_of_intValued` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:156 | `w8ext_eq_zero_of_bounded_mul` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:167 | `w8ext_abs_sqrt_sub_le` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:187 | `w8ext_infDist` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:196 | `w8ext_rpow` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:202 | `w8ext_rpow_le_rpow` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:207 | `w8ext_tendsto_const_mul_rpow` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:218 | `w8ext_continuousOn_of_local` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:228 | `w8ext_clm_comp_analyticOnNhd` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:235 | `w8ext_fderiv_clm_comp` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Ext.lean:242 | `w8ext_le_of_tendsto` (theorem) | ext-inner through ext-local | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| FreqShell.lean:40 | `w8ShellGamma_subset` (theorem) | freq-shell | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| FreqShell.lean:45 | `w8ShellGamma_subset_Pi` (theorem) | freq-shell | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| FreqShell.lean:49 | `w8ShellGamma_subset_D` (theorem) | freq-shell | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| FreqShell.lean:60 | `w8ShellOmega_tendsto` (theorem) | freq-shell | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| FreqShell.lean:68 | `w8ShellGamma_measurableSet` (theorem) | freq-shell | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| FreqShell.lean:80 | `w8_freqShell` (theorem) | freq-shell | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| InjAssembly.lean:47 | `w8_injMod_of_phase` (theorem) | shell-embedding / injective reductions | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| InjAssembly.lean:68 | `w8_eq_zero_of_add_clm` (theorem) | shell-embedding / injective reductions | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| InjAssembly.lean:80 | `w8KOfBirk_eq_of_eq` (theorem) | shell-embedding / injective reductions | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| InjAssembly.lean:95 | `w8_freq_eq_of_shape` (theorem) | shell-embedding / injective reductions | CONDITIONAL PASS; distinct helper with explicit inputs, supplied at final source instance. | S |
| InjAssembly.lean:137 | `w8_injective_of_pieces` (theorem) | shell-embedding / injective reductions | CONDITIONAL PASS; distinct helper with explicit inputs, supplied at final source instance. | S |
| Nlw2Proof.lean:55 | `w8_tn_le_two_sum` (theorem) | nlw2-proof | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Nlw2Proof.lean:68 | `w8_close_arith` (theorem) | nlw2-proof | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Nlw2Proof.lean:91 | `w8_size_arith` (theorem) | nlw2-proof | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Nlw2Proof.lean:105 | `w8_patchClose` (theorem) | nlw2-proof | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Nlw2Proof.lean:129 | `nlw2_proof` (theorem) | nlw2-proof | PASS; exact frozen Expr type; all conjuncts supplied. | S |
| NuInj.lean:38 | `w8_freq_ne_of_shells` (theorem) | nu-injective reductions | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| NuInj.lean:70 | `w8PatchNu_injOn_of_pieces` (theorem) | nu-injective reductions | CONDITIONAL PASS; distinct helper with explicit inputs, supplied at final source instance. | S |
| Patch.lean:40 | `w8ShellIdx` (def) | patch / patch-local / patch-cont | PASS on source carrier; unique shell identification proved. | N/A |
| Patch.lean:45 | `w8PatchSet` (def) | patch / patch-local / patch-cont | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Patch.lean:49 | `w8PatchNu` (def) | patch / patch-local / patch-cont | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Patch.lean:56 | `w8PatchK` (def) | patch / patch-local / patch-cont | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Patch.lean:64 | `w8ShellIdx_eq` (theorem) | patch / patch-local / patch-cont | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Patch.lean:79 | `w8PatchSet_inter_w8Pi` (theorem) | patch / patch-local / patch-cont | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Patch.lean:88 | `w8ShellIdx_of_mem` (theorem) | patch / patch-local / patch-cont | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Patch.lean:93 | `w8PatchNu_of_mem` (theorem) | patch / patch-local / patch-cont | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Patch.lean:101 | `w8PatchK_of_mem` (theorem) | patch / patch-local / patch-cont | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Patch.lean:112 | `w8Patch_local` (theorem) | patch / patch-local / patch-cont | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Patch.lean:124 | `w8PatchSet_subset` (theorem) | patch / patch-local / patch-cont | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Patch.lean:137 | `continuousOn_w8PatchNu_of_pieces` (theorem) | patch / patch-local / patch-cont | CONDITIONAL PASS; distinct helper with explicit inputs, supplied at final source instance. | S |
| Patch.lean:150 | `continuousOn_w8PatchK_of_pieces` (theorem) | patch / patch-local / patch-cont | CONDITIONAL PASS; distinct helper with explicit inputs, supplied at final source instance. | S |
| Patch.lean:170 | `measurableSet_w8PatchSet_of_pieces` (theorem) | patch / patch-local / patch-cont | CONDITIONAL PASS; distinct helper with explicit inputs, supplied at final source instance. | S |
| PatchInst.lean:54 | `w8KOfBirk` (def) | source patch/frequency instances; generic K wrappers | GENERIC ONLY; unrestricted source-definition FAIL; source restriction discharged by w8Psi_ball. | N/A |
| PatchInst.lean:60 | `w8KOfBirk_of_mem` (theorem) | source patch/frequency instances; generic K wrappers | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| PatchInst.lean:67 | `w8KOfBirk_periodic` (theorem) | source patch/frequency instances; generic K wrappers | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| PatchInst.lean:75 | `w8Kshell` (def) | source patch/frequency instances; generic K wrappers | GENERIC ONLY for arbitrary A/H; actual w8AA/w8HW source instance PASS on Γ_n. | N/A |
| PatchInst.lean:89 | `w8Gammas` (def) | source patch/frequency instances; generic K wrappers | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| PatchInst.lean:93 | `w8Nus` (def) | source patch/frequency instances; generic K wrappers | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| PatchInst.lean:97 | `w8GammaW` (def) | source patch/frequency instances; generic K wrappers | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| PatchInst.lean:101 | `w8NuW` (def) | source patch/frequency instances; generic K wrappers | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| PatchInst.lean:105 | `w8KW` (def) | source patch/frequency instances; generic K wrappers | PASS at w8AA/w8HF source instance; generic formula alone asserts no torus property. | N/A |
| PatchInst.lean:109 | `w8Gammas_subset` (theorem) | source patch/frequency instances; generic K wrappers | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| PatchInst.lean:114 | `w8ShellNu_smul` (theorem) | source patch/frequency instances; generic K wrappers | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| PatchInst.lean:123 | `w8_patchLocal` (theorem) | source patch/frequency instances; generic K wrappers | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| PatchInst.lean:135 | `w8_patchCont` (theorem) | source patch/frequency instances; generic K wrappers | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| PatchInst.lean:146 | `w8_patchContK_of_pieces` (theorem) | source patch/frequency instances; generic K wrappers | CONDITIONAL PASS; distinct helper with explicit inputs, supplied at final source instance. | S |
| PatchInst.lean:154 | `w8_nuInjective` (theorem) | source patch/frequency instances; generic K wrappers | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellClose.lean:38 | `w8_tan_weights` (theorem) | shell-close | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellClose.lean:57 | `w8_tanDiff_hasSum` (theorem) | shell-close | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellClose.lean:79 | `w8_tanDiff_norm_le` (theorem) | shell-close | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellClose.lean:104 | `w8_coord_diff_le` (theorem) | shell-close | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellClose.lean:136 | `w8_birkSgn_real` (theorem) | shell-close | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellClose.lean:147 | `w8_birkPi_linearTorus` (theorem) | shell-close | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellClose.lean:153 | `w8_shellDist` (theorem) | shell-close | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellClose.lean:228 | `w8_gammaR_bounds` (theorem) | shell-close | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellClose.lean:254 | `w8_gamma_arith` (theorem) | shell-close | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellClose.lean:293 | `w8_tan_arith` (theorem) | shell-close | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellClose.lean:305 | `w8_shellClose` (theorem) | shell-close | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:33 | `w8CF_pos` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:35 | `w8M_pos` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:42 | `w8E1_ge_one` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:50 | `w8E3_pos` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:55 | `w8E4_pos` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:59 | `w8E5_pos` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:64 | `w8Rho1_pos` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:69 | `w8Alpha0_pos` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:78 | `w8T0_pos` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:91 | `w8T0_le` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:105 | `rpow_one_div_64_le_of_le_pow` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:112 | `w8tn_facts` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:125 | `w8alpha_le` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:143 | `w8rn_le` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:159 | `w8kappa_le` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:183 | `w8rho_sq_le` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellData.lean:207 | `w8_shellData_sizes` (theorem) | shell-data(i) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:44 | `w8AA` (def) | Kshell / shell-embedding | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellEmbed.lean:55 | `w8Kshell_eq` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:58 | `w8_birkPi_eq_reWave` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:62 | `w8_phase_int_of_eq` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:87 | `w8_exp_cancel` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:93 | `w8_coord_true` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:101 | `w8_sqrt_pos` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:108 | `w8Kshell_analytic` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:117 | `w8Kshell_injMod` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:137 | `w8Kshell_leftInv` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:146 | `w8Kshell_leftInv_hasFDerivAt` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:183 | `w8Kshell_fderiv_injective` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellEmbed.lean:324 | `w8_shellEmbedding` (theorem) | Kshell / shell-embedding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellFamily.lean:45 | `w8_birkEmbed_comp` (theorem) | shell-inv / patch-cont / injective | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellFamily.lean:61 | `w8HF` (abbrev) | shell-inv / patch-cont / injective | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellFamily.lean:64 | `w8ShellNu_eq` (theorem) | shell-inv / patch-cont / injective | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellFamily.lean:74 | `w8_shellInv` (theorem) | shell-inv / patch-cont / injective | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellFamily.lean:117 | `w8_shellInvCont` (theorem) | shell-inv / patch-cont / injective | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellFamily.lean:126 | `w8_patchContK` (theorem) | shell-inv / patch-cont / injective | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellFamily.lean:131 | `w8_patch_of_mem` (theorem) | shell-inv / patch-cont / injective | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellFamily.lean:139 | `w8_patchEmb` (theorem) | shell-inv / patch-cont / injective | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellFamily.lean:147 | `w8_patchInv` (theorem) | shell-inv / patch-cont / injective | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellFamily.lean:158 | `w8TK_continuous_real` (theorem) | shell-inv / patch-cont / injective | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellFamily.lean:168 | `w8_shell_freq_eq` (theorem) | shell-inv / patch-cont / injective | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellFamily.lean:193 | `w8_injective` (theorem) | shell-inv / patch-cont / injective | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:33 | `w8tn_pos` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:35 | `w8tn_le` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:39 | `w8alpha_pos` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:43 | `w8alpha_lt_tn` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:51 | `w8Rn_subset_box` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:54 | `boxIoo_subset_closedBall_half` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:62 | `w8Pi_eq` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:73 | `w8Pi_isOpen` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:77 | `w8Pi_measurableSet` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:81 | `w8Pi_subset_Rn` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:84 | `w8Pi_subset_ball` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:90 | `w8Pi_sep` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:95 | `w8Pi_coord` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:123 | `w8Rn_disjoint` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:131 | `w8Pi_disjoint` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:137 | `w8Pi_sep_of_ne` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:148 | `w8Pi_subset_shellInner` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:153 | `shellInner_subset_w8Pi_of_lt` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellGeom.lean:160 | `volume_w8Rn_diff_w8Pi_le` (theorem) | shell-data(ii) / boundaries | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellInit.lean:50 | `w8T0W` (abbrev) | shell-data(iii),(iv) | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellInit.lean:54 | `w8EpsIn` (def) | shell-data(iii),(iv) | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellInit.lean:60 | `W8ShellPrep` (abbrev) | shell-data(iii),(iv) | PASS as transparent input predicate; all fields produced in w8HW. | N/A |
| ShellInit.lean:67 | `w8EpsIn_le_pow` (theorem) | shell-data(iii),(iv) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellInit.lean:135 | `w8tn_quarter_pow` (theorem) | shell-data(iii),(iv) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellInit.lean:146 | `w8EpsIn_shell_le` (theorem) | shell-data(iii),(iv) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellInit.lean:161 | `w8lam_div_rhoXi` (theorem) | shell-data(iii),(iv) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellInit.lean:170 | `w8EpsIn_shell_sharp` (theorem) | shell-data(iii),(iv) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellInit.lean:185 | `w8_shellData_init` (theorem) | shell-data(iii),(iv) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellInit.lean:232 | `w8_famBound_sharp_of_initial` (theorem) | shell-data(iii),(iv) | CONDITIONAL PASS; distinct helper with explicit inputs, supplied at final source instance. | S |
| ShellInit.lean:248 | `w8_shellData_prep` (theorem) | shell-data(iii),(iv) | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellInit.lean:269 | `w8ShellPrep_of_initial` (theorem) | shell-data(iii),(iv) | CONDITIONAL PASS; distinct helper with explicit inputs, supplied at final source instance. | S |
| ShellInv.lean:40 | `w8Gam1` (abbrev) | shell-inv reductions | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellInv.lean:47 | `w8KOfBirk_eq_gamma` (theorem) | shell-inv reductions | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellInv.lean:58 | `w8_shellInv_of_birk` (theorem) | shell-inv reductions | CONDITIONAL PASS; distinct helper with explicit inputs, supplied at final source instance. | S |
| ShellInv.lean:80 | `w8_shellInvCont_of_birk` (theorem) | shell-inv reductions | CONDITIONAL PASS; distinct helper with explicit inputs, supplied at final source instance. | S |
| ShellIter.lean:53 | `w8Eps0W` (abbrev) | sharp-prep / shell-iter / w6-general | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellIter.lean:64 | `w8MeasSetup` (theorem) | sharp-prep / shell-iter / w6-general | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellIter.lean:70 | `w8_epsFlat_shell` (theorem) | sharp-prep / shell-iter / w6-general | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellIter.lean:125 | `w8ShellSeqData` (def) | sharp-prep / shell-iter / w6-general | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellIter.lean:130 | `w8ShellStart` (def) | sharp-prep / shell-iter / w6-general | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellIter.lean:135 | `w8ShellGamma` (def) | sharp-prep / shell-iter / w6-general | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellIter.lean:138 | `w8ShellOmega` (def) | sharp-prep / shell-iter / w6-general | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellIter.lean:142 | `w8ShellNu` (def) | sharp-prep / shell-iter / w6-general | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellIter.lean:147 | `w8ShellFamily` (def) | sharp-prep / shell-iter / w6-general | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellIter.lean:152 | `w8ShellExcl` (def) | sharp-prep / shell-iter / w6-general | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellIter.lean:157 | `w8ShellEtor` (def) | sharp-prep / shell-iter / w6-general | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellIter.lean:162 | `w8ShellEpsOm` (def) | sharp-prep / shell-iter / w6-general | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellIter.lean:167 | `w8ShellTorusKam` (def) | sharp-prep / shell-iter / w6-general | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellIter.lean:170 | `w8ShellGamma_eq` (theorem) | sharp-prep / shell-iter / w6-general | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellIter.lean:174 | `w8ShellEtor_eq` (theorem) | sharp-prep / shell-iter / w6-general | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellIter.lean:210 | `w8_sharpPrep` (theorem) | sharp-prep / shell-iter / w6-general | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellIter.lean:231 | `w8_w6General` (theorem) | sharp-prep / shell-iter / w6-general | PASS WITH NOTES; exact ε₁/ε₂, tori in separate theorem. | S |
| ShellIter.lean:255 | `w8ShellToriKam` (theorem) | sharp-prep / shell-iter / w6-general | PASS; unconditional W6 API, no StepSmooth premise. | S |
| ShellTorus.lean:48 | `w8_shellPi_bounds` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:63 | `w8_shellRho1` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:69 | `w8HW` (theorem) | source shell-data / torus-shape | PASS; constructs source H from hm and shell data. | S |
| ShellTorus.lean:75 | `w8TK` (abbrev) | source shell-data / torus-shape | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellTorus.lean:79 | `w8Psi` (def) | source shell-data / torus-shape | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellTorus.lean:84 | `w8_toriData` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:100 | `w8Phase` (def) | source shell-data / torus-shape | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellTorus.lean:103 | `w8Yact` (def) | source shell-data / torus-shape | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellTorus.lean:106 | `w8Xang` (def) | source shell-data / torus-shape | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellTorus.lean:109 | `w8XC` (def) | source shell-data / torus-shape | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| ShellTorus.lean:111 | `w8_strip_half_sub` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:115 | `w8TK_differentiableOn` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:120 | `w8TK_close` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:137 | `w8TK_real` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:145 | `w8XC_real` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:154 | `w8_torusShape_bounds` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:172 | `w8_shell_consts` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:198 | `w8_torusShape_real` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:213 | `w8_torusShape_coord` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:232 | `w8XC_periodic` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:244 | `w8_aaOfReal_add_int` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:249 | `w8Xang_periodic` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:263 | `w8Psi_periodic` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:280 | `w8_torusShape_deriv` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:300 | `w8Xang_lipschitz` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| ShellTorus.lean:327 | `w8Psi_ball` (theorem) | source shell-data / torus-shape | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Unique.lean:34 | `w8CubicG` (def) | unique / orbit reduction | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| Unique.lean:38 | `w8CubicG_apply` (theorem) | unique / orbit reduction | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Unique.lean:45 | `w8CubicG_sub_le` (theorem) | unique / orbit reduction | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Unique.lean:63 | `w8_deriv_fst_apply` (theorem) | unique / orbit reduction | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Unique.lean:75 | `w8_deriv_snd_apply` (theorem) | unique / orbit reduction | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Unique.lean:90 | `w8_eq_zero_of_abs_deriv_le` (theorem) | unique / orbit reduction | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Unique.lean:114 | `isAnalyticCoeffSolution_unique` (theorem) | unique / orbit reduction | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Unique.lean:199 | `w8_orbit_eq_of_meet` (theorem) | unique / orbit reduction | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| UpstreamW6.lean:30 | `w8Upstream` (def) | const upstream instance | PASS; literal formula/alias or actual upstream construction; see classification. | N/A |
| UpstreamW6.lean:40 | `w8Upstream_gam` (theorem) | const upstream instance | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| UpstreamW6.lean:42 | `w8Upstream_gam1` (theorem) | const upstream instance | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| UpstreamW6.lean:44 | `w8Upstream_cF` (theorem) | const upstream instance | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| UpstreamW6.lean:46 | `w8Upstream_cFnat` (theorem) | const upstream instance | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| UpstreamW6.lean:48 | `w8SigmaP_eq_w6` (theorem) | const upstream instance | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| UpstreamW6.lean:50 | `w8Sigma0_eq_w6` (theorem) | const upstream instance | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| UpstreamW6.lean:52 | `w8M_eq_w6` (theorem) | const upstream instance | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Winding.lean:26 | `winding_rate_eq` (theorem) | winding | PASS; stated source step or explicit auxiliary at displayed inputs. | S |
| Nlw2.lean:39 | `nlw2` (theorem) | frozen provider | PASS; exact frozen Expr type; body nlw2_proof hm. | S |

## Final snapshot check

While lint ran, another process advanced shared `inp` to `30e417df53c57aed5b634d7bb723210c0f7b274b`. Final merge base is `698fd38075bb3d814749ecfeae94a919cac3743e`; W8 diff SHA-256 is `e1f7fd9d296623840532c7355178cff2871ec4adce5d142124a86770678ee2a0` (238960 bytes). The original W8 diff hash is unchanged. Protected-path three-dot diff remains empty. HEAD and all audited source bytes remained unchanged; no branch update was performed by this auditor.

## Handoff

Auditor change: this report only. Temporary proof/type/axiom probe removed after validation; logs are under /tmp as named above. No state-changing git, source repair, seal, manifest, frozen or generated-root edit was performed. Overall W8/provider verdict is PASS WITH NOTES in the requested scope; the frozen anchor remains DRAFT_SORRY.
