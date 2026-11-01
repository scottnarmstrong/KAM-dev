# W8 independent package audit 1

Date: 2026-11-01. Auditor: maud-wpl-1. **Overall: FAIL for literal completion of the claimed W8 source labels; PASS WITH NOTES for the useful partial implementation.** The requested StepSmooth quarantine passes: the only W8 theorem taking those named W5 dependencies is distinctly named `w8ShellToriKam_of_stepSmooth`; no unconditional W8 source theorem silently binds them. This does not close W-NLW2.

## Snapshot and scope

Worktree `/root/code/KAM-inp-wpl` (the supplied `/mnt/.../KAM-inp-wpl` resolves here), HEAD `60cff5a8d54d3193da1af3070709c3524572617f`; comparison branch `inp` = `d3a2c262b6b99851b768298de443febdd8630cb5`. Reviewed `git diff inp...HEAD`, restricting semantic review to the 17 new `KAM/Wave/Assembly/*.lean` modules (2953 physical lines, 196 public declaration commands, including 136 theorems). W5/W6 implementations in the diff are outside D60 scope; imported interfaces were read only to identify W8 premises and applications. No result on another branch was used.

During the audit another process advanced `inp` to `5090562d4826c933407f5140aa2ea3e2fb32f5bc`. Final read-only verification found the same merge base `d3a2c262b6b99851b768298de443febdd8630cb5` and byte-identical W8 three-dot diff (152922 bytes, SHA-256 `9a934f50040b5f223269044a9b334930d087abedf86317815029020cfac8e2a9`). HEAD stayed unchanged. Protected-path comparison remained empty. No work was rebased or altered.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, both producer handoffs, `docs/tracks/W/W-STATEMENTS.md`, the relevant frozen Wave definitions/theorem, and `blueprint-W/parts/w8-assembly.tex`. Applied the lean-statement-audit skill for premise expansion, definition bodies, and promotion boundaries. The requested `docs/tracks/W/audits/W8-handoff.md` does not exist in this checkout or the main inp checkout. W8-PREP-handoff.md has no literal AUDIT FOCUS heading; its labels, deviations, and interface-defect sections were reviewed. All eight items of W8-ASM's AUDIT FOCUS were reviewed below.

The manifest entry `wave.nlw2.v1`, export `KAM.Wave.nlw2`, remains `DRAFT_SORRY`. No W8 provider or seal is supplied. **PROOF_STATUS: FROZEN_UNPROVED; no seal-ready verdict.** Provider/frozen-type and seal-body probes are inapplicable to this package. Frozen declaration fidelity is not being re-certified here.

“Unconditional PASS” below means a proved result at the displayed shell/preparatory input, with no unproduced StepSmooth premise. It does not mean the package constructs the source's initial perturbation, action-angle map, or the seven frozen witnesses from `m > 0` alone.

## Findings

### F1 — `w6-general` is not the literal blueprint result (FAIL)

Source: `blueprint-W/parts/w8-assembly.tex:212–217` specifies “ε₁ = 3γα_n, ε₂ = 4ε_{0,n}” and includes W6 tori among its conclusions. `ShellIter.lean:232–247` exports the source-facing `w8_w6General` with `IsFreqPair ... εω 0 (3γα_n + 4ε_{0,n}) θ`, and omits the tori conjunct. Its docstring records this as inherited W6-ITER D4, so the deviation is visible, but documentation does not establish equality to the pinned statement.

The error components are separate inputs to `IsFreqPair`; its expanded `h2_sup` (`Measure/Family.lean:61–63`) is `|Ω−Ω⁰| ≤ ε₁/L + ε₂/L^(1/2)`, with `L = normLab ν`. Moving `3γα_n` from ε₁ to ε₂ therefore replaces decay `L⁻¹` by `L⁻¹/²` for that term, a weaker estimate when L>1. This is not an equivalent rewriting. No W8 theorem restores the literal `IsFreqPair ... (3γα_n) (4ε_{0,n}) θ`. W7's ability to consume the altered admissible family explains why the density/frequency consequences still work, but does not prove the omitted source conclusion. The tori part is correctly quarantined as `w8ShellToriKam_of_stepSmooth`; it is CONDITIONAL, not source-label closure.

Required disposition: retain the altered result as distinctly scoped infrastructure, and either prove the exact label or obtain an explicit source revision/ruling for that change. The present user ruling permits conditional helpers for StepSmooth; it does not approve new frequency-error constants. No source falsity is asserted here, only a literal implementation/source mismatch.

### F2 — `Kshell` is a generic totalization, not the source definition (FAIL as a source label)

Source: `blueprint-W/parts/w8-assembly.tex:314–321` defines the actual shell torus, on `ξ ∈ Γ_n`, by `τ_E Γ^ℝ(𝒵⁻¹ Ψ̃_ξ(θ))`, “well defined by ... torus-shape(v).” `PatchInst.lean:54–58` instead defines `w8KOfBirk` for arbitrary `Ψ`, with `else 0` when `birkPi (Ψ θ)` is outside `birkRealBall1`. `w8Kshell` at lines 75–80 takes an arbitrary `A : ... → BirkSpace`, with no relation to the source action-angle map and no ball/reality proof. Even when `ξ ∈ Γ_n`, those inputs impose no restriction on `A`; choosing it constantly outside the ball activates the zero branch. Thus the fallback is reachable on the purported shell carrier, not just off Γ.

`w8KOfBirk_of_mem`, `w8KOfBirk_eq_gamma`, and `w8KOfBirk_eq_of_eq` prove correct restricted statements after adding the missing ball/reality premises. They do not establish those premises for `w8Kshell`. The handoff honestly says “done generically” and reports D4, which is sufficient to identify useful internal infrastructure but insufficient to pass the literal definition audit. No theorem asserting that these arbitrary objects are embeddings was found.

Definition assessment of `w8KOfBirk` / `w8Kshell` as `bpW:w8:Kshell`: BODY_MATCH FAIL; PUBLIC_CARRIER FAIL; WELL_DEFINEDNESS FAIL on the source shell instance; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT FAIL. As an explicitly documented internal total function, its conditional equations are sound. The generic `w8KW` has the same uninstantiated source-object dependency and is not a completed family of source tori.

Required disposition: keep the generic wrapper separate from the source object; construct the actual action-angle instance and prove every real shell point lies in the required ball, or use a carrier enforcing that fact. `torus-shape` is expressly unclaimed, so this is a completion boundary, not a demand to prove that label in this audit.

### N1 — partial labels and stale documentation

`shell-data` (iii) proves the numerical hypotheses of W5 initialPerturbation, but its concluding `X_P` bound is only `w8_famBound_sharp_of_initial`. Part (iv)'s complete perturbation bundle is only `w8ShellPrep_of_initial`. Neither constructs the actual initial perturbation. `patch-cont` proves Borel/inclusion/ν-continuity; its K-continuity is a conditional helper. `shell-embedding`, `shell-inv`, and family `injective` remain partial/conditional, as the handoff says. None may be recorded as an unconditional full source label.

W8-PREP's old W7 inner-shell defect is resolved in this snapshot: `Measure/Shells.lean:45` now uses the same strict `Metric.infDist` condition as `w8Pi`; the equality is `rfl`, and `w8_shell_defect` supplies W7's inner-shell inclusion directly. The PREP warning should not be propagated as an outstanding blocker here. The comments in Consts/Patch claiming upstream definitions have no Lean form are historical; UpstreamW6/ShellIter now supply them.

## Per-label verdicts

All names in this report are in `KAM.Wave` unless qualified otherwise.

| Blueprint label / part | Lean declaration(s) | Verdict | Scope / reason |
|---|---|---|---|
| ext-inner | w8ext_hasDerivAt_inner, w8ext_inner_eq_tsum, w8ext_summable_abs_mul, w8ext_tsum_add, w8ext_abs_inner_le | unconditional PASS | Same ℓ² inner product/absolute convergence; summable subtraction used directly from Mathlib where needed. |
| ext-mono | w8ext_antitoneOn_Icc, w8ext_monotoneOn_Icc, w8ext_hasDerivAt_exp_mul | PASS WITH NOTES | Correct closed-interval specialization, sufficient for W8; the generic interval fact remains Mathlib's. |
| ext-compact | w8ext_bounded_Icc, w8ext_continuous_of_analyticAt | unconditional PASS | Compact interval and Banach analytic continuity. |
| ext-exp | w8ext_exp_eq_one_iff, w8ext_norm_exp_I, w8ext_const_of_intValued, w8ext_eq_zero_of_bounded_mul | unconditional PASS | Period-one normalization and connected integer-valued argument match. |
| ext-sqrt | w8ext_abs_sqrt_sub_le | unconditional PASS | Exactly a>0, a+b≥0, denominator √a. |
| ext-dist | w8ext_infDist | unconditional PASS | Open strict-distance superlevel, zero on S, distance comparison. |
| ext-rpow | w8ext_rpow, w8ext_rpow_le_rpow, w8ext_tendsto_const_mul_rpow | unconditional PASS | Positive-base identities and limit at 0⁺. |
| ext-local | w8ext_continuousOn_of_local, w8ext_clm_comp_analyticOnNhd, w8ext_fderiv_clm_comp, w8ext_le_of_tendsto | unconditional PASS | Locality, linear composition, chain rule, limits. |
| const | Consts definitions instantiated by w8Upstream | unconditional PASS | Four upstream constants instantiated; constants fixed after m, before shell/action/angle. |
| shells | w8tn, w8Rn, w8alpha, w8rn, w8rhoXi, w8rho, w8epsSharp, w8kappa, w8eps0, w8alphaHat, w8Pi | unconditional PASS | q=1/2; exponents 95/64, 3/4, 4/3, 48/47, 44/47 match. |
| shell-data (i),(ii) | w8_shellData_sizes; ShellGeom lemmas | unconditional PASS | Full stated size/geometry bounds. |
| shell-data (iii), numerical hypotheses | w8_shellData_init | unconditional PASS | Exact ζ condition and radius inequality; no StepSmooth input. |
| shell-data (iii), X_P conclusion | w8_famBound_sharp_of_initial | CONDITIONAL | Assumes initial field bound; actual P not constructed here. |
| shell-data (iv), numerical hypotheses | w8_shellData_prep | unconditional PASS | Shell admissibility. |
| shell-data (iv), full perturbation | w8ShellPrep_of_initial | CONDITIONAL | Initial smoothing/periodicity/reality/field bounds remain inputs. |
| sharp-prep | w8_sharpPrep, w8_epsFlat_shell | unconditional PASS at source prep input | H is the source “run prep-step” premise, not its conclusion. |
| shell-iter | w8ShellSeqData/Start/Gamma/Omega/Nu/Family/Excl/Etor/EpsOm/TorusKam | PASS WITH NOTES / PARTIAL | Correct shell sequence and KAM-coordinate objects; source Ψ̃ including A not instantiated. |
| w6-general | w8_w6General | FAIL for literal label | F1: altered ε₁/ε₂; tori omitted. Applicable/exclusion/final-freq portions independently pass. |
| w6-general, W6 tori portion | w8ShellToriKam_of_stepSmooth | CONDITIONAL PASS as helper | Explicit hS,hSm; no unconditional tori promotion. |
| etor | w8_etor | unconditional PASS | E₄κ=E₅t^(1/64)≤7/256 and εω≤α/(70L_A)≤α. |
| freq-shell (i)–(iv) | w8_freqShell | unconditional PASS at source prep input | Limit of H1, co-Lipschitz bound, divisors, ν regularity, Borel set. |
| Kshell | w8Kshell, w8KOfBirk | FAIL as source definition | F2; only generic totalized construction. |
| patch, Γ/ν | w8GammaW, w8NuW | unconditional PASS at source prep family | Literal union and specified zero off Γ. |
| patch, K | w8KW | PARTIAL / source-instance not established | Generic patch formula passes, but source Kshell does not. |
| patch-local | w8Patch_local, w8_patchLocal | unconditional PASS for given pieces | Generic Ks allowed; requires only proved shell inclusion; no torus properties asserted. |
| patch-cont, Γ/inclusion/ν | w8_patchCont | unconditional PASS at source prep family | Actual frequency pieces supplied, no smoothness hypothesis. |
| patch-cont, K | w8_patchContK_of_pieces | CONDITIONAL | Per-shell joint continuity input; no source K continuity obtained. |
| boundaries | w8Pi_isOpen, w8Pi_disjoint, w8Pi_sep_of_ne, volume_w8Rn_diff_w8Pi_le | unconditional PASS | Strict margins and 7α_nt_n boundary cost. |
| unique | isAnalyticCoeffSolution_unique | unconditional PASS | Analytic coefficient solutions + common value only. |
| winding | winding_rate_eq | unconditional PASS | Positive amplitudes, continuous phases, bounded phase drift; period 1. |
| nu-injective | w8_nuInjective | unconditional PASS at source prep family | Same-shell lower bound and different-shell margins, all supplied in proof. |
| shell-embedding | w8_injMod_of_phase, w8_eq_zero_of_add_clm, w8KOfBirk_eq_of_eq, w8KOfBirk_periodic | PARTIAL | Correct individual reductions; no source embedding instance claimed/proved. |
| shell-inv | w8_shellInv_of_birk, w8_shellInvCont_of_birk | CONDITIONAL | Exact weak-field/real-ball/regularity input still needed. |
| injective | w8_injective_of_pieces; w8_freq_eq_of_shape; w8_orbit_eq_of_meet | CONDITIONAL / PARTIAL | Generic assembly and orbit/winding steps pass; missing source torus pieces explicit. |
| torus-shape; shell-close; nlw2-proof | none | NOT CLAIMED / NOT AUDITED FOR CLOSURE | User excludes these claims. Clauses supplies only density/Diophantine/frequency-limit substeps. |

## Hypothesis expansion and conditional quarantine

The following tables expose logical inputs; ordinary values and carriers (`m,n,P,X,ξ,θ`, functions, real constants, types and topological/vector-space instances) are TYPING. `hm : 0 < m` is STANDING (`bpW:w0:mass`) wherever present. There are no new project typeclasses/instances in W8. A table entry indexed by j or ξ represents the quantified predicate as written, not an additional premise for every value.

`W8ShellPrep` is exactly an abbreviation of `W6PrepHyp` at the shell data. Its logical fields expand as follows; each row is SOURCE for sharp-prep's “run Lemma prep-step” input (`w8-assembly.tex:178–185`, and shell-data iv at 144–147). They are not conclusions of the W8 labels being proved.

| Expanded logical input | Bin | Evidence |
|---|---|---|
| meas: Π_n measurable | SOURCE | prep-step parameter hypotheses |
| sub: ξ∈Π_n → ‖ξ‖≤1/2 | SOURCE | same |
| hα: 0<α_n | SOURCE | same |
| hα0: α_n≤α₀ | SOURCE | same |
| hr: 0<r_n | SOURCE | same |
| smooth.holoP on Π_n∖Ξ | SOURCE | P in smoothing Hamiltonian class |
| smooth.holoX on Π_n∖Ξ | SOURCE | same class |
| smooth.deriv_eq: derivative of P is pairing with X | SOURCE | Hamiltonian field identity; IsSmoothing definition |
| per: integer coordinate periodicity of P | SOURCE | real periodic perturbation premise |
| real: imaginary part of P vanishes at StepReal points | SOURCE | same |
| hε: 0<εsharp_n | SOURCE | positive majorant premise |
| hεγ: εsharp_n≤γα_n | SOURCE | smallness premise |
| bound: ε₀≥0 | SOURCE | FamBound decomposition |
| bound: ε₁≥0 | SOURCE | same |
| bound: ε₀+(α_n/M)ε₁≤εsharp_n | SOURCE | same |
| bound: sup kamNorm_r_n X≤ε₀ | SOURCE | same |
| bound: parameter difference norm≤ε₁‖ξ−ζ‖ | SOURCE | same |

Counts for this expanded H: SOURCE 17, STANDING 0, TYPING witness data ε₀,ε₁, RULED 0, EXCESS 0. Together with STANDING hm and TYPING m,n,P,X, this is the complete assumption schema of w8_sharpPrep, w8_w6General, w8_freqShell and their per-shell support results. Patched statements quantify a family of this same schema. H is not a proof that the actual W5 initial perturbation has been constructed.

| Additional input / declaration | Bin relative to full source label | Status |
|---|---|---|
| hS : W6StepSmooth, w8ShellToriKam_of_stepSmooth | RULED conditional dependency (user D60 audit scope) | Explicit named W5 obligation; expands to existence of holomorphic displacement, Φ=id+ιΨ, sup and derivative bounds for every unmodified StepHypSrc. |
| hSm : W6StepSmoothMod, same theorem | RULED conditional dependency | Same for modified StepHypModSrc. Counts RULED 2, EXCESS 0 under the conditional-helper ruling; never proved here. |
| hX, w8_famBound_sharp_of_initial | EXCESS for unconditional shell-data iii | Conditional helper, not label closure; ∀λ≥0, bound by ε_in(1+4λ/ρξ). |
| hsm,hper,hreal,hX, w8ShellPrep_of_initial | EXCESS for unconditional shell-data iv | Conditional helper. hsm expands to 3 class clauses, hper/hreal one each, hX to FamBound's 5 clauses for every λ. Ten logical input clauses; produces H rather than assuming H as conclusion. |
| hν, continuousOn_w8PatchNu_of_pieces | EXCESS for full patch-cont | Per-shell ν continuity; actual w8_patchCont supplies it using freq-shell. |
| hK, continuousOn_w8PatchK_of_pieces and w8_patchContK_of_pieces | EXCESS for full patch-cont | Per-shell joint K continuity; no source instance supplied. |
| hmeas, measurableSet_w8PatchSet_of_pieces | EXCESS for full patch-cont | Per-shell measurability; actual w8_patchCont supplies it. |
| hsame,hclose, w8PatchNu_injOn_of_pieces | EXCESS for full nu-injective | Both discharged inside w8_nuInjective using freq-shell. |
| hρ,hΨ,hb,hder,heq, w8_shellInv_of_birk | EXCESS for unconditional shell-inv | Five explicit predicates: reality, Birk ball, real ball, derivative, weak field identity. Distinct `_of_birk` name. |
| hc,hρ,hΨ,hb, w8_shellInvCont_of_birk | EXCESS for unconditional shell-inv ii | Four explicit predicates, distinct `_of_birk` name. |
| hemb.periodic, w8_injective_of_pieces | EXCESS for full injective | Source embedding conclusion assumed only in named assembly helper. |
| hemb.analytic, same | EXCESS | same |
| hemb.injectiveMod, same | EXCESS | same |
| hemb.injectiveDerivative, same | EXCESS | same |
| hinv.first coefficient equation, same | EXCESS | source invariance conclusion |
| hinv.second coefficient equation, same | EXCESS | same |
| hfreq: common orbit ⇒ equal ν, same | EXCESS | source winding/shape step |
| hνinj: InjOn ν Γ, same | EXCESS | source nu-injective conclusion; total 8 expanded clauses, helper only |

For `unique`, hY expands to analytic-at-every-t plus the two coefficient derivative equations; hY' gives the same three, and h0 is equality at 0. SOURCE 7, STANDING 1 (hm), RULED 0, EXCESS 0; all values/carriers are TYPING. No global Lipschitz/uniqueness conclusion is assumed. For `winding`, the four continuity premises, two positivity predicates, two bounded-drift predicates and common complex value identity are SOURCE 9; RULED 0, EXCESS 0. The positive-amplitude codomain is represented faithfully by real-valued functions plus pointwise positivity.

The other `_of_...` or explicitly step-scoped results (`w8_injMod_of_phase`, `w8_freq_eq_of_shape`, `w8_orbit_eq_of_meet`, `w8KOfBirk_eq_of_eq`, etc.) are correct local implications, not source-label substitutes. No alias exports an unconditional torus, embedding, shell invariance or family injectivity from the named StepSmooth hypotheses. The sole explicit W8 use is the last line of ShellIter: `H.w6ToriKam_of_stepSmooth hS hSm hlo hhi`.

## AUDIT FOCUS results and mathematical proof checks

1. **Initial-shell arithmetic:** ShellInit:185–225 concludes precisely the ζ condition in the handoff, with sup norm on `Fin 2 → ℂ`, real-part lower bound `2r_n²`, and `w8cA(t_n+r_n²)<w8Rho1²`. The x=t^(1/4) proof bounds x^6≤x^4 and x^7≤x^6 for 0<x≤1, and √2≤3/2, giving coefficient 6. EpsIn has the displayed blueprint formula. The W5-AA implementation is outside this snapshot/scope, so a term-level definitional equality probe against its unavailable `aaEpsIn` / `initialPerturbation` was not possible; no claim of that cross-branch compatibility is made.
2. **Prep input:** Expanded above. w8ShellPrep_of_initial restricts each input from Π_n to Π_n∖Ξ using membership `.1`; it does not assume the prep-step result or a torus as an input.
3. **Sharp comparison:** w8_epsFlat_shell uses ε/α=κγ, positivity of αcheck and κ, the exact rpow identity with exponent 48/47, and w6prep_size_arith. κ≤1 gives ε₀≤γ₁αcheck. No smoothness premise is needed for this numerical bound.
4. **W6 general:** F1. Applicable, exclusion, final-frequency are genuine term-level consumers. The altered frequency pair is sufficient for the subsequent general W7 consumer, but the exact blueprint frequency decomposition remains unpaid.
5. **Error bounds:** Etor:65–175 proves e≤E₄κ, equality E₄κ=E₅t^(1/64), the 7/256 cap, and εω≤α/(70L_A)≤α. Uses κ^(4/3)≤κ and αcheck≤α for α≤1, positivity of all divisors, `Real.pi_lt_d2` (π<3.15), and L_A>1. No dependence on arbitrary shell parameters is introduced into E₄,E₅.
6. **Frequency limit:** FreqShell:99–113 passes H1 to the limit, with both parameters in every D_μ and w6Seq_om_limit; θ≤θ₀. Co-Lipschitz bound subtracts θ₀≤1/(8L_A), giving 7/(8L_A). Frequency continuity is supplied directly from a Lipschitz estimate, bypassing the conditional tori theorem.
7. **Density:** Clauses:72–105 supplies W7's hinner by the literal infDist definition, the shell inclusion, and exclusion implication. `(95/64)(32/47)=95/94=1+1/94`; dividing by shell scale yields t^(1/94), hence defect→0. Diophantine normalization is αcheck/(8π) at exponent 24; frequency limit is λ_(i+1)/(2π). These are proved substeps only; nlw2-proof remains unclaimed.
8. **Return coordinates:** BirkReal and frozen WaveSpace are definitionally the same two real ℓ² factors; the scratch probe checks this by rfl. birkPi is continuous real-linear projection, inverse to birkZR only on real fixed points. w8KOfBirk_eq_gamma explicitly uses that reality identity; it is not silently assumed. Full Kshell still fails F2.

Uniqueness uses the squared Hilbert energy `‖D₁‖²+‖D₂‖²` even though WaveSpace's product norm is max; equivalence is not assumed. Each linear cancellation occurs in absolutely summable products of actual ℓ² derivative vectors, so no unjustified interchange with an unbounded λ multiplier occurs. The cubic estimate is local on bounded curves; compactness supplies the bound on each [-T,T]. Mathlib Gronwall is used for both time directions, yielding equality of solutions globally. Winding first cancels equal positive amplitudes, obtains integer-valued phase difference, uses connectedness, then boundedness of t(ν−ν') forces equality. Frequency injectivity uses positive shell margins and the exact frequency normalization.

## Definition classification

All 60 definition/abbreviation/structure commands are listed individually in the declaration inventory below. The following classification specifies the semantic result for each family, rather than treating existence of a codomain as a definition audit.

| Definitions | Classification and body/carrier assessment |
|---|---|
| W8UpstreamConsts | Internal record of four positive constants; no torus/proof output hidden as a field. PASS as parameter schema, not the source's fixed constants on its own. |
| w8Upstream | Literal actual W5/W6 constants plus their proved positivity; PASS; fixes the parameter record after m. |
| All scalar constants in Consts; w8T0W; w8Eps0W; w8EpsIn | Literal formulas, PASS on stated mathematical domain; no fallback or arbitrary selection. Constants with u remain parameterized formulas until w8Upstream is applied. |
| w8tn, w8Rn, w8alpha, w8rn, w8rhoXi, w8rho, w8epsSharp, w8kappa, w8eps0, w8alphaHat, w8Pi | Literal formulas/sets, PASS. shellT/shellSet and infDist definitions expanded. Division uses positive denominators at actual shell input. |
| w8ShellIdx | Internal index, Nat.find on actual shell membership, zero if no shell. PASS: unique on intended box by disjoint shells; index off that box is unobservable in the source ν/K formulas (they are zero there). No choice of a non-unique source object. |
| w8PatchSet, w8PatchNu, w8PatchK | Literal union and prescribed piecewise-zero formulas; PASS as operations on pieces satisfying the stated inclusion. The source explicitly specifies zero off Γ. |
| W8ShellPrep | Internal assumption abbreviation; not a manuscript-defined object or a proved result. Valid source input for sharp-prep; never counted as existence of actual P. |
| w8ShellSeqData, w8ShellStart | Literal specialization of imported W6 sequence/state definitions, PASS at H; no W8 choice or fallback. |
| w8ShellGamma, w8ShellOmega, w8ShellNu, w8ShellFamily, w8ShellExcl, w8ShellEtor, w8ShellEpsOm, w8ShellTorusKam | Literal imported sequence/limit/family constructions, PASS as relative objects at H; KAM torus is only Φ_P∘Φ_*, not the complete Ψ̃. Imported W6 implementation is an explicit audit boundary, not re-certified here. |
| w8Gammas, w8Nus, w8GammaW, w8NuW | Literal specialization of the preceding constructions and patch operations, PASS at H family. |
| w8KOfBirk, w8Kshell, w8KW | Generic totalized internal operations only; source Kshell FAIL (F2); source K part of patch remains PARTIAL. |
| w8Gam1 | Literal alias of actual W3 birkGamma at a=p=1; PASS. |
| w8CubicG | Literal waveShift(waveGw y), PASS on every real ℓ² input. w8CubicG_apply proves the full coordinate characterization; no fallback or deferred convergence claim. |

For the literal PASS definitions: BODY_MATCH OK (at the expressly indicated source/input domain), PUBLIC_CARRIER OK as the specified formula or internal operation, WELL_DEFINEDNESS N/A_LITERAL, CHARACTERIZATION N/A_LITERAL, CHOICE_INDEPENDENCE N/A. For the index selector: intended-domain existence/uniqueness follows from shell membership and disjointness; w8ShellIdx_eq is the characterization there. F2's separate FAIL cannot be waived by these PASS entries.

## Verification

D53 applied to every Lean/Lake invocation initiated in this audit, serially, via `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 ...`. No override, new provider, frozen edit, root regeneration, or state-changing git command was used.

Targeted builds used the D53 serial compile-gate driver (same slot lock files as inp_lake_build.sh; the older driver itself lacks the required cap):

```text
/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpl KAM.Wave.Assembly.Ext KAM.Wave.Assembly.Clauses KAM.Wave.Assembly.InjAssembly KAM.Wave.Assembly.ShellInv
```

Exit 0. Ext: `Build completed successfully (2609 jobs).`; Clauses: `Build completed successfully (3758 jobs).`; ShellInv: `Build completed successfully (3753 jobs).`; InjAssembly also completed successfully. These targets cover the import closure of all 17 W8 modules. Output contains replayed warnings from upstream Birkhoff/Cubic/Normal modules, not warnings in the audited W8 modules. No OOM/default-heartbeat failure occurred. Kernel replay and short-name checks were not rerun: user says launcher ran them, but its output is not visible, so no independent exit-code claim is made for them.

Prescribed lint command (run once, after the targeted builds, within the D53 cap):

```text
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpl > /tmp/maud-wpl-1-lint.log 2>&1
```

Exit 0; complete output:

```text
check_lean_modules: PASS (4009 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

No stale-root exception was needed. The opt-in lunar declarations were checked by file hash only, as explicitly reported by the lint; this audit does not certify their ABI by a new application build.

After lint fully exited, ran:

```text
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/W8Audit1.lean > /tmp/maud-wpl-1-axioms.log 2>&1
```

Exit 0. The scratch file imported all 17 audited modules and issued `#print axioms KAM.Wave.<name>` for each of the 136 theorem commands in the inventory below. Every emitted axiom set is a subset of `[propext, Classical.choice, Quot.sound]`; no sorryAx/project axiom. Axiom output was parsed to verify all 136 results and the allowed set. Exact distribution: 136 with `[propext, Classical.choice, Quot.sound]`. Axiom checks of conditional helpers establish correctness of the implications, not availability of their premises.

The same invocation elaborated these three independent probes (no output/errors):

```lean
example {m : ℝ} {hm : 0 < m} {Y Y' : ℝ → KAM.Wave.WaveSpace}
    (hY : KAM.Wave.IsAnalyticCoeffSolution m hm Y)
    (hY' : KAM.Wave.IsAnalyticCoeffSolution m hm Y') (h0 : Y 0 = Y' 0) : Y = Y' :=
  KAM.Wave.isAnalyticCoeffSolution_unique hY hY' h0
example {t0 : ℝ} (n : ℕ) : KAM.Wave.w8Pi t0 n =
    KAM.Wave.shellInner (1/2) t0 n (KAM.Wave.w8alpha t0 n) := rfl
example : KAM.Wave.BirkReal = KAM.Wave.WaveSpace := rfl
```

It also printed the fully elaborated signatures of `@w8_w6General`, `@w8ShellToriKam_of_stepSmooth`, `@w8_freqShell`, `@w8_nuInjective`, and `@w8_density`, confirming the first, third, fourth and fifth have only the source prep-input schema, while the second explicitly has both named StepSmooth premises. The probe was deleted after exit 0. Logs remain in `/tmp/maud-wpl-1-{lint,axioms}.log`.

Static checks: 17/17 files have copyright, module command, module docstring, public section and imports; largest file ShellInit.lean is 301 physical lines, below 1500. No forbidden proof escape/resource override or EuclideanSpace found in these modules. Every new public theorem is included in the axiom probe inventory (136). No provider or frozen theorem is directly imported by a W8 module; the clean axiom closure additionally checks no proof hole was consumed transitively.

`git diff --name-only inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Adding `KAM/Root` reports `KAM/Root/Wave.lean` (160 added generated imports, including 17 W8 modules and the out-of-scope W5/W6 modules). This is a disclosed existing generated-root change, not an auditor edit. Both handoffs report generator use, consistent with AGENTS rule 10; byte-diff evidence alone cannot independently prove how it was generated. No generated root was regenerated for this audit.

Snapshot source SHA-256: dfe5c696903edc33308c3dcbe38198c872f3bfa71e2de61cd39573fffdda46f0. Producer handoff SHA-256: PREP 3225eac54bb126b361791d92a184fc24f205434866ef57887431c85de6593c44, ASM c26f0aae67de0ecc21d47f5c27a5218162ea1e0b14f3227c168b5c0169860cee.

## Complete declaration inventory

One row per public declaration command, including internal helpers; “PASS” for a conditional helper means correctness as that implication, never source closure. `SOURCE FAIL` identifies the two literal source issues. File names refer to `KAM/Wave/Assembly/`; namespace is `KAM.Wave`.

| File:line | Declaration | Verdict | Reason / scope |
|---|---|---|---|
| Clauses.lean:51 | `w8_defect_rate_eq` (theorem) | PASS | Proved density/frequency substep at H family; no nlw2 closure. |
| Clauses.lean:60 | `w8tn_tendsto_rpow` (theorem) | PASS | Proved density/frequency substep at H family; no nlw2 closure. |
| Clauses.lean:72 | `w8_shell_defect` (theorem) | PASS | Proved density/frequency substep at H family; no nlw2 closure. |
| Clauses.lean:89 | `w8_density` (theorem) | PASS | Proved density/frequency substep at H family; no nlw2 closure. |
| Clauses.lean:107 | `w8NuW_of_mem` (theorem) | PASS | Proved density/frequency substep at H family; no nlw2 closure. |
| Clauses.lean:116 | `w8_dioph` (theorem) | PASS | Proved density/frequency substep at H family; no nlw2 closure. |
| Clauses.lean:138 | `w8_freqLimit` (theorem) | PASS | Proved density/frequency substep at H family; no nlw2 closure. |
| Consts.lean:43 | `W8UpstreamConsts` (structure) | INTERNAL PASS | Positive-constant parameter record; actual instance w8Upstream supplied. |
| Consts.lean:60 | `w8cA` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:63 | `w8CStar` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:66 | `w8CF` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:69 | `w8Rho1` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:72 | `w8CKp` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:75 | `w8M` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:78 | `w8SigmaP` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:81 | `w8Sigma0` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:86 | `w8E1` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:89 | `w8E3` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:92 | `w8E4` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:96 | `w8E5` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:99 | `w8E6` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:102 | `w8E7` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:106 | `w8T0` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:111 | `w8Tau` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:114 | `w8R0` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:117 | `w8C3` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:120 | `w8C` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:123 | `w8Eta` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:129 | `w8tn` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:132 | `w8Rn` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:135 | `w8alpha` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:138 | `w8rn` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:141 | `w8rhoXi` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:144 | `w8rho` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:147 | `w8epsSharp` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:151 | `w8kappa` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:155 | `w8eps0` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:159 | `w8alphaHat` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:163 | `w8Pi` (def) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Consts.lean:167 | `w8kappa_eq` (theorem) | PASS | Literal scalar/shell formula or arithmetic identity; u instantiated in UpstreamW6. |
| Etor.lean:35 | `measTheta0_le_inv_eight_LA` (theorem) | PASS | Unconditional numerical shell/error estimate. |
| Etor.lean:43 | `one_lt_measLA` (theorem) | PASS | Unconditional numerical shell/error estimate. |
| Etor.lean:56 | `w8_rpow_one_sub_exp` (theorem) | PASS | Unconditional numerical shell/error estimate. |
| Etor.lean:65 | `w8_etor` (theorem) | PASS | Unconditional numerical shell/error estimate. |
| Ext.lean:39 | `w8ext_hasDerivAt_inner` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:47 | `w8ext_inner_eq_tsum` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:58 | `w8ext_summable_abs_mul` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:63 | `w8ext_tsum_add` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:68 | `w8ext_abs_inner_le` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:75 | `w8ext_antitoneOn_Icc` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:85 | `w8ext_monotoneOn_Icc` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:95 | `w8ext_hasDerivAt_exp_mul` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:106 | `w8ext_bounded_Icc` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:111 | `w8ext_continuous_of_analyticAt` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:118 | `w8ext_exp_eq_one_iff` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:123 | `w8ext_norm_exp_I` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:130 | `w8ext_const_of_intValued` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:156 | `w8ext_eq_zero_of_bounded_mul` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:167 | `w8ext_abs_sqrt_sub_le` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:187 | `w8ext_infDist` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:196 | `w8ext_rpow` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:202 | `w8ext_rpow_le_rpow` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:207 | `w8ext_tendsto_const_mul_rpow` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:218 | `w8ext_continuousOn_of_local` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:228 | `w8ext_clm_comp_analyticOnNhd` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:235 | `w8ext_fderiv_clm_comp` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| Ext.lean:242 | `w8ext_le_of_tendsto` (theorem) | PASS | External calculus/topology/algebra fact under explicit local premises. |
| FreqShell.lean:40 | `w8ShellGamma_subset` (theorem) | PASS | Actual shell-frequency consequence at source prep input H. |
| FreqShell.lean:45 | `w8ShellGamma_subset_Pi` (theorem) | PASS | Actual shell-frequency consequence at source prep input H. |
| FreqShell.lean:49 | `w8ShellGamma_subset_D` (theorem) | PASS | Actual shell-frequency consequence at source prep input H. |
| FreqShell.lean:60 | `w8ShellOmega_tendsto` (theorem) | PASS | Actual shell-frequency consequence at source prep input H. |
| FreqShell.lean:68 | `w8ShellGamma_measurableSet` (theorem) | PASS | Actual shell-frequency consequence at source prep input H. |
| FreqShell.lean:80 | `w8_freqShell` (theorem) | PASS | Actual shell-frequency consequence at source prep input H. |
| InjAssembly.lean:47 | `w8_injMod_of_phase` (theorem) | PASS | Generic local embedding/winding step; source torus instance not supplied. |
| InjAssembly.lean:68 | `w8_eq_zero_of_add_clm` (theorem) | PASS | Generic local embedding/winding step; source torus instance not supplied. |
| InjAssembly.lean:80 | `w8KOfBirk_eq_of_eq` (theorem) | PASS | Generic local embedding/winding step; source torus instance not supplied. |
| InjAssembly.lean:95 | `w8_freq_eq_of_shape` (theorem) | PASS | Generic local embedding/winding step; source torus instance not supplied. |
| InjAssembly.lean:137 | `w8_injective_of_pieces` (theorem) | CONDITIONAL PASS | Named internal helper; inputs exposed in hypothesis table; no source-label substitution. |
| NuInj.lean:38 | `w8_freq_ne_of_shells` (theorem) | PASS | Frequency separation/assembly step for supplied pieces. |
| NuInj.lean:70 | `w8PatchNu_injOn_of_pieces` (theorem) | CONDITIONAL PASS | Named internal helper; inputs exposed in hypothesis table; no source-label substitution. |
| Patch.lean:40 | `w8ShellIdx` (def) | PASS | Literal patch operation or local identity on supplied pieces. |
| Patch.lean:45 | `w8PatchSet` (def) | PASS | Literal patch operation or local identity on supplied pieces. |
| Patch.lean:49 | `w8PatchNu` (def) | PASS | Literal patch operation or local identity on supplied pieces. |
| Patch.lean:56 | `w8PatchK` (def) | PASS | Literal patch operation or local identity on supplied pieces. |
| Patch.lean:64 | `w8ShellIdx_eq` (theorem) | PASS | Literal patch operation or local identity on supplied pieces. |
| Patch.lean:79 | `w8PatchSet_inter_w8Pi` (theorem) | PASS | Literal patch operation or local identity on supplied pieces. |
| Patch.lean:88 | `w8ShellIdx_of_mem` (theorem) | PASS | Literal patch operation or local identity on supplied pieces. |
| Patch.lean:93 | `w8PatchNu_of_mem` (theorem) | PASS | Literal patch operation or local identity on supplied pieces. |
| Patch.lean:101 | `w8PatchK_of_mem` (theorem) | PASS | Literal patch operation or local identity on supplied pieces. |
| Patch.lean:112 | `w8Patch_local` (theorem) | PASS | Literal patch operation or local identity on supplied pieces. |
| Patch.lean:124 | `w8PatchSet_subset` (theorem) | PASS | Literal patch operation or local identity on supplied pieces. |
| Patch.lean:137 | `continuousOn_w8PatchNu_of_pieces` (theorem) | CONDITIONAL PASS | Named internal helper; inputs exposed in hypothesis table; no source-label substitution. |
| Patch.lean:150 | `continuousOn_w8PatchK_of_pieces` (theorem) | CONDITIONAL PASS | Named internal helper; inputs exposed in hypothesis table; no source-label substitution. |
| Patch.lean:170 | `measurableSet_w8PatchSet_of_pieces` (theorem) | CONDITIONAL PASS | Named internal helper; inputs exposed in hypothesis table; no source-label substitution. |
| PatchInst.lean:54 | `w8KOfBirk` (def) | SOURCE FAIL | F2: generic A/Ψ and reachable zero fallback; conditional equations only. |
| PatchInst.lean:60 | `w8KOfBirk_of_mem` (theorem) | PASS | Shell-family specialization at H; K pieces remain generic. |
| PatchInst.lean:67 | `w8KOfBirk_periodic` (theorem) | PASS | Shell-family specialization at H; K pieces remain generic. |
| PatchInst.lean:75 | `w8Kshell` (def) | SOURCE FAIL | F2: generic A/Ψ and reachable zero fallback; conditional equations only. |
| PatchInst.lean:89 | `w8Gammas` (def) | PASS | Shell-family specialization at H; K pieces remain generic. |
| PatchInst.lean:93 | `w8Nus` (def) | PASS | Shell-family specialization at H; K pieces remain generic. |
| PatchInst.lean:97 | `w8GammaW` (def) | PASS | Shell-family specialization at H; K pieces remain generic. |
| PatchInst.lean:101 | `w8NuW` (def) | PASS | Shell-family specialization at H; K pieces remain generic. |
| PatchInst.lean:105 | `w8KW` (def) | PARTIAL | Patch formula correct, source K pieces not established (F2). |
| PatchInst.lean:109 | `w8Gammas_subset` (theorem) | PASS | Shell-family specialization at H; K pieces remain generic. |
| PatchInst.lean:114 | `w8ShellNu_smul` (theorem) | PASS | Shell-family specialization at H; K pieces remain generic. |
| PatchInst.lean:123 | `w8_patchLocal` (theorem) | PASS | Shell-family specialization at H; K pieces remain generic. |
| PatchInst.lean:135 | `w8_patchCont` (theorem) | PASS | Shell-family specialization at H; K pieces remain generic. |
| PatchInst.lean:146 | `w8_patchContK_of_pieces` (theorem) | CONDITIONAL PASS | Named internal helper; inputs exposed in hypothesis table; no source-label substitution. |
| PatchInst.lean:154 | `w8_nuInjective` (theorem) | PASS | Shell-family specialization at H; K pieces remain generic. |
| ShellData.lean:33 | `w8CF_pos` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:35 | `w8M_pos` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:42 | `w8E1_ge_one` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:50 | `w8E3_pos` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:55 | `w8E4_pos` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:59 | `w8E5_pos` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:64 | `w8Rho1_pos` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:69 | `w8Alpha0_pos` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:78 | `w8T0_pos` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:91 | `w8T0_le` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:105 | `rpow_one_div_64_le_of_le_pow` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:112 | `w8tn_facts` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:125 | `w8alpha_le` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:143 | `w8rn_le` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:159 | `w8kappa_le` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:183 | `w8rho_sq_le` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellData.lean:207 | `w8_shellData_sizes` (theorem) | PASS | Positive-constant arithmetic and shell-size bounds. |
| ShellGeom.lean:33 | `w8tn_pos` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:35 | `w8tn_le` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:39 | `w8alpha_pos` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:43 | `w8alpha_lt_tn` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:51 | `w8Rn_subset_box` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:54 | `boxIoo_subset_closedBall_half` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:62 | `w8Pi_eq` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:73 | `w8Pi_isOpen` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:77 | `w8Pi_measurableSet` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:81 | `w8Pi_subset_Rn` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:84 | `w8Pi_subset_ball` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:90 | `w8Pi_sep` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:95 | `w8Pi_coord` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:123 | `w8Rn_disjoint` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:131 | `w8Pi_disjoint` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:137 | `w8Pi_sep_of_ne` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:148 | `w8Pi_subset_shellInner` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:153 | `shellInner_subset_w8Pi_of_lt` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellGeom.lean:160 | `volume_w8Rn_diff_w8Pi_le` (theorem) | PASS | Actual infDist shell geometry and boundary estimate. |
| ShellInit.lean:50 | `w8T0W` (abbrev) | PASS | Shell initial/preparatory arithmetic or explicitly named initial-input implication. |
| ShellInit.lean:54 | `w8EpsIn` (def) | PASS | Shell initial/preparatory arithmetic or explicitly named initial-input implication. |
| ShellInit.lean:60 | `W8ShellPrep` (abbrev) | INPUT SCHEMA | Expanded source prep-step hypotheses, not a result or constructed perturbation. |
| ShellInit.lean:67 | `w8EpsIn_le_pow` (theorem) | PASS | Shell initial/preparatory arithmetic or explicitly named initial-input implication. |
| ShellInit.lean:135 | `w8tn_quarter_pow` (theorem) | PASS | Shell initial/preparatory arithmetic or explicitly named initial-input implication. |
| ShellInit.lean:146 | `w8EpsIn_shell_le` (theorem) | PASS | Shell initial/preparatory arithmetic or explicitly named initial-input implication. |
| ShellInit.lean:161 | `w8lam_div_rhoXi` (theorem) | PASS | Shell initial/preparatory arithmetic or explicitly named initial-input implication. |
| ShellInit.lean:170 | `w8EpsIn_shell_sharp` (theorem) | PASS | Shell initial/preparatory arithmetic or explicitly named initial-input implication. |
| ShellInit.lean:185 | `w8_shellData_init` (theorem) | PASS | Shell initial/preparatory arithmetic or explicitly named initial-input implication. |
| ShellInit.lean:232 | `w8_famBound_sharp_of_initial` (theorem) | CONDITIONAL PASS | Named internal helper; inputs exposed in hypothesis table; no source-label substitution. |
| ShellInit.lean:248 | `w8_shellData_prep` (theorem) | PASS | Shell initial/preparatory arithmetic or explicitly named initial-input implication. |
| ShellInit.lean:269 | `w8ShellPrep_of_initial` (theorem) | CONDITIONAL PASS | Named internal helper; inputs exposed in hypothesis table; no source-label substitution. |
| ShellInv.lean:40 | `w8Gam1` (abbrev) | PASS | Return-coordinate reduction; source torus instance absent. |
| ShellInv.lean:47 | `w8KOfBirk_eq_gamma` (theorem) | PASS | Return-coordinate reduction; source torus instance absent. |
| ShellInv.lean:58 | `w8_shellInv_of_birk` (theorem) | CONDITIONAL PASS | Named internal helper; inputs exposed in hypothesis table; no source-label substitution. |
| ShellInv.lean:80 | `w8_shellInvCont_of_birk` (theorem) | CONDITIONAL PASS | Named internal helper; inputs exposed in hypothesis table; no source-label substitution. |
| ShellIter.lean:54 | `w8Eps0W` (abbrev) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:65 | `w8MeasSetup` (theorem) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:71 | `w8_epsFlat_shell` (theorem) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:126 | `w8ShellSeqData` (def) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. KAM coordinates only. |
| ShellIter.lean:131 | `w8ShellStart` (def) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. KAM coordinates only. |
| ShellIter.lean:136 | `w8ShellGamma` (def) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:139 | `w8ShellOmega` (def) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:143 | `w8ShellNu` (def) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:148 | `w8ShellFamily` (def) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:153 | `w8ShellExcl` (def) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:158 | `w8ShellEtor` (def) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:163 | `w8ShellEpsOm` (def) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:168 | `w8ShellTorusKam` (def) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. KAM coordinates only. |
| ShellIter.lean:171 | `w8ShellGamma_eq` (theorem) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:175 | `w8ShellEtor_eq` (theorem) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:211 | `w8_sharpPrep` (theorem) | PASS | Shell-specialized W6 input/sequence/arithmetic; no full source torus claim. |
| ShellIter.lean:232 | `w8_w6General` (theorem) | SOURCE FAIL | F1: changed frequency-error decomposition and incomplete full label. |
| ShellIter.lean:256 | `w8ShellToriKam_of_stepSmooth` (theorem) | CONDITIONAL PASS | Named internal helper; inputs exposed in hypothesis table; no source-label substitution. |
| Unique.lean:34 | `w8CubicG` (def) | PASS | Coefficient dynamics/energy estimate/uniqueness step. |
| Unique.lean:38 | `w8CubicG_apply` (theorem) | PASS | Coefficient dynamics/energy estimate/uniqueness step. |
| Unique.lean:45 | `w8CubicG_sub_le` (theorem) | PASS | Coefficient dynamics/energy estimate/uniqueness step. |
| Unique.lean:63 | `w8_deriv_fst_apply` (theorem) | PASS | Coefficient dynamics/energy estimate/uniqueness step. |
| Unique.lean:75 | `w8_deriv_snd_apply` (theorem) | PASS | Coefficient dynamics/energy estimate/uniqueness step. |
| Unique.lean:90 | `w8_eq_zero_of_abs_deriv_le` (theorem) | PASS | Coefficient dynamics/energy estimate/uniqueness step. |
| Unique.lean:114 | `isAnalyticCoeffSolution_unique` (theorem) | PASS | Coefficient dynamics/energy estimate/uniqueness step. |
| Unique.lean:199 | `w8_orbit_eq_of_meet` (theorem) | PASS | Coefficient dynamics/energy estimate/uniqueness step. |
| UpstreamW6.lean:30 | `w8Upstream` (def) | PASS | Actual fixed upstream constants or definitional compatibility. |
| UpstreamW6.lean:40 | `w8Upstream_gam` (theorem) | PASS | Actual fixed upstream constants or definitional compatibility. |
| UpstreamW6.lean:42 | `w8Upstream_gam1` (theorem) | PASS | Actual fixed upstream constants or definitional compatibility. |
| UpstreamW6.lean:44 | `w8Upstream_cF` (theorem) | PASS | Actual fixed upstream constants or definitional compatibility. |
| UpstreamW6.lean:46 | `w8Upstream_cFnat` (theorem) | PASS | Actual fixed upstream constants or definitional compatibility. |
| UpstreamW6.lean:48 | `w8SigmaP_eq_w6` (theorem) | PASS | Actual fixed upstream constants or definitional compatibility. |
| UpstreamW6.lean:50 | `w8Sigma0_eq_w6` (theorem) | PASS | Actual fixed upstream constants or definitional compatibility. |
| UpstreamW6.lean:52 | `w8M_eq_w6` (theorem) | PASS | Actual fixed upstream constants or definitional compatibility. |
| Winding.lean:26 | `winding_rate_eq` (theorem) | PASS | Exact winding-rate result. |

## Handoff and disposition

Auditor repository change: this report only; transient probes under `.lake/abi-scratch/` were deleted after checking. No mathematical repair attempted. F1 and F2 prevent a blanket literal-source PASS. The StepSmooth naming/quarantine request itself passes, and the unconditional arithmetic, frequency, uniqueness, winding and density subresults are usable within their stated input scope. Source claims torus-shape, shell-close and nlw2-proof remain unclaimed.

Suspected source/blueprint defects: no new mathematical falsehood established. F1 is an implementation deviation from the exact quoted blueprint constants, to be recorded/decided by the orchestrator rather than silently changing the source. F2 is an implementation carrier/definition mismatch. PREP's historical W7 interface defect is fixed at the audited dependency version. The absent combined handoff and missing PREP AUDIT FOCUS heading limit evidence to the available documents; no approval was inferred from an unavailable file.
