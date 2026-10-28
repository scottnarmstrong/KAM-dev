# P23-18 independent package audit 1

Overall verdict: **FAIL — public-name collision prevents integration.** The private mathematical helpers pass the scoped statement/applicability review, but the explicit AUDIT FOCUS requirement “no public name already used elsewhere in KAM” fails. No frozen anchor is proved by this package, so provider/frozen-type equality and seal-body probes are **not applicable**; this is not a seal-ready verdict for P-G or `two_scale_kam`.

Snapshot: HEAD `0e8f8536a2f3557ed967edeb55956f9cf182484c`; `inp` at comparison `b5f37af202b6262fa6521c90a58854b4d58b3555`. Ran `git diff inp...HEAD`; Git warned `multiple merge bases, using 31f0bfbf70c07b1eefd006237f331c00e003a0e5`. As explicitly instructed, audited only the ten `KAM/Planetary/TwoScale/LimitMap*.lean` files (1677 lines total; largest 294); ignored other branch-diff files, including the already-audited P23-17 implementation. The pre-existing untracked P23-18 handoff was preserved. Only this report is a persistent repository edit. The user's exact worktree report destination overrides the common brief's main-worktree destination.

Read AGENTS.md, PLAN, DECISIONS, common audit brief, handoff/AUDIT FOCUS, P23 design row P23-18/N2/private release gate, P23-17 audit, track-P statement, P3b L43–95, `Iteration.lean`, upstream action-limit interface, frozen `Phase`/`actionNbhd` and the coefficient-domain/real-tube/block definitions. Inspected frozen P-G only for scope; it is not an imported premise. The signature file is absent at this checkout's `.drafts/design/P23Signatures.lean`; read the explicitly referenced authoritative copy at `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` (SHA256 `d067d47dbabfdf4913da3e2b76886eb29598f4502ad16318d328568d82380cd3`). P3b SHA256 `e923c1f3856cd7c27fc73b1a5bdb21139a31d0484e30421c4e0db9cfdff86c1a`. This audits the local blueprint/design contract; no fresh external-source/PDF audit is claimed.

## Blocking finding F1: duplicate exported declaration

`LimitMapScale.lean:83` introduces public `KAM.Planetary.norm_append_le`, already declared publicly at `KAM/Planetary/PGMeasure/ResonanceFast/Pullback.lean:35` (also present in current `inp`). These have different signatures: the new lemma is generic in the coefficient normed group and appends two equally sized blocks to bound their norm by their maximum; the existing lemma handles possibly unequal real blocks and assumes a common upper bound. They cannot coexist under one global Lean name.

Independent co-import probe:

```lean
import KAM.Planetary.PGMeasure.ResonanceFast.Pullback
import KAM.Planetary.TwoScale.LimitMap
#check KAM.Planetary.norm_append_le
```

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2318Coimport.lean
```

Exit **1**, exact output:

```text
.lake/abi-scratch/P2318Coimport.lean:1:0: error: import KAM.Planetary.TwoScale.LimitMapScale failed, environment already contains 'KAM.Planetary.norm_append_le' from KAM.Planetary.PGMeasure.ResonanceFast.Pullback
```

Required repair: give the new scaling helper a fresh qualified name (or place it in a dedicated namespace) and update its use in `norm_sc`, then rerun this probe and the targeted checks. No repair was made under this report-only brief. A namespace-aware scan found no other duplicate among the 77 audited declarations. The targeted package build alone does not exercise this co-import.

## PsiSteps field expansion and shared-witness applicability

`PsiSteps` (`LimitMapPsi.lean:40–75`) is a transparent Prop structure with **15 fields**, all derived from ONE `iterative H` tuple `(Ds, hs, fs, Ψ, Φ, is)`. None assumes a limit, composed defect bound, summability, uniform convergence, injectivity of the limit, or analytic extension. The following table accounts for every field; line references in the producer column are to `Iteration.lean`.

| Field | Produced output | Projection in `iterative_steps` (Psi L87–91) |
|---|---|---|
| `hyp` | L35, stage `KamHyp` | `hK` |
| `Phi_zero` | L34, `Φ 0 = id` | `h3` |
| `Phi_succ` | L36, composition | `hP` |
| `phi_diff` | L50, complex differentiability | `(hPh j).1` |
| `phi_real` | L51–52, real range | `(hPh j).2.2.1` |
| `phi_per` | L53–54, full lattice identity | `(hPh j).2.2.2.1` |
| `psi_diff` | L63, stage differentiability | `(hΨ j).1` |
| `psi_real` | L64–65, real range | `(hΨ j).2.1` |
| `psi_per` | L66–67, stage lattice identity | `(hΨ j).2.2.1` |
| `psi_maps` | L70, complex maps-to | `(hΨ j).2.2.2.2.1` |
| `psi_bd` | L71–75, three block bounds | `(hΨ j).2.2.2.2.2` |
| `tube` | L58, next-base tube inclusion | `(ht j).1` |
| `eHat_sq` | L76, strict quadratic recurrence | `(hr j).1` |
| `rho_lo` | L77, lower radius recurrence | `(hr j).2.1` |
| `rho_hi` | L78, upper radius recurrence | `(hr j).2.2.1` |

All constants and carriers match literally, including fixed initial `p.Mhat / p.M` in `psi_bd`; no stage-dependent replacement or changed norm. `iterative_steps` also constructs all eight `ActionSteps` fields from that same tuple, using exactly the projections accounted for in P23-17. Every field is a DERIVED dependency at this private boundary; these would be excessive premises if advertised as new source assumptions. The design expressly authorizes this conditional interface. The source-facing applicability theorem assumes only `H : KamHyp D sbar p h f`, whose standing positivity, analytic/class/norm/frequency/Hessian and KAM-smallness content is unchanged.

`limit_map_of_iterative` (facade L57–62) calls `iterative_steps` once, then `limit_actions_of_steps S` once. It defines `hD` directly from the same action limit's `hloc`, with `Dstar = i '' Ds 0`, calls `P.limit_phi_real_of_steps hD` once, and calls `P.limit_phi_strip_of_steps hD hU` for that exact `Φinf`. No re-selection of stages, no independent action image, no new limit used for the extension.

## Obligation inventory and mathematical review

| Local obligation | Implementing helpers | Application / result |
|---|---|---|
| pl-dom | `PsiSteps.psi_step`, `psi_lip_of_steps` | Real half-radius maps-to; reality is proved before real-part projection is used |
| pl-disp | `scaled_bound`, `psi_disp`, `psi_lip_of_steps` | `(3/4) Ehat_j / 12^j` in the literal scaled norm |
| pl-lip | `stageEps_lower`, `unsc_mem`, `psi_lip_step` | `lip_sup` with dimension `2(a+b)`, not a replacement norm |
| pl-sum | `kam_small`, `psi_lip_of_steps` | Summable; sum ≤ `384n Ehat_0 < 1/20` |
| lp-tele | `phi_disp_complex`, `phi_disp_real`, `partial_sum_le` | All three block bounds, factor `3/2`, including complex stage domains |
| lp-cauchy | `phi_lip`, `lp_le`, `phi_step_diff`, `e_sums`, `phi_limit` | Product-minus-one bound; real limit with uniform tail |
| lp-per | `limit_phi_real_of_steps` | Full lattice identity and `InjOn` on `univ ×ˢ Dstar` |
| lp-an | `strip_mem`, `strip_comp`, `limit_phi_strip_of_steps` | All coordinate extensions on the same strip; all iterated derivatives on closed substrips |
| Joint applicability | `iterative_steps`, `limit_map_of_iterative` | Same tuple, same action image, same real limit and its extension |

The `192n c^j Ehat_j` bound is proved by scaled complex-neighborhood control and `lip_sup`: `ε_j ≥ 1/(32 q^j)`, displacement `(3/4) Ehat_j 12^(-j)`, dimension `2n`, hence `4·2n·(3/4)·32=192n`, `q/12=c`. Both actual radii and coefficient/physical widths are retained; `geometricWidth σ = σ/(2π)`. The inclusion proof uses strict tube inequalities and positivity from stage hypotheses. `rho_upper` gives `16^(-j)`, then weakens to `12^(-j)` only where needed.

`kam_small` derives `8192n Ehat_0 < 1` and `c Ehat_0 ≤ 1/2` from `kamConstant * Ehat_0 < 1`. The proved scalar `sums` theorem yields sum ≤ `384n Ehat_0`, and `384/8192 < 1/20`. `phi_lip` proves the composition rule by induction on the actual `Φ_{j+1}=Φ_j∘Ψ_{j+1}`. `lp_le` bounds the product by the exponential of the partial sum and then `1+2x`; `lam_small` proves `768n Ehat_0 < 1/10`. These numerical inequalities are conclusions, not bundled assumptions.

`phi_disp_complex` telescopes by induction over the complex maps-to property, enlarging `rhoHat_j` to the actual `ρ_j` for the induction hypothesis; it does not rely on real-only displacement. `phi_step_diff` converts the scaled bound to ambient norm with `max(s_0/(2π),rhoHat_0)` and the summable majorant `(33/40) Ehat_j`. `phi_limit` proves Cauchy convergence by completeness; the uniform tail `2 max(...) (33/40) Ehat_j` tends to zero independent of the point. Limit inequalities and periodicity follow by continuity/uniqueness of limits. Positive scaling gives nondegeneracy for injectivity.

For each fixed `I ∈ Dstar`, `strip_mem` puts the *whole* angle strip `|Im θ_i| < sbar/(2π)` in every finite-stage complex domain. `strip_comp` applies `fourier_compact` to the finite-stage coordinate displacement, using uniform real convergence and complex block bounds. `StripLimit` explicitly quantifies every `0<v<w` and every derivative order, using `iteratedFDeriv ℂ m (F j)` of the same finite-stage functions. Angle, first-action and last-action coordinates receive respectively `(3/2) Ehat_0 s_0/(2π)`, `(3/2)(Mhat/M) Ehat_0 rhoHat_0`, and `(3/2) Ehat_0 rhoHat_0`. Coordinatewise existential extensions suffice for the stated finite-dimensional block sup bounds; no common holomorphic action neighborhood is claimed.

Release notes: the facade's exported joint theorem intentionally forgets `S/P`, the action-limit location, bi-Lipschitz/injectivity and real block bounds, and the two action-strip families. Its *proof* applies all the helpers on matching witnesses and demonstrates applicability; its conclusion alone is not a full P23-22 assembly API. A downstream consumer must retain the full results in a common construction, rather than separately destruct this reduced existential and choose new stages. The generic helpers retain the necessary conclusions. This distinction is not an extra hypothesis or a mathematical refutation of the private package. P23-20's common inner domain and uniform field error remain unproved here; no declaration in scope claims them, nor torus invariance/Lagrangian/measure closure.

## Declaration-by-declaration inventory

All names are under `KAM.Planetary`; `PsiSteps.` prefixes are retained. File names below abbreviate `KAM/Planetary/TwoScale/<file>.lean`. PASS is scoped mathematical/definition review; F1 controls the overall release verdict.

| Node / role | Declaration | Location | Verdict | Reason |
|---|---|---|---|---|
| joint applicability | `limit_map_of_iterative` | LimitMap:34 | PASS | Same witnesses and exact image; reduced exported conclusion |
| supporting lemma | `PsiSteps.rho_le_zero` | LimitMapDisp:32 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.s_le_zero` | LimitMapDisp:38 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.partial_sum_le` | LimitMapDisp:43 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| lp-tele | `PsiSteps.phi_disp_complex` | LimitMapDisp:55 | PASS | Complex-domain telescoping of all three blocks |
| lp-cauchy | `PsiSteps.lp_le` | LimitMapLimit:33 | PASS | Product bound ≤ 768n Ehat0 |
| lp-cauchy | `PsiSteps.lam_small` | LimitMapLimit:57 | PASS | 768n Ehat0 < 1/10 proved |
| supporting lemma | `PsiSteps.phi_step_diff` | LimitMapLimit:65 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.e_sums` | LimitMapLimit:111 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| lp-cauchy | `PsiSteps.phi_limit` | LimitMapLimit:121 | PASS | Completeness; chosen limit with uniform point-independent tail |
| lp-tele | `PsiSteps.phi_disp_real` | LimitMapLimit:160 | PASS | Real inclusion preserves both blocks and angle norm |
| supporting lemma | `seq_s` | LimitMapLip:32 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `seq_ρ_succ` | LimitMapLip:37 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `two_pow_ge_twelve` | LimitMapLip:39 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.rho_pos` | LimitMapLip:47 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.rho_upper` | LimitMapLip:50 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.rho_lower` | LimitMapLip:59 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `differentiable_unsc` | LimitMapLip:82 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `differentiable_sc` | LimitMapLip:86 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| pl-lip data | `stageEps` | LimitMapLip:93 | PASS | Literal minimum radius; positivity and lower bound proved |
| supporting lemma | `PsiSteps.stageEps_pos` | LimitMapLip:98 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.stageEps_lower` | LimitMapLip:104 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.unsc_mem` | LimitMapLip:126 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.scaled_bound` | LimitMapLip:196 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| pl-lip | `PsiSteps.psi_lip_step` | LimitMapLip:225 | PASS | 192n c^j Ehat_j via scaled lip_sup |
| pl-sum prerequisite | `PsiSteps.kam_small` | LimitMapPack:33 | PASS | Both smallness bounds derived from KamHyp |
| supporting lemma | `PsiSteps.psi_disp` | LimitMapPack:45 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| psi-lip / pl-dom,disp,lip,sum | `psi_lip_of_steps` | LimitMapPack:77 | PASS | All four obligations, summability and strict smallness |
| supporting lemma | `coefficientDom_mono_of_le` | LimitMapPhi:27 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `realTube_mono` | LimitMapPhi:33 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| pl-lip data | `psiConst` | LimitMapPhi:40 | PASS | Literal 192n c^k Ehat_k |
| supporting lemma | `PsiSteps.rho_stage_pos` | LimitMapPhi:49 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.incl_mem_stage` | LimitMapPhi:52 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.phi_real_pt` | LimitMapPhi:61 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.phiR_zero` | LimitMapPhi:69 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.phiR_succ` | LimitMapPhi:73 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.psiConst_nonneg` | LimitMapPhi:80 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.lp_nonneg` | LimitMapPhi:85 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| lp-cauchy composition | `PsiSteps.phi_lip` | LimitMapPhi:96 | PASS | Actual composition; product-minus-one defect constant |
| real restriction | `psiR` | LimitMapPsi:32 | PASS | Real part of complex map; exact on real-range hypotheses |
| real domain | `phaseTube` | LimitMapPsi:36 | PASS | Angles unrestricted; action strict real tube |
| private interface | `PsiSteps` | LimitMapPsi:40 | PASS | All 15 fields expanded above; no assumed limit conclusion |
| private release gate | `iterative_steps` | LimitMapPsi:79 | PASS | All 15 PsiSteps and 8 ActionSteps fields projected from one iterative output |
| supporting lemma | `mem_realTube_iff` | LimitMapPsi:93 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `real_mem_coefDom` | LimitMapPsi:107 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `norm_le_of_blocks` | LimitMapPsi:114 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `PsiSteps.action_bd` | LimitMapPsi:129 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| pl-dom | `PsiSteps.psi_step` | LimitMapPsi:143 | PASS | Reality and strict half-radius maps-to plus displacement |
| supporting lemma | `continuous_limitmap_data` | LimitMapReal:31 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| limit-phi / lp-cauchy,per | `PsiSteps.limit_phi_real_of_steps` | LimitMapReal:40 | PASS | Uniform real limit, scaled bounds, InjOn, lattice and three blocks |
| limitmap data | `limitmap_data` | LimitMapScale:30 | PASS | Verbatim signature-file body; scratch rfl check |
| rescaling | `unsc` | LimitMapScale:37 | PASS | Inverse scaling where R,s nonzero; proved inverse laws |
| rescaling | `sc` | LimitMapScale:42 | PASS | Linear scaling into Fin(n+n), total arithmetic body |
| supporting lemma | `sc_unsc` | LimitMapScale:45 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `unsc_sc` | LimitMapScale:58 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `unsc_sub` | LimitMapScale:72 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `sc_sub` | LimitMapScale:76 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| rescaling norm | `norm_append_le` | LimitMapScale:83 | FAIL (F1) | Public name already exported by ResonanceFast.Pullback; co-import fails |
| supporting lemma | `le_norm_append_left` | LimitMapScale:90 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `le_norm_append_right` | LimitMapScale:96 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `norm_ofReal_mul_pi` | LimitMapScale:102 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `norm_sc` | LimitMapScale:109 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `limitmap_data_eq_norm_sc` | LimitMapScale:127 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `sc_incl` | LimitMapScale:130 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `unsc_incl` | LimitMapScale:138 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `norm_unsc_fst_le` | LimitMapScale:142 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `norm_unsc_snd_le` | LimitMapScale:148 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `limitmap_data_nonneg` | LimitMapScale:154 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `limitmap_data_sub_le` | LimitMapScale:158 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `limitmap_data_add_le` | LimitMapScale:164 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `limitmap_data_eq_zero` | LimitMapScale:173 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| supporting lemma | `norm_le_limitmap_data` | LimitMapScale:181 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| lp-an predicate | `StripLimit` | LimitMapStrip:34 | PASS | Literal conjunction of extension, periodicity, bound and all derivative convergence |
| lp-an data | `PsiSteps.stripSeq` | LimitMapStrip:47 | PASS | Same finite-stage complex coordinate displacement |
| supporting lemma | `PsiSteps.strip_mem` | LimitMapStrip:51 | PASS | Literal algebra/domain/scalar adapter used by the obligations above; no added source premise |
| lp-an adapter | `PsiSteps.strip_comp` | LimitMapStrip:65 | PASS | Bound hbd and convergence hU are explicit conditional inputs discharged in strip theorem |
| limit-phi / lp-an | `PsiSteps.limit_phi_strip_of_steps` | LimitMapStrip:127 | PASS | Whole common strip, three coordinate families and all derivatives |

## Definition classification

Every new def/structure is listed in the inventory (10 total). No abbrev is introduced. All have BODY_MATCH=OK and PUBLIC_CARRIER=OK for their documented private roles; choice independence is N/A because the definition bodies make no arbitrary choices. `limitmap_data` is literally the signed design function on its entire real carrier, including Lean's total division at zero; every norm/positive-scaling claim explicitly requires or derives positive radii, so no theorem treats its zero-radius value as a norm. `sc`/`unsc` are likewise total arithmetic formulas; inverse laws require nonzero scales. `psiR` is the literal real-part restriction on the whole ambient carrier and is identified with the complex map on the asserted real domains. `phaseTube` uses the frozen strict action-neighborhood preimage. `stageEps` and `psiConst` are numerical expressions. `PsiSteps` and `StripLimit` are transparent private proof predicates, not source-defined mathematical objects or standing hypotheses; no hidden field is accepted as the hard limit theorem. `stripSeq` is a literal coordinate projection of the same `Φ_j-id`.

The proof-local `choose! l` in `phi_limit` chooses proved limits on the asserted domain. All exported claims are restricted to that domain; outside values are unused, and uniqueness of the domain limit follows from the Hausdorff topology. No fallback value is used to prove a source claim.

## Independent verification receipts

All audit Lean/Lake invocations were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No clean/update/cache operation or dependency edit occurred. Compile-gate waiting was respected.

1. Targeted gated build:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2318 KAM.Planetary.TwoScale.LimitMap
```

Exit **0**. Output included `[inp-gate] slot 2 acquired 14:09:01 for KAM.Planetary.TwoScale.LimitMap` and `Build completed successfully (9177 jobs).` This was a warm build/replay, not forced recompilation. Package warnings: unused `hs` at facade L36:40, `fs` at L37:7, and `Ψ` at L37:31; no package errors or sorry warnings. Upstream unused-variable/deprecation warnings were replayed.

2. Every new public theorem's axioms, plus the literal data-body check:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2318Audit.lean
```

Exit **0**, 67 axiom-output lines, all exactly the permitted three axioms. The probe imported the facade, printed every theorem from the 77-row inventory, and checked:

```lean
example {n : ℕ} (R s : ℝ) (z : KAM.Planetary.Phase n) :
    KAM.Planetary.limitmap_data R s z =
      max (‖z.1‖ * (2 * Real.pi / s)) (‖z.2‖ / R) := rfl
```

Exact axiom output:

```text
'KAM.Planetary.limit_map_of_iterative' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.rho_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.s_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.partial_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.phi_disp_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.lp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.lam_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.phi_step_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.e_sums' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.phi_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.phi_disp_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.seq_s' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.seq_ρ_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.two_pow_ge_twelve' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.rho_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.rho_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.rho_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiable_unsc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiable_sc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.stageEps_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.stageEps_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.unsc_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.scaled_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.psi_lip_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.kam_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.psi_disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.psi_lip_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.coefficientDom_mono_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.realTube_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.rho_stage_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.incl_mem_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.phi_real_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.phiR_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.phiR_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.psiConst_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.lp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.phi_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iterative_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_realTube_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_mem_coefDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_le_of_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.action_bd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.psi_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_limitmap_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.limit_phi_real_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sc_unsc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.unsc_sc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.unsc_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sc_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_append_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.le_norm_append_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.le_norm_append_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_ofReal_mul_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_sc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limitmap_data_eq_norm_sc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sc_incl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.unsc_incl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_unsc_fst_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_unsc_snd_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limitmap_data_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limitmap_data_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limitmap_data_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limitmap_data_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_le_limitmap_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.strip_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.strip_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PsiSteps.limit_phi_strip_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation for the facade and all nine implementation modules:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.LimitMap KAM.Planetary.TwoScale.LimitMapScale KAM.Planetary.TwoScale.LimitMapPsi KAM.Planetary.TwoScale.LimitMapLip KAM.Planetary.TwoScale.LimitMapPack KAM.Planetary.TwoScale.LimitMapPhi KAM.Planetary.TwoScale.LimitMapDisp KAM.Planetary.TwoScale.LimitMapLimit KAM.Planetary.TwoScale.LimitMapReal KAM.Planetary.TwoScale.LimitMapStrip
```

Exit **0**, exact output:

```text
replaying KAM.Planetary.TwoScale.LimitMapStrip
replaying KAM.Planetary.TwoScale.LimitMapReal
replaying KAM.Planetary.TwoScale.LimitMapLimit
replaying KAM.Planetary.TwoScale.LimitMapDisp
replaying KAM.Planetary.TwoScale.LimitMapPhi
replaying KAM.Planetary.TwoScale.LimitMapPack
replaying KAM.Planetary.TwoScale.LimitMapLip
replaying KAM.Planetary.TwoScale.LimitMapPsi
replaying KAM.Planetary.TwoScale.LimitMapScale
replaying KAM.Planetary.TwoScale.LimitMap
```

4. Lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the permitted generated-root exception; exact complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (666 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module check, frozen guard and all 144 frozen ABI hashes passed. `KAM.lean` was not regenerated, as required.

5. Static hygiene: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no diff (only the multiple-merge-base warning). `git diff --check` exited 0. A recursive KAM import traversal from the facade visited 131 KAM modules and found **no provider or frozen theorem import**, so no DRAFT_SORRY theorem premise is reachable. The only frozen imports are definitions. The ten audited files all have copyright, `module`, public imports, module docstring and exposed public sections. Source scan found no forbidden proof escapes, resource overrides or `EuclideanSpace` in scope. All files are below 1500 lines (counts: 72, 120, 193, 294, 115, 146, 185, 157, 200, 195). All 67 theorem names and all 10 definitions/structures are listed above; only the qualified-name collision F1 was found by the independent duplicate scan. Co-import failure is independently recorded in F1 and is not hidden by successful build/kernel checks.

## Blueprint/source defects, deviations and limits

No suspected new pinned-source mathematical defect was found in the audited obligations; no source text was silently repaired. P3b L43 writes actions first while frozen `Phase` and the design function use angles first; the implementation explicitly permutes the block order and retains the literal scaling. P3b L94 subtracts only the identity angle part whereas the code subtracts the full `(θ,I)`; at each fixed I the action coordinate differs by a constant, so holomorphicity, periodicity and positive-order derivatives agree, and displacement bounds are stated for the actual displacement.

Documentation typo: `LimitMapPsi.lean:16` says `iterative_psiSteps`; the implemented applicability theorem is `iterative_steps` at L79. The stale design N2 wording that these interfaces are “unimplemented” describes the pre-package status; this audit reviews the supplied commands, not a change in source premises. The P23-17 open-initial-tube endpoint note is neither repaired nor claimed here; only its already-proved strict stage half-tube location is consumed.

F1 is a concrete Lean integration defect, not a source erratum. No production deviation was introduced by this audit. Frozen anchors and manifest were left untouched. The unresolved downstream invariance inner-domain obligation remains outside P23-18. No frozen theorem, physical theorem, or full two-scale theorem is certified by these private results.

## Private-interface signature appendix

These are the actual complete principal helper statements reviewed for the release gate (proof bodies omitted here; they were read in the source and kernel-checked separately). The shared namespace context is `KAM.Planetary`, with `Set Metric Real Filter Topology` and `KAM.Weighted KAM.Canonical KAM.NormalForm` open. Generic helper context:

```lean
variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}
```

For the last two generic helpers below the namespace is additionally `PsiSteps`; the joint theorem has its own explicit context. `StripLimit` is expanded in the definition-classification and obligation discussion above and in Strip L34–43.

```lean
theorem psi_lip_of_steps (P : PsiSteps sbar p Ds hs fs Ψ Φ) :
    (∀ j, ∀ x ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2),
      KAM.realInclusion₂ (a + b) (psiR (Ψ (j + 1)) x) = Ψ (j + 1) (KAM.realInclusion₂ (a + b) x) ∧
      psiR (Ψ (j + 1)) x ∈ phaseTube (Ds j) ((seq p j).ρ / 2)) ∧
    (∀ j, ∀ x ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2),
      limitmap_data (rhoHat p) p.s (psiR (Ψ (j + 1)) x - x) ≤ 3 / 4 * eHat (seq p j) / 12 ^ j) ∧
    (∀ j, ∀ x ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2),
      ∀ y ∈ phaseTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2),
      limitmap_data (rhoHat p) p.s
          ((psiR (Ψ (j + 1)) x - x) - (psiR (Ψ (j + 1)) y - y)) ≤
        192 * ((a + b : ℕ) : ℝ) * (((24 : ℝ) ^ (p.τ + 1) / 6) ^ j * eHat (seq p j)) *
          limitmap_data (rhoHat p) p.s (x - y)) ∧
    Summable (fun j =>
      192 * ((a + b : ℕ) : ℝ) * (((24 : ℝ) ^ (p.τ + 1) / 6) ^ j * eHat (seq p j))) ∧
    ∑' j, 192 * ((a + b : ℕ) : ℝ) * (((24 : ℝ) ^ (p.τ + 1) / 6) ^ j * eHat (seq p j)) ≤
      384 * ((a + b : ℕ) : ℝ) * eHat p ∧
    384 * ((a + b : ℕ) : ℝ) * eHat p < 1 / 20
```

```lean
theorem limit_phi_real_of_steps (P : PsiSteps sbar p Ds hs fs Ψ Φ)
    {Dstar : Set (Fin (a + b) → ℝ)} (hD : ∀ j, Dstar ⊆ realTube (Ds j) ((seq p j).ρ / 2)) :
    ∃ Φinf : Phase (a + b) → Phase (a + b),
      TendstoUniformlyOn (fun j => psiR (Φ j)) Φinf atTop (univ ×ˢ Dstar) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ y ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
        limitmap_data (rhoHat p) p.s ((Φinf x - x) - (Φinf y - y)) ≤
          768 * ((a + b : ℕ) : ℝ) * eHat p * limitmap_data (rhoHat p) p.s (x - y)) ∧
      768 * ((a + b : ℕ) : ℝ) * eHat p < 1 / 10 ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ y ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
        9 / 10 * limitmap_data (rhoHat p) p.s (x - y) ≤
            limitmap_data (rhoHat p) p.s (Φinf x - Φinf y) ∧
          limitmap_data (rhoHat p) p.s (Φinf x - Φinf y) ≤
            11 / 10 * limitmap_data (rhoHat p) p.s (x - y)) ∧
      Set.InjOn Φinf (univ ×ˢ Dstar) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ k : Fin (a + b) → ℤ,
        Φinf (x + KAM.ODE.angleShift k) = Φinf x + KAM.ODE.angleShift k) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
        ‖firstBlock (b := b) ((Φinf x - x).2)‖ ≤ 3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p ∧
        ‖lastBlock (a := a) ((Φinf x - x).2)‖ ≤ 3 / 2 * eHat p * rhoHat p ∧
        2 * π * ‖(Φinf x - x).1‖ ≤ 3 / 2 * eHat p * p.s)
```

```lean
theorem limit_phi_strip_of_steps (P : PsiSteps sbar p Ds hs fs Ψ Φ)
    {Dstar : Set (Fin (a + b) → ℝ)} (hD : ∀ j, Dstar ⊆ realTube (Ds j) ((seq p j).ρ / 2))
    {Φinf : Phase (a + b) → Phase (a + b)}
    (hU : TendstoUniformlyOn (fun j => psiR (Φ j)) Φinf atTop (univ ×ˢ Dstar)) :
    ∀ I ∈ Dstar,
      (∀ c : Fin (a + b), ∃ G, StripLimit (a + b) (geometricWidth sbar)
        (3 / 2 * eHat p * p.s / (2 * π))
        (stripSeq Φ ((ContinuousLinearMap.proj c).comp (ContinuousLinearMap.fst ℂ _ _)) I)
        (fun x => (((Φinf (x, I) - (x, I)).1 c : ℝ) : ℂ)) G) ∧
      (∀ i : Fin a, ∃ G, StripLimit (a + b) (geometricWidth sbar)
        (3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p)
        (stripSeq Φ ((ContinuousLinearMap.proj (Fin.castAdd b i)).comp
          (ContinuousLinearMap.snd ℂ _ _)) I)
        (fun x => (((Φinf (x, I) - (x, I)).2 (Fin.castAdd b i) : ℝ) : ℂ)) G) ∧
      (∀ i : Fin b, ∃ G, StripLimit (a + b) (geometricWidth sbar)
        (3 / 2 * eHat p * rhoHat p)
        (stripSeq Φ ((ContinuousLinearMap.proj (Fin.natAdd a i)).comp
          (ContinuousLinearMap.snd ℂ _ _)) I)
        (fun x => (((Φinf (x, I) - (x, I)).2 (Fin.natAdd a i) : ℝ) : ℂ)) G)
```

```lean
theorem iterative_steps {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      Ds 0 = dioBase D h p ∧ ActionSteps sbar p h Ds hs fs is ∧ PsiSteps sbar p Ds hs fs Ψ Φ
```

```lean
theorem limit_map_of_iterative {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      Ds 0 = dioBase D h p ∧
      ∃ i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ),
        TendstoUniformlyOn (actionChain is) i atTop (Ds 0) ∧
        ∃ Φinf : Phase (a + b) → Phase (a + b),
          TendstoUniformlyOn (fun j => psiR (Φ j)) Φinf atTop (univ ×ˢ (i '' Ds 0)) ∧
          (∀ x ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))),
            ∀ y ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))),
            limitmap_data (rhoHat p) p.s ((Φinf x - x) - (Φinf y - y)) ≤
              768 * ((a + b : ℕ) : ℝ) * eHat p * limitmap_data (rhoHat p) p.s (x - y)) ∧
          (∀ x ∈ (univ ×ˢ (i '' Ds 0) : Set (Phase (a + b))), ∀ k : Fin (a + b) → ℤ,
            Φinf (x + KAM.ODE.angleShift k) = Φinf x + KAM.ODE.angleShift k) ∧
          ∀ I ∈ i '' Ds 0, ∀ c : Fin (a + b), ∃ G, StripLimit (a + b) (geometricWidth sbar)
            (3 / 2 * eHat p * p.s / (2 * π))
            (PsiSteps.stripSeq Φ ((ContinuousLinearMap.proj c).comp
              (ContinuousLinearMap.fst ℂ _ _)) I)
            (fun x => (((Φinf (x, I) - (x, I)).1 c : ℝ) : ℂ)) G
```

## Final audit state

Build: PASS. All 67 public theorem axiom checks: PASS. Kernel replay of all ten modules: PASS. Lint: expected generated-root exception only. Definition and private applicability review: PASS within the scope explained above. Integration/public-name hygiene: **FAIL (F1)**, independently reproduced. No frozen anchor is sealed or certified by this package. Both audit-created Lean probes were deleted after checks; only the named report was added, and the original handoff remains untouched.
