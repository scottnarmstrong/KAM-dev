# P23-18 independent package audit 2 — delta audit

Overall verdict: **PASS WITH NOTES — round-1 F1 resolved.** Scope is the private P23-18 helper package, not a frozen-anchor seal. This round checks the sole round-1 blocker F1 and carries forward the unchanged scoped mathematical review from [audit 1](P23-18-audit-1.md).

## Scope, authorization and frozen inputs

Date: 2026-10-28. Audited HEAD `d8fff327a31278de7c088dfddafd79cc4b07e272`; predecessor `fbb2374ec1954fed5267e0f488f2e8c990023f10`; round-1 audited code `0e8f8536a2f3557ed967edeb55956f9cf182484c`. `inp` at comparison: `e5df64700d49778f5a16b13c87fb6e7a5237ea4d`.

Tier 2 focused delta audit: immutable input hashes, exhaustive byte comparison, adversarial name-collision check and fresh build/kernel/axiom checks. The user authorizes only this exact worktree report and temporary `.lake/abi-scratch/` probes; no source repair, commit, push, source fetch or delegation. The explicit destination `/root/code/KAM-inp-p2318/docs/tracks/P/audits/P23-18-audit-2.md` overrides the common brief's main-worktree destination. All Lean/Lake invocations are serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`; builds use the prescribed compile gate.

Read the repository rules, PLAN, DECISIONS, common package-audit brief, handoff/AUDIT FOCUS, round-1 report, track-P statement, P23 design release gate and P3b limit-map clauses. Frozen `Phase`, `actionNbhd` and P-G were inspected for scope. No provider/frozen-type equality or seal-body probe applies: this package introduces no provider and proves no frozen anchor. Round 1's mathematical/source review is inherited only after byte equality to its audited revision, modulo the two name substitutions, was independently established; no fresh external PDF or full mathematical re-audit is claimed.

Audited files are all under `KAM/Planetary/TwoScale/`. Frozen-v1 SHA256:

| File | SHA256 |
|---|---|
| `LimitMap.lean` | `a7ee2feafdfbd57801ecb074ef25e16cf3bf84301b2be4c230fc607308f2e8ef` |
| `LimitMapDisp.lean` | `63edb159cf79982d304862b13754fe645509997c7556098617fe68b3dc7f087f` |
| `LimitMapLimit.lean` | `8221d6e0d5f0bbc3c1d24888a221653c7d1bb34e2aeb64d3b194c7dc7f563c45` |
| `LimitMapLip.lean` | `ef11efe60dbb634e4047f3e564c628178d1529969a7f5f6c178a28e8dcc3a75a` |
| `LimitMapPack.lean` | `bc6c3c72652a27bc4ebae3ec09b84d7a45788034fb5974fd7d4699280f8626d9` |
| `LimitMapPhi.lean` | `f92a51e3b2ae1ccabedd3447c3db8f6890e61af122e04876005f277f778173e9` |
| `LimitMapPsi.lean` | `c60a2110451a6fa829c1ba9a5fc31a5a13181ff12b4c47c87f6a1feb7132f471` |
| `LimitMapReal.lean` | `8c43570110443fcb1fc8899d6a5859be4d7e6f3e8888dc5e63026b7a03311389` |
| `LimitMapScale.lean` | `a50cef11e7a5914f009c60ac78794ed5eb187743c9d0c720c0ece750fffe37d7` |
| `LimitMapStrip.lean` | `3ee8e5f5e6d2eb7ff2a6f14715937020d17a4ce365aa81ca53a7a9e25e110705` |

## Exact delta and F1 disposition

`git diff fbb2374..HEAD` changes exactly one file, `LimitMapScale.lean`, with two additions and two deletions. At L83, `theorem norm_append_le` becomes `theorem limitMap_norm_append_le`; at L116, `(norm_append_le _ _)` becomes `(limitMap_norm_append_le _ _)`. The complete type, proof of the renamed lemma, and every other statement/definition/proof are byte-identical. A Python check compared every package file to `git show fbb2374:<path>`, replacing exactly two whole-identifier matches `\bnorm_append_le\b` in Scale and asserting complete equality; it also repeated the comparison against round 1's actual audited code `0e8f8536`.

```text
DELTA EXACT: one file, two whole-identifier substitutions; all remaining bytes identical
Round-1 audited source 0e8f8536 -> HEAD: identical modulo the two identifier substitutions in Scale
```

`git diff inp...HEAD` was inspected for the package. Git reports `multiple merge bases, using 31f0bfbf70c07b1eefd006237f331c00e003a0e5`. Other branch-diff files are excluded as instructed by AUDIT FOCUS. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty apart from this warning.

Whole-library scan: all 664 `KAM/**/*.lean` files, comments/strings masked, namespaces and section visibility tracked. Used `scripts/check_lean_modules.py`'s scanner with its identifier regex extended **in scratch memory only** to Unicode, so `seq_ρ_succ` is a complete identifier (the stock ASCII regex truncates it to `seq_`). Compared all 77 exported package declarations with the library-wide qualified-name index. No duplicate exists. Both existing and newly renamed append lemmas have exactly one source declaration:

```text
WHOLE-LIBRARY SCAN: 664 files; 77 package declarations; 67 theorems; collisions: []
Old name declarations: ['KAM/Planetary/PGMeasure/ResonanceFast/Pullback.lean']
New name declarations: ['KAM/Planetary/TwoScale/LimitMapScale.lean']
```

The scan was followed by the exact formerly failing round-1 co-import, importing Pullback before the LimitMap facade and checking both distinct names. Its execution receipt appears below. This is a whole-library declaration scan plus the actual conflict-pair co-import, as in round 1; it is not a build/co-import of every quarantined module in KAM.

## Declaration ledger and inherited mathematical verdicts

All names below are under `KAM.Planetary`; locations and role descriptions are those of audit 1, still valid at this snapshot. PASS means the scoped private mathematical/definition contract, with unchanged statements and proofs established mechanically in this round. The renamed lemma additionally receives the fresh integration check. There are 77 declarations, including 67 theorems and 10 definitions/structures.

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
| rescaling norm | `limitMap_norm_append_le` | LimitMapScale:83 | PASS | Renamed helper; mathematical body unchanged; F1 retested below |
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


## Definition classification and applicability limits

All ten definitions/structures are unchanged, with BODY_MATCH=OK and PUBLIC_CARRIER=OK in their round-1 documented roles. `limitmap_data` is the literal max-scaled function on its whole carrier (including total division at zero); norm claims require positive scales. `sc`/`unsc` are total arithmetic maps whose inverse laws require nonzero scales. `psiR` takes the real part and its domain reality is proved; `phaseTube` uses the literal strict action neighborhood. `stageEps` and `psiConst` are numerical expressions. `PsiSteps` and `StripLimit` are transparent private proof predicates. `PsiSteps.stripSeq` projects the actual finite-stage displacement. No arbitrary fallback supplies a claimed result; the proof-local choice of limits is used only where convergence was proved. The literal `limitmap_data` body is rechecked by `rfl` in the fresh axiom probe.

The unchanged `iterative_steps` discharges all 15 PsiSteps fields and the ActionSteps bundle from one iterative witness tuple. The unchanged joint proof selects that tuple once and uses the same action image `Dstar = i '' Ds 0`, real limit and strip extension. The constants 192n, 384n and 768n and their strict smallness bounds remain proved conclusions. The generic helpers retain full block/bi-Lipschitz/strip conclusions; the facade exports a reduced joint existential. Consumers must retain matching witnesses and the full helper outputs. P23-20's common inner domain and uniform field-error obligation, invariance, physical headlines and full two-scale theorem closure remain outside this package. No new source hypothesis, source repair or frozen declaration is introduced.

## Fresh verification receipts

All checks below are independent round-2 runs. No concurrent Lean/Lake checks, clean/update/cache actions or dependency edits occurred.

1. Targeted gated build:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2318 KAM.Planetary.TwoScale.LimitMap
```

Exit **0**. Exact gate and completion lines:

```text
[inp-gate] slot 1 acquired 14:29:12 for KAM.Planetary.TwoScale.LimitMap
Build completed successfully (9177 jobs).
```

Warm build/replay, not forced recompilation. Existing facade unused-variable warnings for `hs` (L36:40), `fs` (L37:7), `Ψ` (L37:31) remain; upstream unused-variable/deprecation warnings were replayed. No package error or sorry warning. The delta adds no warning.

2. Whole-library qualified-name scan and conflict-pair co-import:

```sh
python3 .lake/abi-scratch/P2318R2-scan.py
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2318R2Coimport.lean
```

Both exit **0**. The scan results are recorded above. Probe content:

```lean
import KAM.Planetary.PGMeasure.ResonanceFast.Pullback
import KAM.Planetary.TwoScale.LimitMap
#check KAM.Planetary.norm_append_le
#check KAM.Planetary.limitMap_norm_append_le
```

Exact Lean output:

```text
KAM.Planetary.norm_append_le {a b : ℕ} {u : Fin a → ℝ} {v : Fin b → ℝ} {c : ℝ} (hu : ‖u‖ ≤ c) (hv : ‖v‖ ≤ c)
  (hc : 0 ≤ c) : ‖Fin.append u v‖ ≤ c
KAM.Planetary.limitMap_norm_append_le.{u_2} {α : Type u_2} [SeminormedAddCommGroup α] {m : ℕ} (u v : Fin m → α) :
  ‖Fin.append u v‖ ≤ max ‖u‖ ‖v‖
```

This independently refutes the possibility that a rename-only textual change leaves the previously observed import collision in the checked environment. F1 is resolved.

3. Exhaustive theorem axiom probe and literal definition-body probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2318R2Axioms.lean
```

Exit **0**. Imported the facade, issued `#print axioms` for every theorem in the 77-row ledger (67 commands), and checked:

```lean
example {n : ℕ} (R s : ℝ) (z : KAM.Planetary.Phase n) :
    KAM.Planetary.limitmap_data R s z =
      max (‖z.1‖ * (2 * Real.pi / s)) (‖z.2‖ / R) := rfl
```

Exact complete axiom output (67 lines; independently parsed to require exactly the standard three axioms on every line):

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
'KAM.Planetary.limitMap_norm_append_le' depends on axioms: [propext, Classical.choice, Quot.sound]
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

4. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.LimitMap KAM.Planetary.TwoScale.LimitMapScale KAM.Planetary.TwoScale.LimitMapPsi KAM.Planetary.TwoScale.LimitMapLip KAM.Planetary.TwoScale.LimitMapPack KAM.Planetary.TwoScale.LimitMapPhi KAM.Planetary.TwoScale.LimitMapDisp KAM.Planetary.TwoScale.LimitMapLimit KAM.Planetary.TwoScale.LimitMapReal KAM.Planetary.TwoScale.LimitMapStrip
```

Exit **0**, exact complete output:

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


5. Lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the expressly permitted stale generated-root exception. Exact complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (666 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module check, frozen guard and all 144 frozen ABI hashes passed. `KAM.lean` was not regenerated.


6. Static checks: `git diff --check` exits **0**. Protected-path comparison against `inp...HEAD` is empty as recorded above. Comment-masked package scan finds no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, forbidden resource overrides or `EuclideanSpace`. All ten files have module scaffolding and are below 1500 lines (largest 294). Recursive import traversal visits 131 KAM modules, with no provider or frozen theorem import; therefore no DRAFT_SORRY theorem is a reachable premise. The whole-library name scan covers 664 KAM source files; lint's larger count includes root/build configuration Lean files.


## Defects, notes and closeout

**F1: RESOLVED.** The old round-1 anchor text `theorem norm_append_le` at Scale L83 is now `theorem limitMap_norm_append_le`; only its single use at L116 changes. Both the exhaustive source-name scan and the formerly failing co-import pass. The independent adversarial check found no surviving collision or new delta defect.

No new suspected pinned-source or blueprint defect was found. The following unchanged round-1 notes remain: Psi L16 says `iterative_psiSteps` while the declaration is `iterative_steps` (L79); design N2's “remain unimplemented” wording describes its earlier status. P3b L43 writes actions first while frozen Phase uses angles first; the explicit block permutation preserves the scaling. P3b L94's displacement notation differs by the fixed action coordinate from the full identity subtraction, which leaves angle holomorphicity, periodicity and positive-order derivatives unaffected. These are carried notes, not newly repaired claims. P23-17's initial-tube endpoint note and P23-20's common-inner-domain obligation remain outside this audit.

Per-anchor disposition: **N/A — no frozen anchor is proved or sealed by P23-18.** Private package disposition: **PASS WITH NOTES**, retaining the inherited applicability limits, existing unused-binder warnings and permitted generated-root exception. The scoped mathematical PASS from round 1 is preserved by exact delta verification, not replaced by compilation alone.

Closeout: 77/77 exported declarations classified; 67/67 theorem axiom checks standard; 10/10 modules kernel-replayed; build and co-import exit 0; whole-library collision count 0; lint has only the permitted exception. Source hashes and HEAD were rechecked unchanged at closeout. All audit-created `P2318R2*` scratch scripts, probes and logs were deleted after incorporating receipts. Only this exact-path report was added; the handoff, prior report, production sources, manifest, frozen anchors, generated files and dependencies were not edited. No commit or push was made. No production deviation was introduced.

