# P11A-C8 independent package audit 2 — delta

Overall verdict: **PASS WITH NOTES**. **F1 is resolved.** The only note is the expressly permitted stale generated root (`KAM.lean`); it is not a remaining package finding. All requested delta checks pass. The five C8 theorem exports are accepted as infrastructure; no frozen anchor is sealed by this package.

Audit date: 2026-10-28. Worktree and report destination: `/root/code/KAM-inp-p11ac8`. Audited HEAD: `4fffdaeafdb24be3acbe8f6de4a6b82e330a0918`. Round-1 report commit: `36062800cd26eb702b4e8a95515cff040848e5b3`. Round-1 audited implementation: `e4164985defb6f3c43f492b1609b2b42da25bf32`. These are distinct baselines: the intervening commit adds the handoff and audit-1 report, with no implementation/design/blueprint change.

Read AGENTS.md, PLAN, DECISIONS, the supplied package brief, handoff/AUDIT FOCUS and audit-1. This is the requested delta audit, confined to the ten `KAM/Planetary/MaximalStep/Step*.lean` files. The mathematical, definition, source, signature and cutoff-amendment reviews in [audit 1](P11A-C8-audit-1.md) are inherited by checked identity, not claimed as a second independent mathematical reconstruction. Fresh name, build, axiom, import, kernel and lint checks are recorded below. The user's explicit absolute report destination overrides the generic brief's main-worktree destination. Only this report and temporary scratch files were written; no state-changing git command was used.

## Baseline and exact delta

Ran `git diff inp...HEAD` (including the focused Step-file comparison) and `git diff --stat inp...HEAD`. Observed `inp`: `d9183adae208ecf2e726620694b69c8168e33006`. Git reports multiple merge bases and selects `003b1db80283ab9f885b58a8e415ba28053b37df`. The full comparison has 21 files, including inherited C7 work, HomologicalBracket and the two audit documents; the explicit Step-only scope is preserved.

`git diff 36062800..HEAD` changes exactly two paths. `git diff --numstat 36062800..HEAD`:

```text
2	2	KAM/Planetary/MaximalStep/StepHom.lean
2	2	KAM/Planetary/MaximalStep/StepRemainder.lean
```

A byte-preserving text check loaded each old file using `git show 36062800:<path>`, replaced exactly the token matching `\bstep_small\b` with `p11_step_small`, and required equality with the current file. Both assertions passed; each file has exactly two replacements. The complete changed-path list was asserted equal to these two paths. Thus there are no other statement, proof, comment, whitespace, import or definition changes anywhere in the commit.

| Delta location | Change | Verdict |
|---|---|---|
| `StepHom.lean:66` | Public declaration `step_small` → `p11_step_small`; all binders, type and proof bytes identical | PASS |
| `StepHom.lean:141` | Reference in `step_affHyp` renamed | PASS |
| `StepRemainder.lean:58` | Reference in `step_A_le_quarter` renamed | PASS |
| `StepRemainder.lean:66` | Reference in `step_Aeta_le` renamed | PASS |

`git diff --exit-code e4164985..36062800 -- KAM blueprint-P docs/tracks/P/design` exits 0 with empty output. Together with the exact rename check, this connects the implementation actually audited in round 1 to current HEAD, including its transitive project definitions and proofs.

The three audit-input SHA-256 values also equal audit 1:

```text
627ab032a68be7aca3f547d898c1e82fe8146c18a363a5dd63163916b8d3beee  /root/code/KAM-inp/.drafts/design/P11ASignatures.lean
8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9  docs/tracks/P/design/P11A-LEAN-DESIGN.md
990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec  blueprint-P/parts/p11a2-cutoff-step.tex
```

## F1 and public names

Parsed every Lean file under `KAM/` with the repository's `scripts/check_lean_modules.py` declaration parser, which masks comments/strings, tracks namespaces and section visibility, and excludes private declarations. For every one of the 104 named package declarations, counted exported declarations with the same final name component across KAM. **Each count is exactly 1.** All 104 are public in `KAM.Planetary`; none introduces a root declaration or root shadow.

`rg -n '\b(p11_step_small|step_small)\b' KAM` confirms the new name has one declaration (`StepHom.lean:66`) and three uses (the locations above). The old planetary helper is absent; `KAM.Apost.step_small` remains at `KAM/Apost/Constants.lean:702`. `p11_step_small` is unique both as a full name and as a public short name. No other reused public short name remains among the package's declarations. The unrelated `KAM.NormalForm.poissonBracket_congr` in `KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean:95` was explicitly confirmed **private**, so it is correctly excluded.

## Export and definition verdicts

| Export / anchor scope | Verdict | Reason |
|---|---|---|
| `canonical_step` | PASS | Round-1 signature/completeness result retained by exact identity; fresh build, axioms and kernel pass |
| `canonical_step_param` | PASS | Same; parameter-Cauchy proof unchanged |
| `canonical_step_real` | PASS | Same; approved reality guard unchanged |
| `cutoff_coefficients` | PASS | Amended `z.2 ∈ B` clause unchanged; round-1 independently checked correction retained |
| `canonical_step_simple_inverse` | PASS | Same signature and affine-flow clauses 4/9 proof; fresh validation passes |
| Frozen physical headline anchors | N/A | No anchor is proved or sealed; provider/frozen-type and seal-body probes are inapplicable |

All 23 named definitions/structures are unchanged and retain audit-1's classification: `P11Step` is standing geometric/smallness data; `P11StepHyp` is source input regularity/divisor/bound data. The 21 definitions are literal formulas, restrictions, Taylor/homological coefficients, averages, the actual selected flow and conjugation remainder, coefficient lifts and the real angle field. No new definition, carrier, fallback, hypothesis, or characterization obligation is introduced by the rename. This delta makes no new claim about behavior off the source domains.

## Declaration ledger

One row per named C8 declaration (104: 81 public theorems, 21 definitions, 2 structures). “Identity” means the round-1 semantic/signature verdict is retained by the checks above. “A” means a fresh axiom report exactly `[propext, Classical.choice, Quot.sound]`; every listed theorem also lies in the fresh kernel replay. The renamed helper's type was additionally elaborated directly.

| File:line / node | Declaration (`KAM.Planetary.` prefix) | Verdict | Evidence |
|---|---|---|---|
| `Step:28` | `step_normal_diff` | PASS | Identity; A |
| `Step:36` | `step_U_mem` | PASS | Identity; A |
| `Step:42` | `step_stepMap_diff` | PASS | Identity; A |
| `Step:55` | `step_mapsU` | PASS | Identity; A |
| `Step:66` | `domain_def_mono` | PASS | Identity; A |
| `Step:72` | `step_Rp_admissible` | PASS | Identity; A |
| `Step:109` | `canonical_step` | PASS | Identity; A |
| `Step:200` | `canonical_step_simple_inverse` | PASS | Identity; A |
| `StepBound:26` | `stepAvg` | PASS | Identity; definition classification retained |
| `StepBound:30` | `stepW` | PASS | Identity; definition classification retained |
| `StepBound:34` | `stepU` | PASS | Identity; definition classification retained |
| `StepBound:37` | `coeff_congr_param` | PASS | Identity; A |
| `StepBound:44` | `step_avg_eq` | PASS | Identity; A |
| `StepBound:68` | `step_avg_le` | PASS | Identity; A |
| `StepBound:89` | `step_W_le` | PASS | Identity; A |
| `StepBound:103` | `step_U_diff` | PASS | Identity; A |
| `StepBound:125` | `step_U_le` | PASS | Identity; A |
| `StepBound:142` | `fderiv_pi_apply` | PASS | Identity; A |
| `StepBound:150` | `step_bracket_N` | PASS | Identity; A |
| `StepCoeff:30` | `stepF0` | PASS | Identity; definition classification retained |
| `StepCoeff:33` | `stepF1` | PASS | Identity; definition classification retained |
| `StepCoeff:36` | `coeff_add_sum` | PASS | Identity; A |
| `StepCoeff:65` | `truncate_add_sum` | PASS | Identity; A |
| `StepCoeff:91` | `taylor_eq` | PASS | Identity; A |
| `StepCoeff:101` | `stepF1_eq` | PASS | Identity; A |
| `StepCoeff:116` | `norm_half_single` | PASS | Identity; A |
| `StepCoeff:124` | `stepF0_diff` | PASS | Identity; A |
| `StepCoeff:131` | `stepF1_diff` | PASS | Identity; A |
| `StepCoeff:143` | `stepF0_periodic` | PASS | Identity; A |
| `StepCoeff:149` | `stepF1_periodic` | PASS | Identity; A |
| `StepCoeff:160` | `norm_stepF0_le` | PASS | Identity; A |
| `StepCoeff:165` | `norm_stepF1_le` | PASS | Identity; A |
| `StepCoeff:181` | `truncate_congr_param` | PASS | Identity; A |
| `StepCoeff:189` | `truncate_truncate` | PASS | Identity; A |
| `StepCoeff:211` | `continuous_stepF0` | PASS | Identity; A |
| `StepCoeff:218` | `continuous_stepF1` | PASS | Identity; A |
| `StepCoeff:225` | `cutoff_decomp` | PASS | Identity; A |
| `StepCoeff:237` | `cutoff_R0` | PASS | Identity; A |
| `StepCoeff:244` | `cutoff_R1` | PASS | Identity; A |
| `StepCoeff:260` | `stepFam0` | PASS | Identity; definition classification retained |
| `StepCoeff:262` | `stepFam1` | PASS | Identity; definition classification retained |
| `StepCoeff:264` | `cut_stepFam0` | PASS | Identity; A |
| `StepCoeff:267` | `cut_stepFam1` | PASS | Identity; A |
| `StepCoeff:272` | `p11_cutoff_coeff` | PASS | Identity; A |
| `StepCoeff:367` | `cutoff_coefficients` | PASS | Identity; A |
| `StepData:28` | `P11Step` | PASS | Identity; definition classification retained |
| `StepData:57` | `p11StepA` | PASS | Identity; definition classification retained |
| `StepData:59` | `p11StepKappa` | PASS | Identity; definition classification retained |
| `StepData:60` | `p11StepRem` | PASS | Identity; definition classification retained |
| `StepData:64` | `p11R0` | PASS | Identity; definition classification retained |
| `StepData:66` | `p11R1` | PASS | Identity; definition classification retained |
| `StepData:68` | `p11DeltaH` | PASS | Identity; definition classification retained |
| `StepData:69` | `p11DeltaW` | PASS | Identity; definition classification retained |
| `StepData:71` | `p11StepPhi` | PASS | Identity; definition classification retained |
| `StepData:75` | `p11StepMap` | PASS | Identity; definition classification retained |
| `StepData:78` | `p11Normal` | PASS | Identity; definition classification retained |
| `StepData:80` | `p11StepRemainder` | PASS | Identity; definition classification retained |
| `StepData:84` | `P11StepHyp` | PASS | Identity; definition classification retained |
| `StepHom:31` | `stepP0` | PASS | Identity; definition classification retained |
| `StepHom:35` | `stepP1` | PASS | Identity; definition classification retained |
| `StepHom:41` | `step_B_open` | PASS | Identity; A |
| `StepHom:44` | `step_r_pos` | PASS | Identity; A |
| `StepHom:47` | `step_dr` | PASS | Identity; A |
| `StepHom:50` | `step_E_nonneg` | PASS | Identity; A |
| `StepHom:56` | `step_lambda_nonneg` | PASS | Identity; A |
| `StepHom:60` | `step_A_nonneg` | PASS | Identity; A |
| `StepHom:66` | `p11_step_small` | PASS | F1 resolved; exact renamed type/proof; unique public short name; A |
| `StepHom:74` | `step_hdiv` | PASS | Identity; A |
| `StepHom:79` | `step_M_nonneg` | PASS | Identity; A |
| `StepHom:82` | `step_hm0` | PASS | Identity; A |
| `StepHom:102` | `step_hm1` | PASS | Identity; A |
| `StepHom:129` | `step_affHyp` | PASS | Identity; A |
| `StepLie:32` | `flow_displacement_t` | PASS | Identity; A |
| `StepLie:80` | `norm_fderiv_dir_le` | PASS | Identity; A |
| `StepLie:103` | `norm_fderiv_phase_le` | PASS | Identity; A |
| `StepParameter:24` | `step_slice_diff` | PASS | Identity; A |
| `StepParameter:31` | `canonical_step_param` | PASS | Identity; A |
| `StepReal:26` | `step_R1_eq` | PASS | Identity; A |
| `StepReal:38` | `step_R_real` | PASS | Identity; A |
| `StepReal:73` | `step_hm_real` | PASS | Identity; A |
| `StepReal:89` | `coeff_zero_real` | PASS | Identity; A |
| `StepReal:101` | `step_avg_real` | PASS | Identity; A |
| `StepReal:110` | `step_real_flow` | PASS | Identity; A |
| `StepReal:131` | `step_Rp_real` | PASS | Identity; A |
| `StepRealFlow:29` | `stepV` | PASS | Identity; definition classification retained |
| `StepRealFlow:33` | `stepP1_entire` | PASS | Identity; A |
| `StepRealFlow:41` | `stepV_contDiff` | PASS | Identity; A |
| `StepRealFlow:50` | `stepV_bound` | PASS | Identity; A |
| `StepRealFlow:63` | `stepV_periodic` | PASS | Identity; A |
| `StepRealFlow:76` | `step_fderiv_re` | PASS | Identity; A |
| `StepRealFlow:90` | `stepV_fderiv` | PASS | Identity; A |
| `StepRealFlow:165` | `step_flow_real` | PASS | Identity; A |
| `StepRealFlow:208` | `step_real_lipschitz` | PASS | Identity; A |
| `StepRealFlow:242` | `canonical_step_real` | PASS | Identity; A |
| `StepRemainder:26` | `step_norm_single_le_one` | PASS | Identity; A |
| `StepRemainder:30` | `strip_of_close` | PASS | Identity; A |
| `StepRemainder:39` | `strip_add_dir` | PASS | Identity; A |
| `StepRemainder:49` | `poissonBracket_congr` | PASS | Identity; A |
| `StepRemainder:57` | `step_A_le_quarter` | PASS | Identity; A |
| `StepRemainder:62` | `step_Aeta_le` | PASS | Identity; A |
| `StepRemainder:69` | `step_z_mem` | PASS | Identity; A |
| `StepRemainder:77` | `step_bracket_bound` | PASS | Identity; A |
| `StepRemainder:149` | `step_remainder_eq` | PASS | Identity; A |
| `StepRemainder:212` | `step_remainder_le` | PASS | Identity; A |

## Fresh validation receipts

Every audit-owned Lean/Lake/checker/ABI command was sequential with `LEAN_NUM_THREADS=1`; direct commands used `nice -n 5` and the compile-gate wrapper supplies nice for the build. No source change, root regeneration, clean, update, cache fetch, or resource override was performed.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ac8 KAM.Planetary.MaximalStep.StepRealFlow KAM.Planetary.MaximalStep.StepParameter
```

Exit **0**. Exact gate/final output:

```text
[inp-gate] slot 1 acquired 17:32:21 for KAM.Planetary.MaximalStep.StepRealFlow KAM.Planetary.MaximalStep.StepParameter
Build completed successfully (9151 jobs).
```

These targets cover all ten Step modules. The build reports cached/replayed warnings about unused variables/simp arguments and the existing `if_true` deprecation at `StepRealFlow.lean:130`; no errors or default-heartbeat failure.

2. Axiom and renamed-type probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AC8Audit2.lean > .lake/abi-scratch/P11AC8Audit2Axioms.out 2>&1
```

Exit **0**. The probe imported only StepRealFlow and StepParameter and checked:

```lean
example {n : ℕ} (S : KAM.Planetary.P11Step n) :
    4 * (n + 1) * KAM.Planetary.p11StepA S ≤ S.sigma :=
  KAM.Planetary.p11_step_small S
```

It then issued `#print axioms` for all 81 public package theorems, generated from the declaration inventory. Exactly 81 reports were parsed and each axiom list was exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or error. Selected exact output:

```text
'KAM.Planetary.p11_step_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.canonical_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.canonical_step_simple_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_cutoff_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cutoff_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.canonical_step_param' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.canonical_step_real' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay (one invocation for all ten modules):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.StepData KAM.Planetary.MaximalStep.StepCoeff KAM.Planetary.MaximalStep.StepHom KAM.Planetary.MaximalStep.StepLie KAM.Planetary.MaximalStep.StepBound KAM.Planetary.MaximalStep.StepRemainder KAM.Planetary.MaximalStep.Step KAM.Planetary.MaximalStep.StepParameter KAM.Planetary.MaximalStep.StepReal KAM.Planetary.MaximalStep.StepRealFlow > .lake/abi-scratch/P11AC8Audit2Kernel.out 2>&1
```

Exit **0**. Exact output:

```text
replaying KAM.Planetary.MaximalStep.StepRealFlow
replaying KAM.Planetary.MaximalStep.StepReal
replaying KAM.Planetary.MaximalStep.StepParameter
replaying KAM.Planetary.MaximalStep.Step
replaying KAM.Planetary.MaximalStep.StepRemainder
replaying KAM.Planetary.MaximalStep.StepBound
replaying KAM.Planetary.MaximalStep.StepLie
replaying KAM.Planetary.MaximalStep.StepHom
replaying KAM.Planetary.MaximalStep.StepCoeff
replaying KAM.Planetary.MaximalStep.StepData
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/P11AC8Audit2Lint.out 2>&1
```

Exit **1**, solely the expressly allowed generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (726 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module checks, frozen-anchor guard and all 144 elaborated frozen ABI hashes pass. No forbidden-token, line-length or file-size failure was emitted. `KAM.lean` was left untouched.

5. Static integrity, import quarantine and report validation:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty diff; only the multiple-merge-base warning described above.
- `git diff --check`: exit 0, empty output. Initial tracked/untracked git status was clean; final status adds only this report.
- All ten Step files pass the module/header/public-interface checks. Line counts: Step 232; StepBound 181; StepCoeff 380; StepData 100; StepHom 153; StepLie 142; StepParameter 83; StepReal 173; StepRealFlow 261; StepRemainder 248. Maximum 380 < 1500.
- Comment/string-masked Step-source scan: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option`. No heartbeat, synthesis or recursion override was used.
- Recursive import scan from all ten Step modules: **105 KAM modules**, **zero frozen theorem imports**, **zero provider imports**. Frozen definition imports remain permitted; no DRAFT_SORRY anchor is reached.
- Public-name scan: **104 declarations; zero reused public short names** in KAM. The remaining private match is excluded as required by the public-name gate.
- The report's declaration ledger has 104 unique rows, balanced code fences and no trailing whitespace. Scratch scripts, probe files and logs owned by this audit were deleted after recording these receipts.

## Errata, deviations and remaining uncertainty

No new source/blueprint defect, deviation or mathematical uncertainty was found in this pure rename. Audit-1's D1 remains explicitly inherited: the older local design at `docs/tracks/P/design/P11A-LEAN-DESIGN.md:2191` still prints `∀ z, p11Cutoff T R z = ...` without `z.2 ∈ B`. That unrestricted identity fails for non-integrable off-B slices, as independently checked in round 1. The handoff's overnight ruling and current signature/implementation supply the membership guard; their bytes are unchanged. This round does not re-prove that counterexample or alter the approved amendment.

Likewise, the inherited blueprint reality issue at `blueprint-P/parts/p11a2-cutoff-step.tex:248,264` remains reported: “if reality is wanted” guards the input while the real-Lipschitz conclusion is printed unguarded. The signed `canonical_step_real` retains its already approved explicit reality premise. No pinned-paper erratum or frozen declaration defect is newly alleged here.

F1 requires no further change. **P11A-C8 is accepted, PASS WITH NOTES solely for the permitted stale generated root.** This is infrastructure package acceptance, not closure of a frozen physical headline or a re-audit of inherited C7 mathematics.
