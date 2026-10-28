# N12-09 independent package audit 1

Overall verdict: **PASS WITH NOTES** for N12-09 (`bpN:p12:shells` and `bpN:p12:envelopes`). The mathematical contracts and proofs pass; notes concern generated-root lint and nonblocking compiler warnings. No frozen anchor is proved or sealed by this package. In particular, this is not closure of `averaging_mean` or `averaging_most`.

## Scope and authority

Audited 2026-10-28 in `/root/code/KAM-inp-n1209`, HEAD `4f2be17475d1635e94917fea80123ef543d725d4`, against `inp` at `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`, using `git diff inp...HEAD`. The entire diff adds only Shells (398 lines) and EnvelopeIntegrals (505 lines). Audit focus limits proof review to those modules. Read AGENTS, PLAN, DECISIONS, package brief, handoff, design N12-09 row/proof plan, both design audits, Part 12 blueprint, averaging track statements, frozen averaging anchors and relevant frozen definitions. Missing worktree-local signature/audit paths were resolved to the explicitly referenced main inp worktree. No subagents were used.

The user's exact report destination overrides the generic brief's main-worktree destination. The pre-existing untracked handoff is preserved. No repository file other than this report was edited; temporary probes/logs are confined to `.lake/abi-scratch/` and removed at closeout. No state-changing git operation or generated-root regeneration was performed.

## Statement and proof assessment

All four principal declaration headers are byte-identical (from `theorem` through `:=`) to both the design Appendix and `/root/code/KAM-inp/.drafts/design/N12Signatures.lean`. Fresh renamed declarations copied from the design elaborate with the submitted results as their bodies. No premise, quantifier order, norm, carrier, constant or dependence changes. `shells` and `envelopes` construct constants from `AveragingData`; the distinctly named `_from_slab` helpers legitimately consume the proved dependency `AvgSlabBound`.

The dyadic proof bounds by overlapping sublevel indicators, which are safe nonnegative majorants. AE cutoff follows from the bounded frequency on G. The ψ proof handles zero logarithm input and the natural ceiling; ψD and residual use inverse estimates only when outer-shell membership implies nonzero argument. Ω₀≥0 is derived from 0∈G, with R>0. Envelope integration uses restricted AE measurability and Tonelli, then actual summability from `coef` before identifying the real sum. Zero modes vanish by their norm. For the matrix term, the proof uses the stronger max/Euclidean ratio≤1 and then sqrt(n)≥1, preserving the designed cB. The ε specialization proves κ avgLog κ≤1 and keeps the larger promised constants.

There is no new structure, instance or conclusion-shaped source premise. The unused `hM` is the prescribed frequency-matrix bound; integration of the already defined envelope only needs the scalar M₂≥0. Its omission from the proof does not weaken or change the signed statement.

## Declaration-by-declaration review

Names below are in `KAM.Nekhoroshev`. Every new public declaration has a row. Helper rows implement the named node rather than claiming to replace a complete source theorem.

| Node | Lean declaration (file:line) | Verdict | Reason / note |
|---|---|---|---|
| shells / sh-shells, sh-i–iii | `AvgShell.measurable_sub` (Shells:38) | PASS | Closed sublevel indicator is measurable. |
| shells / sh-shells, sh-i–iii | `AvgShell.pointwise` (Shells:43) | PASS | Finite dyadic induction; overlapping sublevels only enlarge the majorant. |
| shells / sh-shells, sh-i–iii | `AvgShell.shell_bound` (Shells:68) | PASS | AE domination, measurable majorant, slab measure bound and finite nonnegative sum. |
| shells / sh-shells, sh-i–iii | `AvgShell.geom_shell_bound` (Shells:110) | PASS | Geometric series bound gives exactly 5 A V κ. |
| shells / sh-shells, sh-i–iii | `AvgShell.euclid_ge_one` (Shells:134) | PASS | Nonzero integer coordinate supplies Euclidean length at least one. |
| shells / sh-shells, sh-i–iii | `AvgShell.norm_le_euclid` (Shells:148) | PASS | Pi max norm bounded by Euclidean scalar gauge. |
| shells / sh-shells, sh-i–iii | `AvgShell.norm_le_mode` (Shells:157) | PASS | Pi max norm bounded by integer l1 size. |
| shells / sh-shells, sh-i–iii | `AvgShell.mode_nonneg` (Shells:163) | PASS | Sum of absolute values. |
| shells / sh-shells, sh-i–iii | `AvgShell.abs_Q_le` (Shells:166) | PASS | Literal frequency dot product, bounded by modeSize times frequency max norm. |
| shells / sh-shells, sh-i–iii | `AvgShell.Q_aemeasurable` (Shells:175) | PASS | Frequency continuous on G; finite dot product measurable on restricted measure. |
| shells / sh-shells, sh-i–iii | `AvgShell.vol_restrict` (Shells:184) | PASS | Restricted volume equals intersection volume; literal slab specification used. |
| shells / sh-shells, sh-i–iii | `AvgShell.exists_N` (Shells:194) | PASS | Archimedean dyadic bound; Ω₀ nonnegativity is an unused, removable helper premise. |
| shells / sh-shells, sh-i–iii | `AvgShell.measurableSet_avgG` (Shells:201) | PASS | Closed max-norm ball. |
| shells / sh-shells, sh-i–iii | `AvgShell.ae_Q_le` (Shells:203) | PASS | Domain-restricted frequency bound implies AE dyadic cutoff. |
| shells / sh-shells, sh-i–iii | `AvgShell.integral_psiD` (Shells:212) | PASS | Guarded reciprocal square on outer shells; inner global κ^-2 bound. |
| shells / sh-shells, sh-i–iii | `AvgShell.integral_resid` (Shells:236) | PASS | Global residual at most one and guarded reciprocal-square outer bound. |
| shells / sh-shells, sh-i–iii | `AvgShell.integral_psi` (Shells:262) | PASS | N=ceil(log-plus(x)/log(2)); 2/log(2)<3; handles x=0 explicitly. |
| shells / sh-shells, sh-i–iii | `avgLog` (Shells:322) | PASS | Exact 1+log(1/κ); used with positive κ, at most one. |
| shells / sh-shells, sh-i–iii | `AvgShell.avgLog_nonneg` (Shells:326) | PASS | Logarithm nonnegative on 0<κ≤1 (the lemma bounds log, despite its name). |
| shells / sh-shells, sh-i–iii | `AvgShell.log_le` (Shells:329) | PASS | Log product and log(P)≤P-1, with P=0 handled separately. |
| shells / sh-shells, sh-i–iii | `shells_from_slab` (Shells:340) | PASS | Exact design telescope and all four inequalities; Ω₀≥0 derived at I=0. |
| shells / sh-shells, sh-i–iii | `shells` (Shells:377) | PASS | Exact design; slab and compact witnesses are constructed before κ and k. |
| envelopes / en-term, en-choice | `avgSigma` (EnvelopeIntegrals:31) | PASS | Exact nonzero-mode cubic exponential sum; convergence paid under d.hs>0 by wt_summable. |
| envelopes / en-term, en-choice | `avgCW` (EnvelopeIntegrals:33) | PASS | Exact 3 C₁ (1+Ω₀) σ. |
| envelopes / en-term, en-choice | `avgCB` (EnvelopeIntegrals:34) | PASS | Exact σ C₁ [6n(1+Ω₀)/s+5 sqrt(n) M₂]. |
| envelopes / en-term, en-choice | `avgCR` (EnvelopeIntegrals:36) | PASS | Exact 10π C₁ σ. |
| envelopes / en-term, en-choice | `avgCPhi` (EnvelopeIntegrals:37) | PASS | Exact 4cB/s+8πcW/s+cR. |
| envelopes / en-term, en-choice | `AvgEnv.wt` (EnvelopeIntegrals:43) | PASS | Exact summand of avgSigma, zero only at zero mode. |
| envelopes / en-term, en-choice | `AvgEnv.avgBeta_nonneg` (EnvelopeIntegrals:46) | PASS | Positive exponential. |
| envelopes / en-term, en-choice | `AvgEnv.wt_nonneg` (EnvelopeIntegrals:48) | PASS | Zero at zero mode; otherwise positive polynomial times exponential. |
| envelopes / en-term, en-choice | `AvgEnv.wt_summable` (EnvelopeIntegrals:56) | PASS | Dominated by the proved polynomial-exponential summability in coef. |
| envelopes / en-term, en-choice | `AvgEnv.sigma_eq` (EnvelopeIntegrals:65) | PASS | Definitional equality with wt sum. |
| envelopes / en-term, en-choice | `AvgEnv.sigma_nonneg` (EnvelopeIntegrals:67) | PASS | Nonnegative real tsum; no convergence-dependent upper bound inferred here. |
| envelopes / en-term, en-choice | `AvgEnv.aem_comp` (EnvelopeIntegrals:69) | PASS | Measurable scalar function composed with restricted AE-measurable avgQ. |
| envelopes / en-term, en-choice | `AvgEnv.env_aem` (EnvelopeIntegrals:74) | PASS | Countable ENNReal sum is AE-measurable. |
| envelopes / en-term, en-choice | `AvgEnv.env_le` (EnvelopeIntegrals:81) | PASS | Tonelli, termwise bound, and proved real summability justify ofReal_tsum. |
| envelopes / en-term, en-choice | `AvgEnv.lint_const_mul` (EnvelopeIntegrals:95) | PASS | Nonnegative finite scalar factored out of lintegral. |
| envelopes / en-term, en-choice | `AvgEnv.contPsi` (EnvelopeIntegrals:101) | PASS | Corrector differentiability gives continuity. |
| envelopes / en-term, en-choice | `AvgEnv.contPsiD` (EnvelopeIntegrals:104) | PASS | Positive denominator for κ>0. |
| envelopes / en-term, en-choice | `AvgEnv.contRes` (EnvelopeIntegrals:108) | PASS | Positive denominator for κ>0. |
| envelopes / en-term, en-choice | `AvgEnv.avgLog_ge_one` (EnvelopeIntegrals:111) | PASS | Exact domain restriction 0<κ≤1. |
| envelopes / en-term, en-choice | `AvgEnv.mul_avgLog_le` (EnvelopeIntegrals:114) | PASS | log(x)≤x-1 gives κ avgLog κ≤1 for all κ>0, a valid strengthening. |
| envelopes / en-term, en-choice | `AvgEnv.avgLog_le` (EnvelopeIntegrals:120) | PASS | Divide previous inequality by positive κ. |
| envelopes / en-term, en-choice | `AvgEnv.term_W` (EnvelopeIntegrals:133) | PASS | Shell estimate times mode weight, dominated by cubic polynomial weight. |
| envelopes / en-term, en-choice | `AvgEnv.term_W1` (EnvelopeIntegrals:165) | PASS | Preserves 2π and extra modeSize; cubic weight dominates. |
| envelopes / en-term, en-choice | `AvgEnv.term_R` (EnvelopeIntegrals:196) | PASS | Pi/Euclidean ratio≤1; preserves 10π C₁ κ. |
| envelopes / en-term, en-choice | `AvgEnv.term_B` (EnvelopeIntegrals:229) | PASS | Splits ψ and ψD; log bound≤1/κ; sqrt(n)≥1 slack retains exact cB. |
| envelopes / en-term, en-choice | `AvgEnv.env_zero` (EnvelopeIntegrals:299) | PASS | Zero integer mode has zero Pi norm. |
| envelopes / en-term, en-choice | `AvgEnv.wt_zero` (EnvelopeIntegrals:304) | PASS | Literal zero-mode branch. |
| envelopes / en-term, en-choice | `AvgEnv.kappa_part` (EnvelopeIntegrals:312) | PASS | Four envelopes via env_le; each zero mode killed explicitly. |
| envelopes / en-term, en-choice | `AvgEnv.W1env_aem` (EnvelopeIntegrals:366) | PASS | Restricted AE measurability, using κ>0 only. |
| envelopes / en-term, en-choice | `AvgEnv.Benv_aem` (EnvelopeIntegrals:374) | PASS | Restricted AE measurability, using κ>0 only. |
| envelopes / en-term, en-choice | `AvgEnv.eps_part` (EnvelopeIntegrals:382) | PASS | ε=κ² and κ avgLog κ≤1 give stronger intermediate bounds; displayed 4 and 8π constants retained. |
| envelopes / en-term, en-choice | `envelopes_from_slab` (EnvelopeIntegrals:461) | PASS | Exact design; restricts bounds from closedBall R to G; hΩ0 and hM unused but prescribed. |
| envelopes / en-term, en-choice | `envelopes` (EnvelopeIntegrals:484) | PASS | Exact design; constructs slab, frequency, matrix witnesses before κ and ε. |

## Definition classification

All seven new definitions are intended arithmetic/summation objects: `avgLog`, `avgSigma`, `avgCW`, `avgCB`, `avgCR`, `avgCPhi`, and helper `AvgEnv.wt`. There are no choice-based fillers or invented models. `avgSigma` and `wt` exclude exactly k=0; all constants have literal designed bodies. The total real `tsum` may use its conventional value outside the convergent regime (e.g. s≤0), but no audited bound relies on that behavior: valid data supply s>0 and `wt_summable` proves summability before the integral estimate. The logarithm and divisions are likewise only used with their stated positive-domain guards. This is not junk-dependent correctness.

## Imports and anchor applicability

The project import closure has no provider and no frozen theorem imports. All 18 reachable frozen modules are definition anchors, each manifest state `SEALED`; no DRAFT_SORRY theorem is consumed. `AveragingData` contains dimension/positivity, genuine analytic hypotheses and the approved frequency-rank alternatives, not the slab or shell conclusions. The downstream frozen averaging anchors remain outside this package. Provider/frozen exact-type and seal-body probes are therefore **not applicable**, rather than passed vacuously. The four design-copy elaborations check the actual package interface instead.

## Independent validation

All audit-owned Lean/Lake/checker invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`; the targeted build used the prescribed compile gate. Other sessions' processes were not modified.

Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1209 KAM.Nekhoroshev.Averaging.EnvelopeIntegrals
```

Exit 0. Gate receipt: `[inp-gate] slot 2 acquired 10:01:47 for KAM.Nekhoroshev.Averaging.EnvelopeIntegrals`. Final output: `Build completed successfully (3192 jobs).` Both audited modules replayed. Warnings: unused `j` (Shells:164), unused `hΩ0` (Shells:194), deprecated `AEMeasurable.ennreal_tsum` (EnvelopeIntegrals:78), deprecated `if_neg` (:266), unused prescribed `hΩ0` (:462) and `hM` (:464). No heartbeat or elaboration failure.

Design-copy and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1209Audit.lean
```

Exit 0; four fresh design-copy declarations elaborate with no diagnostics. The probe contains `#print axioms` for every one of the 48 public theorems; exact output follows:

```text
'KAM.Nekhoroshev.AvgShell.measurable_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.shell_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.geom_shell_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.euclid_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.norm_le_euclid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.norm_le_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.mode_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.abs_Q_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.Q_aemeasurable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.vol_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.exists_N' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.measurableSet_avgG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.ae_Q_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.integral_psiD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.integral_resid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.integral_psi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.avgLog_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgShell.log_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.shells_from_slab' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.shells' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.avgBeta_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.wt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.wt_summable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.sigma_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.sigma_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.aem_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.env_aem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.env_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.lint_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.contPsi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.contPsiD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.contRes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.avgLog_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.mul_avgLog_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.avgLog_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.term_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.term_W1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.term_R' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.term_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.env_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.wt_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.kappa_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.W1env_aem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.Benv_aem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgEnv.eps_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.envelopes_from_slab' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.envelopes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay (one invocation):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.EnvelopeIntegrals KAM.Nekhoroshev.Averaging.Shells
```

Exit 0; exact output:

```text
replaying KAM.Nekhoroshev.Averaging.Shells
replaying KAM.Nekhoroshev.Averaging.EnvelopeIntegrals
```

Source hygiene: both files have required copyright, module declaration, public imports, module docstring and exposed public noncomputable section. Unicode line-length scan: **zero lines over 100 characters** in either file. File lengths are 398 and 505, below 1500. Forbidden-word/override scan: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option` in either file. `git diff --check inp...HEAD` exits 0 with no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exits 0 with empty output.

Repository lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, exclusively for the expressly permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (521 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The 100-character check, module check, frozen guard and all 144 ABI hashes pass. The report does not call this a literal zero-exit lint run.

## Defects, deviations and limitations

No new suspected blueprint defect, pinned-source erratum, frozen-statement defect, or meaning-changing formalization deviation was identified. Blueprint Part 12:165–189 gives exactly the four shell and six envelope inequalities proved here. The inherited Nei76 maximum/interchange issue is already documented by the track statements and design audits; these local nonnegative integral estimates introduce no interchange of time supremum and initial-data integral. No new pinned-PDF re-audit or downstream stopped-flow/root proof audit is claimed.

`avgLog` lives in Shells and `AvgSlabBound` remains in Slab, matching the approved interface roles. The finite overlapping-sublevel majorant and stronger intermediate ε/log and norm-ratio bounds are valid proof choices. Generated root regeneration remains an orchestrator action, as required by the brief. The six compiler warnings above are nonblocking maintenance notes.

Input hashes (SHA-256):

| Input | Hash |
|---|---|
| `docs/tracks/N/design/N12-LEAN-DESIGN.md` | `d66059fe35c7b3f76307ae60df90aa3da66ea089cd3ec073b39cbe2ffd1b6370` |
| `/root/code/KAM-inp/.drafts/design/N12Signatures.lean` | `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369` |
| `blueprint-N/parts/p12-averaging.tex` | `dd549dc5c3069e1a185767b5fa580d979963fa920a4b9e7939529047d13ebbfc` |
| `KAM/Nekhoroshev/Averaging/Shells.lean` | `fff73e63ea70908551c9ac932d79d01a5364d24932d9210391342a9124e235be` |
| `KAM/Nekhoroshev/Averaging/EnvelopeIntegrals.lean` | `d126f2bd430fad15632a825544e1148a6c1e7b33fbb206dd791222f3c9faa7e0` |

## Closeout

Only the requested audit report was created; the original untracked handoff remains. All audit-owned probe/log files were removed after embedding their results. Report whitespace validation with `git diff --no-index --check /dev/null docs/tracks/N/audits/N12-09-audit-1.md` produces no whitespace diagnostics (exit 1 is the new-file difference status). Protected-path comparison remains empty. Verdict: **PASS WITH NOTES for the two N12-09 nodes; no frozen anchor seal claimed.**
