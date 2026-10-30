# SO-DION independent audit 1

Verdict: **PASS WITH NOTES** for both additive modules. No mathematical or implementation blocker found. The note is the brief-permitted stale generated `KAM.lean` lint exception (see exact receipt below). There is no frozen theorem anchor or provider in this package; “seal-ready” is therefore not an applicable claim. No lunar certificate, barrier, confinement theorem, or graph node is closed by this audit.

Audited HEAD `dc8590c0bd2c20296e1d5766bcaac5fee098bd7d` against live `inp` `680e9f21546488841aa8db69d2d6c9060c5d63a9`, using the full `git diff inp...HEAD`. Scope: two new Lean modules (456 and 124 lines) and the 71-line handoff; zero deletions and no existing declaration changes. Initial working tree was clean. Only this report is a repository edit; scratch probes were removed after use. The user's exact worktree report path overrides the generic brief's main-worktree destination.

Authority read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, `/root/code/KAM-inp/.drafts/briefs/offload-main/SO-DION.md`, and `SO-DION-handoff.md` including all five AUDIT FOCUS items. SO has no `docs/tracks/SO/statement.md`; the applicable original design is `docs/tracks/SO/design/SO-LEAN-DESIGN.md` §§I.0b/I.3 (lines 2289–2316, 2397–2425), plus `docs/campaign/design/SPIN-ORBIT-PLAN.md` and `docs/tracks/SO/FREEZE-PROPOSAL.md`. The general-N contract comes from the SO-DION brief; it extends the old N=40 design under new names. No I/N/P theorem is implemented here, so unrelated frozen I/N/P provider/seal comparisons are inapplicable.

## Mathematical refutation attempts

1. **Closed forms and quadratics.** In `QuadraticDiophantineN.lean:47–129`, L=N²−N−1 is nonzero for every natural N: N=0,1 give −1, and N≥2 gives L>0. Also N+g>0. Rationalization gives 1/(N+g)=(2N−1−√5)/(2L), with D=2L. Thus no totalized division hides a singular natural index. Writing m=2N−1, the conjugate pairs are (2L±m∓√5)/(2L). Their sums are (2N²−4N−1)/L and (2N²−3)/L, and products are (N²−3N+1)/L and (N²+N−1)/L. Both displayed quadratic equations are correct for all natural N. Lean proves polynomial identities; it does not separately export minimality/irreducibility. The nonzero rational √5 coefficient also establishes degree two mathematically.

2. **Norm argument.** `norm_boundN` (`QuadraticDiophantineN.lean:134–225`) uses the integer M=a²C+abB+Lb²=L(ax+b)(ay+b). Irrationality of both x and y and (a,b)≠(0,0) prove M≠0, hence |ax+b||ay+b|≥1/L. This is the correctly scaled integer norm; it does not incorrectly assert that the product itself is an integer. Put s=|a|+|b| and d=|ax+b|. For s<2, integrality forces either a=0 or b=0, so c≤1/2 and x≥1/2 suffice. For s≥2, assuming d<c/s gives ds<c and d<c/2. The conjugate estimate is |ay+b|≤d+sδ with δ=√5/L. Consequently d|ay+b|≤d(d+sδ)<c²/4+cδ≤1/L, a contradiction. Signs, strict inequalities, positivity of every denominator, and the a=0 cases are all supplied. The private helper's norm/irrationality hypotheses are discharged by `lower_aux`, rather than exposed as missing public proof obligations.

3. **Numeric constant.** `gamma_key` (lines 242–257) reduces c²/4+c√5/L≤1/L at c=2/(N+2) to L+2√5(N+2)≤(N+2)², or 2√5(N+2)≤5N+5. Since √5<9/4, the left side is strictly less than (9/2)(N+2), and 5N+5−(9/2)(N+2)=N/2−4≥0 at N≥8. All multiplication factors are positive. `lower_aux` (267–307) proves L>0, both conjugates irrational, the exact sum/product/separation, and x≥1/2 for both signs. No extra public premise beyond N≥8 and a nonzero integer pair is introduced. N≥8 is stronger coverage than the brief's allowed N≥40 route; optimality of c is not claimed.

4. **Norm and transfer.** The frozen `KAM/Frozen/Defs/IsDiophantine.lean:24–25` is literally γ/(Σ|kᵢ|)^τ≤|Σkᵢωᵢ|. `isDiophantine_of_lowerN` (325–338) unfolds that definition using `Fin.sum_univ_two` and `Real.rpow_one`. The rotation (341–366) uses T(a,b)=(a,b−a), which preserves the divisor, sends nonzero pairs to nonzero pairs, and has ℓ¹ bound |T(a,b)|₁≤2|(a,b)|₁. Thus γ becomes γ/2=1/(N+2). `RotFreqN.lean:62–81` then uses positive rational κ and the landed `soIsDiophantine_smul`, yielding κ/(N+2), at τ=1. Both `KAM/Certificate/Soundness.lean:61–65` and `KAM/CertificateSharp/Sound.lean:38–42` consume precisely this frozen definition. No alternate norm or predicate is introduced.

5. **Frequency-box attachment.** `RotFreqN.lean:38–59` has rational coefficients (N is cast before rational subtraction), two rows of lengths 2 and 1, and exact real equality to `algFreq 2 … √5`. The signs are −mκ/D,+κ/D for minus and +mκ/D,−κ/D for plus; second coordinate κ. These match polynomial-in-root semantics in `KAM/Certificate/Freq.lean:39–42`. Fresh Lean probes for both signs compose these equalities with `sqrt_mem_of_checkRootEnclosure` (`Arith/Roots.lean:62–67`) and `algFreq_encloses` (`Freq.lean:82–84`), deriving `FreqEncloses` from the exact root/box checks. This verifies consumer compatibility, not that any concrete certificate box passes. The certificate must use τ=1 and γ≤κ/(N+2); reducing γ still requires the ordinary monotonicity argument if equality is not used.

6. **N=40 attachment.** Three fresh `type_of%` assignments compare the new minus original-frame, plus rotated-frame, and minus RotFreq sanity exports with their landed exports. All elaborate. Two further probes specialize the new algebraic descriptions at 40 and normalize rational arithmetic to the exact landed rows ±79κ/3118, ∓κ/3118, κ. The first attempt used `simpa`, which did not evaluate rational numerals under `algFreq`; replacing scratch-only simplification with `norm_num` discharged both. This was a probe tactic issue, not a package defect. The package sanity proofs invoke the general-N results, not the landed Diophantine theorem proofs.

Exact constants:

| N | Original | Rotated | RotFreq |
|---|---|---|---|
| 40 | 1/21 | 1/42 | κ/42 |
| 55 | 2/57 | 1/57 | κ/57 |
| 60 | 1/31 | 1/62 | κ/62 |
| 65 | 2/67 | 1/67 | κ/67 |

## Declaration-by-declaration results

Namespaces are written explicitly below. Every row is compared to the SO-DION task/handoff contract; these additive declarations have no separately numbered blueprint nodes.

| Contract/node | Lean declaration | Verdict | Reason |
|---|---|---|---|
| Definition | `KAM.Certificate.lunarNuMinusN` | PASS | Literal intended scalar formula, all natural N. |
| Definition | `KAM.Certificate.lunarNuPlusN` | PASS | Literal intended scalar formula, all natural N. |
| Definition | `KAM.Certificate.lunarGammaN` | PASS | Literal intended scalar formula, all natural N. |
| Closed form | `KAM.Certificate.lunarNuMinusN_eq` | PASS | Exact equality, all natural N; rational algebraic rows in RotFreq. |
| Closed form | `KAM.Certificate.lunarNuPlusN_eq` | PASS | Exact equality, all natural N; rational algebraic rows in RotFreq. |
| Quadratic identity | `KAM.Certificate.lunarNuMinusN_quadratic` | PASS | Exact coefficients, all natural N. |
| Quadratic identity | `KAM.Certificate.lunarNuPlusN_quadratic` | PASS | Exact coefficients, all natural N. |
| Norm lower bound | `KAM.Certificate.lunarNuMinusN_lower` | PASS | N≥8; arbitrary nonzero integer pair; ℓ¹ denominator. |
| Norm lower bound | `KAM.Certificate.lunarNuPlusN_lower` | PASS | N≥8; arbitrary nonzero integer pair; ℓ¹ denominator. |
| Original frame | `KAM.Certificate.lunarNuMinusN_isDiophantine` | PASS | Constant 2/(N+2), τ=1, N≥8. |
| Original frame | `KAM.Certificate.lunarNuPlusN_isDiophantine` | PASS | Constant 2/(N+2), τ=1, N≥8. |
| Rotation | `KAM.Certificate.lunarNuMinusN_rot_isDiophantine` | PASS | Constant 1/(N+2), τ=1, N≥8. |
| Rotation | `KAM.Certificate.lunarNuPlusN_rot_isDiophantine` | PASS | Constant 1/(N+2), τ=1, N≥8. |
| N=40 sanity | `KAM.Certificate.lunarNuMinusN_forty` | PASS | Exact landed value/type; derived from new formulas/general theorem. |
| N=40 sanity | `KAM.Certificate.lunarNuPlusN_forty` | PASS | Exact landed value/type; derived from new formulas/general theorem. |
| N=40 sanity | `KAM.Certificate.lunarGammaN_forty` | PASS | Exact landed value/type; derived from new formulas/general theorem. |
| N=40 sanity | `KAM.Certificate.lunarNuMinusN_isDiophantine_forty` | PASS | Exact landed value/type; derived from new formulas/general theorem. |
| N=40 sanity | `KAM.Certificate.lunarNuPlusN_rot_isDiophantine_forty` | PASS | Exact landed value/type; derived from new formulas/general theorem. |
| Concrete index | `KAM.Certificate.lunarNuMinusN_rot_isDiophantine_65` | PASS | Exact specialization; κ>0 where scaled. |
| Concrete index | `KAM.Certificate.lunarNuPlusN_rot_isDiophantine_65` | PASS | Exact specialization; κ>0 where scaled. |
| Concrete index | `KAM.Certificate.lunarNuMinusN_rot_isDiophantine_60` | PASS | Exact specialization; κ>0 where scaled. |
| Concrete index | `KAM.Certificate.lunarNuPlusN_rot_isDiophantine_60` | PASS | Exact specialization; κ>0 where scaled. |
| Concrete index | `KAM.Certificate.lunarNuMinusN_rot_isDiophantine_55` | PASS | Exact specialization; κ>0 where scaled. |
| Concrete index | `KAM.Certificate.lunarNuPlusN_rot_isDiophantine_55` | PASS | Exact specialization; κ>0 where scaled. |
| Closed form | `KAM.SpinOrbit.lunarRotFreqMinusN_eq` | PASS | Exact equality, all natural N; rational algebraic rows in RotFreq. |
| Closed form | `KAM.SpinOrbit.lunarRotFreqPlusN_eq` | PASS | Exact equality, all natural N; rational algebraic rows in RotFreq. |
| Positive scaling | `KAM.SpinOrbit.lunarRotFreqMinusN_isDiophantine` | PASS | Constant κ/(N+2), τ=1, N≥8, κ>0. |
| Positive scaling | `KAM.SpinOrbit.lunarRotFreqPlusN_isDiophantine` | PASS | Constant κ/(N+2), τ=1, N≥8, κ>0. |
| Concrete index | `KAM.SpinOrbit.lunarRotFreqMinusN_isDiophantine_65` | PASS | Exact specialization; κ>0 where scaled. |
| Concrete index | `KAM.SpinOrbit.lunarRotFreqPlusN_isDiophantine_65` | PASS | Exact specialization; κ>0 where scaled. |
| Concrete index | `KAM.SpinOrbit.lunarRotFreqMinusN_isDiophantine_60` | PASS | Exact specialization; κ>0 where scaled. |
| Concrete index | `KAM.SpinOrbit.lunarRotFreqPlusN_isDiophantine_60` | PASS | Exact specialization; κ>0 where scaled. |
| Concrete index | `KAM.SpinOrbit.lunarRotFreqMinusN_isDiophantine_55` | PASS | Exact specialization; κ>0 where scaled. |
| Concrete index | `KAM.SpinOrbit.lunarRotFreqPlusN_isDiophantine_55` | PASS | Exact specialization; κ>0 where scaled. |
| N=40 sanity | `KAM.SpinOrbit.lunarRotFreqMinusN_forty` | PASS | Exact landed value/type; derived from new formulas/general theorem. |

## Definition classification and hypothesis/import review

All five new definitions are ordinary intended objects throughout their carriers:

- Public `lunarNuMinusN`, `lunarNuPlusN`, `lunarGammaN` (`QuadraticDiophantineN.lean:29,32,35`): exactly 1∓1/(N+g), 2/(N+2); denominators never vanish for N:ℕ.
- Private `lunarLR` (45): real polynomial N²−N−1, including its legitimate negative values at 0,1; no natural truncated subtraction.
- Private `rotIdxN` (341): explicit integer shear on all `Fin 2 → ℤ`.

There are no new abbrevs, structures, instances, choices, or fallback branches in definitions. The `_55/_60/_65` “instances” are named theorems, not typeclass instances. Every public theorem has only index, scalar, typing, and nonzero-pair premises. No conclusion-shaped premise or missing hard step is bundled in a public field.

Source traversal of both modules' KAM import closure found 8 KAM modules, one frozen anchor (`KAM.IsDiophantine`, SEALED), no DRAFT_SORRY anchors and no provider modules. Frozen provider type/seal-body probes are N/A: no provider or new frozen anchor is part of SO-DION.

## Independent checks and exact receipts

All Lean/Lake operations were serialized, under `LEAN_NUM_THREADS=1`, with `nice -n 5` (the build gate supplies nice internally). Default heartbeats were retained.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sodion KAM.Certificate.QuadraticDiophantineN KAM.SpinOrbit.RotFreqN
[inp-gate] slot 1 acquired 12:29:41 for KAM.Certificate.QuadraticDiophantineN KAM.SpinOrbit.RotFreqN
Build completed successfully (2201 jobs).
exit 0

LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.QuadraticDiophantineN KAM.SpinOrbit.RotFreqN
replaying KAM.SpinOrbit.RotFreqN
replaying KAM.Certificate.QuadraticDiophantineN
exit 0

LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SODionAudit.lean
exit 0 (32 axiom receipts below, seven successful examples)

python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sodion KAM.Certificate.QuadraticDiophantineN KAM.SpinOrbit.RotFreqN
short-name check OK (no reused public short name)
exit 0
```

The successful scratch probe printed axioms for every new public theorem:

```text
'KAM.Certificate.lunarNuMinusN_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlusN_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinusN_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlusN_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinusN_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlusN_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinusN_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlusN_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinusN_rot_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlusN_rot_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinusN_forty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlusN_forty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarGammaN_forty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinusN_isDiophantine_forty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlusN_rot_isDiophantine_forty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinusN_rot_isDiophantine_65' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlusN_rot_isDiophantine_65' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinusN_rot_isDiophantine_60' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlusN_rot_isDiophantine_60' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinusN_rot_isDiophantine_55' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlusN_rot_isDiophantine_55' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqMinusN_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqPlusN_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqMinusN_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqPlusN_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqMinusN_isDiophantine_65' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqPlusN_isDiophantine_65' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqMinusN_isDiophantine_60' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqPlusN_isDiophantine_60' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqMinusN_isDiophantine_55' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqPlusN_isDiophantine_55' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqMinusN_forty' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1460 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (146 frozen declarations)
exit 1
```

The sole failure is the generated-root freshness check, explicitly excepted by the audit brief. It was not regenerated. The full lint found no forbidden proof escapes, resource overrides, oversized files, overlong lines, module violations, provider-quarantine violations, or other errors. Both new modules have copyright, `module`, public imports, module docstrings and `@[expose] public section`.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)

git diff --check
(no output; exit 0)
```

## Errata, deviations, and limits

No suspected pinned-source defect, blueprint contradiction, or implementation deviation found. The N=40 design text is the old specialized contract; SO-DION's explicit brief authorizes this additive generalization. No frozen statement was changed, no source file was repaired, no anchor was sealed, and no state-changing git operation was performed. Only the report remains as an untracked repository file after scratch cleanup.

The only landing note is to have the orchestrator regenerate `KAM.lean` under its normal workflow. This report does not establish a concrete root enclosure or frequency-box check, a passing sharp certificate, or the final lunar application; it establishes the exact analytic/algebraic interfaces and proofs supplied by these two modules.

