# Q1 independent package audit 1

**Verdict: PASS WITH NOTES (definitions package accepted).** No frozen anchor is supplied or sealed by Q1; provider/type/seal-body tests are not applicable. This audit does not establish positivity, budget comparison, cutoff estimates, or the quantitative KAM theorem.

Audit date: 2026-10-28. Scope is exclusively `KAM/Planetary/Quantitative/Thresholds.lean`, per the handoff AUDIT FOCUS. HEAD `90e233c55de2b02501ab859e6de7b7bf6463ed0b`; comparison ref `inp` was `dca5e7e3ee3a8b0d8f0f2b53a377bf87ac1fc024`. `git diff inp...HEAD --stat` contains only this new 107-line file (handoff says 108). SHA-256: `96f986fe49cf0eded8fe256857075c6312748346250b9a8f5712a7be1e7ce545`.

Read AGENTS.md, PLAN, DECISIONS, the package brief, handoff, P11C design row Q1 and Appendix A, its independent design audit, track P statement conventions, and blueprint Parts 11a-2, 11a-3, 11a-5. The standalone signature is in `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`, not this worktree; SHA-256 `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079`, matching the design audit. The user's explicit destination overrides the generic brief's main-worktree destination. Only this report is a persistent edit; scratch probes are removed after validation. No git mutation.

## Declaration and definition classification

Names are fully qualified by `KAM.Planetary.`. Blueprint labels abbreviate `bpP:p11a:`. Lines refer to the audited module. Generated constructor and field projections belong to the structure row.

| Node | Declaration | Line | Verdict | Classification / reason |
|---|---|---:|---|---|
| `sec-q-thm#data` | `QuantitativeData` | 28 | PASS | Structure: eleven numerical/set fields, exactly the signature; no analytic or KAM output hidden in fields. |
| `sec-q-thm#data` | `QuantitativeData.NumericalValid` | 41 | PASS | Predicate: N, mu positive, rho=1 or 2, numerical bounds and compact positive-measure K. epsLoss condition implies positive volume. |
| `sec-q-thm#data` | `QuantitativeData.Valid` | 48 | PASS | Predicate: adds tau>N-1 and beta<=1 as required by the quantitative theorem. |
| `smooth-cutoff` | `p11c_bump` | 51 | PASS | Polynomial positive-part bump, exponent mu+1. |
| `smooth-cutoff` | `p11c_mollifier` | 52 | PASS | Actual Lebesgue-integral normalization of that bump, no arbitrary normalization input. |
| `smooth-cutoff` | `p11c_mollifierMass` | 55 | PASS | L1 mass of the actual j-th iterated derivative. |
| `smooth-cutoff` | `p11c_cutoffDerivative` | 56 | PASS | N^k times supremum over multiindices of total degree k; finite, nonempty for N>=1. |
| `smooth-cutoff` | `p11c_cutoffConstant` | 59 | PASS | sqrt N times finite maximum over k<=mu of the literal binomial formula; includes 0^0=1. |
| `thresholds` | `QuantitativeData.diameter` | 64 | PASS | Pi max-metric diameter of K, not Euclidean diameter. |
| `schedule-consts` | `QuantitativeData.varpi` | 65 | PASS | 2^(-2 E_*), E_*=2(tau+1)(mu+1)+N+4; real exponent. |
| `fourier-cutoff` | `QuantitativeData.cN` | 67 | PASS | Literal upstream Fourier constant; natural exponent N-1. |
| `thresholds` | `QuantitativeData.A0` | 69 | PASS | log(16 cN/varpi). |
| `thresholds` | `QuantitativeData.cDio` | 70 | PASS | All diameter, beta, rho/mu and summation factors agree with a5 L25. |
| `thresholds` | `QuantitativeData.gamma` | 75 | PASS | Exactly half the minimum defining gamma_*; dimension and fractional powers correct. |
| `thresholds` | `QuantitativeData.tbar` | 79 | PASS | 1 plus explicit absolute-A0 bound, not the old max formula. |
| `thresholds` | `QuantitativeData.tflat` | 81 | PASS | Minimum of thickness/sqrt N and gamma tbar^(-tau-1)/(4 C1). |
| `thresholds` | `QuantitativeData.xibar` | 83 | PASS | Minorant budget uses reciprocal strip/collar terms, not old ratios. |
| `adm-params` | `QuantitativeData.thetaMax` | 85 | PASS | rho=1 beta/2; rho=2 exact minimum with 2^(mu+1)(2 M0+beta). |
| `thresholds` | `QuantitativeData.lambdaFlat` | 87 | PASS | Three-way minimum; first term tflat/8; CQ=18 N(4 N+5) expanded literally. |
| `thresholds` | `thresholds` | 92 | PASS | lambdaFlat squared divided by 2 N C1; data-only. |
| `adm-params` | `p11c_oldThreshold` | 95 | PASS | Comparison-only literal old T, t, Xi, C1*t/8 and threshold formula. |
| `U11a2 adapter` | `QuantitativeData.cN_eq_p11C` | 105 | PASS | Unconditional rfl theorem; exact upstream object for every N, including N=0. |

The complete production block from `structure QuantitativeData` through `p11c_oldThreshold` is byte-identical to signature L47–121 (including field order). Twenty copied definitions were elaborated in a fresh nested namespace, with the original signature imports and `open KAM KAM.Kepler KAM.ODE`; the data carrier was aliased to the production structure. Each function/predicate equals its production counterpart by `rfl`, including implicit binders. This checks elaborated bodies as well as types and refutes a meaning change from the omitted `open` line. Structure fields were compared byte for byte. The added adapter requires no hypothesis and identifies exactly `KAM.Planetary.p11C` from MaximalStep.Constants L28–29, agreeing with blueprint 11a-2 L44.

Definitions are literal total Lean formulas. On the source domain, NumericalValid supplies N>=1, mu>=1, rho in {1,2}, compact K, positive beta/M0/C1/widths and positive permitted measure loss. Valid adds the theorem's stronger exponent and beta conditions. Finite multiindex sets and k<=mu sets support the maxima; normalized compactly supported polynomial bump derivatives through order mu have the intended L1 interpretation. Outside these guards, Lean's total division, real powers, integral, diameter and supremum conventions apply; no theorem here relies on a degenerate default value. In particular thetaMax's `else` coincides with the source rho=2 branch on valid data and deliberately extends the signature outside it. There is no added arbitrary constant, proof-as-field, hard-step hypothesis or fallback standing in for source analysis.

## Notes, upstream boundaries, defects

- **N1 (expected hygiene exception):** the generated root omits this new module, so lint reports `KAM.lean is out of date`. The brief explicitly allows this and forbids regeneration by the auditor.
- **N2 (scope boundary):** no delivered upstream mollifier/cutoff-constant or old-threshold owner is identified in this checkout. These formulas match the design and blueprint, but future U11a3 consumers still owe their reconciliation and positivity/estimate proofs. Q1 proves no such attachment and introduces no assumed certificate. BudgetOrder belongs to Q2; analytic input and family structures belong to Q0/Q5.
- No suspected new source/blueprint defect or mathematical deviation found in the audited module. No pinned external PDF was independently re-audited; the immediate authority for these explicit constants is the supplied blueprint. Existing design-audit graph-hash and package-DAG notes remain outside Q1. The handoff's line-count discrepancy is documentary only.

## Independent validation

All Lean/Lake invocations below were sequential with `LEAN_NUM_THREADS=1` and niceness 5. No heartbeat, recursion-depth or synthesis-budget override; no dependency edits or clean/rebuild-from-scratch operation. The targeted build used the mandatory compile gate.

1. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output. `git diff --check inp...HEAD`: exit 0, empty output.
2. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-q1 KAM.Planetary.Quantitative.Thresholds`: exit 0. Output after the expected slot wait:

```text
[inp-gate] slot 1 acquired 15:00:26 for KAM.Planetary.Quantitative.Thresholds
Build completed successfully (9086 jobs).
```

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Q1Signature.lean`: exit 0; all 20 `rfl` body/type comparisons succeeded, no warnings/errors. Exact axiom output:

```text
'KAM.Planetary.QuantitativeData.cN_eq_p11C' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.NumericalValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.Valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_bump' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_mollifier' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_mollifierMass' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_cutoffDerivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_cutoffConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.diameter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.varpi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.cN' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.A0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.cDio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.tbar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.tflat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.xibar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.thetaMax' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.QuantitativeData.lambdaFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.thresholds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_oldThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Q1Coimport.lean`: exit 0. Probe co-imported all 745 modules in the generated root plus Thresholds (the entire non-quarantined library). The only other files omitted by that root are the 9 providers and their 9 DRAFT_SORRY anchors; no unrelated deliverable was silently excluded. Exact output:

```text
KAM.Planetary.QuantitativeData.cN_eq_p11C (N : ℕ) : KAM.Planetary.QuantitativeData.cN N = KAM.Planetary.p11C N
```

Generic names live under `KAM.Planetary.QuantitativeData` except the explicitly prefixed bump/cutoff/oldThreshold names and `KAM.Planetary.thresholds`. Whole-source name search found no competing declaration at these fully qualified names; for example `KAM.Head.A0` has a distinct namespace. Co-import elaboration confirms no collision in the usable library.

The audited module transitively imports 40 KAM modules, no provider and no frozen theorem. Its ten frozen imports are all manifest state SEALED, kind definition: `actionNbhd`, `complexStrip`, `hamiltonianVectorField`, `hamiltonianVectorFieldℂ`, `IsDiophantine`, `IsPrimaryOnStrip`, `IsRealOnReals`, `omegaZero`, `symplecticForm`, `Planetary.Phase`. No frozen theorem is being substituted for a proof obligation.

5. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Quantitative.Thresholds`: exit 0. Single invocation, exact output:

```text
replaying KAM.Planetary.Quantitative.Thresholds
```

No provider or additional lemma module belongs to Q1. This replays the declarations in the actual audited module, including the added adapter.

6. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`: exit 1, solely the explicitly permitted generated-root diagnostic. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (766 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All forbidden-token, override, ambient-type, line-length and 1500-line checks pass. The new module has the copyright header, `module`, public imports, module docstring, exposed public noncomputable section, and 107 total lines. Its only theorem has the axiom set printed above. No additional forbidden axiom or `sorryAx` occurs in its audited exports.

Final verification: `git diff --check -- docs/tracks/P/audits/Q1-audit-1.md` exits 0 (untracked report additionally checked for trailing whitespace); protected-path comparison remains empty. All Q1-created `.lean` probes and logs in `.lake/abi-scratch/` were removed. The pre-existing untracked `Q1-handoff.md` was left untouched. No uncertainty changes the scoped acceptance; N1 and N2 explain the PASS WITH NOTES verdict.
