# Q3 independent package audit 1

Verdict: **PASS WITH NOTES** for the complete Q3 slice, including `KAM.Planetary.qb_poly`.
No frozen theorem anchor or provider belongs to Q3; “seal-ready” is inapplicable. This is an
accepted numerical infrastructure result, not closure of the quantitative KAM theorem or B20.

## Scope and authority

Worktree `/root/code/KAM-inp-p11c-q3`; HEAD `ec1afcb84098475f12ec99f6d77cb531df71d871`.
Comparison `inp` resolved to `8731638a13555ea8908a13dd6a4435194b95b5e1`.
`git diff inp...HEAD` warns of multiple merge bases and selects
`e631fe0e7ba0a70ccfa647c4c28194642c373eba`. The full diff inventory is ten files:
the five Q3 files below, three inherited `WeakKAM/{Admissible,Budgets,BudgetsStage}.lean`
files and two inherited B07 audit/handoff files. Only the five Q3 files are mathematically
audited, as explicitly instructed. Initial status contained only the untracked Q3 handoff.
No source, generated file, manifest, or git state was changed by this audit.

Read AGENTS, PLAN, DECISIONS, the package audit brief, Q3 handoff/focus, P11C Lean design
(row Q3, U11a3, node table and Appendix A), P11C design audit, standalone signatures,
P statement and the relevant blueprint and graph records. The prompt's exact report path
overrides the generic brief's instruction to write in the main inp worktree.

## Fidelity, completeness and dependency findings

The five SIGNED declarations (`BudgetRates`, `.Valid`, `.exponent`, `RateBounds`, `qb_poly`)
match `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean:136–171` exactly after whitespace
normalization (the theorem comparison omits only its proof). A fresh declaration copied from
the signed theorem elaborated with the body
`by exact qb_poly N mu rho tau c asRate hN hmu hrho htau htau0 hc hc1 has`.
`example : type_of% @auditQ3_signed := @qb_poly` also elaborated.
This is the signed-interface check appropriate here; there is no frozen-provider seal to probe.

The constant is chosen after `(N,mu,rho,tau,c,a_s)` and before the other seven rates, datum K,
all data entries and u. The construction uses `c' = k^2*c/(2*N)`; k depends only on the allowed
fixed parameters. The gamma estimate has no rate-dependent coefficient. The only strip-rate
coefficient is in the logarithmic cutoff bound, where the two cases a_s=0 and a_s>0 are proved
separately. Exact exponent:

```
D = N*a_d + a_M + a_vartheta + (1+1/mu)*a_beta
G = max (a_beta/rho) ((mu/rho)*(a_loss+D))
L = if 0<a_s then a_s+1 else 0
J = max a_vartheta (G+(tau+1)*L+a_C)
X = max J L
H = max (max J (G+(N+1)*a_s+tau*L+X)) (a_beta+a_M0+mu*J)
B = 2*H+a_C
```

| Graph obligation | Verdict | Established scope |
|---|---|---|
| `bpP:p11a:budget`, clause `bpP:p11a:bu-poly` | PASS | Signed `qb_poly` proves precisely the general flat-threshold power bound. Other budget clauses belong to Q2/Q4. |
| `stepP:p11a:qb-poly` (a5:52) | PASS | Entire proof chain through local gamma, cutoff, collar, Xi and all three lambda branches, ending with the C1 denominator. |
| `stepP:p11a:ab-gamma` (a3:387), as reused by Q3 | PASS | `qbPoly_cDio_bound` and `qbPoly_gamma_lower` prove the literal needed gamma bound. |
| `stepP:p11a:ab-T0` (a3:389), as reused by Q3 | PASS | `qbPoly_tbar_bound` proves the required stronger-cutoff analogue for tbar. |
| `stepP:p11a:ab-t0` (a3:391), as reused by Q3 | PASS | `qbPoly_collar` and `qbPoly_xibar_upper` establish the flat collar/Xi analogues. |
| `stepP:p11a:ab-lam` (a3:393), as reused by Q3 | PASS | `qbPoly_second_lower`, `qbPoly_thetaMax_lower`, `qbPoly_lambda_lower` prove the three flat branches. |

The design explicitly permits these local proof fragments (P11C-LEAN-DESIGN.md:50,59,193).
The helper names do not purport to export the old T0/t0/Xi/lambda_max graph nodes.
Their flat counterparts are exactly what a5:52 requests. They do not prove or assume B20
`adm_budget`, old-threshold comparison, monotonicity or the beta specialization. Those are
separate obligations. No conclusion-shaped premise enters the signed theorem. Conditional
arithmetic helpers have distinct names; their bound hypotheses are discharged explicitly by
proved lemmas in `qbPoly_lambda_lower` and `qb_poly`.

The direct graph edges at `docs/graph/P/DEPGRAPH.md:28049–28058` describe hypotheses,
exponent formulas and reused proof fragments. Q3 supplies these numerically rather than
calling an unavailable B20 theorem; this is consistent with the design. Q4's beta specialization
and K5 consumers require exactly this uniformity and exponent; no signed narrowing or missing
Q3 consumer obligation was found. No other design node is assigned exclusively to Q3.

## Every public declaration

All names below are in `KAM.Planetary`. Locations are in the five audited files.

| File:line | Declaration | Verdict | Reason / node |
|---|---|---|---|
| `BudgetPower.lean:31` | `BudgetRates` | PASS | SIGNED: exact eight independent real rates; no output fields. |
| `BudgetPower.lean:41` | `BudgetRates.Valid` | PASS | SIGNED: conjunction of precisely the eight nonnegativity conditions. |
| `BudgetPower.lean:44` | `BudgetRates.exponent` | PASS | SIGNED: literal D,G,L,J,X,H and B=2H+a_C; exact maxima and casts. |
| `BudgetPower.lean:53` | `RateBounds` | PASS | SIGNED: four lower and four upper data bounds in the signed order. |
| `BudgetPower.lean:61` | `BudgetRates.rateD` | PASS | Concrete named D formula, definitionally the corresponding signed exponent subexpression. |
| `BudgetPower.lean:65` | `BudgetRates.rateG` | PASS | Concrete named G formula, definitionally the corresponding signed exponent subexpression. |
| `BudgetPower.lean:69` | `BudgetRates.rateL` | PASS | Concrete named L formula, definitionally the corresponding signed exponent subexpression. |
| `BudgetPower.lean:72` | `BudgetRates.rateJ` | PASS | Concrete named J formula, definitionally the corresponding signed exponent subexpression. |
| `BudgetPower.lean:76` | `BudgetRates.rateX` | PASS | Concrete named X formula, definitionally the corresponding signed exponent subexpression. |
| `BudgetPower.lean:80` | `BudgetRates.rateH` | PASS | Concrete named H formula, definitionally the corresponding signed exponent subexpression. |
| `BudgetPower.lean:84` | `BudgetRates.exponent_eq` | PASS | Definitional identity; rfl; no altered exponent. |
| `BudgetPower.lean:89` | `qbPoly_collar` | PASS | ab-T0/ab-t0 adapted to flat quantities: both tbar bounds and tflat >= k u^J. |
| `BudgetPower.lean:178` | `BudgetRates.rateJ_nonneg` | PASS | Valid rates imply J >= a_vartheta >= 0. |
| `BudgetPower.lean:182` | `BudgetRates.s_le_rateL` | PASS | a_s <= L; actually stronger, validity is unused. |
| `BudgetPower.lean:188` | `BudgetRates.rateL_le_rateX` | PASS | L <= max J L, on the full carrier. |
| `BudgetPower.lean:191` | `BudgetRates.rateJ_le_rateX` | PASS | J <= max J L, on the full carrier. |
| `BudgetPower.lean:194` | `qbPoly_xibar_upper` | PASS | ab-t0: xibar <= Cx u^(-X); conditional bound inputs discharged in lambda_lower. |
| `BudgetPower.lean:244` | `qbPoly_second_lower` | PASS | ab-lam, second factor: gamma, strip power and tbar denominator; no X factor lost. |
| `BudgetPower.lean:298` | `qbPoly_lambda_lower` | PASS | ab-lam adapted to flat quantities: all three branches >= k u^H. |
| `BudgetPower.lean:419` | `qb_poly` | PASS | SIGNED; bu-poly/qb-poly: exact signature, constants before all varying rates/data/u. |
| `Collar.lean:22` | `qbPoly_tbar_bound` | PASS | ab-T0 adapted to tbar: explicit positive C; separate a_s=0 and a_s>0 cases. |
| `Collar.lean:110` | `qbPoly_thetaMax_lower` | PASS | ab-lam third branch: c^2/2^(mu+3) u^(a_beta+a_M0); both rho cases. |
| `Gamma.lean:23` | `qbPoly_gap_pos` | PASS | Strict lattice gap follows from the source tau condition; no added premise. |
| `Gamma.lean:34` | `qbPoly_cDio_bound` | PASS | ab-gamma: positive cDio <= C u^(-D); C independent of all rates. |
| `Gamma.lean:153` | `qbPoly_gamma_lower` | PASS | ab-gamma: both min branches and the factor 1/2; exact G. |
| `Positivity.lean:23` | `qbPoly_bump_nonneg` | PASS | Actual Q1 bump is nonnegative. |
| `Positivity.lean:26` | `qbPoly_bump_continuous` | PASS | Actual Q1 bump is continuous. |
| `Positivity.lean:29` | `qbPoly_bump_zero` | PASS | Actual Q1 bump equals 1 at zero. |
| `Positivity.lean:32` | `qbPoly_bump_integral_pos` | PASS | Continuity, compact support and positivity at zero imply positive integral. |
| `Positivity.lean:46` | `qbPoly_diameter_pos` | PASS | Positive-volume compact K is nontrivial in positive dimension; actual max diameter. |
| `Positivity.lean:59` | `qbPoly_mollifierMass_zero` | PASS | Normalized bump has zeroth L1 mass 1; no total-integral fallback used. |
| `Positivity.lean:71` | `qbPoly_cutoffDerivative_zero` | PASS | Finite-index zero multi-index set is exactly {1}; sSup is legitimate. |
| `Positivity.lean:88` | `qbPoly_cutoffConstant_pos` | PASS | Finite outer sSup contains the k=0 term 1; positive sqrt N. |
| `Rates.lean:21` | `qbPoly_pow_anti` | PASS | Exponent antitonicity for positive u <= 1. |
| `Rates.lean:25` | `qbPoly_negpow_mono` | PASS | Negative-exponent monotonicity for positive u <= 1. |
| `Rates.lean:29` | `qbPoly_negpow_ge_one` | PASS | Nonnegative rate gives u^(-e) >= 1. |
| `Rates.lean:33` | `qbPoly_pow_le_one` | PASS | Nonnegative rate gives u^e <= 1. |
| `Rates.lean:38` | `qbPoly_ub_mul` | PASS | Elementary conditional product upper bound; used with proved nonnegativity. |
| `Rates.lean:44` | `qbPoly_lb_mul` | PASS | Elementary conditional product lower bound; used with proved nonnegativity. |
| `Rates.lean:49` | `qbPoly_pow_add` | PASS | Positive-base rpow addition identity. |

## Definition classification

There is one structure (`BudgetRates`), nine definitions and no abbrev, new instance, opaque
object, alternate norm or new carrier. `BudgetRates` is an unbundled eight-real record;
nonnegativity is a separate source predicate, not hidden proof data. `RateBounds` records
precisely the input bounds. `exponent` and `rateD/G/L/J/X/H` are explicit total real formulas,
with the literal conditional for L. At nonpositive s-rates or zero natural denominators Lean's
total operations remain the stated formulas; theorems requiring rate interpretation impose
nonnegativity, mu>=1 and rho in {1,2}. No theorem exploits a junk branch. All are exposed by
`@[expose] public noncomputable section`. The unfolding identity `exponent_eq` is proved by rfl.

Q1's existing formulas were read for interpretation, not changed or re-audited as Q3 ownership.
The positivity lemmas actually prove the needed nondegeneracy: normalized bump integral >0,
zeroth mollifier mass=1, cutoff derivative at zero=1, finite outer sSup >=1, diameter>0.
Thus division by the cutoff constant and the positive cDio estimate do not use fallback values.
The actual carrier of K is `Set (Fin N → ℝ)` with the Pi max norm, and the volume condition
excludes empty/singleton K. No `EuclideanSpace` occurs.

## Checks and hygiene

All Lean operations were serialized and run with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No overrides, library rebuild, cache mutation command, generated-file repair or source edit.

1. Targeted compile gate:

```
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-q3 KAM.Planetary.Quantitative.BudgetPower
```

Exit 0; output: `Build completed successfully (9091 jobs).`
Only warnings: unused `hrho` at Collar.lean:110:54, `hv` at BudgetPower.lean:182:50,
`hu1` at BudgetPower.lean:246:49. These are harmless stronger helper interfaces.

2. Signed declaration extraction and whitespace comparison: five `EXACT` results.
The scratch probe `.lake/abi-scratch/Q3Audit.lean` was elaborated with:

```
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Q3Audit.lean
```

Exit 0; no type/proof errors. `#print axioms` was run on all 30 public theorems listed above.
Exact output:

```
'KAM.Planetary.BudgetRates.exponent_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_collar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.BudgetRates.rateJ_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.BudgetRates.s_le_rateL' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.BudgetRates.rateL_le_rateX' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.BudgetRates.rateJ_le_rateX' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_xibar_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_second_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_lambda_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qb_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_tbar_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_thetaMax_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_gap_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_cDio_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_gamma_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_bump_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_bump_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_bump_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_bump_integral_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_diameter_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_mollifierMass_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_cutoffDerivative_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_cutoffConstant_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_pow_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_negpow_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_negpow_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_pow_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_ub_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_lb_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbPoly_pow_add' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Quantitative.BudgetPower KAM.Planetary.Quantitative.BudgetPower.Positivity KAM.Planetary.Quantitative.BudgetPower.Rates KAM.Planetary.Quantitative.BudgetPower.Gamma KAM.Planetary.Quantitative.BudgetPower.Collar
```

Exit 0. Exact output:

```
replaying KAM.Planetary.Quantitative.BudgetPower
replaying KAM.Planetary.Quantitative.BudgetPower.Collar
replaying KAM.Planetary.Quantitative.BudgetPower.Positivity
replaying KAM.Planetary.Quantitative.BudgetPower.Gamma
replaying KAM.Planetary.Quantitative.BudgetPower.Rates
```

Source lint:

```
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted stale generated root. Exact output:

```
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (905 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No substantive source-lint failure; the generated root was left untouched.

4. Hygiene scan: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option` or
`EuclideanSpace` in any Q3 file. All five have copyright, module, public imports, module
docstring and public section. No duplicate public helper declaration short name was found
elsewhere in KAM; every new declaration stays inside `KAM.Planetary`, with no harmful root
shadow. Module sizes and maximum Unicode line widths:

| File | Lines | Maximum width |
|---|---:|---:|
| BudgetPower.lean | 464 | 100 |
| BudgetPower/Collar.lean | 174 | 96 |
| BudgetPower/Gamma.lean | 229 | 99 |
| BudgetPower/Positivity.lean | 102 | 94 |
| BudgetPower/Rates.lean | 52 | 91 |

Project import closure has 45 KAM modules, zero providers and zero frozen theorem imports.
Its ten frozen definition modules are all manifest `SEALED`: ActionNbhd, ComplexStrip,
HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals,
OmegaZero, SymplecticForm, Planetary/Defs/Phase. Thus no DRAFT_SORRY anchor is imported.

5. Protected paths:

```
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Exit 0, empty stdout (only the multiple-merge-base warning on stderr).
`git diff --check inp...HEAD` exits 2 solely for inherited
`docs/tracks/P/audits/B07-audit-1.md:175: new blank line at EOF.`
This lies outside the named Q3 scope; no Q3 whitespace issue was reported.

## Notes, uncertainties and suspected errata

No new mathematical source/blueprint defect or introduced deviation was found. The signed
Q3 statement is proved without extra premises. The design audit already records a stale
integration-graph hash and unrelated scheduling/DAG notes; this audit makes no graph edits.
The expected generated-root lint exception, harmless unused-variable warnings and inherited
B07 whitespace warning account for the package-level PASS WITH NOTES.
Q3 readiness does not certify the old-threshold B20 result, other Q2/Q4 budget clauses,
upstream analytic attachment or any frozen planetary headline.

## Final audit state

The scratch signature/axiom probe and audit logs were deleted after their output was copied
into this report. Final tracked diff is unchanged; the only new repository artifact from this
audit is this report. The pre-existing untracked Q3 handoff remains untouched.
