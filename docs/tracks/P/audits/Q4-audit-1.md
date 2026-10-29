# Q4 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the Q4 infrastructure slice. `qb_beta`,
`budget`, and `displacement_power_flat` pass exact-signature and mathematical review.
There is no Q4 frozen theorem/provider anchor to seal; this does not close the
quantitative weak KAM theorem, Q6 assembly, or a planetary headline theorem.

## Scope and pinned evidence

Audited 2026-10-28 in `/root/code/KAM-inp-p11c-q4`, HEAD
`ec61ba294757fb4fd23480f41ddbcc209f6dad30`. The only audited production file is
`KAM/Planetary/Quantitative/Budget.lean`, SHA-256
`441a8f910ff38a8cdc94c5cd1ffe1c966d16ca82b7ca5d5e112b62f523c5cfaf`.
Authority read: AGENTS.md, PLAN, DECISIONS, the package brief, Q4 handoff,
P11C design sections 1–7/node table, its independent design audit 1, P statement,
and the relevant p11a-3/4/5 numerical and consumer statements.
The standalone signatures at `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`
hash to `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079`.
All five signed declarations match their signature text exactly, excluding theorem
proof bodies; the two signed definition bodies match exactly too.

The requested `git diff inp...HEAD` was run. `inp` resolved to
`bea4e8e486c920ad0f51758913e31756dd9e9554`; Git warns:
`multiple merge bases, using 5ddc1d835ec60da521818ffb93d9ee832d85b316`.
The resulting comparison contains 196 changed files, 32825 insertions and 756 deletions,
including inherited integration work outside this expressly restricted audit.
The complete Q4 delta, `git diff 7351a0d7..HEAD`, contains only Budget.lean,
205 insertions, across commits `2cdedf7e` and `ec61ba29`.
No other package is certified here.

## Declaration and node coverage

All names below are in `KAM.Planetary`. Line numbers refer to Budget.lean.

| Node / purpose | Declaration | Verdict | Evidence |
|---|---|---|---|
| K6 exponent | `p11c_G0` L28 | PASS | Literal `(mu+1)/rho`; exact signed body. |
| K5 exponent | `p11c_B0` L29 | PASS | Literal `2*max(2*G0)(1+mu*G0)`; exact signed body. |
| qb-beta specialization | `qbBetaRates` L33 | PASS | beta rate 1; all seven remaining rates 0. |
| Rate nonnegativity | `qbBetaRates_valid` L43 | PASS | All eight inequalities proved by simplification. |
| Gamma exponent | `qbBeta_rateG` L46 | PASS | Uses mu≥1 and rho>0 to identify the maximum with G0. |
| Budget exponent | `qbBeta_exponent` L63 | PASS | L=0, J=X=G0; H=max(2G0,1+mu*G0), B=2H. |
| Rate constant | `qbBetaC` L91 | PASS | Exactly the minimum specified in qb-beta source step. |
| Constant positivity | `qbBetaC_pos` L95 | PASS | Positive diameter follows from compact K of positive volume, not a premise. |
| Eight rate bounds | `qbBeta_rateBounds` L104 | PASS | Each lower/inverse upper bound derived; no assumed rate package. |
| Updated numerical validity | `qbBeta_valid` L138 | PASS | Replaces precisely beta positivity and beta≤M. |
| `stepP:p11a:qb-beta`, budget clause (d) | `qb_beta` L143 | PASS | Applies Q3 qb_poly at u=b, a_s=0; constant precedes all b. |
| `bpP:p11a:budget`, K5 | `budget` L159 | PASS | Exact signed conjunction of Q2 comparison/order and beta power. |
| K6 numerical bound | `displacement_power_flat` L168 | PASS | Gamma lower bound and min≤second branch give cD=cDelta/k, uniformly in b and eps≥0. |

The design's Q2–Q4 node rows are jointly implemented: qb-comp and qb-mono are
consumed from Q2, qb-poly from Q3, and qb-beta is established here. The source
budget has four clauses; signed `budget` intentionally packages (a),(b),(d),
with (c) available separately as the imported signed `qb_poly`. This is exactly
the design's section 5 and design-audit consumer ruling, not a missing clause.
No unsigned export is misleadingly named after a stronger graph node.
The qt-order/reduce/zero/iter/k2/k3/k4/k5/k6 rows are assigned to Q6 by the node
table; Q4 supplies its promised K5/K6 inputs and does not claim their torus assembly.

Design row Q4 names U11a1 `gamma_inverse`. No such declaration is imported or
assumed. Lines 177–194 instead apply Q3's proved `qbPoly_gamma_lower` at rates
(0,1,0,0,0), with its numerical validity, rate bounds and equality binders actually
supplied. It yields `k*b^G0 ≤ gamma`, k>0; division reverses this into the needed
inverse bound. The named numerical K6 conclusion is proved in full. This is a
sound alternate dependency route; it does not certify the separately stated
source gamma-inverse lemma with its explicit source constant.

The witnesses have the required dependence despite d also containing its original
beta: `qbBetaC` uses only the fixed entries, Q3 chooses c' before the varying
updated data/b, and the gamma witness k is chosen before b. The exponent
identifications use only mu and rho. Thus no original beta value is needed to
select the power-law constants.

Interface→Budget, omitted in the original package DAG and flagged by design audit
N2, is present at L9. The Q6 signature needs only these signed data-only surfaces.
No Q6 implementation is present to certify production consumption; the exact
signature-copy application probes below establish that the intended calls typecheck.
For K6 the scalar estimate holds for every eps≥0, including zero and values above
threshold; applicability to actual torus displacement still belongs to Q6.

## Expanded binder audit

Bins: SOURCE is an explicit numerical/source assumption; STANDING is a numerical
standing assumption; TYPING forms the carrier; RULED and EXCESS are both absent.
For each theorem accepting hd, the following is its complete expanded numerical
bundle (Thresholds.lean L43–48; a5 L73–80 and retained numerical hypotheses).

| Expanded hd component | Bin | Source / meaning |
|---|---|---|
| `1 ≤ N` | STANDING | a5 data, positive dimension |
| `1 ≤ d.mu` | STANDING | a5 finite-type order |
| `d.rho = 1 ∨ d.rho = 2` | STANDING | a5 allowed scalar powers |
| `N*mu/rho-1 < tau` | STANDING | a5 summability condition |
| `0 ≤ tau` | STANDING | a5 retained numerical condition |
| `0 < vartheta` | STANDING | positive thickness |
| `vartheta ≤ 1` | STANDING | normalized thickness |
| `0 < s` | STANDING | positive strip |
| `s ≤ 1` | STANDING | normalized strip |
| `1 ≤ C1` | STANDING | Hessian bound normalization |
| `0 < M0` | STANDING | positive derivative upper bound |
| `0 < beta` | STANDING | finite-type amount |
| `beta ≤ M` | STANDING | compatible derivative bound |
| `IsCompact K` | STANDING | compact action set |
| `0 < epsLoss` | STANDING | positive allowed loss |
| `ofReal epsLoss < volume K` | STANDING | nontrivial surviving volume |
| `N-1 < tau` (Valid only) | STANDING | a5 KAM exponent condition |
| `beta ≤ 1` (Valid only) | STANDING | a5 normalized KAM amount |

The remaining input binders are listed individually below; `N` is implicit, and
each d binder has type `QuantitativeData N`, with no instances or result fields.

| Declaration(s) | Binder | Bin | Reason |
|---|---|---|---|
| Each of the eight d-dependent theorems | `{N : ℕ}` | TYPING | coordinate dimension |
| Each of the eight d-dependent theorems | `d : QuantitativeData N` | TYPING | numerical parameters and K; no proofs in structure |
| `qbBeta_rateBounds`, `qbBeta_valid` | `{b : ℝ}` | TYPING | varying amount |
| `qbBeta_rateBounds`, `qbBeta_valid` | `hb : 0 < b` | SOURCE | qb-beta positive interval |
| `qbBeta_valid` | `hbM : b ≤ d.M` | SOURCE | updated numerical-validity domain |
| `displacement_power_flat` | `cDelta : ℝ` | TYPING | supplied uniform displacement coefficient |
| `displacement_power_flat` | `hc : 0 < cDelta` | SOURCE | positive coefficient, signature L258 |

Expanded-input totals per theorem (SOURCE/STANDING/TYPING/RULED/EXCESS):
`qbBetaRates_valid` 0/0/0/0/0;
`qbBeta_rateG`, `qbBeta_exponent`, `qbBetaC_pos`, `qb_beta`, `budget` each 0/16/2/0/0;
`qbBeta_rateBounds` 1/16/3/0/0;
`qbBeta_valid` 2/16/3/0/0;
`displacement_power_flat` 1/18/3/0/0.
Output-side universal b, eps, M0', d', and their guards are inside the respective
conclusions, in exactly the signed order. In particular the existential c and cD
precede every varying b (and eps); neither a gamma estimate nor a budget bound
has been moved into an input. No conclusion-shaped hypothesis was found.

## Definitions

| Definition | Body classification | Carrier |
|---|---|---|
| `p11c_G0` | Literal arithmetic formula | All QuantitativeData; ordinary total Lean division |
| `p11c_B0` | Literal arithmetic maximum | All QuantitativeData |
| `qbBetaRates` | Literal eight-component rate vector | BudgetRates, no proof fields |
| `qbBetaC` | Literal finite minimum | All QuantitativeData; positivity asserted only on NumericalValid |

For each of these four definitions:
`BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL;
CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS`.
There is no choice, default branch, manufactured object, new structure/abbrev,
or validity-dependent replacement of the mathematical object. The positivity
proof for qbBetaC establishes the needed domain facts rather than hiding them
in the definition. Existing RateBounds, BudgetOrder, NumericalValid, Valid,
rate/exponent formulas, gamma, thresholds and p11c_displacement were unfolded
and checked for hidden outputs. K6 uses hd.1 only, but preserves its exact signed
Valid binder; the handoff's weaker-hypothesis observation is not a signature change.

## Validation receipts

All auditor-controlled build/probe/replay/lint commands ran sequentially with
`LEAN_NUM_THREADS=1` and `nice -n 5`. No budget override, clean, update, cache fetch,
package modification or generated-file regeneration was performed.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-q4 KAM.Planetary.Quantitative.Budget
```

Exit 0: `[inp-gate] slot 2 acquired 22:04:38 for KAM.Planetary.Quantitative.Budget`;
`Build completed successfully (9116 jobs).` No Budget.lean warnings. Replayed
upstream warnings are unused binders in Hamiltonian/{Algebra,Chart,Diophantine,Transport},
BudgetPower/Collar and BudgetPower; no proof-budget failure occurred.

2. Exact statement/body and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Q4Audit.lean
```

Exit 0. The probe copied the three theorem commands from the independently supplied
signature file under fresh names and used, respectively,
`by exact qb_beta d hd`, `by exact budget d hd`, and
`by exact displacement_power_flat d hd cDelta hc`.
The two signed definitions were copied under fresh names and their defining
equalities with production definitions proved by rfl. No frozen/provider seal
probe applies: no Q4 export is manifest-bound and no Q4 provider exists.
Every new public theorem printed exactly `[propext, Classical.choice, Quot.sound]`:

```text
qbBetaRates_valid: [propext, Classical.choice, Quot.sound]
qbBeta_rateG: [propext, Classical.choice, Quot.sound]
qbBeta_exponent: [propext, Classical.choice, Quot.sound]
qbBetaC_pos: [propext, Classical.choice, Quot.sound]
qbBeta_rateBounds: [propext, Classical.choice, Quot.sound]
qbBeta_valid: [propext, Classical.choice, Quot.sound]
qb_beta: [propext, Classical.choice, Quot.sound]
budget: [propext, Classical.choice, Quot.sound]
displacement_power_flat: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Quantitative.Budget
```

Exit 0. Complete output: `replaying KAM.Planetary.Quantitative.Budget`.
Only Budget is the scoped lemma module; no provider module exists.

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, with complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1002 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole failure is the generated-root exception expressly permitted by the
package brief. No source was regenerated. No other forbidden-token, length,
module, frozen-byte or ABI violation was reported.

5. Scoped static checks: 205 lines, maximum 99 characters; module header,
public imports, documentation and `@[expose] public noncomputable section` present.
No forbidden proof token, EuclideanSpace or set_option occurs in Budget.lean.
Scanning all other KAM Lean declarations found no duplicate of any of the 13
new public names; no new root namespace, global instance or harmful shadow is
introduced. The internal local name `inv` is not a public declaration.
A recursive local-import scan found 24 frozen modules, all manifest-owned SEALED
definitions, no frozen theorem (draft or sealed), and no provider. Thus there is
no production import of a DRAFT_SORRY anchor or quarantined provider.

## Notes, defects and limits

- Handoff metadata is stale: Budget.lean has 205 total lines, not 99. Its maximum
  line length is 99 characters, which may explain the mismatch. All 13 public
  declarations listed above were reviewed, not merely the three headline theorems.
- The literal full three-dot protected-path check is nonempty: KAM.lean,
  the N quasi-convex complex-bound frozen theorem, and manifest/frozen-anchors.json
  changed in inherited integration history. The frozen change is its provider
  seal and the manifest transition DRAFT_SORRY→SEALED. These are already present
  at Q4's parent `7351a0d7`; `git diff 7351a0d7..HEAD -- KAM/Frozen manifest KAM.lean README.md`
  is empty. Thus the brief's literal full-history emptiness condition is not met,
  but no protected file was changed by Q4. This note does not independently approve
  the inherited N sealing work.
- `git diff --check inp...HEAD` exits 2 on inherited whitespace:
  SecularForm/Quartic/Conversion.lean:93 trailing whitespace and
  docs/tracks/P/audits/B07-audit-2.md:284 blank line at EOF.
  `git diff --check 7351a0d7..HEAD` exits 0.
- The dependency table's `gamma_inverse` name is reconciled by the local proved
  lower-bound route described above; no unavailable theorem is assumed.
- No new suspected pinned-source mathematical erratum or Q4 statement defect was
  found. The existing source citation correction and Interface DAG omission are
  recorded in the P11C design/audit; no source, graph, manifest or production repair
  was made here. No claim about unseen pinned PDF pages is made.

Only this report is a lasting auditor edit. Disposable probes and replay logs
are removed after recording the final receipts. No state-changing git operation
was performed.
